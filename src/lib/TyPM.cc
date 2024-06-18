//===-- TyPM.cc - type-based dependence analysisgraph------------===//
// 
// This pass performs module-level, type-based dependence analysis,
// which identifies dependent modules of a given pair<type, module>. 
//
//===-----------------------------------------------------------===//

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h" 
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"  
#include "llvm/IR/InstrTypes.h" 
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h" 
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h" 

#include "TyPMCommon.h"
#include "TyPMPass.h"

#include <deque>
#include <map>
#include <vector>
#include <iomanip>


using namespace llvm;

//
// Static variables
//
// DenseMap<pair<Module*, size_t>, set<Module*>> TyPM::moPropMapAll;
//
// extern map<Module *, Type *>Int8PtrTy;

//
// Implementation
//

// Customize the function to support various types for
// modularization, such as function types or a specific struct
bool TyPM::isTargetTy(Type *TTy) {

#if FUNCTION_AS_TARGET_TYPE
	return TTy->isFunctionTy();
#else
	// structs as target types

	if (StructType *STy = dyn_cast<StructType>(TTy)) {
		size_t TyH = typeHash(STy);
		return (TTySet.find(TyH) != TTySet.end());
	}
	return false;
#endif
}

bool TyPM::isContainerTy(Type *Ty) {
	return isCompositeType(Ty);
}





/////////////////////////////////////////////////////////////////////
//
// The following functions maintain maps for type flows
//
/////////////////////////////////////////////////////////////////////


void TyPM::addPropagation(const Module *ToM, const Module *FromM, Type *Ty, 
		bool isICall) {
	size_t TyH = typeHash(Ty);
#if 0	
	if (Ty->isFunctionTy())
		OP<<"@@ FuncType: "<<*Ty<<"; "<<"\n\t"
			<<FromM->getName()<<" ==> "<<ToM->getName()
			<<" HASH: "<<TyH<<"\n";
#endif
	if (isICall)
		moPropMapV[make_pair(ToM, TyH)].insert(FromM);
	else
		moPropMap[make_pair(ToM, TyH)].insert(FromM);
}

void TyPM::addModuleToGVType(Type *Ty, const Module *M, const GlobalVariable *GV) {
#if 0
	OP<<"@@ Store to GV: "<<GV->getName()<<"\n\t";
	OP<<"@@ Add: "<<*Ty<<"\n\t"
		<<" <== "<<M->getName()<<" HASH: "<<typeHash(Ty)<<"\n";
#endif
	TypesFromModuleGVMap[make_pair(GV->getGUID(), typeHash(Ty))].insert(M);
}


void TyPM::addGVToModuleType(Type *Ty, const GlobalVariable *GV, const Module *M) {
#if 0
	OP<<"@@ Load from GV: "<<GV->getName()<<"\n\t";
	OP<<"@@ Add: "<<*Ty<<"\n\t"
		<<" ==> "<<M->getName()<<" HASH: "<<typeHash(Ty)<<"\n";
#endif
	TypesToModuleGVMap[make_pair(GV->getGUID(), typeHash(Ty))].insert(M);
}



/////////////////////////////////////////////////////////////////////
//
// The following functions perform typecasting analysis
//
/////////////////////////////////////////////////////////////////////


void TyPM::findCastsInGV(const GlobalVariable * GV, userset_t &CastSet) {

	auto Ini = GV->getInitializer();
	if (!Ini) return;
	if (!isa<ConstantAggregate>(Ini)) return;

	deque<const User*> LU;
	LU.push_back(Ini);
	visited_t Visited;

	while (!LU.empty()) {
		auto U = LU.front();
		LU.pop_front();
		if (Visited.find(U) != Visited.end()) {
			continue;
		}
		Visited.insert(U);

		for (auto oi = U->op_begin(), oe = U->op_end();
				oi != oe; ++oi) {

			const Value *O = *oi;
			Type *OTy = O->getType();

			if (PointerType *POTy = dyn_cast<PointerType>(OTy)) {
				if (isa<ConstantPointerNull>(O))
					continue;

				if (auto CO = dyn_cast<BitCastOperator>(O)) {

					// Record the cast
					CastSet.insert(CO);

					auto OU = dyn_cast<User>(CO->getOperand(0));
					LU.push_back(OU);
				}
				else if (auto GO = dyn_cast<GEPOperator>(O)){

					auto OU = dyn_cast<User>(GO->getOperand(0));
					if (!isa<GlobalVariable>(OU))
						LU.push_back(OU);
				}
			}
			// If it is a composite type 
			else if (isContainerTy(OTy)) {

				// Continue analyzing nested composite types
				auto OU = dyn_cast<User>(O);
				LU.push_back(OU);
			}

		}
	}
}


void TyPM::findCastsInFunction(const Function *F, userset_t &CastSet) {

	for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		auto I = &*i;

		if (auto CastI = dyn_cast<CastInst>(I)) {
			// Record the cast, handle later
			CastSet.insert(CastI);
		}

		// Operands of instructions can be BitCastOperator
		for (auto OI = I->op_begin(), OE = I->op_end();
				OI != OE; ++OI) {
			if (auto CO = dyn_cast<BitCastOperator>(*OI)) {
				CastSet.insert(CO);
			}
		}
	}
}

void TyPM::processCasts(userset_t &CastSet, const Module *M) {

	for (auto CO : CastSet) {
		Type *TyFrom = CO->getOperand(0)->getType();
		Type *TyTo = CO->getType();
		// The following filters are a bit aggressive
		if (!TyFrom->isPointerTy() || !TyTo->isPointerTy())
			continue;
		if (TyFrom != Int8PtrTy[M] && TyTo != Int8PtrTy[M])
			continue;

		Type *ETyFrom = TyFrom->getPointerElementType();
		Type *ETyTo = TyTo->getPointerElementType();
		if (!isTargetTy(ETyFrom) && !isContainerTy(ETyFrom) 
				&& !isTargetTy(ETyTo) && !isContainerTy(ETyTo)) {
			continue;
		}


		Type *BTyFrom = TyFrom, *BTyTo = TyTo;
		if (BTyFrom && BTyTo) {
			CastFromMap[M][TyTo].insert(TyFrom);
			CastToMap[M][TyFrom].insert(TyTo);
		}
	}
}




/////////////////////////////////////////////////////////////////////
// 
// The following functions analyze globals and function calls for
// potential types of data flows
//
/////////////////////////////////////////////////////////////////////

void TyPM::findTargetTypesInInitializer(const GlobalVariable * GV,
		const Module *M, typeset_t &TargetTypes) {

	auto Ini = GV->getInitializer();
	if (!Ini) return;
	// The global can be a pointer to another global; in this case, we
	// still need to look into it, so comment out the following line
	//if (!isa<ConstantAggregate>(Ini)) return;

	if (ParsedGlobalTypesMap.find(GV)
			!= ParsedGlobalTypesMap.end()) {
		TargetTypes = ParsedGlobalTypesMap[GV];
		return;
	}

	deque<const User*> LU;
	LU.push_back(Ini);
	visited_t Visited;

	while (!LU.empty()) {
		auto U = LU.front();
		LU.pop_front();
		if (Visited.find(U) != Visited.end()) {
			continue;
		}
		Visited.insert(U);

		Type *UTy = U->getType();

		if (isTargetTy(UTy)) {
			// Found a target type
			TargetTypes.insert(UTy);
		}
#ifdef TYPE_ELEVATION
		// If it is a composite-type object (value)
		else if (isContainerTy(UTy)) {
			// We also collect the containter types, as using the
			// containter type for matching can improve the precision
			TargetTypes.insert(UTy);
			// Record allocations
			TargetDataAllocModules[typeHash(UTy)].insert(M);
		}
#endif
		// Special handling for function pointers and external globals
		else if (PointerType *PTy = dyn_cast<PointerType>(UTy)) {
			if (auto GO = dyn_cast<GlobalVariable>(U)) {

				if (GO->hasInitializer()) {
					LU.push_back(GO->getInitializer());
				} else {
					auto EGV = Ctx->Gobjs[GO->getGUID()];
					if (!EGV)
						continue;
					const Module *EM = EGV->getParent();

					typeset_t &ExternalTypes = ParsedGlobalTypesMap[GV];
					findTargetTypesInInitializer(EGV, EM, ExternalTypes);

					for (auto Ty : ExternalTypes) {
						size_t TyH = typeHash(Ty);
						// Must use type hash, as Type * is specific to a module
						// As this is in initializer, there is no load from the GV
						moPropMap[make_pair(M, TyH)].insert(EM);
					}

				}
			} else if (isa<Function>(U)) {
				Type *ETy = PTy->getPointerElementType();
				TargetTypes.insert(ETy);
			}
			continue;
		}

		// Go through each field/operand
		for (auto oi = U->op_begin(), oe = U->op_end();
				oi != oe; ++oi) {

			const Value *O = *oi;
			Type *OTy = O->getType();
			if (PointerType *POTy = dyn_cast<PointerType>(OTy)) {

				if (isa<ConstantPointerNull>(O))
					continue;

				Type *ETy = POTy->getPointerElementType();

				if (isTargetTy(ETy)) {
					TargetTypes.insert(ETy);

					// Record allocations
					TargetDataAllocModules[typeHash(UTy)].insert(M);

					if (ETy->isFunctionTy()) {
						auto F = dyn_cast<Function>(O);
						if (F && F->isDeclaration())
							storedTypeIdxMap[M][UTy].insert(oi->getOperandNo());
					}
					continue;

				} else if (auto CO = dyn_cast<BitCastOperator>(O)) {

					auto OU = dyn_cast<User>(CO->getOperand(0));
					LU.push_back(OU);
					continue;

				} else if (auto GO = dyn_cast<GEPOperator>(O)){

					auto OU = dyn_cast<User>(GO->getOperand(0));
					LU.push_back(OU);
					continue;

				} else if (auto GO = dyn_cast<GlobalVariable>(O)) {
					// A GlobalVariable can be a composite type
					// TODO
					if (!GO->hasInitializer()) {
						// If it is an external initializer, record it
						storedTypeIdxMap[M][UTy].insert(oi->getOperandNo());
					}
					LU.push_back(GO);
					continue;

				}
			}

			auto OU = dyn_cast<User>(O);
			if (OU)
				LU.push_back(OU);
		}
	}

	// Process the type propagations
	for (auto Ty : TargetTypes) {
		addModuleToGVType(Ty, M, GV);
	}

	ParsedGlobalTypesMap[GV] = TargetTypes;
}

// Collect types from reads and writes against a value 
bool TyPM::parseUsesOfValue(const Value *V, typeset_t &ReadTypes,
		typeset_t &WrittenTypes, const Module *M) {

#ifndef PARSE_VALUE_USES
	return false;
#endif

	deque<const Value*>LV;
	LV.push_back(V);
	visited_t Visited;

	while (!LV.empty()) {
		auto CV = LV.front();
		LV.pop_front();
		if (Visited.find(CV) != Visited.end())
			continue;
		Visited.insert(CV);

		if (!isa<PointerType>(CV->getType()) && 
				!CV->getType()->isIntegerTy(64))
			continue;

		for (auto I : CV->users()) {

			Type *Ty = I->getType();

			// 
			// Just continue the tracking for the following cases
			//
			if (Operator::getOpcode(I) == Instruction::GetElementPtr) {
				// GEP Instruction cast into V
				LV.push_back(I);
			}

			else if (Operator::getOpcode(I) == Instruction::BitCast) {
				// Cast Instruction into GV
				LV.push_back(I);
			}
			else if (auto PIO = dyn_cast<PtrToIntOperator>(I)) {
				LV.push_back(I);
			}

			//
			// Handle store and loads
			//
			else if (auto SI = dyn_cast<StoreInst>(I)) {

				// Value operand
				auto VO = SI->getValueOperand();
				auto PO = SI->getPointerOperand();
				// Store something to the value
				if (PO == CV) { 
					typeset_t TySet;
					findTargetTypesInValue(VO, TySet, M);
					for (auto FTy : TySet)
						WrittenTypes.insert(FTy);
				}
				// The pointer is stored to else where, and we need to keep
				// track of the new location
				else {
					// Assume it is escaping?
					return false;

				}
			}
			else if (auto LI = dyn_cast<LoadInst>(I)) {
				Type *Ty = LI->getType();
				if (PointerType *PTy = dyn_cast<PointerType>(LI->getType())) {
					Type *ETy = PTy->getPointerElementType();
					if (isTargetTy(ETy)) {
						ReadTypes.insert(ETy);
					}
				}
				LV.push_back(LI);
			}

			// 
			// Handling calls with conservative policy: Assume escaping if
			// the pointer is passed to function in other modules
			//
			else if (auto CI = dyn_cast<CallInst>(I)) {

				// No, maybe just assume it is not parsable if the value is
				// passed to a call
				return false;

#if 0
				for (auto CF : Ctx->Callees[CI]) {
					if (!CF) continue;
					// Keep tracking if it is in the same module
					if (CF->getParent() == M) {
						int8_t ArgNo = getArgNoInCall(CI, CV);
						if (ArgNo != -1) {
							if (auto Arg = getParamByArgNo(CF, ArgNo)) {
								LV.push_back(Arg);
								continue;
							}
							else 
								continue;
						}
						else
							continue;
					}
					// Espacing case: Calling a function in another module
					else {
						typeset_t TySet;
						findTargetTypesInValue(CV, TySet, M);
						auto CalleeM = CF->getParent();
						for (auto FTy : TySet) {
							size_t FTH = typeHash(FTy);
							if (CI->isIndirectCall()) {
								if (!CF->onlyWritesMemory())
									moPropMapV[make_pair(CalleeM, FTH)].insert(M);
								if (!CF->onlyReadsMemory())
									moPropMapV[make_pair(M, FTH)].insert(CalleeM);
							}
							else {
								if (!CF->onlyWritesMemory())
									moPropMap[make_pair(CalleeM, FTH)].insert(M);
								if (!CF->onlyReadsMemory())
									moPropMap[make_pair(M, FTH)].insert(CalleeM);
							}
						}
					}
				}
#endif
			}
			// 
			// Other cases
			//
			else {
				// ?
			}
		}
	}
	return true;
}


// Parse stores and loads against a global
void TyPM::parseUsesOfGV(const GlobalVariable *GV, const Value *V, 
		const Module *M, visited_t &Visited) {

	if (Visited.find(V) != Visited.end())
		return;
	Visited.insert(V);

	for (auto I : V->users()) {

		if (auto SI = dyn_cast<StoreInst>(I)) {

			// Value operand
			auto VO = SI->getValueOperand();
			auto PO = SI->getPointerOperand();
			// Store something to the global
			if (PO == V) {
				Type *PTy = dyn_cast<PointerType>(VO->getType());
				if (!PTy)
					continue;
				Type *ETy = PTy->getPointerElementType();
				if (isTargetTy(ETy)) {
					// Found a function pointer
					// Add the module of the function to map
					addModuleToGVType(ETy, M, GV);
#ifdef TYPE_ELEVATION
					typelist_t TyList;
					const Value *NextV;
					nextLayerBaseTypeWL(PO, TyList, NextV);
					//typeset_t TySet;
					//findTargetTypesInValue(GV, TySet, M);
					for (auto Ty : TyList) {
						addModuleToGVType(Ty.first, M, GV);
					}
#endif
				}
#ifdef TYPE_ELEVATION
				else if (isContainerTy(ETy)) {
					addModuleToGVType(ETy, M, GV);
				}
#endif
				else {
					typeset_t TySet;
					findTargetTypesInValue(VO, TySet, M);
					for (auto Ty : TySet) {
						addModuleToGVType(Ty, M, GV);
					}
				}
			}
			// The pointer is stored to else where, and we need to keep
			// track of the new location
			else {
				typeset_t TySet;
				findTargetTypesInValue(VO, TySet, M);
				for (auto Ty : TySet) {
					addModuleToGVType(Ty, M, GV);
					addGVToModuleType(Ty, GV, M);
				}
			}

		} 
		else if (auto LI = dyn_cast<LoadInst>(I)) {

			auto PO = LI->getPointerOperand();
			auto GO = dyn_cast<GEPOperator>(PO);
			if (!isa<GetElementPtrInst>(PO) && GO) {
				Type * ETy = 
					dyn_cast<PointerType>(GO->getOperand(0)
							->getType())->getPointerElementType();
				if (isTargetTy(ETy)) {
					addGVToModuleType(ETy, GV, M);
				}
#ifdef TYPE_ELEVATION
				else if (isContainerTy(ETy))
					addGVToModuleType(ETy, GV, M);
#endif
			}

			Type *Ty = LI->getType();
			if (PointerType *PTy = dyn_cast<PointerType>(LI->getType())) {

				Type *ETy = PTy->getPointerElementType();
				if (isTargetTy(ETy)) {
					addGVToModuleType(ETy, GV, M);
				}
#ifdef TYPE_ELEVATION
				else if (isContainerTy(ETy)) {
					addGVToModuleType(ETy, GV, M);
				}
#endif

				// TODO: nextLayerBaseType?
				visited_t Visited;
				Type *BTy = getBaseType(LI->getPointerOperand(), Visited);
				if (BTy && isContainerTy(BTy)) {
					addGVToModuleType(BTy, GV, M);
				}
			}
			parseUsesOfGV(GV, LI, M, Visited);
		}
		else if (auto GO = dyn_cast<GEPOperator>(I)) {
			// GEP Instruction cast into V
			Type *ETy = GO->getSourceElementType();
			if (isTargetTy(ETy)) {
				addGVToModuleType(ETy, GV, M);
			}
#ifdef TYPE_ELEVATION
			else if (isContainerTy(ETy)) 
				addGVToModuleType(ETy, GV, M);
#endif
			parseUsesOfGV(GV, I, M, Visited);

		} 
		else if (Operator::getOpcode(I) == Instruction::BitCast) {
			// Cast Instruction into GV
			parseUsesOfGV(GV, I, M, Visited);
		} 
		else if (auto Call = dyn_cast<CallInst>(I)) {
			auto EGV = Ctx->Gobjs[GV->getGUID()];
			if (EGV && EGV->hasInitializer()) {
				typeset_t TySet;
				findTargetTypesInInitializer(EGV, M, TySet);
				for (auto Ty : TySet) {
					addGVToModuleType(Ty, GV, M);
				}
			}
			continue;
		} 
		else {
			// ?
		}
	} // Iteration of uses
}


void TyPM::parseTargetTypesInCalls(const CallInst *CI, const Function *CF) {

	const Module *CallerM = CI->getModule();
	const Module *CalleeM = CF->getParent();

#if 0
	OP<<"@@ Cross-module call: "<<*CI<<"; "<<CF->getName()<<"\n\t"
		<<CallerM->getName()<<" ==> "<<CalleeM->getName()<<"\n";
#endif

	auto MP = make_pair(CallerM, CalleeM);
	for (auto AI = CF->arg_begin(), E = CF->arg_end(); AI != E; ++AI) {

		auto Arg = dyn_cast<Argument>(&*AI);

		// Can the arg pass a function pointer? If so which
		// type?
		Type *ATy = Arg->getType();
		size_t HTy = typeHash(ATy);

		// The arg itself is a target type
		if (isTargetTy(ATy)) {
			addPropagation(CalleeM, CallerM, ATy, CI->isIndirectCall());
		}
		else if (PointerType *PTy = dyn_cast<PointerType>(ATy)){
			Type *ETy = PTy->getPointerElementType();
			if (isTargetTy(ETy)) {

				// First handle implicit flows where functions are
				// used as function arguments
				auto CI_Arg = CI->getArgOperand(AI - CF->arg_begin()); 
				if (auto AF = dyn_cast<Function>(CI_Arg)) {
					if (AF->isDeclaration())
						AF = Ctx->Funcs[AF->getGUID()];
					if (AF) {
						addPropagation(CallerM, AF->getParent(), 
								ETy, CI->isIndirectCall());
					}
				}

				addPropagation(CalleeM, CallerM, ETy, CI->isIndirectCall());
			}
		}

		typeset_t ReadTypes, WrittenTypes;
		bool UseParsable = parseUsesOfValue(Arg, ReadTypes,
				WrittenTypes, CF->getParent());

		if (UseParsable) {
#ifdef FLOW_DIRECTION
			if (!CF->onlyWritesMemory()) {
#endif
				for (auto FTy : ReadTypes) {
					addPropagation(CalleeM, CallerM, FTy, CI->isIndirectCall());
				}
#ifdef FLOW_DIRECTION
			}
#endif
#ifdef FLOW_DIRECTION
			if (!CF->onlyReadsMemory()) {
#endif
				for (auto FTy : WrittenTypes) {
					addPropagation(CallerM, CalleeM, FTy, CI->isIndirectCall());
				}
#ifdef FLOW_DIRECTION
			}
#endif
		}

		else {

			// Avoid repeatation for performance
			if (CI->isIndirectCall()) {
				if (ParsedModuleTypeICallMap[MP].find(ATy) 
						!= ParsedModuleTypeICallMap[MP].end())
					continue;
				ParsedModuleTypeICallMap[MP].insert(ATy);
			}
			else {
				if (ParsedModuleTypeDCallMap[MP].find(ATy) 
						!= ParsedModuleTypeDCallMap[MP].end())
					continue;
				ParsedModuleTypeDCallMap[MP].insert(ATy);
			}


#if 1
			typeset_t TySet;
			findTargetTypesInValue(Arg, TySet, CalleeM);
			// The callee function may read
#ifdef FLOW_DIRECTION
			if (!CF->onlyWritesMemory()) {
#endif

				for (auto FTy : TySet) {
					addPropagation(CalleeM, CallerM, FTy, CI->isIndirectCall());
				}
#ifdef FLOW_DIRECTION
			}
#endif

			// The callee function may write
#ifdef FLOW_DIRECTION
			if (!CF->onlyReadsMemory()) {
#endif

				for (auto FTy : TySet) {
					addPropagation(CallerM, CalleeM, FTy, CI->isIndirectCall());
				}
#ifdef FLOW_DIRECTION
			}
#endif
#endif
		}
	}

	// Parsing return values

	Type *RTy = CI->getType();

	typeset_t ReadTypes, WrittenTypes;
	bool UseParsable = parseUsesOfValue(CI, ReadTypes, WrittenTypes, 
			CI->getFunction()->getParent());

	if (UseParsable) {
#ifdef FLOW_DIRECTION
		if (!CI->getFunction()->onlyWritesMemory()) {
#endif
			for (auto FTy : ReadTypes) {
				addPropagation(CallerM, CalleeM, FTy, CI->isIndirectCall());
			}
#ifdef FLOW_DIRECTION
		}
#endif
#ifdef FLOW_DIRECTION
		if (!CI->getFunction()->onlyReadsMemory()) {
#endif
			for (auto FTy : WrittenTypes) {
				addPropagation(CalleeM, CallerM, FTy, CI->isIndirectCall());
			}
#ifdef FLOW_DIRECTION
		}
#endif
	}

	else {
		// Avoid repeatation for performance
		if (CI->isIndirectCall()) {
			if (ParsedModuleTypeICallMap[MP].find(RTy) 
					!= ParsedModuleTypeICallMap[MP].end())
				return;
			ParsedModuleTypeICallMap[MP].insert(RTy);
		}
		else {
			if (ParsedModuleTypeDCallMap[MP].find(RTy) 
					!= ParsedModuleTypeDCallMap[MP].end())
				return;
			ParsedModuleTypeDCallMap[MP].insert(RTy);
		}

		typeset_t TySet;
		findTargetTypesInValue(CI, TySet, CallerM);
		for (auto FTy : TySet) {

#ifdef FLOW_DIRECTION
			if (!CI->getFunction()->onlyWritesMemory()) {
#endif
				addPropagation(CallerM, CalleeM, FTy, CI->isIndirectCall());
#ifdef FLOW_DIRECTION
			}
#endif
#ifdef FLOW_DIRECTION
			else if (!CI->getFunction()->onlyReadsMemory()) {
#endif
				addPropagation(CalleeM, CallerM, FTy, CI->isIndirectCall());
#ifdef FLOW_DIRECTION
			}
#endif
		}
	}
}

void TyPM::findTargetTypesInValue(const Value *V, typeset_t &TargetTypes,
		const Module *M) {

	Type *VTy = V->getType();
	// Check cached results
	if (ParsedTypeMap.find(make_pair(M, VTy)) 
			!= ParsedTypeMap.end()) {
		TargetTypes = ParsedTypeMap[make_pair(M, VTy)];
		return;
	}

	deque<Type*> LT; 
	LT.push_back(VTy);
	SmallPtrSet<Type*, 8> Visited;

	while (!LT.empty()) {
		Type *Ty = LT.front();
		LT.pop_front();
		if (Visited.find(Ty) != Visited.end()) {
			// TODO: Why can this happen?
			continue;
		}
		Visited.insert(Ty);

		// Handle the current type
		if (isTargetTy(Ty)) {
			TargetTypes.insert(Ty);
		}
#ifdef TYPE_ELEVATION
		else if (isContainerTy(Ty)) {
			TargetTypes.insert(Ty);
		}
#endif

		// Handle pointer type
		PointerType *PTy = dyn_cast<PointerType>(Ty);
		if (PTy) {

			// Handling general pointers (void *, char *) that can
			// also pass function pointers
			if (PTy == Int8PtrTy[M]) {
				TargetTypes.insert(Int8PtrTy[M]);
			}
			else 
				// Continue with the element type
				LT.push_back(PTy->getPointerElementType());

			// Also track types with cast relation to it
#if 1
			for (auto CastTy : CastFromMap[M][Ty]) {
				LT.push_back(CastTy);
			}
			for (auto CastTy : CastToMap[M][Ty]) {
				LT.push_back(CastTy);
			}
#endif
		}
		// Handle composite type
		else if (isContainerTy(Ty)) {
			for (Type::subtype_iterator I = Ty->subtype_begin(), 
					E = Ty->subtype_end();
					I != E; ++I) {
				Type *SubTy = (Type *)*I;

				LT.push_back(SubTy);
			}
		}
	}

	ParsedTypeMap[make_pair(M, VTy)] = TargetTypes;
	//for (auto FTy : TargetTypes) {
	//	OP<<*FTy<<"\n";
	//}
}



/////////////////////////////////////////////////////////////////////
//
// The following functions iterate through functions for various
// semsntics
//
/////////////////////////////////////////////////////////////////////

void TyPM::mapDeclToActualFuncs(FuncSet &FS) {
	for (auto F : FS) {
		if (!F) {
			FS.erase(F);
			continue;
		}
		if (F->isDeclaration()) {
			FS.erase(F);
			F = Ctx->Funcs[F->getGUID()];
			if (F) {
				FS.insert(F);
			}
		}
		else
			FS.insert(F);
	}
}

void TyPM::findTargetAllocInFunction(const Function * F) {

	for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		auto I = &*i;

		if (auto AI = dyn_cast<AllocaInst>(I)) {
			Type *Ty = AI->getAllocatedType();
			if (isTargetTy(Ty)) {
				TargetDataAllocModules[typeHash(Ty)].insert(F->getParent());
			}
		}
	}
}

// This function collect stores to fields of structs. This
// essentially collects structs that may be internally
// created/initialized in the function---a key step of the
// "externality analysis" of the type elevation
void TyPM::findStoredTypeIdxInFunction(const Function * F) {

	for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		auto I = &*i;

		if (auto SI = dyn_cast<StoreInst>(I)) {

			StoreInstSet.insert(SI);

			auto PO = SI->getPointerOperand();

			typelist_t TyList;
			const Value *NextV;
			nextLayerBaseTypeWL(PO, TyList, NextV);
			if (!TyList.empty()) {
				typeidx_t TI = TyList.front();
				storedTypeIdxMap[F->getParent()][TI.first].insert(TI.second);
				continue;
			}
			visited_t Visited;
			Type *BTy = getBaseType(PO, Visited);
			if (BTy) {
				storedTypeIdxMap[F->getParent()][BTy].insert(0);
				continue;
			}
		}
	}
}



/////////////////////////////////////////////////////////////////////
//
// The following are APIs for resolving dependent modules and targets
//
/////////////////////////////////////////////////////////////////////

void TyPM::getDependentModulesV(const Value* TV, const Module *M,
		modset_t &MSet) {

	Type *Ty = TV->getType();

	// Get the outermost layer type
	typelist_t TyList;
	const Value *CV = TV, *NextV;
	visited_t Visited;
	while (nextLayerBaseTypeWL(CV, TyList, NextV)) {
		Visited.insert(CV);
		if (Visited.find(NextV) != Visited.end()) {
			break;
		}
		CV = NextV;
	}

	typeidx_t Outermost = make_pair((Type *)NULL, -1);
	for (auto TyIdx : TyList) {
		
		// The assumption is that if a field of a struct type has
		// never been stored to in the module, it must be passed in
		// from the outside, and we can check cross-module dependence
		// for the struct type. Using the outermost (i.e., typically
		// the most unique) type allows us to get more precise results

		// FIXME: this may cause false negatives in Linux when the code
		// use "container_of" to access memory beyond the current object.
		// One solution is to identify the missed "cast" through GEP
		// instruction (with -1 indice)

		// FIXME: TODO: the following externality check should also
		// be applied to depedent modules to avoid potential false
		// negatives
		//
		// Externality check
		if (storedTypeIdxMap[M].find(TyIdx.first) 
				!= storedTypeIdxMap[M].end()) {
			if ((storedTypeIdxMap[M][TyIdx.first].find(TyIdx.second)
						!= storedTypeIdxMap[M][TyIdx.first].end())
					|| TyIdx.second == -1)
				break;
		}
		Outermost = TyIdx;
		break;
	}

#ifndef TYPE_ELEVATION // disable type elevation?
	Outermost.first = NULL;
#endif

	Type *TTy = Ty;
	if (Outermost.first) {
		TTy = Outermost.first;
		OP<<"@@ Elevated type: "<<*(Ty)<<" ==> "<<*(TTy)<<"\n";
		OP<<"@@ Field index: "<<Outermost.second<<"\n";
		while (TTy->isPointerTy())
			TTy = TTy->getPointerElementType();
	}
	else {
		while (TTy->isPointerTy())
			TTy = TTy->getPointerElementType();
	}

	auto TyM = make_pair(M, typeHash(TTy));
	if (ResolvedDepModulesMap.find(TyM)
			!= ResolvedDepModulesMap.end())
		MSet = ResolvedDepModulesMap[TyM];
	else {
		getDependentModulesTy(typeHash(TTy), M, MSet);
		ResolvedDepModulesMap[TyM] = MSet;
	}
	if (MSet.size() == 0 && isContainerTy(TTy)) {
		if (storedTypeIdxMap[M].find(TTy) == storedTypeIdxMap[M].end()) {
			modset_t &MSet = TargetDataAllocModules[typeHash(TTy)];
			if (MSet.find(M) == MSet.end()) {
				OP<<"!!! NO DEPENDENCE: "<<*TTy<<"\n";
				printSourceCodeInfo(TV, "TYPE-ERR");
			}
		}
	}
}


void TyPM::getDependentModulesTy(size_t TyH, const Module *M,
		modset_t &MSet) {

	//
	// Resolving dependent modules for M
	//

	modset_t PM;
	deque<const Module*> EM;
	EM.push_back(M);

	while (!EM.empty()) {
		auto TM = EM.front();
		EM.pop_front();
		// To test the presence of an element - find() in set, count() in multiset
		if (PM.find(TM) != PM.end())
			continue;
		PM.insert(TM);

		for (auto m : moPropMapAll[make_pair(TM, TyH)]) {
			MSet.insert(m);
			EM.push_back(m);
		}

		// Handling transitioning modules that can pass function
		// poitners, although there is no function type
		for (auto m : moPropMapAll[make_pair(TM, typeHash(Int8PtrTy[TM]))]) {
			// Simply continue to search related modules
			EM.push_back(m);
		}

	}
}

bool TyPM::resolveFunctionTargets() {

	uint64_t oldCount = 0, newCount = 0, outScopeCount = 0;
	uint64_t oldModuleCount = 0, newModuleCount = 0;

	for (auto CI : ICallSet) {

		oldCount += Ctx->Callees[CI].size();
		oldModuleCount += Ctx->Modules.size();
		auto CallerM = CI->getModule();
		// CallBase *CB = dyn_cast<CallBase>(CI);
		Type *FuncType = CI->getFunctionType(); 
		modset_t MSet;
		getDependentModulesV(CI->getCalledOperand(), CallerM, MSet);
		MSet.insert(CallerM);
		newModuleCount += MSet.size();

#ifdef PRINT_ICALL_TARGET
		printSourceCodeInfo(CI, "RESOLVING");
#endif
		for (auto Callee : Ctx->Callees[CI]) {
			auto CalleeM = Callee->getParent();
			if (MSet.find(CalleeM) != MSet.end()) {
				newCount += 1;
			}
			else {
				// Do not remove out-of-analysis-scope functions which
				// can still be valid targets
				string FN = Callee->getName().str();
				if ((OutScopeFuncNames.find(FN) 
							== OutScopeFuncNames.end())
						//&& (StoredFuncs.find(Callee) != StoredFuncs.end())
				   ) {

					Ctx->Callees[CI].erase(Callee);
#ifdef PRINT_ICALL_TARGET
					printSourceCodeInfo(Callee, "REMOVED");
#endif
				}
				else { 
					outScopeCount += 1;
				}
			}
		}
		mapDeclToActualFuncs(Ctx->Callees[CI]);
#ifdef PRINT_ICALL_TARGET
		printTargets(Ctx->Callees[CI], CI);
#endif
	}
	if (NumIndirectCallTargets > 0) {
		time_t my_time = time(NULL);
		OP<<"# TIME: "<<ctime(&my_time)<<"\n";
		cout<<"\n@@ Target Reduction: "
			<<newCount<<"/"<<oldCount<<"/"
			<<NumIndirectCallTargets<< ", Reduction Rate: "
			<<std::setprecision(5)
			<<((NumIndirectCallTargets - newCount)*(float)100)/NumIndirectCallTargets<<"\%\n";
	}
	if (oldModuleCount > 0) {
		cout<<"@@ Module Reduction: "
			<<newModuleCount<<"/"<<oldModuleCount<<", Reduction Rate: "
			<<std::setprecision(5)
			<<((oldModuleCount - newModuleCount)*(float)100)/oldModuleCount<<"\%\n\n";
	}
	cout<<"@@ Out-of-scope Count: "<<outScopeCount<<"\n\n";
	if (newCount + outScopeCount == oldCount) {
		// Done with the iteration
		return false;
	}
	return true;
}

bool TyPM::resolveStructTargets() {

	uint64_t oldCount = 0, newCount = 0, totalCount = 0;
	int criticalWrites = 0;

	int Progress = 0;
	for (auto SI : StoreInstSet) {
		++Progress;

		bool criticalType = false;
		auto PO = SI->getPointerOperand();
		typelist_t TyList;
		const Value *CV = PO, *NextV;
		visited_t Visited;
		while (nextLayerBaseTypeWL(CV, TyList, NextV)) {
			Visited.insert(CV);
			if (Visited.find(NextV) != Visited.end()) {
				break;
			}
			CV = NextV;
		}
		Type *TTy = NULL;
		for (auto TyIdx : TyList) {
			if (isTargetTy(TyIdx.first)) {
				TTy = TyIdx.first;
				criticalType = true;
				break;
			}
		}
		if (!TTy) {
			visited_t Visited;
			TTy = getBaseType(PO, Visited);
			if (TTy && isTargetTy(TTy)) {
				criticalType = true;
			}
		}
		if ((PO->getType() != Int8PtrTy[SI->getModule()]) 
				&& !criticalType)
			continue;

		// the remaining writes target either critical structures or
		// general pointers.
		// now, further resolve the dependences for them

		if (criticalType) {

			totalCount += Ctx->Modules.size();

			size_t TyH = typeHash(TTy);

			// Resolving dependences for TTy
			modset_t MSet;
			getDependentModulesTy(TyH, SI->getModule(), MSet);
			if (MSet.size() == 0)
				continue;
			for (auto tyh : TargetDataAllocModules[TyH]) {
				++oldCount;
				// Matched
				if (MSet.find(tyh) != MSet.end()) {
					++newCount;
				}
			}
		}

		// the following assumes that general pointer may also target
		// critical data structures and goes ahead to resove
		// dependences
#if 0
		else {
			totalCount += Ctx->Modules.size();
			for (size_t TyH : TTySet) {
				// Resolving dependences for TTy
				modset_t MSet;
				getDependentModules(TyH, SI->getModule(), MSet);
				if (MSet.size() == 0)
					continue;
				for (auto tyh : TargetDataAllocModules[TyH]) {
					++oldCount;
					// Matched
					if (MSet.find(tyh) != MSet.end()) {
						++newCount;
						criticalType = true;
					}
				}
				if (criticalType)
					break;
			}
		}
#endif
		if (criticalType)
			++criticalWrites;

		OP<<Progress<<" / "<<StoreInstSet.size()<<"\n";
	}

	time_t my_time = time(NULL);
	OP<<"# TIME: "<<ctime(&my_time)<<"\n";
	cout<<"@@ Total stores: "<<StoreInstSet.size()<<"\n";
	cout<<"@@ Critical stores: "<<criticalWrites<<"\n";
	cout<<"\n@@ Target Reduction: "
		<<newCount<<"/"<<oldCount<<"/"<<totalCount<<", Reduction Rate: "
		<<std::setprecision(5)
		<<((totalCount - newCount)*(float)100)/totalCount<<"\%\n";

	return false;
}

