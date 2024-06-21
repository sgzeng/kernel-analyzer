//===-- CallGraph.cc - Build global call-graph------------------===//
//
// This pass builds a global call-graph. The targets of an indirect
// call are identified based on type analysis. This is scope-aware
// and multi-layer type analysis.
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

#include <unordered_map>
#include <vector>
#include <pthread.h>

#include "TyPMCommon.h"
#include "TyPMConfig.h"
#include "TyPMPass.h"

#define TYPM_LOG(stmt) KA_LOG(2, "TyPM: " << stmt)
#define TYPM_DEBUG(stmt) KA_LOG(3, "TyPM: " << stmt)

using namespace llvm;

int ENABLE_MLTA = 0;
int ENABLE_TYDM = 1;
int MAX_PHASE_CG = 2;

static void LoadTraces(map<size_t, set<size_t>> &hashedTraces,
		map<size_t, SrcLn> &hashSrcMap) {

	string exepath = sys::fs::getMainExecutable(NULL, NULL);
	string exedir = exepath.substr(0, exepath.find_last_of('/'));
	string line;
#ifdef EVAL_FN_FIRFOX
	ifstream tracefile(exedir + "/../../data/traces-ff.list");
#else 
	ifstream tracefile(exedir + "/../../data/traces.list");
#endif

	SrcLn CallerSrcLn("", 0);
	SrcLn CalleeSrcLn("", 0);
	if (tracefile.is_open()) {
		while (!tracefile.eof()) {
			getline (tracefile, line);
			if (line.length() == 0)
				continue;
			size_t pos = line.find("CALLER:");
			if (pos != string::npos) {
				line = line.substr(pos + 8);
				pos = line.rfind(":");
				if (pos == string::npos) {
					CallerSrcLn.Ln = -1;
					continue;
				}
				CallerSrcLn.Ln = stoi(line.substr(pos + 1));
				CallerSrcLn.Src = line.substr(0, pos);
#ifdef EVAL_FN_FIRFOX
				pos = CallerSrcLn.Src.find("gecko-dev");
				if (pos != string::npos)
					CallerSrcLn.Src = CallerSrcLn.Src.substr(pos + 10);
#endif
				hashSrcMap[strIntHash(CallerSrcLn.Src, CallerSrcLn.Ln)] = CallerSrcLn;

				continue;
			}
			pos = line.find("CALLEE:");
			if (pos != string::npos) {
				if (CallerSrcLn.Ln == -1)
					continue;

				line = line.substr(pos + 8);
				pos = line.rfind(":");
				if (pos == string::npos)
					continue;
				CalleeSrcLn.Ln = stoi(line.substr(pos + 1));
				CalleeSrcLn.Src = line.substr(0, pos);
#ifdef EVAL_FN_FIRFOX
				pos = CalleeSrcLn.Src.find("gecko-dev");
				if (pos != string::npos) {
					CalleeSrcLn.Src = CalleeSrcLn.Src.substr(pos + 10);
				}
#endif
				// Assume every callee is preceded with a caller
				size_t callerhash = strIntHash(CallerSrcLn.Src, CallerSrcLn.Ln);
				size_t calleehash = strIntHash(CalleeSrcLn.Src, CalleeSrcLn.Ln);
				hashedTraces[callerhash].insert(calleehash);
				hashSrcMap[calleehash] = CalleeSrcLn;

				continue;
			}
		}
		tracefile.close();
	}
}


//
// Static variables
//
int TyPMCGPass::AnalysisPhase = 1;

//
// Implementation
//

void TyPMCGPass::PhaseMLTA(Function *F) {

	// Unroll loops
#ifdef UNROLL_LOOP_ONCE
	unrollLoops(F);
#endif

	TYPM_LOG("PhaseMLTA: " << F->getName() << "\n");

	// Collect callers and callees
	for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
		// Map callsite to possible callees.
		if (CallInst *CI = dyn_cast<CallInst>(&*i)) {

			CallSet.push_back(CI);

			FuncSet &FS = MLTA::Ctx->Callees[CI];
			const Value *CV = CI->getCalledOperand();
			const Function *CF = dyn_cast<Function>(CV);

			// Indirect call
			if (CI->isIndirectCall()) {

				// Multi-layer type matching
				findCalleesWithMLTA(CI, FS);

				for (auto Callee : FS) {
					TYPM_DEBUG("Found ICALLEE: " << Callee->getName() << "\n");
					MLTA::Ctx->Callers[Callee].insert(CI);
				}

				// Save called values for future uses.
				MLTA::Ctx->IndirectCallInsts.push_back(CI);

				ICallSet.push_back(CI);
				if (!FS.empty()) {
					MatchedICallSet.push_back(CI);
					NumIndirectCallTargets += FS.size();
					NumValidIndirectCalls++;
				}
			}
			// Direct call
			else {
				// not InlineAsm
				if (CF) {
					// Call external functions
					if (CF->isDeclaration()) {
						//StringRef FName = CF->getName();
						//if (FName.startswith("SyS_"))
						//	FName = StringRef("sys_" + FName.str().substr(4));
						CF = getFuncDef(CF);
					}

					FS.insert(CF);
					MLTA::Ctx->Callers[CF].insert(CI);
				}
				// InlineAsm
				else {
					// TODO: handle InlineAsm functions
				}
			}
		}
	}
}

void TyPMCGPass::PhaseTyPM(Function *F) {

	TYPM_LOG("PhaseTyPM: " << F->getName() << "\n");

	for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {

		//
		// Step 1: Collect data flows among modules
		//

		// Note: the following impl is not type-aware yet
		// Collect data flows through functions calls
		CallInst *CI = dyn_cast<CallInst>(&*i);
		if (!CI)
			continue;

		if (CI->arg_empty())
			continue;

		// Indirect call
		if (CI->isIndirectCall()) {

			for (auto CF : MLTA::Ctx->Callees[CI]) {
				// Need to use the actual function with body here
				CF = getFuncDef(CF);
				if (CF->isDeclaration()) {
					continue;
				}
				if (CF->doesNotAccessMemory())
					continue;

				parseTargetTypesInCalls(CI, CF);
			}
		}

		// Direct call, no need to repeat for following iterations
		else if (AnalysisPhase == 2) {
			// NOTE: Do not use getCalledFunction as it can only return
			// function within the module
			Value *CO = CI->getCalledOperand();
			if (!CO) {
				continue;
			}

			const Function *CF = dyn_cast<Function>(CO);
			if (!CF || CF->isIntrinsic()) {
				// Likely it is ASM code
				continue;
			}
			CF = getFuncDef(CF);
			// Need to use the actual function with body here
			if (CF->isDeclaration()) {
				// Have to skip it as the function body is not in
				// the analysis scope
				continue;
			}
			if (CF->doesNotAccessMemory())
				continue;

			parseTargetTypesInCalls(CI, CF);
		}
	}
}

bool TyPMCGPass::doInitialization(Module *M) {

	TYPM_LOG("#" << MIdx << " Initializing: " << M->getName() << "\n");

	++MIdx;

	DLMap[M] = &(M->getDataLayout());
	Int8PtrTy[M] = Type::getInt8PtrTy(M->getContext());
	assert(Int8PtrTy[M]);
	IntPtrTy[M] = DLMap[M]->getIntPtrType(M->getContext());

	userset_t CastSet;

	//
	// Iterate and process globals
	//
	for (Module::global_iterator gi = M->global_begin();
			gi != M->global_end(); ++gi) {

		GlobalVariable* GV = &*gi;
		if (GV->hasInitializer()) {

			Type *ITy = GV->getInitializer()->getType();
			if (!ITy->isPointerTy() && !isContainerTy(ITy))
				continue;

			// Parse the initializer
			unordered_set<Type*> TySet;
			findTargetTypesInInitializer(GV, M, TySet);

			typeConfineInInitializer(GV);

			// Collect all casts in the global variable
			findCastsInGV(GV, CastSet);
		}
	}

	// Iterate functions and instructions
	for (Function &F : *M) {

		// Do not include LLVM intrinsic functions?
		if (F.isIntrinsic()) {
			continue;
		}

		// Collect address-taken functions.
		// NOTE: declaration functions can also have address taken
		if (F.hasAddressTaken()) {
			auto RF = getFuncDef(&F);
			MLTA::Ctx->AddressTakenFuncs.insert(RF);
			size_t FuncHash = funcHash(&F, false);
			MLTA::Ctx->FuncSigs[FuncHash].insert(RF);
			StringRef FName = F.getName();
			// The following functions are not in the analysis scope
			if (FName.startswith("__x64") ||
					FName.startswith("__ia32") ||
					FName.startswith("__do_sys")) {
				OutScopeFuncNames.insert(F.getName().str());
			}
		}

		// The following only considers actual functions with body
		if (F.isDeclaration()) {
			continue;
		}
		++NumFunctions;


		//
		// MLTA and TyPM
		//
		typePropInFunction(&F);

		collectAliasStructPtr(&F);
		typeConfineInFunction(&F);

		// Collect all casts in the function
		findCastsInFunction(&F, CastSet);

		// Handle casts
		processCasts(CastSet, M);

		// Collect all stores against fields of composite types in the
		// function
		findStoredTypeIdxInFunction(&F);

		// Collection allocations of critical data structures
		findTargetAllocInFunction(&F);
	}

	if (MIdx == MLTA::Ctx->Modules.size()) {
		MIdx = 0;
	}

	return false;
}

bool TyPMCGPass::doFinalization(Module *M) {

	++ MIdx;
	if (MLTA::Ctx->Modules.size() == MIdx) {
		// Finally map declaration functions to actual functions
		TYPM_LOG("Mapping declaration functions to actual ones...\n");
		NumIndirectCallTargets = 0;
		for (auto CI : CallSet) {
			mapDeclToActualFuncs(MLTA::Ctx->Callees[CI]);

			if (CI->isIndirectCall()) {
				NumIndirectCallTargets += MLTA::Ctx->Callees[CI].size();
				printTargets(MLTA::Ctx->Callees[CI], CI);
			}
		}
	}

	TYPM_LOG("############## Result Statistics ##############\n");
	TYPM_LOG("# Number of indirect calls: \t\t\t" << MLTA::Ctx->IndirectCallInsts.size() << "\n");
	TYPM_LOG("# Number of indirect calls with targets: \t" << NumValidIndirectCalls << "\n");
	TYPM_LOG("# Number of indirect-call targets: \t\t" << NumIndirectCallTargets << "\n");
	TYPM_LOG("# Number of address-taken functions: \t\t" << MLTA::Ctx->AddressTakenFuncs.size() << "\n");
	TYPM_LOG("# Number of second layer calls: \t\t" << NumSecondLayerTypeCalls << "\n");
	TYPM_LOG("# Number of second layer targets: \t\t" << NumSecondLayerTargets << "\n");
	TYPM_LOG("# Number of first layer calls: \t\t\t" << NumFirstLayerTypeCalls << "\n");
	TYPM_LOG("# Number of first layer targets: \t\t" << NumFirstLayerTargets << "\n");

	return false;
}

bool TyPMCGPass::doModulePass(Module *M) {

	++ MIdx;
	TYPM_LOG("Module [" << MIdx << "/" << MLTA::Ctx->Modules.size() << "]\n");

	//
	// Iterate and process globals
	//
	for (Module::global_iterator gi = M->global_begin();
			gi != M->global_end(); ++gi) {

		GlobalVariable* GV = &*gi;

		Type *GTy = GV->getType();
		assert(GTy->isPointerTy());

		if (AnalysisPhase == 1) {

#ifdef PARSE_VALUE_USES
			// Parse its uses
			visited_t Visited;
			parseUsesOfGV(GV, GV, M, Visited);
#else

			if (!GV->hasInitializer()) {
				GV = MLTA::Ctx->Gobjs[GV->getGUID()];
				if (!GV) {
					continue;
				}
			}

			typeset_t TySet;
			findTargetTypesInValue(GV->getInitializer(), TySet, M);
			for (auto Ty : TySet) {

				// TODO: can be optimized for better precision: either from
				// or to
				size_t TyH = typeHash(Ty);
				TypesFromModuleGVMap[make_pair(GV->getGUID(), TyH)].insert(M);
				TypesToModuleGVMap[make_pair(GV->getGUID(), TyH)].insert(M);
			}

#endif

		}
	}
	if (MIdx == MLTA::Ctx->Modules.size()) {
		// Use globals to connect modules
		for (auto GMM : TypesToModuleGVMap) {
			for (auto DstM : GMM.second) {
				size_t TyH = GMM.first.second;
				moPropMap[make_pair(DstM, TyH)].insert(
						TypesFromModuleGVMap[GMM.first].begin(),
						TypesFromModuleGVMap[GMM.first].end());
			}
		}
#if 0
		for (auto m : moPropMap)
			for (auto m1 : m.second)
				TYPM_LOG("@@ dependence " << m1->getName()
					<< " ==> " << m.first.first->getName()
					<< " HASH: " << m.first.second << "\n");
#endif
	}

	//
	// Process functions
	//
	for (auto f = M->begin(), fe = M->end(); f != fe; ++f) {

		auto F = &*f;

		if (F->isDeclaration() || F->isIntrinsic())
			continue;

		// Phase 1: Multi-layer type analysis
		if (AnalysisPhase == 1) {
			PhaseMLTA(F);
		} else {
			// Phase 2-to-n: Modular type analysis
			// TODO: only iterate over indirect calls
			PhaseTyPM(F);
		}
	}

	// Analysis phase control
	if (MLTA::Ctx->Modules.size() == MIdx) {

		if (AnalysisPhase == 2) {
			//
			// Clear no longer useful structures
			//
			GVFuncTypesMap.clear();
			TypesFromModuleGVMap.clear();
			TypesToModuleGVMap.clear();
		}

		if (AnalysisPhase >= 2) {

			ResolvedDepModulesMap.clear();
			bool Iter = true;
			// Merge the propagation maps
			moPropMapAll.insert(moPropMap.begin(), moPropMap.end());
			// Add map one by one to avoid overwritting
			for (auto m : moPropMapV) {
				moPropMapAll[m.first].insert(m.second.begin(), m.second.end());
			}

			// TODO: multi-threading for better performance

			//
			// Steps 2 and 3 of TyPM: Collecting depedent modules
			// and resolving targets within  on dependent modules
			//
#ifdef FUNCTION_AS_TARGET_TYPE
			bool NextIter = resolveFunctionTargets();
#else // struct as target type
			bool NextIter = resolveStructTargets();
#endif

			if (!NextIter) {
				// Done with the iteration
				MIdx = 0;
				return false;
			}

			// Reset the map when phase >= 2
			moPropMapV.clear();
			moPropMapAll.clear();
			ParsedModuleTypeICallMap.clear();
			ParsedModuleTypeDCallMap.clear();
		}

		++AnalysisPhase;
		MIdx = 0;
		if (AnalysisPhase <= MAX_PHASE_CG) {
			TYPM_LOG("\n\n=== Move to phase " << AnalysisPhase << " ===\n\n");
			return true;
		} else {
			TYPM_LOG("\n=== Done " << MAX_PHASE_CG << "===\n");
		}
	}

	return false;
}

void TyPMCGPass::processResults() {

	// Load traces for evaluation
	// Key: hash of SrcLn for caller
	map<size_t, set<size_t>> hashedTraces;
	map<size_t, SrcLn> hashSrcMap;
	LoadTraces(hashedTraces, hashSrcMap);
	size_t TraceCount = 0;
	for (auto T : hashedTraces) {
		TraceCount += T.second.size();
	}
	OP<<"@@ Trace size: "<<TraceCount<<"\n";


	for (auto T : hashedTraces) {
		if (calleesSrcMap.find(T.first) == calleesSrcMap.end())
			continue;
		for (auto calleehash : T.second) {
			if (srcLnHashSet.find(calleehash) == srcLnHashSet.end())
				continue;
			if (addrTakenFuncHashSet.find(calleehash) == 
					addrTakenFuncHashSet.end())
				continue;
			if (calleesSrcMap[T.first].count(calleehash)) {
				// the callee is in the target set
				SrcLn Caller = hashSrcMap[T.first];
				OP<<"@ Found callee for: "<<Caller.Src<<" +"<<Caller.Ln<<"\n";
			}
			else if (L1CalleesSrcMap[T.first].count(calleehash)){
				// false negative
				OP<<"!! Cannot find callee\n";
				SrcLn Caller = hashSrcMap[T.first];
				SrcLn Callee = hashSrcMap[calleehash];
				OP<<"@ Caller: "<<Caller.Src<<" +"<<Caller.Ln<<"\n";
				OP<<"\t@ Callee: "<<Callee.Src<<" +"<<Callee.Ln<<"\n";
			}
		}
	}
}
