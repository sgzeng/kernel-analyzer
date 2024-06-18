#ifndef _MULTI_LAYER_TYPE_ANALYSIS_H
#define _MULTI_LAYER_TYPE_ANALYSIS_H

#include "Global.h"
#include "TyPMConfig.h"
#include "llvm/IR/Operator.h"


class MLTA {

	protected:

		typedef pair<Type *, int> typeidx_t;
		typeidx_t typeidx_c(Type *Ty, int Idx);
		typedef pair<size_t, int> hashidx_t;
		hashidx_t hashidx_c(size_t Hash, int Idx);


		// Statistics 
		unsigned NumFunctions = 0;
		unsigned NumFirstLayerTypeCalls = 0;
		unsigned NumSecondLayerTypeCalls = 0;
		unsigned NumSecondLayerTargets = 0;
		unsigned NumValidIndirectCalls = 0;
		unsigned NumIndirectCallTargets = 0;
		unsigned NumFirstLayerTargets = 0;


		//
		// Variables
		//

		GlobalContext *Ctx;


		////////////////////////////////////////////////////////////////
		// Important data structures for type confinement, propagation,
		// and escapes.
		////////////////////////////////////////////////////////////////
		DenseMap<size_t, unordered_map<int, FuncSet>> typeIdxFuncsMap;
		unordered_map<size_t, unordered_map<int, set<hashidx_t>>> typeIdxPropMap;
		unordered_set<size_t> typeEscapeSet;
		// Cap type: We cannot know where the type can be futher
		// propagated to. Do not include idx in the hash
		unordered_set<size_t> typeCapSet;


		////////////////////////////////////////////////////////////////
		// Other data structures
		////////////////////////////////////////////////////////////////
		// Cache matched functions for CallInst
		DenseMap<size_t, FuncSet> MatchedFuncsMap;
		DenseMap<const Value*, FuncSet> VTableFuncsMap;

		std::unordered_set<size_t> srcLnHashSet;
		unordered_set<size_t> addrTakenFuncHashSet;

		unordered_map<size_t, set<size_t>> calleesSrcMap;
		unordered_map<size_t, set<size_t>> L1CalleesSrcMap;

		// Matched icall types -- to avoid repeatation
		DenseMap<size_t, FuncSet> MatchedICallTypeMap;

		// Set of target types
		unordered_set<size_t> TTySet;

		// Functions that are actually stored to variables
		FuncSet StoredFuncs;

		// Alias struct pointer of a general pointer
		unordered_map<const Function*, unordered_map<const Value*, const Value*>> AliasStructPtrMap;


		//
		// Methods
		//

		////////////////////////////////////////////////////////////////
		// Type-related basic functions
		////////////////////////////////////////////////////////////////
		typedef SmallPtrSet<const Value*, 8> visited_t;
		typedef vector<typeidx_t> typelist_t;

		bool fuzzyTypeMatch(Type *Ty1, Type *Ty2, const Module *M1, const Module *M2);

		void escapeType(const Value *V);
		void propagateType(const Value *ToV, Type *FromTy, int Idx = -1);

		Type *getBaseType(const Value *V, visited_t &Visited);
		Type *_getPhiBaseType(const PHINode *PN, visited_t &Visited);
		const Function *getBaseFunction(const Value *V);
		bool nextLayerBaseType(const Value *V, typelist_t &TyList, 
				const Value* &NextV, visited_t &Visited);
		bool nextLayerBaseTypeWL(const Value *V, typelist_t &TyList, 
				const Value* &NextV);
		bool getGEPLayerTypes(const GEPOperator *GEP, typelist_t &TyList);
		bool getBaseTypeChain(typelist_t &Chain, const Value *V, 
				bool &Complete);
		bool getDependentTypes(Type *Ty, int Idx, set<hashidx_t> &PropSet);


		////////////////////////////////////////////////////////////////
		// Target-related basic functions
		////////////////////////////////////////////////////////////////
		void confineTargetFunction(const Value *V, const Function *F);
		void intersectFuncSets(FuncSet &FS1, FuncSet &FS2,
				FuncSet &FS); 
		bool typeConfineInInitializer(const GlobalVariable *GV);
		bool typeConfineInFunction(const Function *F);
		bool typePropInFunction(const Function *F);
		void collectAliasStructPtr(const Function *F);

		// deprecated
		//bool typeConfineInStore(StoreInst *SI);
		//bool typePropWithCast(User *Cast);
		const Value *getVTable(const Value *V);


		////////////////////////////////////////////////////////////////
		// API functions
		////////////////////////////////////////////////////////////////
		// Use type-based analysis to find targets of indirect calls
		void findCalleesWithType(const CallInst*, FuncSet&);
		bool findCalleesWithMLTA(const CallInst *CI, FuncSet &FS);
		bool getTargetsWithLayerType(size_t TyHash, int Idx,
				FuncSet &FS);


		////////////////////////////////////////////////////////////////
		// Util functions
		////////////////////////////////////////////////////////////////
		bool isCompositeType(Type *Ty);
		Type *getFuncPtrType(const Value *V);
		const Value *recoverBaseType(const Value *V);
		Type *getRealType(const Value *V);
		const BasicBlock* getParentBlock(const Value* V);

		void unrollLoops(Function *F);
		void saveCalleesInfo(const CallInst *CI, FuncSet &FS, bool mlta);
		void printTargets(FuncSet &FS, const CallInst *CI = NULL);
		void printTypeChain(typelist_t &Chain);


	public:

		// General pointer types like char * and void *
		unordered_map<const Module*, Type*> Int8PtrTy;
		// long interger type
		unordered_map<const Module*, Type*> IntPtrTy;
		unordered_map<const Module*, const DataLayout*> DLMap;

		MLTA(GlobalContext *Ctx_) {
			Ctx = Ctx_;
		}

};

#endif
