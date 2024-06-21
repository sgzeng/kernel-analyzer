#ifndef _TYPE_BASED_DEPENDENCE_MODULARIZATION_H
#define _TYPE_BASED_DEPENDENCE_MODULARIZATION_H

#include "Global.h"
#include "MLTA.h"
#include "TyPMConfig.h"


class TyPM : public MLTA {

	private:

		//////////////////////////////////////////////////////////
		//
		// Define target types
		//
		//////////////////////////////////////////////////////////

		void LoadTargetTypes(unordered_set<size_t> &TTySet) {

			hash<string> str_hash;
			string exepath = sys::fs::getMainExecutable(NULL, NULL);
			string exedir = exepath.substr(0, exepath.find_last_of('/'));
			string line;
			ifstream structfile(exedir + "/configs/critical-structs");
			if (structfile.is_open()) {
				while (!structfile.eof()) {
					getline (structfile, line);
					if (line.length() > 1) {
						TTySet.insert(str_hash("struct." + line));
					}
				}
				structfile.close();
			}
			string TTyName[] = {
				"struct.kernfs_node",
				"struct.ksm_scan",
			};
			for (auto name : TTyName) {
				TTySet.insert(str_hash(name));
			}
		}

		//
		// Functions that are out of the analysis scope: definition, data
		// flows, etc. Common causes include linktime behaviors and assembly
		//

		void LoadOutScopeFuncs(unordered_set<string> &FuncSet) {
			string exepath = sys::fs::getMainExecutable(NULL, NULL);
			string exedir = exepath.substr(0, exepath.find_last_of('/'));
			string line;
			ifstream structfile(exedir + "/configs/out-scope-funcs");
			if (structfile.is_open()) {
				while (!structfile.eof()) {
					getline (structfile, line);
					if (line.length() > 1) {
						FuncSet.insert(line);
					}
				}
				structfile.close();
			}
		}

	protected:

		//
		// Variables
		//

		vector<const CallInst*> CallSet;
		vector<const CallInst*> ICallSet;
		vector<const CallInst*> MatchedICallSet;
		set<const StoreInst*> StoreInstSet;


		//
		// Structures for type-based dependece analysis
		//

		typedef unordered_set<Type*> typeset_t;
		typedef unordered_set<const Module*> modset_t;

		// Set of target types
		unordered_set<size_t> TTySet;
		DenseMap<size_t, modset_t> TargetDataAllocModules;

		unordered_set<string> OutScopeFuncNames;

		// Propagation maps
		DenseMap<const Module*, unordered_set<size_t>> moTyIdxMap;
		DenseMap<const Module*, modset_t> moTyPropMap;
		DenseMap<pair<const Module*, size_t>, modset_t> moPropMap;

		// Versatile map for refined indirect calls
		DenseMap<pair<const Module*, size_t>, modset_t> moPropMapV;

		// Which fields of a type have been stored to
		typedef unordered_set<int> storeset_t;
		typedef unordered_map<Type*, storeset_t> storemap_t;
		DenseMap<const Module*, storemap_t> storedTypeIdxMap;

		// All casts in a module
		typedef unordered_map<Type*, typeset_t> typemap_t;
		DenseMap<const Module*, typemap_t> CastFromMap;
		DenseMap<const Module*, typemap_t> CastToMap;

		// Function types that can be held by the GV
		DenseMap<const GlobalVariable*, typeset_t> GVFuncTypesMap;
		// Modules that store function pointers of the type to the global
		DenseMap<pair<uint64_t, size_t>, modset_t> TypesFromModuleGVMap;
		// Modules that load function pointers of the type from the global
		DenseMap<pair<uint64_t, size_t>, modset_t> TypesToModuleGVMap;

		// For caching
		DenseMap<size_t, FuncSet> MatchedICallTypeMap;
		DenseMap<pair<const Module*, size_t>, modset_t> ResolvedDepModulesMap;
		DenseMap<pair<const Module*, Type*>, typeset_t> ParsedTypeMap;
		DenseMap<const GlobalVariable*, typeset_t> ParsedGlobalTypesMap;
		DenseMap<pair<const Module*, const Module*>, typeset_t>ParsedModuleTypeICallMap;
		DenseMap<pair<const Module*, const Module*>, typeset_t>ParsedModuleTypeDCallMap;



		//
		// Methods
		//

		// Custom isTargetTy to decide if it is interested type
		bool isTargetTy(Type *);
		// A type such as struct that can contain the target type
		bool isContainerTy(Type *);


		// API for getting dependent modules based on the target type
		bool resolveFunctionTargets();
		bool resolveStructTargets();
		void getDependentModulesTy(size_t TyH, const Module *M, modset_t &MSet);
		// API for getting dependent modules based on the target value
		void getDependentModulesV(const Value *TV, const Module *M, modset_t &MSet);


		// Typecasting analysis
		typedef unordered_set<const User*> userset_t;
		void findCastsInGV(const GlobalVariable*, userset_t &CastSet);
		void findCastsInFunction(const Function*, userset_t &CastSet);
		void processCasts(userset_t &CastSet, const Module *M);
		
		
		// Analyze globals and function calls for potential types of
		// data flows
		void findTargetTypesInInitializer(const GlobalVariable*, const Module*,
				typeset_t &TargetTypes);
		void parseUsesOfGV(const GlobalVariable*, const Value*,
				const Module*, visited_t &Visited);
		bool parseUsesOfValue(const Value *V, typeset_t &ReadTypes,
				typeset_t &WrittenTypes, const Module *M);
		void findTargetTypesInValue(const Value *V,
				typeset_t &TargetTypes, const Module *M);
		void parseTargetTypesInCalls(const CallInst *CI, const Function *CF);


		// Maintain the maps
		// mapping between modules, through calls
		void addPropagation(const Module *ToM, const Module *FromM, Type *Ty,
				bool isICall = false);
		// mapping between module and global, through globals
		void addModuleToGVType(Type *Ty, const Module*, const GlobalVariable*);
		void addGVToModuleType(Type *Ty, const GlobalVariable*, const Module*);



		// Parse functions for various semantic information
		void findStoredTypeIdxInFunction(const Function *F);
		void findTargetAllocInFunction(const Function *F);
		void mapDeclToActualFuncs(FuncSet &FS);

	public:

		// Merged map
		DenseMap<pair<const Module*, size_t>, modset_t> moPropMapAll;

		TyPM(GlobalContext *Ctx_) : MLTA(Ctx_) {
			LoadTargetTypes(TTySet);
			LoadOutScopeFuncs(OutScopeFuncNames);
		}

};

#endif
