#ifndef _TYP_CALL_GRAPH_H
#define _TYP_CALL_GRAPH_H

#include "Global.h"
#include "MLTA.h"
#include "TyPM.h"

class TyPMCGPass :
	public virtual IterativeModulePass, public virtual TyPM {

	private:

		//
		// Variables
		//

		// Index of the module
		int MIdx;


		//
		// Methods
		//

		// Phases
		void PhaseMLTA(Function *F);
		void PhaseTyPM(Function *F);


	public:
		static int AnalysisPhase;

		TyPMCGPass(GlobalContext *Ctx_)
			: IterativeModulePass(Ctx_, "TyPCGPass"),
			  TyPM(Ctx_) {

				LoadElementsStructNameMap(Ctx_->Modules);
				MIdx = 0;

			}

		virtual bool doInitialization(llvm::Module *);
		virtual bool doFinalization(llvm::Module *);
		virtual bool doModulePass(llvm::Module *);

		void processResults();

};

#endif
