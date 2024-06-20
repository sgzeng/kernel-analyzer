#ifndef _TYPM_CONFIG_H
#define _TYPM_CONFIG_H


#include "llvm/Support/FileSystem.h"

#include <map>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <fstream>
#include <map>

#include "TyPMCommon.h"


using namespace std;
using namespace llvm;

//
// Configurations
//

//#define VERBOSE_SA 1
//#define DEBUG_SA 1

extern int ENABLE_MLTA;
extern int ENABLE_TYDM;
extern int MAX_PHASE_CG;

#define SOUND_MODE 1
#define UNROLL_LOOP_ONCE 1

///////////////////////////////////////////////////////////
// TyPM-related configurations
///////////////////////////////////////////////////////////
#define PARSE_VALUE_USES 1
#define TYPE_ELEVATION 1
#define FLOW_DIRECTION 1
#define FUNCTION_AS_TARGET_TYPE 1 // Target types: struct type or function type
#define MAP_DECLARATION_FUNCTION
#define PRINT_ICALL_TARGET
///////////////////////////////////////////////////////////

#define MAX_TYPE_LAYER 10
//#define MAP_CALLER_TO_CALLEE 1
//#define MLTA_FIELD_INSENSITIVE
#define PRINT_SOURCE_LINE
//#define DEBUG_MLTA

// Paths of sources
#define LINUX_SOURCE_KASE "/home/kjlu/projects/kernels/linux-5.18"




//
// Load data from files
//

struct SrcLn {
	SrcLn() {};
	SrcLn(string s, int l) {
		Src = s;
		Ln = l;
	};
	string Src;
	int Ln;
};

#endif
