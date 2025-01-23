#include<climits>

#ifndef _COMMON_
#define _COMMON_


#define NO_NODE (UINT_MAX)
#define NOCHILD (UINT_MAX)
#define TRUE_SV (INT_MAX)
#define FALSE_SV (INT_MIN)
#define LI_MIN INT_MIN
#define LI_MAX INT_MAX
#define TRUE_LIT (UINT_MAX-1)
#define FALSE_LIT (UINT_MAX-2)
#define NO_VAR (UINT_MAX-1)
#define TRUE_VAR (UINT_MAX-1)
#define FALSE_VAR (UINT_MAX-2)


//#define dassert(x) assert(x)
#define dassert(x) {}

#endif /* _COMMON_ */
