#ifndef SIZE_T_H
#define SIZE_T_H

#ifdef __cplusplus
extern "C" {
#endif

#ifdef __SIZE_TYPE__
typedef __SIZE_TYPE__ size_t;
#else
# if __WORDSIZE == 64
typedef unsigned long int size_t;
#else
typedef unsigned int size_t;
#endif
#endif

#ifdef __cplusplus
}
#endif

#endif /* SIZE_T_H */
