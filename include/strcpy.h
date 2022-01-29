#include <stdlib.h>
#include <limits.h>
#include <assert.h>
#include <stdio.h>
void dep_strcpy(char* dst, char* src, size_t size);
unsigned get_strsize_1(char* str);
unsigned get_strsize_2(char* str);

char* get_heap_str(char* str);
void  free_heap_str(char* str);

