#define ADD_DIRECT(table, key, value, hash_val, bin_pos)\
do {\
    st_table_entry *entry;\
    if (table->num_entries/(table->num_bins) > ST_DEFAULT_MAX_DENSITY) {\
	rehash(table);\
        bin_pos = hash_val % table->num_bins;\
    }\
    \
    entry = alloc(st_table_entry);\
    \
    entry->hash = hash_val;\
    entry->key = key;\
    entry->record = value;\
    entry->next = table->bins[bin_pos];\
    table->bins[bin_pos] = entry;\
    table->num_entries++;\
} while (0)


#define DUPLICATES rehash(global), rehash(global), rehash(global), \
	rehash(global)	

#define SIMPLE 1

#define CALL_EXTRN_MACRO(table)\
do {\
    entry->hash = EXTERN_MACRO(table);\
    table->num_entries++;\
} while (0)

#define EMPTY

void stub(){
	char table,key,value,hash_val,bin_pos;
	ADD_DIRECT(table, key, value, hash_val, bin_pos);
}

void stub1(){
	DUPLICATES;
}

void stub2(){
	SIMPLE;
}

void stub3(){
	char table;
	CALL_EXTRN_MACRO(table)
}
