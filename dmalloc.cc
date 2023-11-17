#define M61_DISABLE 1
#include "dmalloc.hh"
#include <cstdlib>
#include <cstring>
#include <cstdio>
#include <cinttypes>
#include <cassert>
#include <climits>
#include <unordered_map> //C++ STL hash table implementation
#include <iostream>
#include <string>
#include <vector>
#include <algorithm> //For C++ Sort function

using namespace std;

#define POINTER_INVALID 1495028 //random number used when allocation is freed

static long CANARY_FLAG = 957291; //random number used to check boundary overwrite errors (8 bytes)
static long MAX_FILE_NAME_LENGTH = 100; //assumption for the largest file name (not more than a 100 character long file name)
static long MAX_LINES = 4; //assumption for the largest line number fed in (not more than 9999 lines of code!)

//Header struct to store metadata for each allocation. Keeping a reference to the next / previous allocations in the header packet of each allocation
//Alignment: struct is 40 bytes, CANARY flag is 8 bytes, so payload is +48 bytes from start of base_malloc address (multiple of 16, so aligned)
typedef struct alloc_header
{
	void* next; //Pointer to the next memory allocation
	void* prev; //Pointer to the previous memory allocation
	const char* file_name; //store the file name where the allocation was called from
	uintptr_t validity_flag; //secret validity flag for each allocation
	int line; //store the line number the allocation was called from
	int size; //store the size of each allocation
} allocation_header;

//Global counter variables
void* tail = NULL; //A POINTER TO THE TAIL OF THE LINKED LIST
unsigned long long ntotal = 0; //total successful mallocs
unsigned long long nfrees = 0; //number of successful frees
unsigned long long active_size = 0; //total size of active allocations
unsigned long long freed_size = 0; //total size of freed allocations
unsigned long long total_size = 0; //total size of all allocations
unsigned long long nfail = 0; //number of failed allocations
unsigned long long fail_size = 0; //total size of failed allocations
uintptr_t heap_min = ULONG_MAX;
uintptr_t heap_max = 0;
size_t num_bytes_eliminated = 0; //keep track of number of bytes eliminated from elimination set

//Global C++ STL hash map to keep track of elimination sets:
unordered_map<string, unsigned long long> elim;

//Function to update the elimination set each time we get an incoming malloc call 
void update_elimination_set(const char* key, size_t value) {
	//If the current file/line pair is already in the list, increment it's value by the current call
	if (elim.find(key) != elim.end()) {
		elim[key] += value;
	}

	//The incoming call is not in the list
	else {
		//If we have less than 5 elements in the list, simply add the incoming call
		if (elim.size() < 5) {
			elim[key] = value;
		}

		//If we have more than 5, first find the smallest value out of all those currently in the list, and the incoming call
		else {
			char min_key[MAX_FILE_NAME_LENGTH+MAX_LINES+2];
			size_t min_value = SIZE_MAX;
			for (auto x : elim) {
				if (x.second < min_value) {
					min_value = x.second;
					strcpy(min_key, x.first.c_str());
				}
			}
			//Min key & value contain the minimum element in elimination set

			//C++ STL vector, to store a list of all the keys from the elimination set that need to be removed (because their counts reached 0)
			vector<decltype(elim)::key_type> vec;

			if (min_value < value) { //If the minimum element is in the list, decremenet all elements by min_value, if it is 0 then remove it, then add current entry (with value decremented by min_value)
				num_bytes_eliminated += min_value;
				for (auto &x : elim) {
					x.second -= min_value;
					if (x.second == 0) {
						vec.emplace_back(x.first);
					}
				}
				elim[key] = value - min_value;
			}

			else { //The incoming call value is the smallest out of all, ignore the incoming call but decrement all values in the map by the value of incoming call
				num_bytes_eliminated += value;
				for (auto &x : elim) {
					x.second -= value;
					if (x.second == 0) {
						vec.emplace_back(x.first);
					}
				}
			}

			//Remove all the elements from the list which reached 0 count
			for (auto &i : vec) {
				elim.erase(i);
			}
		}
	}
	
	
}

/// dmalloc_malloc(sz, file, line)
///    Return a pointer to `sz` bytes of newly-allocated dynamic memory.
///    The memory is not initialized. If `sz == 0`, then dmalloc_malloc must
///    return a unique, newly-allocated pointer value. The allocation
///    request was at location `file`:`line`.

void* dmalloc_malloc(size_t sz, const char* file, long line) {
    (void) file, (void) line;   // avoid uninitialized variable warnings

	if (SIZE_MAX - sz < sizeof(allocation_header) + 2*sizeof(CANARY_FLAG)) { //overflow because requested size is so large, when we add allocation header size and canary size, it overflows back to a small amount
		//Cannot allocate
		nfail++;
		fail_size += sz;
		return NULL;
	}

	//Get memory from base malloc, large enough to store the header, payload and canaries
	//Complete memory for each allocation looks like: |Header|Canary|Payload|Canary|. Thus, Header will always be at address Payload - sizeof(Canary) - sizeof(Header)
	void* complete_memory = base_malloc(sizeof(allocation_header) + sz + 2*sizeof(CANARY_FLAG));
	if (complete_memory != NULL) {
		//Create the metadata header
		allocation_header header;
		uintptr_t return_address = ((uintptr_t) complete_memory + sizeof(header) + sizeof(CANARY_FLAG));
		header.size = sz;
		header.validity_flag = return_address; //setting the secret validity flag as the numerical address of each allocation - thus it is unique to that allocation, but can be verified. 
		//This elegantly solves for test032, because if memory is copied with a valid header and validity flag into the payload of another allocation, and then a free is called from the new location, the validity flag will not match the address of the free!
		header.prev = tail;
		header.next = NULL;
		header.file_name = file; //From the spec: You may assume that the file argument to these functions has static storage duration. This means you don’t need to copy the string's contents into your block metadata—it is safe to use the string pointer.
		header.line = line;
		if (tail != NULL) {
			((allocation_header*)tail)->next = complete_memory; //casting tail to a header pointer, and setting it's next to the currently allocated block
		}
		tail = complete_memory;
		memcpy(complete_memory, &header, sizeof(header)); //copy the data from the local (stack-allocated) header struct
		memcpy((void*) ((uintptr_t) complete_memory + sizeof(header)), &CANARY_FLAG, sizeof(CANARY_FLAG)); //use uintptr_t to do pointer arithmetic, then cast back to pointer - setting the region after the header to be the canary flag
		memcpy((void*) ((uintptr_t) complete_memory + sizeof(header) + sizeof(CANARY_FLAG) + sz), &CANARY_FLAG, sizeof(CANARY_FLAG)); //Setting the region after the payload to be the canary flag
		ntotal++;
		total_size += sz;
		if (return_address < heap_min) {
			heap_min = return_address;
		}
		if (return_address + sz > heap_max) {
			heap_max = return_address + sz;
		}
		
		//Tracking bytes in elimination set for each incoming dmalloc
		//Step 1 - create a string with the file name and number (converted from long to string) concatenated
		char file_name_number[MAX_FILE_NAME_LENGTH];
		strcpy(file_name_number, file);
		strcat(file_name_number, ":");
		char line_number[MAX_LINES];
		sprintf(line_number, "%ld", line);
		strcat(file_name_number, line_number);
		//Step 2 - track it in the elimination set
		update_elimination_set(file_name_number , sz);
		return (void*) return_address; //returning part of the total allocated memory, starting from the payload
	}
	else {
		//Allocation failed
		nfail++;
		fail_size += sz;
		return NULL;
	}
}


/// dmalloc_free(ptr, file, line)
///    Free the memory space pointed to by `ptr`, which must have been
///    returned by a previous call to dmalloc_malloc. If `ptr == NULL`,
///    does nothing. The free was called at location `file`:`line`.

void dmalloc_free(void* ptr, const char* file, long line) {
    (void) file, (void) line;   // avoid uninitialized variable warnings

	if (ptr != NULL) {
		//If the pointer is not within the heap, throw an error
		if ((uintptr_t) ptr < heap_min || (uintptr_t) ptr > heap_max) {
			fprintf(stderr, "MEMORY BUG: %s:%01lu: invalid free of pointer %p, not in heap\n", file, line, ptr);
			exit(1);
		}

		//Calculate the start address of the complete allocated memory (including header & canaries), given the address of the payload
		void* start_address = (void*) ((uintptr_t)ptr - sizeof(CANARY_FLAG) - sizeof(allocation_header));

		//If we'd specifically freed this memory address before, throw a double free error
		if (((allocation_header*) start_address)->validity_flag == POINTER_INVALID) {
			fprintf(stderr, "MEMORY BUG: %s:%01lu: invalid free of pointer %p, double free\n", file, line, ptr);
			exit(1);
		}

		else if (((allocation_header*) start_address)->validity_flag != (uintptr_t) ptr) {
			//This is within the heap limits (which means it could've been allocated), and also the alignment is such that the validity flag is not the correct value
			//This means that this is an address within a previously allocated heap region - either one that was freed, or is still active - need to find the larger memory region

			//Iterate through active allocations (in linked list)
			void* curr = tail;
			while (curr != NULL) {
				allocation_header* curr_header = (allocation_header*) curr;
				if ((uintptr_t) curr + sizeof(allocation_header) + sizeof(CANARY_FLAG) < (uintptr_t) ptr && (uintptr_t) ptr <= (uintptr_t) curr + sizeof(allocation_header) + 2*sizeof(CANARY_FLAG) + curr_header->size) {
					//Ptr is within previously allocated, active region
					fprintf(stderr, "MEMORY BUG: %s:%ld: invalid free of pointer %p, not allocated\n  %s:%d: %p is %ld bytes inside a %d byte region allocated here\n", file, line, ptr, curr_header->file_name, curr_header->line, ptr, (uintptr_t) ptr - ((uintptr_t) curr + sizeof(allocation_header) + sizeof(CANARY_FLAG)), curr_header->size);
					exit(1);
				}
				curr = ((allocation_header*) curr)->prev;
			}
		}

		else { //Passed all the previous tests: within heap location, not a standard double free, validity flag exists & matches the location. One last test for test033
		//What if, an allocated location x (and it's surrounding, including header) is copied to another region, then x is freed, then the copy (including) header, is copied back into x.
		//In this situation, x will contain all the original data - payload, valid canaries and valid headers with correct validity flag (so it'll pass all above tests)
		//However, while the copy will contain outbound pointers to the previous/next allocations, when the original is freed, the surrounding allocations in the linked list lose their pointers to x
		//So, if this is the situation, x's next -> previous will not be x. And x's previous->next will not be x.
			if (((allocation_header*) start_address)->prev != NULL) {
				if (((allocation_header*) (((allocation_header*) start_address)->prev))->next != start_address) {
					fprintf(stderr, "MEMORY BUG: %s:%01lu: invalid (sneaky) free of pointer %p, region already freed then copied\n", file, line, ptr);
					exit(1);
				}
			}
			else if (((allocation_header*) start_address)->next != NULL) {
				if (((allocation_header*) (((allocation_header*) start_address)->next))->prev != start_address) {
					fprintf(stderr, "MEMORY BUG: %s:%01lu: invalid (sneaky) free of pointer %p, region already freed then copied\n", file, line, ptr);
					exit(1);
				}
			}
		}

		//Check for boundary write errors
		long cflag1 = *((long*) ((uintptr_t) start_address + sizeof(allocation_header)));
		long cflag2 = *((long*) ((uintptr_t) start_address + sizeof(allocation_header) + sizeof(CANARY_FLAG) + ((allocation_header*) start_address)->size));
		if (cflag1 != CANARY_FLAG || cflag2 != CANARY_FLAG) {
			fprintf(stderr, "MEMORY BUG: %s:%01lu: detected wild write during free of pointer %p\n", file, line, ptr);
			exit(1);
		}

		//Rearrange the linked list after removing current allocation
		if (((allocation_header*) start_address)->prev != NULL) {
			((allocation_header*) ((allocation_header*) start_address)->prev)->next = ((allocation_header*) start_address)->next;
		}

		if (((allocation_header*) start_address)->next != NULL) { 
			((allocation_header*) ((allocation_header*) start_address)->next)->prev = ((allocation_header*) start_address)->prev;
		}
		else {//This is the last allocation in the list (the tail) - we need to reset the tail to an active allocation
			tail = ((allocation_header*) tail)->prev;
		}

		((allocation_header*) start_address)->validity_flag = POINTER_INVALID; //set it to a specific value after freeing
		nfrees++;
		freed_size += ((allocation_header*) start_address)->size;
		base_free(start_address); //The actual address starts at the pointer - canary_flag - sizeof(header)
		if (ntotal-nfrees == 0) {
			tail = NULL; //if we freed the last element, the tail is null
		}
	}
}


/// dmalloc_calloc(nmemb, sz, file, line)
///    Return a pointer to newly-allocated dynamic memory big enough to
///    hold an array of `nmemb` elements of `sz` bytes each. If `sz == 0`,
///    then must return a unique, newly-allocated pointer value. Returned
///    memory should be initialized to zero. The allocation request was at
///    location `file`:`line`.

void* dmalloc_calloc(size_t nmemb, size_t sz, const char* file, long line) {
	if ((sz > 0 && nmemb > SIZE_MAX/sz) || (nmemb > 0 && sz > SIZE_MAX/nmemb)) {
		//Allocation failed due to overflow
		nfail++;
		fail_size += SIZE_MAX-1;
		return NULL;
	}
	else {
		void* ptr = dmalloc_malloc(nmemb * sz, file, line);
		if (ptr) {
			memset(ptr, 0, nmemb * sz);
		}
		return ptr;
	}
}


/// dmalloc_get_statistics(stats)
///    Store the current memory statistics in `*stats`.

void dmalloc_get_statistics(dmalloc_statistics* stats) {
    // Set all statistics to 0 (in case no allocs done)
    memset(stats, 0, sizeof(dmalloc_statistics));
	stats->ntotal = ntotal;
	stats->nactive = ntotal-nfrees;
	stats->total_size = total_size;
	stats->active_size = total_size - freed_size;
	stats->nfail = nfail;
	stats->fail_size = fail_size;
	stats->heap_min = heap_min;
	stats->heap_max = heap_max;	
}


/// dmalloc_print_statistics()
///    Print the current memory statistics.

void dmalloc_print_statistics() {
    dmalloc_statistics stats;
    dmalloc_get_statistics(&stats);

    printf("alloc count: active %10llu   total %10llu   fail %10llu\n",
           stats.nactive, stats.ntotal, stats.nfail);
    printf("alloc size:  active %10llu   total %10llu   fail %10llu\n",
           stats.active_size, stats.total_size, stats.fail_size);

}


/// dmalloc_print_leak_report()
///    Print a report of all currently-active allocated blocks of dynamic
///    memory.

void dmalloc_print_leak_report() {
    //Iterate through active allocations (in linked list)
	void* curr = tail;
	while (curr != NULL) {
		allocation_header* curr_header = (allocation_header*) curr;
		fprintf(stdout, "LEAK CHECK: %s:%d: allocated object %p with size %d\n", curr_header->file_name, curr_header->line, (void*) ((uintptr_t) curr + sizeof(allocation_header) + sizeof(CANARY_FLAG)), curr_header->size);
		curr = ((allocation_header*) curr)->prev;
	}
}

//Function to compare the second value of 2 vectors - using this to sort a list of vectors that contain the elements from the hash map storing the heavy hitters
bool compare(pair<string, unsigned long long>& x,
        pair<string, unsigned long long>& y)
{
    return x.second > y.second;
}

/// dmalloc_print_heavy_hitter_report()
///    Print a report of heavily-used allocation locations.

void dmalloc_print_heavy_hitter_report() {

	if (elim.size() > 0) {
		// Create a vector to store all the elements from the elimination set hash table
		vector<pair<string, unsigned long long> > elim_vector;
	
		//Iterate through the elimination set hash map and add each element to the vector
		for (auto it : elim) {
			elim_vector.push_back(it);
		}
	
		// Sort the vector in descending order
		sort(elim_vector.begin(), elim_vector.end(), compare);

		//Iterate through the sorted vector and print out heavy hitter report
		for (auto x : elim_vector) {
			size_t total_bytes = x.second+num_bytes_eliminated;
			if ((float) 100*total_bytes/total_size > 10) {
				printf("HEAVY HITTER: %s: %zu bytes (~%.1lf%%)\n", x.first.c_str(), total_bytes, (float) 100*total_bytes/total_size);
			}
		}
	}
	
}
