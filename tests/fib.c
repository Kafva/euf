#include <stdio.h>
#define swap(array, idx1, idx2) { \
	uint tmp = array[idx1]; array[idx1] = array[idx2]; array[idx2] = tmp; \
}
typedef unsigned int uint;

const int n = 9;

int fib(int k) {
	if ( k<=1 ) return 1;
	else return fib(k-1) + k;
}

/* Sequential*/
uint partition(uint v[], unsigned low_index, unsigned high_index, unsigned pivot_index) {
    if (pivot_index != low_index) swap(v, low_index, pivot_index);     // Move the pivot element to the bottom of the vector 

    pivot_index = low_index;
    low_index++;
    
    while (low_index <= high_index) {
        // Start from the element after the pivot element (position 1)
        // and move the low_index and high_index closer to another until they intersect
        
        if (v[low_index] <= v[pivot_index])
            // If the current lowest element is lower or equal to the
            // pivot it is in a correct position and we move the low_index forward 
            low_index++;
        else if (v[high_index] > v[pivot_index])
            // If the current highest element is greater than the pivot element
            // it is in a correct position and we move the high_index backward 
            high_index--;
        else
            // If the value at the lowest index is greater than the pivot_element
            // and the element in the highest index is lower than the pivot_element
            // swap the elements at these positions
            swap(v, low_index, high_index);
    }

    // Put pivot back between the two groups (low_index will be == high_index)
    // and return the position the pivot value was placed at
    if (high_index != pivot_index) swap(v, pivot_index, high_index);
    return high_index;
}

void qsort(uint v[], unsigned low_index, unsigned high_index) {    
    if (low_index >= high_index) return;

    unsigned pivot_index;

    // Select the pivot position from the middle of the low and high point of the array
    pivot_index = (low_index+high_index)/2;

    // Partition the vector around the ELEMENT found at `pivot_index`,
    // all elements lower than the element will be placed
    // before `pivot_index`, all elements greater than it will be placed after it
    pivot_index = partition(v, low_index, high_index, pivot_index);

    // Sort each of the sub arrays 
    //  [low,pivot-1]
    //  [pivot+1,high]

    if (low_index < pivot_index)
        // Provided that the low value is not the same as the pivot value
        qsort(v, low_index, pivot_index-1);
    if (pivot_index < high_index)
        // Provided that the high value is not the same as the pivot value
        // in which case the subarray would already be sorted
        qsort(v, pivot_index+1, high_index);
}



void print_arr(uint arr[], uint size){
	printf("arr  = [ ") ;
	for (int i = 0; i < size; i++){
		printf("%u ", arr[i]);
	}
	printf("]\n");
}

int main(int argc, char* argv[]){
	uint arr[] = {	138, 874, 869, 255, 636, 473, 993, 536, 249, 605, 986, 135, 702, 813, 932, 135, 913, 690, 405, 300 };
	//uint arr[] = { 8, 1, 2, 10, 90, 1000, 3, 6};

	uint size = sizeof(arr)/sizeof(uint);

	print_arr(arr, size);
	printf("=====================\n");
	qsort(arr, 0, size);
	print_arr(arr, size);


	// printf("%d\n", fib(n) );
	return 0;
}
