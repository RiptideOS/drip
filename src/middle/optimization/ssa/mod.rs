// TODO: remove redundant get_element_pointer computations for the same
// structure

// TODO: remove alloc instructions where all the fields are immediately
// deconstructed and the ptr is not used for any other purpose. to do this,
// check that the pointer returned from alloc is only used in get_element_ptr
// and the returned pointers are only used for load/store instructions. if thats
// the case, just replace the load dest regs with the initial values.
