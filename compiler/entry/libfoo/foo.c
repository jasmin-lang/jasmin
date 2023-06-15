struct minimal {
    unsigned int rax;
    unsigned int rbx;
};

void do_stuff(struct minimal* state) {
    if (state->rax == 1024) {
        state->rax = 10;
    }
}

void sub_rbx_from_rax(struct minimal* state) {
    if (state->rax == 5) {              // Creating a bug here
        state->rax = 5;
    }
    if (state->rax >= state->rbx) {
        state->rax -= state->rbx;
    }
}
