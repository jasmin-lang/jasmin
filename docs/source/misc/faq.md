# FAQ

## How to debug compilation errors?

### Register allocation

> register allocation: no more register to allocate “ ra.357”

This message says that there are no free registers for storing the return address of some function
(its name is a white space followed by `ra`).
Which function? With the command-line flag `-debug` on, the compiler will output the required information
(`grep` for the actual name of the variable to filter the too verbose output).

There are two possible kinds of fix to this kind of issue: either spill some registers to ensure there is at least one register that is free at *all* call sites; or change the calling-convention of the function so that return address is passed on the stack
(this can be achieved through the `#returnaddress=stack` annotation before the function declaration).

### Stack allocation

> no region associated to variable p

Here is a minimal program triggering this error:

~~~
export fn dangling_reference() -> reg u32 {
  reg ptr u32[1] p;
  p[0] = 0;
  reg u32 r;
  r = p[0];
  return r;
}
~~~

The problem comes from the fact that there is no memory allocated to the array: variable `p` is tagged as `ptr` so that after compilation the register that corresponds to `p` only contains a reference (aka a pointer) to the array. One way to solve this issue is to link `p` to an other array for which there is some allocated memory, for instance with: `stack u32[2] s; p = s[1:1];`.


### Linearization

> assignment remains

Assignments (instructions of the form `d = e;`) are processed by the various compilation passes,
removed (when they become dead) or replaced by target operations (i.e., assembly-level instructions, such as `rax = #MOV(rbx);`).
When everything goes well, all assignments are gone before the [[linearization pass|Linearization]].

This error message arises when one of the earlier passes could not handle the assignment.
Often, the [[instruction selection pass|Instruction selection]] could not find in the target instruction set (ISA) an operation matching said assignment.
A common work-around is to decompose the assignment into several simpler steps.

## How do I set a register to zero?

For setting variables to zero, Jasmin has the special `#set0()` intrinsic.
For example:

```jazz
reg u64 i;

i = #set0();
while (i < 256) {
    // ...
    i += 1;
}
```
