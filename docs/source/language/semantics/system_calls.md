# System calls

Since version 2022.09.0, Jasmin features a `#randombytes` _systemcall_. Here is a small example using it, that return a byte (which one I cannot tell):

~~~
export
fn randombyte() -> reg u8 {
    stack u8[1] buf;
    reg u8 r;
    buf = #randombytes(buf);
    r = buf[0];
    return r;
}
~~~

The `#randombytes` Jasmin function receives an array — whose contents need not be initialized before the call — and returns an array, of the same type as the one given as argument, fully initialized. The contents of the returned array is not specified. Formally, the behavior of the `#randombytes` function is modeled as a deterministic function in a state monad: calling it from a given state, returns an array and the updated state (and there are no other ways to tamper with said state).

The compiler emits a call to a `__jasmin_syscall_randombytes__` symbol that shall be resolved at link time. The user of the assembly code is responsible for implementing that function. Its specification is that it receives as first argument a pointer to a valid region of memory whose size is given as second argument and returns its first argument. Argument and returned value are exchanged according to the regular ABI.

Proofs in EasyCrypt about programs calling `#randombytes` need to specify its properties. To this end, the compiler produces an EasyCrypt model that is parametrized by a theory defining the various `randombytes` calls performed in the program; proofs shall be done relative to an instance of that theory.

Regarding constant-time security, arguments to `#randombytes` must be public; its result is considered secret.
