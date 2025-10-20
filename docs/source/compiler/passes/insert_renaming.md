# Insert Renaming

Calling conventions mandated by the application binary interface (ABI) constrain
which registers must be used for each argument and each returned value of
*export* functions. Therefore it is often needed to move (i.e., *rename*) arguments or values to be returned.

A common example is the “identity” function, which simply returns its argument: on x86, a `MOV` instruction is required.

~~~
export fn identity(reg u64 x) -> reg u64 { return x; }
~~~

In order to let Jasmin programmers avoid this issue, this “insert renaming” pass,
which occurs very early in the compilation process, introduces assignments for each argument
at the beginning of the function body, and for each returned value at the end of the function body.
For instance, the function above is turned into the following:

~~~
export
fn identity(reg u64 x) -> reg u64 {
  x = x; // renaming of the argument
  x = x; // renaming of the returned value
  return x;
}
~~~

Note that in this case, only one of the assignments is needed, and [register
allocation](reg_alloc) will remove the redundant one. So the resulting assembly will be:

~~~
identity:
	mov 	rax, rdi
	ret
~~~

However, this transformation may add unwanted copies. This pass is therefore
optional. It can be disabled, when using `jasminc`, by using the command-line
flag `-noinsertrenamig`.
