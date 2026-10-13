# Name discarded values

Discarded values, or “holes”, are left-values written `_`.

This pass replaces these holes with variables. In order to avoid overwriting
live variables, the replacement variables must usually be fresh.

When such a hole is the destination of an in-place operation (many instructions
of the `x86_64` instruction set operate in-place), it is often not possible to
fill it correctly. Hence compilation will abort. Consider for instance the
instruction written below compiled on `x86_64` (where `x` holds the address of
some machine word in memory).

~~~
_ = [x] + 1;
~~~

The instruction that loads a value and increments it (`INC`) operates in-place,
i.e., write its result in memory, here at address `x`. Therefore, as it is not
possible to discard the result, compilation fails.
