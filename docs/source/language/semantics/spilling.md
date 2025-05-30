# Variable Spilling

Registers are limited, so some variables must be temporarily stored in memory (usually on the stack) and later reloaded when needed. This process is called **spilling** a variable.

In Jasmin, variable spilling must be done explicitly. The basic syntax is:
~~~
reg u64 var;
stack u64 var_s;
var_s = var;  // spill
...
var = var_s;  // unspill
~~~
Alternatively, Jasmin provides syntactic sugar to simplify this:
~~~
reg u64 var;
() = #spill(var);
...
() = #unspill(var);
~~~

## Spilling to MMX Registers
You can spill variables to **MMX registers** using `#spill_to_mmx`:
~~~
#spill_to_mmx reg u64 var;
...
() = #spill(var);
~~~  
This can be useful when working with security checkers, as MMX spills prevent a variable from becoming secret.

## Liveness and Spilling
Spilling a variable does not make it dead. It is totally fine to spill a variable and still use it afterwards, typically passing it to a function. When you unspill the variable (typically after the call), you kill the variable, making it dead after the call and allowing the function to reuse the register when it does not need the value anymore.

### Example: Without Spilling
~~~
r = ...;
// r is live
f(r);
// r is live
... = ... r ...;
~~~

### Example: With Spilling
~~~
r = ...;
s = r;  // spill
// r is live
f(r);
// r is dead
r = s;  // unspill
// r is live again
... = ... r ...;
~~~

## Debugging Spills
Jasmin provides the `-pliveness` flag, which shows which registers are alive at each instruction. This is useful for verifying that variables are correctly spilled.
