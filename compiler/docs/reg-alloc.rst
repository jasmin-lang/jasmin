*******************
Register allocation
*******************

.. highlight:: haskell

Preliminaries
-------------

**Positions**.
We denote basic blocks by their position ``p`` in a statement.
The function ``addPos`` demonstrates how positions are computed.
We assume ``addPos`` is called with ``addPos [0] s`` on the
outermost statement ``s`` and ``setPos`` annotates a basic-block
with its position::

    addPos :: Pos -> [Instr] -> [Instr]
    addPos p (i:is) =
      case i of
        Block(_)     -> (setPos p i):is'
        If(c,s1,s2)  -> If(c,addPos (p++[0,0]) s1, addPos (p++[1,0]) s2):is'
        WhileDo(c,s) -> WhileDo(c,addPos (p++[0]) s):is'
        DoWhile(c,s) -> DoWhile(c,addPos (p++[0]) s):is'
    where
      incPos p = init p ++ (last p + 1)
      is'      = addPos (incPos p) is


Register constraints
--------------------

To lower everything to assembly, our assigned registers must satisfy
certain constraints:

1. **Fixed registers**: Certain instuctions and the arguments and return
   values for exported functions require fixed registers such as ``RAX``,
   ``RDX``, etc. We assume there is a subset ``FixRegs`` of registers
   that can be be fixed.

   **NOTE**: For now, it seems like we only need register constraints
   of the form ``FIX(v,rᵢ)``, i.e., the register ``rᵢ`` is the only
   register allowed for ``v``. In the future, we might require
   constraints of the form ``ONEOF(v;r₁,...,rₖ)``.

2. **Equality constraints**: Two variables must be assigned the same
   register. These stem from two-address assembly instructions like
   ``addc`` or from renaming assignments in the input (e.g., ``x := y``).
   Renaming assignments are also introduced when inlining function
   calls. We use ``Eq(v,v')`` do denote the corresponding equality
   constraint.

Input
-----

To perform register allocation, we assume given a statement, a
list of argument variables of type ``reg u64``, and a list of
return variables of type ``reg u64`` [#args]_.

1. For each basic-block, we have computed the φ-function (if
   necessary) and the :literal:`liveOut` set.

2. For each variable ``v``, we have computed the equivalence
   class ``[v]`` arising from the equality constraints. We
   derive equality constraints from

   (1) two-address assembly instructions
   (2) renaming assignments, and
   (3) φ-functions.

   The information is stored in a map ``repr`` such that
   ``repr[v] = repr[v']`` iff ``[v] = [v']``.
   
3. For each variable ``v``, we have computed a map ``blocks`` such
   that ``p ∈ blocks[v]`` iff ``v`` occurs in the block with position
   ``p``. We have also computed a map ``live`` such that ``live[v,p]``
   is defined iff ``v`` is live in the block with position ``p``.
   If ``live[v,p] = (l,u)`` then
  
   (1) if ``l = ⊥``, then ``v`` is defined in another basic block (that
       dominates ``p``)

       if ``l ≠ ⊥``, then ``v`` is defined in line ``l``
   (2) if ``u = ⊥``, then ``v`` is in :literal:`liveOut`
       
       if ``u ≠ ⊥``, then ``v`` is last used in line ``u`` [#deadpos]_

4. For each variable ``v ∈ range(repr)``, we have computed if the
   register is fixed. We store this information in a map ``fix`` such
   that ``fix[v] = rᵢ ∈ FixRegs`` if ``v`` must be assigned the fixed
   register ``rᵢ``.

Output
------

A map ``reg`` such that for each variable ``v`` that occurs in the function
``reg[v]`` is the assigned register. The assignment must satisfy the following
requirements:

1. Compatible with ``repr`` and ``fix``.

2. Compatible with ``live``, i.e., if ``reg[v] = reg[v']`` then the two
   variables do not interfere.

Algorithm for basic blocks
--------------------------



Dealing with ``if-then-else``
-----------------------------

Dealing with ``while-do``
-------------------------

Dealing with ``do-while``
-------------------------


.. rubric:: Footnotes

.. [#args]    For now, we assume there are fewer arguments/return values
              than we can pass in registers.
.. [#deadpos] You must check where ``v`` is used to determine when it can
              be reused, for example, in ``arr[v₁],v₂ = v₃ * v₄``, 
              ``v₁`` occurs as index in the left-hand-side and it depends
              on the concrete instruction if the register assigned to
              ``v₁`` can be used for ``v₂``.
