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

- For each basic-block, we have computed the φ-function (if
  necessary) and the :literal:`liveOut` set.

- For each variable ``v``, we have computed the equivalence
  class ``[v]`` arising from the equality constraints. We
  derive equality constraints from

  (1) two-address assembly instructions
  (2) renaming assignemnts, and
  (3) φ-functions.

  The information is stored in a map ``repr`` such that
  ``repr[v] = repr[v']`` iff ``[v] = [v']``.
   
- For each variable ``v``, we have computed a map ``blocks`` such
  that ``p ∈ blocks[v]`` iff ``v`` occurs in the block with position
  ``p``. We have also computed a map ``live`` such that ``live[v,p]``
  is defined iff ``v`` is live in the block with position ``p``.
  If ``live[v,p] = (l,u)`` then
  
  (1) ``l = ⊥`` if ``v`` is defined in another basic block (that
      dominates ``j``) and ``v`` defined in line ``l`` otherwise.
  (2) ``u = ⊥`` if ``v`` is in :literal:`liveOut` and ``v`` last used
      in line ``u`` otherwise [#deadpos]_. 

Basic-block
------------

Given a basic block in SSA form, we can first make a backwards pass and
add instructions :literal:`free(v₁,..,vₖ)` immediately after the first
use of all variables :literal:`vᵢ` that are not live when exiting
the block (i.e., in the :literal:`liveOut` set).


.. rubric:: Footnotes

.. [#args]_    For now, we assume there are fewer arguments/return than
                we can pass in registers.
.. [#deadpos]_ You must check where ``v`` is used to determine when it can
               be reused, for example, in ``arr[v₁],v₂ = v₃ * v₄``, the
               can occur as an index in the dest
