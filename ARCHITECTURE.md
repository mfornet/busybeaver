High level architecture:

Run TNF enumeration over all Tabular Machines with n states and m labels, then use deciders to prove that each machine halts or loops.

Deciders operate on top of Model (which are higher level Machine abstractions, not necessarily Tabular Machines). This allows us to enhance machines with more metadata and functionality, maintaining the equivalence with the base Tabular Machine.

```
Busybeaver/
    Deciders/       -- Deciders implementations live here
    Enumerate/      -- TNF logic and proofs about correctness live here
    TM/
        Model/      -- Abstraction that defines what is a machine and how to operate with it. Internal details are usually opaque.
        Table/      -- Tabular Machine implementation, which is the base machine type that we enumerate over. This is the lowest level machine type, and it should be as simple as possible.
        Wrappers/   -- New machine types that enhance a lower level machine implementation with more functionality
```

## Audit correctness

We define the Busybeaver function in `Problem.lean`. Check `noncomputable def Busybeaver`.

The method `BBCompute` defined in `Busybeaver/Enumerate/Alg.lean` runs the enumeration and computes the Busybeaver function.

The `theorem correct_complete` asserts that the computation is equivalent to the function definition.
