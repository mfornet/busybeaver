import Busybeaver.Deciders.BB5Table
import Busybeaver.Deciders.Skelet.Skelet1Kernel

namespace Deciders.BB5Table.Kernel

open TM.Table

/-- The kernel-only instantiation of the shared Skelet #1 table proof. -/
theorem sporadicMachine5_nonHalting :
    ¬ sporadicMachine5.halts (default : Config 4 1) :=
  BB5Table.sporadicMachine5_nonHalting Skelet.Skelet1.Kernel.backend

end Deciders.BB5Table.Kernel
