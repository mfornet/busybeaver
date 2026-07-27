import Busybeaver.Deciders.BB5Table
import Busybeaver.Deciders.Skelet.Skelet1Native

namespace Deciders.BB5Table.Native

open TM.Table

/-- The native-evaluation instantiation of the shared Skelet #1 table proof. -/
theorem sporadicMachine5_nonHalting :
    ¬ sporadicMachine5.halts (default : Config 4 1) :=
  BB5Table.sporadicMachine5_nonHalting Skelet.Skelet1.Native.backend

end Deciders.BB5Table.Native
