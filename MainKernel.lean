import Busybeaver.CLI
import Busybeaver.Deciders.Skelet.Skelet1Kernel

unsafe def main (args : List String) : IO UInt32 :=
  BeaverCLI.main Deciders.Skelet.Skelet1.Kernel.backend args
