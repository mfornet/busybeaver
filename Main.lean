import Busybeaver.CLI
import Busybeaver.Deciders.Skelet.Skelet1Native

unsafe def main (args : List String) : IO UInt32 :=
  BeaverCLI.main Deciders.Skelet.Skelet1.Native.backend args
