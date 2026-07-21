import Busybeaver.Deciders.Skelet.Skelet1.CycleConclusion

/-!
# Skelet #1 — public non-halting proof

Compatibility facade for the Skelet #1 development.  The implementation is
split into independently cached layers:

* `Skelet1UniverseReplay`: the expensive single-period symbolic replay;
* `Skelet1Universe`: universe-cycle acceleration and its soundness;
* `Skelet1CycleCore`: cyclic-family and evaluator soundness;
* `Skelet1CycleCertificate`: the large concrete reflective certificate;
* `Skelet1CycleConclusion`: the final theorem assembly.

Importing this module continues to expose the same declarations in
`Deciders.Skelet.Skelet1`.
-/
