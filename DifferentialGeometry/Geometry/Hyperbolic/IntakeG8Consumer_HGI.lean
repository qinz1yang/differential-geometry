import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.HyperbolicTruncation

/-!
# Consumer of the G8 intake (S-HG-INTAKE, suffix `_HGI`)

The conditional HG03 producer `exists_hyperbolicTruncation_of_translation_lattices`, elaborated
at its full binder list (the unconditional `∀ H, Nonempty (HyperbolicTruncation H)` is not in
the donor).
-/

set_option autoImplicit false

open DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

example := @exists_hyperbolicTruncation_of_translation_lattices
