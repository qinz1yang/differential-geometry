import DifferentialGeometry.Bundle.PartialMfderiv.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open scoped BigOperators

variable {Idx : Type*} [Fintype Idx] [DecidableEq Idx]

def covDerivStepComp {r : ℕ}
    (ext : (Fin r → Idx) → Idx → Real)
    (chr : Idx → Idx → Idx → Real)
    (A : (Fin r → Idx) → Real) : (Fin (r + 1) → Idx) → Real :=
  fun n =>
    ext (Fin.tail n) (n 0) -
      ∑ s : Fin r, ∑ p : Idx,
        chr (n 0) (Fin.tail n s) p * A (Function.update (Fin.tail n) s p)

def frameExtData {r : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (frame : Idx → (x : M) → TangentSpace I x)
    (A : M → (Fin r → Idx) → Real) (x : M) :
    (Fin r → Idx) → Idx → Real :=
  fun m d => extDerivFun (I := I) (fun y : M => A y m) x (frame d x)

end DifferentialGeometry.PDE.RicciFlow
