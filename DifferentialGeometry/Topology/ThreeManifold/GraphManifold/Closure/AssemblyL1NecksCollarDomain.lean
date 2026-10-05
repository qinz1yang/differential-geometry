import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the domain of the ball-side collar

Lane ASM-L1m. The shared domain `collarDomain η` of the ball-side collar (E2a, lane ASM-L1e3) and
of the collar hypotheses of the master bicollar (E2b, `AssemblyL1NecksMaster.lean`): inside the rim
annulus `‖z‖ < 15/16`, thin in height `|s| < η`. It is standalone so that both statements use the
same constant.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace GC.GraphManifold.Assembly

/-- The domain of the ball-side collar: inside the rim annulus, thin in height. -/
def collarDomain (η : ℝ) : Set (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  {q | ‖q.1‖ < 15 / 16 ∧ |q.2| < η}

theorem isOpen_collarDomain (η : ℝ) : IsOpen (collarDomain η) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const)

theorem mem_collarDomain {η : ℝ} {q : EuclideanSpace ℝ (Fin 2) × ℝ} :
    q ∈ collarDomain η ↔ ‖q.1‖ < 15 / 16 ∧ |q.2| < η :=
  Iff.rfl

end GC.GraphManifold.Assembly
