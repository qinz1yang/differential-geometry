import DifferentialGeometry.Topology.Manifold.Pi
import Mathlib.Geometry.Manifold.Diffeomorph

open scoped ContDiff Manifold

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Fin 2 → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  {H : Fin 2 → Type*} [∀ i, TopologicalSpace (H i)]
  (I : ∀ i, ModelWithCorners 𝕜 (E i) (H i))
  (M : Fin 2 → Type*) [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
  (n : WithTop ℕ∞)

def piFinTwo : Diffeomorph (ModelWithCorners.pi I) ((I 0).prod (I 1))
    (∀ i, M i) (M 0 × M 1) n where
  toEquiv := (Homeomorph.piFinTwo M).toEquiv
  contMDiff_toFun := (contMDiff_pi_apply (J := I) 0).prodMk
    (contMDiff_pi_apply (J := I) 1)
  contMDiff_invFun := by
    apply contMDiff_pi.mpr
    exact Fin.forall_fin_two.mpr ⟨contMDiff_fst, contMDiff_snd⟩

@[simp] theorem piFinTwo_apply (x : ∀ i, M i) :
    piFinTwo I M n x = (x 0, x 1) := rfl

@[simp] theorem piFinTwo_symm_apply_zero (x : M 0 × M 1) :
    (piFinTwo I M n).symm x 0 = x.1 := rfl

@[simp] theorem piFinTwo_symm_apply_one (x : M 0 × M 1) :
    (piFinTwo I M n).symm x 1 = x.2 := rfl

end Diffeomorph
