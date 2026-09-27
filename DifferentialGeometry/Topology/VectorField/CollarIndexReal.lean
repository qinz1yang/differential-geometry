import DifferentialGeometry.Topology.VectorField.CollarExtension
import DifferentialGeometry.Topology.LocalDegree.Real

set_option autoImplicit false
open Set
open scoped Manifold Topology
noncomputable section
namespace DifferentialGeometry.VectorField
open DifferentialGeometry.LocalDegree
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


theorem realIsolatedZero_collarExtension_normal {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {x : M} {t : ℝ} (hb : b x ≠ 0)
    (hz : collarExtension T b collarTransition (x, t) = 0) :
    realIsolatedZero (fun s => (collarExtension T b collarTransition (x, s)).2) t := by
  have hd := hasDerivAt_collarExtension_normal (T := T) (b := b) (x := x)
    (contDiff_collarTransition.differentiable (by simp) t).hasDerivAt
  have hc : Continuous (fun s => (collarExtension T b collarTransition (x, s)).2) := by
    change Continuous (fun s => (1 - collarTransition s) * b x + collarTransition s)
    exact ((continuous_const.sub contDiff_collarTransition.continuous).mul continuous_const).add
      contDiff_collarTransition.continuous
  apply realIsolatedZero_of_hasDerivAt (s := univ) (by simp) hc.continuousOn
    (congrArg Prod.snd hz) hd
  have hp := collarExtension_normal_deriv_pos (fun _ => hb) hz
  rw [hd.deriv] at hp
  exact hp.ne'

theorem realLocalDegree_collarExtension_normal {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {x : M} {t : ℝ} (hb : b x ≠ 0)
    (hz : collarExtension T b collarTransition (x, t) = 0) :
    realLocalDegree (fun s => (collarExtension T b collarTransition (x, s)).2) t
      (realIsolatedZero_collarExtension_normal hb hz) = 1 := by
  have hd := hasDerivAt_collarExtension_normal (T := T) (b := b) (x := x)
    (contDiff_collarTransition.differentiable (by simp) t).hasDerivAt
  have hp := collarExtension_normal_deriv_pos (fun _ => hb) hz
  rw [hd.deriv] at hp
  rw [realLocalDegree_eq_sign_of_hasDerivAt _ hd hp.ne', sign_pos hp]
  rfl

end DifferentialGeometry.VectorField
