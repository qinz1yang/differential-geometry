import DifferentialGeometry.Topology.Manifold.HalfClosedInterval

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E H P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace P] [ChartedSpace H P]

theorem contMDiff_halfClosedInterval_of_val {a b : ℝ} (hab : a < b)
    (f : P → Ico a b) (hf : ContMDiff I 𝓘(ℝ) ∞ (fun p => (f p).val)) :
    let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
    ContMDiff I (𝓡∂ 1) ∞ f := by
  let : ChartedSpace (EuclideanHalfSpace 1) (Ico a b) := halfClosedIntervalChartedSpace hab
  let e : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).symm
  have hc : ContMDiff I (𝓡 1) ∞ (fun p => e ((f p).val - a)) :=
    e.contDiff.contMDiff.comp (hf.sub contMDiff_const)
  dsimp only
  intro p
  rw [contMDiffAt_iff_target]
  refine ⟨_root_.Topology.IsInducing.subtypeVal.continuousAt_iff.mpr hf.continuous.continuousAt, ?_⟩
  have he : (extChartAt (𝓡∂ 1) (f p) ∘ f) = (fun q => e ((f q).val - a)) := by
    funext q
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (extChartAt (𝓡∂ 1) (f p) (f q)) 0 = (f q).val - a
    exact halfClosedInterval_extChartAt_apply hab (f p) (f q)
  rw [he]
  exact hc.contMDiffAt
end DifferentialGeometry.Topology.Manifold
