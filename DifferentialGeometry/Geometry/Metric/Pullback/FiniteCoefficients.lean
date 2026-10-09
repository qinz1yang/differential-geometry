import DifferentialGeometry.Bundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

private theorem contMDiffAt_source_mfderiv_of_le {r s : ℕ∞ω} {f : V → M} {x : V}
    (hf : ContMDiffAt 𝓘(ℝ, V) I s f x) (hrs : r + 1 ≤ s) :
    ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V →L[ℝ] E)) r
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, V) I f y⟩ :
        TotalSpace (V →L[ℝ] E)
          (fun m => Bundle.Trivial M V m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hrs), ?_⟩
  have hd := hf.mfderiv_const (m := r) hrs
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

theorem contDiffOn_pullback_inner {n r s : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hrn : r ≤ n) (hrs : r + 1 ≤ s) {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I s f U) :
    ContDiffOn ℝ r
      (fun y => (g.inner (f y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
        (E := E) (F := E) (E' := V) (F' := V)
        (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)
        (mfderiv 𝓘(ℝ, V) I f y : V →L[ℝ] E)) U := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hD := contMDiffAt_source_mfderiv_of_le hfx hrs
  have hG := (g.contMDiff.of_le hrn).contMDiffAt.comp x
    (hfx.of_le ((le_add_of_nonneg_right zero_le_one).trans hrs))
  have hB := hG.clm_bundle_bilinearComp
    (U₁ := TangentSpace I) (U₂ := TangentSpace I) (U₃ := Bundle.Trivial M ℝ)
    (U₄ := Bundle.Trivial M V) (U₅ := Bundle.Trivial M V) hD hD
  have h := (contMDiffAt_totalSpace.mp hB).2.contDiffAt
  refine (h.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [] with y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, Trivialization.continuousLinearMapAt_apply]
  rfl

end Bundle.ContMDiffRiemannianMetric
