import DifferentialGeometry.Bundle.Hom
import DifferentialGeometry.Geometry.Metric.Basic
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

def pullbackMetricCoefficients (g : SmoothRiemannianMetric I M) (f : V → M) (x : V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  let D : V →L[ℝ] E := mfderiv 𝓘(ℝ, V) I f x
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner (f x)
  G.bilinearComp D D

@[simp]
theorem pullbackMetricCoefficients_apply (g : SmoothRiemannianMetric I M)
    (f : V → M) (x v w : V) :
    pullbackMetricCoefficients g f x v w =
      g.inner (f x) (mfderiv 𝓘(ℝ, V) I f x v) (mfderiv 𝓘(ℝ, V) I f x w) := rfl

theorem pullbackMetricCoefficients_isPosSemidef (g : SmoothRiemannianMetric I M)
    (f : V → M) (x : V) :
    LinearMap.IsPosSemidef (pullbackMetricCoefficients g f x).toBilinForm := by
  refine ⟨⟨fun v w => g.symm (f x) _ _⟩, ⟨fun v => ?_⟩⟩
  exact metric_inner_self_nonneg g (f x) (mfderiv 𝓘(ℝ, V) I f x v)

theorem pullbackMetricCoefficients_pos (g : SmoothRiemannianMetric I M)
    {f : V → M} {x : V} (hinj : Function.Injective (mfderiv 𝓘(ℝ, V) I f x))
    {v : V} (hv : v ≠ 0) : 0 < pullbackMetricCoefficients g f x v v := by
  apply g.pos
  intro hzero
  apply hv
  apply hinj
  exact hzero.trans (map_zero (mfderiv 𝓘(ℝ, V) I f x)).symm

private theorem contMDiffAt_source_mfderiv {f : V → M} {x : V}
    (hf : ContMDiffAt 𝓘(ℝ, V) I ∞ f x) :
    ContMDiffAt 𝓘(ℝ, V) (I.prod 𝓘(ℝ, V →L[ℝ] E)) ∞
      (fun y => (⟨f y, mfderiv 𝓘(ℝ, V) I f y⟩ :
        TotalSpace (V →L[ℝ] E)
          (fun m => Bundle.Trivial M V m →L[ℝ] TangentSpace I m))) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨hf, ?_⟩
  have hd := hf.mfderiv_const (m := ∞) (by simp)
  apply hd.congr_of_eventuallyEq
  filter_upwards [] with y
  ext v
  simp [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_def]
  rfl

theorem contDiffOn_pullback_metric_coefficients (g : SmoothRiemannianMetric I M)
    {f : V → M} {U : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) I ∞ f U) :
    ContDiffOn ℝ ∞ (pullbackMetricCoefficients g f) U := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  intro x hx
  have hfx := (hf x hx).contMDiffAt (hU.mem_nhds hx)
  have hD := contMDiffAt_source_mfderiv hfx
  have hG := g.contMDiff.contMDiffAt.comp x hfx
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

theorem pullbackMetricCoefficients_fderiv_symm (g : SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞) {U : V → M} {z : V}
    (hU : MDifferentiableAt 𝓘(ℝ, V) I U z) (hz : U z ∈ Φ.target) (v w : V) :
    let X := Φ.symm ∘ U
    pullbackMetricCoefficients g Φ (X z) (fderiv ℝ X z v) (fderiv ℝ X z w) =
      g.inner (U z) (mfderiv 𝓘(ℝ, V) I U z v) (mfderiv 𝓘(ℝ, V) I U z w) := by
  let X := Φ.symm ∘ U
  have hX : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) X z :=
    ((Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hz)).mdifferentiableAt
      (by simp)).comp z hU
  have hx : X z ∈ Φ.source := Φ.toOpenPartialHomeomorph.map_target hz
  have hΦ : MDifferentiableAt 𝓘(ℝ, E) I Φ (X z) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hr : Φ (X z) = U z := Φ.toOpenPartialHomeomorph.right_inv hz
  have heq : Φ ∘ X =ᶠ[𝓝 z] U := by
    filter_upwards [hU.continuousAt.preimage_mem_nhds (Φ.open_target.mem_nhds hz)] with q hq
    exact Φ.toOpenPartialHomeomorph.right_inv hq
  have hd : (mfderiv 𝓘(ℝ, E) I Φ (X z) : E →L[ℝ] E).comp (fderiv ℝ X z) =
      (mfderiv 𝓘(ℝ, V) I U z : V →L[ℝ] E) := by
    have hc := mfderiv_comp (I := 𝓘(ℝ, V)) (I' := 𝓘(ℝ, E)) (I'' := I) z hΦ hX
    rw [mfderiv_eq_fderiv] at hc
    exact hc.symm.trans heq.mfderiv_eq
  change (g.inner (Φ (X z)) : E →L[ℝ] E →L[ℝ] ℝ)
    (((mfderiv 𝓘(ℝ, E) I Φ (X z) : E →L[ℝ] E).comp (fderiv ℝ X z)) v)
    (((mfderiv 𝓘(ℝ, E) I Φ (X z) : E →L[ℝ] E).comp (fderiv ℝ X z)) w) = _
  rw [hd]
  change (g.inner (Φ (X z)) : E →L[ℝ] E →L[ℝ] ℝ)
    (mfderiv 𝓘(ℝ, V) I U z v) (mfderiv 𝓘(ℝ, V) I U z w) = _
  rw [hr]

end DifferentialGeometry.Geometry
