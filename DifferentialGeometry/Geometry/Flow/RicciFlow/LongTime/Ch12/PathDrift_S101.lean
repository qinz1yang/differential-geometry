import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MetricWindow_S49
import DifferentialGeometry.Geometry.Metric.CurveSpeed

set_option autoImplicit false

/-! # CH12-S101 G2: length of the image of a slow curve under a near-isometric chart

`edist_image_curve_S101`: if `f` is smooth on an open `A` with `ckErr_S45 H g' c f 0 < δ ≤ 1` there (so
`c · f^*g' ≤ 2 h`), and `γ : [0,1] → A` is `C¹` with `h`-speed `≤ σ`, then `d_{c g'}(f (γ 0), f (γ 1)) ≤ 2 σ`.
Used for both tracks of `HDdist` (the new patch with the isotopy tube of `E_j`, the old patch with its chart). -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12
universe u

theorem edist_image_curve_S101 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g' : SmoothRiemannianMetric (𝓡 3) N) {c : ℝ} (hc : 0 < c) (f : H.Carrier → N)
    (A : Set H.Carrier) (hA : IsOpen A) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f A) {δ σ : ℝ} (hδ : δ ≤ 1)
    (hσ : 0 ≤ σ) (hck : ∀ p ∈ A, ckErr_S45 H g' c f 0 p < δ)
    (γ : ℝ → H.Carrier) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1)) (hγA : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ A)
    (hspd : ∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) ≤ σ ^ 2) :
    riemannianEDistOf (scaleMetric c hc g') (f (γ 0)) (f (γ 1)) ≤ ENNReal.ofReal (2 * σ) := by
  have hfγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ γ) (Icc 0 1) :=
    ((hf.of_le (by exact_mod_cast le_top)).comp hγ hγA : _)
  have := riemannianEDistOf_le_of_curve_speed_bound (scaleMetric c hc g') (γ := f ∘ γ) (a := 0) (b := 1)
    (C := 2 * σ) zero_le_one hfγ ?_
  · simpa using this
  intro s hs
  have hsγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) γ s :=
    ((hγ.contMDiffAt (Icc_mem_nhds hs.1 hs.2)).mdifferentiableAt (by simp))
  have hsf : MDifferentiableAt (𝓡 3) (𝓡 3) f (γ s) :=
    ((hf.contMDiffAt (hA.mem_nhds (hγA s ⟨hs.1.le, hs.2.le⟩))).mdifferentiableAt (by simp))
  have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (f ∘ γ) s 1 =
      mfderiv (𝓡 3) (𝓡 3) f (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) := by
    rw [mfderiv_comp s hsf hsγ]; rfl
  have h1 := pullback_inner_le_of_ckErr_S49 H g' c f (γ s) (hck _ (hγA s ⟨hs.1.le, hs.2.le⟩))
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1)
  have h2 := hspd s hs
  rw [Function.comp_apply, hcomp, scaleMetric_inner]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hnn : 0 ≤ H.metric.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ s 1) :=
    metric_inner_self_nonneg _ _ _
  nlinarith [sq_nonneg σ]

end GC.LongTime.Ch12
