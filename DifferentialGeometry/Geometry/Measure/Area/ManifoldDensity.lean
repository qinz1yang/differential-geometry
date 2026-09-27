import DifferentialGeometry.Geometry.Measure.Area.Riemannian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions










noncomputable section

open Bundle Manifold DifferentialGeometry Filter
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def riemannianAreaDensity (g : SmoothRiemannianMetric I M) (u : ℂ → M) (z : ℂ) : ℝ :=
  tangentTwoJacobian g (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))
    (mfderiv 𝓘(ℝ, ℂ) I u z Complex.I)

theorem riemannianAreaDensity_nonneg (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) (z : ℂ) : 0 ≤ riemannianAreaDensity g u z :=
  tangentTwoJacobian_nonneg _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt
    (g : SmoothRiemannianMetric I M) {u : ℂ → M} {z : ℂ}
    (hu : ¬ MDifferentiableAt 𝓘(ℝ, ℂ) I u z) : riemannianAreaDensity g u z = 0 := by
  simp [riemannianAreaDensity, mfderiv_zero_of_not_mdifferentiableAt hu,
    tangentTwoJacobian]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem riemannianAreaDensity_const (g : SmoothRiemannianMetric I M)
    (q : M) (z : ℂ) : riemannianAreaDensity g (fun _ => q) z = 0 := by
  simp [riemannianAreaDensity, tangentTwoJacobian]

theorem riemannianAreaDensity_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (u : ℂ → M) (z : ℂ) :
    riemannianAreaDensity (scaleMetric c hc g) u z = c * riemannianAreaDensity g u z :=
  tangentTwoJacobian_scaleMetric _ _ _ _ _

theorem riemannianAreaDensity_congr (g : SmoothRiemannianMetric I M)
    {u v : ℂ → M} {z : ℂ} (h : u =ᶠ[𝓝 z] v) :
    riemannianAreaDensity g u z = riemannianAreaDensity g v z := by
  unfold riemannianAreaDensity tangentTwoJacobian
  rw [h.mfderiv_eq, h.eq_of_nhds]



theorem tangentTwoJacobian_mono (g h : SmoothRiemannianMetric I M) {x : M}
    (hgh : ∀ v : TangentSpace I x, g.inner x v v ≤ h.inner x v v)
    (v w : TangentSpace I x) : tangentTwoJacobian g v w ≤ tangentTwoJacobian h v w := by
  have hh := tangentTwoJacobian_le_of_combinations h g (v := v) (w := w)
    (v' := v) (w' := w) (L := 1) zero_le_one (fun a b => by
      simpa only [one_mul] using Real.sqrt_le_sqrt (hgh (a • v + b • w)))
  simpa only [one_pow, one_mul] using hh

theorem riemannianAreaDensity_mono (g h : SmoothRiemannianMetric I M)
    (hgh : ∀ (x : M) (v : TangentSpace I x), g.inner x v v ≤ h.inner x v v)
    (u : ℂ → M) (z : ℂ) : riemannianAreaDensity g u z ≤ riemannianAreaDensity h u z :=
  tangentTwoJacobian_mono g h (hgh (u z)) _ _

theorem riemannianAreaDensity_metric_upper (g h : SmoothRiemannianMetric I M)
    {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace I x), h.inner x v v ≤ c * g.inner x v v)
    (u : ℂ → M) (z : ℂ) : riemannianAreaDensity h u z ≤ c * riemannianAreaDensity g u z := by
  rw [← riemannianAreaDensity_scaleMetric g c hc]
  apply riemannianAreaDensity_mono
  intro x v
  simpa only [scaleMetric_inner] using hgh x v

theorem riemannianAreaDensity_metric_lower (g h : SmoothRiemannianMetric I M)
    {c : ℝ} (hc : 0 < c)
    (hgh : ∀ (x : M) (v : TangentSpace I x), c * g.inner x v v ≤ h.inner x v v)
    (u : ℂ → M) (z : ℂ) : c * riemannianAreaDensity g u z ≤ riemannianAreaDensity h u z := by
  rw [← riemannianAreaDensity_scaleMetric g c hc]
  apply riemannianAreaDensity_mono
  intro x v
  simpa only [scaleMetric_inner] using hgh x v

section Chart

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ, E) ∞ N]



def chartAreaDensity (g : SmoothRiemannianMetric 𝓘(ℝ, E) N) (p : N)
    (ξ : E) (A : ℂ →L[ℝ] E) : ℝ :=
  tangentTwoJacobian g
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ (A 1))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E p).symm ξ (A Complex.I))

omit [NormedSpace ℝ E] [IsManifold 𝓘(ℝ, E) ∞ N] in
theorem chart_reconstruction_eventuallyEq {u : ℂ → N} {z : ℂ} (p : N)
    (hu : ContinuousAt u z) (hp : u z ∈ (chartAt E p).source) :
    ((chartAt E p).symm ∘ ((chartAt E p) ∘ u)) =ᶠ[𝓝 z] u := by
  filter_upwards [hu ((chartAt E p).open_source.mem_nhds hp)] with w hw
  exact (chartAt E p).left_inv hw



theorem mdifferentiableAt_iff_differentiableAt_chart {u : ℂ → N} {z : ℂ}
    (p : N) (hu : ContinuousAt u z) (hp : u z ∈ (chartAt E p).source) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z ↔
      DifferentiableAt ℝ ((chartAt E p) ∘ u) z := by
  have hc := mdifferentiableAt_atlas (I := 𝓘(ℝ, E)) (ChartedSpace.chart_mem_atlas p) hp
  have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
    (ChartedSpace.chart_mem_atlas p) ((chartAt E p).map_source hp)
  constructor
  · intro h
    exact mdifferentiableAt_iff_differentiableAt.mp (hc.comp z h)
  · intro h
    have hh := hi.comp z (mdifferentiableAt_iff_differentiableAt.mpr h)
    exact hh.congr_of_eventuallyEq (chart_reconstruction_eventuallyEq p hu hp).symm

set_option backward.isDefEq.respectTransparency false in


theorem riemannianAreaDensity_eq_chart (g : SmoothRiemannianMetric 𝓘(ℝ, E) N)
    {u : ℂ → N} {z : ℂ} (p : N) (hu : ContinuousAt u z)
    (hp : u z ∈ (chartAt E p).source) :
    riemannianAreaDensity g u z =
      chartAreaDensity g p ((chartAt E p) (u z))
        (fderiv ℝ ((chartAt E p) ∘ u) z) := by
  by_cases hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) u z
  · have hc := (mdifferentiableAt_iff_differentiableAt_chart p hu hp).mp hd
    have hi := mdifferentiableAt_atlas_symm (I := 𝓘(ℝ, E))
      (ChartedSpace.chart_mem_atlas p) ((chartAt E p).map_source hp)
    have heq := chart_reconstruction_eventuallyEq p hu hp
    rw [← riemannianAreaDensity_congr g heq]
    unfold riemannianAreaDensity chartAreaDensity
    rw [mfderiv_comp z hi (mdifferentiableAt_iff_differentiableAt.mpr hc),
      mfderiv_eq_fderiv]
    rfl
  · rw [riemannianAreaDensity_eq_zero_of_not_mdifferentiableAt g hd]
    have hc : ¬ DifferentiableAt ℝ ((chartAt E p) ∘ u) z :=
      fun h => hd ((mdifferentiableAt_iff_differentiableAt_chart p hu hp).mpr h)
    simp [chartAreaDensity, fderiv_zero_of_not_differentiableAt hc, tangentTwoJacobian]

end Chart

theorem riemannianAreaDensity_le_mfderiv_speeds
    (g : SmoothRiemannianMetric I M) (u : ℂ → M) (z : ℂ) :
    riemannianAreaDensity g u z ≤
      Real.sqrt (g.inner (u z) (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) I u z (1 : ℂ))) *
      Real.sqrt (g.inner (u z) (mfderiv 𝓘(ℝ, ℂ) I u z Complex.I)
        (mfderiv 𝓘(ℝ, ℂ) I u z Complex.I)) := by
  unfold riemannianAreaDensity
  exact tangentTwoJacobian_le g _ _

end DifferentialGeometry.Geometry
