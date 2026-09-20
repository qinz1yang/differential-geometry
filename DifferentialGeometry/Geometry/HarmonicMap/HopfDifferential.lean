import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCoordinates
import DifferentialGeometry.Geometry.Metric.Pullback.Coefficients
import Mathlib.Analysis.Complex.Conformal

noncomputable section

open Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def hopfDifferentialCoefficient (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (z : ℂ) : ℂ :=
  ⟨(g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) -
      g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) / 4,
    -g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z Complex.I) / 2⟩

theorem hopfDifferentialCoefficient_eq_zero_iff
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M) (z : ℂ) :
    hopfDifferentialCoefficient g U z = 0 ↔ DiskMapConformalAt g U z := by
  rw [Complex.ext_iff]
  dsimp only [hopfDifferentialCoefficient, Complex.zero_re, Complex.zero_im, DiskMapConformalAt]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [h₂]; ring, by rw [h₁]; ring⟩

private theorem differentiableAt_diskMapMetricPairing
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    DifferentiableAt ℝ (fun q => g.inner (U q) (diskMapPartial U q v) (diskMapPartial U q w)) z := by
  have h := (contDiffOn_pullback_metric_coefficients g hs hU).contDiffAt (hs.mem_nhds hz)
  exact ((h.clm_apply contDiffAt_const).clm_apply contDiffAt_const).differentiableAt (by simp)

private theorem fderiv_hopfDifferentialCoefficient_apply
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    fderiv ℝ (hopfDifferentialCoefficient g U) z v =
      ⟨(fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)) z v -
        fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q Complex.I)
          (diskMapPartial U q Complex.I)) z v) / 4,
      -fderiv ℝ (fun q => g.inner (U q) (diskMapPartial U q 1)
        (diskMapPartial U q Complex.I)) z v / 2⟩ := by
  have ha := differentiableAt_diskMapMetricPairing g hs hU hz 1 1
  have hb := differentiableAt_diskMapMetricPairing g hs hU hz Complex.I Complex.I
  have hc := differentiableAt_diskMapMetricPairing g hs hU hz 1 Complex.I
  have hprod := ((ha.hasFDerivAt.sub hb.hasFDerivAt).mul_const (4 : ℝ)⁻¹).prodMk
    (hc.hasFDerivAt.neg.mul_const (2 : ℝ)⁻¹)
  have h := Complex.equivRealProdCLM.symm.hasFDerivAt.comp z hprod
  change HasFDerivAt (hopfDifferentialCoefficient g U) _ z at h
  rw [h.fderiv]
  apply Complex.ext <;>
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, smul_eq_mul,
      div_eq_mul_inv] <;> ring

private theorem differentiableAt_hopfDifferentialCoefficient_real
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) : DifferentiableAt ℝ (hopfDifferentialCoefficient g U) z := by
  have ha := differentiableAt_diskMapMetricPairing g hs hU hz 1 1
  have hb := differentiableAt_diskMapMetricPairing g hs hU hz Complex.I Complex.I
  have hc := differentiableAt_diskMapMetricPairing g hs hU hz 1 Complex.I
  have h₁ := (ha.sub hb).mul_const (4 : ℝ)⁻¹
  have h₂ := hc.neg.mul_const (2 : ℝ)⁻¹
  have h := Complex.equivRealProdCLM.symm.differentiableAt.comp z (h₁.prodMk h₂)
  exact h

variable [FiniteDimensional ℝ E]

theorem hopfDifferentialCoefficient_cauchy_riemann
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (hτ : diskMapTension g U z = 0) :
    fderiv ℝ (hopfDifferentialCoefficient g U) z Complex.I =
      Complex.I * fderiv ℝ (hopfDifferentialCoefficient g U) z 1 := by
  have ht : diskMapCovariantPartial g U z Complex.I Complex.I =
      -diskMapCovariantPartial g U z 1 1 := by
    change diskMapCovariantPartial g U z 1 1 + diskMapCovariantPartial g U z Complex.I Complex.I = 0 at hτ
    exact eq_neg_of_add_eq_zero_right hτ
  have hxy := diskMapCovariantPartial_symm g hs hU hz 1 Complex.I
  rw [fderiv_hopfDifferentialCoefficient_apply g hs hU hz,
    fderiv_hopfDifferentialCoefficient_apply g hs hU hz]
  apply Complex.ext
  · simp only [Complex.mul_re]
    norm_num
    simp only [fderiv_diskMapMetricPairing g hs hU hz, ht, hxy, map_neg, _root_.neg_apply]
    simp only [g.symm (U z) (diskMapPartial U z 1),
      g.symm (U z) (diskMapPartial U z Complex.I)]
    ring
  · simp only [Complex.mul_im]
    norm_num
    simp only [fderiv_diskMapMetricPairing g hs hU hz, ht, hxy, map_neg]
    simp only [g.symm (U z) (diskMapPartial U z 1),
      g.symm (U z) (diskMapPartial U z Complex.I)]
    ring

theorem differentiableAt_hopfDifferentialCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (hτ : diskMapTension g U z = 0) :
    DifferentiableAt ℂ (hopfDifferentialCoefficient g U) z := by
  apply differentiableAt_complex_iff_differentiableAt_real.mpr
  exact ⟨differentiableAt_hopfDifferentialCoefficient_real g hs hU hz,
    hopfDifferentialCoefficient_cauchy_riemann g hs hU hz hτ⟩

theorem differentiableOn_hopfDifferentialCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hτ : ∀ z ∈ s, diskMapTension g U z = 0) :
    DifferentiableOn ℂ (hopfDifferentialCoefficient g U) s :=
  fun z hz => (differentiableAt_hopfDifferentialCoefficient g hs hU hz (hτ z hz)).differentiableWithinAt

end DifferentialGeometry.Geometry

end
