import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Chart kernel of the Gauss lemma for a finite-regularity metric

Let `Z(s, t) = (y, η)` be a `C²` family of solutions of the metric spray `∂ₜ Z = metricSpray B Z`
whose speed `B(y)(η, η)` depends on `s` only, through `q(s)`. Then the pairing of the velocity with
the variation field, `P(t) = B(y)(η, ∂ₛ y)` at `s = 0`, has derivative `q'(0) / 2`
(`hasDerivAt_gauss_chart`). This is the computation behind the Gauss lemma: symmetry of the mixed
second derivatives (`ContDiffAt.isSymmSndFDerivAt`) and the Koszul identity
(`MetricKoszul.metricSpray_snd_apply`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ContinuousDualEquiv E]

local instance gaussBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance gaussBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- **Gauss chart kernel.** -/
theorem hasDerivAt_gauss_chart {B : E → E →L[ℝ] E →L[ℝ] ℝ} {Z : ℝ × ℝ → E × E} {t₀ : ℝ}
    {q : ℝ → ℝ} {c : ℝ}
    (hZ : ContDiffAt ℝ 2 Z (0, t₀))
    (hflow : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀),
      HasDerivAt (fun t => Z (p.1, t)) (metricSpray B (Z p)) p.2)
    (hB : DifferentiableAt ℝ B (Z (0, t₀)).1) (hco : IsCoercive (B (Z (0, t₀)).1))
    (hsym : ∀ v w, B (Z (0, t₀)).1 v w = B (Z (0, t₀)).1 w v)
    (hspeed : (fun s => B (Z (s, t₀)).1 (Z (s, t₀)).2 (Z (s, t₀)).2) =ᶠ[𝓝 0] q)
    (hq : HasDerivAt q c 0) :
    HasDerivAt (fun t => B (Z (0, t)).1 (Z (0, t)).2 (fderiv ℝ Z (0, t) (1, 0)).1) (c / 2) t₀ := by
  set D1 := fderiv ℝ Z with hD1def
  set D2 := fderiv ℝ D1 (0, t₀) with hD2def
  set y₀ := (Z (0, t₀)).1
  set η₀ := (Z (0, t₀)).2
  set Y₀ := (D1 (0, t₀) (1, 0)).1
  set W₀ := (D1 (0, t₀) (1, 0)).2
  -- regularity
  have hZev : ∀ᶠ p in 𝓝 ((0 : ℝ), t₀), DifferentiableAt ℝ Z p :=
    (hZ.eventually (by simp)).mono fun p hp => hp.differentiableAt (by simp)
  have hD1d : DifferentiableAt ℝ D1 (0, t₀) :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hsymm : ∀ a b, D2 a b = D2 b a :=
    hZ.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  -- slices
  have hslice_t : ∀ s : ℝ, HasDerivAt (fun t : ℝ => (s, t)) ((0 : ℝ), (1 : ℝ)) t₀ := fun s =>
    (hasDerivAt_const t₀ s).prodMk (hasDerivAt_id t₀)
  have hslice_s : HasDerivAt (fun s : ℝ => (s, t₀)) ((1 : ℝ), (0 : ℝ)) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 t₀)
  have hZs : HasDerivAt (fun s : ℝ => Z (s, t₀)) (D1 (0, t₀) (1, 0)) 0 :=
    (hZev.self_of_nhds.hasFDerivAt).comp_hasDerivAt 0 hslice_s
  have hZt : HasDerivAt (fun t : ℝ => Z (0, t)) (metricSpray B (Z (0, t₀))) t₀ :=
    hflow.self_of_nhds
  -- the time derivative of the variation field
  have hD1t : HasDerivAt (fun t : ℝ => D1 (0, t)) (D2 (0, 1)) t₀ :=
    hD1d.hasFDerivAt.comp_hasDerivAt t₀ (hslice_t 0)
  have hD1s : HasDerivAt (fun s : ℝ => D1 (s, t₀)) (D2 (1, 0)) 0 :=
    hD1d.hasFDerivAt.comp_hasDerivAt 0 hslice_s
  have hspray_s : (fun s : ℝ => (D1 (s, t₀) (0, 1)).1) =ᶠ[𝓝 0] fun s => (Z (s, t₀)).2 := by
    have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (s, t₀) ∈ {p : ℝ × ℝ | DifferentiableAt ℝ Z p ∧
        HasDerivAt (fun t => Z (p.1, t)) (metricSpray B (Z p)) p.2} :=
      hslice_s.continuousAt.preimage_mem_nhds (hZev.and hflow)
    filter_upwards [hev] with s hs
    have h1 : HasDerivAt (fun t : ℝ => Z (s, t)) (D1 (s, t₀) (0, 1)) t₀ :=
      hs.1.hasFDerivAt.comp_hasDerivAt t₀ (hslice_t s)
    have h2 := h1.unique hs.2
    rw [h2]
    rfl
  have hW : (D2 (1, 0) (0, 1)).1 = W₀ := by
    have h1 : HasDerivAt (fun s : ℝ => (D1 (s, t₀) (0, 1)).1) (D2 (1, 0) (0, 1)).1 0 := by
      have h := (hD1s.clm_apply (hasDerivAt_const (0 : ℝ) ((0 : ℝ), (1 : ℝ))))
      simp only [map_zero, add_zero] at h
      exact (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0 h
    have h2 : HasDerivAt (fun s : ℝ => (Z (s, t₀)).2) W₀ 0 :=
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hZs
    exact (h1.congr_of_eventuallyEq hspray_s.symm).unique h2 |>.symm.symm
  have hY : HasDerivAt (fun t : ℝ => (D1 (0, t) (1, 0)).1) W₀ t₀ := by
    have h := (hD1t.clm_apply (hasDerivAt_const t₀ ((1 : ℝ), (0 : ℝ))))
    simp only [map_zero, add_zero] at h
    have h' := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ h
    rw [hsymm] at h'
    change HasDerivAt (fun t => (D1 (0, t) (1, 0)).1) (D2 (1, 0) (0, 1)).1 t₀ at h'
    rw [hW] at h'
    exact h'
  -- the pairing
  have hy : HasDerivAt (fun t : ℝ => (Z (0, t)).1) η₀ t₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ hZt
  have hη : HasDerivAt (fun t : ℝ => (Z (0, t)).2) (metricSpray B (Z (0, t₀))).2 t₀ :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ hZt
  have hBy : HasDerivAt (fun t : ℝ => B (Z (0, t)).1) (fderiv ℝ B y₀ η₀) t₀ :=
    hB.hasFDerivAt.comp_hasDerivAt t₀ hy
  have hP := (hBy.clm_apply hη).clm_apply hY
  -- the speed
  have hys : HasDerivAt (fun s : ℝ => (Z (s, t₀)).1) Y₀ 0 :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hZs
  have hηs : HasDerivAt (fun s : ℝ => (Z (s, t₀)).2) W₀ 0 :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt 0 hZs
  have hBs : HasDerivAt (fun s : ℝ => B (Z (s, t₀)).1) (fderiv ℝ B y₀ Y₀) 0 :=
    hB.hasFDerivAt.comp_hasDerivAt 0 hys
  have hQ := (hBs.clm_apply hηs).clm_apply hηs
  have hc := (hQ.congr_of_eventuallyEq hspeed.symm).unique hq
  -- algebra
  have hk := metricSpray_snd_apply B y₀ η₀ Y₀ hco
  convert hP using 1
  simp only [add_apply] at hc ⊢
  have hZ0 : (y₀, η₀) = Z (0, t₀) := rfl
  rw [hZ0] at hk
  rw [hk, ← hc, hsym W₀ η₀]
  ring

end DifferentialGeometry.MetricKoszul
