import DifferentialGeometry.Geometry.Metric.CurveSpeed
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel

set_option autoImplicit false

/-! # CH12-S136 G1a: `edist_curve_log_S136` — the distance along a `C¹` curve with `h`-speed `≤ K / σ`

If `c : ℝ → M` is `C¹` on `[s1, s2]` (`0 < s1 ≤ s2`) with `√ h(c', c') ≤ K / σ` on `(s1, s2)`, then
`d_h (c s1) (c s2) ≤ K · log (s2 / s1)` (reparametrise `u = log σ`: constant speed `≤ K`; the bound telescopes
exactly in `log`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry
open Manifold
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem lin_apply_S136 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (L : ℝ →L[ℝ] V) (a : ℝ) :
    L a = a • L 1 := by
  have := L.map_smul a (1 : ℝ)
  rwa [smul_eq_mul, mul_one] at this

theorem bil_smul_S136 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (a : ℝ) (v : V) : B (a • v) (a • v) = a ^ 2 * B v v := by
  simp [map_smul]
  ring

theorem edist_curve_log_S136 {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 3) M) (c : ℝ → M) {s1 s2 K : ℝ} (hK0 : 0 ≤ K) (hs1 : 0 < s1) (h12 : s1 ≤ s2)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 c (Icc s1 s2))
    (hK : ∀ σ ∈ Ioo s1 s2,
      Real.sqrt (g.inner (c σ) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c σ 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c σ 1)) ≤ K / σ) :
    riemannianEDistOf g (c s1) (c s2) ≤ ENNReal.ofReal (K * Real.log (s2 / s1)) := by
  have hs2 : 0 < s2 := hs1.trans_le h12
  have hmaps : MapsTo Real.exp (Icc (Real.log s1) (Real.log s2)) (Icc s1 s2) := by
    intro u hu
    refine ⟨?_, ?_⟩
    · calc s1 = Real.exp (Real.log s1) := (Real.exp_log hs1).symm
        _ ≤ Real.exp u := Real.exp_le_exp.mpr hu.1
    · calc Real.exp u ≤ Real.exp (Real.log s2) := Real.exp_le_exp.mpr hu.2
        _ = s2 := Real.exp_log hs2
  have hexp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 Real.exp :=
    (Real.contDiff_exp.of_le (by exact_mod_cast le_top)).contMDiff
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (c ∘ Real.exp) (Icc (Real.log s1) (Real.log s2)) :=
    hc.comp hexp.contMDiffOn hmaps
  have hlog : Real.log s1 ≤ Real.log s2 := Real.log_le_log hs1 h12
  have key := riemannianEDistOf_le_of_curve_speed_bound g (γ := c ∘ Real.exp) (C := K) hlog hγ ?_
  · have h1 : (c ∘ Real.exp) (Real.log s1) = c s1 := by simp [Function.comp, Real.exp_log hs1]
    have h2 : (c ∘ Real.exp) (Real.log s2) = c s2 := by simp [Function.comp, Real.exp_log hs2]
    rw [h1, h2] at key
    refine key.trans ?_
    rw [← ENNReal.ofReal_mul hK0, ← Real.log_div hs2.ne' hs1.ne']
  · intro u hu
    have hexpu : Real.exp u ∈ Ioo s1 s2 := by
      refine ⟨?_, ?_⟩
      · calc s1 = Real.exp (Real.log s1) := (Real.exp_log hs1).symm
          _ < Real.exp u := Real.exp_lt_exp.mpr hu.1
      · calc Real.exp u < Real.exp (Real.log s2) := Real.exp_lt_exp.mpr hu.2
          _ = s2 := Real.exp_log hs2
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) :=
      (hc.contMDiffAt (Icc_mem_nhds hexpu.1 hexpu.2)).mdifferentiableAt (by simp)
    have hed : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.exp u :=
      (hexp.contMDiffAt).mdifferentiableAt (by simp)
    have hder : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.exp u 1 = Real.exp u := by
      rw [mfderiv_eq_fderiv, (Real.hasDerivAt_exp u).hasFDerivAt.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      change (1 : ℝ) * Real.exp u = Real.exp u
      rw [one_mul]
    have hcomp : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (c ∘ Real.exp) u 1 =
        Real.exp u • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1 := by
      rw [mfderiv_comp u hcd hed]
      change mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Real.exp u 1) = _
      rw [hder]
      exact lin_apply_S136 (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u)) (Real.exp u)
    rw [hcomp]
    have hσ := hK _ hexpu
    have hnn : 0 ≤ g.inner (c (Real.exp u)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1) := metric_inner_self_nonneg _ _ _
    have hq : g.inner (c (Real.exp u)) (Real.exp u • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1)
        (Real.exp u • mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1) =
        Real.exp u ^ 2 * g.inner (c (Real.exp u)) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c (Real.exp u) 1) := by
      exact bil_smul_S136 (g.inner (c (Real.exp u))) (Real.exp u) _
    change Real.sqrt (g.inner (c (Real.exp u)) _ _) ≤ K
    rw [hq, Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos u).le]
    calc Real.exp u * _ ≤ Real.exp u * (K / Real.exp u) :=
          mul_le_mul_of_nonneg_left hσ (Real.exp_pos u).le
      _ = K := by field_simp

end GC.LongTime.Ch12
