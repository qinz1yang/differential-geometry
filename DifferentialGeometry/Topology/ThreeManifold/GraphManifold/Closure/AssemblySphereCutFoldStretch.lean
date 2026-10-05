import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.EmbeddedPieces

/-!
# Chapter-14 assembly, L2 COMPARE A6-c, part 1: the height stretch of the fold

Lane ASM-L2d. The fold of the closed comparison reads the shell `1 ≤ ‖x‖ ≤ 2` of a shell ball chart,
whose cut-collar height is `s₀ + μ (‖x‖ - 1)`, at the stretched height `foldStretch a s₀ μ (‖x‖ - 1)`:

* `foldStretch a s₀ μ t = a t` for `t ≤ 1/4` (`foldStretch_of_le`) — the same slope `a` on both
  sides of the seam, so that the collar of the connected sum is smooth;
* `foldStretch a s₀ μ t = s₀ + μ t` for `t ≥ 1/2` (`foldStretch_of_ge`) — the fold of the core;
* smooth, with derivative `≥ a > 0` for `t ≥ 0` when `0 < a ≤ μ`, `0 < s₀`
  (`deriv_foldStretch_pos`), hence strictly increasing on `[0, 1]` and a local diffeomorphism of
  the line at every `t > 0` (`isLocalDiffeomorphAt_foldStretch`);
* onto `[0, s₀ + μ]` from `[0, 1]` (`exists_foldStretch_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The smooth step `t ↦ φ (4 t - 1)`: `0` for `t ≤ 1/4`, `1` for `t ≥ 1/2`. -/
def foldStep (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1)

/-- The height stretch of the fold. -/
def foldStretch (a s₀ μ t : ℝ) : ℝ := a * t + foldStep t * (s₀ + (μ - a) * t)

theorem foldStep_of_le {t : ℝ} (ht : t ≤ 1 / 4) : foldStep t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem foldStep_of_ge {t : ℝ} (ht : 1 / 2 ≤ t) : foldStep t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem foldStep_nonneg (t : ℝ) : 0 ≤ foldStep t := Real.smoothTransition.nonneg _

theorem monotone_foldStep : Monotone foldStep := fun s t hst =>
  Real.smoothTransition.monotone (by linarith)

theorem contDiff_foldStep : ContDiff ℝ ∞ foldStep :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem foldStretch_of_le (a s₀ μ : ℝ) {t : ℝ} (ht : t ≤ 1 / 4) :
    foldStretch a s₀ μ t = a * t := by
  rw [foldStretch, foldStep_of_le ht, zero_mul, add_zero]

theorem foldStretch_of_ge (a s₀ μ : ℝ) {t : ℝ} (ht : 1 / 2 ≤ t) :
    foldStretch a s₀ μ t = s₀ + μ * t := by
  rw [foldStretch, foldStep_of_ge ht, one_mul]
  ring

theorem foldStretch_zero (a s₀ μ : ℝ) : foldStretch a s₀ μ 0 = 0 := by
  rw [foldStretch_of_le a s₀ μ (by norm_num), mul_zero]

theorem foldStretch_one (a s₀ μ : ℝ) : foldStretch a s₀ μ 1 = s₀ + μ := by
  rw [foldStretch_of_ge a s₀ μ (by norm_num), mul_one]

theorem contDiff_foldStretch (a s₀ μ : ℝ) : ContDiff ℝ ∞ (foldStretch a s₀ μ) :=
  (contDiff_const.mul contDiff_id).add
    (contDiff_foldStep.mul (contDiff_const.add (contDiff_const.mul contDiff_id)))

theorem continuous_foldStretch (a s₀ μ : ℝ) : Continuous (foldStretch a s₀ μ) :=
  (contDiff_foldStretch a s₀ μ).continuous

theorem hasDerivAt_foldStretch (a s₀ μ t : ℝ) :
    HasDerivAt (foldStretch a s₀ μ)
      (a + (deriv foldStep t * (s₀ + (μ - a) * t) + foldStep t * (μ - a))) t := by
  have h1 : HasDerivAt (fun t : ℝ => a * t) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt foldStep (deriv foldStep t) t :=
    ((contDiff_foldStep.differentiable (by simp)) t).hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => s₀ + (μ - a) * t) (μ - a) t := by
    simpa using ((hasDerivAt_id t).const_mul (μ - a)).const_add s₀
  exact h1.add (h2.mul h3)

/-- A smooth function of the line with nonzero derivative at a point is a local diffeomorphism
there. -/
theorem isLocalDiffeomorphAt_of_hasDerivAt {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {t d : ℝ}
    (hd : HasDerivAt f d t) (hd0 : d ≠ 0) : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ f t := by
  have hb : Bijective (fderiv ℝ f t) := by
    rw [hd.hasFDerivAt.fderiv]
    constructor
    · intro v w hvw
      have h' : v * d = w * d := hvw
      exact mul_right_cancel₀ hd0 h'
    · intro w
      refine ⟨w / d, ?_⟩
      change w / d * d = w
      exact div_mul_cancel₀ w hd0
  refine GC.Seifert.isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective hf.contMDiff
    BoundarylessManifold.isInteriorPoint ?_
  rw [mfderiv_eq_fderiv]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  exact (ContinuousLinearEquiv.bijective _).comp (hb.comp (ContinuousLinearEquiv.bijective _))

variable {a s₀ μ : ℝ} (ha : 0 < a) (haμ : a ≤ μ) (hs₀ : 0 < s₀)
include ha haμ hs₀

theorem deriv_foldStretch_pos {t : ℝ} (ht : 0 ≤ t) : 0 < deriv (foldStretch a s₀ μ) t := by
  rw [(hasDerivAt_foldStretch a s₀ μ t).deriv]
  have h1 : 0 ≤ deriv foldStep t := monotone_foldStep.deriv_nonneg
  have h2 : 0 < s₀ + (μ - a) * t := by nlinarith
  have h3 := foldStep_nonneg t
  have h4 : 0 ≤ μ - a := by linarith
  have := mul_nonneg h1 h2.le
  have := mul_nonneg h3 h4
  linarith

theorem strictMonoOn_foldStretch : StrictMonoOn (foldStretch a s₀ μ) (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0) (continuous_foldStretch a s₀ μ).continuousOn ?_
  intro t ht
  rw [interior_Ici] at ht
  exact deriv_foldStretch_pos ha haμ hs₀ (le_of_lt ht)

theorem foldStretch_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ foldStretch a s₀ μ t := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [foldStretch_zero]
  · rw [← foldStretch_zero a s₀ μ]
    exact (strictMonoOn_foldStretch ha haμ hs₀ (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.le) ht).le

theorem foldStretch_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) : foldStretch a s₀ μ t ≤ s₀ + μ := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [foldStretch_one]
  · rw [← foldStretch_one a s₀ μ]
    exact (strictMonoOn_foldStretch ha haμ hs₀ (mem_Ici.mpr ht0) (mem_Ici.mpr zero_le_one) ht).le

theorem foldStretch_injOn : InjOn (foldStretch a s₀ μ) (Ici 0) :=
  (strictMonoOn_foldStretch ha haμ hs₀).injOn

omit ha haμ hs₀ in
theorem exists_foldStretch_eq {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ s₀ + μ) :
    ∃ t ∈ Icc (0 : ℝ) 1, foldStretch a s₀ μ t = h := by
  have hivt := intermediate_value_Icc (zero_le_one' ℝ)
    (continuous_foldStretch a s₀ μ).continuousOn
  rw [foldStretch_zero, foldStretch_one] at hivt
  exact hivt ⟨h0, h1⟩

theorem isLocalDiffeomorphAt_foldStretch {t : ℝ} (ht : 0 ≤ t) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (foldStretch a s₀ μ) t :=
  isLocalDiffeomorphAt_of_hasDerivAt (contDiff_foldStretch a s₀ μ)
    (hasDerivAt_foldStretch a s₀ μ t).differentiableAt.hasDerivAt
    (deriv_foldStretch_pos ha haμ hs₀ ht).ne'

/-- The signed stretch `r ↦ σ · foldStretch (r - 1)` (`σ = ± 1`) is a local diffeomorphism at every
`r ≥ 1`. -/
theorem isLocalDiffeomorphAt_signedFoldStretch {σ : ℝ} (hσ : σ ≠ 0) {r : ℝ} (hr : 1 ≤ r) :
    IsLocalDiffeomorphAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun r => σ * foldStretch a s₀ μ (r - 1)) r := by
  have hd : HasDerivAt (fun r => σ * foldStretch a s₀ μ (r - 1))
      (σ * deriv (foldStretch a s₀ μ) (r - 1)) r := by
    have h := ((hasDerivAt_foldStretch a s₀ μ (r - 1)).differentiableAt.hasDerivAt.comp r
      ((hasDerivAt_id r).sub_const 1))
    simpa using h.const_mul σ
  refine isLocalDiffeomorphAt_of_hasDerivAt
    (contDiff_const.mul ((contDiff_foldStretch a s₀ μ).comp (contDiff_id.sub contDiff_const))) hd ?_
  exact mul_ne_zero hσ (deriv_foldStretch_pos ha haμ hs₀ (by linarith)).ne'

end GC.GraphManifold.Assembly
