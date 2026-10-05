import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.Topology.Manifold.CollarStretch

/-!
# Chapter-14 assembly, relative COMPARE G3: the neck profile

Lane ASM-L2e, group G3. The neck of the comparison is the seam collar of `W` reparametrised by a
diffeomorphism of the line which agrees with one affine map on `[a, ∞)` (the shell of one capped
side) and with another one on `(-∞, -a]` (the shell of the other side). With
`ℓ₀ s = c₀ + m₀ s`, `ℓ₁ s = c₁ + m₁ s` and the smooth transition `β` from `-a` to `a`,

  `neckProfile s = ℓ₁ s + β s · (ℓ₀ s - ℓ₁ s)`,

whose derivative `(1 - β) m₁ + β m₀ + β' (ℓ₀ - ℓ₁)` is positive as soon as `ℓ₀ ≥ ℓ₁` on `[-a, a]`,
which the hypothesis `|m₀ - m₁| a ≤ c₀ - c₁` guarantees (`exists_neckProfile`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The neck profile: `ℓ₁` on `(-∞, -a]`, `ℓ₀` on `[a, ∞)`, a smooth transition between. -/
def neckProfile (a m₀ m₁ c₀ c₁ s : ℝ) : ℝ :=
  (c₁ + m₁ * s) + Real.smoothTransition ((s + a) / (2 * a)) * ((c₀ - c₁) + (m₀ - m₁) * s)

variable {a m₀ m₁ c₀ c₁ : ℝ}

theorem neckProfile_of_le (ha : 0 < a) {s : ℝ} (hs : a ≤ s) :
    neckProfile a m₀ m₁ c₀ c₁ s = c₀ + m₀ * s := by
  have h1 : 1 ≤ (s + a) / (2 * a) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  rw [neckProfile, Real.smoothTransition.one_of_one_le h1]
  ring

theorem neckProfile_of_le_neg (ha : 0 < a) {s : ℝ} (hs : s ≤ -a) :
    neckProfile a m₀ m₁ c₀ c₁ s = c₁ + m₁ * s := by
  have h0 : (s + a) / (2 * a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [neckProfile, Real.smoothTransition.zero_of_nonpos h0]
  ring

theorem contDiff_neckProfile : ContDiff ℝ ∞ (neckProfile a m₀ m₁ c₀ c₁) := by
  unfold neckProfile
  apply (contDiff_const.add (contDiff_const.mul contDiff_id)).add
  apply ContDiff.mul
  · exact (Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_id.add contDiff_const).div_const _)
  · exact contDiff_const.add (contDiff_const.mul contDiff_id)

/-- The derivative of the neck profile. -/
theorem hasDerivAt_neckProfile (s : ℝ) :
    HasDerivAt (neckProfile a m₀ m₁ c₀ c₁)
      (m₁ + (deriv Real.smoothTransition ((s + a) / (2 * a)) * (1 / (2 * a)) *
        ((c₀ - c₁) + (m₀ - m₁) * s) +
        Real.smoothTransition ((s + a) / (2 * a)) * (m₀ - m₁))) s := by
  have hl : HasDerivAt (fun s : ℝ => c₁ + m₁ * s) m₁ s := by
    simpa using ((hasDerivAt_id s).const_mul m₁).const_add c₁
  have hin : HasDerivAt (fun s : ℝ => (s + a) / (2 * a)) (1 / (2 * a)) s := by
    simpa using ((hasDerivAt_id s).add_const a).div_const (2 * a)
  have hβ : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition ((s + a) / (2 * a))) ((s + a) / (2 * a)) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have hg : HasDerivAt (fun s : ℝ => (c₀ - c₁) + (m₀ - m₁) * s) (m₀ - m₁) s := by
    simpa using ((hasDerivAt_id s).const_mul (m₀ - m₁)).const_add (c₀ - c₁)
  have hβc := hβ.comp s hin
  have hprod := hβc.mul hg
  exact hl.add hprod

/-- Off the transition interval the derivative of the smooth transition vanishes. -/
theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) :
    deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [he.deriv_eq, deriv_const]
  · have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [he.deriv_eq, deriv_const]

theorem neckProfile_deriv_pos (ha : 0 < a) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁)
    (hgap : |m₀ - m₁| * a ≤ c₀ - c₁) (s : ℝ) :
    0 < m₁ + (deriv Real.smoothTransition ((s + a) / (2 * a)) * (1 / (2 * a)) *
        ((c₀ - c₁) + (m₀ - m₁) * s) +
        Real.smoothTransition ((s + a) / (2 * a)) * (m₀ - m₁)) := by
  set b := Real.smoothTransition ((s + a) / (2 * a))
  set b' := deriv Real.smoothTransition ((s + a) / (2 * a))
  have hb0 : 0 ≤ b := Real.smoothTransition.nonneg _
  have hb1 : b ≤ 1 := Real.smoothTransition.le_one _
  have hb' : 0 ≤ b' := Real.smoothTransition.monotone.deriv_nonneg
  have hkey : 0 ≤ b' * (1 / (2 * a)) * ((c₀ - c₁) + (m₀ - m₁) * s) := by
    by_cases hs : |s| ≤ a
    · apply mul_nonneg (mul_nonneg hb' (by positivity))
      have h1 : -(|m₀ - m₁| * a) ≤ (m₀ - m₁) * s := by
        have h2 : |(m₀ - m₁) * s| ≤ |m₀ - m₁| * a := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hs (abs_nonneg _)
        linarith [neg_abs_le ((m₀ - m₁) * s)]
      linarith
    · have hb'0 : b' = 0 := by
        apply deriv_smoothTransition_eq_zero
        rcases lt_or_gt_of_ne (show |s| ≠ a from fun h => hs h.le) with h | h
        · exact (hs h.le).elim
        · rcases le_or_gt 0 s with h0 | h0
          · right
            rw [abs_of_nonneg h0] at h
            rw [lt_div_iff₀ (by linarith)]
            linarith
          · left
            rw [abs_of_neg h0] at h
            exact div_neg_of_neg_of_pos (by linarith) (by linarith)
      rw [hb'0]
      simp
  have hconv : 0 < m₁ + b * (m₀ - m₁) := by
    have : m₁ + b * (m₀ - m₁) = (1 - b) * m₁ + b * m₀ := by ring
    rw [this]
    rcases eq_or_lt_of_le hb1 with h | h
    · rw [h]
      linarith
    · have h1 : 0 < (1 - b) * m₁ := mul_pos (by linarith) hm₁
      nlinarith [mul_nonneg hb0 hm₀.le]
  linarith

/-- **G3 (ASM-L2e).** A diffeomorphism of the line with prescribed affine germs on `[a, ∞)` and
`(-∞, -a]`. -/
theorem exists_neckProfile (ha : 0 < a) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁)
    (hgap : |m₀ - m₁| * a ≤ c₀ - c₁) :
    ∃ h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ, StrictMono h ∧
      (∀ s, a ≤ s → h s = c₀ + m₀ * s) ∧ ∀ s, s ≤ -a → h s = c₁ + m₁ * s := by
  let f := neckProfile a m₀ m₁ c₀ c₁
  have hderiv (s : ℝ) := hasDerivAt_neckProfile (a := a) (m₀ := m₀) (m₁ := m₁) (c₀ := c₀)
    (c₁ := c₁) s
  have hpos (s : ℝ) := neckProfile_deriv_pos ha hm₀ hm₁ hgap s
  have hmono : StrictMono f := strictMono_of_deriv_pos fun s => by
    rw [(hderiv s).deriv]
    exact hpos s
  have hsurj : Surjective f := by
    refine contDiff_neckProfile.continuous.surjective ?_ ?_
    · have he : f =ᶠ[atTop] fun s => c₀ + m₀ * s := by
        filter_upwards [eventually_ge_atTop a] with s hs
        exact neckProfile_of_le ha hs
      exact (tendsto_atTop_add_const_left _ c₀
        (tendsto_id.const_mul_atTop hm₀)).congr' he.symm
    · have he : f =ᶠ[atBot] fun s => c₁ + m₁ * s := by
        filter_upwards [eventually_le_atBot (-a)] with s hs
        exact neckProfile_of_le_neg ha hs
      exact (tendsto_atBot_add_const_left _ c₁
        (tendsto_id.const_mul_atBot hm₁)).congr' he.symm
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective f hmono hsurj
  have hsymm : ContDiff ℝ ∞ e.symm :=
    Homeomorph.contDiff_symm_deriv e.toHomeomorph (fun s => ne_of_gt (hpos s)) hderiv
      contDiff_neckProfile
  refine ⟨{ toEquiv := e.toEquiv
            contMDiff_toFun := contDiff_neckProfile.contMDiff
            contMDiff_invFun := hsymm.contMDiff }, hmono, ?_, ?_⟩
  · intro s hs
    exact neckProfile_of_le ha hs
  · intro s hs
    exact neckProfile_of_le_neg ha hs

end GC.GraphManifold.Assembly
