import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Analysis.ODE.BarrierInvariance
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open Set
open scoped BigOperators Topology

variable {l1 l2 l3 : ℝ → ℝ} {K a b : ℝ}

private theorem continuous_of_hasDerivAt {f : ℝ → ℝ} {v : ℝ → ℝ}
    (h : ∀ t : ℝ, HasDerivAt f (v t) t) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  exact (h x).continuousAt

private theorem reactionODE_vbound
    (l1 l3 m1 m2 D₁ D₂ D₃ R v : ℝ)
    (hD : v = 2 * (D₁ * (l1 + m1) + l3 * D₂ + m2 * D₃))
    (hRl1 : |l1| ≤ R) (hRm1 : |m1| ≤ R) (hRm2 : |m2| ≤ R)
    (hRl3 : |l3| ≤ R) :
    |v| ≤ 2 * (2 * R * |D₁| + R * |D₂| + R * |D₃|) := by
  have hsum : |D₁ * (l1 + m1) + l3 * D₂ + m2 * D₃| ≤
      2 * R * |D₁| + R * |D₂| + R * |D₃| := by
    have habsA : |D₁ * (l1 + m1)| ≤ 2 * R * |D₁| := by
      have htri : |l1 + m1| ≤ |l1| + |m1| := abs_add_le l1 m1
      have hle : |l1| + |m1| ≤ 2 * R := by nlinarith [hRl1, hRm1]
      calc
        |D₁ * (l1 + m1)| = |D₁| * |l1 + m1| := abs_mul D₁ (l1 + m1)
        _ ≤ |D₁| * (2 * R) := mul_le_mul_of_nonneg_left (htri.trans hle) (abs_nonneg D₁)
        _ = 2 * R * |D₁| := by ring
    have habsB : |l3 * D₂| ≤ R * |D₂| := by
      calc
        |l3 * D₂| = |l3| * |D₂| := abs_mul l3 D₂
        _ ≤ R * |D₂| := mul_le_mul_of_nonneg_right hRl3 (abs_nonneg D₂)
    have habsC : |m2 * D₃| ≤ R * |D₃| := by
      calc
        |m2 * D₃| = |m2| * |D₃| := abs_mul m2 D₃
        _ ≤ R * |D₃| := mul_le_mul_of_nonneg_right hRm2 (abs_nonneg D₃)
    have hx1 := abs_add_le (D₁ * (l1 + m1) + l3 * D₂) (m2 * D₃)
    have hx2 := abs_add_le (D₁ * (l1 + m1)) (l3 * D₂)
    nlinarith
  have habs : |v| = 2 * |D₁ * (l1 + m1) + l3 * D₂ + m2 * D₃| := by
    rw [hD, abs_mul, abs_of_nonneg]
    norm_num
  rw [habs]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2)

private theorem reactionODE_eineq_bound
    (D₁ D₂ D₃ R v₁ v₂ v₃ e : ℝ)
    (hv1 : |v₁| ≤ 2 * (2 * R * |D₁| + R * |D₂| + R * |D₃|))
    (hv2 : |v₂| ≤ 2 * (2 * R * |D₂| + R * |D₃| + R * |D₁|))
    (hv3 : |v₃| ≤ 2 * (2 * R * |D₃| + R * |D₁| + R * |D₂|))
    (hR : 0 ≤ R) (he : |D₁| ^ 2 + |D₂| ^ 2 + |D₃| ^ 2 = e) :
    2 * (D₁ * v₁ + D₂ * v₂ + D₃ * v₃) ≤ 16 * R * e := by
  have ht1 : D₁ * v₁ ≤ 2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) := by
    have hle := mul_le_mul_of_nonneg_left hv1 (abs_nonneg D₁)
    have h1 : |D₁ * v₁| = |D₁| * |v₁| := abs_mul D₁ v₁
    have hle' : |D₁| * |v₁| ≤ 2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) := by
      have hr : |D₁| * (2 * (2 * R * |D₁| + R * |D₂| + R * |D₃|)) =
          2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) := by ring
      rw [← hr]
      exact hle
    exact (le_abs_self _).trans (h1.symm ▸ hle')
  have ht2 : D₂ * v₂ ≤ 2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) := by
    have hle := mul_le_mul_of_nonneg_left hv2 (abs_nonneg D₂)
    have h1 : |D₂ * v₂| = |D₂| * |v₂| := abs_mul D₂ v₂
    have hle' : |D₂| * |v₂| ≤ 2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) := by
      have hr : |D₂| * (2 * (2 * R * |D₂| + R * |D₃| + R * |D₁|)) =
          2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) := by ring
      rw [← hr]
      exact hle
    exact (le_abs_self _).trans (h1.symm ▸ hle')
  have ht3 : D₃ * v₃ ≤ 2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) := by
    have hle := mul_le_mul_of_nonneg_left hv3 (abs_nonneg D₃)
    have h1 : |D₃ * v₃| = |D₃| * |v₃| := abs_mul D₃ v₃
    have hle' : |D₃| * |v₃| ≤ 2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) := by
      have hr : |D₃| * (2 * (2 * R * |D₃| + R * |D₁| + R * |D₂|)) =
          2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) := by ring
      rw [← hr]
      exact hle
    exact (le_abs_self _).trans (h1.symm ▸ hle')
  have hsumle : D₁ * v₁ + D₂ * v₂ + D₃ * v₃ ≤
      2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) +
      2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) +
      2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) :=
    (add_le_add (add_le_add ht1 ht2) ht3)
  have hcross1 : |D₁| * |D₂| ≤ (|D₁| ^ 2 + |D₂| ^ 2) / 2 := by
    have hsq : 0 ≤ (|D₁| - |D₂|) ^ 2 := sq_nonneg _
    ring_nf at hsq ⊢
    linarith
  have hcross2 : |D₁| * |D₃| ≤ (|D₁| ^ 2 + |D₃| ^ 2) / 2 := by
    have hsq : 0 ≤ (|D₁| - |D₃|) ^ 2 := sq_nonneg _
    ring_nf at hsq ⊢
    linarith
  have hcross3 : |D₂| * |D₃| ≤ (|D₂| ^ 2 + |D₃| ^ 2) / 2 := by
    have hsq : 0 ≤ (|D₂| - |D₃|) ^ 2 := sq_nonneg _
    ring_nf at hsq ⊢
    linarith
  have hcrosssum : |D₁| * |D₂| + |D₁| * |D₃| + |D₂| * |D₃| ≤
      |D₁| ^ 2 + |D₂| ^ 2 + |D₃| ^ 2 := by
    nlinarith [hcross1, hcross2, hcross3]
  have henonneg : 0 ≤ e := by
    rw [← he]
    nlinarith [sq_nonneg (|D₁|), sq_nonneg (|D₂|), sq_nonneg (|D₃|)]
  have hreduced : 2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) +
      2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) +
      2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) ≤
      8 * R * e := by
    have hexp : 2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) +
        2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) +
        2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|) =
        4 * R * (|D₁| ^ 2 + |D₂| ^ 2 + |D₃| ^ 2) +
          4 * R * (|D₁| * |D₂| + |D₁| * |D₃| + |D₂| * |D₃|) := by
      ring_nf
    rw [hexp, ← he]
    have hcrosssum' : |D₁| * |D₂| + |D₁| * |D₃| + |D₂| * |D₃| ≤ e := by
      rw [← he]
      exact hcrosssum
    have hc1 : 4 * R * (|D₁| * |D₂| + |D₁| * |D₃| + |D₂| * |D₃|) ≤ 4 * R * e :=
      mul_le_mul_of_nonneg_left hcrosssum'
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hR)
    have hc2 : 4 * R * e + 4 * R * e ≤ 8 * R * e := by
      nlinarith [mul_nonneg hR henonneg]
    nlinarith [hc1, hc2]
  have hmul := mul_le_mul_of_nonneg_left hsumle (by norm_num : (0 : ℝ) ≤ 2)
  have h2 : 2 * (2 * |D₁| * (2 * R * |D₁| + R * |D₂| + R * |D₃|) +
      2 * |D₂| * (2 * R * |D₂| + R * |D₃| + R * |D₁|) +
      2 * |D₃| * (2 * R * |D₃| + R * |D₁| + R * |D₂|)) ≤ 16 * R * e := by
    nlinarith [hreduced]
  exact hmul.trans h2

private theorem reactionODE_unique
    {m1 m2 m3 : ℝ → ℝ}
    (h1 : ∀ t : ℝ, HasDerivAt l1 (2 * (l1 t ^ 2 + l2 t * l3 t)) t)
    (h2 : ∀ t : ℝ, HasDerivAt l2 (2 * (l2 t ^ 2 + l1 t * l3 t)) t)
    (h3 : ∀ t : ℝ, HasDerivAt l3 (2 * (l3 t ^ 2 + l1 t * l2 t)) t)
    (h4 : ∀ t : ℝ, HasDerivAt m1 (2 * (m1 t ^ 2 + m2 t * m3 t)) t)
    (h5 : ∀ t : ℝ, HasDerivAt m2 (2 * (m2 t ^ 2 + m1 t * m3 t)) t)
    (h6 : ∀ t : ℝ, HasDerivAt m3 (2 * (m3 t ^ 2 + m1 t * m2 t)) t)
    {t₀ : ℝ} (h0 : l1 t₀ = m1 t₀ ∧ l2 t₀ = m2 t₀ ∧ l3 t₀ = m3 t₀)
    {b : ℝ} (htb : t₀ ≤ b) :
    ∀ t ∈ Set.Icc t₀ b, l1 t = m1 t ∧ l2 t = m2 t ∧ l3 t = m3 t := by
  let D₁ : ℝ → ℝ := fun s => l1 s - m1 s
  let D₂ : ℝ → ℝ := fun s => l2 s - m2 s
  let D₃ : ℝ → ℝ := fun s => l3 s - m3 s
  let e : ℝ → ℝ := fun s => D₁ s ^ 2 + D₂ s ^ 2 + D₃ s ^ 2
  let R : ℝ → ℝ := fun s => |l1 s| + |m1 s| + |l2 s| + |m2 s| + |l3 s| + |m3 s|
  let v₁ : ℝ → ℝ := fun s => 2 * (D₁ s * (l1 s + m1 s) + l3 s * D₂ s + m2 s * D₃ s)
  let v₂ : ℝ → ℝ := fun s => 2 * (D₂ s * (l2 s + m2 s) + l1 s * D₃ s + m3 s * D₁ s)
  let v₃ : ℝ → ℝ := fun s => 2 * (D₃ s * (l3 s + m3 s) + l2 s * D₁ s + m1 s * D₂ s)
  have hD₁' : ∀ s : ℝ, HasDerivAt D₁ (v₁ s) s := by
    intro s
    have hd := (h1 s).sub (h4 s)
    have hval : 2 * (l1 s ^ 2 + l2 s * l3 s) - 2 * (m1 s ^ 2 + m2 s * m3 s) = v₁ s := by
      dsimp [v₁, D₁, D₂, D₃]
      ring
    simpa [hval] using hd
  have hD₂' : ∀ s : ℝ, HasDerivAt D₂ (v₂ s) s := by
    intro s
    have hd := (h2 s).sub (h5 s)
    have hval : 2 * (l2 s ^ 2 + l1 s * l3 s) - 2 * (m2 s ^ 2 + m1 s * m3 s) = v₂ s := by
      dsimp [v₂, D₁, D₂, D₃]
      ring
    simpa [hval] using hd
  have hD₃' : ∀ s : ℝ, HasDerivAt D₃ (v₃ s) s := by
    intro s
    have hd := (h3 s).sub (h6 s)
    have hval : 2 * (l3 s ^ 2 + l1 s * l2 s) - 2 * (m3 s ^ 2 + m1 s * m2 s) = v₃ s := by
      dsimp [v₃, D₁, D₂, D₃]
      ring
    simpa [hval] using hd
  have he' : ∀ s : ℝ, HasDerivAt e (2 * (D₁ s * v₁ s + D₂ s * v₂ s + D₃ s * v₃ s)) s := by
    intro s
    have hsq1 : HasDerivAt (fun t : ℝ => D₁ t * D₁ t) (2 * (D₁ s * v₁ s)) s := by
      have hm := (hD₁' s).mul (hD₁' s)
      have hval : v₁ s * D₁ s + D₁ s * v₁ s = 2 * (D₁ s * v₁ s) := by ring
      simpa [hval] using hm
    have hsq2 : HasDerivAt (fun t : ℝ => D₂ t * D₂ t) (2 * (D₂ s * v₂ s)) s := by
      have hm := (hD₂' s).mul (hD₂' s)
      have hval : v₂ s * D₂ s + D₂ s * v₂ s = 2 * (D₂ s * v₂ s) := by ring
      simpa [hval] using hm
    have hsq3 : HasDerivAt (fun t : ℝ => D₃ t * D₃ t) (2 * (D₃ s * v₃ s)) s := by
      have hm := (hD₃' s).mul (hD₃' s)
      have hval : v₃ s * D₃ s + D₃ s * v₃ s = 2 * (D₃ s * v₃ s) := by ring
      simpa [hval] using hm
    have hall := hsq1.add hsq2
    have htotal := hall.add hsq3
    have hval : (2 * (D₁ s * v₁ s) + 2 * (D₂ s * v₂ s)) + 2 * (D₃ s * v₃ s) =
        2 * (D₁ s * v₁ s + D₂ s * v₂ s + D₃ s * v₃ s) := by ring
    simpa [e, hval, sq] using htotal
  have hR_bounds : ∀ s : ℝ, |l1 s| ≤ R s ∧ |m1 s| ≤ R s ∧ |l2 s| ≤ R s ∧
      |m2 s| ≤ R s ∧ |l3 s| ≤ R s ∧ |m3 s| ≤ R s := by
    intro s
    dsimp [R]
    repeat' constructor
    all_goals nlinarith [abs_nonneg (l1 s), abs_nonneg (m1 s), abs_nonneg (l2 s),
      abs_nonneg (m2 s), abs_nonneg (l3 s), abs_nonneg (m3 s)]
  have hcoord_bounds : ∀ s : ℝ, |v₁ s| ≤ 2 * (2 * R s * |D₁ s| + R s * |D₂ s| + R s * |D₃ s|) ∧
      |v₂ s| ≤ 2 * (2 * R s * |D₂ s| + R s * |D₃ s| + R s * |D₁ s|) ∧
      |v₃ s| ≤ 2 * (2 * R s * |D₃ s| + R s * |D₁ s| + R s * |D₂ s|) := by
    intro s
    have hb := hR_bounds s
    have h1 := reactionODE_vbound (l1 s) (l3 s) (m1 s) (m2 s)
      (D₁ s) (D₂ s) (D₃ s) (R s) (v₁ s) (by dsimp [v₁, D₁, D₂, D₃])
      hb.1 hb.2.1 hb.2.2.2.1 hb.2.2.2.2.1
    have h2 := reactionODE_vbound (l2 s) (l1 s) (m2 s) (m3 s)
      (D₂ s) (D₃ s) (D₁ s) (R s) (v₂ s) (by dsimp [v₂, D₁, D₂, D₃])
      hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.2 hb.1
    have h3 := reactionODE_vbound (l3 s) (l2 s) (m3 s) (m1 s)
      (D₃ s) (D₁ s) (D₂ s) (R s) (v₃ s) (by dsimp [v₃, D₁, D₂, D₃])
      hb.2.2.2.2.1 hb.2.2.2.2.2 hb.2.1 hb.2.2.1
    exact ⟨h1, h2, h3⟩
  have he_ineq : ∀ s ∈ Set.Icc t₀ b, deriv e s ≤ 16 * R s * e s := by
    intro s hs
    have hd : deriv e s = 2 * (D₁ s * v₁ s + D₂ s * v₂ s + D₃ s * v₃ s) := (he' s).deriv
    rw [hd]
    have hcb := hcoord_bounds s
    have habs : 0 ≤ R s := by
      dsimp [R]
      nlinarith [abs_nonneg (l1 s), abs_nonneg (m1 s), abs_nonneg (l2 s),
        abs_nonneg (m2 s), abs_nonneg (l3 s), abs_nonneg (m3 s)]
    have hsq : |D₁ s| ^ 2 + |D₂ s| ^ 2 + |D₃ s| ^ 2 = e s := by
      dsimp [e, D₁, D₂, D₃]
      simp only [sq_abs]
    exact reactionODE_eineq_bound (D₁ s) (D₂ s) (D₃ s) (R s) (v₁ s) (v₂ s) (v₃ s) (e s)
      hcb.1 hcb.2.1 hcb.2.2 habs hsq
  have hneg_ineq : ∀ t ∈ Set.Icc t₀ b, (16 * R t) * (-e t) ≤ deriv (-e) t := by
    intro t ht
    have hd : HasDerivAt (-e) (-deriv e t) t := by
      have hd' := (he' t).neg
      simpa [(he' t).deriv] using hd'
    have hderiv : deriv (-e) t = -deriv e t := hd.deriv
    rw [hderiv]
    rw [show (16 * R t) * (-e t) = -(16 * R t * e t) by ring]
    nlinarith [he_ineq t ht]
  have hu_nonneg := DifferentialGeometry.Analysis.ODE.gronwall_nonneg_on_of_deriv_ge_mul
    (u := fun t => -e t) (β := fun t => 16 * R t) htb
    (by
      intro t ht
      dsimp [R]
      have hc1 := (h1 t).continuousAt.abs
      have hc2 := (h4 t).continuousAt.abs
      have hc3 := (h2 t).continuousAt.abs
      have hc4 := (h5 t).continuousAt.abs
      have hc5 := (h3 t).continuousAt.abs
      have hc6 := (h6 t).continuousAt.abs
      exact continuousAt_const.mul (((((hc1.add hc2).add hc3).add hc4).add hc5).add hc6))
    (by
      dsimp [R]
      have hc1 := continuous_abs.comp (continuous_of_hasDerivAt h1)
      have hc2 := continuous_abs.comp (continuous_of_hasDerivAt h4)
      have hc3 := continuous_abs.comp (continuous_of_hasDerivAt h2)
      have hc4 := continuous_abs.comp (continuous_of_hasDerivAt h5)
      have hc5 := continuous_abs.comp (continuous_of_hasDerivAt h3)
      have hc6 := continuous_abs.comp (continuous_of_hasDerivAt h6)
      exact (((((hc1.add hc2).add hc3).add hc4).add hc5).add hc6).const_mul (16 : ℝ)
        |>.measurable.stronglyMeasurable)
    (by
      intro t ht
      exact (he' t).continuousAt.neg)
    (by
      intro t ht
      exact (he' t).differentiableAt.neg)
    hneg_ineq
    (by
      dsimp [e, D₁, D₂, D₃]
      nlinarith [h0.1, h0.2.1, h0.2.2])
  intro t ht
  have hnonneg : 0 ≤ -e t := hu_nonneg t ht
  have hnonpos : e t ≤ 0 := by nlinarith
  have hzero : e t = 0 := by
    have hpos : 0 ≤ e t := by
      dsimp [e]
      nlinarith [sq_nonneg (D₁ t), sq_nonneg (D₂ t), sq_nonneg (D₃ t)]
    exact le_antisymm hnonpos hpos
  have hD₁₀ : D₁ t = 0 := by
    dsimp [e] at hzero
    nlinarith [sq_nonneg (D₁ t), sq_nonneg (D₂ t), sq_nonneg (D₃ t), hzero]
  have hD₂₀ : D₂ t = 0 := by
    dsimp [e] at hzero
    nlinarith [sq_nonneg (D₁ t), sq_nonneg (D₂ t), sq_nonneg (D₃ t), hzero]
  have hD₃₀ : D₃ t = 0 := by
    dsimp [e] at hzero
    nlinarith [sq_nonneg (D₁ t), sq_nonneg (D₂ t), sq_nonneg (D₃ t), hzero]
  constructor
  · dsimp [D₁] at hD₁₀
    linarith
  constructor
  · dsimp [D₂] at hD₂₀
    linarith
  · dsimp [D₃] at hD₃₀
    linarith

theorem reactionODE_order_preserved
    (h1 : ∀ t : ℝ, HasDerivAt l1 (2 * (l1 t ^ 2 + l2 t * l3 t)) t)
    (h2 : ∀ t : ℝ, HasDerivAt l2 (2 * (l2 t ^ 2 + l1 t * l3 t)) t)
    (h3 : ∀ t : ℝ, HasDerivAt l3 (2 * (l3 t ^ 2 + l1 t * l2 t)) t)
    (hab : a ≤ b) (h21 : l2 a ≤ l1 a) (h32 : l3 a ≤ l2 a) :
    ∀ t ∈ Set.Icc a b, l2 t ≤ l1 t ∧ l3 t ≤ l2 t := by
  have hd : ∀ t ∈ Set.Icc a b, 0 ≤ l1 t - l2 t := by
    refine DifferentialGeometry.Analysis.ODE.gronwall_nonneg_on_of_deriv_ge_mul
      (u := fun t => l1 t - l2 t) (β := fun t => 2 * (l1 t + l2 t - l3 t)) hab ?_ ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact continuousAt_const.mul (((h1 t).continuousAt.add (h2 t).continuousAt).sub (h3 t).continuousAt)
    · exact (continuous_const.mul
        (((continuous_of_hasDerivAt h1).add (continuous_of_hasDerivAt h2)).sub
          (continuous_of_hasDerivAt h3))).measurable.stronglyMeasurable
    · intro t ht
      exact (h1 t).continuousAt.sub (h2 t).continuousAt
    · intro t ht
      exact (h1 t).differentiableAt.sub (h2 t).differentiableAt
    · intro t ht
      have hderiv : HasDerivAt (fun s : ℝ => l1 s - l2 s)
          (2 * ((l1 t - l2 t) * (l1 t + l2 t - l3 t))) t := by
        have hdd := (h1 t).sub (h2 t)
        have hval : 2 * (l1 t ^ 2 + l2 t * l3 t) - 2 * (l2 t ^ 2 + l1 t * l3 t) =
            2 * ((l1 t - l2 t) * (l1 t + l2 t - l3 t)) := by ring
        simpa [hval] using hdd
      rw [hderiv.deriv]
      exact le_of_eq (by ring)
    · linarith
  have he : ∀ t ∈ Set.Icc a b, 0 ≤ l2 t - l3 t := by
    refine DifferentialGeometry.Analysis.ODE.gronwall_nonneg_on_of_deriv_ge_mul
      (u := fun t => l2 t - l3 t) (β := fun t => 2 * (l2 t + l3 t - l1 t)) hab ?_ ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact continuousAt_const.mul (((h2 t).continuousAt.add (h3 t).continuousAt).sub (h1 t).continuousAt)
    · exact (continuous_const.mul
        (((continuous_of_hasDerivAt h2).add (continuous_of_hasDerivAt h3)).sub
          (continuous_of_hasDerivAt h1))).measurable.stronglyMeasurable
    · intro t ht
      exact (h2 t).continuousAt.sub (h3 t).continuousAt
    · intro t ht
      exact (h2 t).differentiableAt.sub (h3 t).differentiableAt
    · intro t ht
      have hderiv : HasDerivAt (fun s : ℝ => l2 s - l3 s)
          (2 * ((l2 t - l3 t) * (l2 t + l3 t - l1 t))) t := by
        have hdd := (h2 t).sub (h3 t)
        have hval : 2 * (l2 t ^ 2 + l1 t * l3 t) - 2 * (l3 t ^ 2 + l1 t * l2 t) =
            2 * ((l2 t - l3 t) * (l2 t + l3 t - l1 t)) := by ring
        simpa [hval] using hdd
      rw [hderiv.deriv]
      exact le_of_eq (by ring)
    · linarith
  intro t ht
  exact ⟨sub_nonneg.mp (hd t ht), sub_nonneg.mp (he t ht)⟩

theorem sectionalSum_lower_of_reactionODE
    (h1 : ∀ t : ℝ, HasDerivAt l1 (2 * (l1 t ^ 2 + l2 t * l3 t)) t)
    (h2 : ∀ t : ℝ, HasDerivAt l2 (2 * (l2 t ^ 2 + l1 t * l3 t)) t)
    (h3 : ∀ t : ℝ, HasDerivAt l3 (2 * (l3 t ^ 2 + l1 t * l2 t)) t)
    (hab : a ≤ b) (hK : 0 < K)
    (h21 : l2 a ≤ l1 a) (h32 : l3 a ≤ l2 a) (hpinch : -K ≤ l3 a) :
    ∀ t ∈ Set.Icc a b, -3 * K / (1 + 4 * K * (t - a)) ≤ sectionalSum3 (l1 t) (l2 t) (l3 t) := by
  let w : ℝ → ℝ := fun t => -3 * K / (1 + 4 * K * (t - a))
  let u : ℝ → ℝ := fun t => sectionalSum3 (l1 t) (l2 t) (l3 t) - w t
  have hS_deriv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s))
      (reactionSectionalSum3 (l1 t) (l2 t) (l3 t)) t := by
    intro t
    have hsum := (h1 t).add (h2 t)
    have htotal := hsum.add (h3 t)
    simpa [sectionalSum3, reactionSectionalSum3,
      DifferentialGeometry.Dim3Reaction.sectionalReaction12,
      DifferentialGeometry.Dim3Reaction.sectionalReaction13,
      DifferentialGeometry.Dim3Reaction.sectionalReaction23] using htotal
  have hw_deriv : ∀ t ∈ Set.Icc a b, HasDerivAt w ((4 / 3 : ℝ) * w t ^ 2) t := by
    intro t ht
    have hdenpos : 0 < 1 + 4 * K * (t - a) := by
      have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
      nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 4) hK).le hta]
    have hdenne : 1 + 4 * K * (t - a) ≠ 0 := ne_of_gt hdenpos
    have hinner : HasDerivAt (fun s : ℝ => 1 + 4 * K * (s - a)) (4 * K) t := by
      have hsub : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) t := by
        simpa only [sub_zero] using (hasDerivAt_id t).sub (hasDerivAt_const t a)
      have hmul := hsub.const_mul (4 * K)
      have hadd := (hasDerivAt_const t (1 : ℝ)).add hmul
      simpa only [zero_add, sub_zero, mul_one] using hadd
    have hdiv : HasDerivAt (fun s : ℝ => -(3 * K) / (1 + 4 * K * (s - a)))
        (((0 : ℝ) * (1 + 4 * K * (t - a)) - -(3 * K) * (4 * K)) /
          (1 + 4 * K * (t - a)) ^ 2) t :=
      (hasDerivAt_const t (-(3 * K))).div hinner hdenne
    have hval : ((0 : ℝ) * (1 + 4 * K * (t - a)) - -3 * K * (4 * K)) /
        (1 + 4 * K * (t - a)) ^ 2 = (4 / 3 : ℝ) * w t ^ 2 := by
      dsimp [w]
      field_simp [hdenne]
      ring
    have hval2 : -(3 * K) = -3 * K := by ring
    simpa only [w, hval, hval2] using hdiv
  have hineq : ∀ t ∈ Set.Icc a b, ((4 / 3 : ℝ) *
      (sectionalSum3 (l1 t) (l2 t) (l3 t) + w t)) * u t ≤ deriv u t := by
    intro t ht
    have hd := (hS_deriv t).sub (hw_deriv t ht)
    have hderiv : deriv u t = reactionSectionalSum3 (l1 t) (l2 t) (l3 t) -
        (4 / 3 : ℝ) * w t ^ 2 := hd.deriv
    rw [hderiv]
    have hmain : (4 / 3 : ℝ) * sectionalSum3 (l1 t) (l2 t) (l3 t) ^ 2 ≤
        reactionSectionalSum3 (l1 t) (l2 t) (l3 t) :=
      reactionSectionalSum3_ge_quadratic (l1 t) (l2 t) (l3 t)
    dsimp [u]
    have hgoal : (4 / 3 : ℝ) * (sectionalSum3 (l1 t) (l2 t) (l3 t) + w t) *
        (sectionalSum3 (l1 t) (l2 t) (l3 t) - w t) ≤
        reactionSectionalSum3 (l1 t) (l2 t) (l3 t) - (4 / 3 : ℝ) * w t ^ 2 := by
      nlinarith [hmain]
    exact hgoal
  have hβ_at : ∀ t ∈ Set.Icc a b,
      ContinuousAt (fun s : ℝ => (4 / 3 : ℝ) *
        (sectionalSum3 (l1 s) (l2 s) (l3 s) + w s)) t := by
    intro t ht
    have hc1 := (h1 t).continuousAt.add (h2 t).continuousAt
    have hc2 := hc1.add (h3 t).continuousAt
    have hc3 := hc2.add (hw_deriv t ht).continuousAt
    have hc4 : ContinuousAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s) + w s) t := by
      simpa only [sectionalSum3] using hc3
    exact hc4.const_mul (4 / 3 : ℝ)
  have hβ_meas : MeasureTheory.StronglyMeasurable
      (fun t => (4 / 3 : ℝ) * (sectionalSum3 (l1 t) (l2 t) (l3 t) + w t)) := by
    have hS : MeasureTheory.StronglyMeasurable
        (fun t => sectionalSum3 (l1 t) (l2 t) (l3 t)) := by
      exact (((continuous_of_hasDerivAt h1).add (continuous_of_hasDerivAt h2)).add
        (continuous_of_hasDerivAt h3)).measurable.stronglyMeasurable
    have hw : MeasureTheory.StronglyMeasurable (fun t => -3 * K / (1 + 4 * K * (t - a))) := by
      have hden : Continuous (fun t : ℝ => 1 + 4 * K * (t - a)) := by
        have hsub : Continuous (fun t : ℝ => t - a) := continuous_id.sub continuous_const
        have hmul : Continuous (fun t : ℝ => 4 * K * (t - a)) := hsub.const_mul (4 * K)
        have hadd := Continuous.add (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))) hmul
        simpa using hadd
      simpa only [div_eq_mul_inv] using
        (hden.measurable.inv).const_mul (-3 * K) |>.stronglyMeasurable
    have hsum := hS.add hw
    exact hsum.const_mul (4 / 3 : ℝ)
  have hu_cont : ∀ t ∈ Set.Icc a b, ContinuousAt u t := by
    intro t ht
    have hc1 := (h1 t).continuousAt.add (h2 t).continuousAt
    have hc2 := hc1.add (h3 t).continuousAt
    have hc3 : ContinuousAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s)) t := by
      simpa only [sectionalSum3] using hc2
    exact hc3.sub (hw_deriv t ht).continuousAt
  have hu_deriv : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ u t := by
    intro t ht
    exact (hS_deriv t).differentiableAt.sub (hw_deriv t ht).differentiableAt
  have hinit : 0 ≤ u a := by
    have hS₀ : -3 * K ≤ sectionalSum3 (l1 a) (l2 a) (l3 a) := by
      unfold sectionalSum3
      nlinarith [h21, h32, hpinch]
    dsimp [u, w]
    have hden1 : 1 + 4 * K * (a - a) = 1 := by
      rw [sub_self, mul_zero, add_zero]
    rw [hden1, div_one]
    nlinarith
  have hu_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ u t :=
    DifferentialGeometry.Analysis.ODE.gronwall_nonneg_on_of_deriv_ge_mul
      (u := u) (β := fun t => (4 / 3 : ℝ) * (sectionalSum3 (l1 t) (l2 t) (l3 t) + w t))
      hab hβ_at hβ_meas hu_cont hu_deriv hineq hinit
  intro t ht
  have hu : 0 ≤ u t := hu_nonneg t ht
  dsimp [u, w] at hu
  nlinarith

private theorem hamiltonIveyBarrier_sub_deriv_eq
    (h1 : ∀ t : ℝ, HasDerivAt l1 (2 * (l1 t ^ 2 + l2 t * l3 t)) t)
    (h2 : ∀ t : ℝ, HasDerivAt l2 (2 * (l2 t ^ 2 + l1 t * l3 t)) t)
    (h3 : ∀ t : ℝ, HasDerivAt l3 (2 * (l3 t ^ 2 + l1 t * l2 t)) t)
    (hK : 0 < K) {t : ℝ} (hl3 : l3 t < 0) (hta : a ≤ t) :
    HasDerivAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s) -
        hamiltonIveyBarrier K (s - a) (pinchHeight3 (l3 s)))
      (reactionSectionalSum3 (l1 t) (l2 t) (l3 t) -
        (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) *
          (Real.log ((-l3 t) / K) + Real.log (1 + 2 * K * (t - a)) - 2)
          + (-l3 t) * (2 * K / (1 + 2 * K * (t - a))))) t := by
  have hS' : HasDerivAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s))
      (reactionSectionalSum3 (l1 t) (l2 t) (l3 t)) t := by
    have hsum := (h1 t).add (h2 t)
    have htotal := hsum.add (h3 t)
    simpa [sectionalSum3, reactionSectionalSum3,
      DifferentialGeometry.Dim3Reaction.sectionalReaction12,
      DifferentialGeometry.Dim3Reaction.sectionalReaction13,
      DifferentialGeometry.Dim3Reaction.sectionalReaction23] using htotal
  have hXpos : 0 < -l3 t := neg_pos.mpr hl3
  have hXeq : pinchHeight3 (l3 t) = -l3 t := by
    dsimp [pinchHeight3]
    rw [max_eq_left (neg_nonneg.mpr hl3.le)]
  have hX : HasDerivAt (fun s : ℝ => pinchHeight3 (l3 s))
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t)) t := by
    have hev : ∀ᶠ s in 𝓝 t, pinchHeight3 (l3 s) = -l3 s := by
      have hpos := (h3 t).continuousAt.eventually (Iio_mem_nhds hl3)
      exact hpos.mono (fun s hs => by
        dsimp [pinchHeight3]
        rw [max_eq_left (neg_nonneg.mpr hs.le)])
    have hneg := (h3 t).neg
    have hcongr := hneg.congr_of_eventuallyEq hev
    simpa [reactionPinchHeight3, DifferentialGeometry.Dim3Reaction.sectionalReaction23]
      using hcongr
  have hden' : HasDerivAt (fun s : ℝ => 1 + 2 * K * (s - a)) (2 * K) t := by
    have hsub : HasDerivAt (fun s : ℝ => s - a) (1 : ℝ) t := by
      simpa only [sub_zero] using (hasDerivAt_id t).sub (hasDerivAt_const t a)
    have hmul := hsub.const_mul (2 * K)
    have hadd := (hasDerivAt_const t (1 : ℝ)).add hmul
    simpa only [zero_add, sub_zero, mul_one] using hadd
  have hdenpos : 0 < 1 + 2 * K * (t - a) := by
    have hta0 : 0 ≤ t - a := sub_nonneg.mpr hta
    nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) hK).le hta0]
  have hlogden : HasDerivAt (fun s : ℝ => Real.log (1 + 2 * K * (s - a)))
      (2 * K / (1 + 2 * K * (t - a))) t :=
    hden'.log (ne_of_gt hdenpos)
  have hXK : HasDerivAt (fun s : ℝ => pinchHeight3 (l3 s) / K)
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / K) t :=
    hX.div_const K
  have hlogX : HasDerivAt (fun s : ℝ => Real.log (pinchHeight3 (l3 s) / K))
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / K / (pinchHeight3 (l3 t) / K)) t :=
    hXK.log (div_ne_zero (hXeq ▸ hXpos.ne') hK.ne')
  have hlogX' : HasDerivAt (fun s : ℝ => Real.log (pinchHeight3 (l3 s) / K))
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t)) t := by
    have hval : reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / K / (pinchHeight3 (l3 t) / K) =
        reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t) := by
      rw [hXeq]
      field_simp [hK.ne', hXpos.ne']
    simpa [hval] using hlogX
  have hlogsum : HasDerivAt (fun s : ℝ => Real.log (pinchHeight3 (l3 s) / K) +
      Real.log (1 + 2 * K * (s - a)) - 3)
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t) + 2 * K / (1 + 2 * K * (t - a))) t := by
    have h := (hlogX'.add hlogden).sub (hasDerivAt_const t (3 : ℝ))
    simpa only [sub_zero] using h
  have hprod := hX.mul hlogsum
  have hbar' : HasDerivAt (fun s : ℝ => hamiltonIveyBarrier K (s - a) (pinchHeight3 (l3 s)))
      (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) *
        (Real.log ((-l3 t) / K) + Real.log (1 + 2 * K * (t - a)) - 2)
        + (-l3 t) * (2 * K / (1 + 2 * K * (t - a)))) t := by
    unfold hamiltonIveyBarrier
    have hval : reactionPinchHeight3 (l1 t) (l2 t) (l3 t) *
        (Real.log (pinchHeight3 (l3 t) / K) + Real.log (1 + 2 * K * (t - a)) - 3)
        + pinchHeight3 (l3 t) *
          (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t) + 2 * K / (1 + 2 * K * (t - a))) =
        reactionPinchHeight3 (l1 t) (l2 t) (l3 t) *
          (Real.log ((-l3 t) / K) + Real.log (1 + 2 * K * (t - a)) - 2)
        + (-l3 t) * (2 * K / (1 + 2 * K * (t - a))) := by
      have h1 : (-l3 t) * (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t)) =
          reactionPinchHeight3 (l1 t) (l2 t) (l3 t) := by
        rw [show reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t) =
            -reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / l3 t by ring]
        rw [show (-l3 t) * (-reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / l3 t) =
            l3 t * (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / l3 t) by ring]
        exact mul_div_cancel₀ (reactionPinchHeight3 (l1 t) (l2 t) (l3 t)) hl3.ne
      have h1' : (-l3 t) * (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) / (-l3 t) +
          2 * K / (1 + 2 * K * (t - a))) =
          reactionPinchHeight3 (l1 t) (l2 t) (l3 t) +
            (-l3 t) * (2 * K / (1 + 2 * K * (t - a))) := by
        rw [mul_add, h1]
      rw [hXeq, h1']
      ring
    simpa [hval] using hprod
  have hu' := hS'.sub hbar'
  exact hu'

theorem hamiltonIveyBarrier_le_sectionalSum_of_reactionODE
    (h1 : ∀ t : ℝ, HasDerivAt l1 (2 * (l1 t ^ 2 + l2 t * l3 t)) t)
    (h2 : ∀ t : ℝ, HasDerivAt l2 (2 * (l2 t ^ 2 + l1 t * l3 t)) t)
    (h3 : ∀ t : ℝ, HasDerivAt l3 (2 * (l3 t ^ 2 + l1 t * l2 t)) t)
    (hab : a ≤ b) (hK : 0 < K)
    (h21 : l2 a ≤ l1 a) (h32 : l3 a ≤ l2 a) (hpinch : -K ≤ l3 a) :
    ∀ t ∈ Set.Icc a b,
      hamiltonIveyBarrier K (t - a) (pinchHeight3 (l3 t)) ≤
        sectionalSum3 (l1 t) (l2 t) (l3 t) := by
  let u : ℝ → ℝ := fun t => sectionalSum3 (l1 t) (l2 t) (l3 t) -
    hamiltonIveyBarrier K (t - a) (pinchHeight3 (l3 t))
  have horder := reactionODE_order_preserved h1 h2 h3 hab h21 h32
  have hu_cont : ∀ t ∈ Set.Icc a b, ContinuousAt u t := by
    intro t ht
    have hS : ContinuousAt (fun s : ℝ => sectionalSum3 (l1 s) (l2 s) (l3 s)) t := by
      simpa only [sectionalSum3] using
        ((h1 t).continuousAt.add (h2 t).continuousAt).add (h3 t).continuousAt
    have hX : ContinuousAt (fun s : ℝ => pinchHeight3 (l3 s)) t :=
      (continuousAt_neg.comp (h3 t).continuousAt).max continuousAt_const
    have hdiv : ContinuousAt (fun s : ℝ => pinchHeight3 (l3 s) / K) t :=
      hX.div_const K
    have hpart1 : ContinuousAt
        (fun s : ℝ => K * (pinchHeight3 (l3 s) / K * Real.log (pinchHeight3 (l3 s) / K))) t := by
      have hcomp : ContinuousAt
          (fun s : ℝ => pinchHeight3 (l3 s) / K * Real.log (pinchHeight3 (l3 s) / K)) t :=
        (Continuous.continuousAt Real.continuous_mul_log).comp hdiv
      exact hcomp.const_mul K
    have hden : ContinuousAt (fun s : ℝ => 1 + 2 * K * (s - a)) t := by
      have hsub : ContinuousAt (fun s : ℝ => s - a) t := continuousAt_id.sub continuousAt_const
      have hmul := hsub.const_mul (2 * K)
      have hadd := ContinuousAt.add (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) t) hmul
      simpa using hadd
    have hlog2 : ContinuousAt (fun s : ℝ => Real.log (1 + 2 * K * (s - a))) t := by
      have hdenpos : 0 < 1 + 2 * K * (t - a) := by
        have hta0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
        nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) hK).le hta0]
      have hg : ContinuousAt Real.log (1 + 2 * K * (t - a)) :=
        Real.continuousAt_log (ne_of_gt hdenpos)
      exact ContinuousAt.comp (g := Real.log) (f := fun s : ℝ => 1 + 2 * K * (s - a)) hg hden
    have hpart2 : ContinuousAt
        (fun s : ℝ => pinchHeight3 (l3 s) * (Real.log (1 + 2 * K * (s - a)) - 3)) t :=
      hX.mul (hlog2.sub continuousAt_const)
    have hbar : ContinuousAt (fun s : ℝ => hamiltonIveyBarrier K (s - a) (pinchHeight3 (l3 s))) t := by
      have hident : ∀ s : ℝ, hamiltonIveyBarrier K (s - a) (pinchHeight3 (l3 s)) =
          K * (pinchHeight3 (l3 s) / K * Real.log (pinchHeight3 (l3 s) / K)) +
            pinchHeight3 (l3 s) * (Real.log (1 + 2 * K * (s - a)) - 3) := by
        intro s
        unfold hamiltonIveyBarrier
        field_simp [hK.ne']
        ring
      exact (hpart1.add hpart2).congr_of_eventuallyEq
        (Filter.Eventually.of_forall hident)
    simpa [u] using hS.sub hbar
  have hzero : ∀ t ∈ Set.Icc a b, u t = 0 →
      (DifferentiableAt ℝ u t ∧ 0 < deriv u t) ∨ ∀ s ∈ Set.Icc t b, u s = 0 := by
    intro t ht hut
    by_cases hl3 : l3 t < 0
    · left
      have hden : 0 < 1 + 2 * K * (t - a) := by
        have hta0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
        nlinarith [mul_nonneg (mul_pos (by norm_num : (0 : ℝ) < 2) hK).le hta0]
      have hboundary : hamiltonIveyBarrier K (t - a) (-(l3 t)) =
          sectionalSum3 (l1 t) (l2 t) (l3 t) := by
        dsimp [u] at hut
        have hXeq : pinchHeight3 (l3 t) = -l3 t := by
          dsimp [pinchHeight3]
          rw [max_eq_left (neg_nonneg.mpr hl3.le)]
        rw [hXeq, sub_eq_zero] at hut
        exact hut.symm
      have hstrict := hamiltonIveyBarrier_reaction_derivative_pos_on_boundary
        (horder t ht).1 (horder t ht).2 hl3 hK hden hboundary
      have hstrict' : 0 < reactionSectionalSum3 (l1 t) (l2 t) (l3 t) -
          (reactionPinchHeight3 (l1 t) (l2 t) (l3 t) *
            (Real.log ((-l3 t) / K) + Real.log (1 + 2 * K * (t - a)) - 2)
            + (-l3 t) * (2 * K / (1 + 2 * K * (t - a)))) := by
        convert hstrict using 1; ring
      have hd := (hamiltonIveyBarrier_sub_deriv_eq h1 h2 h3 hK hl3 ht.1).differentiableAt
      have hdval := (hamiltonIveyBarrier_sub_deriv_eq h1 h2 h3 hK hl3 ht.1).deriv
      constructor
      · simpa [u] using hd
      · rw [hdval]
        exact hstrict'
    · right
      have hnonneg : 0 ≤ l3 t := le_of_not_gt hl3
      have hX0 : pinchHeight3 (l3 t) = 0 := by
        dsimp [pinchHeight3]
        rw [max_eq_right (neg_nonpos.mpr hnonneg)]
      have hbar0 : hamiltonIveyBarrier K (t - a) (pinchHeight3 (l3 t)) = 0 := by
        rw [hX0]
        unfold hamiltonIveyBarrier
        ring
      have hS0 : sectionalSum3 (l1 t) (l2 t) (l3 t) = 0 := by
        dsimp [u] at hut
        rw [hbar0] at hut
        exact sub_eq_zero.mp hut
      have hl1₀ : l1 t = 0 := by
        unfold sectionalSum3 at hS0
        have hordt := horder t ht
        nlinarith
      have hl2₀ : l2 t = 0 := by
        unfold sectionalSum3 at hS0
        have hordt := horder t ht
        nlinarith
      have hl3₀ : l3 t = 0 := by
        unfold sectionalSum3 at hS0
        have hordt := horder t ht
        nlinarith
      have huniq := reactionODE_unique h1 h2 h3
        (fun s => (show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (2 * ((0 : ℝ) ^ 2 + 0 * 0)) s from by
          simpa using hasDerivAt_const s (0 : ℝ)))
        (fun s => (show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (2 * ((0 : ℝ) ^ 2 + 0 * 0)) s from by
          simpa using hasDerivAt_const s (0 : ℝ)))
        (fun s => (show HasDerivAt (fun _ : ℝ => (0 : ℝ)) (2 * ((0 : ℝ) ^ 2 + 0 * 0)) s from by
          simpa using hasDerivAt_const s (0 : ℝ)))
        ⟨hl1₀, hl2₀, hl3₀⟩ ht.2
      intro s hs
      have hzeroes := huniq s hs
      have hX0' : pinchHeight3 (l3 s) = 0 := by
        dsimp [pinchHeight3]
        rw [hzeroes.2.2, neg_zero, max_self]
      have hbar0' : hamiltonIveyBarrier K (s - a) (pinchHeight3 (l3 s)) = 0 := by
        rw [hX0']
        unfold hamiltonIveyBarrier
        ring
      dsimp [u]
      rw [hbar0']
      unfold sectionalSum3
      nlinarith [hzeroes.1, hzeroes.2.1, hzeroes.2.2]
  have hinit : 0 ≤ u a := by
    have hbound := hamiltonIveyBarrier_initial_le_sectionalSum_of_ordered h21 h32 hpinch hK
    simpa [u] using sub_nonneg.mpr hbound
  have hu_nonneg := DifferentialGeometry.Analysis.ODE.barrier_nonneg_on_of_derivPos_or_constAfter_of_zero
    (u := u) hu_cont hinit hzero
  intro t ht
  have hu : 0 ≤ u t := hu_nonneg t ht
  dsimp [u] at hu
  exact sub_nonneg.mp hu

end DifferentialGeometry.Geometry.Curvature.DimensionThree
