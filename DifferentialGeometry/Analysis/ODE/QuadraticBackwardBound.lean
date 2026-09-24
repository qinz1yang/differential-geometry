import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Set Filter
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis.ODE

theorem le_of_quadratic_deriv_bound
    {r r' : ℝ → ℝ} {a b q A B t : ℝ} {C : ℝ≥0}
    (hA : 0 < A) (hB : 0 < B) (hqA : q ≤ A)
    (hc : ContinuousOn r (Icc a b))
    (hd : ∀ s ∈ Ioo a b, q < r s → HasDerivAt r (r' s) s)
    (hb : ∀ s ∈ Ioo a b, q < r s → |r' s| ≤ C * r s ^ 2)
    (hend : r b ≤ A) (ht : t ∈ Icc a b)
    (htime : C * (b - t) ≤ A⁻¹ - B⁻¹) : r t ≤ B := by
  have hlip := DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    hA hc (fun s hs hAs => hd s hs (hqA.trans_lt hAs))
    (fun s hs hAs => hb s hs (hqA.trans_lt hAs))
  have hrec := hlip.dist_le_mul b ⟨ht.1.trans ht.2, le_rfl⟩ t ht
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2),
    max_eq_left hend] at hrec
  have hlow : B⁻¹ ≤ (max A (r t))⁻¹ := by linarith [(le_abs_self (A⁻¹ - (max A (r t))⁻¹))]
  exact (le_max_right _ _).trans
    ((inv_le_inv₀ hB (hA.trans_le (le_max_left _ _))).mp hlow)

theorem eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {r r' : ι → ℝ → X → ℝ} {rInf : X → ℝ}
    {q : ι → ℝ} {σ b ε : ℝ} {C : ℝ≥0}
    (htime : 6 * C * ε * max σ 1 ≤ 1)
    (hconv : TendstoUniformlyOn (fun i x => r i b x) rInf l K)
    (hlim : ∀ x ∈ K, rInf x ≤ σ)
    (hq : ∀ᶠ i in l, q i ≤ max σ 1)
    (hc : ∀ᶠ i in l, ∀ x ∈ K, ContinuousOn (fun t => r i t x) (Icc (b - ε) b))
    (hd : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - ε) b,
      q i < r i t x → HasDerivAt (fun s => r i s x) (r' i t x) t)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - ε) b,
      q i < r i t x → |r' i t x| ≤ C * r i t x ^ 2) :
    ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - ε) b, r i t x ≤ 2 * max σ 1 := by
  let Q := max σ 1
  have hQ : 0 < Q := zero_lt_one.trans_le (le_max_right _ _)
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hconv) (Q / 2) (by positivity)
  filter_upwards [hq, hc, hd, hb, hclose] with i hiq hic hid hib hiclose
  intro x hx t ht
  have hend : r i b x ≤ (3 / 2 : ℝ) * Q := by
    have hdist := hiclose x hx
    rw [Real.dist_eq] at hdist
    have hsQ : σ ≤ Q := le_max_left _ _
    have hdiff := (abs_lt.mp hdist).1
    have hlimx := hlim x hx
    linarith
  apply le_of_quadratic_deriv_bound (q := q i) (r' := fun s => r' i s x)
    (by positivity : 0 < (3 / 2 : ℝ) * Q) (by positivity : 0 < 2 * Q)
    (by dsimp [Q] at *; linarith) (hic x hx) (hid x hx) (hib x hx) hend ht
  have hsmall : C * (b - t) ≤ (6 * Q)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
    have htε : b - t ≤ ε := by linarith [ht.1]
    have hmul := mul_le_mul_of_nonneg_left htε C.coe_nonneg
    change 6 * C * ε * Q ≤ 1 at htime
    nlinarith
  have heq : ((3 / 2 : ℝ) * Q)⁻¹ - (2 * Q)⁻¹ = (6 * Q)⁻¹ := by
    field_simp
    ring
  rw [heq]
  exact hsmall

theorem eventually_le_two_mul_on_backward_interval_of_tendstoUniformlyOn
    {ι X : Type*} {l : Filter ι} {K : Set X}
    {r r' : ι → ℝ → X → ℝ} {q : ι → ℝ} {σ b : ℝ} {C : ℝ≥0}
    (hC : 0 < C)
    (hconv : TendstoUniformlyOn (fun i x => r i b x) (fun _ => σ) l K)
    (hq : ∀ᶠ i in l, q i ≤ max σ 1)
    (hc : ∀ᶠ i in l, ∀ x ∈ K,
      ContinuousOn (fun t => r i t x) (Icc (b - (6 * C * max σ 1)⁻¹) b))
    (hd : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (6 * C * max σ 1)⁻¹) b,
      q i < r i t x → HasDerivAt (fun s => r i s x) (r' i t x) t)
    (hb : ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Ioo (b - (6 * C * max σ 1)⁻¹) b,
      q i < r i t x → |r' i t x| ≤ C * r i t x ^ 2) :
    0 < (6 * C * max σ 1)⁻¹ ∧
      ∀ᶠ i in l, ∀ x ∈ K, ∀ t ∈ Icc (b - (6 * C * max σ 1)⁻¹) b,
        r i t x ≤ 2 * max σ 1 := by
  have hQ : 0 < max σ 1 := zero_lt_one.trans_le (le_max_right _ _)
  have hC' : 0 < (C : ℝ) := hC
  have hpos : 0 < 6 * (C : ℝ) * max σ 1 := by positivity
  refine ⟨inv_pos.mpr hpos, ?_⟩
  apply eventually_le_two_mul_of_tendstoUniformlyOn_of_quadratic_deriv_bound
    (σ := σ) (C := C) ?_ hconv (fun _ _ => le_rfl) hq hc hd hb
  have heq : 6 * C * (6 * C * max σ 1)⁻¹ * max σ 1 = 1 := by
    calc
      6 * C * (6 * C * max σ 1)⁻¹ * max σ 1 =
          (6 * C * max σ 1) * (6 * C * max σ 1)⁻¹ := by ring
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  exact heq.le

end DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Analysis

theorem derivWithin_const_mul_comp_affine_Iic
    {f : ℝ → ℝ} {T Q s : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (Iic (T + s / Q)) (T + s / Q)) :
    derivWithin (fun u => Q⁻¹ * f (T + u / Q)) (Iic s) s =
      Q⁻¹ ^ 2 * derivWithin f (Iic (T + s / Q)) (T + s / Q) := by
  have htime : HasDerivAt (fun u : ℝ => T + u / Q) Q⁻¹ s := by
    have hh : HasDerivAt (fun u : ℝ => u / Q) (1 / Q) s :=
      (hasDerivAt_id s).div_const Q
    rw [one_div] at hh
    exact hh.const_add T
  have hmaps : MapsTo (fun u : ℝ => T + u / Q) (Iic s) (Iic (T + s / Q)) := by
    intro u hu
    exact add_le_add_right (div_le_div_of_nonneg_right hu hQ.le) T
  have hd := (hf.hasDerivWithinAt.comp s htime.hasDerivWithinAt hmaps).const_mul Q⁻¹
  calc
    _ = Q⁻¹ * (derivWithin f (Iic (T + s / Q)) (T + s / Q) * Q⁻¹) :=
      hd.derivWithin (uniqueDiffWithinAt_Iic s)
    _ = _ := by ring

theorem abs_derivWithin_comp_affine_le_sq
    {f : ℝ → ℝ} {T Q s q C : ℝ} (hQ : 0 < Q)
    (hf : DifferentiableWithinAt ℝ f (Iic (T + s / Q)) (T + s / Q))
    (hb : q < f (T + s / Q) →
      |derivWithin f (Iic (T + s / Q)) (T + s / Q)| ≤ C * f (T + s / Q) ^ 2)
    (hhigh : q / Q < Q⁻¹ * f (T + s / Q)) :
    |derivWithin (fun u => Q⁻¹ * f (T + u / Q)) (Iic s) s| ≤
      C * (Q⁻¹ * f (T + s / Q)) ^ 2 := by
  have hh : q < f (T + s / Q) := by
    rw [inv_mul_eq_div] at hhigh
    exact (div_lt_div_iff_of_pos_right hQ).mp hhigh
  rw [derivWithin_const_mul_comp_affine_Iic hQ hf, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    Q⁻¹ ^ 2 * |derivWithin f (Iic (T + s / Q)) (T + s / Q)| ≤
        Q⁻¹ ^ 2 * (C * f (T + s / Q) ^ 2) :=
      mul_le_mul_of_nonneg_left (hb hh) (sq_nonneg _)
    _ = _ := by ring

end DifferentialGeometry.Analysis
