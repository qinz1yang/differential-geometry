import DifferentialGeometry.Analysis.Parabolic.Bernstein.Cutoff
import DifferentialGeometry.Geometry.Operator.Gradient.PowerBounds
import DifferentialGeometry.Geometry.Operator.Gradient.Regularity

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem parabolic_cutoff_pow_mul_le
    {G : MetricConnectionFamily (I := I) (M := M) ℝ} {T ε t : ℝ}
    {χ : ℝ → M → ℝ} {x : M}
    (q : ShiCutoffLowerSupportAt G T ε χ t x)
    (ht : t ∈ Icc 0 T) (hε : 0 ≤ ε)
    (u : ℝ → M → ℝ) (v f : ℝ) (p : ℕ)
    (hu0 : 0 ≤ u t x) (hv0 : 0 ≤ v)
    (hut : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (u t) y) x)
    (huP : parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) u t x ≤
      -2 * v + f)
    (hun : (G.metric t).inner x (gradientFun (G.metric t) (u t) x)
      (gradientFun (G.metric t) (u t) x) ≤ 4 * u t x * v) :
    parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y))
      (fun s y => q.phi s y ^ (p + 1) * u s y) t x ≤
      -(3 / 2 : ℝ) * q.phi t x ^ (p + 1) * v + q.phi t x ^ (p + 1) * f +
        (((p + 1 : ℕ) : ℝ) + 8 * ((p + 1 : ℕ) : ℝ) ^ 2) * ε *
          q.phi t x ^ p * u t x := by
  have hq0 : 0 ≤ q.phi t x :=
    (q.lower_nhds.self_of_nhdsWithin (show (t, x) ∈ spacetimeSlab (M := M) T from
      ⟨ht, mem_univ _⟩)).1
  have hqP := parabolic_pow_le_nhds T (fun _ y => (0 : TangentSpace I y))
    q.phi t x ε hq0 q.time_diff q.space_diff_nhds q.grad_diff q.parabolic_le p
  have hqg : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (fun z => q.phi t z ^ (p + 1)) y) x := by
    apply grad_comp_mdiffAt (G.metric t) (φ := fun r : ℝ => r ^ (p + 1))
      (differentiable_id.pow (p + 1)) _ q.space_diff_nhds q.grad_diff
    have hd : deriv (fun r : ℝ => r ^ (p + 1)) = fun r =>
        ((p + 1 : ℕ) : ℝ) * r ^ p := by
      funext r
      simp
    rw [hd]
    fun_prop
  have hqs : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => q.phi t z ^ (p + 1)) y :=
    q.space_diff_nhds.mono fun _ hy => hy.pow (p + 1)
  have hprod := parabolic_mul_nhds T (fun _ y => (0 : TangentSpace I y))
    (fun s y => q.phi s y ^ (p + 1)) u t x (q.time_diff.pow (p + 1)) hut
    hqs hus hqg hug
  have hcross := neg_two_mul_inner_gradient_pow_le (G.metric t)
    (gradientFun (G.metric t) (u t) x) p
    (a := 4 * u t x) (b := v) (ε := ε) (δ := 1 / 2)
    q.space_diff_nhds.self_of_nhds hq0 (mul_nonneg (by norm_num) hu0)
    hv0 hε (by norm_num) q.grad_sq_le hun
  rw [hprod]
  unfold gradientAt
  have hfirst := mul_le_mul_of_nonneg_left huP (pow_nonneg hq0 (p + 1))
  have hsecond := mul_le_mul_of_nonneg_left hqP hu0
  nlinarith only [hfirst, hsecond, hcross]

private theorem bernstein_first_order_algebra
    {q u v w t c K α ε P₀ P₁ : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (ht : 0 ≤ t) (hc : 0 ≤ c) (hK : 0 ≤ K) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (huK : u ≤ K ^ 2) (htK : t * K ≤ α) (hsmall : 34 * ε * t ≤ 1 / 2)
    (hP₀ : P₀ ≤ -(3 / 2) * q * v + q * (c * u * Real.sqrt u) + 9 * ε * u)
    (hP₁ : P₁ ≤ -(3 / 2) * q ^ 2 * w + q ^ 2 * (2 * c * Real.sqrt u * v) +
      34 * ε * q * v) :
    (1 + 2 * c * α) * P₀ + q ^ 2 * v + t * P₁ ≤
      (1 + 2 * c * α) * c * K ^ 3 + 9 * ε * (1 + 2 * c * α) * K ^ 2 := by
  let β := 1 + 2 * c * α
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have hsqrt : Real.sqrt u ≤ K := (Real.sqrt_le_left hK).mpr huK
  have hq2 : q ^ 2 ≤ q := by nlinarith [hq.1, hq.2]
  have hqv : 0 ≤ q * v := mul_nonneg hq.1 hv
  have hqu : q * u ≤ K ^ 2 :=
    (mul_le_of_le_one_left hu hq.2).trans huK
  have hprod : q * (c * u * Real.sqrt u) ≤ c * K ^ 3 := by
    have h := mul_le_mul hqu hsqrt (Real.sqrt_nonneg u) (sq_nonneg K)
    have hc' := mul_le_mul_of_nonneg_left h hc
    nlinarith only [hc']
  have herr := mul_le_mul_of_nonneg_left huK (mul_nonneg (by norm_num : (0 : ℝ) ≤ 9) hε)
  have hzero : P₀ ≤ -(3 / 2) * q * v + c * K ^ 3 + 9 * ε * K ^ 2 := by
    linarith
  have hsp : 0 ≤ 2 * c * Real.sqrt u := by positivity
  have hscale : t * (2 * c * Real.sqrt u) ≤ 2 * c * α := by
    have h := (mul_le_mul_of_nonneg_left hsqrt ht).trans htK
    have hc' := mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * c by positivity)
    nlinarith only [hc']
  have hsecond : t * (q ^ 2 * (2 * c * Real.sqrt u * v)) ≤ 2 * c * α * (q * v) := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hq2 hv)
      (mul_nonneg ht hsp)
    have h' := mul_le_mul_of_nonneg_right hscale hqv
    nlinarith only [h, h']
  have herr' := mul_le_mul_of_nonneg_right hsmall hqv
  have hneg : -(3 / 2 : ℝ) * t * q ^ 2 * w ≤ 0 := by
    nlinarith only [mul_nonneg (mul_nonneg ht (sq_nonneg q)) hw]
  have h1 := mul_le_mul_of_nonneg_left hP₁ ht
  have h0 := mul_le_mul_of_nonneg_left hzero hβ
  have hqv' := mul_le_mul_of_nonneg_right hq2 hv
  have hrest : 0 ≤ c * α * (q * v) := by positivity
  dsimp only [β] at h0
  nlinarith only [h0, h1, hsecond, herr', hneg, hqv', hrest]

private theorem cutoff_product_regularity
    {G : MetricConnectionFamily (I := I) (M := M) ℝ} {T ε t : ℝ}
    {χ : ℝ → M → ℝ} {x : M}
    (q : ShiCutoffLowerSupportAt G T ε χ t x)
    (u : ℝ → M → ℝ) (p : ℕ)
    (hut : DifferentiableWithinAt ℝ (fun s => u s x) (Icc 0 T) t)
    (hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u t) y)
    (hug : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (u t) y) x) :
    DifferentiableWithinAt ℝ (fun s => q.phi s x ^ (p + 1) * u s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ)
        (fun z => q.phi t z ^ (p + 1) * u t z) y) ∧
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
        gradientFun (G.metric t) (fun z => q.phi t z ^ (p + 1) * u t z) y) x := by
  have hqs : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => q.phi t z ^ (p + 1)) y :=
    q.space_diff_nhds.mono fun _ hy => hy.pow (p + 1)
  refine ⟨(q.time_diff.pow (p + 1)).mul hut,
    (hqs.and hus).mono (fun _ h => h.1.mul h.2), ?_⟩
  apply mdifferentiableAt_gradientFun_mul (G.metric t) hqs hus _ hug
  apply grad_comp_mdiffAt (G.metric t) (φ := fun r : ℝ => r ^ (p + 1))
    (differentiable_id.pow (p + 1)) _ q.space_diff_nhds q.grad_diff
  have hd : deriv (fun r : ℝ => r ^ (p + 1)) = fun r =>
      ((p + 1 : ℕ) : ℝ) * r ^ p := by funext r; simp
  rw [hd]
  fun_prop

private theorem bernstein_combination_data
    {G : MetricConnectionFamily (I := I) (M := M) ℝ}
    (T : ℝ) (X : ℝ → (x : M) → TangentSpace I x) (β : ℝ)
    (A B : ℝ → M → ℝ) (t : ℝ) (x : M)
    (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hat : DifferentiableWithinAt ℝ (fun s => A s x) (Icc 0 T) t)
    (hbt : DifferentiableWithinAt ℝ (fun s => B s x) (Icc 0 T) t)
    (has : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (A t) y)
    (hbs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (B t) y)
    (hag : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (A t) y) x)
    (hbg : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (B t) y) x) :
    let F := fun s y => β * A s y + s * B s y
    DifferentiableWithinAt ℝ (fun s => F s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (F t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
        gradientFun (G.metric t) (F t) y) x ∧
      parabolicOperatorWithDrift G T X F t x =
        β * parabolicOperatorWithDrift G T X A t x + B t x +
          t * parabolicOperatorWithDrift G T X B t x := by
  let U := fun s y => β * A s y
  let V := fun s y => s * B s y
  have hut : DifferentiableWithinAt ℝ (fun s => U s x) (Icc 0 T) t := hat.const_mul β
  have hvt : DifferentiableWithinAt ℝ (fun s => V s x) (Icc 0 T) t :=
    differentiableWithinAt_id.mul hbt
  have hus : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (U t) y :=
    has.mono fun _ hy => hy.const_smul β
  have hvs : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (V t) y :=
    hbs.mono fun _ hy => hy.const_smul t
  have hug := mdifferentiableAt_gradientFun_const_mul (G.metric t) β has hag
  have hvg := mdifferentiableAt_gradientFun_const_mul (G.metric t) t hbs hbg
  refine ⟨hut.add hvt, (hus.and hvs).mono (fun _ h => h.1.add h.2),
    mdifferentiableAt_gradientFun_add (G.metric t) hus hvs hug hvg, ?_⟩
  have hP := parabolic_add_nhds T X U V t x hut hvt hus hvs hug hvg
  have hU := parabolic_smul_nhds T X β A t x has hag
  have hV := parabolic_time_mul_nhds T X id B t x differentiableWithinAt_id hbt hbs hbg
  have hid : derivWithin id (Icc 0 T) t = 1 := (hasDerivWithinAt_id t (Icc 0 T)).derivWithin huniq
  simp only [hid, id_eq, one_mul] at hV
  dsimp only [U, V] at hP
  rw [hP, hU, hV]
  ring

private theorem support_bernstein_data
    {G : MetricConnectionFamily (I := I) (M := M) ℝ} {T ε t : ℝ}
    {χ : ℝ → M → ℝ} {x : M}
    (q : ShiCutoffLowerSupportAt G T ε χ t x)
    (u₀ u₁ u₂ : ℝ → M → ℝ) (c K α : ℝ)
    (ht : t ∈ Icc 0 T) (huniq : UniqueDiffWithinAt ℝ (Icc 0 T) t)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hα : 0 ≤ α) (hε : 0 ≤ ε)
    (hχ : χ t x ∈ Icc (0 : ℝ) 1)
    (hu₀ : 0 ≤ u₀ t x) (hu₁ : 0 ≤ u₁ t x) (hu₂ : 0 ≤ u₂ t x)
    (huK : u₀ t x ≤ K ^ 2) (htK : t * K ≤ α) (hsmall : 34 * ε * t ≤ 1 / 2)
    (ht₀ : DifferentiableWithinAt ℝ (fun s => u₀ s x) (Icc 0 T) t)
    (ht₁ : DifferentiableWithinAt ℝ (fun s => u₁ s x) (Icc 0 T) t)
    (hs₀ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u₀ t) y)
    (hs₁ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u₁ t) y)
    (hg₀ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (u₀ t) y) x)
    (hg₁ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
      gradientFun (G.metric t) (u₁ t) y) x)
    (hP₀ : parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) u₀ t x ≤
      -2 * u₁ t x + c * u₀ t x * Real.sqrt (u₀ t x))
    (hP₁ : parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) u₁ t x ≤
      -2 * u₂ t x + 2 * c * Real.sqrt (u₀ t x) * u₁ t x)
    (hn₀ : (G.metric t).inner x (gradientFun (G.metric t) (u₀ t) x)
      (gradientFun (G.metric t) (u₀ t) x) ≤ 4 * u₀ t x * u₁ t x)
    (hn₁ : (G.metric t).inner x (gradientFun (G.metric t) (u₁ t) x)
      (gradientFun (G.metric t) (u₁ t) x) ≤ 4 * u₁ t x * u₂ t x) :
    let β := 1 + 2 * c * α
    let F := fun s y => β * (q.phi s y * u₀ s y) + s * (q.phi s y ^ 2 * u₁ s y)
    DifferentiableWithinAt ℝ (fun s => F s x) (Icc 0 T) t ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (F t) y) ∧
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M =>
        gradientFun (G.metric t) (F t) y) x ∧
      parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) F t x ≤
        β * c * K ^ 3 + 9 * ε * β * K ^ 2 := by
  let A := fun s y => q.phi s y * u₀ s y
  let B := fun s y => q.phi s y ^ 2 * u₁ s y
  have hA := cutoff_product_regularity q u₀ 0 ht₀ hs₀ hg₀
  simp only [Nat.zero_add, pow_one] at hA
  have hB := cutoff_product_regularity q u₁ 1 ht₁ hs₁ hg₁
  have hdata := bernstein_combination_data T (fun _ y => (0 : TangentSpace I y))
    (1 + 2 * c * α) A B t x huniq hA.1 hB.1 hA.2.1 hB.2.1 hA.2.2 hB.2.2
  refine ⟨hdata.1, hdata.2.1, hdata.2.2.1, ?_⟩
  rw [hdata.2.2.2]
  have hAP := parabolic_cutoff_pow_mul_le q ht hε u₀ (u₁ t x)
    (c * u₀ t x * Real.sqrt (u₀ t x)) 0 hu₀ hu₁ ht₀ hs₀ hg₀ hP₀ hn₀
  have hBP := parabolic_cutoff_pow_mul_le q ht hε u₁ (u₂ t x)
    (2 * c * Real.sqrt (u₀ t x) * u₁ t x) 1 hu₁ hu₂ ht₁ hs₁ hg₁ hP₁ hn₁
  norm_num only [Nat.zero_add, Nat.reduceAdd, Nat.cast_one, Nat.cast_ofNat,
    pow_one, pow_zero, one_pow, mul_one] at hAP hBP
  exact bernstein_first_order_algebra (by simpa only [q.eq_at] using hχ) hu₀ hu₁ hu₂ ht.1 hc hK hα hε
    huK htK hsmall hAP hBP

theorem ParabolicCutoff.bernstein_first_order_estimate
    [I.Boundaryless]
    {G : MetricConnectionFamily (I := I) (M := M) ℝ} {T ε : ℝ}
    (cut : ParabolicCutoff G T ε) (u₀ u₁ u₂ : ℝ → M → ℝ) (c K α : ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hTK : T * K ≤ α) (hsmall : 34 * ε * T ≤ 1 / 2)
    (hu₀ : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u₀ t x)
    (hu₁ : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u₁ t x)
    (hu₂ : ∀ t ∈ Icc 0 T, ∀ x, 0 ≤ u₂ t x)
    (huK : ∀ t ∈ Icc 0 T, ∀ x, 0 < cut.chi t x → u₀ t x ≤ K ^ 2)
    (hcont₀ : ContinuousOn (fun p : ℝ × M => u₀ p.1 p.2) (Icc 0 T ×ˢ cut.support))
    (hcont₁ : ContinuousOn (fun p : ℝ × M => u₁ p.1 p.2) (Icc 0 T ×ˢ cut.support))
    (ht₀ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => u₀ s x) (Icc 0 T) t)
    (ht₁ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      DifferentiableWithinAt ℝ (fun s => u₁ s x) (Icc 0 T) t)
    (hs₀ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u₀ t) x)
    (hs₁ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) (u₁ t) x)
    (hg₀ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun (G.metric t) (u₀ t) y) x)
    (hg₁ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% fun y : M => gradientFun (G.metric t) (u₁ t) y) x)
    (hP₀ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) u₀ t x ≤
        -2 * u₁ t x + c * u₀ t x * Real.sqrt (u₀ t x))
    (hP₁ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y)) u₁ t x ≤
        -2 * u₂ t x + 2 * c * Real.sqrt (u₀ t x) * u₁ t x)
    (hn₀ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      (G.metric t).inner x (gradientFun (G.metric t) (u₀ t) x)
        (gradientFun (G.metric t) (u₀ t) x) ≤ 4 * u₀ t x * u₁ t x)
    (hn₁ : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      (G.metric t).inner x (gradientFun (G.metric t) (u₁ t) x)
        (gradientFun (G.metric t) (u₁ t) x) ≤ 4 * u₁ t x * u₂ t x) :
    ∀ t ∈ Icc 0 T, ∀ x,
      t * cut.chi t x ^ 2 * u₁ t x ≤
        (1 + 2 * c * α) * (1 + c * α) * K ^ 2 +
          9 * ε * (1 + 2 * c * α) * K ^ 2 * t := by
  classical
  by_cases hT : 0 ≤ T
  · let β := 1 + 2 * c * α
    let A := β * K ^ 2
    let B := β * c * K ^ 3 + 9 * ε * β * K ^ 2
    let F := fun s y => β * (cut.chi s y * u₀ s y) + s * (cut.chi s y ^ 2 * u₁ s y)
    let w := fun s y => (A + B * s) - F s y
    have hβ : 0 ≤ β := by dsimp only [β]; positivity
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    have hB : 0 ≤ B := by dsimp only [B]; have := cut.err_nonneg; positivity
    have hFc : ContinuousOn (fun p : ℝ × M => F p.1 p.2) (Icc 0 T ×ˢ cut.support) :=
      ((continuousOn_const.mul (cut.joint_cont.mul hcont₀))).add
        (continuous_fst.continuousOn.mul ((cut.joint_cont.pow 2).mul hcont₁))
    have hinit : ∀ x, F 0 x ≤ A := by
      intro x
      have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
      by_cases hx : 0 < cut.chi 0 x
      · have hu := (mul_le_of_le_one_left (hu₀ 0 h0 x) (cut.range 0 h0 x).2).trans
          (huK 0 h0 x hx)
        simpa only [F, A, zero_mul, zero_add, add_zero] using mul_le_mul_of_nonneg_left hu hβ
      · have hz : cut.chi 0 x = 0 := le_antisymm (le_of_not_gt hx) (cut.range 0 h0 x).1
        simpa only [F, hz, zero_mul, mul_zero, add_zero] using hA
    have hout : ∀ t ∈ Icc 0 T, ∀ x, x ∉ cut.support → 0 ≤ w t x := by
      intro t ht x hx
      have hz := cut.support_zero t ht x hx
      simpa only [w, F, hz, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        mul_zero, add_zero, sub_zero] using add_nonneg hA (mul_nonneg hB ht.1)
    have hwc : ContinuousOn (fun p : ℝ × M => w p.1 p.2) (Icc 0 T ×ˢ cut.support) :=
      (continuous_const.add (continuous_const.mul continuous_fst)).continuousOn.sub hFc
    have hw0 : ∀ x, 0 ≤ w 0 x := by
      intro x
      simpa only [w, mul_zero, add_zero] using sub_nonneg.mpr (hinit x)
    have hsupp : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, w t x < 0 →
        ParabolicUpperSupportAt G T (fun _ y => (0 : TangentSpace I y)) w t x := by
      intro t ht htpos x hneg
      have hpos : 0 < F t x := by
        have := add_nonneg hA (mul_nonneg hB ht.1)
        dsimp only [w] at hneg
        linarith
      have hχ : 0 < cut.chi t x := by
        by_contra hχ
        have hz : cut.chi t x = 0 := le_antisymm (le_of_not_gt hχ) (cut.range t ht x).1
        have : F t x = 0 := by simp only [F, hz, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
        linarith
      let q := Classical.choice (cut.lowerSupport t ht htpos x hχ)
      let V := fun s y => β * (q.phi s y * u₀ s y) + s * (q.phi s y ^ 2 * u₁ s y)
      let z := fun s y => (A + B * s) - V s y
      have huniq := (uniqueDiffOn_Icc (htpos.trans_le ht.2)).uniqueDiffWithinAt ht
      have htK : t * K ≤ α := (mul_le_mul_of_nonneg_right ht.2 hK).trans hTK
      have hsm : 34 * ε * t ≤ 1 / 2 :=
        (mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) cut.err_nonneg)).trans hsmall
      have hdata := support_bernstein_data q u₀ u₁ u₂ c K α ht huniq hc hK hα cut.err_nonneg
        (cut.range t ht x) (hu₀ t ht x) (hu₁ t ht x) (hu₂ t ht x) (huK t ht x hχ) htK hsm
        (ht₀ t ht htpos x) (ht₁ t ht htpos x)
        (Eventually.of_forall (hs₀ t ht htpos)) (Eventually.of_forall (hs₁ t ht htpos))
        (hg₀ t ht htpos x) (hg₁ t ht htpos x) (hP₀ t ht htpos x) (hP₁ t ht htpos x)
        (hn₀ t ht htpos x) (hn₁ t ht htpos x)
      have heq : V t x = F t x := by simp only [V, F, q.eq_at]
      refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [z, w, heq]
      · filter_upwards [q.lower_nhds, self_mem_nhdsWithin] with p hp hpt
        have h0 := mul_le_mul_of_nonneg_right hp.2 (hu₀ p.1 hpt.1 p.2)
        have h1 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hp.1 hp.2 2) (hu₁ p.1 hpt.1 p.2)
        have hsum := add_le_add (mul_le_mul_of_nonneg_left h0 hβ)
          (mul_le_mul_of_nonneg_left h1 hpt.1.1)
        exact sub_le_sub_left hsum _
      · exact ((differentiableWithinAt_const A).add
          (differentiableWithinAt_id.const_mul B)).sub hdata.1
      · exact hdata.2.1.mono fun _ hy => mdifferentiableAt_const.sub hy
      · refine (hdata.2.2.1.smul_const_section (a := (-1 : ℝ))).congr_of_eventuallyEq ?_
        filter_upwards [hdata.2.1] with y hy
        apply congrArg (fun v => (⟨y, v⟩ : TotalSpace E (TangentSpace I : M → Type _)))
        change gradientFun (G.metric t) (fun y => (A + B * t) - V t y) y = _
        rw [gradientFun_sub (G.metric t) mdifferentiableAt_const hy, gradientFun_const]
        simp
      · have hP := parabolic_affine_sub_nhds T (fun _ y => (0 : TangentSpace I y))
          V A B t x huniq hdata.1 hdata.2.1 hdata.2.2.1
        change 0 ≤ parabolicOperatorWithDrift G T (fun _ y => (0 : TangentSpace I y))
          (fun s y => (A + B * s) - V s y) t x
        rw [hP]
        exact sub_nonneg.mpr hdata.2.2.2
    have hw := strict_barrier_compact_of_upperSupport G T (fun _ y => (0 : TangentSpace I y))
      w cut.support cut.support_compact hout hwc hw0 hsupp
    intro t ht x
    have hf : F t x ≤ A + B * t := sub_nonneg.mp (hw t ht x)
    have hfirst : 0 ≤ β * (cut.chi t x * u₀ t x) :=
      mul_nonneg hβ (mul_nonneg (cut.range t ht x).1 (hu₀ t ht x))
    have htK : t * K ≤ α := (mul_le_mul_of_nonneg_right ht.2 hK).trans hTK
    have hgap := mul_nonneg (mul_nonneg hβ hc) (mul_nonneg (sq_nonneg K) (sub_nonneg.mpr htK))
    dsimp only [F, A, B, β] at hf hfirst hgap
    nlinarith only [hf, hfirst, hgap]
  · intro t ht x
    exact False.elim (hT (ht.1.trans ht.2))

end DifferentialGeometry.Analysis.Parabolic
