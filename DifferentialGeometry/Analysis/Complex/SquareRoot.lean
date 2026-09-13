import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.ExtendFrom

open Set Filter Metric
open scoped Topology NNReal

theorem Complex.sq_sqrt (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem Complex.exists_tendsto_of_sq_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {x : E} {f : E → ℂ} {q : ℂ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hlim : Tendsto (fun y => f y ^ 2) (𝓝[s] x) (𝓝 q)) :
    ∃ a : ℂ, a ^ 2 = q ∧ Tendsto f (𝓝[s] x) (𝓝 a) := by
  by_cases hq : q = 0
  · refine ⟨0, by simp [hq], ?_⟩
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hlim.norm
    simpa only [hq, norm_zero, norm_pow, Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hh
  let a := Complex.sqrt q
  have ha : a ^ 2 = q := Complex.sq_sqrt q
  have hratio : Tendsto (fun y => f y ^ 2 / q) (𝓝[s] x) (𝓝 1) := by
    simpa only [div_self hq] using hlim.div_const q
  have hpos : ∀ᶠ y in 𝓝[s] x, 0 < (f y ^ 2 / q).re :=
    (Complex.continuous_re.continuousAt.tendsto.comp hratio).eventually
      (lt_mem_nhds (by simp : (0 : ℝ) < (1 : ℂ).re))
  obtain ⟨δ, hδ, hδpos⟩ := Metric.mem_nhdsWithin_iff.mp hpos
  let T := ball x δ ∩ s
  have hT : IsPreconnected T := ((convex_ball x δ).inter hs).isPreconnected
  have hTmem : T ∈ 𝓝[s] x := inter_mem
    (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x hδ)) self_mem_nhdsWithin
  let g (y : E) := a * Complex.sqrt (f y ^ 2 / q)
  have hgsq (y : E) : g y ^ 2 = f y ^ 2 := by
    dsimp only [g]
    rw [mul_pow, ha, Complex.sq_sqrt]
    field_simp [hq]
  have hg : ContinuousOn g T := by
    intro y hy
    have hh := ((hf.mono inter_subset_right) y hy).pow 2
    exact continuousWithinAt_const.mul
      ((Complex.continuousAt_sqrt (.inl (hδpos hy).le)).comp_continuousWithinAt (hh.div_const q))
  have hgn {y : E} (hy : y ∈ T) : g y ≠ 0 := by
    intro hz
    have hh := hgsq y
    rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hh
    have hn : 0 < (f y ^ 2 / q).re := hδpos hy
    rw [← hh, zero_div, Complex.zero_re] at hn
    exact lt_irrefl 0 hn
  have hgLim : Tendsto g (𝓝[s] x) (𝓝 a) := by
    have hh := (tendsto_const_nhds (x := a)).mul
      ((Complex.continuousAt_sqrt (.inl (by simp : (0 : ℝ) ≤ (1 : ℂ).re))).tendsto.comp hratio)
    simpa only [Complex.sqrt_one, mul_one, Function.comp_def, g] using hh
  rcases hT.eq_or_eq_neg_of_sq_eq (hf.mono inter_subset_right) hg
    (fun y _ => (hgsq y).symm) hgn with hp | hn
  · refine ⟨a, ha, ?_⟩
    apply (tendsto_congr' (show f =ᶠ[𝓝[s] x] g from ?_)).mpr hgLim
    filter_upwards [hTmem] with y hy using hp hy
  · refine ⟨-a, by simpa only [neg_sq] using ha, ?_⟩
    apply (tendsto_congr' (show f =ᶠ[𝓝[s] x] -g from ?_)).mpr hgLim.neg
    filter_upwards [hTmem] with y hy using hn hy

theorem Complex.exists_continuousOn_extension_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f q : E → ℂ} (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hq : ContinuousOn q (closure s)) (hsq : EqOn (fun y => f y ^ 2) q s) :
    ∃ g : E → ℂ, ContinuousOn g (closure s) ∧ EqOn g f s ∧
      EqOn (fun y => g y ^ 2) q (closure s) := by
  have hlim (x : E) (hx : x ∈ closure s) :
      ∃ a : ℂ, a ^ 2 = q x ∧ Tendsto f (𝓝[s] x) (𝓝 a) := by
    apply Complex.exists_tendsto_of_sq_tendsto hs hf
    have hh : Tendsto q (𝓝[s] x) (𝓝 (q x)) := (hq x hx).mono subset_closure
    apply (tendsto_congr' (show (fun y => f y ^ 2) =ᶠ[𝓝[s] x] q from ?_)).mpr hh
    filter_upwards [self_mem_nhdsWithin] with y hy using hsq hy
  refine ⟨extendFrom s f, continuousOn_extendFrom Subset.rfl ?_, extendFrom_extends hf, ?_⟩
  · intro x hx
    obtain ⟨a, _, ha⟩ := hlim x hx
    exact ⟨a, ha⟩
  · intro x hx
    obtain ⟨a, ha, ht⟩ := hlim x hx
    change extendFrom s f x ^ 2 = q x
    rw [extendFrom_eq hx ht]
    exact ha

private theorem sq_norm_sub_le_norm_sq_sub {a b : ℂ}
    (h : 0 ≤ a.re * b.re + a.im * b.im) : ‖a - b‖ ^ 2 ≤ ‖a ^ 2 - b ^ 2‖ := by
  have hab : ‖a - b‖ ≤ ‖a + b‖ := by
    have hs : ‖a - b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im, Complex.add_re, Complex.add_im]
      nlinarith
    nlinarith [norm_nonneg (a - b), norm_nonneg (a + b)]
  calc
    ‖a - b‖ ^ 2 ≤ ‖a - b‖ * ‖a + b‖ := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hab (norm_nonneg (a - b))
    _ = ‖a ^ 2 - b ^ 2‖ := by rw [← norm_mul]; congr 1; ring

private theorem sq_norm_le_norm_sq_sub_of_orthogonal {a b : ℂ}
    (h : a.re * b.re + a.im * b.im = 0) : ‖b‖ ^ 2 ≤ ‖a ^ 2 - b ^ 2‖ := by
  have hn : ‖b‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    nlinarith [sq_nonneg a.re, sq_nonneg a.im]
  exact hn.trans (sq_norm_sub_le_norm_sq_sub h.ge)

private theorem sq_norm_sub_le_of_sq_sub_le
    {X : Type*} [TopologicalSpace X] {s : Set X} (hs : IsPreconnected s)
    {f : X → ℂ} (hf : ContinuousOn f s) {x y : X} (hx : x ∈ s) (hy : y ∈ s)
    {M : ℝ} (hM : ∀ z ∈ s, ‖f z ^ 2 - f x ^ 2‖ ≤ M) :
    ‖f y - f x‖ ^ 2 ≤ 6 * M := by
  have hM0 : 0 ≤ M := by simpa only [sub_self, norm_zero] using hM x hx
  by_cases hpos : 0 ≤ (f y).re * (f x).re + (f y).im * (f x).im
  · exact (sq_norm_sub_le_norm_sq_sub hpos).trans ((hM y hy).trans (by linarith))
  have hcont : ContinuousOn (fun z => (f z).re * (f x).re + (f z).im * (f x).im) s :=
    ((Complex.continuous_re.comp_continuousOn hf).mul_const _).add
      ((Complex.continuous_im.comp_continuousOn hf).mul_const _)
  have hzero : (0 : ℝ) ∈ Icc
      ((f y).re * (f x).re + (f y).im * (f x).im)
      ((f x).re * (f x).re + (f x).im * (f x).im) := by
    constructor
    · exact (lt_of_not_ge hpos).le
    · nlinarith [sq_nonneg (f x).re, sq_nonneg (f x).im]
  obtain ⟨z, hz, horth⟩ := hs.intermediate_value hy hx hcont hzero
  have hxn : ‖f x‖ ^ 2 ≤ M := (sq_norm_le_norm_sq_sub_of_orthogonal horth).trans (hM z hz)
  have hyn : ‖f y‖ ^ 2 ≤ 2 * M := by
    calc
      ‖f y‖ ^ 2 = ‖f y ^ 2‖ := (norm_pow _ _).symm
      _ ≤ ‖f y ^ 2 - f x ^ 2‖ + ‖f x ^ 2‖ := norm_le_norm_sub_add _ _
      _ ≤ M + M := add_le_add (hM y hy) (by simpa only [norm_pow] using hxn)
      _ = 2 * M := by ring
  have ht := norm_sub_le (f y) (f x)
  nlinarith [sq_nonneg (‖f y‖ - ‖f x‖), norm_nonneg (f y - f x), norm_nonneg (f y), norm_nonneg (f x)]

theorem Complex.holderOnWith_of_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : Convex ℝ s) {f : E → ℂ} (hf : ContinuousOn f s)
    {C α : ℝ≥0} (hq : HolderOnWith C α (fun z => f z ^ 2) s) :
    HolderOnWith (NNReal.sqrt (6 * C)) (α / 2) f s := by
  intro x hx y hy
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ (α / 2).coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
  simp only [coe_nndist, NNReal.coe_mul, NNReal.coe_rpow, Real.coe_sqrt,
    NNReal.coe_div, NNReal.coe_ofNat]
  have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
  have hbound : ‖f y - f x‖ ^ 2 ≤ 6 * ((C : ℝ) * dist x y ^ (α : ℝ)) := by
    apply sq_norm_sub_le_of_sq_sub_le (convex_segment x y).isPreconnected
      (hf.mono hseg) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
    intro z hz
    have hd : dist z x ≤ dist x y := segment_subset_closedBall_left x y hz
    simpa only [dist_eq_norm] using hq.dist_le_of_le (hseg hz) hx hd
  have hp : (dist x y ^ ((α : ℝ) / 2)) ^ 2 = dist x y ^ (α : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul dist_nonneg]
    congr 1
    norm_num
  have hC : 0 ≤ 6 * (C : ℝ) := by positivity
  have hh : (Real.sqrt (6 * (C : ℝ)) * dist x y ^ ((α : ℝ) / 2)) ^ 2 =
      6 * ((C : ℝ) * dist x y ^ (α : ℝ)) := by
    rw [mul_pow, Real.sq_sqrt hC, hp]
    ring
  have hnon : 0 ≤ Real.sqrt (6 * (C : ℝ)) * dist x y ^ ((α : ℝ) / 2) := by positivity
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (f y - f x)]


theorem Complex.exists_holderOnWith_extension_of_sq_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f q : E → ℂ} {C α : ℝ≥0} (hs : Convex ℝ s)
    (hf : ContinuousOn f s) (hα : 0 < α) (hq : HolderOnWith C α q (closure s))
    (hsq : EqOn (fun y => f y ^ 2) q s) :
    ∃ g : E → ℂ, HolderOnWith (NNReal.sqrt (6 * C)) (α / 2) g (closure s) ∧
      EqOn g f s ∧ EqOn (fun y => g y ^ 2) q (closure s) := by
  obtain ⟨g, hg, hgf, hgq⟩ :=
    Complex.exists_continuousOn_extension_of_sq_eq hs hf (hq.continuousOn hα) hsq
  have hpow : HolderOnWith C α (fun y => g y ^ 2) (closure s) := by
    intro x hx y hy
    change edist (g x ^ 2) (g y ^ 2) ≤ _
    rw [show g x ^ 2 = q x from hgq hx, show g y ^ 2 = q y from hgq hy]
    exact hq.edist_le hx hy
  exact ⟨g, Complex.holderOnWith_of_sq hs.closure hg hpow, hgf, hgq⟩
