import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.ExtendFrom

open Set Filter Metric
open scoped Topology

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
