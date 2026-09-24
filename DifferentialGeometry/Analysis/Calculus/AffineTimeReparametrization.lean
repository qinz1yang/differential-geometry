import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Set
open Filter
open scoped Topology

namespace Real

theorem abs_rescale_time_sub_le {q Q s τ v θ : ℝ} (hv : |v| ≤ θ) :
    |q * (s + v / Q - τ) - v| ≤ |q / Q - 1| * θ + |q| * |s - τ| := by
  have heq : q * (s + v / Q - τ) - v = (q / Q - 1) * v + q * (s - τ) := by
    ring
  rw [heq]
  calc
    |(q / Q - 1) * v + q * (s - τ)| ≤ |(q / Q - 1) * v| + |q * (s - τ)| :=
      abs_add_le _ _
    _ = |q / Q - 1| * |v| + |q| * |s - τ| := by rw [abs_mul, abs_mul]
    _ ≤ |q / Q - 1| * θ + |q| * |s - τ| :=
      add_le_add (mul_le_mul_of_nonneg_left hv (abs_nonneg _)) le_rfl

theorem abs_rescale_time_sub_le_of_nonneg {q Q s τ v θ : ℝ}
    (hq : 0 ≤ q) (hv : |v| ≤ θ) :
    |q * (s + v / Q - τ) - v| ≤ |q / Q - 1| * θ + q * |s - τ| := by
  simpa only [abs_of_nonneg hq] using abs_rescale_time_sub_le (q := q) (Q := Q)
    (s := s) (τ := τ) hv

theorem tendsto_rescale_time_error_bound {ι : Type*} {l : Filter ι}
    {q τ : ι → ℝ} {Q s : ℝ} (hq : Tendsto q l (𝓝 Q))
    (hτ : Tendsto τ l (𝓝 s)) (hQ : Q ≠ 0) (θ : ℝ) :
    Tendsto (fun i => |q i / Q - 1| * θ + |q i| * |s - τ i|) l (𝓝 0) := by
  simpa only [div_self hQ, sub_self, abs_zero, zero_mul, mul_zero, add_zero] using
    (((hq.div_const Q).sub_const 1).abs.mul_const θ).add
      (hq.abs.mul (((tendsto_const_nhds (x := s)).sub hτ).abs))

theorem tendstoUniformlyOn_rescale_time {ι : Type*} {l : Filter ι}
    {q τ : ι → ℝ} {Q s : ℝ} (hq : Tendsto q l (𝓝 Q))
    (hτ : Tendsto τ l (𝓝 s)) (hQ : Q ≠ 0) (θ : ℝ) :
    TendstoUniformlyOn (fun i v => q i * (s + v / Q - τ i))
      (fun v => v) l (Set.Icc (-θ) θ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_rescale_time_error_bound hq hτ hQ θ).eventually_lt_const hε]
    with i hi v hv
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_rescale_time_sub_le (abs_le.mpr hv)).trans_lt hi

theorem eventually_mapsTo_rescale_time_Icc {ι : Type*} {l : Filter ι}
    {q τ : ι → ℝ} {Q s θ η : ℝ} (hq : Tendsto q l (𝓝 Q))
    (hτ : Tendsto τ l (𝓝 s)) (hQ : Q ≠ 0) (hθ : θ < 1) (hη : 0 < η) :
    ∀ᶠ i in l, Set.MapsTo (fun v => q i * (s + v / Q - τ i))
      (Set.Icc (-θ) (-η)) (Set.Ioo (-1) 0) := by
  have hbound := tendsto_rescale_time_error_bound hq hτ hQ θ
  filter_upwards [hbound.eventually_lt_const (sub_pos.mpr hθ),
    hbound.eventually_lt_const hη] with i hiθ hiη v hv
  have hvabs : |v| ≤ θ := abs_le.mpr ⟨hv.1, by linarith [hv.1, hv.2]⟩
  have he := abs_le.mp (abs_rescale_time_sub_le (q := q i) (Q := Q)
    (s := s) (τ := τ i) hvabs)
  constructor <;> linarith [hv.1, hv.2, he.1, he.2]

theorem hasDerivAt_rescale_time (q Q s τ v : ℝ) :
    HasDerivAt (fun v => q * (s + v / Q - τ)) (q / Q) v := by
  have hd : HasDerivAt (fun v : ℝ => s + v / Q - τ) (1 / Q) v := by
    convert ((hasDerivAt_id v).div_const Q).const_add s |>.sub_const τ using 1
    all_goals rfl
  simpa only [mul_one_div] using hd.const_mul q

theorem deriv_rescale_time (q Q s τ v : ℝ) :
    deriv (fun v => q * (s + v / Q - τ)) v = q / Q :=
  (hasDerivAt_rescale_time q Q s τ v).deriv

theorem tendstoUniformly_deriv_rescale_time {ι : Type*} {l : Filter ι}
    {q : ι → ℝ} {Q : ℝ} (hq : Tendsto q l (𝓝 Q)) (hQ : Q ≠ 0)
    (τ : ι → ℝ) (s : ℝ) :
    TendstoUniformly (fun i => deriv (fun v => q i * (s + v / Q - τ i)))
      (fun _ => 1) l := by
  simp_rw [funext (deriv_rescale_time _ _ _ _)]
  have hlim : Tendsto (fun i => q i / Q) l (𝓝 1) := by
    simpa only [div_self hQ] using hq.div_const Q
  exact hlim.tendstoUniformly_const

theorem iteratedDeriv_rescale_time (q Q s τ v : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    iteratedDeriv k (fun v => q * (s + v / Q - τ)) v = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [show 2 + n = (n + 1) + 1 by omega, iteratedDeriv_succ']
  simp_rw [funext (deriv_rescale_time _ _ _ _)]
  simp [iteratedDeriv_const]



def clippedAffineTime (s τ q Q v : ℝ) : ℝ :=
  τ + max (-1) (min (q * (s + v / Q - τ)) 0) / q

private theorem abs_clip_sub_le {u v : ℝ} (hv : v ∈ Icc (-1 : ℝ) 0) :
    |max (-1) (min u 0) - u| ≤ |u - v| := by
  by_cases hl : u ≤ -1
  · rw [min_eq_left (by linarith), max_eq_left hl,
      abs_of_nonneg (by linarith : 0 ≤ -1 - u)]
    have h := neg_le_abs (u - v)
    linarith [hv.1]
  · by_cases hu : 0 ≤ u
    · rw [min_eq_right hu, max_eq_right (by norm_num), zero_sub, abs_neg,
        abs_of_nonneg hu]
      have h := le_abs_self (u - v)
      linarith [hv.2]
    · rw [min_eq_left (le_of_not_ge hu), max_eq_right (le_of_not_ge hl),
        sub_self, abs_zero]
      exact abs_nonneg _

theorem clippedAffineTime_mem_source {s τ q Q v : ℝ} (hq : 0 < q) :
    clippedAffineTime s τ q Q v ∈ Icc (τ - q⁻¹) τ := by
  have hlo : -1 ≤ max (-1 : ℝ) (min (q * (s + v / Q - τ)) 0) := le_max_left _ _
  have hhi : max (-1 : ℝ) (min (q * (s + v / Q - τ)) 0) ≤ 0 :=
    max_le (by norm_num) (min_le_right _ _)
  have hl := div_le_div_of_nonneg_right hlo hq.le
  have hh := div_nonpos_of_nonpos_of_nonneg hhi hq.le
  simp only [neg_div, one_div] at hl
  constructor <;> dsimp [clippedAffineTime] <;> linarith

theorem abs_clippedAffineTime_sub_le {s τ q Q v : ℝ} (hq : 0 < q)
    (hv : v ∈ Icc (-1 : ℝ) 0) :
    |clippedAffineTime s τ q Q v - (s + v / Q)| ≤
      (|q / Q - 1| + q * |s - τ|) / q := by
  let u := q * (s + v / Q - τ)
  have he : clippedAffineTime s τ q Q v - (s + v / Q) =
      (max (-1) (min u 0) - u) / q := by
    dsimp [clippedAffineTime, u]
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hq]
  have hbound := abs_rescale_time_sub_le_of_nonneg (q := q) (Q := Q)
    (s := s) (τ := τ) hq.le (show |v| ≤ 1 from abs_le.mpr ⟨hv.1, by linarith [hv.2]⟩)
  rw [mul_one] at hbound
  exact div_le_div_of_nonneg_right ((abs_clip_sub_le hv).trans hbound) hq.le

theorem tendstoUniformlyOn_clippedAffineTime {ι : Type*} {l : Filter ι}
    {q τ : ι → ℝ} {Q s : ℝ} (hq : Tendsto q l (𝓝 Q))
    (hτ : Tendsto τ l (𝓝 s)) (hQ : 0 < Q) (hqpos : ∀ i, 0 < q i) :
    TendstoUniformlyOn (fun i v => clippedAffineTime s (τ i) (q i) Q v)
      (fun v => s + v / Q) l (Icc (-1 : ℝ) 0) := by
  have he : Tendsto (fun i => (|q i / Q - 1| + q i * |s - τ i|) / q i)
      l (𝓝 0) := by
    have h0 := (tendsto_rescale_time_error_bound hq hτ hQ.ne' 1).div hq hQ.ne'
    have hfun : (fun i => (|q i / Q - 1| * 1 + |q i| * |s - τ i|) / q i) =
        (fun i => (|q i / Q - 1| + q i * |s - τ i|) / q i) := by
      funext i
      simp only [mul_one, abs_of_pos (hqpos i)]
    change Tendsto (fun i => (|q i / Q - 1| * 1 + |q i| * |s - τ i|) / q i)
      l (𝓝 (0 / Q)) at h0
    rw [hfun, zero_div] at h0
    exact h0
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [he.eventually_lt_const hε] with i hi v hv
  rw [Real.dist_eq, abs_sub_comm]
  exact (abs_clippedAffineTime_sub_le (hqpos i) hv).trans_lt hi


theorem tendstoUniformlyOn_comp_clippedAffineTime
    {ι X Y : Type*} {l : Filter ι} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {q τ : ι → ℝ} {Q s a b : ℝ} (hq : Tendsto q l (𝓝 Q))
    (hτ : Tendsto τ l (𝓝 s)) (hQ : 0 < Q) (hqpos : ∀ i, 0 < q i)
    (hsource : ∀ᶠ i in l, Icc (τ i - (q i)⁻¹) (τ i) ⊆ Icc a b)
    (htarget : MapsTo (fun v => s + v / Q) (Icc (-1 : ℝ) 0) (Icc a b))
    {K : Set X} (hK : IsCompact K) {F : ℝ × X → Y}
    (hF : ContinuousOn F (Icc a b ×ˢ K)) :
    TendstoUniformlyOn (fun i (p : ℝ × X) =>
      F (clippedAffineTime s (τ i) (q i) Q p.1, p.2))
      (fun p => F (s + p.1 / Q, p.2)) l (Icc (-1 : ℝ) 0 ×ˢ K) := by
  have hUC := (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hF
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  have htimes := Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_clippedAffineTime hq hτ hQ hqpos) δ hδ
  filter_upwards [hsource, htimes] with i hi ht p hp
  apply hclose (s + p.1 / Q, p.2) ⟨htarget hp.1, hp.2⟩
    (clippedAffineTime s (τ i) (q i) Q p.1, p.2)
    ⟨hi (clippedAffineTime_mem_source (hqpos i)), hp.2⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using ht p.1 hp.1


end Real
