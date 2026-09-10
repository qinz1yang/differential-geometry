import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.DiniComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.ScalarThreshold
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section

open Set Filter
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

structure ScalarComparisonHypotheses (c H : ℝ) (E : Set ℝ) (W : ℝ → ℝ) : Prop where
  c_pos : 0 < c
  horizon_pos : 0 < H
  finite_events : E.Finite
  events_subset : E ⊆ Ioc 0 H
  nonneg : ∀ t ∈ Icc 0 H, 0 ≤ W t
  continuous : ∀ t ∈ Icc 0 H, t ∉ E → ContinuousWithinAt W (Icc 0 H) t
  right_continuous : ∀ t ∈ Ico 0 H, ContinuousWithinAt W (Ici t) t
  incoming_jump : ∀ e ∈ E,
    (W e : EReal) ≤ liminf (fun s => (W s : EReal)) (𝓝[<] e)
  dini : ∀ t ∈ Ico 0 H, t ∉ E →
    UpperRightDiniLE W t (-2 * Real.pi + 3 * W t / (4 * (t + c)))

def scalarWeightedWidth (c : ℝ) (W : ℝ → ℝ) (t : ℝ) : ℝ :=
  (t + c) ^ (-(3 / 4 : ℝ)) * W t + 8 * Real.pi * (t + c) ^ (1 / 4 : ℝ)

private def weight (c t : ℝ) : ℝ := (t + c) ^ (-(3 / 4 : ℝ))

private def primitive (c t : ℝ) : ℝ := 8 * Real.pi * (t + c) ^ (1 / 4 : ℝ)

private theorem weight_pos {c t : ℝ} (ht : 0 < t + c) : 0 < weight c t :=
  Real.rpow_pos_of_pos ht _

private theorem hasDerivAt_weight {c t : ℝ} (ht : 0 < t + c) :
    HasDerivAt (weight c) (-(3 * weight c t) / (4 * (t + c))) t := by
  apply (((hasDerivAt_id t).add_const c).rpow_const
    (p := -(3 / 4 : ℝ)) (Or.inl ht.ne')).congr_deriv
  dsimp [weight]
  rw [Real.rpow_sub_one ht.ne']
  field_simp

private theorem hasDerivAt_primitive {c t : ℝ} (ht : 0 < t + c) :
    HasDerivAt (primitive c) (2 * Real.pi * weight c t) t := by
  apply ((((hasDerivAt_id t).add_const c).rpow_const
    (p := (1 / 4 : ℝ)) (Or.inl ht.ne')).const_mul (8 * Real.pi)).congr_deriv
  dsimp [weight]
  norm_num
  ring

private theorem upperRightDiniLE_mul_add {p W q : ℝ → ℝ} {x p' q' L : ℝ}
    (hp : HasDerivAt p p' x) (hq : HasDerivAt q q' x)
    (hW : ContinuousWithinAt W (Ioi x) x) (hp_pos : 0 < p x)
    (hDini : UpperRightDiniLE W x L) :
    UpperRightDiniLE (fun s => p s * W s + q s) x (p x * L + p' * W x + q') := by
  intro ε hε
  have hp_slope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp
    (hp.hasDerivWithinAt (s := Ioi x))
  have hq_slope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).mp
    (hq.hasDerivWithinAt (s := Ioi x))
  have haux : ∀ᶠ y in 𝓝[>] x,
      slope p x y * W y + slope q x y < p' * W x + q' + ε / 2 :=
    ((hp_slope.mul hW).add hq_slope).eventually_lt_const (by linarith)
  have hmain := hDini (ε / (2 * p x)) (div_pos hε (by positivity))
  filter_upwards [haux, hmain] with y hyaux hymain
  have hmul := mul_le_mul_of_nonneg_left hymain hp_pos.le
  have hcancel : p x * (L + ε / (2 * p x)) = p x * L + ε / 2 := by
    field_simp [hp_pos.ne']
  rw [hcancel] at hmul
  have heq : slope (fun s => p s * W s + q s) x y =
      p x * slope W x y + slope p x y * W y + slope q x y := by
    simp only [slope, vsub_eq_sub, smul_eq_mul]
    ring
  rw [heq]
  linarith

private theorem weighted_dini {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) {t : ℝ} (ht : t ∈ Ico 0 H)
    (htE : t ∉ E) : UpperRightDiniLE (scalarWeightedWidth c W) t 0 := by
  have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht.1 h.c_pos
  have hd := upperRightDiniLE_mul_add (hasDerivAt_weight htc)
    (hasDerivAt_primitive htc)
    ((h.right_continuous t ht).mono Ioi_subset_Ici_self) (weight_pos htc) (h.dini t ht htE)
  have hzero : weight c t * (-2 * Real.pi + 3 * W t / (4 * (t + c))) +
      (-(3 * weight c t) / (4 * (t + c))) * W t +
      2 * Real.pi * weight c t = 0 := by ring
  rw [hzero] at hd
  exact hd

private theorem weighted_incoming_jump {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) {e : ℝ} (he : e ∈ E) :
    (scalarWeightedWidth c W e : EReal) ≤
      liminf (fun s => (scalarWeightedWidth c W s : EReal)) (𝓝[<] e) := by
  have heH := h.events_subset he
  have hec : 0 < e + c := add_pos heH.1 h.c_pos
  have hp : Tendsto (fun s => (weight c s : EReal)) (𝓝[<] e)
      (𝓝 (weight c e : EReal)) := EReal.tendsto_coe.mpr
    ((hasDerivAt_weight hec).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hq : Tendsto (fun s => (primitive c s : EReal)) (𝓝[<] e)
      (𝓝 (primitive c e : EReal)) := EReal.tendsto_coe.mpr
    ((hasDerivAt_primitive hec).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hp0 : ∀ᶠ s in 𝓝[<] e, (0 : EReal) ≤ (weight c s : EReal) := by
    filter_upwards [Ioo_mem_nhdsLT heH.1] with s hs
    exact_mod_cast (weight_pos (add_pos hs.1 h.c_pos)).le
  have hW0 : ∀ᶠ s in 𝓝[<] e, (0 : EReal) ≤ (W s : EReal) := by
    filter_upwards [Ioo_mem_nhdsLT heH.1] with s hs
    exact_mod_cast h.nonneg s ⟨hs.1.le, hs.2.le.trans heH.2⟩
  have hpW := EReal.le_liminf_mul hp0 hW0
  rw [hp.liminf_eq] at hpW
  have hsum := EReal.le_liminf_add
    (u := fun s => (weight c s : EReal) * (W s : EReal))
    (v := fun s => (primitive c s : EReal)) (f := 𝓝[<] e)
  rw [hq.liminf_eq] at hsum
  have hp_nonneg : (0 : EReal) ≤ (weight c e : EReal) := by
    exact_mod_cast (weight_pos hec).le
  calc
    (scalarWeightedWidth c W e : EReal) =
        (weight c e : EReal) * (W e : EReal) + (primitive c e : EReal) := by
      simp only [scalarWeightedWidth, weight, primitive, EReal.coe_add, EReal.coe_mul]
    _ ≤ (weight c e : EReal) * liminf (fun s => (W s : EReal)) (𝓝[<] e) +
        (primitive c e : EReal) :=
      add_le_add_left (mul_le_mul_of_nonneg_left (h.incoming_jump e he) hp_nonneg) _
    _ ≤ liminf (fun s => (weight c s : EReal) * (W s : EReal)) (𝓝[<] e) +
        (primitive c e : EReal) := by
      simpa only [Pi.mul_def] using add_le_add_left hpW (primitive c e : EReal)
    _ ≤ liminf (fun s => (scalarWeightedWidth c W s : EReal)) (𝓝[<] e) := by
      simpa only [scalarWeightedWidth, weight, primitive, Pi.add_def,
        EReal.coe_add, EReal.coe_mul] using hsum

theorem scalarWeightedWidth_antitoneOn {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) :
    AntitoneOn (scalarWeightedWidth c W) (Icc 0 H) := by
  apply antitoneOn_of_finite_jumps_upperRightDiniLE h.finite_events
  · intro t ht htE
    have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht.1 h.c_pos
    exact ((hasDerivAt_weight htc).continuousAt.continuousWithinAt.mul
      (h.continuous t ht htE)).add
        (hasDerivAt_primitive htc).continuousAt.continuousWithinAt
  · intro t ht
    have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht.1 h.c_pos
    exact ((hasDerivAt_weight htc).continuousAt.continuousWithinAt.mul
      (h.right_continuous t ht)).add
        (hasDerivAt_primitive htc).continuousAt.continuousWithinAt
  · exact fun t ht htE => weighted_dini h ht htE
  · exact fun e he => weighted_incoming_jump h he

theorem scalarComparison_integrated_bound {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) {t : ℝ} (ht : t ∈ Icc 0 H) :
    W t / (t + c) ^ (3 / 4 : ℝ) ≤ W 0 / c ^ (3 / 4 : ℝ) -
      8 * Real.pi * ((t + c) ^ (1 / 4 : ℝ) - c ^ (1 / 4 : ℝ)) := by
  have hm := scalarWeightedWidth_antitoneOn h ⟨le_rfl, h.horizon_pos.le⟩ ht ht.1
  have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht.1 h.c_pos
  dsimp [scalarWeightedWidth] at hm
  rw [zero_add, Real.rpow_neg htc.le, Real.rpow_neg h.c_pos.le] at hm
  simp only [div_eq_mul_inv]
  nlinarith [hm]

theorem scalarComparison_incoming_limit {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) {e : ℝ} (he : e ∈ E) :
    ∃ L : ℝ, Tendsto W (𝓝[<] e) (𝓝 L) ∧ W e ≤ L := by
  have heH := h.events_subset he
  have hec : 0 < e + c := add_pos heH.1 h.c_pos
  have hb : BddBelow (scalarWeightedWidth c W '' Icc 0 H) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have htc : 0 < t + c := add_pos_of_nonneg_of_pos ht.1 h.c_pos
    exact add_nonneg (mul_nonneg (Real.rpow_nonneg htc.le _) (h.nonneg t ht))
      (mul_nonneg (by positivity) (Real.rpow_nonneg htc.le _))
  obtain ⟨L, hL, heL⟩ := incoming_limit_of_antitoneOn
    (scalarWeightedWidth_antitoneOn h) hb heH
  refine ⟨(L - primitive c e) / weight c e, ?_, ?_⟩
  · have hp : Tendsto (weight c) (𝓝[<] e) (𝓝 (weight c e)) :=
      (hasDerivAt_weight hec).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hq : Tendsto (primitive c) (𝓝[<] e) (𝓝 (primitive c e)) :=
      (hasDerivAt_primitive hec).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hquot := (hL.sub hq).div hp (weight_pos hec).ne'
    apply hquot.congr'
    filter_upwards [Ioo_mem_nhdsLT heH.1] with s hs
    have hp_ne := (weight_pos (add_pos hs.1 h.c_pos)).ne'
    change (weight c s * W s + primitive c s - primitive c s) / weight c s = W s
    field_simp [hp_ne]
    ring
  · apply (le_div_iff₀ (weight_pos hec)).mpr
    change weight c e * W e + primitive c e ≤ L at heL
    nlinarith

theorem scalarComparison_horizon_le_threshold {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W) :
    H ≤ extinctionThreshold c (W 0) := by
  by_contra hnot
  have hH : extinctionThreshold c (W 0) < H := lt_of_not_ge hnot
  have hnegative := (extinctionThreshold_lt_iff h.c_pos
    (h.nonneg 0 ⟨le_rfl, h.horizon_pos.le⟩) h.horizon_pos.le).mp hH
  have hbound := scalarComparison_integrated_bound h
    (show H ∈ Icc 0 H from ⟨h.horizon_pos.le, le_rfl⟩)
  have hn : 0 ≤ W H / (H + c) ^ (3 / 4 : ℝ) :=
    div_nonneg (h.nonneg H ⟨h.horizon_pos.le, le_rfl⟩)
      (Real.rpow_nonneg (add_pos h.horizon_pos h.c_pos).le _)
  linarith

theorem scalarComparison_false_of_threshold_lt {c H : ℝ} {E : Set ℝ} {W : ℝ → ℝ}
    (h : ScalarComparisonHypotheses c H E W)
    (hH : extinctionThreshold c (W 0) < H) : False :=
  (not_lt_of_ge (scalarComparison_horizon_le_threshold h)) hH

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
