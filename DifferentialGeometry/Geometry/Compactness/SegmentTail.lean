import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.Geometry

variable {M : ℕ → Type*} [∀ i, PseudoMetricSpace (M i)]

private theorem rescaled_segment_tail_mem_Icc
    {L a ell s : ℝ} (hell : 0 < ell) (ha : a ∈ Icc 0 L) (hs : s ∈ Icc 0 ell) :
    a + (L - a) * s / ell ∈ Icc 0 L := by
  have hnonneg : 0 ≤ (L - a) * s / ell := by
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr ha.2) hs.1) hell.le
  refine ⟨by linarith [ha.1], ?_⟩
  have hupper : (L - a) * s / ell ≤ L - a := by
    apply (div_le_iff₀ hell).mpr
    nlinarith [ha.2, hs.2]
  linarith

theorem rescaled_segment_tail_dist
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (i : ℕ) {s t : ℝ} (hs : s ∈ Icc 0 ell) (ht : t ∈ Icc 0 ell) :
    dist (gamma i (a i + (L i - a i) * s / ell))
      (gamma i (a i + (L i - a i) * t / ell)) = (L i - a i) / ell * |s - t| := by
  rw [hsegment i _ (rescaled_segment_tail_mem_Icc hell (ha i) hs)
    _ (rescaled_segment_tail_mem_Icc hell (ha i) ht)]
  have heq : a i + (L i - a i) * s / ell - (a i + (L i - a i) * t / ell) =
      (L i - a i) / ell * (s - t) := by ring
  rw [heq, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr (ha i).2) hell.le)]

theorem continuousOn_rescaled_segment_tail
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (i : ℕ) :
    ContinuousOn (fun s => gamma i (a i + (L i - a i) * s / ell)) (Icc 0 ell) := by
  have hnonneg : 0 ≤ (L i - a i) / ell :=
    div_nonneg (sub_nonneg.mpr (ha i).2) hell.le
  have hLip : LipschitzOnWith (Real.toNNReal ((L i - a i) / ell))
      (fun s => gamma i (a i + (L i - a i) * s / ell)) (Icc 0 ell) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [rescaled_segment_tail_dist gamma L a hell ha hsegment i hs ht,
      Real.coe_toNNReal _ hnonneg, Real.dist_eq]
  exact hLip.continuousOn

theorem tendsto_rescaled_segment_tail_dist
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (htail : Tendsto (fun i => L i - a i) atTop (𝓝 ell))
    {s t : ℝ} (hs : s ∈ Icc 0 ell) (ht : t ∈ Icc 0 ell) :
    Tendsto (fun i => dist (gamma i (a i + (L i - a i) * s / ell))
      (gamma i (a i + (L i - a i) * t / ell))) atTop (𝓝 |s - t|) := by
  have hlim := (htail.div_const ell).mul_const |s - t|
  simpa only [rescaled_segment_tail_dist gamma L a hell ha hsegment _ hs ht,
    div_self hell.ne', one_mul] using hlim

theorem tendsto_rescaled_segment_tail_endpoint_dist
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (htail : Tendsto (fun i => L i - a i) atTop (𝓝 ell))
    {s : ℝ} (hs : s ∈ Icc 0 ell) :
    Tendsto (fun i => dist (gamma i (a i + (L i - a i) * s / ell))
      (gamma i (L i))) atTop (𝓝 (ell - s)) := by
  have h := tendsto_rescaled_segment_tail_dist gamma L a hell ha hsegment htail
    hs (show ell ∈ Icc 0 ell from ⟨hell.le, le_rfl⟩)
  simpa only [mul_div_cancel_right₀ _ hell.ne', add_sub_cancel,
    abs_of_nonpos (sub_nonpos.mpr hs.2), neg_sub] using h

theorem eventually_rescaled_segment_tail_subset_ball
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {rho ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (hL : Tendsto L atTop (𝓝 rho))
    (htail : Tendsto (fun i => L i - a i) atTop (𝓝 ell))
    {T : ℝ} (hT : 0 ≤ T) (hTell : T < ell) :
    ∃ A : ℝ, 0 < A ∧ A < rho ∧ ∀ᶠ i in atTop,
      ∀ s ∈ Icc 0 T,
        gamma i (a i + (L i - a i) * s / ell) ∈ Metric.ball (gamma i 0) A := by
  have halim : Tendsto a atTop (𝓝 (rho - ell)) := by
    simpa only [sub_sub_cancel] using hL.sub htail
  have hapos : 0 ≤ rho - ell := ge_of_tendsto halim (Eventually.of_forall fun i => (ha i).1)
  let A : ℝ := (rho + (rho - ell + T)) / 2
  have hApos : 0 < A := by dsimp [A]; linarith
  have hArho : A < rho := by dsimp [A]; linarith
  have hgap : rho - ell + T < A := by dsimp [A]; linarith
  have hlim : Tendsto (fun i => a i + (L i - a i) * T / ell)
      atTop (𝓝 (rho - ell + T)) := by
    convert halim.add ((htail.mul_const T).div_const ell) using 1
    field_simp
  refine ⟨A, hApos, hArho, ?_⟩
  filter_upwards [hlim.eventually_lt_const hgap] with i hi
  intro s hs
  have hs' : s ∈ Icc 0 ell := ⟨hs.1, hs.2.trans hTell.le⟩
  have hmem := rescaled_segment_tail_mem_Icc hell (ha i) hs'
  have hzero : (0 : ℝ) ∈ Icc 0 (L i) := ⟨le_rfl, (ha i).1.trans (ha i).2⟩
  rw [Metric.mem_ball, hsegment i _ hmem _ hzero, sub_zero, abs_of_nonneg hmem.1]
  have hle : (L i - a i) * s / ell ≤ (L i - a i) * T / ell :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs.2 (sub_nonneg.mpr (ha i).2)) hell.le
  linarith

theorem eventually_lipschitzOnWith_rescaled_segment_tail
    (gamma : ∀ i, ℝ → M i) (L a : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (ha : ∀ i, a i ∈ Icc 0 (L i))
    (hsegment : ∀ i, ∀ s ∈ Icc 0 (L i), ∀ t ∈ Icc 0 (L i),
      dist (gamma i s) (gamma i t) = |s - t|)
    (htail : Tendsto (fun i => L i - a i) atTop (𝓝 ell))
    {C : ℝ≥0} (hC : 1 < C) :
    ∀ᶠ i in atTop, LipschitzOnWith C
      (fun s => gamma i (a i + (L i - a i) * s / ell)) (Icc 0 ell) := by
  have hlim : Tendsto (fun i => (L i - a i) / ell) atTop (𝓝 1) := by
    simpa only [div_self hell.ne'] using htail.div_const ell
  have hC' : (1 : ℝ) < C := hC
  filter_upwards [hlim.eventually_lt_const hC'] with i hi
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [rescaled_segment_tail_dist gamma L a hell ha hsegment i hs ht, Real.dist_eq]
  exact mul_le_mul_of_nonneg_right hi.le (abs_nonneg _)


end DifferentialGeometry.Geometry
