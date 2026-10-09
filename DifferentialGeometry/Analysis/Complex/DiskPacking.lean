import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic.Choose

namespace Homeomorph

theorem sum_sq_dist_apply_le_volume_image
    {ι : Type*} (h : ℂ ≃ₜ ℂ) (s : Finset ι)
    (c a b : ι → ℂ) (r : ι → ℝ)
    {K : Set ℂ} (hK : IsCompact K) {κ : ℝ}
    (hdisj : (s : Set ι).PairwiseDisjoint (fun i => Metric.ball (c i) (r i)))
    (hcontain : ∀ i ∈ s, Metric.ball (c i) (r i) ⊆ K)
    (ha : ∀ i ∈ s, a i ∈ Metric.closedBall (c i) (r i))
    (hb : ∀ i ∈ s, b i ∈ Metric.closedBall (c i) (r i))
    (hdisks : ∀ i ∈ s, ∃ ρ R : ℝ, 0 < ρ ∧
      Metric.closedBall (h (c i)) ρ ⊆ h '' Metric.ball (c i) (r i) ∧
      h '' Metric.closedBall (c i) (r i) ⊆ Metric.closedBall (h (c i)) R ∧
      R ≤ κ * ρ) :
    ∑ i ∈ s, dist (h (a i)) (h (b i)) ^ 2 ≤
      (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (h '' K)).toReal := by
  classical
  choose! ρ R hρ hinner houter hratio using hdisks
  let D (i : ι) := Metric.closedBall (h (c i)) (ρ i)
  have hDdisj : (s : Set ι).PairwiseDisjoint D := by
    intro i hi j hj hij
    exact (Set.disjoint_image_of_injective h.injective (hdisj hi hj hij)).mono
      (hinner i hi) (hinner j hj)
  have hfinite (i : ι) : MeasureTheory.volume (D i) ≠ ⊤ :=
    (isCompact_closedBall (h (c i)) (ρ i)).measure_ne_top
  have himageFinite : MeasureTheory.volume (h '' K) ≠ ⊤ :=
    (hK.image h.continuous).measure_ne_top
  have hmass : ∑ i ∈ s, MeasureTheory.volume (D i) ≤ MeasureTheory.volume (h '' K) := by
    rw [← MeasureTheory.measure_biUnion_finset hDdisj
      (fun i _ => (isCompact_closedBall (h (c i)) (ρ i)).isClosed.measurableSet)]
    apply MeasureTheory.measure_mono
    intro z hz
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
    exact Set.image_mono (hcontain i hi) (hinner i hi hzi)
  have hmassReal := ENNReal.toReal_mono himageFinite hmass
  rw [ENNReal.toReal_sum (fun i _ => hfinite i)] at hmassReal
  have harea (i : ι) (hi : i ∈ s) :
      (MeasureTheory.volume (D i)).toReal = Real.pi * ρ i ^ 2 := by
    change (MeasureTheory.volume (Metric.closedBall (h (c i)) (ρ i))).toReal = _
    rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (hρ i hi).le, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  have hbound (i : ι) (hi : i ∈ s) :
      dist (h (a i)) (h (b i)) ^ 2 ≤
        (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (D i)).toReal := by
    have hai := Metric.mem_closedBall.mp (houter i hi (Set.mem_image_of_mem h (ha i hi)))
    have hbi := Metric.mem_closedBall.mp (houter i hi (Set.mem_image_of_mem h (hb i hi)))
    have hd : dist (h (a i)) (h (b i)) ≤ 2 * κ * ρ i := calc
      _ ≤ dist (h (a i)) (h (c i)) + dist (h (c i)) (h (b i)) := dist_triangle _ _ _
      _ ≤ R i + R i := add_le_add hai (by simpa only [dist_comm] using hbi)
      _ ≤ 2 * κ * ρ i := by linarith [hratio i hi]
    calc
      _ ≤ (2 * κ * ρ i) ^ 2 :=
        (sq_le_sq₀ dist_nonneg (dist_nonneg.trans hd)).mpr hd
      _ = (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (D i)).toReal := by
        rw [harea i hi]
        field_simp
        ring
  calc
    _ ≤ ∑ i ∈ s, (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (D i)).toReal :=
      Finset.sum_le_sum hbound
    _ = (4 * κ ^ 2 / Real.pi) * ∑ i ∈ s, (MeasureTheory.volume (D i)).toReal :=
      (Finset.mul_sum ..).symm
    _ ≤ (4 * κ ^ 2 / Real.pi) * (MeasureTheory.volume (h '' K)).toReal :=
      mul_le_mul_of_nonneg_left hmassReal (by positivity)

end Homeomorph
