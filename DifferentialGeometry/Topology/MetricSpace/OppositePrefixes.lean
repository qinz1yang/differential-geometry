import DifferentialGeometry.Topology.MetricSpace.ShortCurvePrefix

open Set

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem opposite_prefix_distance_calibration
    {o aPlus aMinus : X} {L η : ℝ}
    (hplus : dist o aPlus = L)
    (qPlus qMinus : Icc (0 : ℝ) L → X)
    (hrPlus : ∀ t, dist o (qPlus t) ≤ t.val)
    (hrMinus : ∀ t, dist o (qMinus t) ≤ t.val)
    (htPlus : ∀ t, dist (qPlus t) aPlus ≤ L + η - t.val)
    (htMinus : ∀ t, dist (qMinus t) aMinus ≤ L + η - t.val) :
    (∀ t u, t.val + u.val - (2 * L - dist aPlus aMinus) - 2 * η ≤
        dist (qPlus t) (qMinus u) ∧ dist (qPlus t) (qMinus u) ≤ t.val + u.val) ∧
    (∀ t, t.val - η ≤ L - dist (qPlus t) aPlus ∧
      L - dist (qPlus t) aPlus ≤ t.val ∧
      -t.val ≤ L - dist (qMinus t) aPlus ∧
      L - dist (qMinus t) aPlus ≤ -t.val + (2 * L - dist aPlus aMinus) + η) := by
  constructor
  · intro t u
    have hcross := dist_triangle4 aPlus (qPlus t) (qMinus u) aMinus
    rw [dist_comm aPlus (qPlus t)] at hcross
    have hupper := dist_triangle (qPlus t) o (qMinus u)
    rw [dist_comm (qPlus t) o] at hupper
    exact ⟨by linarith [htPlus t, htMinus u], by linarith [hrPlus t, hrMinus u]⟩
  · intro t
    have hp := dist_triangle o (qPlus t) aPlus
    rw [hplus] at hp
    have hm := dist_triangle (qMinus t) o aPlus
    rw [dist_comm (qMinus t) o, hplus] at hm
    have hpm := dist_triangle aPlus (qMinus t) aMinus
    rw [dist_comm aPlus (qMinus t)] at hpm
    exact ⟨by linarith [htPlus t], by linarith [hrPlus t],
      by linarith [hrMinus t], by linarith [htMinus t]⟩

theorem exists_opposite_calibrated_prefixes
    (hcurves : ∀ p a : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = p ∧ c 1 = a ∧
        eVariationOn c univ < ENNReal.ofReal (dist p a + η))
    (o aPlus aMinus : X) {L η : ℝ} (hL : 0 < L) (hη : 0 < η)
    (hplus : dist o aPlus = L) (hminus : dist o aMinus = L) :
    ∃ qPlus qMinus : Icc (0 : ℝ) L → X,
      LipschitzWith 1 qPlus ∧ LipschitzWith 1 qMinus ∧
      qPlus ⟨0, ⟨le_rfl, hL.le⟩⟩ = o ∧ qMinus ⟨0, ⟨le_rfl, hL.le⟩⟩ = o ∧
      (∀ t, t.val - η ≤ dist o (qPlus t) ∧ dist o (qPlus t) ≤ t.val ∧
        t.val - η ≤ dist o (qMinus t) ∧ dist o (qMinus t) ≤ t.val) ∧
      (∀ s t, s ≤ t → t.val - s.val - η ≤ dist (qPlus s) (qPlus t) ∧
        dist (qPlus s) (qPlus t) ≤ t.val - s.val ∧
        t.val - s.val - η ≤ dist (qMinus s) (qMinus t) ∧
        dist (qMinus s) (qMinus t) ≤ t.val - s.val) ∧
      (∀ t u, t.val + u.val - (2 * L - dist aPlus aMinus) - 2 * η ≤
        dist (qPlus t) (qMinus u) ∧ dist (qPlus t) (qMinus u) ≤ t.val + u.val) ∧
      (∀ t, t.val - η ≤ L - dist (qPlus t) aPlus ∧
        L - dist (qPlus t) aPlus ≤ t.val ∧
        -t.val ≤ L - dist (qMinus t) aPlus ∧
        L - dist (qMinus t) aPlus ≤ -t.val + (2 * L - dist aPlus aMinus) + η) ∧
      ∀ T : ℝ, ∀ t, t.val ≤ T → qPlus t ∈ closedBall o T ∧ qMinus t ∈ closedBall o T := by
  obtain ⟨cPlus, hcPlus, hcPlus0, hcPlus1, hlenPlus⟩ := hcurves o aPlus η hη
  obtain ⟨cMinus, hcMinus, hcMinus0, hcMinus1, hlenMinus⟩ := hcurves o aMinus η hη
  have hp := exists_short_curve_prefix hη cPlus hcPlus hcPlus0 hcPlus1 hlenPlus
  have hm := exists_short_curve_prefix hη cMinus hcMinus hcMinus0 hcMinus1 hlenMinus
  obtain ⟨QPlus, hQPlus, hQPlus0, htQPlus, hrQPlus, hdQPlus, _⟩ := hp
  obtain ⟨QMinus, hQMinus, hQMinus0, htQMinus, hrQMinus, hdQMinus, _⟩ := hm
  let inclPlus : Icc (0 : ℝ) L → Icc (0 : ℝ) (dist o aPlus) :=
    fun t => ⟨t.val, by simpa only [hplus] using t.property⟩
  let inclMinus : Icc (0 : ℝ) L → Icc (0 : ℝ) (dist o aMinus) :=
    fun t => ⟨t.val, by simpa only [hminus] using t.property⟩
  let qPlus := QPlus ∘ inclPlus
  let qMinus := QMinus ∘ inclMinus
  have hiPlus : Isometry inclPlus := Isometry.of_dist_eq (fun _ _ => rfl)
  have hiMinus : Isometry inclMinus := Isometry.of_dist_eq (fun _ _ => rfl)
  have hqPlus : LipschitzWith 1 qPlus := by simpa only [mul_one] using hQPlus.comp hiPlus.lipschitzWith
  have hqMinus : LipschitzWith 1 qMinus := by simpa only [mul_one] using hQMinus.comp hiMinus.lipschitzWith
  have hqPlus0 : qPlus ⟨0, ⟨le_rfl, hL.le⟩⟩ = o := hQPlus0
  have hqMinus0 : qMinus ⟨0, ⟨le_rfl, hL.le⟩⟩ = o := hQMinus0
  have htPlus (t : Icc (0 : ℝ) L) : dist (qPlus t) aPlus < L + η - t.val := by
    have hh := htQPlus (inclPlus t)
    change dist (qPlus t) aPlus < dist o aPlus + η - t.val at hh
    rwa [hplus] at hh
  have htMinus (t : Icc (0 : ℝ) L) : dist (qMinus t) aMinus < L + η - t.val := by
    have hh := htQMinus (inclMinus t)
    change dist (qMinus t) aMinus < dist o aMinus + η - t.val at hh
    rwa [hminus] at hh
  have hrPlus (t : Icc (0 : ℝ) L) : t.val - η ≤ dist o (qPlus t) ∧ dist o (qPlus t) ≤ t.val :=
    hrQPlus (inclPlus t)
  have hrMinus (t : Icc (0 : ℝ) L) : t.val - η ≤ dist o (qMinus t) ∧ dist o (qMinus t) ≤ t.val :=
    hrQMinus (inclMinus t)
  have hdPlus (s t : Icc (0 : ℝ) L) (hst : s ≤ t) :
      t.val - s.val - η ≤ dist (qPlus s) (qPlus t) ∧ dist (qPlus s) (qPlus t) ≤ t.val - s.val :=
    hdQPlus (inclPlus s) (inclPlus t) hst
  have hdMinus (s t : Icc (0 : ℝ) L) (hst : s ≤ t) :
      t.val - s.val - η ≤ dist (qMinus s) (qMinus t) ∧ dist (qMinus s) (qMinus t) ≤ t.val - s.val :=
    hdQMinus (inclMinus s) (inclMinus t) hst
  obtain ⟨hcross, hcal⟩ := opposite_prefix_distance_calibration hplus qPlus qMinus
    (fun t => (hrPlus t).2) (fun t => (hrMinus t).2)
    (fun t => (htPlus t).le) (fun t => (htMinus t).le)
  refine ⟨qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0, ?_, ?_, hcross, hcal, ?_⟩
  · intro t
    exact ⟨(hrPlus t).1, (hrPlus t).2, (hrMinus t).1, (hrMinus t).2⟩
  · intro s t hst
    exact ⟨(hdPlus s t hst).1, (hdPlus s t hst).2, (hdMinus s t hst).1, (hdMinus s t hst).2⟩
  · intro T t ht
    constructor
    · rw [mem_closedBall, dist_comm]; exact (hrPlus t).2.trans ht
    · rw [mem_closedBall, dist_comm]; exact (hrMinus t).2.trans ht

end Metric
