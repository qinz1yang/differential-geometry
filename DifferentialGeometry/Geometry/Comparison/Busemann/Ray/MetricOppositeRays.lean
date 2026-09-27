import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry.Geometry.Topology

variable {X : Type*} [MetricSpace X]

theorem dist_eq_add_of_opposite_minimizing_rays {alpha beta : ℝ → X}
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t → dist (alpha s) (alpha t) = |s - t|)
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t → dist (beta s) (beta t) = |s - t|)
    (hcenter : alpha 0 = beta 0)
    (hopposite : ∀ r, 0 ≤ r → dist (alpha r) (beta r) = 2 * r)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (alpha s) (beta t) = s + t := by
  have hleft : dist (alpha s) (alpha 0) = s := by
    simpa only [sub_zero, abs_of_nonneg hs] using halpha s 0 hs le_rfl
  have hright : dist (beta 0) (beta t) = t := by
    simpa only [zero_sub, abs_neg, abs_of_nonneg ht] using hbeta 0 t le_rfl ht
  have hupper := dist_triangle (alpha s) (alpha 0) (beta t)
  rw [hleft, hcenter, hright] at hupper
  have hR : 0 ≤ s + t := add_nonneg hs ht
  have hfarLeft : dist (alpha (s + t)) (alpha s) = t := by
    rw [halpha (s + t) s hR hs]
    have hsub : s + t - s = t := by ring
    rw [hsub, abs_of_nonneg ht]
  have hfarRight : dist (beta t) (beta (s + t)) = s := by
    rw [hbeta t (s + t) ht hR]
    have hsub : t - (s + t) = -s := by ring
    rw [hsub, abs_neg, abs_of_nonneg hs]
  have hchain := (dist_triangle (alpha (s + t)) (alpha s) (beta (s + t))).trans
    (add_le_add_right (dist_triangle (alpha s) (beta t) (beta (s + t)))
      (dist (alpha (s + t)) (alpha s)))
  rw [hopposite (s + t) hR, hfarLeft, hfarRight] at hchain
  exact le_antisymm hupper (by linarith)


def oppositeRayLine (alpha beta : ℝ → X) (t : ℝ) : X :=
  if 0 ≤ t then alpha t else beta (-t)

omit [MetricSpace X] in
theorem oppositeRayLine_of_nonneg (alpha beta : ℝ → X) {t : ℝ} (ht : 0 ≤ t) :
    oppositeRayLine alpha beta t = alpha t := by
  simp only [oppositeRayLine, if_pos ht]

omit [MetricSpace X] in
theorem oppositeRayLine_neg_of_nonneg {alpha beta : ℝ → X}
    (hcenter : alpha 0 = beta 0) {t : ℝ} (ht : 0 ≤ t) :
    oppositeRayLine alpha beta (-t) = beta t := by
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · subst t
    simpa only [neg_zero, oppositeRayLine, le_refl, ite_true] using hcenter
  · have hn : ¬0 ≤ -t := by linarith
    simp only [oppositeRayLine, if_neg hn, neg_neg]

theorem isometry_oppositeRayLine {alpha beta : ℝ → X}
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t → dist (alpha s) (alpha t) = |s - t|)
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t → dist (beta s) (beta t) = |s - t|)
    (hcenter : alpha 0 = beta 0)
    (hopposite : ∀ r, 0 ≤ r → dist (alpha r) (beta r) = 2 * r) :
    Isometry (oppositeRayLine alpha beta) := by
  have hcross (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      dist (alpha u) (beta v) = u + v :=
    dist_eq_add_of_opposite_minimizing_rays halpha hbeta hcenter hopposite hu hv
  apply Isometry.of_dist_eq
  intro s t
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · simpa only [oppositeRayLine, if_pos hs, if_pos ht, Real.dist_eq] using
        halpha s t hs ht
    · have hnt : 0 ≤ -t := by linarith
      have hst : 0 ≤ s - t := by linarith
      simp only [oppositeRayLine, if_pos hs, if_neg ht]
      rw [hcross s (-t) hs hnt, Real.dist_eq, abs_of_nonneg hst]
      ring
  · have hns : 0 ≤ -s := by linarith
    by_cases ht : 0 ≤ t
    · have hst : s - t ≤ 0 := by linarith
      simp only [oppositeRayLine, if_neg hs, if_pos ht]
      rw [dist_comm (beta (-s)) (alpha t), hcross t (-s) ht hns, Real.dist_eq,
        abs_of_nonpos hst]
      ring
    · have hnt : 0 ≤ -t := by linarith
      simp only [oppositeRayLine, if_neg hs, if_neg ht]
      rw [hbeta (-s) (-t) hns hnt, Real.dist_eq, neg_sub_neg, abs_sub_comm]

theorem exists_isometry_of_opposite_minimizing_rays {alpha beta : ℝ → X} {p : X}
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t → dist (alpha s) (alpha t) = |s - t|)
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t → dist (beta s) (beta t) = |s - t|)
    (halpha0 : alpha 0 = p) (hbeta0 : beta 0 = p)
    (hopposite : ∀ r, 0 ≤ r → dist (alpha r) (beta r) = 2 * r) :
    ∃ gamma : ℝ → X, Isometry gamma ∧ gamma 0 = p ∧
      (∀ t, 0 ≤ t → gamma t = alpha t) ∧
      (∀ t, 0 ≤ t → gamma (-t) = beta t) := by
  have hcenter := halpha0.trans hbeta0.symm
  refine ⟨oppositeRayLine alpha beta,
    isometry_oppositeRayLine halpha hbeta hcenter hopposite, ?_, ?_, ?_⟩
  · simpa only [oppositeRayLine, le_refl, ite_true] using halpha0
  · intro t ht
    exact oppositeRayLine_of_nonneg alpha beta ht
  · intro t ht
    exact oppositeRayLine_neg_of_nonneg hcenter ht

theorem isometry_oppositeRayLine_of_endpoint_limits {ι : Type*} {l : Filter ι} [l.NeBot]
    {alpha beta : ℝ → X} {a b : ι → ℝ → X}
    (halpha : ∀ s t, 0 ≤ s → 0 ≤ t → dist (alpha s) (alpha t) = |s - t|)
    (hbeta : ∀ s t, 0 ≤ s → 0 ≤ t → dist (beta s) (beta t) = |s - t|)
    (hcenter : alpha 0 = beta 0)
    (ha : ∀ r, 0 ≤ r → Tendsto (fun i => a i r) l (𝓝 (alpha r)))
    (hb : ∀ r, 0 ≤ r → Tendsto (fun i => b i r) l (𝓝 (beta r)))
    (hdist : ∀ r, 0 ≤ r → Tendsto (fun i => dist (a i r) (b i r)) l (𝓝 (2 * r))) :
    Isometry (oppositeRayLine alpha beta) := by
  apply isometry_oppositeRayLine halpha hbeta hcenter
  intro r hr
  exact tendsto_nhds_unique ((ha r hr).dist (hb r hr)) (hdist r hr)

end DifferentialGeometry.Geometry.Topology
