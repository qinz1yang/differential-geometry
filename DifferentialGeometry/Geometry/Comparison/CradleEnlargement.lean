import DifferentialGeometry.Geometry.Comparison.GeometricCradleStep
import DifferentialGeometry.Geometry.Comparison.CradleIteration

set_option autoImplicit false

open Set

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem modelSide_ge_dist_of_small_hinges (H : MinimizingHinge p q)
    {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ)
    (hp : endpointHingeComparison κ p (2 * ℓ / 3))
    (hq : endpointHingeComparison κ q (2 * ℓ / 3))
    (hjoins : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ J : MinimizingHinge p q, J.center = z)
    (hlocal : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (hsum : dist H.center p + dist H.center q < ℓ) : dist p q ≤ H.modelSide κ := by
  let T := {J : MinimizingHinge p q // dist J.center p + dist J.center q < ℓ}
  let a : T → ℝ := fun z => min (dist z.val.center p) (dist z.val.center q)
  let b : T → ℝ := fun z => max (dist z.val.center p) (dist z.val.center q)
  let α : T → ℝ := fun z => z.val.germAngle κ
  have heq (z : T) : modelSideNegCurvature κ (a z) (b z) (α z) = z.val.modelSide κ :=
    z.val.modelSide_sorted κ
  have hwindow (z : T) (hbad : modelSideNegCurvature κ (a z) (b z) (α z) < dist p q) :
      0 ≤ a z ∧ a z ≤ b z ∧ 2 * ℓ / 3 ≤ a z + b z ∧ a z + b z < ℓ := by
    rw [heq] at hbad
    have hlo : 2 * ℓ / 3 ≤ dist z.val.center p + dist z.val.center q := by
      by_contra hn
      exact (not_le_of_gt hbad)
        (z.val.modelSide_ge_dist_of_endpoint_comparison hκ hp (lt_of_not_ge hn))
    exact ⟨le_min dist_nonneg dist_nonneg, (min_le_left _ _).trans (le_max_left _ _),
      by simpa only [a, b, min_add_max] using hlo,
      by simpa only [a, b, min_add_max] using z.property⟩
  have htriangle (z : T) : dist p q ≤ a z + b z := by
    have ht := dist_triangle p z.val.center q
    rw [dist_comm p z.val.center] at ht
    simpa only [a, b, min_add_max] using ht
  have hstep (z : T) (hbad : modelSideNegCurvature κ (a z) (b z) (α z) < dist p q) :
      ∃ z' : T, ∃ c, 0 ≤ c ∧ c ≤ a z + (2 * ℓ / 3 - a z) / 3 ∧
        a z' = min c (b z - (2 * ℓ / 3 - a z) / 3) ∧
        b z' = max c (b z - (2 * ℓ / 3 - a z) / 3) ∧
        modelSideNegCurvature κ (a z') (b z') (α z') ≤
          modelSideNegCurvature κ (a z) (b z) (α z) ∧
        comparisonAngleNegCurvature κ (a z) ((2 * ℓ / 3 - a z) / 3) c ≤ α z := by
    rw [heq] at hbad
    by_cases hsort : dist z.val.center p ≤ dist z.val.center q
    · obtain ⟨K, hrange, hmove, hbound, hremain, hsumK, hside, hangle⟩ :=
        z.val.exists_cradle_successor_of_modelSide_lt hκ hℓ hp hjoins hlocal hsort z.property hbad
      refine ⟨⟨K, hsumK⟩, dist K.center p, dist_nonneg, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [a, min_eq_left hsort] using hbound
      · change min (dist K.center p) (dist K.center q) = _
        rw [hremain]
        simp only [a, b, min_eq_left hsort, max_eq_right hsort]
      · change max (dist K.center p) (dist K.center q) = _
        rw [hremain]
        simp only [a, b, min_eq_left hsort, max_eq_right hsort]
      · rw [heq, heq]
        exact hside
      · simpa only [a, α, min_eq_left hsort] using hangle
    · have hsort' : dist z.val.center q ≤ dist z.val.center p := le_of_not_ge hsort
      have hjoins' : ∀ y : X, dist y q + dist y p < ℓ →
          ∃ J : MinimizingHinge q p, J.center = y := by
        intro y hy
        obtain ⟨J, hJ⟩ := hjoins y (by linarith)
        exact ⟨J.reverse, hJ⟩
      have hlocal' : ∀ y : X, dist y q + dist y p < ℓ →
          ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ y ∈ Ω := by
        intro y hy
        exact hlocal y (by linarith)
      have hsum' : dist z.val.reverse.center q + dist z.val.reverse.center p < ℓ := by
        change dist z.val.center q + dist z.val.center p < ℓ
        linarith [z.property]
      have hbad' : z.val.reverse.modelSide κ < dist q p := by
        rw [z.val.modelSide_reverse, dist_comm q p]
        exact hbad
      obtain ⟨K, hrange, hmove, hbound, hremain, hsumK, hside, hangle⟩ :=
        z.val.reverse.exists_cradle_successor_of_modelSide_lt hκ hℓ hq hjoins' hlocal'
          hsort' hsum' hbad'
      have hsumK' : dist K.reverse.center p + dist K.reverse.center q < ℓ := by
        change dist K.center p + dist K.center q < ℓ
        linarith
      refine ⟨⟨K.reverse, hsumK'⟩, dist K.center q, dist_nonneg, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [a, min_eq_right hsort', reverse] using hbound
      · change min (dist K.center p) (dist K.center q) = _
        rw [min_comm (dist K.center p) (dist K.center q), hremain]
        simp only [a, b, min_eq_right hsort', max_eq_left hsort', reverse]
      · change max (dist K.center p) (dist K.center q) = _
        rw [max_comm (dist K.center p) (dist K.center q), hremain]
        simp only [a, b, min_eq_right hsort', max_eq_left hsort', reverse]
      · rw [heq, heq, K.modelSide_reverse, ← z.val.modelSide_reverse κ]
        exact hside
      · change comparisonAngleNegCurvature κ (a z) ((2 * ℓ / 3 - a z) / 3)
          (dist K.center q) ≤ z.val.germAngle κ
        rw [← z.val.germAngle_reverse κ]
        simpa only [a, min_eq_right hsort', reverse] using hangle
  have hbound := le_modelSideNegCurvature_of_cradle_steps hκ hℓ a b α hwindow
    (fun z => z.val.germAngle_mem_Icc κ) htriangle hstep
  have hfinal := hbound ⟨H, hsum⟩
  rwa [heq] at hfinal

end Metric.MinimizingHinge

namespace Metric.MinimizingHinge

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] {p q : X}

theorem comparisonAngle_le_of_small_hinges (H : MinimizingHinge p q)
    {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ)
    (hp : endpointHingeComparison κ p (2 * ℓ / 3))
    (hq : endpointHingeComparison κ q (2 * ℓ / 3))
    (hjoins : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ J : MinimizingHinge p q, J.center = z)
    (hlocal : ∀ z : X, dist z p + dist z q < ℓ →
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω)
    (ha : 0 < dist H.center p) (hb : 0 < dist H.center q)
    (hsum : dist H.center p + dist H.center q < ℓ) :
    comparisonAngleNegCurvature κ (dist H.center p) (dist H.center q) (dist p q) ≤
      H.germAngle κ :=
  (H.comparisonAngle_le_iff_dist_le_modelSide hκ ha hb).mpr
    (H.modelSide_ge_dist_of_small_hinges hκ hℓ hp hq hjoins hlocal hsum)

end Metric.MinimizingHinge
