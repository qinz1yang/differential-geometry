# Full conditional AC09–10 independent acceptance

Nine public theorems, two definitions and one private helper in four leaves add14 owned declarations, including two generated declarations. The364-module gate checks1706 declarations in3199 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;16 reports cover all11 public production declarations and five concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root independently read the full09 proof and the actual source passages. The independent reviewer read all10 proofs, including the literal obstruction and compactness corollary, and the original source statements. Root read every final regression body. Final tests import canonical production leaves with minimal production imports.

The short-hinge tests take theta=pi/6,a0=a2, the EXACT maximal allowed ell=tau(2,theta), and the maximal allowed model anglepi/2-theta. An actual real minimizing hinge at that threshold is built, its canonical germ angle0 proved, and its actual model comparison verified. A separate actual real hinge with endpoints2,4 at0 retains angle0 and comparison but disproves the distance-drop conclusion when shortness is omitted. This is a checked negative control for a material hypothesis.

The full original-angular-input test constructs signed real minimizing hinges for EVERY ordered distinct point pair and EVERY anchor. Their canonical angles0/pi and actual comparisons are proved. The two-point metric direction space{0,pi} has its literal rank1 obstruction proved; no obstruction hypothesis is merely assumed. Actual anchors-3,+3 and radius tau(2,pi/6)/4 satisfy all remaining inputs. The production theorem's SAME centered distance map is proved exactly F(x)=-x, retaining lower constant1/4, upper1, normalization and a homeomorphism to its own range. A separate metric test exercises both endpoint orientations: the first distance-drop witness is auxiliary0 in one case and genuine1 in the other, so the auxiliary-exclusion branch is checked.

Full AC09 and the original CONDITIONAL AC10 are proved. Direction spaces, their angular obstruction, regular tangent existence and comparison production remain explicit inputs. The chosen direction is shared across anchors, and after choosing an acute anchor the SAME supplied hinge with its exact canonical angle is used. No openness or surjectivity onto a Euclidean neighborhood is claimed. Compactness is asserted only for the actual complete closed inner balls. These results do not bind inherited smooth foundations or complete Chapters3–4. Blueprint207 and migration interfaces are unchanged.

```lean
import DifferentialGeometry.Geometry.Comparison.AngularDistanceEmbedding
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCShortHingeReview

private noncomputable def positiveHinge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    MinimizingHinge a b where
  center := 0
  left t := t
  right t := t
  left_isometry := isometry_subtype_coe
  right_isometry := isometry_subtype_coe
  left_zero := rfl
  right_zero := rfl
  left_end := by simp [Real.dist_eq, abs_of_nonneg ha]
  right_end := by simp [Real.dist_eq, abs_of_nonneg hb]

private theorem positiveHinge_angle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (positiveHinge a b ha.le hb.le).germAngle 1 = 0 := by
  have he : (positiveHinge a b ha.le hb.le).germAngle 1 =
      germComparisonAngle 1 (fun t : ℝ => t) (fun t : ℝ => t) := by
    apply germComparisonAngle_congr_on ha hb
    · intro t ht
      apply IccExtend_of_mem
      simpa only [positiveHinge, Real.dist_eq, sub_zero, zero_sub, abs_neg,
        abs_of_nonneg ha.le, mem_Icc] using (show 0 ≤ t ∧ t ≤ a from ⟨ht.1.le, ht.2⟩)
    · intro t ht
      apply IccExtend_of_mem
      simpa only [positiveHinge, Real.dist_eq, sub_zero, zero_sub, abs_neg,
        abs_of_nonneg hb.le, mem_Icc] using (show 0 ≤ t ∧ t ≤ b from ⟨ht.1.le, ht.2⟩)
  rw [he]
  exact germComparisonAngle_self (by norm_num) (R := 1) zero_lt_one
    (fun _ _ _ _ => Real.dist_eq _ _)

private theorem positiveHinge_comparison {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    dist a b ≤ (positiveHinge a b ha.le hb.le).modelSide 1 := by
  rw [MinimizingHinge.modelSide, positiveHinge_angle ha hb,
    modelSideNegCurvature_zero_angle (by norm_num)]
  simp only [positiveHinge, Real.dist_eq, zero_sub, abs_neg,
    abs_of_nonneg ha.le, abs_of_nonneg hb.le, le_refl]

theorem exact_short_hinge_boundary :
    let ℓ := shortHingeScale 2 (Real.pi / 6)
    0 < ℓ ∧
      modelSideNegCurvature 1 2 ℓ (Real.pi / 2 - Real.pi / 6) ≤ 2 - ℓ / 4 := by
  have hθ : 0 < Real.pi / 6 := by positivity
  have hθhalf : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hℓ := shortHingeScale_pos (a₀ := 2) (by norm_num) hθ hθhalf
  refine ⟨hℓ, ?_⟩
  have hh := modelSide_short_hinge_le (a₀ := 2) (a := 2)
    (by norm_num) le_rfl hℓ hθ hθhalf (by linarith [Real.pi_pos]) le_rfl le_rfl
  rw [Real.sin_pi_div_six] at hh
  convert hh using 1
  ring

theorem actual_positive_hinge_at_threshold :
    let ℓ := shortHingeScale 2 (Real.pi / 6)
    ∃ H : MinimizingHinge (2 : ℝ) ℓ,
      H.center = 0 ∧ H.germAngle 1 = 0 ∧ dist 2 ℓ ≤ H.modelSide 1 ∧
      ℓ / 4 ≤ dist H.center 2 - dist 2 ℓ := by
  have hθ : 0 < Real.pi / 6 := by positivity
  have hθhalf : Real.pi / 6 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hℓ := shortHingeScale_pos (a₀ := 2) (by norm_num) hθ hθhalf
  let ℓ := shortHingeScale 2 (Real.pi / 6)
  let H := positiveHinge 2 ℓ (by norm_num) hℓ.le
  have hangle : H.germAngle 1 = 0 := positiveHinge_angle (by norm_num) hℓ
  have hcomp : dist 2 ℓ ≤ H.modelSide 1 := positiveHinge_comparison (by norm_num) hℓ
  have hdist : dist H.center ℓ = ℓ := by
    change dist (0 : ℝ) ℓ = ℓ
    change |(0 : ℝ) - ℓ| = ℓ
    rw [zero_sub, abs_neg]
    exact abs_of_nonneg hℓ.le
  refine ⟨H, rfl, hangle, hcomp, ?_⟩
  have hh := H.distance_drop_of_short_hinge (a₀ := 2) (θ := Real.pi / 6)
    (by norm_num) (by norm_num [H, positiveHinge, Real.dist_eq])
    (by rw [hdist]; exact hℓ) hθ hθhalf (by rw [hangle]; linarith [Real.pi_pos]) hcomp
    (by rw [hdist])
  rw [hdist, Real.sin_pi_div_six] at hh
  convert hh using 1
  ring

theorem shortness_is_necessary :
    ∃ H : MinimizingHinge (2 : ℝ) 4,
      H.center = 0 ∧ H.germAngle 1 = 0 ∧ dist (2 : ℝ) 4 ≤ H.modelSide 1 ∧
      ¬ dist H.center 4 / 4 ≤ dist H.center 2 - dist (2 : ℝ) 4 := by
  let H := positiveHinge 2 4 (by norm_num) (by norm_num)
  refine ⟨H, rfl, positiveHinge_angle (by norm_num) (by norm_num),
    positiveHinge_comparison (by norm_num) (by norm_num), ?_⟩
  norm_num [H, positiveHinge, Real.dist_eq]

end GCShortHingeReview

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCAngularDistanceReview

private noncomputable def ray (x a t : ℝ) : ℝ := if x ≤ a then x + t else x - t

private theorem ray_isometry (x a : ℝ) : Isometry (ray x a) := by
  apply Isometry.of_dist_eq
  intro s t
  by_cases h : x ≤ a
  · simp only [ray, ite_eq_left h, Real.dist_eq]
    congr 1
    ring
  · simp only [ray, ite_eq_right h, Real.dist_eq]
    rw [show x - s - (x - t) = t - s by ring, abs_sub_comm]

private noncomputable def realHinge (x a y : ℝ) : MinimizingHinge a y where
  center := x
  left t := ray x a t
  right t := ray x y t
  left_isometry := (ray_isometry x a).comp isometry_subtype_coe
  right_isometry := (ray_isometry x y).comp isometry_subtype_coe
  left_zero := by simp [ray]
  right_zero := by simp [ray]
  left_end := by
    by_cases h : x ≤ a
    · simp only [ray, ite_eq_left h, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [ray, ite_eq_right h, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      ring
  right_end := by
    by_cases h : x ≤ y
    · simp only [ray, ite_eq_left h, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [ray, ite_eq_right h, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge h))]
      ring

private theorem realHinge_angle {x a y : ℝ} (ha : x ≠ a) (hy : x ≠ y) :
    (realHinge x a y).germAngle 1 = if (x ≤ a ↔ x ≤ y) then 0 else Real.pi := by
  have he : (realHinge x a y).germAngle 1 = germComparisonAngle 1 (ray x a) (ray x y) := by
    apply germComparisonAngle_congr_on (dist_pos.mpr ha) (dist_pos.mpr hy)
    · intro t ht
      exact IccExtend_of_mem _ _ ⟨ht.1.le, ht.2⟩
    · intro t ht
      exact IccExtend_of_mem _ _ ⟨ht.1.le, ht.2⟩
  have hplus : germComparisonAngle 1 (fun t : ℝ => x + t) (fun t : ℝ => x + t) = 0 := by
    apply germComparisonAngle_self (κ := 1) (by norm_num) (R := 1) zero_lt_one
    intro s _ t _
    rw [Real.dist_eq]
    congr 1
    ring
  have hminus : germComparisonAngle 1 (fun t : ℝ => x - t) (fun t : ℝ => x - t) = 0 := by
    apply germComparisonAngle_self (κ := 1) (by norm_num) (R := 1) zero_lt_one
    intro s _ t _
    rw [Real.dist_eq, show x - s - (x - t) = t - s by ring, abs_sub_comm]
  have hopposite : germComparisonAngle 1 (fun t : ℝ => x + t) (fun t : ℝ => x - t) = Real.pi := by
    apply germComparisonAngle_opposite (κ := 1) (by norm_num) (R := 1) zero_lt_one (S := 1) zero_lt_one
    intro s hs t ht
    rw [Real.dist_eq, show x + s - (x - t) = s + t by ring, abs_of_pos (by linarith [hs.1, ht.1])]
  rw [he]
  unfold ray
  by_cases hxa : x ≤ a <;> by_cases hxy : x ≤ y
  · simpa [hxa, hxy] using hplus
  · simpa [hxa, hxy] using hopposite
  · simpa [hxa, hxy] using
      (germComparisonAngle_comm 1 (fun t : ℝ => x - t) (fun t : ℝ => x + t)).trans hopposite
  · simpa [hxa, hxy] using hminus

private theorem realHinge_comparison {x a y : ℝ} (ha : x ≠ a) (hy : x ≠ y) :
    dist a y ≤ (realHinge x a y).modelSide 1 := by
  rw [MinimizingHinge.modelSide, realHinge_angle ha hy]
  change dist a y ≤ modelSideNegCurvature 1 (dist x a) (dist x y) _
  by_cases hxa : x ≤ a <;> by_cases hxy : x ≤ y
  · rw [ite_eq_left (by simp [hxa, hxy]), modelSideNegCurvature_zero_angle (by norm_num)]
    rw [Real.dist_eq x a, Real.dist_eq x y, abs_of_nonpos (sub_nonpos.mpr hxa),
      abs_of_nonpos (sub_nonpos.mpr hxy), Real.dist_eq]
    have he : -(x - a) - -(x - y) = a - y := by ring
    rw [he]
  · rw [ite_eq_right (by simp [hxa, hxy]), modelSideNegCurvature_pi (by norm_num) dist_nonneg dist_nonneg]
    exact dist_triangle_left a y x
  · rw [ite_eq_right (by simp [hxa, hxy]), modelSideNegCurvature_pi (by norm_num) dist_nonneg dist_nonneg]
    exact dist_triangle_left a y x
  · rw [ite_eq_left (by simp [hxa, hxy]), modelSideNegCurvature_zero_angle (by norm_num)]
    rw [Real.dist_eq x a, Real.dist_eq x y, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxa)),
      abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy)), Real.dist_eq]
    have he : (x - a) - (x - y) = y - a := by ring
    rw [he, abs_sub_comm]

private abbrev Directions := {r : ℝ // r = 0 ∨ r = Real.pi}
private def minusDirection : Directions := ⟨0, Or.inl rfl⟩
private noncomputable def plusDirection : Directions := ⟨Real.pi, Or.inr rfl⟩
private def anchors (j : Fin 2) : ℝ := if j = 0 then -3 else 3
private noncomputable def anchorDirections (j : Fin 2) : Directions := if j = 0 then minusDirection else plusDirection

private theorem obstruction : AngularObstruction Directions 1 (Real.pi / 6) := by
  rintro ⟨ξ, ζ, hsep, hfar⟩
  have hs := hsep 0 1 (by decide)
  have h0 := hfar 0
  have h1 := hfar 1
  change Real.pi / 2 + Real.pi / 6 < |(ζ 0).val - (ζ 1).val| at hs
  change Real.pi / 2 - Real.pi / 6 < |ξ.val - (ζ 0).val| at h0
  change Real.pi / 2 - Real.pi / 6 < |ξ.val - (ζ 1).val| at h1
  rcases ξ.property with hξ | hξ <;> rcases (ζ 0).property with hz | hz <;>
    rcases (ζ 1).property with ho | ho
  all_goals rw [hξ, hz] at h0; rw [hξ, ho] at h1; rw [hz, ho] at hs
  all_goals simp only [sub_self, abs_zero, zero_sub, abs_neg, sub_zero,
    abs_of_nonneg Real.pi_pos.le] at hs h0 h1
  all_goals linarith [Real.pi_pos]

private noncomputable def radius : ℝ := shortHingeScale 2 (Real.pi / 6) / 4
private theorem radius_pos : 0 < radius := by
  apply div_pos _ (by norm_num)
  exact shortHingeScale_pos (by norm_num) (by positivity) (by linarith [Real.pi_pos])
private theorem radius_le : radius ≤ 1 / 4 := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

private theorem abs_lt_one (x : ball (0 : ℝ) radius) : |x.val| < 1 := by
  have h : |x.val| < radius := by simpa only [mem_ball, Real.dist_eq, sub_zero] using x.property
  linarith [radius_le]

private theorem anchor_bound (x : ball (0 : ℝ) radius) (j : Fin 2) : 2 ≤ dist x.val (anchors j) := by
  have hx := abs_lt_one x
  have hb := abs_lt.mp hx
  fin_cases j <;> norm_num [anchors, Real.dist_eq]
  · rw [abs_of_pos (by linarith)]
    linarith
  · rw [abs_of_neg (by linarith)]
    linarith

private theorem actual_hinges (x y : ball (0 : ℝ) radius) (hxy : x ≠ y) :
    ∃ ξ : Directions, ∀ j, ∃ H : MinimizingHinge (anchors j) y.val,
      H.center = x.val ∧ H.germAngle 1 = dist ξ (anchorDirections j) ∧
        dist (anchors j) y.val ≤ H.modelSide 1 := by
  have hne : x.val ≠ y.val := fun hh => hxy (Subtype.ext hh)
  let ξ : Directions := if x.val ≤ y.val then plusDirection else minusDirection
  refine ⟨ξ, fun j => ?_⟩
  have hxa : x.val ≠ anchors j := dist_pos.mp (lt_of_lt_of_le (by norm_num) (anchor_bound x j))
  refine ⟨realHinge x.val (anchors j) y.val, rfl, ?_, realHinge_comparison hxa hne⟩
  rw [realHinge_angle hxa hne]
  have hx := abs_lt.mp (abs_lt_one x)
  by_cases h : x.val ≤ y.val <;> fin_cases j
  all_goals norm_num [anchors, anchorDirections, ξ, h, plusDirection, minusDirection,
    Subtype.dist_eq, Real.dist_eq, show ¬ x.val ≤ -3 by linarith,
    show x.val ≤ 3 by linarith, abs_of_nonneg Real.pi_pos.le]

theorem actual_angular_distance_embedding :
    let F : ball (0 : ℝ) radius → EuclideanSpace ℝ (Fin 1) := fun x => WithLp.toLp 2 (fun _ => -x.val)
    F ⟨0, mem_ball_self radius_pos⟩ = 0 ∧
      (∀ x y, dist x y / 4 ≤ dist (F x) (F y)) ∧ LipschitzWith 1 F ∧
      ∃ e : ball (0 : ℝ) radius ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin 1)) = F x := by
  let G : ball (0 : ℝ) radius → EuclideanSpace ℝ (Fin 1) := fun x =>
    distanceCoordinates 2 (fun j : Fin 1 => anchors j.succ) x -
      distanceCoordinates 2 (fun j : Fin 1 => anchors j.succ) 0
  have hh := exists_centered_distance_embedding_of_angular_obstruction radius_pos
    (a₀ := 2) (θ := Real.pi / 6) (by norm_num) (by positivity) (by linarith [Real.pi_pos])
    anchors (fun _ => Directions) (fun _ => anchorDirections) anchor_bound
    (by have hr := radius_pos; dsimp [radius] at hr ⊢; linarith)
    (by
      intro x i j hij
      fin_cases i <;> fin_cases j
      all_goals try exact (hij rfl).elim
      all_goals norm_num [anchorDirections, minusDirection, plusDirection,
        Subtype.dist_eq, Real.dist_eq, abs_of_nonneg Real.pi_pos.le]
      all_goals linarith [Real.pi_pos])
    (fun _ => obstruction) actual_hinges
  change G ⟨0, mem_ball_self radius_pos⟩ = 0 ∧
    (∀ x y, (Real.sin (Real.pi / 6) / 2) * dist x y ≤ dist (G x) (G y)) ∧
    LipschitzWith (NNReal.sqrt (1 : ℕ)) G ∧ ∃ e : ball (0 : ℝ) radius ≃ₜ range G,
      ∀ x, (e x : EuclideanSpace ℝ (Fin 1)) = G x at hh
  have hG : G = fun x : ball (0 : ℝ) radius => WithLp.toLp 2 (fun _ : Fin 1 => -x.val) := by
    funext x
    ext j
    fin_cases j
    have hx := abs_lt.mp (abs_lt_one x)
    change dist x.val (anchors 1) - dist (0 : ℝ) (anchors 1) = -x.val
    norm_num [anchors, Real.dist_eq, abs_of_neg (show x.val - 3 < 0 by linarith)]
  rw [hG] at hh
  simpa only [Real.sin_pi_div_six, NNReal.sqrt_one, Nat.cast_one,
    show (1 / 2 / 2 : ℝ) = 1 / 4 by norm_num, one_div_mul_eq_div] using hh


theorem both_endpoint_orientations :
    (∃ j : Fin 1, (1 / 4 : ℝ) * dist (1 / 8 : ℝ) 0 ≤
      |dist (1 / 8 : ℝ) (anchors j.succ) - dist (0 : ℝ) (anchors j.succ)|) ∧
    (∃ j : Fin 1, (1 / 4 : ℝ) * dist (0 : ℝ) (1 / 8) ≤
      |dist (0 : ℝ) (anchors j.succ) - dist (1 / 8 : ℝ) (anchors j.succ)|) := by
  constructor
  · apply exists_nonauxiliary_distance_separation anchors (by norm_num) (by norm_num)
    · exact ⟨0, by norm_num [anchors, Real.dist_eq]⟩
    · exact ⟨1, by norm_num [anchors, Real.dist_eq]⟩
  · apply exists_nonauxiliary_distance_separation anchors (by norm_num) (by norm_num)
    · exact ⟨1, by norm_num [anchors, Real.dist_eq]⟩
    · exact ⟨0, by norm_num [anchors, Real.dist_eq]⟩

end GCAngularDistanceReview

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.shortHingeScale
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.shortHingeScale_pos
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.modelSide_short_hinge_le
#print axioms Metric.MinimizingHinge.distance_drop_of_short_hinge
#print axioms Metric.exists_nonauxiliary_distance_separation
#print axioms Metric.distanceCoordinates_lower_of_endpoint_reversal
#print axioms Metric.exists_centered_distance_embedding_of_endpoint_reversal
#print axioms Metric.isCompact_closedBall_of_endpoint_reversal
#print axioms Metric.AngularObstruction
#print axioms Metric.AngularObstruction.exists_acute_anchor
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_centered_distance_embedding_of_angular_obstruction
#print axioms GCShortHingeReview.exact_short_hinge_boundary
#print axioms GCShortHingeReview.actual_positive_hinge_at_threshold
#print axioms GCShortHingeReview.shortness_is_necessary
#print axioms GCAngularDistanceReview.actual_angular_distance_embedding
#print axioms GCAngularDistanceReview.both_endpoint_orientations
#lint- only unusedArguments simpNF synTaut
```
