# Conditional AC12 uniform chart independent acceptance

One public theorem, one definition and one private linear-isometry definition in one leaf add7 owned declarations, including four generated declarations. The369-module gate checks1727 declarations in3204 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;four reports cover both public declarations and two concrete original-input tests (the shortening fixture and the full padded chart). Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root independently read the complete proof and all fixtures. The returned chart uses exactly the same original selected labels and scale and the actual chosen ordered distance coordinates, centered at q. The Euclidean insertion is constructed by the standard orthogonal product decomposition and(v,0); it is not an assumed embedding. Original ball containment is proved for every anchor and chart point before any local direction/hinge invocation. The one actual supplied hinge package also establishes the comparison-angle-to-direction-angle inequality between anchor directions. No unnecessary separate inequality is assumed.

The full regression uses actual sourceR, m1,n2,p27/4,q7,R1,eta1/100. Original Bool-labeled paths7+s and7-s have available lengths2 and3; their actual density, radial identities and comparison-angle limits are proved. The literal two-point angular metric and obstruction are constructed and checked, and actual minimizing real hinges with correct canonical angles/model comparison are supplied for EVERY ordered distinct source pair and anchor. The theorem then chooses unknown d/s/rho and its SAME returned E1→E2/F. For EVERY chart point the test proves F(x)=E(single(7-x)) or E(single(x-7)), according to the original selected d(1), and proves this F is actually an isometry. It retains the exact displayed L(2), all original domain bounds, normalization and homeomorphism to the actual range.

This closes conditional metric chart assembly. The original source-geometric8R assumptions have not yet been connected automatically to the direction/hinge package; sharp AC02 and actual tangent/direction bindings remain explicit. Neither angular obstruction nor Euclidean tangent production is inferred from the dimension upper bound. No openness, Euclidean-neighborhood surjectivity or full Chapters3–4 completion is claimed. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Comparison.UniformStrutChart
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
open Set Filter Topology
namespace GCSimplexShorteningReview
open DifferentialGeometry.Geometry.Comparison.Toponogov

private def direction (b : Bool) : EuclideanSpace ℝ (Fin 1) :=
  PiLp.single 2 0 (if b then (1 : ℝ) else -1)

private theorem direction_norm (b : Bool) : ‖direction b‖ = 1 := by
  cases b <;> simp [direction]

private def unitDirection (b : Bool) : {v : EuclideanSpace ℝ (Fin 1) // ‖v‖ = 1} :=
  ⟨direction b, direction_norm b⟩

private def path (b : Bool) (s : ℝ) : ℝ := 7 + if b then s else -s
private def radius (b : Bool) : ℝ := if b then 2 else 3

private theorem direction_angle (b c : Bool) :
    InnerProductGeometry.angle (direction b) (direction c) = if b = c then 0 else Real.pi := by
  cases b <;> cases c <;>
    norm_num [InnerProductGeometry.angle, direction, PiLp.inner_apply, EuclideanSpace.norm_eq]

private theorem direction_dense (v : EuclideanSpace ℝ (Fin 1)) (hv : ‖v‖ = 1)
    (ε : ℝ) (hε : 0 < ε) : ∃ b, InnerProductGeometry.angle v (unitDirection b).val < ε := by
  have hval : v 0 = 1 ∨ v 0 = -1 := by simpa [EuclideanSpace.norm_eq] using hv
  rcases hval with hval | hval
  · have he : v = direction true := by ext i; fin_cases i; simpa [direction] using hval
    refine ⟨true, ?_⟩
    rw [he]
    simpa [unitDirection, direction_angle] using hε
  · have he : v = direction false := by ext i; fin_cases i; simpa [direction] using hval
    refine ⟨false, ?_⟩
    rw [he]
    simpa [unitDirection, direction_angle] using hε

private theorem path_radial (b : Bool) (s : ℝ) (hs : 0 < s) : dist 7 (path b s) = s := by
  cases b <;> simp [path, abs_of_pos hs]

private theorem path_angle (b c : Bool) (s : ℝ) (hs : 0 < s) :
    comparisonAngleNegCurvature 1 s s (dist (path b s) (path c s)) =
      InnerProductGeometry.angle (unitDirection b).val (unitDirection c).val := by
  by_cases hbc : b = c
  · subst c
    simpa [unitDirection, direction_angle] using comparisonAngleNegCurvature_self (by norm_num) hs
  · have hd : dist (path b s) (path c s) = s + s := by
      cases b <;> cases c <;> norm_num [path, Real.dist_eq] at *
      · rw [abs_of_neg (by linarith)]
        ring
      · exact hs.le
    rw [hd, comparisonAngleNegCurvature_add (by norm_num) hs hs]
    simp [unitDirection, direction_angle, hbc]

theorem original_translated_opposite_paths_have_arbitrarily_small_struts :
    ∃ (d : Fin 2 → Bool) (s : ℝ), 0 < s ∧ s < 1/100 ∧
      (∀ i, s ≤ radius (d i)) ∧
      (∀ i, dist 7 (path (d i) s) = s) ∧
      (∀ i j, i ≠ j → Real.pi/2 + 6 * (8 * (1 : ℝ))⁻¹ <
        InnerProductGeometry.angle (unitDirection (d i)).val (unitDirection (d j)).val) ∧
      (∀ i j, i ≠ j → Real.pi/2 + 5 * (8 * (1 : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 (dist 7 (path (d i) s)) (dist 7 (path (d j) s))
          (dist (path (d i) s) (path (d j) s))) := by
  have hr : ∀ b, 0 < radius b := by intro b; cases b <;> norm_num [radius]
  have hrad : ∀ b, ∀ s ∈ Ioc (0 : ℝ) (radius b), dist 7 (path b s) = s :=
    fun b s hs => path_radial b s hs.1
  have hang : ∀ b c, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (path b s) (path c s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (unitDirection b).val (unitDirection c).val)) := by
    intro b c
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (path_angle b c s hs).symm
  simpa only [Nat.cast_one] using
    exists_common_shortening_strut_of_dense_directions (m := 1) (n := 1)
      (by decide) (by decide) (7 : ℝ) unitDirection path radius hr hrad direction_dense hang
      (S := 1/100) (by norm_num)

end GCSimplexShorteningReview

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


end GCAngularDistanceReview

namespace GCUniformStrutChartReview
open Set Metric Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GCSimplexShorteningReview GCAngularDistanceReview

private abbrev Directions := {r : ℝ // r = 0 ∨ r = Real.pi}
private def minusDirection : Directions := ⟨0, Or.inl rfl⟩
private noncomputable def plusDirection : Directions := ⟨Real.pi, Or.inr rfl⟩
private noncomputable def localDirection (x y : ball (27 / 4 : ℝ) 1) (_h : x.val ≠ y.val) : Directions :=
  if x.val ≤ y.val then plusDirection else minusDirection

private theorem obstruction : AngularObstruction Directions 1 (8 * (2 : ℝ))⁻¹ := by
  rintro ⟨ξ, ζ, hsep, hfar⟩
  have hs := hsep 0 1 (by decide)
  have h0 := hfar 0
  have h1 := hfar 1
  change Real.pi / 2 + (8 * (2 : ℝ))⁻¹ < |(ζ 0).val - (ζ 1).val| at hs
  change Real.pi / 2 - (8 * (2 : ℝ))⁻¹ < |ξ.val - (ζ 0).val| at h0
  change Real.pi / 2 - (8 * (2 : ℝ))⁻¹ < |ξ.val - (ζ 1).val| at h1
  have hpi := Real.sin_le (show 0 ≤ Real.pi / 2 by positivity)
  rw [Real.sin_pi_div_two] at hpi
  rcases ξ.property with hξ | hξ <;> rcases (ζ 0).property with hz | hz <;>
    rcases (ζ 1).property with ho | ho
  all_goals rw [hξ, hz] at h0; rw [hξ, ho] at h1; rw [hz, ho] at hs
  all_goals norm_num only [sub_self, abs_zero, zero_sub, abs_neg, sub_zero,
    abs_of_nonneg Real.pi_pos.le] at hs h0 h1
  all_goals linarith

private theorem actual_local_hinges (x a y : ball (27 / 4 : ℝ) 1)
    (ha : x.val ≠ a.val) (hy : x.val ≠ y.val) :
    ∃ H : MinimizingHinge a.val y.val,
      H.center = x.val ∧ H.germAngle 1 = dist (localDirection x y hy) (localDirection x a ha) ∧
        dist a.val y.val ≤ H.modelSide 1 := by
  refine ⟨realHinge x.val a.val y.val, rfl, ?_, realHinge_comparison ha hy⟩
  rw [realHinge_angle ha hy]
  by_cases hxa : x.val ≤ a.val <;> by_cases hxy : x.val ≤ y.val
  all_goals simp [localDirection, hxa, hxy, plusDirection, minusDirection,
    Subtype.dist_eq, Real.dist_eq, abs_of_nonneg Real.pi_pos.le]

theorem original_dense_paths_have_padded_uniform_chart :
    ∃ (d : Fin 2 → Bool) (s ρ : ℝ), 0 < s ∧ s < 1 / 8 ∧
      (∀ i, s ≤ radius (d i)) ∧ (∀ i, dist 7 (path (d i) s) = s) ∧
      ∃ hρ : 0 < ρ, ρ < s / 8 ∧ ρ < 1 / 100 ∧
        (∀ i, path (d i) s ∈ ball (27 / 4 : ℝ) 1) ∧
        ball (7 : ℝ) ρ ⊆ ball (27 / 4 : ℝ) 1 ∧
        ∃ (E : EuclideanSpace ℝ (Fin 1) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
          (F : ball (7 : ℝ) ρ → EuclideanSpace ℝ (Fin 2)),
          F ⟨7, mem_ball_self hρ⟩ = 0 ∧
          (∀ x, F x = E (PiLp.single 2 0 (if d 1 then 7 - x.val else x.val - 7))) ∧
          (∀ x y, (max (Real.sqrt 2) (2 / Real.sin (1 / 16)))⁻¹ * dist x y ≤ dist (F x) (F y) ∧
            dist (F x) (F y) ≤ max (Real.sqrt 2) (2 / Real.sin (1 / 16)) * dist x y) ∧
          Isometry F ∧
          ∃ e : ball (7 : ℝ) ρ ≃ₜ range F, ∀ x, (e x : EuclideanSpace ℝ (Fin 2)) = F x := by
  have hr : ∀ b, 0 < radius b := by intro b; cases b <;> norm_num [radius]
  have hrad : ∀ b, ∀ s ∈ Ioc (0 : ℝ) (radius b), dist 7 (path b s) = s :=
    fun b s hs => path_radial b s hs.1
  have hang : ∀ b c, Tendsto
      (fun s : ℝ => comparisonAngleNegCurvature 1 s s (dist (path b s) (path c s)))
      (𝓝[>] (0 : ℝ)) (𝓝 (InnerProductGeometry.angle (unitDirection b).val (unitDirection c).val)) := by
    intro b c
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (path_angle b c s hs).symm
  obtain ⟨d, s, ρ, hs, hsR, hsr, hsa, hρ, hρs, hρη, haR, hsubset, _hL,
      E, F, hF, hzero, hbounds, e, he⟩ := exists_uniform_strut_chart_of_dense_directions
    (m := 1) (n := 2) (by decide) (by decide)
    (p := (27 / 4 : ℝ)) (q := 7) (R := 1) (η := 1 / 100)
    (by norm_num) (by norm_num [Real.dist_eq]) (by norm_num)
    unitDirection path radius hr hrad direction_dense hang
    (fun _ => Directions) localDirection (fun _ _ => obstruction) actual_local_hinges
  have hformula (x : ball (7 : ℝ) ρ) :
      F x = E (PiLp.single 2 0 (if d 1 then 7 - x.val else x.val - 7)) := by
    rw [hF]
    congr 1
    ext i
    fin_cases i
    change dist x.val (path (d 1) s) - dist (7 : ℝ) (path (d 1) s) = _
    rw [hsa 1]
    change dist x.val (path (d 1) s) - s = if d 1 then 7 - x.val else x.val - 7
    have hx : |x.val - 7| < ρ := x.property
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hx
    cases d 1
    · simp only [path, Bool.false_eq_true, ite_false]
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      ring
    · simp only [path, ite_true]
      rw [Real.dist_eq, abs_of_neg (by linarith)]
      ring
  have hFiso : Isometry F := by
    apply Isometry.of_dist_eq
    intro x y
    rw [hformula x, hformula y, E.isometry.dist_eq, PiLp.dist_single_same]
    change |(if d 1 then 7 - x.val else x.val - 7) -
      (if d 1 then 7 - y.val else y.val - 7)| = |x.val - y.val|
    cases d 1
    · simp only [Bool.false_eq_true, ite_false]
      congr 1
      ring
    · simp only [ite_true]
      rw [show 7 - x.val - (7 - y.val) = y.val - x.val by ring, abs_sub_comm]
  refine ⟨d, s, ρ, hs, hsR, hsr, hsa, hρ, hρs, hρη, haR, hsubset,
    E, F, hzero, hformula, ?_, hFiso, e, he⟩
  simpa only [strutChartDistortion, Nat.cast_ofNat,
    show (8 * (2 : ℝ))⁻¹ = 1 / 16 by norm_num] using hbounds

end GCUniformStrutChartReview

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.strutChartDistortion
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_uniform_strut_chart_of_dense_directions
#print axioms GCSimplexShorteningReview.original_translated_opposite_paths_have_arbitrarily_small_struts
#print axioms GCUniformStrutChartReview.original_dense_paths_have_padded_uniform_chart
#lint- only unusedArguments simpNF synTaut
```
