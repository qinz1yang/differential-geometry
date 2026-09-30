# Full conditional AC11 independent acceptance

Ten public theorems, one definition and one private algebra helper in four leaves add14 owned declarations, including two generated declarations. The368-module gate checks1720 declarations in3203 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import regression lint is silent;20 reports cover all11 public production declarations and nine concrete regressions. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. The separate blueprint static audit passes. No migrated-root/PDF/Overleaf build or human approval is claimed.

Root independently read all simplex/shortening proofs and every regression. Independent peers checked vertex continuity, exact common-scale selection and the full same-anchor assembly. Production formatting normalizes whitespace from the frozen candidate; receipt hashes identify the exact accepted source. Source/label universes remain independent. No claim of a universe defect in Lean's grouped Type* syntax is made.

Tests include the exact rank-one antipodal anglepi, rank-two norm and off-diagonal inner product, actual realization in Eucl2, dimension-three angular margin, and the zero-dimension guard. The full original-input regression uses sourceR, apex7, ORIGINAL paths7+s and7-s, available radii2 and3, actual Eucl1 unit-direction density proved exhaustively, and actual curvature-minus-one angle limits0/pi. The theorem selects original labels and ONE unknown common s<1/100; no strut is assumed. The full neighborhood regression retains these SAME original selected paths/endpoints and s for EVERY subsequent positive cap, returning every strict radius, distance and angle condition. A separate actual rank-one -1/+1 fixture proves the comparison angle is EXACTLYpi at every point of the returned neighborhood, testing continuity at collinear configurations and arbitrary cap handling.

The four layers have exact8theta,6theta,5theta,4theta margins. The nearby-distance conclusion is strict>s/2, withrho<s/8. The final cap is quantified after the original scale, permitting dependence on it without replacing anchors. Source regular tangent, direction completion, density and angle-limit production remain explicit inputs. The local angular obstruction and original8R comparison producer are not supplied by this milestone. The result is the full conditional AC11 metric construction, not completion of the alternate tangent-based route or of Chapters3–4. Blueprint207 and migration interfaces remain unchanged.

```lean
import DifferentialGeometry.Geometry.Comparison.SimplexStrutNeighborhood
import Mathlib.Tactic

set_option autoImplicit false

namespace GCRegularSimplexReview
open scoped RealInnerProductSpace

theorem rank_one_antipodal_angle : InnerProductGeometry.angle (EuclideanSpace.regularSimplexVector 1 0)
    (EuclideanSpace.regularSimplexVector 1 1) = Real.pi := by
  rw [EuclideanSpace.angle_regularSimplexVector (by decide) (by decide)]
  norm_num

theorem rank_two_off_diagonal_inner : ⟪EuclideanSpace.regularSimplexVector 2 0,
    EuclideanSpace.regularSimplexVector 2 2⟫ = -(1 / 2 : ℝ) := by
  rw [EuclideanSpace.inner_regularSimplexVector (by decide)]
  norm_num

theorem rank_two_unit_norm : ‖EuclideanSpace.regularSimplexVector 2 1‖ = 1 :=
  EuclideanSpace.norm_regularSimplexVector (by decide) _

theorem rank_zero_guard : EuclideanSpace.regularSimplexVector 0 0 = 0 := by
  simp [EuclideanSpace.regularSimplexVector]

theorem rank_two_exact_model : ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 2),
    (∀ i, ‖v i‖ = 1) ∧
    (∀ i j, ⟪v i, v j⟫ = if i = j then 1 else -(1 / 2 : ℝ)) ∧
    (∀ i j, i ≠ j → InnerProductGeometry.angle (v i) (v j) =
      Real.pi / 2 + Real.arcsin (1 / 2)) := by
  simpa using EuclideanSpace.exists_regularSimplex (m := 2) (by decide)

theorem dimension_three_margin : Real.pi / 2 + 1 / 3 ≤
    InnerProductGeometry.angle (EuclideanSpace.regularSimplexVector 2 0)
      (EuclideanSpace.regularSimplexVector 2 1) := by
  have hh := EuclideanSpace.regularSimplex_angle_margin (m := 2) (n := 3)
    (by decide) (by decide) (i := 0) (j := 1) (by decide)
  norm_num at hh ⊢
  exact hh

end GCRegularSimplexReview

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


namespace GCSimplexShorteningReview
open DifferentialGeometry.Geometry.Comparison.Toponogov

theorem original_translated_paths_have_same_anchor_neighborhoods :
    ∃ (d : Fin 2 → Bool) (s : ℝ), 0 < s ∧ s < 1/100 ∧
      (∀ i, s ≤ radius (d i)) ∧ (∀ i, dist 7 (path (d i) s) = s) ∧
      (∀ i j, i ≠ j → Real.pi/2 + 5 * (8 * (1 : ℝ))⁻¹ <
        comparisonAngleNegCurvature 1 (dist 7 (path (d i) s)) (dist 7 (path (d j) s))
          (dist (path (d i) s) (path (d j) s))) ∧
      ∀ cap : ℝ, 0 < cap → ∃ ρ : ℝ, 0 < ρ ∧ ρ < s/8 ∧ ρ < cap ∧
        (∀ x ∈ Metric.ball 7 ρ, ∀ i, s/2 < dist x (path (d i) s)) ∧
        ∀ x ∈ Metric.ball 7 ρ, ∀ i j, i ≠ j → Real.pi/2 + 4 * (8 * (1 : ℝ))⁻¹ <
          comparisonAngleNegCurvature 1 (dist x (path (d i) s)) (dist x (path (d j) s))
            (dist (path (d i) s) (path (d j) s)) := by
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
    exists_common_shortening_strut_neighborhood (m := 1) (n := 1)
      (by decide) (by decide) (7 : ℝ) unitDirection path radius hr hrad direction_dense hang
      (S := 1/100) (by norm_num)

end GCSimplexShorteningReview

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GCStrutVertexReview

private def anchors (i : Fin 2) : ℝ := if i = 0 then -1 else 1

private theorem anchor_radius (i : Fin 2) : dist (0 : ℝ) (anchors i) = 1 := by
  fin_cases i <;> norm_num [anchors, Real.dist_eq]

private theorem anchor_separation (i j : Fin 2) (hij : i ≠ j) : dist (anchors i) (anchors j) = 2 := by
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals norm_num [anchors, Real.dist_eq]

private theorem exact_collinear_angle {x : ℝ} (hx : |x| < 1) (i j : Fin 2) (hij : i ≠ j) :
    comparisonAngleNegCurvature 1 (dist x (anchors i)) (dist x (anchors j))
      (dist (anchors i) (anchors j)) = Real.pi := by
  have hb := abs_lt.mp hx
  have hminus : dist x (-1) = x + 1 := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]
    ring
  have hplus : dist x 1 = 1 - x := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    ring
  have ha (k : Fin 2) : 0 < dist x (anchors k) := by
    fin_cases k
    · simpa [anchors] using (show 0 < dist x (-1) by rw [hminus]; linarith)
    · simpa [anchors] using (show 0 < dist x 1 by rw [hplus]; linarith)
  have he : dist (anchors i) (anchors j) = dist x (anchors i) + dist x (anchors j) := by
    rw [anchor_separation i j hij]
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    all_goals norm_num [anchors]
    all_goals rw [hminus, hplus]; ring
  rw [he]
  exact comparisonAngleNegCurvature_add (by norm_num) (ha i) (ha j)

theorem actual_collinear_strut_vertex_stability {cap : ℝ} (hcap : 0 < cap) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 8 ∧ ρ < cap ∧
      (∀ x ∈ ball (0 : ℝ) ρ, ∀ i, (1 / 2 : ℝ) < dist x (anchors i)) ∧
      (∀ x ∈ ball (0 : ℝ) ρ, ∀ i j, i ≠ j → Real.pi / 2 + 4 * (1 / 8 : ℝ) <
        comparisonAngleNegCurvature 1 (dist x (anchors i)) (dist x (anchors j))
          (dist (anchors i) (anchors j))) ∧
      ∀ x ∈ ball (0 : ℝ) ρ, ∀ i j, i ≠ j →
        comparisonAngleNegCurvature 1 (dist x (anchors i)) (dist x (anchors j))
          (dist (anchors i) (anchors j)) = Real.pi := by
  have hangle (i j : Fin 2) (hij : i ≠ j) : Real.pi / 2 + 5 * (1 / 8 : ℝ) <
      comparisonAngleNegCurvature 1 (dist (0 : ℝ) (anchors i)) (dist (0 : ℝ) (anchors j))
        (dist (anchors i) (anchors j)) := by
    rw [exact_collinear_angle (by norm_num) i j hij]
    have hpi := Real.sin_le (show 0 ≤ Real.pi / 2 by positivity)
    rw [Real.sin_pi_div_two] at hpi
    linarith
  obtain ⟨ρ, hρ, hρs, hρcap, hdist, hangle'⟩ := exists_ball_strut_margin
    (s := 1) (θ := 1 / 8) (by norm_num) (by norm_num) hcap anchors anchor_radius hangle
  refine ⟨ρ, hρ, hρs, hρcap, hdist, hangle', ?_⟩
  intro x hx i j hij
  apply exact_collinear_angle _ i j hij
  have hx' : |x| < ρ := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hx
  linarith

end GCStrutVertexReview

#print axioms EuclideanSpace.regularSimplexVector
#print axioms EuclideanSpace.inner_regularSimplexVector
#print axioms EuclideanSpace.norm_regularSimplexVector
#print axioms EuclideanSpace.sum_regularSimplexVector_coord
#print axioms EuclideanSpace.angle_regularSimplexVector
#print axioms EuclideanSpace.regularSimplex_angle_margin
#print axioms EuclideanSpace.exists_regularSimplex
#print axioms EuclideanSpace.regularSimplex_perturbed_angle_margin
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_common_shortening_strut_of_dense_directions
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_ball_strut_margin
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_common_shortening_strut_neighborhood
#print axioms GCRegularSimplexReview.rank_one_antipodal_angle
#print axioms GCRegularSimplexReview.rank_two_off_diagonal_inner
#print axioms GCRegularSimplexReview.rank_two_unit_norm
#print axioms GCRegularSimplexReview.rank_zero_guard
#print axioms GCRegularSimplexReview.rank_two_exact_model
#print axioms GCRegularSimplexReview.dimension_three_margin
#print axioms GCSimplexShorteningReview.original_translated_opposite_paths_have_arbitrarily_small_struts
#print axioms GCSimplexShorteningReview.original_translated_paths_have_same_anchor_neighborhoods
#print axioms GCStrutVertexReview.actual_collinear_strut_vertex_stability
#lint- only unusedArguments simpNF synTaut
```
