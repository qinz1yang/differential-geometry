# AC53 independent proof review and actual oriented-plane integration

Seventeen public theorems and one explicit definition in six leaves add twenty
owned declarations including generated declarations. The 300-module gate checks
1369 owned declarations in3135 jobs. New transitive axiom closures contain only
propext, Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF
and synTaut lint is silent. The integration compiles silently apart from its
24 requested axiom reports (18 public declarations and6 concrete review results).
Declaration kinds were inspected; defLemma is unavailable. Earlier math leaves
are unchanged. The inherited AreaUpperBarrier warning remains outside these
closures. Blueprint static audit passes; no full migrated root, fresh blueprint
PDF/Overleaf build or human approval is claimed.

An independent agent source-checked KL4.5 and BBI10.5 with their retained errata,
then inspected every crossing-line, zero-factor and induction proof. It verified
all-real signed parameters, actual joint positive-arm germ limits, exact ordered
singleton coordinates, last-axis recursion, the actual zero factor, all factor
geometry, rank0 and universe preservation. A second agent implemented these
lemmas and produced a concrete orientation driver. Root inspected the proofs,
split them into natural public modules, proved the exact coordinate identity and
Busemann closure, and ran the combined acceptance gate/lint/integration.

The driver works in the ACTUAL Euclidean plane, at the nonzero basepoint(3,-2).
Its first line is gamma0(t)=(3,-2-t), pointing DOWN; its second is
gamma1(t)=(3+t,-2), pointing RIGHT. It proves the metric isometries, shared
basepoint and actual canonical germ angles. Global nonnegative comparison is
proved from Mathlib's vector-angle triangle inequality and norm cosine identity;
actual metric segments are supplied by affine line maps. No geometric existence
hypothesis is assumed merely to instantiate the conclusion.

The returned onto isometry sends these actual lines exactly to POSITIVE axes0
and1 in that order. The final coordinate theorem yields u0(x)=-x1-2 and
u1(x)=x0-3, and the positive-ray Busemann limits are respectively x1+2 and3-x0.
These exact formulas test translation, axis order and orientation together.
Further applications cover rank0 and rank1 with the reversed physical direction.
Negative controls prove coincident oriented lines have germ angle0 and reversed
lines anglepi, both different frompi/2. All review closures are standard.

The accepted result is full AC53, including exact axes and negative-Busemann
coordinates. It generalizes away the unnecessary finite-dimensionality premise;
properness still supplies completeness and the actual factor metric is retained.
Cross-pair orthogonality production from the original long endpoints remains
AC62-66 work, as does downstream compatibility. No migration interface changed.

```lean
import DifferentialGeometry.Geometry.Comparison.OrthogonalLineCoordinates
import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Normed.Affine.AddTorsor

set_option autoImplicit false
open Set Filter Topology

namespace GCAC53OrientationReview

open DifferentialGeometry.Geometry.Comparison.Toponogov
open InnerProductGeometry

private theorem comparison_eq_angle {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x y : V) : comparisonAngle ‖x‖ ‖y‖ ‖x - y‖ = angle x y := by
  rw [comparisonAngle, angle, norm_sub_pow_two_real]
  congr 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem inner_comparison {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    fourPointComparison 0 (univ : Set V) := by
  intro p hp a ha b hb c hc hap hbp hcp
  simp only [comparisonAngleNegCurvature_zero]
  have he (x y : V) : comparisonAngle (dist p x) (dist p y) (dist x y) = angle (x - p) (y - p) := by
    rw [dist_comm p x, dist_comm p y]
    simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using comparison_eq_angle (x - p) (y - p)
  rw [he a b, he b c, he c a]
  have ht := angle_le_angle_add_angle (a - p) (-(b - p)) (c - p)
  rw [angle_neg_right, angle_neg_left, angle_comm (a - p) (c - p)] at ht
  linarith

private theorem inner_segments {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x y : V) :
    ∃ f : Icc (0 : ℝ) 1 → V,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  refine ⟨fun t => AffineMap.lineMap x y (t : ℝ), by fun_prop, ?_, ?_, ?_⟩
  · exact AffineMap.lineMap_apply_zero x y
  · exact AffineMap.lineMap_apply_one x y
  · intro s t
    rw [dist_lineMap_lineMap]
    exact mul_comm _ _

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def p : Plane := WithLp.toLp 2 ![3, -2]
private def down (t : ℝ) : Plane := WithLp.toLp 2 ![3, -2 - t]
private def right (t : ℝ) : Plane := WithLp.toLp 2 ![3 + t, -2]
private def γ (j : Fin 2) : ℝ → Plane := ![down, right] j

private theorem plane_dist_sq (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs]

private theorem down_isometry : Isometry down := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [plane_dist_sq]
  simp only [down, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.dist_eq, sq_abs]
  ring

private theorem right_isometry : Isometry right := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [plane_dist_sq]
  simp only [right, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.dist_eq, sq_abs]
  ring

private theorem γ_isometry (j : Fin 2) : Isometry (γ j) := by
  fin_cases j
  · exact down_isometry
  · exact right_isometry

private theorem γ_base (j : Fin 2) : γ j 0 = p := by
  fin_cases j <;> simp [γ, down, right, p]

private theorem down_right_slope : lineCoordinate down (right 1) = 0 := by
  rw [lineCoordinate, plane_dist_sq, plane_dist_sq]
  norm_num [down, right]

private theorem down_right_angle : germComparisonAngle 0 down right = Real.pi / 2 := by
  rw [germComparisonAngle_crossing_isometries inner_comparison down_isometry right_isometry
    (by simp [down, right]), down_right_slope, Real.arccos_zero]

private theorem γ_angle (j l : Fin 2) (hjl : j ≠ l) :
    germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2 := by
  fin_cases j <;> fin_cases l
  · exact False.elim (hjl rfl)
  · exact down_right_angle
  · rw [germComparisonAngle_comm]
    exact down_right_angle
  · exact False.elim (hjl rfl)

private theorem oriented_plane : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧
      (∀ t, e (down t) = WithLp.toLp 2 (PiLp.single 2 0 t, z)) ∧
      (∀ t, e (right t) = WithLp.toLp 2 (PiLp.single 2 1 t, z)) ∧
      ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) := by
  obtain ⟨Z, m, z, e, hpoint, haxis, hproper, hcomplete, hcomp, hsegments⟩ :=
    exists_oriented_euclidean_splitting p inner_comparison inner_segments γ γ_isometry γ_base γ_angle
  exact ⟨Z, m, z, e, hpoint, (haxis 0), (haxis 1), hproper, hcomplete, hcomp⟩

example : p ≠ 0 := by
  intro h
  have hh := congrArg (fun x : Plane => x 0) h
  norm_num [p] at hh

example : down 1 = WithLp.toLp 2 ![3, -3] := by norm_num [down]
example : right 1 = WithLp.toLp 2 ![4, -2] := by norm_num [right]

private theorem zero_rank : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧ ProperSpace Z := by
  obtain ⟨Z, m, z, e, hpoint, haxis, hproper, hcomplete, hcomp, hsegments⟩ :=
    exists_oriented_euclidean_splitting p inner_comparison inner_segments
      (fun j : Fin 0 => Fin.elim0 j) (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
  exact ⟨Z, m, z, e, hpoint, hproper⟩

private theorem one_reversed_axis : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧
      (∀ t, e (down t) = WithLp.toLp 2 (PiLp.single 2 0 t, z)) ∧ ProperSpace Z := by
  obtain ⟨Z, m, z, e, hpoint, haxis, hproper, hcomplete, hcomp, hsegments⟩ :=
    exists_oriented_euclidean_splitting p inner_comparison inner_segments
      (fun _ : Fin 1 => down) (fun _ => down_isometry)
      (fun _ => by simp [down, p])
      (fun j l hjl => False.elim (hjl (Subsingleton.elim j l)))
  exact ⟨Z, m, z, e, hpoint, haxis 0, hproper⟩

private theorem coincident_angle : germComparisonAngle 0 down down = 0 := by
  rw [germComparisonAngle_crossing_isometries inner_comparison down_isometry down_isometry rfl,
    lineCoordinate_apply_isometry down_isometry, Real.arccos_one]

example : germComparisonAngle 0 down down ≠ Real.pi / 2 := by
  rw [coincident_angle]
  linarith [Real.pi_pos]

private theorem reversed_isometry : Isometry (fun t : ℝ => down (-t)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [down_isometry.dist_eq]
  exact dist_neg_neg s t

private theorem reversed_angle : germComparisonAngle 0 down (fun t => down (-t)) = Real.pi := by
  rw [germComparisonAngle_crossing_isometries inner_comparison down_isometry reversed_isometry
    (by simp), lineCoordinate_apply_isometry down_isometry, Real.arccos_neg_one]

example : germComparisonAngle 0 down (fun t => down (-t)) ≠ Real.pi / 2 := by
  rw [reversed_angle]
  linarith [Real.pi_pos]

private theorem down_coordinate (x : Plane) : lineCoordinate down x = -x 1 - 2 := by
  rw [lineCoordinate, plane_dist_sq, plane_dist_sq]
  simp only [down, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem right_coordinate (x : Plane) : lineCoordinate right x = x 0 - 3 := by
  rw [lineCoordinate, plane_dist_sq, plane_dist_sq]
  simp only [right, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem oriented_plane_coordinates : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧
      (∀ t, e (down t) = WithLp.toLp 2 (PiLp.single 2 0 t, z)) ∧
      (∀ t, e (right t) = WithLp.toLp 2 (PiLp.single 2 1 t, z)) ∧
      (∀ x, (e x).fst 0 = -x 1 - 2 ∧ (e x).fst 1 = x 0 - 3) ∧
      (∀ x, Tendsto (fun T : ℝ => dist x (down T) - T) atTop (𝓝 (x 1 + 2))) ∧
      (∀ x, Tendsto (fun T : ℝ => dist x (right T) - T) atTop (𝓝 (3 - x 0))) := by
  obtain ⟨Z, m, z, e, hp, haxis, hcoord, hbus, hproper, hcomplete, hcomp, hsegments⟩ :=
    exists_oriented_euclidean_coordinates p inner_comparison inner_segments γ γ_isometry γ_base γ_angle
  let := m
  have hdown (x : Plane) : (e x).fst 0 = -x 1 - 2 := (hcoord 0 x).symm.trans (down_coordinate x)
  have hright (x : Plane) : (e x).fst 1 = x 0 - 3 := (hcoord 1 x).symm.trans (right_coordinate x)
  refine ⟨Z, m, z, e, hp, haxis 0, haxis 1, fun x => ⟨hdown x, hright x⟩, ?_, ?_⟩
  · intro x
    have hb := hbus 0 x
    rw [hdown, neg_sub, sub_neg_eq_add] at hb
    simpa [γ, add_comm] using hb
  · intro x
    have hb := hbus 1 x
    rw [hright, neg_sub] at hb
    simpa [γ] using hb

#print axioms oriented_plane
#print axioms zero_rank
#print axioms one_reversed_axis
#print axioms coincident_angle
#print axioms reversed_angle
#print axioms oriented_plane_coordinates

end GCAC53OrientationReview

#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_crossing_isometries_reciprocity
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_crossing_isometry
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.sq_dist_crossing_isometries
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.comparisonAngle_crossing_isometries
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.germComparisonAngle_crossing_isometries
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_crossing_isometry_eq_zero_of_right_angle
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.orthogonalLineInFactor
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.isometry_orthogonalLineInFactor
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.orthogonalLineInFactor_zero
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.germComparisonAngle_orthogonalLineInFactor
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineSplitting_apply_of_lineCoordinate_eq_zero
#print axioms EuclideanSpace.finSuccProdIsometry_fst_apply
#print axioms EuclideanSpace.finSuccProdIsometry_snd
#print axioms EuclideanSpace.finSuccProdIsometry_symm_single_castSucc
#print axioms EuclideanSpace.finSuccProdIsometry_symm_single_last
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_oriented_euclidean_splitting
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.lineCoordinate_eq_euclidean_coordinate_of_aligned_isometry
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_oriented_euclidean_coordinates
```
