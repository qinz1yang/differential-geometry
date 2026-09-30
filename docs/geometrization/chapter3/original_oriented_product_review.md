# Full AC66/AC54 independent review and same-product integration

Two public theorems in two leaves add two owned declarations. The318-module
gate checks1402 declarations in3153 jobs. All transitive closures contain only
propext, Classical.choice and Quot.sound. Source-copy unusedArguments/simpNF/
synTaut lint is silent. The accepted-import review compiles silently apart from
seven requested standard axiom reports, including both public theorems.
Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside these
closures. Static audit passes. No full migrated root, new PDF/Overleaf build,
or human approval is claimed.

Root implemented the generic calibrated orthogonal-coordinate consumer. One agent
implemented the original-input wrapper. A different agent independently inspected
both proofs and constructed both concrete review drivers, reusing the previously
independently proved original real-line setup. Root reread the wrapper and both
drivers. The shared product e is the SAME map across axis alignment, scalar
coordinate identification, actual positive-ray Busemann limits and all source
coordinate estimates. Each auxiliary scalar lineSplitting is used only for AC60;
its first coordinate is the same lineCoordinate identified by the common e.
No Q, gamma, f or subsequence is selected again. Radius control in the Fin0 case
comes independently from R->infinity. The original wrapper retains ALL AC65
witnesses/geometry before adding e; actual E>=0 follows from the triangle inequality,
its limit is composed with the same psi, and eta=0 uses precisely the original
positive-lower and negative-upper calibration fields. The factor stays in the
target universe independently of the source universe.

The generic consumer's concrete two-axis test uses the Euclidean plane based
at(3,-2), axis0 pointing DOWN and axis1 RIGHT, with lengths i+1 and2(i+1).
Actual signed prefixes lie on these lines, all calibration errors are zero,
and the actual approximation maps are identities on growing balls. The test
retains the SAME returned e and proves its ordered coordinates are exactly
-x_1-2 and x_0-3. The positive-ray Busemann limits have the opposite signs.
It preserves simultaneous all-fixed-source-ball estimates for the ORIGINAL
endpoint-distance coordinates, exact ordered axis alignment and factor geometry.
A separate Fin0 application checks growing approximation radii despite vacuous
axis conditions. This generic test has no long negative-curvature strainer
premise; the separate AC65 negative control excludes that false instantiation.

The ORIGINAL geometric wrapper is independently applied to actual complete real
sources with sigma_i=1/(i+1), endpoints +(i+1) and-(i+1), proved local comparison,
ambientdim<=1, short affine curves and constant pointed convergence. Fin1 and
Fin0 tests retain its ENTIRE public output including original qPlus/qMinus,
psi/f/Q/gamma, all calibrations, the same product and coordinate/Busemann data.
A strengthened rank1 result uses this SAME returned psi/f/gamma/e. Once the
original endpoint radius exceeds S, its actual distance coordinate is exactly x
on the original S-ball. It therefore proves uniform |x-(e(f_i x)).fst0|->0,
while retaining positive-axis alignment, lineCoordinate equality, negative-
Busemann sign and factor geometry. The approximation maps are not assumed to
be identities in this original-input test.

Full AC66 and AC54 are complete through the accepted original-input AC65 and
oriented splitting/calibration proofs. AC55's uniform parameter, reverse
strainers and compatibility remain. Chapters3-4 are unfinished; blueprint207
and migration interfaces are unchanged.

```lean
import Mathlib.Tactic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.Normed.Affine.AddTorsor
import DifferentialGeometry.Geometry.Comparison.OrthogonalLineCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCoordinateConvergence
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import DifferentialGeometry.Topology.MetricSpace.BoundaryRadialSegment
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Geometry.Metric.Approximation.PointedConvergence
import DifferentialGeometry.Topology.MetricSpace.SignedPrefix
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixLineLimit
import DifferentialGeometry.Geometry.Comparison.BufferedAngleShortening
import DifferentialGeometry.Geometry.Comparison.OppositeCrossAngles
import DifferentialGeometry.Analysis.Asymptotics.ReciprocalShortening
import DifferentialGeometry.Geometry.Metric.Approximation.PointedBallApproximation
import DifferentialGeometry.Geometry.Comparison.ModelAngle
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import DifferentialGeometry.Geometry.Metric.Approximation.CalibratedOrthogonalCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalOrientedProduct

open Set Filter Metric
open scoped Topology

open Set Filter Metric
open scoped Topology

namespace GCCalibratedOrthogonalCoordinatesReview

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

private theorem down_coordinate (x : Plane) : lineCoordinate down x = -x 1 - 2 := by
  rw [lineCoordinate, plane_dist_sq, plane_dist_sq]
  simp only [down, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem right_coordinate (x : Plane) : lineCoordinate right x = x 0 - 3 := by
  rw [lineCoordinate, plane_dist_sq, plane_dist_sq]
  simp only [right, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

open GC.MetricGeometry

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by
  dsimp [radius]
  linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
private def lengths (i : ℕ) (j : Fin 2) : ℝ := ((j.val : ℝ) + 1) * radius i
private theorem lengths_ge (i : ℕ) (j : Fin 2) : radius i ≤ lengths i j := by
  dsimp [lengths]
  nlinarith [Nat.cast_nonneg (α := ℝ) j.val, radius_pos i]
private theorem lengths_pos (i : ℕ) (j : Fin 2) : 0 < lengths i j :=
  lt_of_lt_of_le (radius_pos i) (lengths_ge i j)
private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 100
private theorem errors_pos (i : ℕ) : 0 < errors i := by dsimp [errors]; positivity
private theorem errors_lt (i : ℕ) : errors i < radius i := by
  have hdiv : (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  dsimp [errors]
  linarith [radius_one i]
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.div_const (100 : ℝ)
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 100) atTop (𝓝 0)
  simpa only [zero_div] using h
private def approx (i : ℕ) : PointedBallApprox p p (radius i) (errors i) where
  error_pos := errors_pos i
  error_lt_radius := errors_lt i
  toFun := Subtype.val
  basepoint := rfl
  distortion x y := by simpa only [sub_self, abs_zero] using errors_pos i
  coverage y hy := ⟨⟨y, by linarith [errors_pos i]⟩, by simpa only [dist_self] using errors_pos i⟩
private def endpoint (i : ℕ) (j : Fin 2) : Plane := γ j (lengths i j)
private def signedPrefix (i : ℕ) (j : Fin 2) : Icc (-(lengths i j)) (lengths i j) → Plane :=
  fun t => γ j t.val
private theorem endpoint_length (i : ℕ) (j : Fin 2) : dist p (endpoint i j) = lengths i j := by
  rw [endpoint, ← γ_base j, (γ_isometry j).dist_eq, Real.dist_eq, zero_sub, abs_neg,
    abs_of_pos (lengths_pos i j)]
private theorem signedPrefix_lipschitz (i : ℕ) (j : Fin 2) : LipschitzWith 1 (signedPrefix i j) :=
  ((γ_isometry j).comp isometry_subtype_coe).lipschitzWith
private theorem signedPrefix_base (i : ℕ) (j : Fin 2) :
    signedPrefix i j ⟨0, ⟨by linarith [lengths_pos i j], (lengths_pos i j).le⟩⟩ = p := γ_base j
private theorem signedPrefix_calibration (i : ℕ) (j : Fin 2) (t : Icc (0 : ℝ) (lengths i j)) :
    t.val - 0 ≤ lengths i j - dist
      (signedPrefix i j ⟨t.val, ⟨by linarith [t.property.1, lengths_pos i j], t.property.2⟩⟩) (endpoint i j) ∧
    lengths i j - dist
      (signedPrefix i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, lengths_pos i j]⟩⟩)
      (endpoint i j) ≤ -t.val + 0 + 0 := by
  dsimp [signedPrefix, endpoint]
  rw [(γ_isometry j).dist_eq, (γ_isometry j).dist_eq, Real.dist_eq, Real.dist_eq,
    abs_of_nonpos (by linarith [t.property.2] : t.val - lengths i j ≤ 0),
    abs_of_nonpos (by linarith [t.property.1, lengths_pos i j] : -t.val - lengths i j ≤ 0)]
  constructor <;> linarith
private theorem signedPrefix_convergence : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
    S ≤ radius i ∧ ∀ j, S ≤ lengths i j ∧
    ∀ t : Icc (-(lengths i j)) (lengths i j), |t.val| ≤ S →
      ∀ ht : dist (signedPrefix i j t) p ≤ radius i,
        dist ((approx i).toFun ⟨signedPrefix i j t, ht⟩) (γ j t.val) < ζ := by
  intro S ζ hζ
  filter_upwards [radius_top.eventually_ge_atTop S] with i hi
  refine ⟨hi, fun j => ⟨hi.trans (lengths_ge i j), ?_⟩⟩
  intro t ht htr
  simpa only [approx, signedPrefix, dist_self] using hζ

private theorem two_axis_calibrated_product : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧
      (∀ t, e (down t) = WithLp.toLp 2 (PiLp.single 2 0 t, z)) ∧
      (∀ t, e (right t) = WithLp.toLp 2 (PiLp.single 2 1 t, z)) ∧
      (∀ x, (e x).fst 0 = -x 1 - 2 ∧ (e x).fst 1 = x 0 - 3) ∧
      (∀ x, Tendsto (fun T : ℝ => dist x (down T) - T) atTop (𝓝 (x 1 + 2))) ∧
      (∀ x, Tendsto (fun T : ℝ => dist x (right T) - T) atTop (𝓝 (3 - x 0))) ∧
      (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
        S ≤ radius i ∧ ∀ x : Plane, dist x p ≤ S →
          |lengths i 0 - dist x (down (lengths i 0)) - (e x).fst 0| < ζ ∧
          |lengths i 1 - dist x (right (lengths i 1)) - (e x).fst 1| < ζ) ∧
      ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
      (∀ a b : Z, ∃ g : Icc (0 : ℝ) 1 → Z,
        Continuous g ∧ g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (g s) (g t) = dist a b * dist s t) := by
  obtain ⟨Z, m, z, e, hp, haxis, hcoord, hbus, hconv, hproper, hcomplete, hcomp, hseg⟩ :=
    exists_oriented_product_with_converging_distance_coordinates
      (A := fun _ => Plane) inner_comparison inner_segments γ γ_isometry γ_base γ_angle
      approx radius_top errors_zero endpoint endpoint_length (fun i j => (lengths_pos i j).le)
      (E := fun _ _ => 0) (η := fun _ => 0) (fun _ _ => le_rfl)
      (fun _ => tendsto_const_nhds) tendsto_const_nhds
      signedPrefix signedPrefix_lipschitz signedPrefix_base signedPrefix_calibration signedPrefix_convergence
  let := m
  have hdown (x : Plane) : (e x).fst 0 = -x 1 - 2 := (hcoord 0 x).symm.trans (down_coordinate x)
  have hright (x : Plane) : (e x).fst 1 = x 0 - 3 := (hcoord 1 x).symm.trans (right_coordinate x)
  refine ⟨Z, m, z, e, hp, haxis 0, haxis 1, fun x => ⟨hdown x, hright x⟩,
    ?_, ?_, ?_, hproper, hcomplete, hcomp, hseg⟩
  · intro x
    have hb := hbus 0 x
    rw [hdown, neg_sub, sub_neg_eq_add] at hb
    simpa [γ, add_comm] using hb
  · intro x
    have hb := hbus 1 x
    rw [hright, neg_sub] at hb
    simpa [γ] using hb
  · intro S hS ζ hζ
    filter_upwards [hconv S hS ζ hζ] with i hi
    refine ⟨hi.1, ?_⟩
    intro x hx
    let xx : BallCarrier p (radius i) := ⟨x, hx.trans hi.1⟩
    have hd := hi.2 0 xx hx
    have hr := hi.2 1 xx hx
    rw [endpoint_length] at hd hr
    simpa only [approx, xx, endpoint, γ, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using And.intro hd hr

private theorem zero_axis_calibrated_product : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Z)),
      e p = WithLp.toLp 2 (0, z) ∧ ProperSpace Z ∧
      (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
        S ≤ radius i ∧ ∀ j : Fin 0, ∀ x : Plane, dist x p ≤ S →
          |dist p (Fin.elim0 j : Plane) - dist x (Fin.elim0 j : Plane) - (e x).fst j| < ζ) := by
  have hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ radius i ∧ ∀ j : Fin 0, S ≤ (Fin.elim0 j : ℝ) ∧
      ∀ t : Icc (-(Fin.elim0 j : ℝ)) (Fin.elim0 j : ℝ), |t.val| ≤ S →
        ∀ ht : dist (Fin.elim0 j : Plane) p ≤ radius i,
          dist ((approx i).toFun ⟨Fin.elim0 j, ht⟩) (Fin.elim0 j : Plane) < ζ := by
    intro S ζ hζ
    exact (radius_top.eventually_ge_atTop S).mono fun _ hi => ⟨hi, fun j => Fin.elim0 j⟩
  obtain ⟨Z, m, z, e, hp, haxis, hcoord, hbus, hcon, hproper, hcomplete, hcomp, hseg⟩ :=
    exists_oriented_product_with_converging_distance_coordinates
      (A := fun _ => Plane) (k := 0) inner_comparison inner_segments
      (fun (j : Fin 0) (_ : ℝ) => Fin.elim0 j) (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
      (fun j => Fin.elim0 j) approx radius_top errors_zero
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (L := fun _ j => Fin.elim0 j) (E := fun _ j => Fin.elim0 j) (η := fun _ => 0)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j) (fun j => Fin.elim0 j)
      tendsto_const_nhds (fun _ j _ => Fin.elim0 j) (fun _ j => Fin.elim0 j)
      (fun _ j => Fin.elim0 j) (fun _ j => Fin.elim0 j) hconv
  let := m
  refine ⟨Z, m, z, e, hp, hproper, ?_⟩
  intro S hS ζ hζ
  exact (hcon S hS ζ hζ).mono fun i hi => ⟨hi.1, fun j => Fin.elim0 j⟩

#print axioms two_axis_calibrated_product
#print axioms zero_axis_calibrated_product

end GCCalibratedOrthogonalCoordinatesReview

open Set Filter Metric
open scoped Topology

namespace GCOriginalOrientedProductReview

open DifferentialGeometry.Geometry.Comparison.Toponogov GC.MetricGeometry

private def radius (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem radius_one (i : ℕ) : 1 ≤ radius i := by dsimp [radius]; linarith [Nat.cast_nonneg (α := ℝ) i]
private theorem radius_pos (i : ℕ) : 0 < radius i := lt_of_lt_of_le (by norm_num) (radius_one i)
private theorem radius_top : Tendsto radius atTop atTop :=
  tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
private theorem same_side_zero {κ : ℝ} (hκ : 0 ≤ κ) (x a b : ℝ) (ha : a ≠ x) (hb : b ≠ x)
    (hs : (x ≤ a ∧ x ≤ b) ∨ (a ≤ x ∧ b ≤ x)) :
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) = 0 := by
  have heq : dist a b = |dist x a - dist x b| := by
    rcases hs with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonpos (sub_nonpos.mpr ha'), abs_of_nonpos (sub_nonpos.mpr hb')]
      have h : -(x - a) - -(x - b) = a - b := by ring
      rw [h]
    · rw [Real.dist_eq a b, Real.dist_eq x a, Real.dist_eq x b,
        abs_of_nonneg (sub_nonneg.mpr ha'), abs_of_nonneg (sub_nonneg.mpr hb')]
      have h : (x - a) - (x - b) = b - a := by ring
      rw [h, abs_sub_comm]
  rw [heq]
  exact comparisonAngleNegCurvature_abs_sub hκ (dist_pos.mpr ha.symm) (dist_pos.mpr hb.symm)

private theorem real_comparison {κ : ℝ} (hκ : 0 ≤ κ) : fourPointComparison κ (univ : Set ℝ) := by
  intro x _ a _ b _ c _ ha hb hc
  have hab := (comparisonAngleNegCurvature_mem_Icc κ (dist x a) (dist x b) (dist a b)).2
  have hbc := (comparisonAngleNegCurvature_mem_Icc κ (dist x b) (dist x c) (dist b c)).2
  have hca := (comparisonAngleNegCurvature_mem_Icc κ (dist x c) (dist x a) (dist c a)).2
  rcases le_total x a with hxa | hax <;> rcases le_total x b with hxb | hbx <;>
    rcases le_total x c with hxc | hcx
  all_goals first
    | have hz := same_side_zero hκ x a b ha hb (Or.inl ⟨hxa, hxb⟩); linarith
    | have hz := same_side_zero hκ x a b ha hb (Or.inr ⟨hax, hbx⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inl ⟨hxb, hxc⟩); linarith
    | have hz := same_side_zero hκ x b c hb hc (Or.inr ⟨hbx, hcx⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inl ⟨hxc, hxa⟩); linarith
    | have hz := same_side_zero hκ x c a hc ha (Or.inr ⟨hcx, hax⟩); linarith


private theorem real_segments (x y : ℝ) :
    ∃ f : unitInterval → ℝ, Continuous f ∧ f 0 = x ∧ f 1 = y ∧
      ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let f : unitInterval → ℝ := fun t => (1 - (t : ℝ)) * x + (t : ℝ) * y
  refine ⟨f, by fun_prop, by simp [f], by simp [f], ?_⟩
  intro s t
  change |(1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y)| =
    |x - y| * |(s : ℝ) - t|
  rw [show (1 - (s : ℝ)) * x + (s : ℝ) * y - ((1 - (t : ℝ)) * x + (t : ℝ) * y) =
    (y - x) * ((s : ℝ) - t) by ring, abs_mul, abs_sub_comm y x]

private noncomputable def sig (i : ℕ) : ℝ := 1 / radius i
private theorem sig_pos (i : ℕ) : 0 < sig i := div_pos (by norm_num) (radius_pos i)
private theorem sig_zero : Tendsto sig atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
private theorem sig_inv (i : ℕ) : (sig i)⁻¹ = radius i := by simp [sig]

private def RealProductData (k : ℕ) : Prop :=
    fourPointComparison 0 (univ : Set ℝ) ∧
    (∀ a b : ℝ, ∃ c : Icc (0 : ℝ) 1 → ℝ,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    (∀ j : Fin k, Tendsto (fun i => 2 * (sig i)⁻¹ - dist (radius i) ((-radius i))) atTop (𝓝 0)) ∧
    ∃ qPlus qMinus : ∀ i, Fin k → Icc (0 : ℝ) ((sig i)⁻¹) → ℝ,
      (∀ i j, Isometry (qPlus i j)) ∧ (∀ i j, Isometry (qMinus i j)) ∧
      (∀ i j, qPlus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (sig_pos i)).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, qMinus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (sig_pos i)).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, qPlus i j ⟨(sig i)⁻¹, ⟨(inv_pos.mpr (sig_pos i)).le, le_rfl⟩⟩ = radius i) ∧
      (∀ i j, qMinus i j ⟨(sig i)⁻¹, ⟨(inv_pos.mpr (sig_pos i)).le, le_rfl⟩⟩ = (-radius i)) ∧
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => (0 : ℝ)) (0 : ℝ) ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox ((0 : ℝ)) (0 : ℝ) (R i) (ε i),
      ∃ Q : ∀ i, Fin k → Icc (-((sig (ψ i))⁻¹)) ((sig (ψ i))⁻¹) → ℝ,
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [inv_pos.mpr (sig_pos (ψ i))],
        (inv_pos.mpr (sig_pos (ψ i))).le⟩⟩ = (0 : ℝ)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((sig (ψ i))⁻¹),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩ = qPlus (ψ i) j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2],
          by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩ = qMinus (ψ i) j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((sig (ψ i))⁻¹),
        t.val ≤ (sig (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩) (radius (ψ i)) ∧
        (sig (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))], t.property.2⟩⟩) (radius (ψ i)) ≤ t.val ∧
        -t.val ≤ (sig (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩) (radius (ψ i)) ∧
        (sig (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (sig_pos (ψ i))]⟩⟩) (radius (ψ i)) ≤
          -t.val + (2 * (sig (ψ i))⁻¹ - dist (radius (ψ i)) ((-radius (ψ i))))) ∧
      ∃ γ : Fin k → ℝ → ℝ,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = (0 : ℝ)) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (sig (ψ i))⁻¹ ∧
          ∀ t : Icc (-((sig (ψ i))⁻¹)) ((sig (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (Q i j t) ((0 : ℝ)) ≤ R i,
              dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) ∧
        (∀ j l, j ≠ l → germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2) ∧
        ∃ (Z : Type) (m : MetricSpace Z), letI := m
          ∃ (z : Z) (e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)),
            e (0 : ℝ) = WithLp.toLp 2 (0, z) ∧
            (∀ j t, e (γ j t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) ∧
            (∀ j x, lineCoordinate (γ j) x = (e x).fst j) ∧
            (∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-(e x).fst j))) ∧
            (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
              S ≤ R i ∧ ∀ j, ∀ x : BallCarrier ((0 : ℝ)) (R i), dist x.val ((0 : ℝ)) ≤ S →
                |dist ((0 : ℝ)) (radius (ψ i)) - dist x.val (radius (ψ i)) -
                  (e ((f i).toFun x)).fst j| < ζ) ∧
            ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
            (∀ a b : Z, ∃ g : Icc (0 : ℝ) 1 → Z,
              Continuous g ∧ g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (g s) (g t) = dist a b * dist s t)

private theorem real_product_family (k : ℕ) [Subsingleton (Fin k)] : RealProductData k := by
  exact (PointedGHConverges.const (0 : ℝ)).exists_oriented_product_of_reciprocal_local_geometry
    (n := 1) (fun _ => arbitrarily_short_curves_of_metric_segments real_segments)
    (fun i => by simpa only [Nat.cast_one] using
      (dimH_mono (subset_univ (ball (0 : ℝ) ((sig i)⁻¹)))).trans_eq Real.dimH_univ)
    (fun i z _ => ⟨univ, isOpen_univ, real_comparison (sig_pos i).le, mem_univ z⟩)
    (fun i (_ : Fin k) => radius i) (fun i _ => -radius i) sig_pos sig_zero
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos i)])
    (fun i _ => by rw [sig_inv, Real.dist_eq, zero_sub, neg_neg, abs_of_pos (radius_pos i)]) (by
      intro j
      exact Eventually.of_forall fun i => by
        have hh := comparisonAngleNegCurvature_add (sig_pos i).le (radius_pos i) (radius_pos i)
        rw [Real.dist_eq (0 : ℝ) (radius i), Real.dist_eq (0 : ℝ) (-radius i),
          Real.dist_eq (radius i) (-radius i), zero_sub, abs_neg, abs_of_pos (radius_pos i),
          zero_sub, neg_neg, abs_of_pos (radius_pos i), sub_neg_eq_add,
          abs_of_pos (show 0 < radius i + radius i by linarith [radius_pos i]), hh]
        linarith [sig_pos i])
    (fun j k hjk => (hjk (Subsingleton.elim j k)).elim)
    (fun j k hjk => (hjk (Subsingleton.elim j k)).elim)

theorem real_one_axis_product_full_package : RealProductData 1 := real_product_family 1

theorem real_no_axes_product_full_package : RealProductData 0 := real_product_family 0

#print axioms real_one_axis_product_full_package
#print axioms real_no_axes_product_full_package

theorem real_one_axis_prescribed_coordinate :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun _ => (0 : ℝ)) (0 : ℝ) ∧
      Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (0 : ℝ) (0 : ℝ) (R i) (ε i),
      ∃ γ : ℝ → ℝ, Isometry γ ∧ γ 0 = 0 ∧
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ (z : Z) (e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z)),
          e 0 = WithLp.toLp 2 (0, z) ∧
          (∀ t, e (γ t) = WithLp.toLp 2 (PiLp.single 2 0 t, z)) ∧
          (∀ x, lineCoordinate γ x = (e x).fst 0) ∧
          (∀ x, Tendsto (fun T : ℝ => dist x (γ T) - T) atTop (𝓝 (-(e x).fst 0))) ∧
          (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
            S ≤ radius (ψ i) ∧ S ≤ R i ∧
            ∀ x : BallCarrier (0 : ℝ) (R i), dist x.val 0 ≤ S →
              |x.val - (e ((f i).toFun x)).fst 0| < ζ) ∧
          ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) := by
  obtain ⟨hs, hsegments, hE, qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0,
    hqPlusEnd, hqMinusEnd, ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase,
    halign, hcal, γ, hγ, hγ0, hconv, hangle, Z, m, z, e,
    he0, heaxis, hcoord, hbuse, hcoordinates, hproper, hcomplete, hcomparison, hseg⟩ :=
    real_one_axis_product_full_package
  let := m
  refine ⟨ψ, R, ε, hψ, hsub, hR, hε, f, γ 0, hγ 0, hγ0 0,
    Z, m, z, e, he0, heaxis 0, hcoord 0, hbuse 0, ?_, hproper, hcomplete, hcomparison⟩
  intro S hS ζ hζ
  filter_upwards [hcoordinates S hS ζ hζ,
    (radius_top.comp hψ.tendsto_atTop).eventually_ge_atTop S] with i hi hrad
  refine ⟨hrad, hi.1, ?_⟩
  intro x hx
  have hxS : x.val ≤ S := by
    have ha : |x.val| ≤ S := by simpa only [Real.dist_eq, sub_zero] using hx
    exact (le_abs_self _).trans ha
  have hxL : x.val ≤ radius (ψ i) := hxS.trans hrad
  have hpdist : dist (0 : ℝ) (radius (ψ i)) = radius (ψ i) := by
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (radius_pos (ψ i))]
  have hxdist : dist x.val (radius (ψ i)) = radius (ψ i) - x.val := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxL)]
    ring
  have hh := hi.2 (0 : Fin 1) x hx
  rw [hpdist, hxdist,
    show radius (ψ i) - (radius (ψ i) - x.val) = x.val by ring] at hh
  exact hh

#print axioms real_one_axis_prescribed_coordinate

end GCOriginalOrientedProductReview

#print axioms GC.MetricGeometry.exists_oriented_product_with_converging_distance_coordinates
#print axioms GC.MetricGeometry.PointedGHConverges.exists_oriented_product_of_reciprocal_local_geometry

#lint- only unusedArguments simpNF synTaut
```
