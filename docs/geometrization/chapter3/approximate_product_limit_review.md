# Compiled self-review: product approximation and specified-limit identification

Six public theorems, one definition and one instance in three leaves add eighteen
owned declarations including generated declarations. The 266-module gate checks
1249 owned declarations (3100 jobs), with transitive axiom closures limited to
propext, Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF and
synTaut linters are silent. Declaration kinds were manually inspected; defLemma
is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The compiled independent driver retains AC50's genuine rational metric source and
factor, their independently proved incompleteness/nonproperness, actual rational
density approximations to R and exact E0-product maps. New tests apply the actual
product approximation at EVERY input point and arbitrary valid radius/error with
nonzero real left basepoint3, checking exact first-coordinate preservation. They
prove R x_2 Q converges to the specified R x_2 R target. Supplied whole-space KL
maps are explicitly the identity on R x_2 Q with genuine metric infimum coverage;
errors are positive, less than one and tend to zero. The final theorem produces
an actual onto pointed isometry of the specified real plane to R x_2 W with one
complete proper W and the same factor/source subsequence. This tests a genuinely
positive-dimensional left factor and incomplete right factors, not only a trivial
zero-dimensional product. The driver exits zero with twelve axiom reports.

Statement audit verifies actual L2 distances, original closed radius, coverage
margin3epsilon, exact first coordinate, no map continuity/length hypotheses,
properness of the product by compact coordinate balls, original source-target
retention and onto-ness. The existential isometry has no claimed alignment with
the supplied coordinates; uniform subsequential map control remains explicitly
separate. No maximality, strainer production or KL4.8 compatibility is asserted.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateProductLimit
import DifferentialGeometry.Geometry.Metric.Approximation.ApproximateFactorCompactness
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Rat
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

open Set Metric Filter GC.MetricGeometry
open scoped Topology

private theorem rat_incomplete : ¬ CompleteSpace ℚ := by
  intro hc
  let := hc
  have hi : Isometry (fun r : ℚ => (r : ℝ)) := Isometry.of_dist_eq (fun _ _ => rfl)
  have hclosed := hi.antilipschitzWith.isClosed_range hi.uniformContinuous
  have hdense : DenseRange (fun r : ℚ => (r : ℝ)) := Rat.denseRange_cast
  have heq : range (fun r : ℚ => (r : ℝ)) = univ := hclosed.closure_eq.symm.trans hdense.closure_range
  exact irrational_sqrt_two (by rw [heq]; exact mem_univ _)
example : ¬ ProperSpace ℚ := by
  intro hp
  let := hp
  exact rat_incomplete inferInstance

private def ratApprox {R ε : ℝ} (hε : 0 < ε) (hR : ε < R) :
    PointedBallApprox (0 : ℚ) (0 : ℝ) R ε where
  error_pos := hε
  error_lt_radius := hR
  toFun x := (x.val : ℝ)
  basepoint := Rat.cast_zero
  distortion x y := by
    simp only [Rat.dist_cast, sub_self, abs_zero]
    exact hε
  coverage y hy := by
    obtain ⟨r, hrlo, hrhi⟩ := exists_rat_btwn (by linarith : y - ε / 2 < y + ε / 2)
    have hry : dist (r : ℝ) y < ε / 2 := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hrad : dist r (0 : ℚ) ≤ R := by
      rw [← Rat.dist_cast, Rat.cast_zero]
      have ht := dist_triangle (r : ℝ) y 0
      linarith
    refine ⟨⟨r, hrad⟩, ?_⟩
    change dist y (r : ℝ) < ε
    rw [dist_comm]
    linarith

private theorem ratConverges : PointedGHConverges (fun _ : ℕ => (0 : ℚ)) (0 : ℝ) :=
  ⟨inferInstance, fun _ _ hε hR => Eventually.of_forall (fun _ => ⟨ratApprox hε hR⟩)⟩

private abbrev E0 := EuclideanSpace ℝ (Fin 0)
private def ratProductApprox {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    KleinerLottApprox (0 : ℚ) (WithLp.toLp 2 ((0 : E0), (0 : ℚ))) δ where
  error_pos := hδ
  error_lt_one := hδone
  toFun r := WithLp.toLp 2 ((0 : E0), r)
  basepoint := rfl
  distortion x _ y _ := by
    rw [(WithLp.isometry_prodMk_left (0 : E0)).dist_eq x y, sub_self, abs_zero]
    exact hδ.le
  coverage y hy := by
    have heq : WithLp.toLp 2 ((0 : E0), y.snd) = y := by
      apply (WithLp.equiv 2 _).injective
      exact Prod.ext (Subsingleton.elim _ _) rfl
    have hr : dist y.snd (0 : ℚ) < δ⁻¹ := by
      have hd := (WithLp.isometry_prodMk_left (0 : E0)).dist_eq y.snd (0 : ℚ)
      rw [heq] at hd
      linarith
    have hmem : y ∈ (fun r : ℚ => WithLp.toLp 2 ((0 : E0), r)) '' ball 0 δ⁻¹ :=
      ⟨y.snd, hr, heq⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using hδ.le)

private noncomputable def errors (i : ℕ) : ℝ := (1 / ((i : ℝ) + 1)) / 2
private theorem errors_bounds (i : ℕ) : 0 < errors i ∧ errors i < 1 := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hq : 1 / ((i : ℝ) + 1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  dsimp [errors]
  exact ⟨by positivity, by linarith⟩
private theorem errors_zero : Tendsto errors atTop (𝓝 0) := by
  change Tendsto (fun i : ℕ => (1 / ((i : ℝ) + 1)) / 2) atTop (𝓝 0)
  simpa only [zero_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2

example : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ i : ℕ, I ≤ i →
    ∃ T : Finset ℚ, T.card ≤ N ∧ (∀ y ∈ T, dist y 0 ≤ R) ∧
      ∀ y : ℚ, dist y 0 ≤ R → ∃ z ∈ T, dist y z ≤ η :=
  ratConverges.eventual_factor_nets_of_approximate_products
    (E := fun _ => E0) (Z := fun _ => ℚ) (a := fun _ => 0) (b := fun _ => 0)
    (fun i => ratProductApprox (errors_bounds i).1 (errors_bounds i).2) errors_zero

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℚ)) w ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℚ)) (0 : ℝ) :=
  ratConverges.exists_factor_limit_of_approximate_products
    (E := fun _ => E0) (Z := fun _ => ℚ) (a := fun _ => 0) (b := fun _ => 0)
    (fun i => ratProductApprox (errors_bounds i).1 (errors_bounds i).2) errors_zero

#print axioms GC.MetricGeometry.PointedBallApprox.exists_internal_finset_net_factor
#print axioms GC.MetricGeometry.PointedGHConverges.eventual_factor_nets_of_approximate_products
#print axioms GC.MetricGeometry.PointedGHConverges.exists_factor_limit_of_approximate_products
#print axioms rat_incomplete

example {R ε : ℝ} (hε : 0 < ε) (hR : 3 * ε < R)
    (x : BallCarrier (WithLp.toLp 2 ((3 : ℝ), (0 : ℚ))) R) :
    (((ratApprox hε (by linarith)).l2Product (3 : ℝ) hR).toFun x).fst = x.val.fst :=
  PointedBallApprox.l2Product_fst _ _ _ _

example : PointedGHConverges (fun _ : ℕ => WithLp.toLp 2 ((3 : ℝ), (0 : ℚ)))
    (WithLp.toLp 2 ((3 : ℝ), (0 : ℝ))) := ratConverges.l2Product 3

private def identityKL {T : Type*} [MetricSpace T] (p : T) {δ : ℝ}
    (hδ : 0 < δ) (hδone : δ < 1) : KleinerLottApprox p p δ where
  error_pos := hδ
  error_lt_one := hδone
  toFun := id
  basepoint := rfl
  distortion _ _ _ _ := by simpa using hδ.le
  coverage y hy := by
    have hmem : y ∈ id '' ball p δ⁻¹ := ⟨y, by change dist y p < δ⁻¹; linarith, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using hδ.le)

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℚ)) w ∧
      PointedGHConverges (fun _ : ℕ => WithLp.toLp 2 ((3 : ℝ), (0 : ℚ)))
        (WithLp.toLp 2 ((3 : ℝ), (0 : ℝ))) ∧
      ∃ e : WithLp 2 (ℝ × ℝ) ≃ᵢ WithLp 2 (ℝ × W),
        e (WithLp.toLp 2 ((3 : ℝ), (0 : ℝ))) = WithLp.toLp 2 ((3 : ℝ), w) :=
  (ratConverges.l2Product (3 : ℝ)).exists_product_isometry_of_approximate_products
    (E := ℝ) (Z := fun _ => ℚ) (a := 3) (b := fun _ => 0)
    (fun i => identityKL _ (errors_bounds i).1 (errors_bounds i).2) errors_zero

#print axioms Real.abs_sqrt_sq_add_sq_sub_le
#print axioms WithLp.prod_dist_dist_sub_le
#print axioms WithLp.instProperSpaceL2Prod
#print axioms GC.MetricGeometry.PointedBallApprox.l2Product
#print axioms GC.MetricGeometry.PointedBallApprox.l2Product_fst
#print axioms GC.MetricGeometry.PointedGHConverges.l2Product
#print axioms GC.MetricGeometry.PointedGHConverges.of_approximate_sources
#print axioms GC.MetricGeometry.PointedGHConverges.exists_product_isometry_of_approximate_products
```
