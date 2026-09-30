# Compiled self-review: full metric AC51

Three public theorems and one definition in two leaves add thirteen owned
declarations including generated declarations. The270-module gate checks1266
owned declarations (3104 jobs), with transitive axiom closures limited to
propext, Classical.choice and Quot.sound. Source-copy unusedArguments, simpNF
and synTaut linters are silent. Declaration kinds were manually inspected;
defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited
AreaUpperBarrier warning is outside these closures. Static audit passes. No full
migrated root, fresh blueprint PDF/Overleaf build, human or delegated review is claimed.

The independent compiled driver retains the actual rational source/factor and
its independently proved incompleteness and nonproperness, rational-density
approximations to R, exact product approximation tests with nonzero basepoint,
and product identification of the specified real plane. A new actual KL map
reflects the REAL coordinate in R x_2 Q and fixes the rational coordinate. Its
L2 distance preservation, basepoint, explicit involutive preimages and genuine
infimum coverage are proved. Alternating this reflection with identity gives
supplied whole-space product maps whose left coordinate at(1,0) alternates1,-1.
The full AC51 theorem applies to these actual maps and the given real-plane
limit: its result includes one complete proper factor, one common subsequence,
an onto pointed product isometry, actual source approximations on growing balls
with vanishing errors, and uniform control of those SAME alternating original
coordinates. The driver exits zero with sixteen axiom reports. The preceding
controlled_isometry review independently proves nonconvergence of1,-1 on the
full sequence, explaining the retained subsequence qualification.

Statement audit checks all three subsequences compose to one strictly increasing
map, the original source target is unchanged, factor/source convergence remains
on the final sequence, and both the onto isometry and approximation maps are
actual data. The finite coordinate-preservation equality is exact before taking
limits. The final error is uniform over all points in every fixed source ball;
growing domains ensure those entire balls eventually belong to the domain.
Euclidean distance is the stated coordinate norm; the theorem works more generally
for any fixed proper left metric factor. It assumes neither continuity of maps
nor complete/proper source spaces or factors. No KL4.8 compatibility, coordinate
uniqueness, long-strainer production or full-sequence alignment is asserted.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.ControlledProductLimit
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

private def leftReflectionKL {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    KleinerLottApprox (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ)))
      (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) δ := by
  let F : WithLp 2 (ℝ × ℚ) → WithLp 2 (ℝ × ℚ) :=
    fun x => WithLp.toLp 2 (-x.fst, x.snd)
  have hbase : F (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) =
      WithLp.toLp 2 ((0 : ℝ), (0 : ℚ)) := by simp [F]
  have hinv (x : WithLp 2 (ℝ × ℚ)) : F (F x) = x := by simp [F]; rfl
  have hdist (x y : WithLp 2 (ℝ × ℚ)) : dist (F x) (F y) = dist x y := by
    rw [WithLp.prod_dist_eq_sqrt_sq_add_sq, WithLp.prod_dist_eq_sqrt_sq_add_sq]
    change Real.sqrt (dist (-x.fst) (-y.fst) ^ 2 + dist x.snd y.snd ^ 2) = _
    rw [dist_neg_neg]
  refine ⟨hδ, hδone, F, hbase, ?_, ?_⟩
  · intro x _ y _
    simpa only [hdist, sub_self, abs_zero] using hδ.le
  · intro y hy
    have hyin : F y ∈ ball (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) δ⁻¹ := by
      change dist (F y) _ < δ⁻¹
      rw [← hbase, hdist]
      linarith
    have hmem : y ∈ F '' ball (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) δ⁻¹ :=
      ⟨F y, hyin, hinv y⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by simpa using hδ.le)

private noncomputable def alternatingProduct (i : ℕ) :
    KleinerLottApprox (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ)))
      (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) (errors i) :=
  if i % 2 = 0 then identityKL _ (errors_bounds i).1 (errors_bounds i).2
  else leftReflectionKL (errors_bounds i).1 (errors_bounds i).2

example (i : ℕ) : ((alternatingProduct i).toFun (WithLp.toLp 2 ((1 : ℝ), (0 : ℚ)))).fst =
    if i % 2 = 0 then (1 : ℝ) else -1 := by
  simp only [alternatingProduct]
  split_ifs <;> rfl

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace W ∧ CompleteSpace W ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℚ)) w ∧
      PointedGHConverges (fun _ : ℕ => WithLp.toLp 2 ((0 : ℝ), (0 : ℚ)))
        (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) ∧
      ∃ e : WithLp 2 (ℝ × ℝ) ≃ᵢ WithLp 2 (ℝ × W),
        e (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) = WithLp.toLp 2 ((0 : ℝ), w) ∧
        ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
          ∃ g : ∀ i, PointedBallApprox (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ)))
              (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) (R i) (ε i),
            ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
              ∀ x : BallCarrier (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) (R i),
                dist x.val (WithLp.toLp 2 ((0 : ℝ), (0 : ℚ))) ≤ S →
                dist (((alternatingProduct (φ i)).toFun x.val).fst)
                  ((e ((g i).toFun x)).fst) < η :=
  (ratConverges.l2Product (0 : ℝ)).exists_controlled_product_limit_of_approximate_products
    (E := ℝ) (Z := fun _ => ℚ) (a := 0) (b := fun _ => 0) alternatingProduct errors_zero

#print axioms GC.MetricGeometry.KleinerLottApprox.productLimitApprox
#print axioms GC.MetricGeometry.KleinerLottApprox.productLimitApprox_fst
#print axioms GC.MetricGeometry.PointedGHConverges.eventually_product_coordinate_approximation
#print axioms GC.MetricGeometry.PointedGHConverges.exists_controlled_product_limit_of_approximate_products
```
