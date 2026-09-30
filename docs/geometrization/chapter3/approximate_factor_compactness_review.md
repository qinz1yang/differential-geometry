# Compiled self-review: actual approximate factor compactness

Three public theorems in two leaves add three owned declarations. The
263-module gate checks 1231 owned declarations (3097 jobs), with transitive
axiom closures limited to propext, Classical.choice and Quot.sound. Source-copy
unusedArguments, simpNF and synTaut linters are silent. Declaration kinds were
manually inspected; defLemma is unavailable. Earlier mathematical leaves are
unchanged. The inherited AreaUpperBarrier warning is outside these closures.
Static audit passes. No full migrated root, fresh blueprint PDF/Overleaf build,
human or delegated review is claimed.

The compiled independent driver uses the actual rational metric space as BOTH
source and approximate factor, with zero-dimensional Euclidean left factor.
It constructs actual closed-ball approximations from Q to R by rational density,
and actual whole-space KL product maps Q -> E0 x_2 Q. Their errors are positive,
less than one and tend to zero. The new theorems produce uniform internal factor
nets and one complete proper factor limit along a common subsequence, retaining
convergence to the original real target. The driver separately proves that Q
is incomplete: completeness would make its isometric image closed in R, density
would make that image all of R, contradicting irrationality of sqrt(2). It also
proves Q is not proper. Thus source/factor properness and completeness have not
been smuggled into the interface. The driver exits zero with four axiom reports.

Statement audit checks actual supplied product maps, infimum coverage with
positive slack, exact L2 metric, arbitrary varying left factors and universes,
internal net centers, bound-before-tail quantifiers and the single common
subsequence. The conclusion retains the specified original source limit.
No map continuity, source length/curvature/dimension, or factor properness is
assumed. AC51's exact product and coordinate-control assertions remain separate.

```lean
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
```
