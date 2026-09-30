# Compiled self-review: original-input growing-region extraction

Five public theorems in three leaves add five owned declarations. The222-module
gate checks1130 owned declarations (3056 jobs); transitive axiom closures
contain only propext, Classical.choice and Quot.sound. Source-copy
unusedArguments, simpNF and synTaut linters are silent. Declaration kinds
were inspected manually because defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning lies outside
these closures. Static audit passes; no full migrated root, fresh blueprint
PDF/Overleaf build, human or delegated review is claimed.

The compiled review uses a concrete sequence of complete real lines with
basepoint0, positive kappa_i=1/(i+1) tending to0, and positive rho_i=i+1
tending to infinity. Its length curves and local comparison are explicitly
proved and its ambient dimension bound is the actual dimH(real)=1 theorem.
The exact eventual source nets and eventual same-kappa comparison are
exercised. Both original-input extraction theorems then yield all conclusions
on one existentially constructed metric/basepoint/subsequence, including
completeness, properness, dimH<=1, zero-curvature comparison, actual metric
segments, lower point-on-side comparison, and the literal AC40 net constant.
The intrinsic input uses the actual growing-ball intrinsic metric at rho_i,
not the restricted ambient subtype metric. No chart, net, compactness or
convergence witness is supplied by the review. Final compilation exits zero
with only the five axiom reports.

The statement audit checks quantifier order: for each fixed R and mesh,
source tails may depend on those choices; the strictly increasing extraction
subsequence and completed target stay fixed thereafter. Curvature and
ambient dimension are restricted only inside the original growing region.
The new local producers supply both required eventual hypotheses. Original
source completeness is used in those producers, while the generic ceiling
extraction theorem itself assumes no source properness. The target is the
actual completion constructed by the existing countable-net proof, and
comparison, dimension, geodesics and strict internal nets are all attached
to that same target. The C_R constant is exactly(2+16*L_n^2*sqrt(n)*
sinh(2*(R+1)))^n; the4 from mesh delta/4 and the source4 coefficient are
combined by a proved identity. Positive n matches MC18. Zero values of
kappa are additionally permitted by the proved zero branch. No global
source properness, sharp8R/KL comparison, Riemannian adapter, line existence
or full Chapter3/4 completion is smuggled into the conclusion.

The archived KL3.10 statement and Section3.3 standing conventions were read
at their actual printed/PDF locators; PDF19 was visually inspected. The
retained correction sheet is distinct from any moving remote copy. ALG07's
written256R globalization replaces the sharp-buffer dependency; KL's brief
similar-proof citation is not represented as a detailed proof. Historical
blueprint comments about deferred Lean bindings remain unchanged in edition207;
the current proof status is recorded in this contract and gate evidence.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Comparison.FiniteDimensionalCovering
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

open Set Metric Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

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

private theorem real_curves : ∀ x y : ℝ, ∀ ε : ℝ, 0 < ε →
    ∃ c : unitInterval → ℝ, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      eVariationOn c univ < ENNReal.ofReal (dist x y + ε) :=
  arbitrarily_short_curves_of_metric_segments real_segments

private theorem ambient_local (z : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∃ Ω : Set ℝ, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω := by
  refine ⟨Ioo (z - 1) (z + 1), isOpen_Ioo,
    (real_comparison hκ).mono (subset_univ _), ?_⟩
  exact ⟨by linarith, by linarith⟩

open Filter GC.MetricGeometry
open scoped Topology

private noncomputable def kappas (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)
private def radii (i : ℕ) : ℝ := (i : ℝ) + 1
private theorem kappas_pos (i : ℕ) : 0 < kappas i := by dsimp [kappas]; positivity
private theorem kappas_zero : Tendsto kappas atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat
private theorem radii_pos (i : ℕ) : 0 < radii i := by dsimp [radii]; positivity
private theorem radii_top : Tendsto radii atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  obtain ⟨N, hN⟩ := exists_nat_gt b
  filter_upwards [eventually_ge_atTop N] with i hi
  have hNi : (N : ℝ) ≤ i := by exact_mod_cast hi
  dsimp [radii]
  linarith

private theorem real_dim (i : ℕ) : dimH (ball (0 : ℝ) (radii i)) ≤ (1 : ℕ) := by
  simpa only [Nat.cast_one] using
    (dimH_mono (subset_univ (ball (0 : ℝ) (radii i)))).trans_eq Real.dimH_univ

example {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∀ᶠ _i : ℕ in atTop, ∃ T : Finset ℝ,
      T.card ≤ 1 + ⌈4 * (pairedChartDistortion 1) ^ 2 * Real.sinh (2 * R) / ε⌉₊ ∧
      (T : Set ℝ) ⊆ closedBall 0 R ∧
      ∀ x ∈ closedBall (0 : ℝ) R, ∃ y ∈ T, dist x y < ε := by
  have h := eventual_internal_nets_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le) hR hε
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

example {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i in atTop, fourPointComparison (kappas i) (ball (0 : ℝ) R) :=
  eventual_fourPointComparison_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
    (fun _ => real_curves) (fun i => (kappas_pos i).le) radii_top real_dim
    (fun i z _ => ambient_local z (kappas_pos i).le) hR

example :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun _ : ℕ => (0 : ℝ)) q ∧
        dimH (univ : Set Y) ≤ (1 : ℕ) ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤
            (2 + 16 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℝ) * Real.sinh (2 * (R + 1))) ^ 1 *
              δ ^ (-(1 : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  simpa only [Nat.cast_one] using
    (exists_pointed_limit_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
      (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
      kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le))

example :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun _ : ℕ => (0 : ℝ)) q ∧
        dimH (univ : Set Y) ≤ (1 : ℕ) ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤
            (2 + 16 * (pairedChartDistortion 1) ^ 2 * Real.sqrt (1 : ℝ) * Real.sinh (2 * (R + 1))) ^ 1 *
              δ ^ (-(1 : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  simpa only [Nat.cast_one] using
    (exists_pointed_limit_of_growing_intrinsic_local_geometry (X := fun _ => ℝ) (fun _ => 0)
      (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
      kappas_zero radii_top radii_pos real_dim
      (fun i z => (exists_local_fourPointComparison_intrinsicBall_iff real_curves 0
        (radii_pos i) z).mpr (ambient_local z (kappas_pos i).le)))

#print axioms eventual_internal_nets_of_growing_local_geometry
#print axioms eventual_fourPointComparison_of_growing_local_geometry
#print axioms exists_geodesic_pointedGHConverges_of_ceil_covering_and_comparison
#print axioms exists_pointed_limit_of_growing_local_geometry
#print axioms exists_pointed_limit_of_growing_intrinsic_local_geometry
```
