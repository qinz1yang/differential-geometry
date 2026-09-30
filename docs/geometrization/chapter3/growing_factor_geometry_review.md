# Compiled self-review: original-input factor consumers

Six public theorems in three leaves add six owned declarations. The225-module
gate checks1136 owned declarations (3059 jobs); all transitive axiom closures
use only propext, Classical.choice and Quot.sound. Source-copy unusedArguments,
simpNF and synTaut linters are silent. Declaration kinds were checked
manually; defLemma is unavailable. Earlier mathematical leaves are unchanged.
The inherited AreaUpperBarrier warning remains outside these closures.
Static audit passes; no full migrated root, fresh blueprint PDF/Overleaf
build, human or delegated review is claimed.

The compiled review supplies the actual positive sequences kappa_i=1/(i+1)
and rho_i=i+1 on the real line, with explicit length curves, local comparison
and the genuine dimension1 bound. It checks the exact source polynomial
constant for arbitrary positive R and0<epsilon<=1. The natural-ceiling
inequality is also tested with B=0 and epsilon=1 for every natural exponent,
including exponent0.

An explicit onto splitting of the real line into Euclidean1-space times
Euclidean0-space is constructed using the singleton orthonormal basis and
the unique-factor isometry. Its basepoint alignment is proved. The new
factor theorem then derives rank1<=1 and transverse dimension0 on the
actual constant pointed limit; the full-rank consumer constructs a pointed
Euclidean isometry. The actual identity line in that same real limit is
used in the line-factor producer, obtaining all factor geometry and the
zero-dimensional bound. These are inhabited uses, not assumed result packets.

A further compiled integration first invokes the original-input growing-
region extraction, retains its actual Y, metric, basepoint and strictly
increasing subsequence, transports kappa/radius convergence and local data
along that subsequence, then applies the new line-factor consumer to any
supplied line on THAT Y. No replacement target or extraction is made.
The final driver exits zero with only six axiom reports.

Statement audit checks that the Euclidean-factor theorem derives k<=n
rather than assuming it, and subtracts exponents using the accepted actual
product-grid covering argument. Full-rank recognition retains explicit
basepoint alignment. Geodesics and comparison are derived for the existing
proper target; they are not extra caller premises. Target properness is
explicit where used and is supplied by ALG07 for its constructed limit.
The line theorem retains an actual Isometry from the entire real line and
aligns the output with its given parameter. No line production, product-
dimension identity, global endpoint-free classification or smooth structure
is inferred. The source and limit constants remain distinct and exact,
with the sharper AC40 constant available from the preceding extraction.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionFactorGeometry
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

private noncomputable def real_one : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv

private noncomputable def real_split :
    ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 0)) :=
  real_one.trans (IsometryEquiv.withLpProdUnique 2
    (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 0))).symm

private theorem real_split_zero : real_split 0 = WithLp.toLp 2 (0, 0) := by
  apply (IsometryEquiv.withLpProdUnique 2
    (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 0))).injective
  change real_one 0 = 0
  exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero

example {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεone : ε ≤ 1) :
    ∀ᶠ _i : ℕ in atTop, ∃ T : Finset ℝ,
      (T.card : ℝ) ≤ (2 + 4 * (pairedChartDistortion 1) ^ 2 * Real.sinh (2 * R)) * ε ^ (-1 : ℝ) ∧
      (∀ x ∈ T, dist x 0 ≤ R) ∧
      ∀ x : ℝ, dist x 0 ≤ R → ∃ y ∈ T, dist x y ≤ ε := by
  have h := eventual_polynomial_nets_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le) hR hε hεone
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one] using h

example : (1 : ℕ) ≤ 1 ∧ dimH (univ : Set (EuclideanSpace ℝ (Fin 0))) ≤ 0 := by
  have h := (PointedGHConverges.const (0 : ℝ)).euclidean_factor_dimension_of_growing_local_geometry
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
    real_split 0
  simpa only [Nat.sub_self, Nat.cast_zero, ENNReal.ofReal_zero] using h

example : ∃ f : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1), f 0 = 0 :=
  (PointedGHConverges.const (0 : ℝ)).exists_pointed_euclidean_of_growing_local_geometry
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
    real_split 0 real_split_zero

example : ∃ (Z : Type) (m : MetricSpace Z), letI := m
    ∃ (z : Z) (e : ℝ ≃ᵢ WithLp 2 (ℝ × Z)),
      (∀ t, e t = WithLp.toLp 2 (t, z)) ∧ ProperSpace Z ∧ CompleteSpace Z ∧
      fourPointComparison 0 (univ : Set Z) ∧
      (∀ a b : Z, ∃ f : Icc (0 : ℝ) 1 → Z,
        Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
      dimH (univ : Set Z) ≤ 0 := by
  have h := (PointedGHConverges.const (0 : ℝ)).exists_line_factor_of_growing_local_geometry
    (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
    kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
    (γ := id) isometry_id
  simpa only [id_eq, Nat.sub_self, Nat.cast_zero, ENNReal.ofReal_zero] using h

example (n : ℕ) : (((1 + Nat.ceil ((0 : ℝ) / 1)) ^ n : ℕ) : ℝ) ≤
    (2 + (0 : ℝ)) ^ n * (1 : ℝ) ^ (-(n : ℝ)) :=
  ceil_covering_bound_le_polynomial (by norm_num) (by norm_num) (by norm_num) n

example : ∃ (Y : Type) (m : MetricSpace Y), letI := m
    ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧
      PointedGHConverges (fun _ : ℕ => (0 : ℝ)) q ∧
      ∀ γ : ℝ → Y, Isometry γ →
        ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
          ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (ℝ × Z)),
            (∀ t, e (γ t) = WithLp.toLp 2 (t, z)) ∧ dimH (univ : Set Z) ≤ 0 := by
  obtain ⟨Y, m, q, φ, hφ, _, hproper, hconv, _, _, _, _, _⟩ :=
    exists_pointed_limit_of_growing_local_geometry (X := fun _ => ℝ) (fun _ => 0)
      (by omega : 1 ≤ (1 : ℕ)) (fun _ => real_curves) (fun i => (kappas_pos i).le)
      kappas_zero radii_top real_dim (fun i z _ => ambient_local z (kappas_pos i).le)
  let := m
  let := hproper
  refine ⟨Y, m, q, φ, hφ, hconv, ?_⟩
  intro γ hγ
  obtain ⟨Z, mZ, z, e, halign, _, _, _, _, hd⟩ :=
    hconv.exists_line_factor_of_growing_local_geometry (by omega : 1 ≤ (1 : ℕ))
      (fun _ => real_curves) (fun i => (kappas_pos (φ i)).le)
      (kappas_zero.comp hφ.tendsto_atTop) (radii_top.comp hφ.tendsto_atTop)
      (fun i => real_dim (φ i)) (fun i z _ => ambient_local z (kappas_pos (φ i)).le) hγ
  refine ⟨Z, mZ, z, e, halign, ?_⟩
  simpa only [Nat.sub_self, Nat.cast_zero, ENNReal.ofReal_zero] using hd

#print axioms Metric.ceil_covering_bound_le_polynomial
#print axioms eventual_polynomial_nets_of_growing_local_geometry
#print axioms polynomial_covering_of_growing_local_geometry
#print axioms PointedGHConverges.euclidean_factor_dimension_of_growing_local_geometry
#print axioms PointedGHConverges.exists_pointed_euclidean_of_growing_local_geometry
#print axioms PointedGHConverges.exists_line_factor_of_growing_local_geometry
```
