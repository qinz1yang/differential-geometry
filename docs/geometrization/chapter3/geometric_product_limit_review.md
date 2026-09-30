# Compiled self-review: full AC56 on the specified limit

Three public theorems in one leaf add five owned declarations including generated
declarations. The274-module gate checks1295 owned declarations (3108 jobs), with
transitive axiom closures limited to propext, Classical.choice and Quot.sound.
Source-copy unusedArguments, simpNF and synTaut linters are silent. Declaration
kinds were manually inspected; defLemma is unavailable. Earlier mathematical
leaves are unchanged. The inherited AreaUpperBarrier warning is outside these
closures. Static audit passes. No full migrated root, fresh blueprint PDF/Overleaf
build, human or delegated review is claimed.

The independent compiled driver uses the actual real line with its true metric,
explicit affine minimizing segments and arbitrarily short curves. It proves
four-point comparison for every nonnegative curvature parameter using the actual
same-side model angle zero and three-angle bound. The Hausdorff bounds follow
from the actual real dimension and subset monotonicity. Its supplied KL maps are
actual onto isometries to EuclideanFin1 x_2 EuclideanFin0, with proven basepoint,
distortion and infimum coverage via explicit inverse witnesses. Errors are
positive, less than one and tend tozero.

All three public consumers are tested at the genuinely positive full rankk=n=1:
independently growing balls with curvature0; exact reciprocal-radius balls with
curvature-errorsdelta_i; and supplied maps restricted to the taili>=7. The tests
extract an onto pointed product on the SAME specified real target and a complete
proper nonnegative factor with dimH<=0. The tail test additionally retains every
selected index>=7, actual growing-domain source approximations and uniform control
of the original Euclidean coordinates. No exact splitting of the target is passed
as a hypothesis to these consumers. The driver exits zero with three axiom reports.

Statement audit checks the precise local geometry on ambient open balls,
curvature-delta rather than-delta^2, positive reciprocal growth, all map/domain
margins inherited from AC41/51, same source target, one common factor/subsequence,
onto-ness, k<=n derived rather than assumed, n-k factor dimension, actual minimizing
factor segments and global factor comparison. The tail theorem evaluates only
supplied valid-index maps and creates none on the excluded prefix. No long-strainer,
orthogonal-line or Busemann producer is used. KL4.8 compatibility and KL6.18's
collapse-specific dimension conclusion remain separate.

This update also corrects source-locator metadata for AC51 to4650-4733 and AC52
to4741-4782, and records AC56 at4939-4975. The mathematical source and earlier Lean
leaves are unchanged; these corrections identify the complete bodies already read.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.GeometricProductLimit
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

open Set Metric Filter GC.MetricGeometry
open scoped Topology
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


private abbrev Z0 := EuclideanSpace ℝ (Fin 0)
private noncomputable def one_basis : ℝ ≃ᵢ EuclideanSpace ℝ (Fin 1) :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr.toIsometryEquiv
private noncomputable def one_split : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z0) :=
  one_basis.trans (IsometryEquiv.withLpProdUnique 2 (EuclideanSpace ℝ (Fin 1)) Z0).symm
private theorem one_split_zero : one_split 0 = WithLp.toLp 2 (0, (0 : Z0)) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact (OrthonormalBasis.singleton (Fin 1) ℝ).repr.map_zero
  · exact Subsingleton.elim _ _

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

private noncomputable def splitKL {δ : ℝ} (hδ : 0 < δ) (hδone : δ < 1) :
    KleinerLottApprox (0 : ℝ) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 1)), (0 : Z0))) δ where
  error_pos := hδ
  error_lt_one := hδone
  toFun := one_split
  basepoint := one_split_zero
  distortion x _ y _ := by simpa only [one_split.dist_eq, sub_self, abs_zero] using hδ.le
  coverage y hy := by
    have hd : dist (one_split.symm y) (0 : ℝ) = dist y (WithLp.toLp 2 (0, (0 : Z0))) := by
      rw [← one_split_zero]
      simpa only [one_split.symm_apply_apply] using one_split.symm.dist_eq y (one_split 0)
    have hmem : y ∈ one_split '' ball (0 : ℝ) δ⁻¹ :=
      ⟨one_split.symm y, by change dist (one_split.symm y) 0 < δ⁻¹; rw [hd]; linarith,
        one_split.apply_symm_apply y⟩
    exact (infDist_le_dist_of_mem hmem).trans (by simpa using hδ.le)

private theorem real_dim (R : ℝ) : dimH (ball (0 : ℝ) R) ≤ (1 : ENNReal) := by
  exact (dimH_mono (subset_univ _)).trans (by rw [Real.dimH_univ])

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × W)),
      e 0 = WithLp.toLp 2 (0, w) ∧ ProperSpace W ∧ CompleteSpace W ∧
      fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 0 := by
  obtain ⟨_, _, _, _, W, m, w, φ, hφ, hp, hc, hz, hx, hcomp, hseg, hd, e, he, _⟩ :=
    (PointedGHConverges.const (0 : ℝ)).exists_controlled_product_of_growing_local_geometry
      (n := 1) (k := 1) (by omega) (fun _ => real_curves)
      (κ := fun _ => 0) (ρ := fun i => (i : ℝ) + 1) (fun _ => le_rfl) tendsto_const_nhds
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
      (fun i => by simpa only [Nat.cast_one] using real_dim ((i : ℝ) + 1))
      (fun _ z _ => ambient_local z (le_refl 0))
      (fun i => splitKL (errors_bounds i).1 (errors_bounds i).2) errors_zero
  exact ⟨W, m, w, e, he, hp, hc, hcomp, by simpa using hd⟩

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × W)),
      e 0 = WithLp.toLp 2 (0, w) ∧ ProperSpace W ∧ CompleteSpace W ∧
      fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 0 := by
  obtain ⟨_, _, _, _, W, m, w, φ, hφ, hp, hc, hz, hx, hcomp, hseg, hd, e, he, _⟩ :=
    (PointedGHConverges.const (0 : ℝ)).exists_controlled_product_of_reciprocal_local_geometry
      (n := 1) (k := 1) (by omega) (fun _ => real_curves)
      (fun i => by simpa only [Nat.cast_one] using real_dim (errors i)⁻¹)
      (fun i z _ => ambient_local z (errors_bounds i).1.le)
      (fun i => splitKL (errors_bounds i).1 (errors_bounds i).2) errors_zero
  exact ⟨W, m, w, e, he, hp, hc, hcomp, by simpa using hd⟩

example : ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ i, 7 ≤ φ i) ∧ ProperSpace W ∧
      CompleteSpace W ∧ fourPointComparison 0 (univ : Set W) ∧ dimH (univ : Set W) ≤ 0 ∧
      ∃ e : ℝ ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × W), e 0 = WithLp.toLp 2 (0, w) ∧
        ∃ R ε : ℕ → ℝ, Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
          ∃ g : ∀ i, PointedBallApprox (0 : ℝ) (0 : ℝ) (R i) (ε i),
            ∀ S η : ℝ, 0 < η → ∀ᶠ i in atTop,
              ∀ x : BallCarrier (0 : ℝ) (R i), dist x.val 0 ≤ S →
                dist (one_split x.val).fst (e ((g i).toFun x)).fst < η := by
  obtain ⟨_, _, _, _, W, m, w, φ, hφ, hφI, hp, hc, hz, hx,
      hcomp, hseg, hd, e, he, R, ε, hR, heps, g, hg⟩ :=
    (PointedGHConverges.const (0 : ℝ)).exists_controlled_product_of_eventual_reciprocal_local_geometry
      7 (n := 1) (k := 1) (by omega) (fun _ => real_curves)
      (fun i => by simpa only [Nat.cast_one] using real_dim (errors i)⁻¹)
      (fun i z _ => ambient_local z (errors_bounds i).1.le)
      (fun i _ => splitKL (errors_bounds i).1 (errors_bounds i).2) errors_zero
  exact ⟨W, m, w, φ, hφ, hφI, hp, hc, hcomp, by simpa using hd, e, he, R, ε, hR, heps, g, hg⟩

#print axioms GC.MetricGeometry.PointedGHConverges.exists_controlled_product_of_growing_local_geometry
#print axioms GC.MetricGeometry.PointedGHConverges.exists_controlled_product_of_reciprocal_local_geometry
#print axioms GC.MetricGeometry.PointedGHConverges.exists_controlled_product_of_eventual_reciprocal_local_geometry
```
