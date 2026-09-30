# Full AC71-73 independent acceptance

Eight public theorems, two definitions and two private helpers in six leaves add25 owned declarations, including13 generated declarations. The332-module gate checks1452 declarations in3167 jobs. All new transitive closures use only propext, Classical.choice and Quot.sound. Source-copy and accepted-import review lint is silent; the driver emits27 requested standard axiom reports. Declaration kinds were inspected; defLemma is unavailable. Earlier mathematical leaves are unchanged. The inherited AreaUpperBarrier warning is outside these closures. Static audit passes. No full migrated root, new PDF/Overleaf build or human approval is claimed.

Root implemented the exact-isometry KL adapter and directed compatibility definition/constructor. One agent independently reviewed them and tested the exact factor directions and coverage. That agent also implemented general metric cancellation and ordered orthonormal extension, whose full proofs root read. A second agent implemented actual product-line geometry and the full maximality assembly; root and the first agent independently read the complete proofs. The first agent also independently recompiled both product-line and full maximality integration drivers. No source hypothesis or conclusion is supplied under a renamed predicate: maximality actually excludes factor lines via inherited factor geometry and the accepted AC43 splitting.

The full maximality proof keeps the ORIGINAL a,b,p. Its axes are a inverse of the original ordered singleton vectors. Their b-directions are obtained from the supplied line coordinate theorem. Exact squared distances identify the two coordinate systems without assuming compatibility. Evaluating on those same axes proves orthonormality; the basis extension preserves original labels/signs. Product reassociation and shared-coordinate cancellation produce H in the required direction, with full global factorization. In the maximality contradiction the new factor is a subtype of B in Type u, inside the actual quantified universe; Euclidean translation normalizes the original basepoint p. Properness/comparison/segments are derived on B. Finite dimension is unused, and no arbitrary-metric common-refinement theorem is claimed.

The AC71 test uses actual j1/k2 maps with reversed second axis, separate approximation parameters1/3 and1/4, and compatibility parameter1/2. Its transverse factors are different: B=(0,infinity), A=B times R. It retains the first-coordinate formula -x_1 and the transverse factor swap globally. The equal-rank test uses the actual zero-dimensional leftover and an onto map to the original B. Each compatibility witness carries its own whole-space KL distortion and coverage.

The AC72 example uses the shared metric interval[0,1], basepoint1/2 and swapped transverse product factors based at(2,3)/(3,2). It proves the transverse factor is incomplete. The returned UNIQUE pointed factor map is proved to be exactly the inverse swap. This checks the general metric, nonzero-basepoint and uniqueness scope.

The ordered basis tests cover rank0, full rank2 and the original reversed rotated vector(-3/5,-4/5). The returned first coordinate has the exact signed inner-product formula and maps that original axis/opposite to+1/-1. The line tests use an actual diagonal unit line in R2 with Euclidean/transverse speeds3/5 and4/5, a reversed horizontal line with nontrivial bounded interval factor and proved absence of a factor line, and rank0 with transverse speed1.

Full AC73 is invoked on actual R2 with a switched smaller axis and full-rank larger splitting. The absence of a rank3 splitting is PROVED from Hausdorff dimension using the accepted rank bound. The returned Q and H recover the switched original coordinates globally. Separate switched equal-rank and rank-zero applications also prove their maximality premises. None assumes the tested no-higher-splitting statement as a free hypothesis.

Rendered-source review found KL Definition4.8(2) uses strict j<k while Lemma4.17 uses j<=k<=n. Both pages were visually checked. The source record explicitly documents this internal convention mismatch and AC71's equal-rank extension with the required factor map. It does not silently attribute the extended definition to the strict source text. Full AC71-73 are complete; simultaneous full limits, quantitative/uniform compatibility and later Chapters3-4 work remain. Blueprint207 and migration interfaces are unchanged.

```lean
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanProductCoordinates
import DifferentialGeometry.Geometry.Comparison.FactorGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.DirectedSplittingCompatibility
import DifferentialGeometry.Geometry.Metric.SharedCoordinateCancellation
import DifferentialGeometry.Analysis.InnerProductSpace.OrthonormalProductCoordinates
import DifferentialGeometry.Geometry.Comparison.ProductLineCoordinates
import DifferentialGeometry.Geometry.Comparison.ExactSplittingCompatibility

open Set Metric
namespace GCAC71Review

open GC.MetricGeometry

private abbrev E₁ := EuclideanSpace ℝ (Fin 1)
private abbrev E₂ := EuclideanSpace ℝ (Fin 2)
private abbrev B := Set.Ioi (0 : ℝ)
private abbrev A := WithLp 2 (B × E₁)
private abbrev X := WithLp 2 (E₂ × B)
private noncomputable def b : B := ⟨2, by norm_num⟩
private noncomputable def a : A := WithLp.toLp 2 (b, 0)
private noncomputable def p : X := WithLp.toLp 2 (0, b)

private theorem reversed_axis_orthonormal :
    Orthonormal ℝ (fun _ : Fin 1 => (PiLp.single 2 (1 : Fin 2) (-1) : E₂)) := by
  rw [orthonormal_iff_ite]
  intro i l
  have hil : i = l := Subsingleton.elim _ _
  subst l
  simp only [ite_true]
  rw [EuclideanSpace.inner_single_left]
  norm_num

private theorem reversed_ordered_compatibility :
    ∃ Q : E₂ ≃ₗᵢ[ℝ] WithLp 2 (E₁ × E₁),
    ∃ φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : E₁), a)) (1 / 3 : ℝ),
    ∃ ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : E₂), b)) (1 / 4 : ℝ),
      SplittingCompatible φ ψ (1 / 2) ∧
      (∀ x, ψ.toFun x = x) ∧
      (∀ x, (φ.toFun x).fst 0 = -x.fst 1) ∧
      ∀ x, (φ.toFun x).snd = WithLp.toLp 2 (x.snd, (Q x.fst).snd) := by
  obtain ⟨Q, hQ⟩ := reversed_axis_orthonormal.exists_euclidean_product_coordinates
    (by decide : 1 ≤ 2)
  let H : WithLp 2 (E₁ × B) ≃ᵢ A := IsometryEquiv.withLpProdComm 2 E₁ B
  let f : X ≃ᵢ WithLp 2 (E₁ × A) :=
    ((IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl B)).trans
      (IsometryEquiv.withLpProdAssoc 2 E₁ E₁ B)).trans
        (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl E₁) H)
  have hf : f p = WithLp.toLp 2 ((0 : E₁), a) := by
    simp [f, p, a, H]
    exact ⟨rfl, rfl⟩
  let φ := f.toKleinerLottApprox hf (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num : (1 / 3 : ℝ) < 1)
  let ψ := (IsometryEquiv.refl X).toKleinerLottApprox
    (show IsometryEquiv.refl X p = WithLp.toLp 2 ((0 : E₂), b) from rfl)
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨Q, φ, ψ, ?_, fun _ => rfl, ?_, fun _ => rfl⟩
  · apply splittingCompatible_of_exact_factorization φ ψ (by decide)
      (by norm_num) (by norm_num) Q H rfl
    intro x _
    rfl
  · intro x
    change (Q x.fst).fst 0 = -x.fst 1
    rw [hQ]
    simp [EuclideanSpace.inner_single_right]

private theorem equal_rank_compatibility :
    ∃ φ ψ : KleinerLottApprox (WithLp.toLp 2 ((0 : E₁), b))
      (WithLp.toLp 2 ((0 : E₁), b)) (1 / 4 : ℝ),
      SplittingCompatible φ ψ (1 / 2) ∧
      (∀ x, φ.toFun x = x) ∧ ∀ x, ψ.toFun x = x := by
  let Q : E₁ ≃ₗᵢ[ℝ] WithLp 2 (E₁ × EuclideanSpace ℝ (Fin 0)) :=
    (LinearIsometryEquiv.withLpProdUnique 2 ℝ E₁ (EuclideanSpace ℝ (Fin 0))).symm
  let H : WithLp 2 (EuclideanSpace ℝ (Fin 0) × B) ≃ᵢ B :=
    IsometryEquiv.withLpUniqueProd 2 (EuclideanSpace ℝ (Fin 0)) B
  let φ := (IsometryEquiv.refl (WithLp 2 (E₁ × B))).toKleinerLottApprox
    (p := WithLp.toLp 2 ((0 : E₁), b)) rfl
    (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
  refine ⟨φ, φ, ?_, fun _ => rfl, fun _ => rfl⟩
  apply splittingCompatible_of_exact_factorization φ φ (by decide)
    (by norm_num) (by norm_num) Q H rfl
  intro x _
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext rfl rfl

#print axioms IsometryEquiv.toKleinerLottApprox
#print axioms GC.MetricGeometry.SplittingCompatible
#print axioms reversed_axis_orthonormal
#print axioms reversed_ordered_compatibility
#print axioms equal_rank_compatibility

end GCAC71Review

#lint- only unusedArguments simpNF synTaut

namespace GCAC72Review

open Set

private abbrev E := Icc (0 : ℝ) 1
private abbrev P := Ioi (0 : ℝ)
private abbrev A := WithLp 2 (P × ℝ)
private abbrev C := WithLp 2 (ℝ × P)
private abbrev X := WithLp 2 (E × A)

private noncomputable def e₀ : E := ⟨1 / 2, by norm_num⟩
private noncomputable def a₀ : A := WithLp.toLp 2 (⟨2, by norm_num⟩, 3)
private noncomputable def c₀ : C := WithLp.toLp 2 (3, ⟨2, by norm_num⟩)
private noncomputable def p : X := WithLp.toLp 2 (e₀, a₀)
private noncomputable def a : X ≃ᵢ WithLp 2 (E × A) := IsometryEquiv.refl _
private noncomputable def c : X ≃ᵢ WithLp 2 (E × C) :=
  IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl E)
    (IsometryEquiv.withLpProdComm 2 P ℝ)

private theorem incomplete_half_line : ¬ CompleteSpace P := by
  intro h
  let := h
  have hc : IsClosed (Ioi (0 : ℝ)) := by
    simpa only [Subtype.range_coe] using
      (isometry_subtype_coe (s := Ioi (0 : ℝ))).isClosedEmbedding.isClosed_range
  have hm : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  exact (lt_irrefl (0 : ℝ)) (hc.closure_subset hm)

private theorem incomplete_factor : ¬ CompleteSpace C := by
  intro h
  let := h
  have hP : CompleteSpace P :=
    (IsometryEquiv.refl C).completeSpace_l2_product_factor (0 : ℝ)
  exact incomplete_half_line hP

private theorem permuted_incomplete_factor_cancellation :
    ∃! H : C ≃ᵢ A, H c₀ = a₀ ∧
      (∀ x, a x = WithLp.toLp 2 ((c x).fst, H (c x).snd)) ∧
      H = IsometryEquiv.withLpProdComm 2 ℝ P := by
  obtain ⟨H, hH, hunique⟩ :=
    IsometryEquiv.exists_unique_l2ProductFactor_of_fst_eq a c (fun _ => rfl)
      (p := p) (e₀ := e₀) (a₀ := a₀) (c₀ := c₀) rfl rfl
  have hs : (IsometryEquiv.withLpProdComm 2 ℝ P) c₀ = a₀ ∧
      ∀ x, a x = WithLp.toLp 2 ((c x).fst,
        (IsometryEquiv.withLpProdComm 2 ℝ P) (c x).snd) := by
    refine ⟨rfl, fun x => ?_⟩
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.equiv 2 _).injective
      exact Prod.ext rfl rfl
  refine ⟨H, ⟨hH.1, hH.2, (hunique _ hs).symm⟩, ?_⟩
  intro K hK
  exact hunique K ⟨hK.1, hK.2.1⟩

#print axioms incomplete_half_line
#print axioms incomplete_factor
#print axioms permuted_incomplete_factor_cancellation

end GCAC72Review

#lint- only unusedArguments simpNF synTaut

namespace GCAC73CoordinatesReview

private theorem rank_zero :
    ∃ Q : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 2)),
      ∀ v, (Q v).fst = 0 := by
  let ξ : Fin 0 → EuclideanSpace ℝ (Fin 2) := Fin.elim0
  have hξ : Orthonormal ℝ ξ := by
    rw [orthonormal_iff_ite]
    intro i
    exact Fin.elim0 i
  obtain ⟨Q, _⟩ := hξ.exists_euclidean_product_coordinates (by decide : 0 ≤ 2)
  refine ⟨Q, fun v => ?_⟩
  ext i
  exact Fin.elim0 i

private theorem full_rank :
    ∃ Q : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 0)),
      ∀ v, Q v = WithLp.toLp 2 (v, 0) := by
  have hξ : Orthonormal ℝ (fun i : Fin 2 => (PiLp.single 2 i 1 : EuclideanSpace ℝ (Fin 2))) :=
    EuclideanSpace.orthonormal_single
  obtain ⟨Q, hQ⟩ := hξ.exists_euclidean_product_coordinates (by decide : 2 ≤ 2)
  refine ⟨Q, fun v => ?_⟩
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    change (Q v).fst i = v i
    simpa [EuclideanSpace.inner_single_right] using hQ v i
  · ext i
    exact Fin.elim0 i

private noncomputable def reversedRotatedAxis : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![-3 / 5, -4 / 5]

private theorem reversedRotatedAxis_orthonormal :
    Orthonormal ℝ (fun _ : Fin 1 => reversedRotatedAxis) := by
  rw [orthonormal_iff_ite]
  intro i l
  have hil : i = l := Subsingleton.elim _ _
  subst l
  simp only [ite_true]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  norm_num [reversedRotatedAxis, dotProduct, Fin.sum_univ_two]

private theorem reversed_rotated_rank_one :
    ∃ Q : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)),
      (∀ v, (Q v).fst 0 = -(3 * v 0 + 4 * v 1) / 5) ∧
      (Q reversedRotatedAxis).fst 0 = 1 ∧
      (Q (-reversedRotatedAxis)).fst 0 = -1 := by
  obtain ⟨Q, hQ⟩ := reversedRotatedAxis_orthonormal.exists_euclidean_product_coordinates
    (by decide : 1 ≤ 2)
  have hformula (v : EuclideanSpace ℝ (Fin 2)) :
      (Q v).fst 0 = -(3 * v 0 + 4 * v 1) / 5 := by
    rw [hQ]
    simp only [reversedRotatedAxis, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, Fin.sum_univ_two]
    norm_num
    ring
  refine ⟨Q, hformula, ?_, ?_⟩
  · norm_num [hformula, reversedRotatedAxis]
  · norm_num [hformula, reversedRotatedAxis]

#print axioms rank_zero
#print axioms full_rank
#print axioms reversedRotatedAxis_orthonormal
#print axioms reversed_rotated_rank_one

end GCAC73CoordinatesReview

#lint- only unusedArguments simpNF synTaut

open Set

namespace GCProductLineReview

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

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def diagonal (t : ℝ) : Plane := WithLp.toLp 2 ![3 * t / 5, 4 * t / 5]

private theorem diagonal_isometry : Isometry diagonal := by
  apply Isometry.of_dist_eq
  intro s t
  apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
  rw [EuclideanSpace.dist_sq_eq]
  norm_num only [diagonal, Fin.sum_univ_two, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Real.dist_eq]
  simp only [sq_abs]
  ring

private noncomputable def planeSplit : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × ℝ) :=
  (EuclideanSpace.finSuccProdIsometry 1).toIsometryEquiv

private theorem diagonal_base : planeSplit (diagonal 0) = WithLp.toLp 2 (0, 0) := by
  have hz : diagonal 0 = 0 := by ext i; fin_cases i <;> norm_num [diagonal]
  rw [hz]
  exact (EuclideanSpace.finSuccProdIsometry 1).map_zero

private theorem diagonal_snd (t : ℝ) : (planeSplit (diagonal t)).snd = 4 * t / 5 := by
  exact EuclideanSpace.finSuccProdIsometry_snd 1 (diagonal t)

theorem diagonal_has_positive_transverse_speed :
    (∀ t : ℝ, (planeSplit (diagonal t)).fst = t • (planeSplit (diagonal 1)).fst) ∧
      ‖(planeSplit (diagonal 1)).fst‖ ^ 2 = (3 / 5 : ℝ) ^ 2 ∧
      dist (0 : ℝ) (planeSplit (diagonal 1)).snd = 4 / 5 ∧
      ∀ s t : ℝ, dist (planeSplit (diagonal s)).snd (planeSplit (diagonal t)).snd =
        (4 / 5 : ℝ) * dist s t := by
  have hspeed := isometry_line_product_speed inner_comparison planeSplit
    diagonal_isometry diagonal_base
  have hc : dist (0 : ℝ) (planeSplit (diagonal 1)).snd = 4 / 5 := by
    rw [diagonal_snd]
    norm_num
  refine ⟨euclidean_coordinate_isometry_line inner_comparison planeSplit
    diagonal_isometry diagonal_base, ?_, hc, ?_⟩
  · rw [hc] at hspeed
    nlinarith [hspeed.1]
  · simpa only [hc] using hspeed.2

private abbrev Interval := Set.Icc (0 : ℝ) 1
private abbrev Strip := WithLp 2 (EuclideanSpace ℝ (Fin 1) × Interval)
private noncomputable def middle : Interval := ⟨1 / 2, by constructor <;> norm_num⟩
private noncomputable def horizontal (t : ℝ) : Strip := WithLp.toLp 2 (PiLp.single 2 0 (-t), middle)

private theorem interval_no_line : ¬ ∃ η : ℝ → Interval, Isometry η := by
  rintro ⟨η, hη⟩
  have he := hη.dist_eq 0 2
  have hh : |(η 0 : ℝ) - (η 2 : ℝ)| ≤ 1 := abs_le.mpr
    ⟨by linarith [(η 0).property.1, (η 2).property.2],
      by linarith [(η 0).property.2, (η 2).property.1]⟩
  norm_num [Subtype.dist_eq, Real.dist_eq] at he
  linarith

private theorem strip_comparison : fourPointComparison 0 (univ : Set Strip) := by
  exact (inner_comparison (V := Plane)).of_isometry
    ((EuclideanSpace.finSuccProdIsometry 1).symm.isometry.comp
      ((isometry_id (α := EuclideanSpace ℝ (Fin 1))).withLpProdMap 2 isometry_subtype_coe))

private theorem horizontal_isometry : Isometry horizontal := by
  apply (WithLp.isometry_prodMk_right middle).comp
  apply Isometry.of_dist_eq
  intro s t
  rw [PiLp.dist_single_same]
  exact dist_neg_neg s t

private theorem horizontal_base : horizontal 0 = WithLp.toLp 2 (0, middle) := by
  simp only [horizontal, neg_zero, (PiLp.single_eq_zero_iff 2 (0 : Fin 1)).mpr rfl]

theorem bounded_factor_same_line :
    ‖(horizontal 1).fst‖ = 1 ∧
      ∀ t : ℝ, horizontal t = WithLp.toLp 2 (t • (horizontal 1).fst, middle) := by
  exact isometry_line_eq_euclidean_smul_of_no_factor_line strip_comparison
    (IsometryEquiv.refl Strip) interval_no_line horizontal_isometry horizontal_base

theorem bounded_factor_is_nontrivial : ∃ x y : Interval, x ≠ y := by
  refine ⟨⟨0, by constructor <;> norm_num⟩, ⟨1, by constructor <;> norm_num⟩, ?_⟩
  intro h
  have he := congrArg Subtype.val h
  norm_num at he

private noncomputable def transverseOnly (t : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  PiLp.single 2 0 t

private noncomputable def emptySplit : EuclideanSpace ℝ (Fin 1) ≃ᵢ
    WithLp 2 (EuclideanSpace ℝ (Fin 0) × ℝ) :=
  (EuclideanSpace.finSuccProdIsometry 0).toIsometryEquiv

theorem rank_zero_transverse_speed :
    (∀ t : ℝ, (emptySplit (transverseOnly t)).fst = 0) ∧
      ∀ s t : ℝ, dist (emptySplit (transverseOnly s)).snd
        (emptySplit (transverseOnly t)).snd = dist s t := by
  have hline : Isometry transverseOnly := Isometry.of_dist_eq
    (fun s t => PiLp.dist_single_same 2 (fun _ : Fin 1 => ℝ) 0 s t)
  have hbase : emptySplit (transverseOnly 0) = WithLp.toLp 2 (0, 0) := by
    change (EuclideanSpace.finSuccProdIsometry 0) (PiLp.single 2 (0 : Fin 1) 0) = _
    rw [(PiLp.single_eq_zero_iff 2 (0 : Fin 1)).mpr rfl]
    exact (EuclideanSpace.finSuccProdIsometry 0).map_zero
  obtain ⟨hnorm, hdist⟩ := isometry_line_product_speed inner_comparison emptySplit hline hbase
  have hfst : (emptySplit (transverseOnly 1)).fst = 0 := Subsingleton.elim _ _
  rw [hfst, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hnorm
  have hc : dist (0 : ℝ) (emptySplit (transverseOnly 1)).snd = 1 :=
    (sq_eq_sq₀ dist_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp (by simpa only [one_pow] using hnorm)
  refine ⟨fun _ => Subsingleton.elim _ _, ?_⟩
  simpa only [hc, one_mul] using hdist

#print axioms diagonal_has_positive_transverse_speed
#print axioms bounded_factor_same_line
#print axioms bounded_factor_is_nontrivial
#print axioms rank_zero_transverse_speed

end GCProductLineReview

open Set

namespace GCExactSplittingCompatibilityReview

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
private abbrev One := EuclideanSpace ℝ (Fin 1)
private abbrev Unit := PUnit.{1}

private noncomputable def switched : Plane ≃ᵢ WithLp 2 (One × ℝ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)).toIsometryEquiv.trans
    (EuclideanSpace.finSuccProdIsometry 1).toIsometryEquiv

private noncomputable def fullSplit : Plane ≃ᵢ WithLp 2 (Plane × Unit) :=
  (IsometryEquiv.withLpProdUnique 2 Plane Unit).symm

private theorem switched_fst (x : Plane) : (switched x).fst 0 = x 1 := by
  change (EuclideanSpace.finSuccProdIsometry 1
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) x)).fst 0 = _
  rw [EuclideanSpace.finSuccProdIsometry_fst_apply]
  rfl

private theorem switched_snd (x : Plane) : (switched x).snd = x 0 := by
  change (EuclideanSpace.finSuccProdIsometry 1
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1) x)).snd = _
  rw [EuclideanSpace.finSuccProdIsometry_snd]
  rfl

private theorem switched_base : switched 0 = WithLp.toLp 2 (0, 0) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact switched_fst 0
  · exact switched_snd 0

private theorem full_base : fullSplit 0 = WithLp.toLp 2 (0, PUnit.unit) := rfl

private theorem full_maximal : ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (F : Plane ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 3) × W)),
      F 0 = WithLp.toLp 2 (0, w) := by
  rintro ⟨W, m, w, F, _⟩
  let := m
  have hd := F.euclidean_rank_le_dimH w
  rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin] at hd
  norm_num at hd

theorem maximal_plane_switched_axis_compatibility :
    ∃ (Q : Plane ≃ₗᵢ[ℝ] WithLp 2 (One × One))
      (H : WithLp 2 (One × Unit) ≃ᵢ ℝ),
      H (WithLp.toLp 2 (0, PUnit.unit)) = 0 ∧
        (∀ x : Plane, switched x = WithLp.toLp 2 ((Q x).fst,
          H (WithLp.toLp 2 ((Q x).snd, PUnit.unit)))) ∧
        (∀ x : Plane, (Q x).fst 0 = x 1) ∧
        ∀ x : Plane, H (WithLp.toLp 2 ((Q x).snd, PUnit.unit)) = x 0 := by
  obtain ⟨Q, H, hpoint, hglobal⟩ := exists_exact_compatibility_of_maximal_splitting
    inner_comparison (by norm_num : 1 ≤ 2) inner_segments switched fullSplit
    switched_base full_base full_maximal
  refine ⟨Q, H, hpoint, hglobal, ?_, ?_⟩
  · intro x
    have hh := congrArg (fun z : WithLp 2 (One × ℝ) => z.fst 0) (hglobal x)
    exact hh.symm.trans (switched_fst x)
  · intro x
    have hh := congrArg (fun z : WithLp 2 (One × ℝ) => z.snd) (hglobal x)
    exact hh.symm.trans (switched_snd x)

private noncomputable def fullSwitched : Plane ≃ᵢ WithLp 2 (Plane × Unit) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)).toIsometryEquiv.trans
    fullSplit

private theorem fullSwitched_base : fullSwitched 0 = WithLp.toLp 2 (0, PUnit.unit) := by
  change fullSplit (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.swap (0 : Fin 2) 1) 0) = _
  rw [map_zero, full_base]

theorem maximal_plane_equal_rank_compatibility :
    ∃ (Q : Plane ≃ₗᵢ[ℝ] WithLp 2 (Plane × EuclideanSpace ℝ (Fin 0)))
      (H : WithLp 2 (EuclideanSpace ℝ (Fin 0) × Unit) ≃ᵢ Unit),
      H (WithLp.toLp 2 (0, PUnit.unit)) = PUnit.unit ∧
        ∀ x : Plane, fullSwitched x = WithLp.toLp 2 ((Q x).fst,
          H (WithLp.toLp 2 ((Q x).snd, PUnit.unit))) := by
  exact exists_exact_compatibility_of_maximal_splitting
    inner_comparison (by norm_num : 2 ≤ 2) inner_segments fullSwitched fullSplit
    fullSwitched_base full_base full_maximal

private abbrev Empty := EuclideanSpace ℝ (Fin 0)

private noncomputable def emptyFull : Empty ≃ᵢ WithLp 2 (Empty × Unit) :=
  (IsometryEquiv.withLpProdUnique 2 Empty Unit).symm

private theorem empty_maximal : ¬ ∃ (W : Type) (m : MetricSpace W), letI := m
    ∃ (w : W) (F : Empty ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 1) × W)),
      F 0 = WithLp.toLp 2 (0, w) := by
  rintro ⟨W, m, w, F, _⟩
  let := m
  have hd := F.euclidean_rank_le_dimH w
  rw [Real.dimH_univ_eq_finrank, finrank_euclideanSpace_fin] at hd
  norm_num at hd

theorem maximal_rank_zero_compatibility :
    ∃ (Q : Empty ≃ₗᵢ[ℝ] WithLp 2 (Empty × Empty))
      (H : WithLp 2 (Empty × Unit) ≃ᵢ Unit),
      H (WithLp.toLp 2 (0, PUnit.unit)) = PUnit.unit ∧
        ∀ x : Empty, emptyFull x = WithLp.toLp 2 ((Q x).fst,
          H (WithLp.toLp 2 ((Q x).snd, PUnit.unit))) := by
  exact exists_exact_compatibility_of_maximal_splitting
    inner_comparison (by norm_num : 0 ≤ 0) inner_segments emptyFull emptyFull
    rfl rfl empty_maximal

#print axioms maximal_plane_switched_axis_compatibility
#print axioms maximal_plane_equal_rank_compatibility
#print axioms maximal_rank_zero_compatibility

end GCExactSplittingCompatibilityReview

#print axioms GC.MetricGeometry.splittingCompatible_of_exact_factorization
#print axioms IsometryEquiv.exists_unique_l2ProductFactor_of_fst_eq
#print axioms Orthonormal.exists_euclidean_product_coordinates
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.euclidean_coordinate_isometry_line
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.isometry_line_product_speed
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.isometry_line_eq_euclidean_smul_of_no_factor_line
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_exact_compatibility_of_no_factor_line
#print axioms DifferentialGeometry.Geometry.Comparison.Toponogov.exists_exact_compatibility_of_maximal_splitting

#lint- only unusedArguments simpNF synTaut
```
