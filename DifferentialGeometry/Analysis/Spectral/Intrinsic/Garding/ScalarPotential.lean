import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffCore
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CovariantLeibniz

/-!
# Smooth scalar potential operators on the spectral scale

This file constructs multiplication by a fixed smooth real coefficient as a
genuine bounded operator from scalar spectral `H¹` to fixed-metric `L²`, then
postcomposes it with the canonical `L² ≃ H⁰` identification.  The construction
extends the pointwise product on the dense finite spectral core.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete Real E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The dense finite-support scalar spectral `H¹` core. -/
abbrev ScalarH1Core (q : SmoothRiemannianMetric I M) :=
  tensorHs.finiteSupportSubmodule
    (I := I) (M := M) (g := q) (r := 0) (s := 0) 1

private noncomputable def scalarSmulLin
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    SmoothCcTensor q 0 0 →ₗ[Real] SmoothCcTensor q 0 0 where
  toFun := scalarSmul (I := I) (M := M) q 0 0 ζ
  map_add' := by
    intro S T
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    change (ζ : M → Real) x • (S.toSection x + T.toSection x) =
      (ζ : M → Real) x • S.toSection x +
        (ζ : M → Real) x • T.toSection x
    exact smul_add _ _ _
  map_smul' := by
    intro c S
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    change (ζ : M → Real) x • (c • S.toSection x) =
      c • ((ζ : M → Real) x • S.toSection x)
    rw [smul_smul, smul_smul, mul_comm]

/-- Multiplication by a smooth scalar coefficient on the finite `H¹` core,
realized as a smooth compactly supported rank-zero tensor section. -/
noncomputable def scalarPotSec
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ScalarH1Core (I := I) (M := M) q →ₗ[Real] SmoothCcTensor q 0 0 :=
  (scalarSmulLin (I := I) (M := M) q ζ).comp
    (finiteReprLin (I := I) (M := M) q 0 0 1)

omit [BoundarylessManifold I M] in
/-- Pointwise realization of the finite-core scalar potential section. -/
theorem scalarPotSec_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) (x : M) :
    (scalarPotSec (I := I) (M := M) q ζ v).toSection x =
      (ζ : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x := by
  rfl

/-- The genuine fixed-metric `L²` realization of multiplication by a smooth
scalar coefficient on the finite spectral core. -/
noncomputable def scalarPotCore
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ScalarH1Core (I := I) (M := M) q →ₗ[Real] TensorL2 0 0 q :=
  (SmoothCcTensor.toL2 (g := q) (r := 0) (s := 0)).toLinearMap.comp
    (scalarPotSec (I := I) (M := M) q ζ)

omit [BoundarylessManifold I M] in
/-- Applied realization of the finite-core scalar potential in `L²`. -/
theorem scalarPotCore_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotCore (I := I) (M := M) q ζ v =
      SmoothCcTensor.toL2
        (scalarSmul (I := I) (M := M) q 0 0 ζ
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) := by
  rfl

private theorem scalarSmul_norm_le
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (S : SmoothCcTensor q 0 0) :
    ‖scalarSmul (I := I) (M := M) q 0 0 ζ S‖ ≤ C * ‖S‖ := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) q
  let base : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q 0 0 x (S.toFun x) (S.toFun x)
  let weighted : M → Real := fun x =>
    tensorInnerPointwise (I := I) (M := M) q 0 0 x
      ((scalarSmul (I := I) (M := M) q 0 0 ζ S).toFun x)
      ((scalarSmul (I := I) (M := M) q 0 0 ζ S).toFun x)
  have hpoint : ∀ x : M, weighted x ≤ C ^ 2 * base x := by
    intro x
    have hsq : ((ζ : M → Real) x) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC).2 (hζ x)
    have hbase : 0 ≤ base x :=
      tensorInnerPointwise_nonneg (I := I) (M := M) q 0 0 x (S.toFun x)
    dsimp only [weighted, base]
    rw [scalarSmul_toFun_apply, tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]
    nlinarith [mul_le_mul_of_nonneg_right hsq hbase]
  have hweighted : Integrable weighted μ := by
    exact (SmoothCcTensor.memL2_toFun
      (scalarSmul (I := I) (M := M) q 0 0 ζ S)).integrable_inner_self
  have hbase : Integrable base μ := by
    exact (SmoothCcTensor.memL2_toFun S).integrable_inner_self
  have hint : (∫ x, weighted x ∂μ) ≤ ∫ x, C ^ 2 * base x ∂μ :=
    integral_mono_ae hweighted (hbase.const_mul (C ^ 2))
      (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hint
  have hsq :
      ‖scalarSmul (I := I) (M := M) q 0 0 ζ S‖ ^ 2 ≤
        (C * ‖S‖) ^ 2 := by
    simpa only [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun, tensorL2Inner, weighted, base, μ, mul_pow] using hint
  have hrhs : 0 ≤ C * ‖S‖ := mul_nonneg hC (norm_nonneg S)
  nlinarith [norm_nonneg
    (scalarSmul (I := I) (M := M) q 0 0 ζ S)]

omit [BoundarylessManifold I M] in
private theorem finiteRepr_norm
    (q : SmoothRiemannianMetric I M)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖tensorHsSmoothRepr (I := I) (M := M) v.1 v.2‖ ≤ ‖v‖ := by
  rw [← SmoothCcTensor.norm_toL2]
  rw [SmoothCcTensor.toL2_apply,
    tensorHsSmoothRepr_toL2 (I := I) (M := M)
      (show (0 : Real) ≤ 1 by norm_num) v.1 v.2,
    tensorHsToL2_apply]
  exact tensorHs.norm_toL2Fun_ofCompact_le (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
    (show (0 : Real) ≤ 1 by norm_num) v.1

/-- A pointwise coefficient bound controls the finite-core multiplier norm,
uniformly in the spectral support. -/
theorem scalarPotCore_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖scalarPotCore (I := I) (M := M) q ζ v‖ ≤ C * ‖v‖ := by
  rw [scalarPotCore_apply, SmoothCcTensor.norm_toL2]
  calc
    _ ≤ C * ‖tensorHsSmoothRepr (I := I) (M := M) v.1 v.2‖ :=
      scalarSmul_norm_le (I := I) (M := M) q ζ hC hζ _
    _ ≤ C * ‖v‖ :=
      mul_le_mul_of_nonneg_left (finiteRepr_norm (I := I) (M := M) q v) hC

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [IsManifold I ∞ M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem exists_pot_bound
    (ζ : C^∞⟮I, M; Real⟯) :
    ∃ C : Real, 0 ≤ C ∧ ∀ x : M, |(ζ : M → Real) x| ≤ C := by
  classical
  have hcont : Continuous (fun x : M => |(ζ : M → Real) x|) :=
    continuous_abs.comp ζ.contMDiff.continuous
  have hcompact := (isCompact_univ (X := M)).image hcont
  obtain ⟨C₀, hC₀⟩ := hcompact.bddAbove
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  exact (hC₀ ⟨x, Set.mem_univ _, rfl⟩).trans (le_max_left _ _)

/-- Multiplication by a fixed smooth scalar coefficient, extended uniquely
from the dense finite spectral core to a bounded map `H¹(q) → L²(q)`. -/
noncomputable def scalarPotOp
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    tensorHs (I := I) (M := M) q 0 0 1 →L[Real] TensorL2 0 0 q :=
  (scalarPotCore (I := I) (M := M) q ζ).extendOfNorm
    (ScalarH1Core (I := I) (M := M) q).subtype

/-- On the finite spectral core, the bounded scalar potential operator is the
genuine pointwise smooth multiplier. -/
theorem scalarPotOp_core
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotOp (I := I) (M := M) q ζ v.1 =
      scalarPotCore (I := I) (M := M) q ζ v := by
  obtain ⟨C, hC, hζ⟩ := exists_pot_bound (I := I) (M := M) ζ
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply LinearMap.extendOfNorm_eq hdense
  refine ⟨C, ?_⟩
  intro w
  simpa only [Submodule.coe_subtype] using
    scalarPotCore_norm (I := I) (M := M) q ζ hC hζ w

/-- A pointwise coefficient bound controls the operator norm of the genuine
scalar potential multiplier. -/
theorem scalarPotOp_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C) (hζ : ∀ x : M, |(ζ : M → Real) x| ≤ C) :
    ‖scalarPotOp (I := I) (M := M) q ζ‖ ≤ C := by
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply LinearMap.opNorm_extendOfNorm_le hdense hC
  intro w
  simpa only [Submodule.coe_subtype] using
    scalarPotCore_norm (I := I) (M := M) q ζ hC hζ w

private noncomputable def scalarL2ToH0
    (q : SmoothRiemannianMetric I M) :
    TensorL2 0 0 q →ₗᵢ[Real] tensorHs (I := I) (M := M) q 0 0 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator
      (I := I) (M := M) q 0 0)).symm.toLinearIsometry

/-- The scalar potential multiplier with its `L²(q)` output identified
canonically and isometrically with spectral `H⁰(q)`. -/
noncomputable def scalarPotH0
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    tensorHs (I := I) (M := M) q 0 0 1 →L[Real]
      tensorHs (I := I) (M := M) q 0 0 0 :=
  (scalarL2ToH0 (I := I) (M := M) q).toContinuousLinearMap.comp
    (scalarPotOp (I := I) (M := M) q ζ)

omit [BoundarylessManifold I M] in
/-- Evaluation of the canonical `H¹(q) → H⁰(q)` scalar potential operator. -/
@[simp] theorem scalarPotH0_apply
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (v : tensorHs (I := I) (M := M) q 0 0 1) :
    scalarPotH0 (I := I) (M := M) q ζ v =
      (tensorHsZeroEquivL2 (I := I) (M := M)
        (tensorResolventL2_isCompactOperator
          (I := I) (M := M) q 0 0)).symm
        (scalarPotOp (I := I) (M := M) q ζ v) := rfl

/-- Testing the applied `H¹ → H⁰` multiplier against a finite spectral
vector is the same as moving the real scalar multiplier to the test vector. -/
theorem scalarPotH0_test
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯)
    (u : tensorHs (I := I) (M := M) q 0 0 1)
    (v : ScalarH1Core (I := I) (M := M) q) :
    inner Real
        (tensorHsZeroEquivL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (scalarPotH0 (I := I) (M := M) q ζ u))
        (tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (show (0 : Real) ≤ 1 by norm_num) v.1) =
      inner Real
        (tensorHsToL2 (I := I) (M := M)
          (tensorResolventL2_isCompactOperator
            (I := I) (M := M) q 0 0)
          (show (0 : Real) ≤ 1 by norm_num) u)
        (scalarPotCore (I := I) (M := M) q ζ v) := by
  let J := tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
  let inc := tensorHsToL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 0)
    (show (0 : Real) ≤ 1 by norm_num)
  have hdense :
      DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  change inner Real (J (scalarPotH0 (I := I) (M := M) q ζ u))
      (inc v.1) =
    inner Real (inc u) (scalarPotCore (I := I) (M := M) q ζ v)
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact ((innerSL Real).flip (inc v.1)).continuous.comp
      (J.continuous.comp
        (scalarPotH0 (I := I) (M := M) q ζ).continuous)
  · exact ((innerSL Real).flip
      (scalarPotCore (I := I) (M := M) q ζ v)).continuous.comp
        inc.continuous
  · intro w
    rw [scalarPotH0_apply, LinearIsometryEquiv.apply_symm_apply]
    change inner Real (scalarPotOp (I := I) (M := M) q ζ w.1)
        (inc v.1) =
      inner Real (inc w.1) (scalarPotCore (I := I) (M := M) q ζ v)
    rw [scalarPotOp_core]
    rw [← tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : Real) ≤ 1 by norm_num) v.1 v.2,
      ← tensorHsSmoothRepr_toL2 (I := I) (M := M)
        (show (0 : Real) ≤ 1 by norm_num) w.1 w.2,
      scalarPotCore_apply, scalarPotCore_apply]
    change inner Real
        (SmoothCcTensor.toL2
          (scalarSmul (I := I) (M := M) q 0 0 ζ
            (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2)))
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)) =
      inner Real
        (SmoothCcTensor.toL2
          (tensorHsSmoothRepr (I := I) (M := M) w.1 w.2))
        (SmoothCcTensor.toL2
          (scalarSmul (I := I) (M := M) q 0 0 ζ
            (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2)))
    rw [SmoothCcTensor.inner_toL2, SmoothCcTensor.inner_toL2]
    rw [SmoothCcTensor.inner_def, SmoothCcTensor.inner_def]
    unfold tensorL2Inner
    apply integral_congr_ae
    filter_upwards with x
    rw [scalarSmul_toFun_apply, scalarSmul_toFun_apply,
      tensorInnerPointwise_smul_left,
      tensorInnerPointwise_smul_right]

omit [BoundarylessManifold I M] in
/-- The canonical `L² ≃ H⁰` postcomposition preserves the multiplier norm. -/
theorem scalarPotH0_norm
    (q : SmoothRiemannianMetric I M) (ζ : C^∞⟮I, M; Real⟯) :
    ‖scalarPotH0 (I := I) (M := M) q ζ‖ =
      ‖scalarPotOp (I := I) (M := M) q ζ‖ := by
  unfold scalarPotH0
  exact (scalarL2ToH0 (I := I) (M := M) q).norm_toContinuousLinearMap_comp

omit [BoundarylessManifold I M] in
private theorem scalarPotCore_sub
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    (v : ScalarH1Core (I := I) (M := M) q) :
    scalarPotCore (I := I) (M := M) q ζ v -
        scalarPotCore (I := I) (M := M) q η v =
      scalarPotCore (I := I) (M := M) q (ζ - η) v := by
  rw [scalarPotCore_apply, scalarPotCore_apply, scalarPotCore_apply, ← map_sub]
  congr 1
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  change (ζ : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x -
      (η : M → Real) x •
        (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x =
    ((ζ : M → Real) x - (η : M → Real) x) •
      (tensorHsSmoothRepr (I := I) (M := M) v.1 v.2).toSection x
  exact (sub_smul _ _ _).symm

/-- A pointwise bound on the coefficient difference controls the finite-core
pairwise multiplier difference. -/
theorem scalarPot_pair_core
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C)
    (v : ScalarH1Core (I := I) (M := M) q) :
    ‖scalarPotCore (I := I) (M := M) q ζ v -
        scalarPotCore (I := I) (M := M) q η v‖ ≤ C * ‖v‖ := by
  rw [scalarPotCore_sub]
  apply scalarPotCore_norm (I := I) (M := M) q (ζ - η) hC
  intro x
  change |(ζ : M → Real) x - (η : M → Real) x| ≤ C
  exact hζη x

/-- The operator norm of a pairwise scalar-potential difference is controlled
by the pointwise coefficient difference, without whole-operator equality. -/
theorem scalarPot_pair_norm
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C) :
    ‖scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η‖ ≤ C := by
  have hdense : DenseRange (ScalarH1Core (I := I) (M := M) q).subtype :=
    (tensorHsFiniteSupportSubmodule_dense
      (I := I) (M := M) (g := q) (r := 0) (s := 0) (σ := 1)).denseRange_val
  apply (scalarPotOp (I := I) (M := M) q ζ -
    scalarPotOp (I := I) (M := M) q η).opNorm_le_bound hC
  intro u
  refine hdense.induction_on u ?_ ?_
  · exact isClosed_le
      (scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η).continuous.norm
      (continuous_const.mul continuous_norm)
  · intro v
    rw [ContinuousLinearMap.sub_apply]
    simp only [Submodule.coe_subtype]
    rw [scalarPotOp_core (I := I) (M := M) q ζ v,
      scalarPotOp_core (I := I) (M := M) q η v]
    exact scalarPot_pair_core (I := I) (M := M) q ζ η hC hζη v

/-- The same pointwise coefficient-difference bound controls the canonical
`H¹(q) → H⁰(q)` scalar-potential difference. -/
theorem scalarPotH0_pair
    (q : SmoothRiemannianMetric I M) (ζ η : C^∞⟮I, M; Real⟯)
    {C : Real} (hC : 0 ≤ C)
    (hζη : ∀ x : M, |(ζ : M → Real) x - (η : M → Real) x| ≤ C) :
    ‖scalarPotH0 (I := I) (M := M) q ζ -
        scalarPotH0 (I := I) (M := M) q η‖ ≤ C := by
  apply (scalarPotH0 (I := I) (M := M) q ζ -
    scalarPotH0 (I := I) (M := M) q η).opNorm_le_bound hC
  intro u
  rw [ContinuousLinearMap.sub_apply]
  change ‖(scalarL2ToH0 (I := I) (M := M) q)
          (scalarPotOp (I := I) (M := M) q ζ u) -
        (scalarL2ToH0 (I := I) (M := M) q)
          (scalarPotOp (I := I) (M := M) q η u)‖ ≤ C * ‖u‖
  rw [← map_sub, LinearIsometry.norm_map]
  change ‖(scalarPotOp (I := I) (M := M) q ζ -
      scalarPotOp (I := I) (M := M) q η) u‖ ≤ C * ‖u‖
  calc
    _ ≤ ‖scalarPotOp (I := I) (M := M) q ζ -
          scalarPotOp (I := I) (M := M) q η‖ * ‖u‖ :=
      (scalarPotOp (I := I) (M := M) q ζ -
        scalarPotOp (I := I) (M := M) q η).le_opNorm u
    _ ≤ C * ‖u‖ := mul_le_mul_of_nonneg_right
      (scalarPot_pair_norm (I := I) (M := M) q ζ η hC hζη) (norm_nonneg u)

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
