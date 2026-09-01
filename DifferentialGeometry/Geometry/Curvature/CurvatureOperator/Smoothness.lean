import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.EndomorphismNaturality
import DifferentialGeometry.Tensor.Alternating.Section
import DifferentialGeometry.Tensor.RSTensor.MetricTrace.NablaTraceGen
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Bundle.SmoothSubbundle.Range
import DifferentialGeometry.Geometry.Connection.Realization.SmoothSections

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection.Realization
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

noncomputable local instance twoFormModelFiniteDimensional :
    FiniteDimensional Real (E [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real E)).finiteDimensional_of_finite

noncomputable local instance twoFormFiniteDimensionalSmoothness (x : M) :
    FiniteDimensional Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

private def curvatureOperatorInterleave : Fin 6 ≃ Fin 6 :=
  Equiv.ofBijective ![0, 2, 4, 5, 1, 3] (by decide)

private def curvatureOperatorSlotEquiv {Idx : Type*} :
    (Fin 4 → Idx) ≃ Idx × Idx × (Fin 2 → Idx) where
  toFun s := (s 0, s 1, ![s 2, s 3])
  invFun p := ![p.1, p.2.1, p.2.2 0, p.2.2 1]
  left_inv s := by
    funext i
    fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨i, j, tail⟩
    apply Prod.ext
    · simp
    apply Prod.ext
    · simp
    · funext q
      fin_cases q <;> simp

private theorem sum_curvatureOperatorSlotEquiv
    {Idx : Type*} [Fintype Idx]
    (f : (Fin 4 → Idx) → Real) :
    ∑ slots : Fin 4 → Idx, f slots =
      ∑ i : Idx, ∑ j : Idx, ∑ tail : Fin 2 → Idx,
        f ![i, j, tail 0, tail 1] := by
  classical
  have h := Equiv.sum_comp (curvatureOperatorSlotEquiv (Idx := Idx))
    (fun p => f (curvatureOperatorSlotEquiv.symm p))
  simp only [Equiv.symm_apply_apply] at h
  rw [h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

private noncomputable def curvatureOperatorContractedTensorAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    Tensor0SSpace 2 I x :=
  (-1 / 2 : Real) •
    metricTraceFirstTwo0STensor (I := I) g
      (metricTraceFirstTwo0STensor (I := I) g
        ((Tensor0SSpace.product A (twoFormTensorAt (I := I) a)).domDomCongr
          curvatureOperatorInterleave))

omit [CompleteSpace E] [T2Space M] in
private theorem metricTraceFirstTwo0STensor_eq_sum_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    {s : ℕ} (T : Tensor0SSpace (s + 2) I x)
    (tail : Fin s → TangentSpace I x) :
    metricTraceFirstTwo0STensor (I := I) g T tail =
      ∑ i : Idx, T (metricTraceInput (I := I) (basis i) (basis i) tail) := by
  rw [metricTraceFirstTwo0STensor_apply,
    metricTraceFirstTwo0SAt_eq_sum_basis (I := I) g basis
      (identityInvMetric (Idx := Idx))
      (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth)]
  unfold metricTrace0S2InBasis
  simp [identityInvMetric, diagonalInvMetric]

omit [CompleteSpace E] [T2Space M] in
private theorem tensor0SFieldProduct_apply_local
    {s q : ℕ}
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) s)
    (B : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) q)
    (x : M) :
    tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x =
      Tensor0SSpace.product (A x) (B x) := by
  apply tensor0SSpace_ext (s + q) x
  intro v
  change tensor0SSpaceFiberContinuousLinearEquiv (I := I) (s + q) x
      (tensor0SFieldProduct (∞ : WithTop ℕ∞) A B x) v = _
  unfold tensor0SFieldProduct MultilinearSection.product
  change Bundle.continuousMultilinearMap.productFun
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) s x (A x))
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) q x (B x)) v = _
  rw [Bundle.continuousMultilinearMap.product_fun_apply,
    Tensor0SSpace.product_apply]
  simp only [tensor0SSpaceFiberContinuousLinearEquiv_apply_apply]

omit [FiniteDimensional Real E] [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorInterleavedProduct_traceInput_apply
    {x : M} (A : Tensor0SSpace 4 I x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real)
    (U V : TangentSpace I x) (tail : Fin 2 → TangentSpace I x) :
    ((Tensor0SSpace.product A (twoFormTensorAt (I := I) a)).domDomCongr
        curvatureOperatorInterleave)
        (metricTraceInput (I := I) U U
          (metricTraceInput (I := I) V V tail)) =
      A ![U, V, tail 0, tail 1] * a ![U, V] := by
  have hslots :
      metricTraceInput (I := I) U U
          (metricTraceInput (I := I) V V tail) =
        ![U, U, V, V, tail 0, tail 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hslots]
  rw [Tensor0SSpace.domDomCongr_apply, Tensor0SSpace.product_apply]
  change A _ * a _ = A ![U, V, tail 0, tail 1] * a ![U, V]
  congr 1
  · congr 1
    funext i
    fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedTensorAt_apply_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (A : Tensor0SSpace 4 I x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real)
    (tail : Fin 2 → TangentSpace I x) :
    curvatureOperatorContractedTensorAt (I := I) g x A a tail =
      (-1 / 2 : Real) * ∑ i : Idx, ∑ j : Idx,
        A ![basis i, basis j, tail 0, tail 1] * a ![basis i, basis j] := by
  unfold curvatureOperatorContractedTensorAt
  rw [Tensor0SSpace.smul_apply]
  rw [metricTraceFirstTwo0STensor_eq_sum_orthonormal
    (I := I) g x basis horth]
  change (-1 / 2 : Real) * _ = _
  refine congrArg (fun z => (-1 / 2 : Real) * z) ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [metricTraceFirstTwo0STensor_eq_sum_orthonormal
    (I := I) g x basis horth]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact curvatureOperatorInterleavedProduct_traceInput_apply
    (I := I) A a (basis i) (basis j) tail

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorPairingAt_eq_sum_orthonormal
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorPairingAt (I := I) g x A a b =
      -(1 / 2 : Real) * ∑ i : Idx, ∑ j : Idx,
        ∑ tail : Fin 2 → Idx,
          (A : Tensor0SSpace 4 I x)
              ![basis i, basis j, basis (tail 0), basis (tail 1)] *
            a ![basis i, basis j] *
            b ![basis (tail 0), basis (tail 1)] := by
  rw [curvatureOperatorPairingAt,
    Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 4 basis
      (metricInverseInBasis_identity_of_orthonormal (I := I) g basis horth),
    sum_curvatureOperatorSlotEquiv]
  refine congrArg (fun z => -(1 / 2 : Real) * z) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun tail _ => ?_
  simp only [component0S_apply]
  rw [Tensor0SSpace.product_apply]
  let v : Fin 4 → TangentSpace I x :=
    fun q => basis (![i, j, tail 0, tail 1] q)
  change (A : Tensor0SSpace 4 I x) v *
      (twoFormTensorAt (I := I) a (v ∘ Fin.castAdd 2) *
        twoFormTensorAt (I := I) b (v ∘ Fin.natAdd 2)) = _
  have hv : v = ![basis i, basis j, basis (tail 0), basis (tail 1)] := by
    funext q
    fin_cases q <;> rfl
  rw [hv]
  change (A : Tensor0SSpace 4 I x)
      ![basis i, basis j, basis (tail 0), basis (tail 1)] *
      (a ((![basis i, basis j, basis (tail 0), basis (tail 1)] :
          Fin 4 → TangentSpace I x) ∘ Fin.castAdd 2) *
        b ((![basis i, basis j, basis (tail 0), basis (tail 1)] :
          Fin 4 → TangentSpace I x) ∘ Fin.natAdd 2)) = _
  have hfirst :
      ((![basis i, basis j, basis (tail 0), basis (tail 1)] :
          Fin 4 → TangentSpace I x) ∘ Fin.castAdd 2) =
        ![basis i, basis j] := by
    funext q
    fin_cases q <;> rfl
  have hlast :
      ((![basis i, basis j, basis (tail 0), basis (tail 1)] :
          Fin 4 → TangentSpace I x) ∘ Fin.natAdd 2) =
        ![basis (tail 0), basis (tail 1)] := by
    funext q
    fin_cases q <;> rfl
  rw [hfirst, hlast]
  ring

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedTensorAt_skew
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real)
    (X Y : TangentSpace I x) :
    curvatureOperatorContractedTensorAt (I := I) g x A a ![X, Y] =
      -curvatureOperatorContractedTensorAt (I := I) g x A a ![Y, X] := by
  classical
  let addV : AddCommGroup (TangentSpace I x) := inferInstance
  let modV : Module Real (TangentSpace I x) := inferInstance
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ addV modV D.toCore
  let : AddCommGroup (TangentSpace I x) := addV
  let : Module Real (TangentSpace I x) := modV
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let basis := stdOrthonormalBasis Real (TangentSpace I x)
  have horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    change D.inner (basis i) (basis j) = if i = j then (1 : Real) else 0
    rw [← D.toCore_inner]
    exact basis.inner_eq_ite i j
  rw [curvatureOperatorContractedTensorAt_apply_orthonormal
      (I := I) g x basis.toBasis horth,
    curvatureOperatorContractedTensorAt_apply_orthonormal
      (I := I) g x basis.toBasis horth]
  have hlast := (mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp hA).2.1
  have hsum :
      (∑ i, ∑ j,
          A ![basis i, basis j, X, Y] * a ![basis i, basis j]) =
        -∑ i, ∑ j,
          A ![basis i, basis j, Y, X] * a ![basis i, basis j] := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hij := hlast (basis i) (basis j) X Y
    unfold tensor04StdAt at hij
    have hvecXY : ![basis i, basis j, X, Y] =
        vec4 (I := I) (basis i) (basis j) X Y := by
      funext q
      fin_cases q <;> rfl
    have hvecYX : ![basis i, basis j, Y, X] =
        vec4 (I := I) (basis i) (basis j) Y X := by
      funext q
      fin_cases q <;> rfl
    rw [hvecXY, hvecYX, hij]
    ring
  change (-1 / 2 : Real) *
      (∑ i, ∑ j, A ![basis i, basis j, X, Y] * a ![basis i, basis j]) =
    -((-1 / 2 : Real) *
      (∑ i, ∑ j, A ![basis i, basis j, Y, X] * a ![basis i, basis j]))
  rw [hsum]
  ring

private noncomputable def curvatureOperatorContractedFormAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    TangentSpace I x [⋀^Fin 2]→L[Real] Real :=
  ContinuousAlternatingMap.mk
    (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
      (curvatureOperatorContractedTensorAt (I := I) g x A a))
    (by
      intro v i j hv hij
      have h01 : v 0 = v 1 := by
        fin_cases i <;> fin_cases j <;> simp_all
      have hs := curvatureOperatorContractedTensorAt_skew
        (I := I) g x A hA a (v 0) (v 1)
      rw [h01] at hs
      have hvect : v = ![v 0, v 1] := by
        funext q
        fin_cases q <;> rfl
      change curvatureOperatorContractedTensorAt (I := I) g x A a v = 0
      rw [hvect, h01]
      linarith)

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedFormAt_toMultilinear
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    (curvatureOperatorContractedFormAt (I := I) g x A hA a).toContinuousMultilinearMap =
      tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
        (curvatureOperatorContractedTensorAt (I := I) g x A a) :=
  rfl

private noncomputable def twoFormTensorSection
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2) :
    Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 2 := by
  letI := tensor0SBundleTopology (I := I) (M := M) 2
  exact a.toMultilinearSection

omit [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorSection_apply
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2)
    (x : M) :
    twoFormTensorSection (I := I) a x = twoFormTensorAt (I := I) (a x) := by
  unfold twoFormTensorSection AlternatingSection.toMultilinearSection twoFormTensorAt
  rfl

private noncomputable def curvatureOperatorContractedSection
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2) :
    MultilinearSection Real E I (TangentSpace I : M → Type _) ∞ 2 :=
  (-1 / 2 : Real) •
    metricTraceFirstTwoField (I := I) (M := M) g
      (metricTraceFirstTwoField (I := I) (M := M) g
        (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvatureOperatorInterleave
          (tensor0SFieldProduct (∞ : WithTop ℕ∞) A
            (twoFormTensorSection (I := I) a))))

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedSection_apply
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2)
    (x : M) :
    curvatureOperatorContractedSection (I := I) g A a x =
      curvatureOperatorContractedTensorAt (I := I) g x (A x) (a x) := by
  unfold curvatureOperatorContractedSection curvatureOperatorContractedTensorAt
  change (-1 / 2 : Real) •
      metricTraceFirstTwoField (I := I) (M := M) g
        (metricTraceFirstTwoField (I := I) (M := M) g
          (Tensor0SField.domDomCongr (∞ : WithTop ℕ∞) curvatureOperatorInterleave
            (tensor0SFieldProduct (∞ : WithTop ℕ∞) A
              (twoFormTensorSection (I := I) a)))) x = _
  rw [metricTraceFirstTwoField_apply, metricTraceFirstTwoField_apply,
    Tensor0SField.domDomCongr_apply]
  rw [tensor0SFieldProduct_apply_local, twoFormTensorSection_apply]

private noncomputable def curvatureOperatorAppliedSection
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2) :
    AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2 :=
  (curvatureOperatorContractedSection (I := I) g A a).alternatization

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorAppliedSection_apply
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : AlternatingSection Real E I (TangentSpace I : M → Type _) ∞ 2)
    (x : M) :
    curvatureOperatorAppliedSection (I := I) g A a x =
      curvatureOperatorContractedFormAt (I := I) g x (A x) (hA x) (a x) := by
  unfold curvatureOperatorAppliedSection
  rw [MultilinearSection.alternatization_apply]
  change ContinuousMultilinearMap.alternatizationCLM
      (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
        (curvatureOperatorContractedSection (I := I) g A a x)) = _
  rw [curvatureOperatorContractedSection_apply]
  rw [← curvatureOperatorContractedFormAt_toMultilinear]
  exact ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap _

omit [CompleteSpace E] [T2Space M] in
private theorem twoFormTensorAt_curvatureOperatorContractedFormAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    twoFormTensorAt (I := I)
        (curvatureOperatorContractedFormAt (I := I) g x A hA a) =
      curvatureOperatorContractedTensorAt (I := I) g x A a := by
  apply tensor0SSpace_ext 2 x
  intro v
  change (tensor0SSpaceFiberContinuousLinearEquiv (I := I) 2 x
      (curvatureOperatorContractedTensorAt (I := I) g x A a)) v = _
  exact tensor0SSpaceFiberContinuousLinearEquiv_apply_apply
    (I := I) (M := M) 2 x
    (curvatureOperatorContractedTensorAt (I := I) g x A a) v

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedTensorAt_pairing
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a b : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    inner0S (I := I) g x 2
        (curvatureOperatorContractedTensorAt (I := I) g x A a)
        (twoFormTensorAt (I := I) b) =
      curvatureOperatorPairingAt (I := I) g x ⟨A, hA⟩ a b := by
  classical
  let addV : AddCommGroup (TangentSpace I x) := inferInstance
  let modV : Module Real (TangentSpace I x) := inferInstance
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ addV modV D.toCore
  let : AddCommGroup (TangentSpace I x) := addV
  let : Module Real (TangentSpace I x) := modV
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let basis := stdOrthonormalBasis Real (TangentSpace I x)
  have horth : ∀ i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    change D.inner (basis i) (basis j) = if i = j then (1 : Real) else 0
    rw [← D.toCore_inner]
    exact basis.inner_eq_ite i j
  have hinv := metricInverseInBasis_identity_of_orthonormal
    (I := I) g basis.toBasis horth
  have hleft :
      inner0S (I := I) g x 2
          (curvatureOperatorContractedTensorAt (I := I) g x A a)
          (twoFormTensorAt (I := I) b) =
        (-1 / 2 : Real) *
          ∑ tail : Fin 2 → Fin (Module.finrank Real (TangentSpace I x)),
            ∑ i, ∑ j,
              A ![basis i, basis j, basis (tail 0), basis (tail 1)] *
                a ![basis i, basis j] *
                b ![basis (tail 0), basis (tail 1)] := by
    rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 2 basis.toBasis hinv]
    simp only [component0S_apply, twoFormTensorAt_apply]
    simp_rw [curvatureOperatorContractedTensorAt_apply_orthonormal
      (I := I) g x basis.toBasis horth]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun tail _ => ?_
    have hb : (fun q : Fin 2 => basis.toBasis (tail q)) =
        ![basis (tail 0), basis (tail 1)] := by
      funext q
      fin_cases q <;> rfl
    rw [hb]
    have hsum :
        (∑ i, ∑ j,
            A ![basis.toBasis i, basis.toBasis j,
                basis.toBasis (tail 0), basis.toBasis (tail 1)] *
              a ![basis.toBasis i, basis.toBasis j]) =
          ∑ i, ∑ j,
            A ![basis i, basis j, basis (tail 0), basis (tail 1)] *
              a ![basis i, basis j] := by
      rfl
    rw [hsum]
    calc
      ((-1 / 2 : Real) * ∑ i, ∑ j,
            A ![basis i, basis j,
                basis (tail 0), basis (tail 1)] *
              a ![basis i, basis j]) *
          b ![basis (tail 0), basis (tail 1)] =
        (-1 / 2 : Real) *
          ((∑ i, ∑ j,
              A ![basis i, basis j, basis (tail 0), basis (tail 1)] *
                a ![basis i, basis j]) *
            b ![basis (tail 0), basis (tail 1)]) := by ring
      _ = _ := by
        rw [Finset.sum_mul]
        refine congrArg (fun z => (-1 / 2 : Real) * z) ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
  rw [hleft, curvatureOperatorPairingAt_eq_sum_orthonormal
    (I := I) g x basis.toBasis horth]
  rw [show (-1 / 2 : Real) = -(1 / 2 : Real) by ring]
  rw [Finset.sum_comm]
  refine congrArg (fun z => -(1 / 2 : Real) * z) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun tail _ => ?_
  rfl

omit [CompleteSpace E] [T2Space M] in
private theorem curvatureOperatorContractedFormAt_eq_endomorphism
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : Tensor0SSpace 4 I x)
    (hA : A ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    curvatureOperatorContractedFormAt (I := I) g x A hA a =
      curvatureOperatorEndomorphismAt (I := I) g x ⟨A, hA⟩ a := by
  apply (twoFormMetricData (I := I) g x).flat.injective
  ext b
  change (twoFormMetricData (I := I) g x).inner
      (curvatureOperatorContractedFormAt (I := I) g x A hA a) b =
    (twoFormMetricData (I := I) g x).inner
      (curvatureOperatorEndomorphismAt (I := I) g x ⟨A, hA⟩ a) b
  rw [twoFormMetricData_inner, twoFormTensorAt_curvatureOperatorContractedFormAt,
    curvatureOperatorContractedTensorAt_pairing,
    twoFormMetricData_inner_curvatureOperatorEndomorphismAt]

noncomputable def curvatureOperatorEndomorphismField
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ∀ x : M, (TangentSpace I x [⋀^Fin 2]→L[Real] Real) →L[Real]
      TangentSpace I x [⋀^Fin 2]→L[Real] Real :=
  fun x => curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩

omit [CompleteSpace E] [T2Space M] in
@[simp] theorem curvatureOperatorEndomorphismField_apply
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (x : M) :
    curvatureOperatorEndomorphismField (I := I) g A hA x =
      curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩ :=
  rfl

omit [CompleteSpace E] in
theorem curvatureOperatorEndomorphismField_contMDiff
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    ContMDiff I
      (I.prod 𝓘(Real,
        (E [⋀^Fin 2]→L[Real] Real) →L[Real] E [⋀^Fin 2]→L[Real] Real)) ∞
      (fun x => TotalSpace.mk'
        ((E [⋀^Fin 2]→L[Real] Real) →L[Real] E [⋀^Fin 2]→L[Real] Real)
        (E := fun y : M =>
          (TangentSpace I y [⋀^Fin 2]→L[Real] Real) →L[Real]
            TangentSpace I y [⋀^Fin 2]→L[Real] Real)
        x (curvatureOperatorEndomorphismField (I := I) g A hA x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E [⋀^Fin 2]→L[Real] Real)
    (V₁ := fun y : M => TangentSpace I y [⋀^Fin 2]→L[Real] Real)
    (F₂ := E [⋀^Fin 2]→L[Real] Real)
    (V₂ := fun y : M => TangentSpace I y [⋀^Fin 2]→L[Real] Real)
    (φ := curvatureOperatorEndomorphismField (I := I) g A hA)
  intro a
  refine (curvatureOperatorAppliedSection (I := I) g A a).contMDiff.congr ?_
  intro x
  rw [curvatureOperatorEndomorphismField_apply,
    curvatureOperatorAppliedSection_apply,
    curvatureOperatorContractedFormAt_eq_endomorphism]

noncomputable def curvatureOperatorImageSubbundle
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (k : ℕ)
    (hrank : ∀ x, Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = k) :
    ContMDiffVectorSubbundle
      (I := I) (F := E [⋀^Fin 2]→L[Real] Real)
      (V := fun x : M => TangentSpace I x [⋀^Fin 2]→L[Real] Real)
      (n := (∞ : WithTop ℕ∞)) :=
  ContMDiffVectorSubbundle.range
    (curvatureOperatorEndomorphismField (I := I) g A hA)
    (curvatureOperatorEndomorphismField_contMDiff (I := I) g A hA)
    k (by
      intro x
      rw [curvatureOperatorEndomorphismField_apply]
      exact hrank x)

omit [CompleteSpace E] in
@[simp] theorem curvatureOperatorImageSubbundle_fiber
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (k : ℕ)
    (hrank : ∀ x, Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = k)
    (x : M) :
    (curvatureOperatorImageSubbundle (I := I) g A hA k hrank).fiber x =
      curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩ := by
  rw [curvatureOperatorImageSubbundle,
    ContMDiffVectorSubbundle.range_fiber,
    curvatureOperatorEndomorphismField_apply]
  rfl

omit [CompleteSpace E] in
@[simp] theorem curvatureOperatorImageSubbundle_rank
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (k : ℕ)
    (hrank : ∀ x, Module.finrank Real
      (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = k) :
    (curvatureOperatorImageSubbundle (I := I) g A hA k hrank).rank = k := by
  rw [curvatureOperatorImageSubbundle,
    ContMDiffVectorSubbundle.range_rank]

end DifferentialGeometry.Geometry.Curvature
