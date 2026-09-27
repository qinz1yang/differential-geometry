import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Kernel
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorNormalization
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Tensor.Alternating.Coordinates.Basis

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open Bundle
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

private def bivectorOrderEmbedding3 (i : Fin 3) : Fin 2 ↪o Fin 3 :=
  if i = 0 then Fin.castSuccOrderEmb
  else if i = 1 then Fin.succAboveOrderEmb (1 : Fin 3)
  else Fin.succOrderEmb 2

private def bivectorOrderEquiv3 : Fin 3 ≃ (Fin 2 ↪o Fin 3) :=
  Equiv.ofBijective bivectorOrderEmbedding3 (by
    rw [Fintype.bijective_iff_injective_and_card]
    constructor
    · intro i j h
      have h0 := congrArg (fun e : Fin 2 ↪o Fin 3 => e 0) h
      have h1 := congrArg (fun e : Fin 2 ↪o Fin 3 => e 1) h
      fin_cases i <;> fin_cases j <;>
        simp [bivectorOrderEmbedding3, Fin.succAbove] at h0 h1 ⊢
    · rw [Fintype.card_congr
        (Set.powersetCard.ofFinEmbEquiv (I := Fin 3) (n := 2))]
      simpa using (Set.powersetCard.card (α := Fin 3) (n := 2)).symm)

noncomputable def curvatureTwoFormBasisAt {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) :
    Module.Basis (Fin 3) Real
      (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2) basis).reindex
    bivectorOrderEquiv3.symm

omit [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
@[simp] theorem curvatureTwoFormBasisAt_apply {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i : Fin 3) :
    curvatureTwoFormBasisAt (I := I) basis i =
      ContinuousAlternatingMap.elementaryCovector basis.cDualBasis
        (bivectorOrderEmbedding3 i) := by
  rw [curvatureTwoFormBasisAt, Module.Basis.reindex_apply,
    ContinuousAlternatingMap.elementaryCovectorBasis_apply]
  rfl

private def curvatureKernelSlots4 (i j k l : Fin 3) : Fin 4 → Fin 3 :=
  ![i, j, k, l]

private def curvatureKernelSlots4Equiv :
    (Fin 4 → Fin 3) ≃ (((Fin 3 × Fin 3) × Fin 3) × Fin 3) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := curvatureKernelSlots4 p.1.1.1 p.1.1.2 p.1.2 p.2
  left_inv f := by
    funext a
    fin_cases a <;> simp [curvatureKernelSlots4]
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    simp [curvatureKernelSlots4]

private theorem curvatureKernel_sum_slots4
    {R : Type*} [AddCommMonoid R] (f : (Fin 4 → Fin 3) → R) :
    (∑ s : Fin 4 → Fin 3, f s) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
        f (curvatureKernelSlots4 i j k l) := by
  classical
  rw [Fintype.sum_equiv curvatureKernelSlots4Equiv f
    (fun p => f (curvatureKernelSlots4 p.1.1.1 p.1.1.2 p.1.2 p.2))]
  · repeat rw [Fintype.sum_prod_type]
  · intro s
    change f s = f (curvatureKernelSlots4Equiv.symm (curvatureKernelSlots4Equiv s))
    rw [Equiv.symm_apply_apply]

private theorem curvatureKernel_sum_fin3
    {R : Type*} [AddCommMonoid R] (f : Fin 3 -> R) :
    (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [add_assoc]

private theorem curvatureKernel_sum_four_by_pairs
    (f : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real)
    (hij : forall i j k l : Fin 3, f i j k l = f j i k l)
    (hkl : forall i j k l : Fin 3, f i j k l = f i j l k)
    (hdi : forall i (_ : Fin 3) k l, f i i k l = 0)
    (hdj : forall i j k (_ : Fin 3), f i j k k = 0) :
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
      4 * (∑ p, ∑ q,
        f (DimensionThree.bivectorIndex3 p).1
          (DimensionThree.bivectorIndex3 p).2
          (DimensionThree.bivectorIndex3 q).2
          (DimensionThree.bivectorIndex3 q).1) := by
  classical
  have hkl2 : forall i j,
      (∑ k, ∑ l, f i j k l) =
        2 * (∑ q, f i j (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2) := by
    intro i j
    rw [curvatureKernel_sum_fin3 (fun k => ∑ l, f i j k l)]
    rw [curvatureKernel_sum_fin3 (fun l => f i j 0 l),
      curvatureKernel_sum_fin3 (fun l => f i j 1 l),
      curvatureKernel_sum_fin3 (fun l => f i j 2 l)]
    rw [curvatureKernel_sum_fin3 (fun q =>
      f i j (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2)]
    rw [hkl i j 1 0, hkl i j 2 0, hkl i j 2 1,
      hdj i j 0 0, hdj i j 1 1, hdj i j 2 2]
    simp [DimensionThree.bivectorIndex3]
    ring
  have hij2 : forall q,
      (∑ i, ∑ j, f i j (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2) =
        2 * (∑ p, f (DimensionThree.bivectorIndex3 p).1
          (DimensionThree.bivectorIndex3 p).2
          (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2) := by
    intro q
    rw [curvatureKernel_sum_fin3 (fun i => ∑ j,
      f i j (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2)]
    rw [curvatureKernel_sum_fin3 (fun j =>
      f 0 j (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2),
      curvatureKernel_sum_fin3 (fun j =>
        f 1 j (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2),
      curvatureKernel_sum_fin3 (fun j =>
        f 2 j (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2)]
    rw [curvatureKernel_sum_fin3 (fun p =>
      f (DimensionThree.bivectorIndex3 p).1
        (DimensionThree.bivectorIndex3 p).2
        (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2)]
    rw [hij 1 0 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2,
      hij 2 0 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2,
      hij 2 1 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2,
      hdi 0 0 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2,
      hdi 1 1 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2,
      hdi 2 2 (DimensionThree.bivectorIndex3 q).1
        (DimensionThree.bivectorIndex3 q).2]
    simp [DimensionThree.bivectorIndex3]
    ring
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, f i j k l) =
        ∑ i, ∑ j, 2 * (∑ q,
          f i j (DimensionThree.bivectorIndex3 q).1
            (DimensionThree.bivectorIndex3 q).2) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro j _
      exact hkl2 i j
    _ = 2 * (∑ i, ∑ j, ∑ q,
        f i j (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.mul_sum]
    _ = 2 * (∑ q, ∑ i, ∑ j,
        f i j (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2) := by
      have h1 : (∑ i, ∑ j, ∑ q,
          f i j (DimensionThree.bivectorIndex3 q).1
            (DimensionThree.bivectorIndex3 q).2) =
          ∑ i, ∑ q, ∑ j,
            f i j (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2 := by
        refine Finset.sum_congr rfl ?_
        intro i _
        simpa using (Finset.sum_comm :
          (∑ j : Fin 3, ∑ q : Fin 3,
            f i j (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2) =
          ∑ q : Fin 3, ∑ j : Fin 3,
            f i j (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2)
      have h2 : (∑ i, ∑ q, ∑ j,
          f i j (DimensionThree.bivectorIndex3 q).1
            (DimensionThree.bivectorIndex3 q).2) =
          ∑ q, ∑ i, ∑ j,
            f i j (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2 := by
        simpa using (Finset.sum_comm
          (s := (Finset.univ : Finset (Fin 3)))
          (t := (Finset.univ : Finset (Fin 3)))
          (f := fun i q => ∑ j,
            f i j (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2))
      rw [h1, h2]
    _ = 2 * (∑ q, 2 * (∑ p,
        f (DimensionThree.bivectorIndex3 p).1
          (DimensionThree.bivectorIndex3 p).2
          (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2)) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro q _
      exact hij2 q
    _ = 4 * (∑ p, ∑ q,
        f (DimensionThree.bivectorIndex3 p).1
          (DimensionThree.bivectorIndex3 p).2
          (DimensionThree.bivectorIndex3 q).1
          (DimensionThree.bivectorIndex3 q).2) := by
      calc
        2 * (∑ q, 2 * (∑ p,
            f (DimensionThree.bivectorIndex3 p).1
              (DimensionThree.bivectorIndex3 p).2
              (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2)) =
            ∑ q, 2 * (2 * (∑ p,
              f (DimensionThree.bivectorIndex3 p).1
                (DimensionThree.bivectorIndex3 p).2
                (DimensionThree.bivectorIndex3 q).1
                (DimensionThree.bivectorIndex3 q).2)) := by
          rw [Finset.mul_sum]
        _ = ∑ q, 4 * (∑ p,
            f (DimensionThree.bivectorIndex3 p).1
              (DimensionThree.bivectorIndex3 p).2
              (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          ring
        _ = ∑ q, ∑ p, 4 *
            f (DimensionThree.bivectorIndex3 p).1
              (DimensionThree.bivectorIndex3 p).2
              (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2 := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [Finset.mul_sum]
        _ = 4 * (∑ p, ∑ q,
            f (DimensionThree.bivectorIndex3 p).1
              (DimensionThree.bivectorIndex3 p).2
              (DimensionThree.bivectorIndex3 q).1
              (DimensionThree.bivectorIndex3 q).2) := by
          calc
            (∑ q, ∑ p, 4 *
                f (DimensionThree.bivectorIndex3 p).1
                  (DimensionThree.bivectorIndex3 p).2
                  (DimensionThree.bivectorIndex3 q).1
                  (DimensionThree.bivectorIndex3 q).2) =
                ∑ q, 4 * (∑ p,
                  f (DimensionThree.bivectorIndex3 p).1
                    (DimensionThree.bivectorIndex3 p).2
                    (DimensionThree.bivectorIndex3 q).1
                    (DimensionThree.bivectorIndex3 q).2) := by
              refine Finset.sum_congr rfl ?_
              intro q _
              rw [Finset.mul_sum]
            _ = 4 * (∑ q, ∑ p,
                f (DimensionThree.bivectorIndex3 p).1
                  (DimensionThree.bivectorIndex3 p).2
                  (DimensionThree.bivectorIndex3 q).1
                  (DimensionThree.bivectorIndex3 q).2) := by
              rw [← Finset.mul_sum]
            _ = 4 * (∑ p, ∑ q,
                f (DimensionThree.bivectorIndex3 p).1
                  (DimensionThree.bivectorIndex3 p).2
                  (DimensionThree.bivectorIndex3 q).1
                  (DimensionThree.bivectorIndex3 q).2) := by
              rw [Finset.sum_comm]
    _ = 4 * (∑ p, ∑ q,
        f (DimensionThree.bivectorIndex3 p).1
          (DimensionThree.bivectorIndex3 p).2
          (DimensionThree.bivectorIndex3 q).2
          (DimensionThree.bivectorIndex3 q).1) := by
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      exact hkl _ _ _ _

omit [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem curvatureTwoFormBasisAt_ordered_apply {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i p : Fin 3) :
    (curvatureTwoFormBasisAt (I := I) basis i)
        (basis ∘ bivectorOrderEmbedding3 p) =
      if i = p then 1 else 0 := by
  rw [curvatureTwoFormBasisAt_apply,
    ContinuousAlternatingMap.elementaryCovector_basis_eval
      basis basis.cDualBasis basis.cDualBasis_apply_self]
  by_cases hip : i = p
  · subst p
    rw [if_pos rfl]
    have h := Fin.multiKroneckerDelta_comp_perm (R := Real)
      (RelEmbedding.injective (bivectorOrderEmbedding3 i))
      (Equiv.refl (Fin 2))
    simpa using h
  · rw [if_neg hip]
    apply Fin.multiKroneckerDelta_eq_zero
    apply Equiv.Perm.orderEmb_ne_comp_perm
    intro hEmbedding
    apply hip
    apply bivectorOrderEquiv3.injective
    exact hEmbedding

omit [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem curvatureTwoFormBasisAt_pair_apply {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i p : Fin 3) :
    (curvatureTwoFormBasisAt (I := I) basis i)
        ![basis (DimensionThree.bivectorIndex3 p).1,
          basis (DimensionThree.bivectorIndex3 p).2] =
      if i = p then 1 else 0 := by
  have hpair :
      ![basis (DimensionThree.bivectorIndex3 p).1,
        basis (DimensionThree.bivectorIndex3 p).2] =
        basis ∘ bivectorOrderEmbedding3 p := by
    funext a
    fin_cases p <;> fin_cases a <;>
      simp [bivectorOrderEmbedding3, DimensionThree.bivectorIndex3, Fin.succAbove]
  rw [hpair, curvatureTwoFormBasisAt_ordered_apply]

omit [CompleteSpace E] [IsManifold I ∞ M] [T2Space M] in
private theorem curvatureTwoFormBasisAt_reversed_pair_apply {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x)) (i p : Fin 3) :
    (curvatureTwoFormBasisAt (I := I) basis i)
        ![basis (DimensionThree.bivectorIndex3 p).2,
          basis (DimensionThree.bivectorIndex3 p).1] =
      -(if i = p then 1 else 0) := by
  have hswap := (curvatureTwoFormBasisAt (I := I) basis i).map_swap
    (v := ![basis (DimensionThree.bivectorIndex3 p).1,
      basis (DimensionThree.bivectorIndex3 p).2])
    (i := (0 : Fin 2)) (j := 1) (by decide)
  have hvector :
      (![basis (DimensionThree.bivectorIndex3 p).1,
        basis (DimensionThree.bivectorIndex3 p).2] ∘ Equiv.swap 0 1) =
        ![basis (DimensionThree.bivectorIndex3 p).2,
          basis (DimensionThree.bivectorIndex3 p).1] := by
    funext a
    fin_cases a <;> rfl
  rw [hvector] at hswap
  change (curvatureTwoFormBasisAt (I := I) basis i)
      ![basis (DimensionThree.bivectorIndex3 p).2,
        basis (DimensionThree.bivectorIndex3 p).1] =
    -(curvatureTwoFormBasisAt (I := I) basis i)
      ![basis (DimensionThree.bivectorIndex3 p).1,
        basis (DimensionThree.bivectorIndex3 p).2] at hswap
  rw [curvatureTwoFormBasisAt_pair_apply] at hswap
  exact hswap

omit [CompleteSpace E] [T2Space M] in
theorem curvatureOperatorPairingAt_curvatureTwoFormBasisAt
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (i j : Fin 3) :
    curvatureOperatorPairingAt (I := I) g x A
        (curvatureTwoFormBasisAt (I := I) basis i)
        (curvatureTwoFormBasisAt (I := I) basis j) =
      DimensionThree.traceNormalizedCurvatureOperatorMatrixAt
        (I := I) x basis A i j := by
  classical
  rw [curvatureOperatorPairingAt]
  rw [Tensor0SBundle.inner0S_identity_eq_sum (I := I) g x 4 basis
    (orthonormal_invBasis3 (I := I) g basis horth)]
  rw [curvatureKernel_sum_slots4]
  rw [DimensionThree.traceNormalizedCurvatureOperatorMatrixAt_apply]
  have hA := mem_algebraicCurvatureTensorSubmodule_iff_symmetries.mp A.2
  let a := curvatureTwoFormBasisAt (I := I) basis i
  let b := curvatureTwoFormBasisAt (I := I) basis j
  let f : Fin 3 -> Fin 3 -> Fin 3 -> Fin 3 -> Real := fun p q r s =>
    tensor04StandardAt (I := I) (M := M)
        (A : Tensor04At (I := I) (M := M) x)
        (basis p) (basis q) (basis r) (basis s) *
      a ![basis p, basis q] * b ![basis r, basis s]
  have hcomponent : forall p q r s,
      component0S (I := I) basis
          (A : Tensor04At (I := I) (M := M) x)
          (curvatureKernelSlots4 p q r s) *
        component0S (I := I) basis
          (Tensor0SSpace.product (twoFormTensorAt (I := I) a)
            (twoFormTensorAt (I := I) b))
          (curvatureKernelSlots4 p q r s) =
        f p q r s := by
    intro p q r s
    unfold f
    simp only [component0S_apply, Tensor0SSpace.product_apply,
      twoFormTensorAt_apply, tensor04StandardAt_apply]
    have h4 : (fun z : Fin 4 => basis (curvatureKernelSlots4 p q r s z)) =
        ![basis p, basis q, basis r, basis s] := by
      funext z
      fin_cases z <;> rfl
    rw [h4]
    have hfirst :
        (![basis p, basis q, basis r, basis s] ∘ Fin.castAdd 2) =
          ![basis p, basis q] := by
      funext z
      fin_cases z <;> rfl
    have hlast :
        (![basis p, basis q, basis r, basis s] ∘ Fin.natAdd 2) =
          ![basis r, basis s] := by
      funext z
      fin_cases z <;> rfl
    have hvec : vec4 (basis p) (basis q) (basis r) (basis s) =
        ![basis p, basis q, basis r, basis s] := by
      funext z
      fin_cases z <;> rfl
    rw [hfirst, hlast, hvec]
    ring
  have hsum :
      (∑ p : Fin 3, ∑ q : Fin 3, ∑ r : Fin 3, ∑ s : Fin 3,
        component0S (I := I) basis
            (A : Tensor04At (I := I) (M := M) x)
            (curvatureKernelSlots4 p q r s) *
          component0S (I := I) basis
            (Tensor0SSpace.product (twoFormTensorAt (I := I) a)
              (twoFormTensorAt (I := I) b))
            (curvatureKernelSlots4 p q r s)) =
        ∑ p, ∑ q, ∑ r, ∑ s, f p q r s := by
    refine Finset.sum_congr rfl ?_
    intro p _
    refine Finset.sum_congr rfl ?_
    intro q _
    refine Finset.sum_congr rfl ?_
    intro r _
    refine Finset.sum_congr rfl ?_
    intro s _
    exact hcomponent p q r s
  change -(1 / 2 : Real) *
      (∑ p : Fin 3, ∑ q : Fin 3, ∑ r : Fin 3, ∑ s : Fin 3,
        component0S (I := I) basis
            (A : Tensor04At (I := I) (M := M) x)
            (curvatureKernelSlots4 p q r s) *
          component0S (I := I) basis
            (Tensor0SSpace.product (twoFormTensorAt (I := I) a)
              (twoFormTensorAt (I := I) b))
            (curvatureKernelSlots4 p q r s)) =
    2 * DimensionThree.curvatureOperatorMatrixAt (I := I) x basis A i j
  rw [hsum]
  have hcollapse := curvatureKernel_sum_four_by_pairs f
    (by
      intro p q r s
      have hcurv := hA.1 (basis p) (basis q) (basis r) (basis s)
      have hform : a ![basis q, basis p] = -a ![basis p, basis q] := by
        simpa using a.map_swap (v := ![basis p, basis q])
          (i := (0 : Fin 2)) (j := 1) (by decide)
      unfold f
      rw [hcurv, hform]
      ring)
    (by
      intro p q r s
      have hcurv := hA.2.1 (basis p) (basis q) (basis r) (basis s)
      have hform : b ![basis s, basis r] = -b ![basis r, basis s] := by
        simpa using b.map_swap (v := ![basis r, basis s])
          (i := (0 : Fin 2)) (j := 1) (by decide)
      unfold f
      rw [hcurv, hform]
      ring)
    (by
      intro p q r s
      have hzero : a ![basis p, basis p] = 0 := by
        exact a.map_eq_zero_of_eq ![basis p, basis p] rfl
          (i := (0 : Fin 2)) (j := 1) (by decide)
      unfold f
      rw [hzero]
      ring)
    (by
      intro p q r s
      have hzero : b ![basis r, basis r] = 0 := by
        exact b.map_eq_zero_of_eq ![basis r, basis r] rfl
          (i := (0 : Fin 2)) (j := 1) (by decide)
      unfold f
      rw [hzero]
      ring)
  rw [hcollapse]
  unfold f a b
  simp_rw [curvatureTwoFormBasisAt_pair_apply,
    curvatureTwoFormBasisAt_reversed_pair_apply]
  simp only [one_div, tensor04StandardAt_apply, mul_ite, mul_one, mul_zero, mul_neg,
    Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, reduceIte,
    neg_mul, neg_neg]
  unfold DimensionThree.curvatureOperatorMatrixAt
  rw [tensor04StandardAt_apply]
  ring

omit [CompleteSpace E] [T2Space M] in
theorem mem_curvatureOperatorKernelAt_iff_basis
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (a : TangentSpace I x [⋀^Fin 2]→L[Real] Real) :
    a ∈ curvatureOperatorKernelAt (I := I) g x A ↔
      ∀ j : Fin 3, curvatureOperatorPairingAt (I := I) g x A a
        (curvatureTwoFormBasisAt (I := I) basis j) = 0 := by
  constructor
  · intro ha j
    exact ha (curvatureTwoFormBasisAt (I := I) basis j)
  · intro ha b
    have hmap : curvatureOperatorPairingRightAt (I := I) g x A a = 0 := by
      refine (curvatureTwoFormBasisAt (I := I) basis).ext ?_
      intro j
      exact ha j
    have hb := LinearMap.congr_fun hmap b
    exact hb

omit [CompleteSpace E] [T2Space M] in
theorem curvatureTwoFormBasisAt_mem_curvatureOperatorKernelAt_iff
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) g x basis)
    (A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (i : Fin 3) :
    curvatureTwoFormBasisAt (I := I) basis i ∈
        curvatureOperatorKernelAt (I := I) g x A ↔
      ∀ j : Fin 3,
        DimensionThree.traceNormalizedCurvatureOperatorMatrixAt
          (I := I) x basis A i j = 0 := by
  rw [mem_curvatureOperatorKernelAt_iff_basis]
  constructor
  · intro h j
    rw [← curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth A i j]
    exact h j
  · intro h j
    rw [curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth A i j]
    exact h j

end DifferentialGeometry.Geometry.Curvature
