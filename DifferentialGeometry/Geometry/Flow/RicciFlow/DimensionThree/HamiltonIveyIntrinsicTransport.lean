import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.UhlenbeckIsometry
import DifferentialGeometry.Geometry.Curvature.DimensionThree.AlgebraicCurvatureOperatorMetric

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology RealInnerProductSpace BigOperators NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M]
variable [SigmaCompactSpace M] [T2Space M]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma tensor04StdAt_compU_apply
    {x : M} (X : Tensor04At (I := I) (M := M) x)
    (U : TangentSpace I x →L[ℝ] TangentSpace I x)
    (v y z w : TangentSpace I x) :
    tensor04StdAt (I := I) (M := M) (X.compContinuousLinearMap (fun _ : Fin 4 => U)) v y z w =
      tensor04StdAt (I := I) (M := M) X (U v) (U y) (U z) (U w) := by
  change (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (fun i : Fin 4 => U (vec4 v y z w i)) =
    (X : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ)
      (vec4 (U v) (U y) (U z) (U w))
  congr 1
  funext i
  fin_cases i <;> simp [vec4]

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private lemma uhlenbeckComp_mem_algebraicCurvatureTensorSubmodule
    {x : M}
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3)) (t : Real)
    (X : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x := by
  have hform : IsAlgCurvForm (tensor04StdAt (I := I) (M := M) (X : Tensor04At (I := I) (M := M) x)) :=
    (mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)).mp X.2
  rw [show (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x ↔
      IsAlgCurvForm (tensor04StdAt (I := I) (M := M)
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))) from
    mem_algebraicCurvatureTensorSubmodule (I := I) (M := M)]
  change IsAlgCurvForm (fun v y z w =>
    tensor04StdAt (I := I) (M := M)
      ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
        (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) v y z w)
  simp_rw [tensor04StdAt_compU_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ y z w
    rw [map_add (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.add_left _ _ _ _ _
  · intro a u y z w
    rw [map_smul (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    exact hform.smul_left _ _ _ _ _
  · intro u v y z
    exact hform.anti_first _ _ _ _
  · intro u v y z
    exact hform.anti_last _ _ _ _
  · intro u v y z
    exact hform.bianchi _ _ _ _

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
theorem fiberInner_compUhlenbeck_isometry
    {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed 0 T hT.le))
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (hgram : ∀ t : ℝ, t ∈ Set.Icc 0 T → ∀ x : M, ∀ a b : Fin 3,
      movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota t x a b =
        movingFrameGramInFrame (metricCompInFrame (I := I) S (fun a x => basisAt x a)) iota 0 x a b)
    (horth0 : ∀ x : M, OrthonormalBasisAt (I := I) (S.base.metric 0) x (basisAt x))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (x : M)
    (X Y : algebraicCurvatureTensorSubmodule (I := I) (M := M) x) :
    inner0S (I := I) (S.base.metric 0) x 4
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        ((Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t)) =
      inner0S (I := I) (S.base.metric t) x 4
        (X : Tensor04At (I := I) (M := M) x)
        (Y : Tensor04At (I := I) (M := M) x) := by
  classical
  let moving : Module.Basis (Fin 3) Real (TangentSpace I x) :=
    uhlenbeckMovingBasis hT S basisAt iota hiota0 hgram t ht x
  have hmovingOrth : OrthonormalBasisAt (I := I) (S.base.metric t) x moving :=
    uhlenbeckMovingBasis_orthonormalBasisAt (I := I) (M := M) hT S basisAt iota hiota0 hgram x
      (horth0 x) ht
  have hXalg : (X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    uhlenbeckComp_mem_algebraicCurvatureTensorSubmodule basisAt iota t X
  have hYalg : (Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t) ∈
      algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    uhlenbeckComp_mem_algebraicCurvatureTensorSubmodule basisAt iota t Y
  have hmatX : curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨(X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hXalg⟩ =
      curvatureOperatorMatrixAt (I := I) x moving X := by
    ext p q
    unfold curvatureOperatorMatrixAt
    rw [tensor04StdAt_compU_apply (X : Tensor04At (I := I) (M := M) x)
      (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    simp [moving, uhlenbeckMovingBasis_apply]
  have hmatY : curvatureOperatorMatrixAt (I := I) x (basisAt x)
        ⟨(Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hYalg⟩ =
      curvatureOperatorMatrixAt (I := I) x moving Y := by
    ext p q
    unfold curvatureOperatorMatrixAt
    rw [tensor04StdAt_compU_apply (Y : Tensor04At (I := I) (M := M) x)
      (uhlenbeckEndomorphismAt (basisAt x) iota t)]
    simp [moving, uhlenbeckMovingBasis_apply]
  have hleft := inner0S_algebraic_eq_four_mul_operatorInner (I := I) (M := M) (S.base.metric 0) x
    (basisAt x) (horth0 x)
    ⟨(X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hXalg⟩
    ⟨(Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
      (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hYalg⟩
  have hright := inner0S_algebraic_eq_four_mul_operatorInner (I := I) (M := M) (S.base.metric t) x
    moving hmovingOrth X Y
  calc
    inner0S (I := I) (S.base.metric 0) x 4
        ((X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        ((Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
          (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t))
        = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
            curvatureOperatorMatrixAt (I := I) x (basisAt x)
              ⟨(X : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
                (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hXalg⟩ p q *
            curvatureOperatorMatrixAt (I := I) x (basisAt x)
              ⟨(Y : Tensor04At (I := I) (M := M) x).compContinuousLinearMap
                (fun _ : Fin 4 => uhlenbeckEndomorphismAt (basisAt x) iota t), hYalg⟩ p q) := by
          simpa using hleft
    _ = 4 * (∑ p : Fin 3, ∑ q : Fin 3,
            curvatureOperatorMatrixAt (I := I) x moving X p q *
              curvatureOperatorMatrixAt (I := I) x moving Y p q) := by
          congr 1
          rw [hmatX, hmatY]
    _ = inner0S (I := I) (S.base.metric t) x 4
        (X : Tensor04At (I := I) (M := M) x)
        (Y : Tensor04At (I := I) (M := M) x) := by
          rw [hright]


omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] [T2Space M] in
private theorem uhlenbeckEndomorphism_zero_eq_id
    {x : M}
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0) :
    uhlenbeckEndomorphismAt (basisAt x) iota 0 = (1 : TangentSpace I x →L[ℝ] TangentSpace I x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  have hv : v = ∑ a : Fin 3, (basisAt x).repr v a • basisAt x a :=
    ((basisAt x).sum_repr v).symm
  have hU : ∀ a : Fin 3, uhlenbeckEndomorphismAt (basisAt x) iota 0 (basisAt x a) = basisAt x a := by
    intro a
    rw [uhlenbeckEndomorphism_apply_basis]
    have hi : iota 0 x a a = 1 := by simpa using hiota0 x a a
    have hne : ∀ k : Fin 3, k ≠ a → iota 0 x a k = 0 := by
      intro k hk
      have hna : a ≠ k := fun h => hk h.symm
      simpa [hna] using hiota0 x a k
    have hsum : (∑ k : Fin 3, iota 0 x a k • basisAt x k) = basisAt x a := by
      calc
        (∑ k : Fin 3, iota 0 x a k • basisAt x k)
            = ∑ k : Fin 3, (if k = a then (1 : ℝ) else 0) • basisAt x k := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases h : k = a
              · subst h
                simp [hi]
              · have h0 : iota 0 x a k = 0 := hne k h
                have hka : k ≠ a := h
                simp [h0, hka]
        _ = basisAt x a := by
              simp
    exact hsum
  rw [hv]
  rw [map_sum]
  simp [hU]

omit [IsManifold I 2 M] [IsManifold I 3 M] [SigmaCompactSpace M] in
theorem uhlenbeckPulledRm04At_zero_eq_rm04
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (basisAt : ∀ x : M, Module.Basis (Fin 3) Real (TangentSpace I x))
    (iota : MatrixComp M (Fin 3))
    (hiota0 : ∀ x : M, ∀ a k : Fin 3, iota 0 x a k = if a = k then 1 else 0)
    (x : M) :
    uhlenbeckPulledRm04At S basisAt iota 0 x = S.base.rm04 0 x := by
  apply ContinuousMultilinearMap.ext
  intro m
  change (S.base.rm04 0 x) (fun i : Fin 4 =>
      uhlenbeckEndomorphismAt (basisAt x) iota 0 (m i)) = (S.base.rm04 0 x) m
  rw [show uhlenbeckEndomorphismAt (basisAt x) iota 0 = (1 : TangentSpace I x →L[ℝ] TangentSpace I x) from
    uhlenbeckEndomorphism_zero_eq_id basisAt iota hiota0]
  simp


end DifferentialGeometry.PDE.RicciFlow

end
