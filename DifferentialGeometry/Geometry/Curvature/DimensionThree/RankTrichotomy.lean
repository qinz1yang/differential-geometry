import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankRigidity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.PinchingAlgebra
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

namespace DifferentialGeometry.Geometry.Curvature

universe uE uH uM

theorem curvatureReactionSumSquares3_ordered_rank_trichotomy
    (lambda mu nu : Real)
    (hnu_nonneg : 0 ≤ nu)
    (hord : And (nu ≤ mu) (mu ≤ lambda))
    (hreaction : curvatureReactionSumSquares3 lambda mu nu = 0) :
    (And (lambda = 0) (And (mu = 0) (nu = 0))) ∨
      (And (0 < lambda) (And (mu = 0) (nu = 0))) ∨
      (And (0 < nu) (And (lambda = mu) (mu = nu))) := by
  by_cases hnu : 0 < nu
  · have hlambda : 0 < lambda := lt_of_lt_of_le hnu (le_trans hord.1 hord.2)
    have hrigid := (curvatureReactionSumSquares3_eq_zero_iff
      lambda mu nu hlambda hnu).mp hreaction
    exact Or.inr (Or.inr ⟨hnu, hrigid.1, hrigid.2⟩)
  · have hnu_zero : nu = 0 := le_antisymm (le_of_not_gt hnu) hnu_nonneg
    have hmu_nonneg : 0 ≤ mu := by linarith [hord.1]
    by_cases hmu : 0 < mu
    · have hlambda : 0 < lambda := lt_of_lt_of_le hmu hord.2
      have hpositive : 0 < lambda ^ 2 * (mu - nu) ^ 2 := by
        rw [hnu_zero]
        positivity
      have hrest : 0 ≤
          mu ^ 2 * (lambda - nu) ^ 2 + nu ^ 2 * (lambda - mu) ^ 2 := by
        positivity
      unfold curvatureReactionSumSquares3 at hreaction
      nlinarith
    · have hmu_zero : mu = 0 := le_antisymm (le_of_not_gt hmu) hmu_nonneg
      have hlambda_nonneg : 0 ≤ lambda := by linarith [hord.2]
      by_cases hlambda : 0 < lambda
      · exact Or.inr (Or.inl ⟨hlambda, hmu_zero, hnu_zero⟩)
      · have hlambda_zero : lambda = 0 := le_antisymm
          (le_of_not_gt hlambda) hlambda_nonneg
        exact Or.inl ⟨hlambda_zero, hmu_zero, hnu_zero⟩

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle
open scoped ContDiff Manifold

noncomputable local instance rankTrichotomyTwoFormFiniteDimensional
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners Real E H}
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
  (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

private theorem inner_pos_of_isPositive_of_finrank_range_eq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
    [FiniteDimensional Real V]
    (A : V →ₗ[Real] V) (hA : A.IsPositive)
    {n : Nat} (hDim : Module.finrank Real V = n)
    (hrank : Module.finrank Real A.range = n)
    {v : V} (hv : v ≠ 0) :
    0 < inner Real (A v) v := by
  let basis : OrthonormalBasis (Fin n) Real V :=
    hA.isSymmetric.eigenvectorBasis hDim
  let matrix : Matrix (Fin n) (Fin n) Real :=
    LinearMap.toMatrix basis.toBasis basis.toBasis A
  have hmatrixPos : matrix.PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff basis).mpr hA
  have hmatrixRank : matrix.rank = n := by
    rw [show matrix = LinearMap.toMatrix basis.toBasis basis.toBasis A by rfl]
    rw [Matrix.rank_eq_finrank_range_toLin
      (LinearMap.toMatrix basis.toBasis basis.toBasis A)
      basis.toBasis basis.toBasis]
    rw [Matrix.toLin_toMatrix]
    exact hrank
  have hmatrixInj : Function.Injective (Matrix.mulVecLin matrix) := by
    apply LinearMap.ker_eq_bot.mp
    have hdim : matrix.rank +
        Module.finrank Real (Matrix.mulVecLin matrix).ker = n := by
      simpa [Matrix.rank] using
        (Matrix.mulVecLin matrix).finrank_range_add_finrank_ker
    have hker : Module.finrank Real (Matrix.mulVecLin matrix).ker = 0 := by
      omega
    exact Submodule.finrank_eq_zero.mp hker
  have hmatrixDef : matrix.PosDef :=
    hmatrixPos.posDef_iff_isUnit.mpr
      (Matrix.mulVec_injective_iff_isUnit.mp hmatrixInj)
  have hvrepr : (basis.repr v).ofLp ≠ 0 := by
    intro h
    apply hv
    apply basis.repr.injective
    simpa using (WithLp.ofLp_eq_zero (2 : ENNReal)).mp h
  have hcoord := hmatrixDef.dotProduct_mulVec_pos hvrepr
  have hvcoord : ((basis.toBasis.repr v : Fin n →₀ Real) : Fin n → Real) =
      (basis.repr v).ofLp := by
    funext i
    exact basis.coe_toBasis_repr_apply v i
  have hAvcoord : ((basis.toBasis.repr (A v) : Fin n →₀ Real) : Fin n → Real) =
      (basis.repr (A v)).ofLp := by
    funext i
    exact basis.coe_toBasis_repr_apply (A v) i
  rw [show Matrix.mulVec matrix (basis.repr v).ofLp =
      (basis.repr (A v)).ofLp by
    simpa [matrix, hvcoord, hAvcoord] using
      LinearMap.toMatrix_mulVec_repr basis.toBasis basis.toBasis A v] at hcoord
  rw [← basis.repr.inner_map_map (A v) v]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct_comm] using hcoord

private theorem MetricFiberData.inner_pos_of_nonnegative_of_finrank_range_eq
    {V : Type*} [AddCommGroup V] [Module Real V] [FiniteDimensional Real V]
    (D : MetricFiberData V) (A : V →ₗ[Real] V)
    (hA_symm : D.IsSymmetric A)
    (hA_nonneg : ∀ v : V, 0 ≤ D.inner (A v) v)
    {n : Nat} (hDim : Module.finrank Real V = n)
    (hrank : Module.finrank Real A.range = n)
    {v : V} (hv : v ≠ 0) :
    0 < D.inner (A v) v := by
  let addV : AddCommGroup V := inferInstance
  let modV : Module Real V := inferInstance
  let : InnerProductSpace.Core Real V := D.toCore
  let : NormedAddCommGroup V :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real V _ addV modV D.toCore
  let : AddCommGroup V := addV
  let : Module Real V := modV
  let : InnerProductSpace Real V :=
    @InnerProductSpace.ofCore Real V _ _ _ D.toCore.toCore
  have hA : A.IsPositive := by
    rw [LinearMap.isPositive_iff]
    constructor
    · intro x y
      rw [MetricFiberData.toCore_inner D, MetricFiberData.toCore_inner D]
      exact hA_symm x y
    · intro x
      rw [MetricFiberData.toCore_inner D]
      exact hA_nonneg x
  have hpos := inner_pos_of_isPositive_of_finrank_range_eq A hA hDim hrank hv
  rw [MetricFiberData.toCore_inner D] at hpos
  exact hpos

theorem curvatureOperator_time_slice_trichotomy
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E]
    {H : Type uH} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} [I.Boundaryless]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [Nonempty M]
    (hE : Module.finrank Real E = 3)
    (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (I := I) (M := M) (∞ : WithTop ℕ∞) 4)
    (hA : ∀ x, A x ∈ algebraicCurvatureTensorSubmodule (I := I) (M := M) x)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩ a = 0 →
          DimensionThree.curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt
              (I := I) g x ⟨A x, hA x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) g y ⟨A y, hA y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x ⟨A x, hA x⟩)) :
    (∀ x, curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩ = 0) ∨
      (And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 1)
        (∀ x, ∃ e : TangentSpace I x,
          And (e ∈ curvatureOperatorImageAnnihilatorAt (I := I) g x ⟨A x, hA x⟩)
          (And (g.inner x e e = 1)
            (Connection.HasLocalRiemannianProductAt (I := I) g x e)))) ∨
      And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x ⟨A x, hA x⟩) = 3)
        (∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) g x).inner
            (curvatureOperatorEndomorphismAt (I := I) g x ⟨A x, hA x⟩ a) a) := by
  have htri :=
    DimensionThree.curvatureOperatorImageAt_finrank_trichotomy_of_spatially_constant
      hE g (fun x => ⟨A x, hA x⟩) hpositive hnull hrank
  rcases htri with hzero | hone | hthree
  · left
    intro x
    apply ContinuousLinearMap.ext
    intro a
    have ha : curvatureOperatorEndomorphismAt
        (I := I) g x ⟨A x, hA x⟩ a ∈
        (curvatureOperatorEndomorphismAt
          (I := I) g x ⟨A x, hA x⟩).toLinearMap.range := ⟨a, rfl⟩
    have hrange :
        (curvatureOperatorEndomorphismAt
          (I := I) g x ⟨A x, hA x⟩).toLinearMap.range = ⊥ :=
      Submodule.finrank_eq_zero.mp (hzero x)
    rw [hrange] at ha
    simpa using ha
  · right
    left
    refine ⟨hone, ?_⟩
    intro x
    exact exists_local_product_of_curvatureOperatorImage_rank_eq_one
      hE g A hA hone hkernel x
  · right
    right
    refine ⟨hthree, ?_⟩
    intro x a ha
    have hTangentDim : Module.finrank Real (TangentSpace I x) = 3 := by
      exact (show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real E from rfl).trans hE
    let tangentBasis : Module.Basis (Fin 3) Real (TangentSpace I x) := by
      have basis := Module.finBasis Real (TangentSpace I x)
      rw [hTangentDim] at basis
      exact basis
    let twoFormBasis := curvatureTwoFormBasisAt (I := I) tangentBasis
    have hTwoFormDim : Module.finrank Real
        (TangentSpace I x [⋀^Fin 2]→L[Real] Real) = 3 := by
      rw [Module.finrank_eq_card_basis twoFormBasis, Fintype.card_fin]
    exact MetricFiberData.inner_pos_of_nonnegative_of_finrank_range_eq
      (twoFormMetricData (I := I) g x)
      (curvatureOperatorEndomorphismAt
        (I := I) g x ⟨A x, hA x⟩).toLinearMap
      (curvatureOperatorEndomorphismAt_isSymmetric
        (I := I) g x ⟨A x, hA x⟩)
      (hpositive x) hTwoFormDim (hthree x) ha

end DifferentialGeometry.Geometry.Curvature
