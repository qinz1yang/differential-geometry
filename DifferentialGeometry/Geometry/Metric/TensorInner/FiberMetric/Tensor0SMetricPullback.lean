import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricCongr
import DifferentialGeometry.Tensor.RSTensor.Functoriality.Pullback

set_option autoImplicit false

noncomputable section

namespace Tensor0SBundle

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

theorem tensor0SPullbackCLE_product
    {r s : Nat} {x y : M}
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (A : Tensor0SSpace r I y) (B : Tensor0SSpace s I y) :
    tensor0SPullbackCLE (I := I) (M := M) (r + s) e
        (Tensor0SSpace.product A B) =
      Tensor0SSpace.product
        (tensor0SPullbackCLE (I := I) (M := M) r e A)
        (tensor0SPullbackCLE (I := I) (M := M) s e B) := by
  apply tensor0SSpace_ext (r + s) x
  intro v
  simp only [tensor0SPullbackCLE_apply, tensor0SPullbackCLM_apply,
    Tensor0SSpace.product_apply]
  rfl

private theorem exists_orthonormalBasisGen
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∃ basis : Module.Basis (Fin (Module.finrank Real (TangentSpace I x))) Real
        (TangentSpace I x),
      ∀ i j, g.inner x (basis i) (basis j) =
        if i = j then (1 : Real) else 0 := by
  classical
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x)
      _ _ _ D.toCore
  let : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let basis := (stdOrthonormalBasis Real (TangentSpace I x)).toBasis
  refine ⟨basis, ?_⟩
  intro i j
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
    MetricFiberData.toCore_inner D (ob i) (ob j)
  change g.inner x (ob.toBasis i) (ob.toBasis j) =
    if i = j then (1 : Real) else 0
  rw [← TangentMetricData.inner_eq
    (tangentMetricData (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
  change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
  rw [← hinner]
  exact ob.inner_eq_ite i j

omit [FiniteDimensional Real E] in
private theorem metricInverseInOrthonormalBasisGen
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g : SmoothRiemannianMetric I M) (x : M)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (horth : ∀ i j, g.inner x (basis i) (basis j) =
      if i = j then (1 : Real) else 0) :
    MetricInverseInBasis (I := I) g x basis
      (identityInvMetric (Idx := Idx)) := by
  intro i j
  constructor <;> simp [identityInvMetric, diagonalInvMetric, horth]

theorem inner0S_tensor0SPullbackCLE
    (gSource gTarget : SmoothRiemannianMetric I M) (x y : M) (s : Nat)
    (e : TangentSpace I x ≃ₗ[Real] TangentSpace I y)
    (hiso : ∀ u v, gTarget.inner y (e u) (e v) =
      gSource.inner x u v)
    (A B : Tensor0SSpace s I y) :
    inner0S (I := I) gSource x s
        (tensor0SPullbackCLE (I := I) (M := M) s e A)
        (tensor0SPullbackCLE (I := I) (M := M) s e B) =
      inner0S (I := I) gTarget y s A B := by
  classical
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisGen (I := I) gSource x
  let targetBasis := basis.map e
  have htarget : ∀ i j, gTarget.inner y (targetBasis i) (targetBasis j) =
      if i = j then (1 : Real) else 0 := by
    intro i j
    change gTarget.inner y (e (basis i)) (e (basis j)) = _
    rw [hiso, horth]
  rw [inner0S_identity_eq_sum (I := I) gSource x s basis
      (metricInverseInOrthonormalBasisGen (I := I) gSource x basis horth),
    inner0S_identity_eq_sum (I := I) gTarget y s targetBasis
      (metricInverseInOrthonormalBasisGen (I := I) gTarget y targetBasis htarget)]
  apply Finset.sum_congr rfl
  intro slots _
  simp only [component0S_apply, tensor0SPullbackCLE_apply,
    tensor0SPullbackCLM_apply]
  congr 2

end Tensor0SBundle
