import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BoundedGeometry
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CovariantDerivativeTower

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [eAdd : NormedAddCommGroup E] [nE : NormedSpace Real E]
  [fdE : FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [boundarylessI : I.Boundaryless]

namespace HasCurvDerivBound

private theorem sqrt_le_of_sq_le_mul {q A : Real}
    (hq : 0 <= q) (hA : 0 <= A) (h : q ^ 2 <= A * q) :
    q <= A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa only [pow_two] using h) hqpos

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit fdE in
private theorem inner_self_nonneg
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    0 <= g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [CompleteSpace E] in
theorem curvOpN_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {k : Nat} {C : Real} (hP : HasCurvDerivBound (I := I) P k C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M) (v : Fin (k + 3) -> TangentSpace I x),
      let R := curvOpN (I := I) P.metric k x v
      Real.sqrt (P.metric.inner x R R) <=
        C * ∏ a : Fin (k + 3),
          Real.sqrt (P.metric.inner x (v a) (v a)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro x v
  let R := curvOpN (I := I) P.metric k x v
  let q := Real.sqrt (P.metric.inner x R R)
  let A :=
    C * ∏ a : Fin (k + 3),
      Real.sqrt (P.metric.inner x (v a) (v a))
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) k P.metric x)).trans (hP x)
  have hA : 0 <= A := by
    dsimp only [A]
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hRR : 0 <= P.metric.inner x R R :=
    inner_self_nonneg (I := I) P.metric x R
  have hbound := apply_le (I := I) P hP x (Fin.snoc v R)
  rw [← curvOpN_inner (I := I) P.metric k x v R] at hbound
  have hprod :
      (∏ a : Fin (k + 4),
          Real.sqrt (P.metric.inner x
            ((Fin.snoc v R : Fin (k + 4) -> TangentSpace I x) a)
            ((Fin.snoc v R : Fin (k + 4) -> TangentSpace I x) a))) =
        (∏ a : Fin (k + 3),
          Real.sqrt (P.metric.inner x (v a) (v a))) * q := by
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, q]
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 <= A * q := by
    rw [show q ^ 2 = P.metric.inner x R R from Real.sq_sqrt hRR]
    simpa only [A, mul_assoc] using hbound
  exact sqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

end HasCurvDerivBound

end HCGCompactness
end DifferentialGeometry
