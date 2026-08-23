import DifferentialGeometry.Geometry.Curvature.Metric

import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Comparison.Volume.BallVolume
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.InjectivityRadius
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison

open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Tensor.Auxiliary
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section FixedMetric

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

noncomputable def curvCovDerivStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A :
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 5) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
    change IsManifold I ∞ M
    infer_instance
  let cov := DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g
  let hcov := DifferentialGeometry.Geometry.Curvature.metricCov_smooth (I := I) (M := M) g
  let hreg :=
    Tensor0SBundle.totalNabla0S_reg (E := E) (H := H)
      (I := I) (M := M) (a + 4) cov hcov A
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cov, hcov, hreg]
    using
      Tensor0SBundle.totalNabla0S (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (a + 4) cov A hreg

noncomputable def curvCovDeriv
    (g : SmoothRiemannianMetric I M) :
    (k : Nat) ->
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4) :=
  Nat.rec
    (motive := fun k : Nat =>
      Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (k + 4))
    (by
      haveI : IsManifold I 1 M :=
        IsManifold.of_le (I := I) (M := M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
        change IsManifold I ∞ M
        infer_instance
      exact DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g)
    (fun k A =>
      by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          curvCovDerivStep (I := I) g k A)

omit [SigmaCompactSpace M] in
theorem curvCovDeriv_succ
    (g : SmoothRiemannianMetric I M) (k : Nat) :
    curvCovDeriv (I := I) (M := M) g (k + 1) =
      curvCovDerivStep (I := I) g k
        (curvCovDeriv (I := I) (M := M) g k) :=
  rfl

section PointwiseCurvature

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem curvZero_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (X Y Z W : TangentSpace I x) :
    curvCovDeriv (I := I) (M := M) g 0 x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      g.inner x W
        (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g)
          x X Y Z) := by
  rw [show curvCovDeriv (I := I) (M := M) g 0 =
      DifferentialGeometry.Geometry.Curvature.metricRm04 (I := I) (M := M) g from rfl]
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04_apply]
  change
    DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At
        g
        (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
        (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
          (I := I) (M := M) g) x
        (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z W) =
      _
  rw [DifferentialGeometry.Geometry.Curvature.CovariantDerivative.riemannCurvature04At_apply_const]
  letI :
      CovariantDerivative.ContMDiffCovariantDerivative
        (DifferentialGeometry.Geometry.Curvature.metricCov
          (I := I) (M := M) g) ∞ :=
    DifferentialGeometry.Geometry.Connection.LeviCivita_isContMDiff
      (I := I) (M := M) g
  rw [DifferentialGeometry.riemannCurvatureAux_tangentConst_eq_riemannOp
    (DifferentialGeometry.Geometry.Curvature.metricCov (I := I) (M := M) g)
    (DifferentialGeometry.Geometry.Curvature.metricCov_smooth
      (I := I) (M := M) g) x X Y Z]
  rfl

omit [SigmaCompactSpace M] [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem curvOne_apply
    (g : SmoothRiemannianMetric I M) (x : M)
    (D X Y Z W : TangentSpace I x) :
    curvCovDeriv (I := I) (M := M) g 1 x
        (DifferentialGeometry.Geometry.Curvature.vec5 (I := I) D X Y Z W) =
      g.inner x W
        (DifferentialGeometry.Integral.Connection.nablaRiemannOp
          (I := I) g x D X Y Z) := by
  simpa [curvCovDeriv, curvCovDerivStep,
    DifferentialGeometry.Geometry.Curvature.metricCov,
    DifferentialGeometry.Geometry.Curvature.metricRm04] using
    (DifferentialGeometry.Integral.Connection.nablaRm04_apply
      (I := I) g x D X Y Z W)

end PointwiseCurvature

noncomputable def curvDerivNormSq
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Tensor0SBundle.normSq0S (I := I) g x (k + 4)
    (curvCovDeriv (I := I) (M := M) g k x)

noncomputable def curvDerivNorm
    (k : Nat) (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  Real.sqrt (curvDerivNormSq (I := I) (M := M) k g x)

omit [SigmaCompactSpace M] in
theorem curv_apply_le
    (g : SmoothRiemannianMetric I M) (k : Nat) (x : M)
    (v : Fin (k + 4) -> TangentSpace I x) :
    |curvCovDeriv (I := I) (M := M) g k x v| <=
      curvDerivNorm (I := I) (M := M) k g x *
        ∏ a : Fin (k + 4), Real.sqrt (g.inner x (v a) (v a)) := by
  simpa [curvDerivNorm, curvDerivNormSq] using
    (Tensor0SBundle.abs_apply_le_norm0S (I := I) g x (k + 4)
      (curvCovDeriv (I := I) (M := M) g k x) v)

end FixedMetric

def HasCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (k : Nat)
    (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  forall x : X.M, curvDerivNorm (I := I) k X.metric x <= C

namespace HasCurvDerivBound

private theorem sqrt_le_of_sq_le_mul {q A : Real}
    (hq : 0 <= q) (hA : 0 <= A) (h : q ^ 2 <= A * q) :
    q <= A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa [pow_two] using h) hqpos

omit [FiniteDimensional ℝ E] in
private theorem inner_self_nonneg
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    0 <= g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

theorem apply_le
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {k : Nat} {C : Real}
    (hX : HasCurvDerivBound (I := I) X k C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    ∀ (x : X.M) (v : Fin (k + 4) -> TangentSpace I x),
      |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  intro x v
  calc
    |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        curvDerivNorm (I := I) (M := X.M) k X.metric x *
          ∏ a : Fin (k + 4),
            Real.sqrt (X.metric.inner x (v a) (v a)) :=
      curv_apply_le (I := I) X.metric k x v
    _ <= C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) :=
      mul_le_mul_of_nonneg_right (hX x)
        (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)

section PointwiseCurvature

variable [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem riemannOp_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 0 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M) (X Y Z : TangentSpace I x),
      let R :=
        DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita
            (I := I) P.metric) x X Y Z
      Real.sqrt (P.metric.inner x R R) <=
        C * Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  intro x X Y Z
  let R :=
    DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita
        (I := I) P.metric) x X Y Z
  let q := Real.sqrt (P.metric.inner x R R)
  let A :=
    C * Real.sqrt (P.metric.inner x X X) *
      Real.sqrt (P.metric.inner x Y Y) *
      Real.sqrt (P.metric.inner x Z Z)
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) 0 P.metric x)).trans (hP x)
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hRR : 0 <= P.metric.inner x R R :=
    inner_self_nonneg (I := I) P.metric x R
  have hbound := apply_le (I := I) P hP x
    (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Z R)
  rw [curvZero_apply] at hbound
  have hprod :
      (∏ a : Fin 4,
          Real.sqrt (P.metric.inner x
            (DifferentialGeometry.Geometry.Curvature.vec4
              (I := I) X Y Z R a)
            (DifferentialGeometry.Geometry.Curvature.vec4
              (I := I) X Y Z R a))) =
        Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) * q := by
    simp [DifferentialGeometry.Geometry.Curvature.vec4,
      Fin.prod_univ_succ, q, mul_assoc]
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 <= A * q := by
    rw [show q ^ 2 = P.metric.inner x R R from by
      exact Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  exact sqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem nablaRiemannOp_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 1 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M) (D X Y Z : TangentSpace I x),
      let R :=
        DifferentialGeometry.Integral.Connection.nablaRiemannOp
          (I := I) P.metric x D X Y Z
      Real.sqrt (P.metric.inner x R R) <=
        C * Real.sqrt (P.metric.inner x D D) *
          Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  intro x D X Y Z
  let R :=
    DifferentialGeometry.Integral.Connection.nablaRiemannOp
      (I := I) P.metric x D X Y Z
  let q := Real.sqrt (P.metric.inner x R R)
  let A :=
    C * Real.sqrt (P.metric.inner x D D) *
      Real.sqrt (P.metric.inner x X X) *
      Real.sqrt (P.metric.inner x Y Y) *
      Real.sqrt (P.metric.inner x Z Z)
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) 1 P.metric x)).trans (hP x)
  have hA : 0 <= A := by
    dsimp [A]
    positivity
  have hRR : 0 <= P.metric.inner x R R :=
    inner_self_nonneg (I := I) P.metric x R
  have hbound := apply_le (I := I) P hP x
    (DifferentialGeometry.Geometry.Curvature.vec5 (I := I) D X Y Z R)
  rw [curvOne_apply] at hbound
  have hprod :
      (∏ a : Fin 5,
          Real.sqrt (P.metric.inner x
            (DifferentialGeometry.Geometry.Curvature.vec5
              (I := I) D X Y Z R a)
            (DifferentialGeometry.Geometry.Curvature.vec5
              (I := I) D X Y Z R a))) =
        Real.sqrt (P.metric.inner x D D) *
          Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) * q := by
    simp [DifferentialGeometry.Geometry.Curvature.vec5,
      Fin.prod_univ_succ, q, mul_assoc]
  rw [hprod, abs_of_nonneg hRR] at hbound
  have hquad : q ^ 2 <= A * q := by
    rw [show q ^ 2 = P.metric.inner x R R from by
      exact Real.sq_sqrt hRR]
    simpa [A, mul_assoc] using hbound
  exact sqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

end PointwiseCurvature

end HasCurvDerivBound

theorem rm04Bound_of_curv0
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) {C : Real}
    (hX : HasCurvDerivBound (I := I) X 0 C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric C := by
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  intro x
  simpa [Geometry.Riemannian.VolumeComparison.Rm04GlobalBound,
    HasCurvDerivBound, curvDerivNorm, curvDerivNormSq, curvCovDeriv,
    DifferentialGeometry.Geometry.Curvature.metricRm04_apply] using hX x

structure BoundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall k : Nat, HasCurvDerivBound (I := I) X k (C k)

theorem rm04Bound_of_geom
    {X : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (hX : BoundedGeometry (I := I) X) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := X.M) X.metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) X (hX.bound 0)

structure SeqBoundedGeometry
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I)) where
  C : Nat -> Real
  nonneg : forall k : Nat, 0 <= C k
  bound : forall i k : Nat, HasCurvDerivBound (I := I) (X.obj i) k (C k)

namespace SeqBoundedGeometry

def subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (f : Nat -> Nat) :
    SeqBoundedGeometry (I := I) (X.subseq f) where
  C := hX.C
  nonneg := hX.nonneg
  bound := by
    intro i k
    simpa [PointedRiemannianSeq.subseq] using hX.bound (f i) k

end SeqBoundedGeometry

theorem rm04Bound_of_seq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hX : SeqBoundedGeometry (I := I) X) (i : Nat) :
    letI : TopologicalSpace (X.obj i).M := (X.obj i).topology
    letI : ChartedSpace H (X.obj i).M := (X.obj i).charted
    letI : IsManifold I ∞ (X.obj i).M := (X.obj i).smooth
    letI : SigmaCompactSpace (X.obj i).M := (X.obj i).sigmaCompact
    letI : T2Space (X.obj i).M := (X.obj i).t2
    Geometry.Riemannian.VolumeComparison.Rm04GlobalBound
      (I := I) (M := (X.obj i).M) (X.obj i).metric (hX.C 0) :=
  rm04Bound_of_curv0 (I := I) (X.obj i) (hX.bound i 0)

end HCGCompactness
end DifferentialGeometry
