import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.JetBounds
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open Geometry.Riemannian

open Geometry.Riemannian.CovariantDerivativeAlong
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.NormalCoordinates
open Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

local instance ljbFormNormedAdd :
    NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance ljbFormNormedSpace :
    NormedSpace Real (E →L[Real] E →L[Real] Real) :=
  ContinuousLinearMap.toNormedSpace

def HasLocalCurvDerivBound
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : X.M) (A : Real)
    (k : Nat) (C : Real) : Prop :=
  letI : TopologicalSpace X.M := X.topology
  letI : ChartedSpace H X.M := X.charted
  letI : IsManifold I ∞ X.M := X.smooth
  letI : SigmaCompactSpace X.M := X.sigmaCompact
  letI : T2Space X.M := X.t2
  ∀ x : X.M, riemannianEDistOf (I := I) X.metric p x ≤ ENNReal.ofReal A →
    curvDerivNorm (I := I) k X.metric x ≤ C

structure LocalBoundedGeometryOn
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : X.M) (A : Real) where
  C : Nat → Real
  nonneg : ∀ k : Nat, 0 ≤ C k
  bound : ∀ k : Nat, HasLocalCurvDerivBound (I := I) X p A k (C k)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
def LocalBoundedGeometryOn.of_boundedGeometry
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hX : BoundedGeometry (I := I) X) (p : X.M) (A : Real) :
    LocalBoundedGeometryOn (I := I) X p A where
  C := hX.C
  nonneg := hX.nonneg
  bound k := by
    intro x _
    exact hX.bound k x

private theorem localSqrt_le_of_sq_le_mul {q A : Real}
    (hq : 0 <= q) (hA : 0 <= A) (h : q ^ 2 <= A * q) :
    q <= A := by
  rcases hq.eq_or_lt with hq0 | hqpos
  · rw [← hq0]
    exact hA
  · exact le_of_mul_le_mul_right (by simpa [pow_two] using h) hqpos

omit [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
private theorem localInner_self_nonneg
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : SmoothRiemannianMetric I M)
    (x : M) (v : TangentSpace I x) :
    0 <= g.inner x v v := by
  rcases eq_or_ne v 0 with hv | hv
  · rw [hv]
    simp
  · exact le_of_lt (g.pos x v hv)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem HasCurvDerivBound.apply_le_local
    (X : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : X.M) {k : Nat} {C A : Real}
    (hX : HasLocalCurvDerivBound (I := I) X p A k C) :
    letI : TopologicalSpace X.M := X.topology
    letI : ChartedSpace H X.M := X.charted
    letI : IsManifold I ∞ X.M := X.smooth
    letI : SigmaCompactSpace X.M := X.sigmaCompact
    letI : T2Space X.M := X.t2
    ∀ (x : X.M)
      (_ : riemannianEDistOf (I := I) X.metric p x ≤ ENNReal.ofReal A)
      (v : Fin (k + 4) -> TangentSpace I x),
      |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) := by
  let : TopologicalSpace X.M := X.topology
  let : ChartedSpace H X.M := X.charted
  let : IsManifold I ∞ X.M := X.smooth
  let : SigmaCompactSpace X.M := X.sigmaCompact
  let : T2Space X.M := X.t2
  intro x hx v
  calc
    |curvCovDeriv (I := I) (M := X.M) X.metric k x v| <=
        curvDerivNorm (I := I) (M := X.M) k X.metric x *
          ∏ a : Fin (k + 4),
            Real.sqrt (X.metric.inner x (v a) (v a)) :=
      curv_apply_le (I := I) X.metric k x v
    _ <= C * ∏ a : Fin (k + 4),
          Real.sqrt (X.metric.inner x (v a) (v a)) :=
      mul_le_mul_of_nonneg_right (hX x hx)
        (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
theorem HasCurvDerivBound.riemann_op_le_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) {C A : Real}
    (hP : HasLocalCurvDerivBound (I := I) P p A 0 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M)
      (_ : riemannianEDistOf (I := I) P.metric p x ≤ ENNReal.ofReal A)
      (X Y Z : TangentSpace I x),
      let R :=
        DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita
            (I := I) P.metric) x X Y Z
      Real.sqrt (P.metric.inner x R R) <=
        C * Real.sqrt (P.metric.inner x X X) *
          Real.sqrt (P.metric.inner x Y Y) *
          Real.sqrt (P.metric.inner x Z Z) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro x hx X Y Z
  let R :=
    DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita
        (I := I) P.metric) x X Y Z
  let q := Real.sqrt (P.metric.inner x R R)
  let A' :=
    C * Real.sqrt (P.metric.inner x X X) *
      Real.sqrt (P.metric.inner x Y Y) *
      Real.sqrt (P.metric.inner x Z Z)
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) 0 P.metric x)).trans (hP x hx)
  have hA : 0 <= A' := by
    dsimp [A']
    positivity
  have hRR : 0 <= P.metric.inner x R R :=
    localInner_self_nonneg (I := I) P.metric x R
  have hbound := HasCurvDerivBound.apply_le_local (I := I) P p hP x hx
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
  have hquad : q ^ 2 <= A' * q := by
    rw [show q ^ 2 = P.metric.inner x R R from by
      exact Real.sq_sqrt hRR]
    simpa [A', mul_assoc] using hbound
  exact localSqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

omit [CompleteSpace E] in
theorem intrinsicGeodesic_riemannianEDistOf_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    ∀ (hEnorm : Geometry.Riemannian.IsMetricNorm (I := I) (M := P.M) P.metric)
      (p : P.M) (v : TangentSpace I p) {U t : Real},
      Real.sqrt (P.metric.inner p v v) <= U -> 0 <= t -> t <= 1 ->
      riemannianEDistOf (I := I) P.metric p
        (intrinsicGeodesic (I := I) P.metric hEnorm p v t) <= ENNReal.ofReal U := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  let : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let : EMetricSpace P.M := P.emetricSpace (I := I)
  let : CompleteSpace P.M := MetricComplete.complete (I := I) P hcomplete
  let : ConnectedSpace P.M := hconn
  intro hEnorm p v U t hspeed ht0 ht1
  have hU0 : 0 <= U := (Real.sqrt_nonneg _).trans hspeed
  have hle : Real.sqrt (P.metric.inner p v v) * t <= U := by
    calc Real.sqrt (P.metric.inner p v v) * t <= U * 1 :=
          mul_le_mul hspeed ht1 ht0 hU0
      _ = U := by ring
  have hgeo : riemannianEDist I p
      (intrinsicGeodesic (I := I) P.metric hEnorm p v t) <= ENNReal.ofReal U := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) P.metric hEnorm p v
      (s := 0) (t := t) ht0
    rw [intrinsicGeodesic_zero (I := I) P.metric hEnorm p v, sub_zero] at h
    exact h.trans (ENNReal.ofReal_le_ofReal hle)
  rw [riemannianEDistOf_eq_riemannianEDist (I := I) P.metric hEnorm]
  exact hgeo

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem HasCurvDerivBound.curv_op_n_le_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) {k : Nat} {C A : Real}
    (hP : HasLocalCurvDerivBound (I := I) P p A k C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (x : P.M)
      (_ : riemannianEDistOf (I := I) P.metric p x ≤ ENNReal.ofReal A)
      (v : Fin (k + 3) -> TangentSpace I x),
      let R := curvOpN (I := I) P.metric k x v
      Real.sqrt (P.metric.inner x R R) <=
        C * ∏ a : Fin (k + 3),
          Real.sqrt (P.metric.inner x (v a) (v a)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro x hx v
  let R := curvOpN (I := I) P.metric k x v
  let q := Real.sqrt (P.metric.inner x R R)
  let A' :=
    C * ∏ a : Fin (k + 3),
      Real.sqrt (P.metric.inner x (v a) (v a))
  have hC : 0 <= C := by
    exact (Real.sqrt_nonneg
      (curvDerivNormSq (I := I) (M := P.M) k P.metric x)).trans (hP x hx)
  have hA : 0 <= A' := by
    dsimp only [A']
    exact mul_nonneg hC (Finset.prod_nonneg fun _ _ => Real.sqrt_nonneg _)
  have hRR : 0 <= P.metric.inner x R R :=
    localInner_self_nonneg (I := I) P.metric x R
  have hbound := HasCurvDerivBound.apply_le_local (I := I) P p hP x hx
    (Fin.snoc v R)
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
  have hquad : q ^ 2 <= A' * q := by
    rw [show q ^ 2 = P.metric.inner x R R from Real.sq_sqrt hRR]
    simpa only [A', mul_assoc] using hbound
  exact localSqrt_le_of_sq_le_mul (Real.sqrt_nonneg _) hA hquad

omit [NeZero (Module.finrank ℝ E)] in
theorem HasCurvDerivBound.curvature_along_le_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) {C A : Real}
    (hP : HasLocalCurvDerivBound (I := I) P p A 0 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (γ : Real -> P.M)
      (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
      (_ : riemannianEDistOf (I := I) P.metric p (γ t) ≤ ENNReal.ofReal A),
      let R :=
        Geometry.Riemannian.Variation.curvAlong (I := I)
          P.metric γ X Y Z t
      Real.sqrt (P.metric.inner (γ t) R R) <=
        C * Real.sqrt (P.metric.inner (γ t) (X t) (X t)) *
          Real.sqrt (P.metric.inner (γ t) (Y t) (Y t)) *
          Real.sqrt (P.metric.inner (γ t) (Z t) (Z t)) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : T2Space P.M := P.t2
  intro γ X Y Z t ht
  simpa only [Geometry.Riemannian.Variation.curvAlong] using
    (HasCurvDerivBound.riemann_op_le_local (I := I) P p hP
      (γ t) ht (X t) (Y t) (Z t))


omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem localLaunchSpeed_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (p : P.M) (u a : E) {r R U D : Real} :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real.sqrt (P.metric.inner p a a) <= D ->
    |r| <= R ->
    0 <= D ->
    Real.sqrt (P.metric.inner p u u) + R * D <= U ->
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <= U := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  intro ha hr hD hu
  have hR : 0 <= R := (abs_nonneg r).trans hr
  calc
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <=
      Real.sqrt (P.metric.inner p u u) +
        Real.sqrt (P.metric.inner p (r • a) (r • a)) :=
      Geometry.Riemannian.sqrt_inner_add_le (I := I) P.metric p u (r • a)
    _ = Real.sqrt (P.metric.inner p u u) +
        |r| * Real.sqrt (P.metric.inner p a a) := by
      congr 1
      exact Geometry.Riemannian.sqrt_inner_smul
        (I := I) P.metric p r (show TangentSpace I p from a)
    _ <= Real.sqrt (P.metric.inner p u u) + R * D := by
      gcongr
    _ <= U := hu

section

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle fun x : M => TangentSpace I x]

omit [CompleteSpace E] in
theorem CurvatureJetTerm.eval_le_at_local
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u a b : E)
    (C : Nat -> Real) (hC : forall k, 0 <= C k)
    (B : IntrinsicJacobiJetAtom -> Real) (P : IntrinsicJacobiJetAtom -> Prop)
    {A : Real}
    (hcurv : forall (k : Nat) (x : M)
      (v : Fin (k + 3) -> TangentSpace I x),
      riemannianEDistOf (I := I) g p x <= ENNReal.ofReal A ->
      Real.sqrt
          (g.inner x (curvOpN (I := I) g k x v)
            (curvOpN (I := I) g k x v)) <=
        C k * ∏ i, Real.sqrt (g.inner x (v i) (v i)))
    (q : Real × Real)
    (hq : riemannianEDistOf (I := I) g p
        (intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) <=
      ENNReal.ofReal A)
    (hatom : forall (atom : IntrinsicJacobiJetAtom), P atom ->
        Real.sqrt
            (g.inner
              (intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (atom.eval (I := I) g hEnorm p u a b q)
              (atom.eval (I := I) g hEnorm p u a b q)) <=
          B atom) :
    forall term : CurvatureJetTerm, term.allAtoms P ->
        Real.sqrt
            (g.inner
              (intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (term.eval (I := I) g hEnorm p u a b q)
              (term.eval (I := I) g hEnorm p u a b q)) <=
          term.majorant C B := by
  intro term
  induction term with
  | zero =>
      intro hterm
      simp only [CurvatureJetTerm.eval, CurvatureJetTerm.majorant, map_zero,
        Real.sqrt_zero]
      exact le_rfl
  | atom atom =>
      intro hterm
      exact hatom atom hterm
  | add y z ihy ihz =>
      intro hterm
      let x :=
        intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      calc
        Real.sqrt
            (g.inner x
              ((y + z).eval (I := I) g hEnorm p u a b q)
              ((y + z).eval (I := I) g hEnorm p u a b q)) <=
            Real.sqrt
                (g.inner x
                  (y.eval (I := I) g hEnorm p u a b q)
                  (y.eval (I := I) g hEnorm p u a b q)) +
              Real.sqrt
                (g.inner x
                  (z.eval (I := I) g hEnorm p u a b q)
                  (z.eval (I := I) g hEnorm p u a b q)) := by
          simpa only [CurvatureJetTerm.eval] using
            Geometry.Riemannian.sqrt_inner_add_le (I := I) g x
              (y.eval (I := I) g hEnorm p u a b q)
              (z.eval (I := I) g hEnorm p u a b q)
        _ <= y.majorant C B + z.majorant C B :=
          add_le_add (ihy hterm.1) (ihz hterm.2)
        _ = (y + z).majorant C B := rfl
  | scale c y ih =>
      intro hterm
      let x :=
        intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      calc
        Real.sqrt
            (g.inner x
              ((c • y).eval (I := I) g hEnorm p u a b q)
              ((c • y).eval (I := I) g hEnorm p u a b q)) =
            |c| * Real.sqrt
              (g.inner x
                (y.eval (I := I) g hEnorm p u a b q)
                (y.eval (I := I) g hEnorm p u a b q)) := by
          rw [CurvatureJetTerm.eval.eq_def]
          exact Geometry.Riemannian.sqrt_inner_smul (I := I) g x c
            (y.eval (I := I) g hEnorm p u a b q)
        _ <= |c| * y.majorant C B :=
          mul_le_mul_of_nonneg_left (ih hterm) (abs_nonneg c)
        _ = (c • y).majorant C B := rfl
  | curv k slots ih =>
      intro hterm
      let x :=
        intrinsicLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      have hprod :
          (∏ i : Fin (k + 3),
              Real.sqrt
                (g.inner x
                  ((slots i).eval (I := I) g hEnorm p u a b q)
                  ((slots i).eval (I := I) g hEnorm p u a b q))) <=
            ∏ i : Fin (k + 3), (slots i).majorant C B := by
        apply Finset.prod_le_prod
        · intro i hi
          exact Real.sqrt_nonneg _
        · intro i hi
          exact ih i (hterm i)
      calc
        Real.sqrt
            (g.inner x
              ((CurvatureJetTerm.curv k slots).eval
                (I := I) g hEnorm p u a b q)
              ((CurvatureJetTerm.curv k slots).eval
                (I := I) g hEnorm p u a b q)) <=
            C k * ∏ i : Fin (k + 3),
              Real.sqrt
                (g.inner x
                  ((slots i).eval (I := I) g hEnorm p u a b q)
                  ((slots i).eval (I := I) g hEnorm p u a b q)) := by
          simpa only [CurvatureJetTerm.eval] using
            hcurv k x
              (fun i => (slots i).eval (I := I) g hEnorm p u a b q) hq
        _ <= C k * ∏ i : Fin (k + 3), (slots i).majorant C B :=
          mul_le_mul_of_nonneg_left hprod (hC k)
        _ = (CurvatureJetTerm.curv k slots).majorant C B := rfl
end

theorem intrinsic_jacobi_jet_pair_le_of_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {C0 U eps delta A : Real} (hC0 : 0 <= C0) (hAU : U <= A)
    (h0 : HasLocalCurvDerivBound (I := I) P p A 0 C0)
    (u a b : E) (n : Nat) (r : Real) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : Geometry.Riemannian.IsMetricNorm
        (I := I) (M := P.M) P.metric := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    let f : Real -> Real -> P.M := fun s t =>
      intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((s, 0), t)
    let W : forall s t : Real, TangentSpace I (f s t) := fun s t =>
      intrinsicLaunchJet (I := I) P.metric hEnorm p u a b n (s, t)
    let DW : forall t : Real, TangentSpace I (f r t) := fun t =>
      Geometry.Riemannian.Variation.covSnd (I := I) P.metric f W r t
    0 <= U ->
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <= U ->
    0 <= eps ->
    (forall t, t ∈ Ico (0 : Real) 1 ->
      Real.sqrt
          (P.metric.inner (f r t)
            (intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t))
            (intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t))) <=
        eps) ->
    Real.sqrt (P.metric.inner (f r 0) (W r 0) (W r 0)) <= delta ->
    Real.sqrt (P.metric.inner (f r 0) (DW 0) (DW 0)) <= delta ->
    (forall t, t ∈ Icc (0 : Real) 1 ->
      Real.sqrt (P.metric.inner (f r t) (W r t) (W r t)) <=
        gronwallBound delta (max (C0 * U ^ 2) 1) eps t) ∧
    (forall t, t ∈ Icc (0 : Real) 1 ->
      Real.sqrt (P.metric.inner (f r t) (DW t) (DW t)) <=
        gronwallBound delta (max (C0 * U ^ 2) 1) eps t) := by
  let _ := hconn
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : Geometry.Riemannian.IsMetricNorm
      (I := I) (M := P.M) P.metric := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  let f : Real -> Real -> P.M := fun s t =>
    intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((s, 0), t)
  let W : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    intrinsicLaunchJet (I := I) P.metric hEnorm p u a b n (s, t)
  let DW : forall t : Real, TangentSpace I (f r t) := fun t =>
    Geometry.Riemannian.Variation.covSnd (I := I) P.metric f W r t
  dsimp only
  intro hU hspeed heps hres hW0 hDW0
  change Real.sqrt (P.metric.inner (f r 0) (W r 0) (W r 0)) <= delta at hW0
  change Real.sqrt (P.metric.inner (f r 0) (DW 0) (DW 0)) <= delta at hDW0
  let u0 : TangentSpace I p :=
    show TangentSpace I p from u + r • a + (0 : Real) • b
  let K := C0 * U ^ 2
  have hK : 0 <= K := mul_nonneg hC0 (sq_nonneg U)
  have hWjoint :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f q.1 q.2) (W q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f, W] using
      intrinsicLaunchJet_smooth (I := I) P.metric hEnorm p u a b n
  have hDWjoint :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f q.1 q.2)
            (Geometry.Riemannian.Variation.covSnd
              (I := I) P.metric f W q.1 q.2) : TangentBundle I P.M)) := by
    exact Geometry.Riemannian.Variation.cov_snd_smooth
      (I := I) P.metric f W hWjoint
  let Q := (modelWithCornersSelf Real Real).prod
    (modelWithCornersSelf Real Real)
  have hr :
      ContMDiff (modelWithCornersSelf Real Real) Q ∞
        (fun t : Real => (r, t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hWslice :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun t : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f r t) (W r t) : TangentBundle I P.M)) := by
    exact hWjoint.comp hr
  have hDWslice :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun t : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f r t) (DW t) : TangentBundle I P.M)) := by
    dsimp only [DW]
    exact hDWjoint.comp hr
  have hODE : forall t, t ∈ Ico (0 : Real) 1 ->
      Real.sqrt
          (P.metric.inner (f r t)
            (Geometry.Riemannian.Variation.covSnd2
              (I := I) P.metric f W r t)
            (Geometry.Riemannian.Variation.covSnd2
              (I := I) P.metric f W r t)) <=
        K * Real.sqrt (P.metric.inner (f r t) (W r t) (W r t)) +
          eps := by
    intro t ht
    let T := Geometry.Riemannian.Variation.varSnd (I := I) f r t
    let R := Geometry.Riemannian.Variation.jacobianCurv
      (I := I) P.metric f W r t
    let L : TangentSpace I (f r t) -> Real := fun z =>
      Real.sqrt (P.metric.inner (f r t) z z)
    have hspeedSq :
        P.metric.inner (f r t) T T = P.metric.inner p u0 u0 := by
      have hspeedEq :=
        intrinsicGeodesic_speedSq_eq
          (I := I) P.metric hEnorm p u0 t
      dsimp only [T, f, u0, intrinsicLaunch3,
        Geometry.Riemannian.Variation.varSnd, curveVelocity]
      apply eq_of_heq
      exact heq_of_eq hspeedEq
    have hLT : L T <= U := by
      dsimp only [L]
      rw [hspeedSq]
      simpa only [u0, zero_smul, add_zero] using hspeed
    have hrt : (0 : Real) <= t := ht.1
    have ht1 : t <= 1 := ht.2.le
    have hspeed_u0 : Real.sqrt (P.metric.inner p u0 u0) <= U := by
      simpa only [u0, zero_smul, add_zero] using hspeed
    have hdist : riemannianEDist I p (f r t) <= ENNReal.ofReal A := by
      have hgeo := intrinsicGeodesic_riemannianEDist_le (I := I) P.metric hEnorm p u0
        (s := 0) (t := t) hrt
      have hzero : intrinsicGeodesic (I := I) P.metric hEnorm p u0 0 = p :=
        intrinsicGeodesic_zero (I := I) P.metric hEnorm p u0
      rw [hzero, sub_zero] at hgeo
      have hft : f r t = intrinsicGeodesic (I := I) P.metric hEnorm p u0 t := by
        simp only [f, u0, intrinsicLaunch3]
      rw [hft]
      refine hgeo.trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hU0 : 0 <= U := (Real.sqrt_nonneg _).trans hspeed_u0
      calc Real.sqrt (P.metric.inner p u0 u0) * t
          <= U * 1 := mul_le_mul hspeed_u0 ht1 hrt hU0
        _ = U := by ring
        _ <= A := hAU
    have hfball : riemannianEDistOf (I := I) P.metric p (f r t) <= ENNReal.ofReal A := by
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) P.metric hEnorm]
      exact hdist
    have hRraw :=
      HasCurvDerivBound.curvature_along_le_local (I := I) P p h0
        (fun v : Real => f r v) (fun v : Real => W r v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r v) t hfball
    have hR : L R <= K * L (W r t) := by
      have hmain :
          L R <= C0 * L (W r t) * L T * L T := by
        simpa only [L, R, T,
          Geometry.Riemannian.Variation.jacobianCurv,
          Geometry.Riemannian.Variation.curvAlong] using hRraw
      calc
        L R <= C0 * L (W r t) * L T * L T := hmain
        _ <= C0 * L (W r t) * U * U := by
          gcongr
        _ = K * L (W r t) := by
          dsimp only [K]
          ring
    have hresEq :
        Geometry.Riemannian.Variation.covSnd2
              (I := I) P.metric f W r t + R =
          intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t) := by
      rfl
    have hD2 :
        Geometry.Riemannian.Variation.covSnd2
            (I := I) P.metric f W r t =
          intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t) - R :=
      eq_sub_of_add_eq hresEq
    change L
        (Geometry.Riemannian.Variation.covSnd2
          (I := I) P.metric f W r t) <=
      K * L (W r t) + eps
    rw [hD2, sub_eq_add_neg]
    calc
      L
          (intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t) +
            -R) <=
          L (intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t)) +
            L (-R) := by
        exact Geometry.Riemannian.sqrt_inner_add_le
          (I := I) P.metric (f r t)
          (intrinsicJetResidual (I := I) P.metric hEnorm p u a b n (r, t)) (-R)
      _ = L (intrinsicJetResidual
            (I := I) P.metric hEnorm p u a b n (r, t)) + L R := by
        congr 1
        simpa only [L, neg_one_smul, abs_neg, abs_one, one_mul] using
          (Geometry.Riemannian.sqrt_inner_smul
            (I := I) P.metric (f r t) (-1 : Real) R)
      _ <= eps + K * L (W r t) := add_le_add (hres t ht) hR
      _ = K * L (W r t) + eps := add_comm _ _
  have hfr : f r = intrinsicGeodesic (I := I) P.metric hEnorm p u0 := by
    funext v
    simp only [f, u0, intrinsicLaunch3]
  rw [hfr] at hW0
  dsimp only [DW, Geometry.Riemannian.Variation.covSnd] at hDW0
  rw [hfr] at hDW0
  have hbounds :=
    Geometry.Riemannian.VolumeComparison.intrinsicForce_pair
      (I := I) P.metric hEnorm p u0 (fun t => W r t)
      hK heps (by norm_num : (0 : Real) < 1)
      (by simpa only [u0, f, intrinsicLaunch3] using hWslice)
      (by simpa only [u0, f, DW, W, intrinsicLaunch3,
        Geometry.Riemannian.Variation.covSnd] using hDWslice)
      (by
        have h := hODE
        simp only [Geometry.Riemannian.Variation.covSnd,
          Geometry.Riemannian.Variation.covSnd2] at h ⊢
        rw [hfr] at h
        exact h)
      hW0 hDW0
  change
    (∀ t ∈ Icc (0 : Real) 1,
      Real.sqrt
          (P.metric.inner
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
            (W r t) (W r t)) <=
        gronwallBound delta (max K 1) eps t) ∧
      ∀ t ∈ Icc (0 : Real) 1,
        Real.sqrt
            (P.metric.inner
              (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
              (covDerivAlong (I := I) P.metric
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0)
                (fun s => W r s) t)
              (covDerivAlong (I := I) P.metric
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0)
                (fun s => W r s) t)) <=
          gronwallBound delta (max K 1) eps t
  exact hbounds
theorem intrinsic_jacobi_jets_le_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {R U D A : Real} (hD : 0 <= D) (hAU : U <= A)
    (hbnd : LocalBoundedGeometryOn (I := I) P p A)
    (u : E) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : Geometry.Riemannian.IsMetricNorm
        (I := I) (M := P.M) P.metric := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    let leafNorm : E -> E -> IntrinsicJacobiJetAtom -> Real -> Real -> Real :=
      fun a b atom r t =>
        Real.sqrt
          (P.metric.inner
            (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t)))
    Real.sqrt (P.metric.inner p u u) + R * D <= U ->
    forall n (a b : E),
      Real.sqrt (P.metric.inner p a a) <= D ->
      Real.sqrt (P.metric.inner p b b) <= D ->
      forall r, |r| <= R ->
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bJet k) r t <= jacobiJetBound hbnd.C U D n) ∧
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bTime k) r t <= jacobiJetBound hbnd.C U D n) := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : Geometry.Riemannian.IsMetricNorm
      (I := I) (M := P.M) P.metric := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hu n
  induction n with
  | zero =>
      intro a b ha hb r hr
      have hU : 0 <= U := by
        have hR : 0 <= R := (abs_nonneg r).trans hr
        exact
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hR hD)).trans hu
      have hspeed :
          Real.sqrt
              (P.metric.inner p (u + r • a) (u + r • a)) <= U :=
        localLaunchSpeed_le (I := I) P p u a ha hr hD hu
      have hpair :=
        intrinsic_jacobi_jet_pair_le_of_local (I := I) P hcomplete hconn p
          (C0 := hbnd.C 0) (U := U) (eps := 0) (delta := D) (A := A)
          (hbnd.nonneg 0) hAU (hbnd.bound 0) u a b 0 r
          hU hspeed (by norm_num)
          (by
            intro t ht
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <= 0
            rw [intrinsicJetResidual_zero (I := I) P.metric hEnorm p u a b r t]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrinsicJacobiJetAtom.b_jet_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using hD)
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrinsicJacobiJetAtom.b_time_zero]
            let u0 : TangentSpace I p :=
              show TangentSpace I p from u + r • a + (0 : Real) • b
            change Real.sqrt
              (P.metric.inner
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0) b b) <= D
            rw [intrinsicGeodesic_zero
              (I := I) P.metric hEnorm p u0]
            exact hb)
      have hrate : 0 <= jacobiJetGrowthRate hbnd.C U := (jacobi_jet_growth_rate_pos hbnd.C U).le
      constructor
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <=
                gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 t
            simpa only [jacobiJetGrowthRate] using hpair.1 t ht
          _ <= gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jacobiJetBound hbnd.C U D 0 := rfl
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)) <=
                gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 t
            simpa only [jacobiJetGrowthRate] using hpair.2 t ht
          _ <= gronwallBound D (jacobiJetGrowthRate hbnd.C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jacobiJetBound hbnd.C U D 0 := rfl
  | succ n ih =>
      intro a b ha hb r hr
      have hU : 0 <= U := by
        have hR : 0 <= R := (abs_nonneg r).trans hr
        exact
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hR hD)).trans hu
      have hspeed :
          Real.sqrt
              (P.metric.inner p (u + r • a) (u + r • a)) <= U :=
        localLaunchSpeed_le (I := I) P p u a ha hr hD hu
      have hprev := ih a b ha hb r hr
      have hself := ih a a ha ha r hr
      have hcap : 0 <= jacobiJetBound hbnd.C U D n :=
        jacobi_jet_bound_nonneg hbnd.C hD n
      have heps : 0 <= jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n :=
        jacobi_jet_forcing_bound_nonneg hbnd.C hbnd.nonneg hU hcap n
      have hres : forall t, t ∈ Ico (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrinsicJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
            jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n := by
        intro t ht
        rw [show intrinsicJetResidual
              (I := I) P.metric hEnorm p u a b (n + 1) (r, t) =
            (intrinsicJacobiResidualTerm (n + 1)).eval
              (I := I) P.metric hEnorm p u a b (r, t) by
          exact congrFun
            (congrFun
              (intrinsic_jacobi_residual_term_eval
                (I := I) P.metric hEnorm p u a b (n + 1)) r) t]
        have hqt : riemannianEDistOf (I := I) P.metric p
            (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t)) <=
              ENNReal.ofReal A := by
          have ht0 : (0 : Real) <= t := ht.1
          have ht1 : t <= 1 := ht.2.le
          have hlaunch :
              intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t) =
                intrinsicGeodesic (I := I) P.metric hEnorm p (u + r • a) t := by
            simp only [intrinsicLaunch3, zero_smul, add_zero]
          rw [hlaunch]
          exact (intrinsicGeodesic_riemannianEDistOf_le (I := I) P hcomplete hconn
            hEnorm p (u + r • a) hspeed ht0 ht1).trans
            (ENNReal.ofReal_le_ofReal hAU)
        apply CurvatureJetTerm.eval_le_at_local
          (I := I) P.metric hEnorm p u a b hbnd.C hbnd.nonneg
          (jacobiJetAtomBound U (jacobiJetBound hbnd.C U D n))
          (fun atom => atom.atMost n) (A := A)
          (fun k x v hx =>
            HasCurvDerivBound.curv_op_n_le_local
              (I := I) P p (hbnd.bound k) x hx v)
          (r, t) hqt
        · intro atom hatom
          have hbaseSelf :
              intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t) =
                intrinsicLaunch3 (I := I) P.metric hEnorm p u a a ((r, 0), t) := by
            simp only [intrinsicLaunch3, zero_smul, add_zero]
          cases atom with
          | pathT =>
              let u0 : TangentSpace I p :=
                show TangentSpace I p from
                  u + r • a + (0 : Real) • b
              have hspeedSq :=
                intrinsicGeodesic_speedSq_eq
                  (I := I) P.metric hEnorm p u0 t
              change Real.sqrt
                  (P.metric.inner
                    (intrinsicLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))) <= U
              rw [show P.metric.inner
                    (intrinsicLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrinsicJacobiJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t)) =
                  P.metric.inner p (u + r • a) (u + r • a) by
                simp only [IntrinsicJacobiJetAtom.eval, intrinsicLaunch3, varSnd]
                change P.metric.inner
                    (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
                    (mfderiv 𝓘(Real, Real) I
                      (fun v => intrinsicGeodesic
                        (I := I) P.metric hEnorm p u0 v) t 1)
                    (mfderiv 𝓘(Real, Real) I
                      (fun v => intrinsicGeodesic
                        (I := I) P.metric hEnorm p u0 v) t 1) =
                  P.metric.inner p (u + r • a) (u + r • a)
                have hfun :
                    (fun v => intrinsicGeodesic
                      (I := I) P.metric hEnorm p u0 v) =
                      intrinsicGeodesic (I := I) P.metric hEnorm p u0 := rfl
                rw [hfun, hspeedSq]
                simp only [u0, zero_smul, add_zero]]
              exact hspeed
          | pathDt =>
              rw [IntrinsicJacobiJetAtom.path_dt_zero]
              simpa only [jacobiJetAtomBound, map_zero, Real.sqrt_zero] using
                (le_refl (0 : Real))
          | aJet k =>
              rw [IntrinsicJacobiJetAtom.a_jet_eq_self]
              rw [hbaseSelf]
              simpa only [jacobiJetAtomBound] using hself.1 k hatom t ⟨ht.1, ht.2.le⟩
          | aTime k =>
              rw [IntrinsicJacobiJetAtom.a_time_eq_self]
              rw [hbaseSelf]
              simpa only [jacobiJetAtomBound] using hself.2 k hatom t ⟨ht.1, ht.2.le⟩
          | bJet k =>
              simpa only [jacobiJetAtomBound] using hprev.1 k hatom t ⟨ht.1, ht.2.le⟩
          | bTime k =>
              simpa only [jacobiJetAtomBound] using hprev.2 k hatom t ⟨ht.1, ht.2.le⟩
        · exact intrinsic_jacobi_residual_term_all_atoms n
      have hpair :=
        intrinsic_jacobi_jet_pair_le_of_local (I := I) P hcomplete hconn p
          (C0 := hbnd.C 0) (U := U) (A := A)
          (eps := jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) (delta := 0)
          (hbnd.nonneg 0) hAU (hbnd.bound 0) u a b (n + 1) r
          hU hspeed heps hres
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrinsicJacobiJetAtom.b_jet_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrinsicJacobiJetAtom.b_time_succ_time_zero]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
      have hrate : 0 <= jacobiJetGrowthRate hbnd.C U := (jacobi_jet_growth_rate_pos hbnd.C U).le
      have hnewPos : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jacobiJetBound hbnd.C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
                (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrinsicLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
                gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
                  (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) t
            simpa only [jacobiJetGrowthRate] using hpair.1 t ht
          _ <= gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
              (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jacobiJetBound hbnd.C U D (n + 1) :=
            jacobi_jet_bound_step_le hbnd.C U D n
      have hnewTime : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jacobiJetBound hbnd.C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrinsicJacobiJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
                (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrinsicLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrinsicLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrinsicLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)) <=
                gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
                  (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) t
            simpa only [jacobiJetGrowthRate] using hpair.2 t ht
          _ <= gronwallBound 0 (jacobiJetGrowthRate hbnd.C U)
              (jacobiJetForcingBound hbnd.C U (jacobiJetBound hbnd.C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jacobiJetBound hbnd.C U D (n + 1) :=
            jacobi_jet_bound_step_le hbnd.C U D n
      constructor
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.1 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jacobi_jet_bound_le_succ hbnd.C U D n)
        · exact hnewPos t ht
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.2 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jacobi_jet_bound_le_succ hbnd.C U D n)
        · exact hnewTime t ht

def CurvatureJetTerm.curvOrderAtMost (N : Nat) : CurvatureJetTerm → Prop
  | .zero => True
  | .atom _ => True
  | .add x y => x.curvOrderAtMost N ∧ y.curvOrderAtMost N
  | .scale _ x => x.curvOrderAtMost N
  | .curv k slots => k ≤ N ∧ ∀ i, (slots i).curvOrderAtMost N

theorem CurvatureJetTerm.curvOrderAtMost.mono {N N' : Nat} (hNN : N ≤ N') :
    ∀ {t : CurvatureJetTerm}, t.curvOrderAtMost N → t.curvOrderAtMost N' := by
  intro t
  induction t with
  | zero => intro _; trivial
  | atom a => intro _; trivial
  | add x y ihx ihy => intro h; exact ⟨ihx h.1, ihy h.2⟩
  | scale c x ih => intro h; exact ih h
  | curv k slots ih => intro h; exact ⟨h.1.trans hNN, fun i => ih i (h.2 i)⟩

theorem CurvatureJetTerm.curvOrderAtMost_finSum {N : Nat} :
    ∀ {n : Nat} (terms : Fin n → CurvatureJetTerm),
      (∀ i, (terms i).curvOrderAtMost N) →
        (CurvatureJetTerm.finSum terms).curvOrderAtMost N := by
  intro n
  induction n with
  | zero => intro terms _; trivial
  | succ n ih =>
      intro terms h
      simp only [CurvatureJetTerm.finSum]
      exact ⟨h 0, ih (fun i => terms i.succ) (fun i => h i.succ)⟩

theorem CurvatureJetTerm.curvOrderAtMost_launchDeriv {N : Nat} :
    ∀ {t : CurvatureJetTerm}, t.curvOrderAtMost N →
      t.launchDeriv.curvOrderAtMost (N + 1) := by
  intro t
  induction t with
  | zero => intro _; trivial
  | atom a =>
      intro _
      cases a with
      | pathT => trivial
      | pathDt => trivial
      | aJet n => trivial
      | bJet n => trivial
      | aTime n =>
          simp only [CurvatureJetTerm.launchDeriv, CurvatureJetTerm.curvOrderAtMost]
          constructor
          · trivial
          · constructor
            · omega
            · intro i
              fin_cases i <;> trivial
      | bTime n =>
          simp only [CurvatureJetTerm.launchDeriv, CurvatureJetTerm.curvOrderAtMost]
          constructor
          · trivial
          · constructor
            · omega
            · intro i
              fin_cases i <;> trivial
  | add x y ihx ihy => intro h; exact ⟨ihx h.1, ihy h.2⟩
  | scale c x ih => intro h; exact ih h
  | curv k slots ih =>
      intro h
      have hk : k ≤ N := h.1
      have hslots : ∀ i, (slots i).curvOrderAtMost N := h.2
      have hupd : ∀ (i : Fin (k + 3)), ∀ j : Fin (k + 3),
          CurvatureJetTerm.curvOrderAtMost (N + 1)
            (Function.update slots i ((slots i).launchDeriv) j) := by
        intro i j
        by_cases hji : j = i
        · rw [hji, Function.update_self]
          exact ih i (hslots i)
        · rw [Function.update_of_ne hji]
          exact (hslots j).mono (Nat.le_succ N)
      simp only [CurvatureJetTerm.launchDeriv, CurvatureJetTerm.curvOrderAtMost]
      constructor
      · constructor
        · omega
        · intro i
          exact Fin.cases trivial (fun j => (hslots j).mono (Nat.le_succ N)) i
      · apply CurvatureJetTerm.curvOrderAtMost_finSum
        intro i
        exact ⟨by omega, hupd i⟩

theorem intrinsicJacobiCorrectionTerm.curvOrderAtMost (m : Nat) :
    (intrinsicJacobiCorrectionTerm m).curvOrderAtMost 1 := by
  simp only [intrinsicJacobiCorrectionTerm, CurvatureJetTerm.curvOrderAtMost]
  repeat' first | constructor | (intro i; fin_cases i <;> trivial)

theorem intrinsicJacobiResidualTerm.curvOrderAtMost (n : Nat) :
    (intrinsicJacobiResidualTerm n).curvOrderAtMost n := by
  induction n with
  | zero => trivial
  | succ n ih =>
      simp only [intrinsicJacobiResidualTerm, CurvatureJetTerm.curvOrderAtMost]
      constructor
      · exact CurvatureJetTerm.curvOrderAtMost_launchDeriv ih
      · exact (intrinsicJacobiCorrectionTerm.curvOrderAtMost n).mono (by omega)

theorem intrinsic_metric_jet_le_of_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {A : Real} (hbnd : LocalBoundedGeometryOn (I := I) P p A)
    (u a b : E) (n : Nat) {U D : Real} (hD : 0 ≤ D) (hAU : U ≤ A) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    Real.sqrt (P.metric.inner p u u) ≤ U →
    Real.sqrt (P.metric.inner p a a) ≤ D →
    Real.sqrt (P.metric.inner p b b) ≤ D →
    |intrinsicMetricJet (I := I) P.metric hEnorm p u a b n 0| ≤
      2 ^ n * jacobiJetBound hbnd.C U D n ^ 2 := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hu ha hb
  have hjets :=
    intrinsic_jacobi_jets_le_local (I := I) P hcomplete hconn p
      (R := 0) (U := U) (D := D) (A := A) hD hAU hbnd u
      (by simpa using hu)
      n a b ha hb 0 (by simp)
  apply intrinsic_metric_jet_abs_le (I := I) P.metric hEnorm p u a b n 0
    (jacobiJetBound hbnd.C U D n) (jacobi_jet_bound_nonneg hbnd.C hD n)
  intro k hk
  simpa only [IntrinsicJacobiJetAtom.eval, intrinsicLaunchJet] using
    hjets.1 k hk 1 (by constructor <;> norm_num)

theorem intrinsic_frame_metric_iterated_fderiv_norm_le_local
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (p : P.M) {A : Real} (hbnd : LocalBoundedGeometryOn (I := I) P p A)
    (z : E) (n : Nat) (U : Real) (hAU : U ≤ A)
    (hzU : ‖z‖ ≤ U) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : IsManifold I 1 P.M :=
      IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    letI : ConnectedSpace P.M := hconn
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      with_unfolding_all
        exact
          Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
            (I := I) P.metric x v
    ContDiffAt Real ∞
        (intrinsicFrameMetric (I := I) P.metric hEnorm p) z →
      ‖iteratedFDeriv Real n
          (intrinsicFrameMetric (I := I) P.metric hEnorm p) z‖ ≤
        ContinuousMultilinearMap.polarConst n *
          (2 * (2 ^ n * jacobiJetBound hbnd.C U 1 n ^ 2)) := by
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := ∞) (by decide)
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  let _ : T2Space P.M := P.t2
  let _ : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  let _ : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  let _ : (x : P.M) → InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  let _ : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  let _ : EMetricSpace P.M := P.emetricSpace (I := I)
  let _ : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let _ : ConnectedSpace P.M := hconn
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    with_unfolding_all
      exact
        Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v
  dsimp only
  intro hsmooth
  let A :=
    iteratedFDeriv Real n
      (intrinsicFrameMetric (I := I) P.metric hEnorm p) z
  let S : Real := 2 ^ n * jacobiJetBound hbnd.C U 1 n ^ 2
  have hS : 0 ≤ S := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have htwoS : 0 ≤ 2 * S := mul_nonneg (by norm_num) hS
  have hAsymm : A.IsSymmetric := by
    intro σ
    exact iterFDeriv_perm hsmooth σ
  have hdiag :
      ∀ a : E, ‖a‖ ≤ 1 → ‖A (fun _ => a)‖ ≤ 2 * S := by
    intro a ha
    let B : E →L[Real] E →L[Real] Real := A (fun _ => a)
    have hBsymm : ∀ v w : E, B v w = B w v := by
      intro v w
      have hmetric :
          (fun y : E =>
              intrinsicFrameMetric (I := I) P.metric hEnorm p y v w) =
            fun y : E =>
              intrinsicFrameMetric (I := I) P.metric hEnorm p y w v := by
        funext y
        rw [intrinsicFrameMetric_apply, intrinsicFrameMetric_apply]
        exact P.metric.symm _ _ _
      calc
        B v w =
            iteratedFDeriv Real n
              (fun y : E =>
                intrinsicFrameMetric (I := I) P.metric hEnorm p y v w) z
              (fun _ => a) := by
          exact (iterFDeriv_apply₂ hsmooth n v w (fun _ => a)).symm
        _ = iteratedFDeriv Real n
              (fun y : E =>
                intrinsicFrameMetric (I := I) P.metric hEnorm p y w v) z
              (fun _ => a) := by rw [hmetric]
        _ = B w v :=
          iterFDeriv_apply₂ hsmooth n w v (fun _ => a)
    have hBdiag : ∀ b : E, ‖b‖ ≤ 1 → |B b b| ≤ S := by
      intro b hb
      have hzu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p z)
                (normalFrame (I := I) P.metric p z)) ≤ U := by
        simpa only [normalFrame_sqrt] using hzU
      have hau :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p a)
                (normalFrame (I := I) P.metric p a)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using ha
      have hbu :
          Real.sqrt
              (P.metric.inner p
                (normalFrame (I := I) P.metric p b)
                (normalFrame (I := I) P.metric p b)) ≤ 1 := by
        simpa only [normalFrame_sqrt] using hb
      have hjet :=
        intrinsic_metric_jet_le_of_local (I := I) P hcomplete hconn p hbnd
          (normalFrame (I := I) P.metric p z)
          (normalFrame (I := I) P.metric p a)
          (normalFrame (I := I) P.metric p b) n
          (U := U) (D := 1) (by norm_num) hAU hzu hau hbu
      change
        |iteratedFDeriv Real n
            (intrinsicFrameMetric (I := I) P.metric hEnorm p) z
            (fun _ => a) b b| ≤ S
      rw [intrinsicMetric_diag_jet (I := I) P.metric hEnorm p z a b n
        hsmooth]
      exact hjet
    have hB :=
      ContinuousLinearMap.opNorm_le_diag2 B hBsymm hS hBdiag
    simpa only [B] using hB
  have hbound :=
    ContinuousMultilinearMap.opNorm_le_diag_unit
      hAsymm htwoS hdiag
  simpa only [A, S] using hbound
end CheegerGromovCompactness
end DifferentialGeometry
