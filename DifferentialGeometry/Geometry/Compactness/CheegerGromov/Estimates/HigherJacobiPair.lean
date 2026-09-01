import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicGronwall
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Estimates.HigherCurvatureJet
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Estimates.HigherJacobiForce
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.CurvatureOperatorBounds

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

open Geometry.Riemannian.CovariantDerivativeAlong
open Geometry.Riemannian.Exponential
open Geometry.Riemannian.Variation

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

def jetLeafCap (U B : Real) : IntrJetAtom -> Real
  | .pathT => U
  | .pathDt => 0
  | .aJet _ => B
  | .aTime _ => B
  | .bJet _ => B
  | .bTime _ => B

def jetRate (C : Nat -> Real) (U : Real) : Real :=
  max (C 0 * U ^ 2) 1

def jetEps (C : Nat -> Real) (U B : Real) (n : Nat) : Real :=
  (intrResidualTerm (n + 1)).majorant C (jetLeafCap U B)

def jetCap (C : Nat -> Real) (U D : Real) : Nat -> Real
  | 0 => gronwallBound D (jetRate C U) 0 1
  | n + 1 =>
      max (jetCap C U D n)
        (gronwallBound 0 (jetRate C U)
          (jetEps C U (jetCap C U D n) n) 1)

theorem jetLeafCap_nonneg
    {U B : Real} (hU : 0 <= U) (hB : 0 <= B) :
    forall atom, 0 <= jetLeafCap U B atom := by
  intro atom
  cases atom <;> simp only [jetLeafCap, hU, hB, le_refl]

theorem jetRate_pos (C : Nat -> Real) (U : Real) :
    0 < jetRate C U := by
  exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem jetEps_nonneg
    (C : Nat -> Real) {U B : Real}
    (hC : forall k, 0 <= C k) (hU : 0 <= U) (hB : 0 <= B)
    (n : Nat) :
    0 <= jetEps C U B n := by
  exact CurvJetTerm.majorant_nonneg C (jetLeafCap U B) hC
    (jetLeafCap_nonneg hU hB) (intrResidualTerm (n + 1))

theorem jetCap_nonneg
    (C : Nat -> Real) {U D : Real} (hD : 0 <= D) :
    forall n, 0 <= jetCap C U D n := by
  intro n
  induction n with
  | zero =>
      rw [jetCap, gronwallBound_ε0]
      exact mul_nonneg hD (Real.exp_pos _).le
  | succ n ih =>
      rw [jetCap]
      exact ih.trans (le_max_left _ _)

theorem jetCap_le_succ
    (C : Nat -> Real) (U D : Real) (n : Nat) :
    jetCap C U D n <= jetCap C U D (n + 1) := by
  rw [jetCap]
  exact le_max_left _ _

theorem jetCap_step_le
    (C : Nat -> Real) (U D : Real) (n : Nat) :
    gronwallBound 0 (jetRate C U)
        (jetEps C U (jetCap C U D n) n) 1 <=
      jetCap C U D (n + 1) := by
  rw [jetCap]
  exact le_max_right _ _

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem launch_speed_le
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

private theorem jac_force_cap
    {C0 C1 U BA BB LA LT LJ LK LDJ LF : Real}
    (hC0 : 0 <= C0) (hC1 : 0 <= C1) (hU : 0 <= U)
    (hBA : 0 <= BA) (hBB : 0 <= BB)
    (hLA0 : 0 <= LA) (hLT0 : 0 <= LT) (hLJ0 : 0 <= LJ)
    (hLK0 : 0 <= LK) (hLDJ0 : 0 <= LDJ)
    (hLA : LA <= BA) (hLT : LT <= U) (hLJ : LJ <= BB)
    (hLK : LK <= BA) (hLDJ : LDJ <= BB)
    (hLF :
      LF <=
        C1 * LT * LA * LT * LJ +
          C0 * LK * LT * LJ +
          2 * (C0 * LA * LT * LDJ) +
          C1 * LA * LJ * LT * LT +
          C0 * LJ * LK * LT +
          C0 * LJ * LT * LK) :
    LF <= (2 * C1 * U ^ 2 + 5 * C0 * U) * BA * BB := by
  calc
    LF <=
        C1 * LT * LA * LT * LJ +
          C0 * LK * LT * LJ +
          2 * (C0 * LA * LT * LDJ) +
          C1 * LA * LJ * LT * LT +
          C0 * LJ * LK * LT +
          C0 * LJ * LT * LK := hLF
    _ <=
        C1 * U * BA * U * BB +
          C0 * BA * U * BB +
          2 * (C0 * BA * U * BB) +
          C1 * BA * BB * U * U +
          C0 * BB * BA * U +
          C0 * BB * U * BA := by
      gcongr
    _ = (2 * C1 * U ^ 2 + 5 * C0 * U) * BA * BB := by
      ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrJacobi_pair_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    {C0 : Real} (hC0 : 0 <= C0)
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (p : P.M) (u w : E) {b : Real} (hb : 0 < b) :
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
    let γ : Real -> P.M :=
      intrinsicGeodesic (I := I) P.metric hEnorm p u
    let J : ∀ t : Real, TangentSpace I (γ t) :=
      intrinsicJacobi (I := I) P.metric hEnorm p u w
    let U := Real.sqrt (P.metric.inner p u u)
    let K := C0 * U ^ 2
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt (P.metric.inner (γ t) (J t) (J t)) <=
        gronwallBound (Real.sqrt (P.metric.inner p w w))
          (max K 1) 0 t) ∧
    (∀ t ∈ Icc (0 : Real) b,
      Real.sqrt
          (P.metric.inner (γ t)
            (covDerivAlong (I := I) P.metric γ J t)
            (covDerivAlong (I := I) P.metric γ J t)) <=
        gronwallBound (Real.sqrt (P.metric.inner p w w))
          (max K 1) 0 t) := by
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
  let γ : Real -> P.M :=
    intrinsicGeodesic (I := I) P.metric hEnorm p u
  let J : ∀ t : Real, TangentSpace I (γ t) :=
    intrinsicJacobi (I := I) P.metric hEnorm p u w
  let U := Real.sqrt (P.metric.inner p u u)
  let K := C0 * U ^ 2
  have hK : 0 <= K := by
    exact mul_nonneg hC0 (sq_nonneg U)
  have hJac : IsJacobiAlong (I := I) P.metric γ J := by
    change IsJacobiAlong (I := I) P.metric
      (intrinsicGeodesic (I := I) P.metric hEnorm p
        (show TangentSpace I p from u))
      (intrinsicJacobi (I := I) P.metric hEnorm p
        (show TangentSpace I p from u) (show TangentSpace I p from w))
    exact Geometry.Riemannian.intrinsic_jacobi
      (I := I) P.metric hEnorm p u w
  have hODE : ∀ t ∈ Ico (0 : Real) b,
      Real.sqrt
          (P.metric.inner (γ t)
            (covDerivAlong (I := I) P.metric γ
              (fun s => covDerivAlong (I := I) P.metric γ J s) t)
            (covDerivAlong (I := I) P.metric γ
              (fun s => covDerivAlong (I := I) P.metric γ J s) t)) <=
        K * Real.sqrt (P.metric.inner (γ t) (J t) (J t)) := by
    intro t _ht
    let T : ∀ s : Real, TangentSpace I (γ s) :=
      fun s => curveVelocity (I := I) γ s
    let R : TangentSpace I (γ t) :=
      Geometry.Riemannian.Variation.curvAlong
        (I := I) P.metric γ J T T t
    have hD2 := (isJacobiAlong_iff (I := I) P.metric γ J).mp hJac t
    have hR :=
      curvAlong_le (I := I) P h0 γ J T T t
    have hspeedSq :
        P.metric.inner (γ t) (T t) (T t) =
          P.metric.inner p u u := by
      dsimp only [γ, T, curveVelocity]
      apply eq_of_heq
      exact heq_of_eq
        (intrinsicGeodesic_speedSq_eq
          (I := I) P.metric hEnorm p (show TangentSpace I p from u) t)
    have hspeed :
        Real.sqrt (P.metric.inner (γ t) (T t) (T t)) = U := by
      rw [hspeedSq]
    rw [hD2]
    change Real.sqrt (P.metric.inner (γ t) (-R) (-R)) <= _
    rw [show P.metric.inner (γ t) (-R) (-R) =
        P.metric.inner (γ t) R R by simp]
    calc
      Real.sqrt (P.metric.inner (γ t) R R) <=
          C0 * Real.sqrt (P.metric.inner (γ t) (J t) (J t)) *
            Real.sqrt (P.metric.inner (γ t) (T t) (T t)) *
            Real.sqrt (P.metric.inner (γ t) (T t) (T t)) := by
        simpa only [R, T] using hR
      _ = K * Real.sqrt (P.metric.inner (γ t) (J t) (J t)) := by
        rw [hspeed]
        dsimp only [K]
        ring
  simpa only [γ, J, U, K] using
    (Geometry.Riemannian.VolumeComparison.intrJacobi_pair
      (I := I) P.metric hEnorm p u w hK hb hODE)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrMix_force_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    {C0 C1 : Real} (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (h1 : HasCurvDerivBound (I := I) P 1 C1)
    (p : P.M) (u a b : E) {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
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
    let f : Real -> Real -> P.M := fun r s =>
      intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), s)
    let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
      intrLaunchJ (I := I) P.metric hEnorm p u a b (r, s)
    let F := Geometry.Riemannian.Variation.jacVarForce
      (I := I) P.metric f V t
    let U := Real.sqrt (P.metric.inner p u u)
    let K := C0 * U ^ 2
    let BA := gronwallBound (Real.sqrt (P.metric.inner p a a))
      (max K 1) 0 1
    let BB := gronwallBound (Real.sqrt (P.metric.inner p b b))
      (max K 1) 0 1
    Real.sqrt (P.metric.inner (f 0 t) F F) <=
      (2 * C1 * U ^ 2 + 5 * C0 * U) * BA * BB := by
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
  let f : Real -> Real -> P.M := fun r s =>
    intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), s)
  let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
    intrLaunchJ (I := I) P.metric hEnorm p u a b (r, s)
  let A := Geometry.Riemannian.Variation.varFst (I := I) f 0 t
  let T := Geometry.Riemannian.Variation.varSnd (I := I) f 0 t
  let J := V 0 t
  let KA := Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
    (fun r s => Geometry.Riemannian.Variation.varFst (I := I) f r s) 0 t
  let DJ := Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V 0 t
  let F := Geometry.Riemannian.Variation.jacVarForce
    (I := I) P.metric f V t
  let L : TangentSpace I (f 0 t) -> Real := fun z =>
    Real.sqrt (P.metric.inner (f 0 t) z z)
  let U := Real.sqrt (P.metric.inner p u u)
  let K := C0 * U ^ 2
  let BA := gronwallBound (Real.sqrt (P.metric.inner p a a))
    (max K 1) 0 1
  let BB := gronwallBound (Real.sqrt (P.metric.inner p b b))
    (max K 1) 0 1
  have hK : 0 <= K := mul_nonneg hC0 (sq_nonneg U)
  have hmaxK : 0 <= max K 1 := by
    exact le_trans (by norm_num) (le_max_right K 1)
  have hBA : 0 <= BA := by
    dsimp only [BA]
    rw [gronwallBound_ε0]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hBB : 0 <= BB := by
    dsimp only [BB]
    rw [gronwallBound_ε0]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hpairA :=
    intrJacobi_pair_le (I := I) P hcomplete hconn hC0 h0 p u a
      (b := 1) (by norm_num)
  have hpairB :=
    intrJacobi_pair_le (I := I) P hcomplete hconn hC0 h0 p u b
      (b := 1) (by norm_num)
  have hmonoA :
      gronwallBound (Real.sqrt (P.metric.inner p a a))
          (max K 1) 0 t <= BA := by
    exact gronwallBound_mono (Real.sqrt_nonneg _) (by norm_num) hmaxK ht.2
  have hmonoB :
      gronwallBound (Real.sqrt (P.metric.inner p b b))
          (max K 1) 0 t <= BB := by
    exact gronwallBound_mono (Real.sqrt_nonneg _) (by norm_num) hmaxK ht.2
  have hf0 :
      f 0 t = intrinsicGeodesic (I := I) P.metric hEnorm p u t := by
    simp only [f, intrLaunch3, zero_smul, add_zero]
  have hLA : L A <= BA := by
    have hbound := (hpairA.1 t ht).trans hmonoA
    rw [show A = intrinsicJacobi (I := I) P.metric hEnorm p u a t from
      intrLaunchA_zero (I := I) P.metric hEnorm p u a b t]
    dsimp only [L]
    rw [hf0]
    simpa only [K] using hbound
  have hLKA : L KA <= BA := by
    have hbound := (hpairA.2 t ht).trans hmonoA
    rw [show KA =
        covDerivAlong (I := I) P.metric
          (intrinsicGeodesic (I := I) P.metric hEnorm p u)
          (intrinsicJacobi (I := I) P.metric hEnorm p u a) t from
      intrLaunchDA_zero (I := I) P.metric hEnorm p u a b t]
    dsimp only [L]
    rw [hf0]
    simpa only [K] using hbound
  have hLJ : L J <= BB := by
    have hbound := (hpairB.1 t ht).trans hmonoB
    rw [show J = intrinsicJacobi (I := I) P.metric hEnorm p u b t from
      intrLaunchJ_zero (I := I) P.metric hEnorm p u a b t]
    dsimp only [L]
    rw [hf0]
    simpa only [K] using hbound
  have hLDJ : L DJ <= BB := by
    have hbound := (hpairB.2 t ht).trans hmonoB
    rw [show DJ =
        covDerivAlong (I := I) P.metric
          (intrinsicGeodesic (I := I) P.metric hEnorm p u)
          (intrinsicJacobi (I := I) P.metric hEnorm p u b) t from
      intrLaunchDJ_zero (I := I) P.metric hEnorm p u a b t]
    dsimp only [L]
    rw [hf0]
    simpa only [K] using hbound
  have hspeedSq :
      P.metric.inner (f 0 t) T T = P.metric.inner p u u := by
    let u0 : TangentSpace I p :=
      show TangentSpace I p from u + (0 : Real) • a + (0 : Real) • b
    have hspeed := intrinsicGeodesic_speedSq_eq
      (I := I) P.metric hEnorm p u0 t
    calc
      P.metric.inner (f 0 t) T T =
          P.metric.inner p u0 u0 := by
        dsimp only [T, f, u0, Geometry.Riemannian.Variation.varSnd,
          intrLaunch3, curveVelocity]
        apply eq_of_heq
        exact heq_of_eq hspeed
      _ = P.metric.inner p u u := by simp [u0]
  have hLT : L T = U := by
    dsimp only [L, U]
    rw [hspeedSq]
  have hforce :
      L F <=
        C1 * L T * L A * L T * L J +
          C0 * L KA * L T * L J +
          2 * (C0 * L A * L T * L DJ) +
          C1 * L A * L J * L T * L T +
          C0 * L J * L KA * L T +
          C0 * L J * L T * L KA := by
    simpa only [f, V, F, L, A, T, J, KA, DJ] using
      intrJacForce_le (I := I) P hcomplete h0 h1 p u a b t
  exact jac_force_cap hC0 hC1 (Real.sqrt_nonneg _) hBA hBB
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hLA hLT.le hLJ hLKA hLDJ hforce

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrMix_pair_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    {C0 C1 : Real} (hC0 : 0 <= C0) (hC1 : 0 <= C1)
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (h1 : HasCurvDerivBound (I := I) P 1 C1)
    (p : P.M) (u a b : E) :
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
    let f : Real -> Real -> P.M := fun r s =>
      intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), s)
    let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
      intrLaunchJ (I := I) P.metric hEnorm p u a b (r, s)
    let W : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
      Geometry.Riemannian.Variation.covFst (I := I) P.metric f V r s
    let DW : ∀ s : Real, TangentSpace I (f 0 s) := fun s =>
      Geometry.Riemannian.Variation.covSnd (I := I) P.metric f W 0 s
    let U := Real.sqrt (P.metric.inner p u u)
    let K := C0 * U ^ 2
    let BA := gronwallBound (Real.sqrt (P.metric.inner p a a))
      (max K 1) 0 1
    let BB := gronwallBound (Real.sqrt (P.metric.inner p b b))
      (max K 1) 0 1
    let eps := (2 * C1 * U ^ 2 + 5 * C0 * U) * BA * BB
    (∀ t ∈ Icc (0 : Real) 1,
      Real.sqrt (P.metric.inner (f 0 t) (W 0 t) (W 0 t)) <=
        gronwallBound 0 (max K 1) eps t) ∧
    (∀ t ∈ Icc (0 : Real) 1,
      Real.sqrt (P.metric.inner (f 0 t) (DW t) (DW t)) <=
        gronwallBound 0 (max K 1) eps t) := by
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
  let f : Real -> Real -> P.M := fun r s =>
    intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), s)
  let V : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
    intrLaunchJ (I := I) P.metric hEnorm p u a b (r, s)
  let W : ∀ r s : Real, TangentSpace I (f r s) := fun r s =>
    Geometry.Riemannian.Variation.covFst (I := I) P.metric f V r s
  let DW : ∀ s : Real, TangentSpace I (f 0 s) := fun s =>
    Geometry.Riemannian.Variation.covSnd (I := I) P.metric f W 0 s
  let U := Real.sqrt (P.metric.inner p u u)
  let K := C0 * U ^ 2
  let BA := gronwallBound (Real.sqrt (P.metric.inner p a a))
    (max K 1) 0 1
  let BB := gronwallBound (Real.sqrt (P.metric.inner p b b))
    (max K 1) 0 1
  let eps := (2 * C1 * U ^ 2 + 5 * C0 * U) * BA * BB
  have hK : 0 <= K := mul_nonneg hC0 (sq_nonneg U)
  have hmaxK : 0 <= max K 1 := by
    exact le_trans (by norm_num) (le_max_right K 1)
  have hBA : 0 <= BA := by
    dsimp only [BA]
    rw [gronwallBound_ε0]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have hBB : 0 <= BB := by
    dsimp only [BB]
    rw [gronwallBound_ε0]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have heps : 0 <= eps := by
    dsimp only [eps]
    positivity
  have hODE : ∀ t ∈ Ico (0 : Real) 1,
      Real.sqrt
          (P.metric.inner (f 0 t)
            (Geometry.Riemannian.Variation.covSnd2
              (I := I) P.metric f W 0 t)
            (Geometry.Riemannian.Variation.covSnd2
              (I := I) P.metric f W 0 t)) <=
        K * Real.sqrt (P.metric.inner (f 0 t) (W 0 t) (W 0 t)) +
          eps := by
    intro t ht
    have htc : t ∈ Icc (0 : Real) 1 := ⟨ht.1, ht.2.le⟩
    let F := Geometry.Riemannian.Variation.jacVarForce
      (I := I) P.metric f V t
    let R := Geometry.Riemannian.Variation.jacCurv
      (I := I) P.metric f W 0 t
    let T := Geometry.Riemannian.Variation.varSnd (I := I) f 0 t
    let L : TangentSpace I (f 0 t) -> Real := fun z =>
      Real.sqrt (P.metric.inner (f 0 t) z z)
    have hforce : L F <= eps := by
      simpa only [f, V, F, L, U, K, BA, BB, eps] using
        intrMix_force_le (I := I) P hcomplete hconn hC0 hC1 h0 h1
          p u a b htc
    have hspeedSq :
        P.metric.inner (f 0 t) T T = P.metric.inner p u u := by
      let u0 : TangentSpace I p :=
        show TangentSpace I p from u + (0 : Real) • a + (0 : Real) • b
      have hspeed := intrinsicGeodesic_speedSq_eq
        (I := I) P.metric hEnorm p u0 t
      calc
        P.metric.inner (f 0 t) T T =
          P.metric.inner p u0 u0 := by
          dsimp only [T, f, u0, Geometry.Riemannian.Variation.varSnd,
            intrLaunch3, curveVelocity]
          apply eq_of_heq
          exact heq_of_eq hspeed
        _ = P.metric.inner p u u := by simp [u0]
    have hLT : L T = U := by
      dsimp only [L, U]
      rw [hspeedSq]
    have hRraw :=
      curvAlong_le (I := I) P h0
        (fun r : Real => f r t) (fun r : Real => W r t)
        (fun r : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r t)
        (fun r : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r t) 0
    have hR : L R <= K * L (W 0 t) := by
      have hmain :
          L R <= C0 * L (W 0 t) * L T * L T := by
        simpa only [L, R, T, Geometry.Riemannian.Variation.jacCurv,
          Geometry.Riemannian.Variation.curvAlong] using hRraw
      calc
        L R <= C0 * L (W 0 t) * L T * L T := hmain
        _ = K * L (W 0 t) := by
          rw [hLT]
          dsimp only [K]
          ring
    have hvar :=
      intrLaunch_var_eq (I := I) P.metric hEnorm p u a b t
    have hD2 :
        Geometry.Riemannian.Variation.covSnd2
            (I := I) P.metric f W 0 t = F - R := by
      exact eq_sub_of_add_eq (by
        simpa only [f, V, W, F, R] using hvar)
    change L
        (Geometry.Riemannian.Variation.covSnd2
          (I := I) P.metric f W 0 t) <=
      K * L (W 0 t) + eps
    rw [hD2, sub_eq_add_neg]
    calc
      L (F + -R) <= L F + L (-R) := by
        exact Geometry.Riemannian.sqrt_inner_add_le
          (I := I) P.metric (f 0 t) F (-R)
      _ = L F + L R := by
        congr 1
        simpa only [L, neg_one_smul, abs_neg, abs_one, one_mul] using
          (Geometry.Riemannian.sqrt_inner_smul
            (I := I) P.metric (f 0 t) (-1 : Real) R)
      _ <= eps + K * L (W 0 t) := add_le_add hforce hR
      _ = K * L (W 0 t) + eps := add_comm _ _
  have hWjoint :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f q.1 q.2) (W q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f, V, W] using
      intrLaunchMix_smooth (I := I) P.metric hEnorm p u a b
  have hDWjoint :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f q.1 q.2)
            (Geometry.Riemannian.Variation.covSnd
              (I := I) P.metric f W q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f, V, W] using
      intrMixDeriv_smooth (I := I) P.metric hEnorm p u a b
  let Q := (modelWithCornersSelf Real Real).prod
    (modelWithCornersSelf Real Real)
  have hzero :
      ContMDiff (modelWithCornersSelf Real Real) Q ∞
        (fun t : Real => ((0 : Real), t)) :=
    contMDiff_const.prodMk contMDiff_id
  have hWslice :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun t : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f 0 t) (W 0 t) : TangentBundle I P.M)) := by
    exact hWjoint.comp hzero
  have hDWslice :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun t : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f 0 t) (DW t) : TangentBundle I P.M)) := by
    dsimp only [DW]
    exact hDWjoint.comp hzero
  have hWzero : W 0 0 = 0 := by
    dsimp only [W, f, V, Geometry.Riemannian.Variation.covFst]
    have hfield :
        (fun r : Real => intrLaunchJ (I := I) P.metric hEnorm p u a b (r, 0)) =
          fun r : Real => mfderiv 𝓘(Real, Real) I
            (fun s : Real => intrLaunch3
              (I := I) P.metric hEnorm p u a b ((r, s), 0)) 0 (1 : Real) := by
      funext r
      exact intrLaunchJ_eq (I := I) P.metric hEnorm p u a b (r, 0)
    rw [hfield]
    exact intrLaunch_mix_zero (I := I) P.metric hEnorm p u a b
  have hDWzero : DW 0 = 0 := by
    simpa only [DW, W, f, V] using
      intrLaunch_dmix0 (I := I) P.metric hEnorm p u a b
  let u0 : TangentSpace I p :=
    show TangentSpace I p from u + (0 : Real) • a + (0 : Real) • b
  have hW0 :
      Real.sqrt
          (P.metric.inner
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
            (W 0 0) (W 0 0)) <= 0 := by
    rw [hWzero]
    have hz : P.metric.inner
        (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
        (0 : TangentSpace I
          (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)) 0 = 0 := by
      rw [map_zero]
    calc
      Real.sqrt (P.metric.inner
          (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
          (0 : TangentSpace I
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)) 0) =
          Real.sqrt 0 := congrArg Real.sqrt hz
      _ <= 0 := by rw [Real.sqrt_zero]
  have hDW0 :
      Real.sqrt
          (P.metric.inner
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
            (DW 0) (DW 0)) <= 0 := by
    rw [hDWzero]
    have hz : P.metric.inner
        (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
        (0 : TangentSpace I
          (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)) 0 = 0 := by
      rw [map_zero]
    calc
      Real.sqrt (P.metric.inner
          (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)
          (0 : TangentSpace I
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0)) 0) =
          Real.sqrt 0 := congrArg Real.sqrt hz
      _ <= 0 := by rw [Real.sqrt_zero]
  have hf0 : f 0 = intrinsicGeodesic (I := I) P.metric hEnorm p u0 := by
    funext v
    simp only [f, u0, intrLaunch3]
  have hbounds :=
    Geometry.Riemannian.VolumeComparison.intrForce_pair
      (I := I) P.metric hEnorm p u0 (fun t => W 0 t)
      hK heps (by norm_num : (0 : Real) < 1)
      (by simpa only [u0, f, intrLaunch3] using hWslice)
      (by simpa only [u0, f, DW, W, intrLaunch3,
        Geometry.Riemannian.Variation.covSnd] using hDWslice)
      (by
        have h := hODE
        simp only [Geometry.Riemannian.Variation.covSnd,
          Geometry.Riemannian.Variation.covSnd2] at h ⊢
        rw [hf0] at h
        exact h)
      hW0 hDW0
  change
    (∀ t ∈ Icc (0 : Real) 1,
      Real.sqrt
          (P.metric.inner
            (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
            (W 0 t) (W 0 t)) <=
        gronwallBound 0 (max K 1) eps t) ∧
      ∀ t ∈ Icc (0 : Real) 1,
        Real.sqrt
            (P.metric.inner
              (intrinsicGeodesic (I := I) P.metric hEnorm p u0 t)
              (covDerivAlong (I := I) P.metric
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0)
                (fun s => W 0 s) t)
              (covDerivAlong (I := I) P.metric
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0)
                (fun s => W 0 s) t)) <=
          gronwallBound 0 (max K 1) eps t
  exact hbounds

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompleteSpace E] in
theorem intrJet_pair_of
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    {C0 U eps delta : Real} (hC0 : 0 <= C0)
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (p : P.M) (u a b : E) (n : Nat) (r : Real) :
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
      intrLaunch3 (I := I) P.metric hEnorm p u a b ((s, 0), t)
    let W : forall s t : Real, TangentSpace I (f s t) := fun s t =>
      intrLaunchJet (I := I) P.metric hEnorm p u a b n (s, t)
    let DW : forall t : Real, TangentSpace I (f r t) := fun t =>
      Geometry.Riemannian.Variation.covSnd (I := I) P.metric f W r t
    0 <= U ->
    Real.sqrt
        (P.metric.inner p (u + r • a) (u + r • a)) <= U ->
    0 <= eps ->
    (forall t, t ∈ Ico (0 : Real) 1 ->
      Real.sqrt
          (P.metric.inner (f r t)
            (intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t))
            (intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t))) <=
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
    intrLaunch3 (I := I) P.metric hEnorm p u a b ((s, 0), t)
  let W : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    intrLaunchJet (I := I) P.metric hEnorm p u a b n (s, t)
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
      intrLaunchJet_smooth (I := I) P.metric hEnorm p u a b n
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
    let R := Geometry.Riemannian.Variation.jacCurv
      (I := I) P.metric f W r t
    let L : TangentSpace I (f r t) -> Real := fun z =>
      Real.sqrt (P.metric.inner (f r t) z z)
    have hspeedSq :
        P.metric.inner (f r t) T T = P.metric.inner p u0 u0 := by
      have hspeedEq :=
        intrinsicGeodesic_speedSq_eq
          (I := I) P.metric hEnorm p u0 t
      dsimp only [T, f, u0, intrLaunch3,
        Geometry.Riemannian.Variation.varSnd, curveVelocity]
      apply eq_of_heq
      exact heq_of_eq hspeedEq
    have hLT : L T <= U := by
      dsimp only [L]
      rw [hspeedSq]
      simpa only [u0, zero_smul, add_zero] using hspeed
    have hRraw :=
      curvAlong_le (I := I) P h0
        (fun v : Real => f r v) (fun v : Real => W r v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.varSnd (I := I) f r v) t
    have hR : L R <= K * L (W r t) := by
      have hmain :
          L R <= C0 * L (W r t) * L T * L T := by
        simpa only [L, R, T,
          Geometry.Riemannian.Variation.jacCurv,
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
          intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t) := by
      rfl
    have hD2 :
        Geometry.Riemannian.Variation.covSnd2
            (I := I) P.metric f W r t =
          intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t) - R :=
      eq_sub_of_add_eq hresEq
    change L
        (Geometry.Riemannian.Variation.covSnd2
          (I := I) P.metric f W r t) <=
      K * L (W r t) + eps
    rw [hD2, sub_eq_add_neg]
    calc
      L
          (intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t) +
            -R) <=
          L (intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t)) +
            L (-R) := by
        exact Geometry.Riemannian.sqrt_inner_add_le
          (I := I) P.metric (f r t)
          (intrJetResidual (I := I) P.metric hEnorm p u a b n (r, t)) (-R)
      _ = L (intrJetResidual
            (I := I) P.metric hEnorm p u a b n (r, t)) + L R := by
        congr 1
        simpa only [L, neg_one_smul, abs_neg, abs_one, one_mul] using
          (Geometry.Riemannian.sqrt_inner_smul
            (I := I) P.metric (f r t) (-1 : Real) R)
      _ <= eps + K * L (W r t) := add_le_add (hres t ht) hR
      _ = K * L (W r t) + eps := add_comm _ _
  have hfr : f r = intrinsicGeodesic (I := I) P.metric hEnorm p u0 := by
    funext v
    simp only [f, u0, intrLaunch3]
  rw [hfr] at hW0
  dsimp only [DW, Geometry.Riemannian.Variation.covSnd] at hDW0
  rw [hfr] at hDW0
  have hbounds :=
    Geometry.Riemannian.VolumeComparison.intrForce_pair
      (I := I) P.metric hEnorm p u0 (fun t => W r t)
      hK heps (by norm_num : (0 : Real) < 1)
      (by simpa only [u0, f, intrLaunch3] using hWslice)
      (by simpa only [u0, f, DW, W, intrLaunch3,
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrJet_upto_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hconn : letI : TopologicalSpace P.M := P.topology; ConnectedSpace P.M)
    (hP : BoundedGeometry (I := I) P)
    (p : P.M) (u : E) {R U D : Real} (hD : 0 <= D) :
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
    let leafNorm : E -> E -> IntrJetAtom -> Real -> Real -> Real :=
      fun a b atom r t =>
        Real.sqrt
          (P.metric.inner
            (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t))
            (atom.eval (I := I) P.metric hEnorm p u a b (r, t)))
    Real.sqrt (P.metric.inner p u u) + R * D <= U ->
    forall n (a b : E),
      Real.sqrt (P.metric.inner p a a) <= D ->
      Real.sqrt (P.metric.inner p b b) <= D ->
      forall r, |r| <= R ->
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bJet k) r t <= jetCap hP.C U D n) ∧
        (forall k, k <= n ->
          forall t, t ∈ Icc (0 : Real) 1 ->
            leafNorm a b (.bTime k) r t <= jetCap hP.C U D n) := by
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
        launch_speed_le (I := I) P p u a ha hr hD hu
      have hpair :=
        intrJet_pair_of (I := I) P hcomplete hconn
          (C0 := hP.C 0) (U := U) (eps := 0) (delta := D)
          (hP.nonneg 0) (hP.bound 0) p u a b 0 r
          hU hspeed (by norm_num)
          (by
            intro t ht
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrJetResidual
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <= 0
            rw [intrJetResidual_zero (I := I) P.metric hEnorm p u a b r t]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrJetAtom.bJet_time0]
            simpa only [map_zero, Real.sqrt_zero] using hD)
          (by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= D
            rw [IntrJetAtom.bTime_zero]
            let u0 : TangentSpace I p :=
              show TangentSpace I p from u + r • a + (0 : Real) • b
            change Real.sqrt
              (P.metric.inner
                (intrinsicGeodesic (I := I) P.metric hEnorm p u0 0) b b) <= D
            rw [intrinsicGeodesic_zero
              (I := I) P.metric hEnorm p u0]
            exact hb)
      have hrate : 0 <= jetRate hP.C U := (jetRate_pos hP.C U).le
      constructor
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bJet 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jetRate hP.C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))
                (intrLaunchJet
                  (I := I) P.metric hEnorm p u a b 0 (r, t))) <=
                gronwallBound D (jetRate hP.C U) 0 t
            simpa only [jetRate] using hpair.1 t ht
          _ <= gronwallBound D (jetRate hP.C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jetCap hP.C U D 0 := rfl
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bTime 0).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound D (jetRate hP.C U) 0 t := by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrLaunchJet
                    (I := I) P.metric hEnorm p u a b 0 (s, t)) r t)) <=
                gronwallBound D (jetRate hP.C U) 0 t
            simpa only [jetRate] using hpair.2 t ht
          _ <= gronwallBound D (jetRate hP.C U) 0 1 :=
            gronwallBound_mono hD (by norm_num) hrate ht.2
          _ = jetCap hP.C U D 0 := rfl
  | succ n ih =>
      intro a b ha hb r hr
      have hU : 0 <= U := by
        have hR : 0 <= R := (abs_nonneg r).trans hr
        exact
          (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg hR hD)).trans hu
      have hspeed :
          Real.sqrt
              (P.metric.inner p (u + r • a) (u + r • a)) <= U :=
        launch_speed_le (I := I) P p u a ha hr hD hu
      have hprev := ih a b ha hb r hr
      have hself := ih a a ha ha r hr
      have hcap : 0 <= jetCap hP.C U D n :=
        jetCap_nonneg hP.C hD n
      have heps : 0 <= jetEps hP.C U (jetCap hP.C U D n) n :=
        jetEps_nonneg hP.C hP.nonneg hU hcap n
      have hres : forall t, t ∈ Ico (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrJetResidual
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
            jetEps hP.C U (jetCap hP.C U D n) n := by
        intro t ht
        rw [show intrJetResidual
              (I := I) P.metric hEnorm p u a b (n + 1) (r, t) =
            (intrResidualTerm (n + 1)).eval
              (I := I) P.metric hEnorm p u a b (r, t) by
          exact congrFun
            (congrFun
              (intrResidualTerm_eval
                (I := I) P.metric hEnorm p u a b (n + 1)) r) t]
        apply CurvJetTerm.eval_le_at
          (I := I) P.metric hEnorm p u a b hP.C hP.nonneg
          (jetLeafCap U (jetCap hP.C U D n))
          (fun atom => atom.AtMost n)
          (fun k x v =>
            HasCurvDerivBound.curvOpN_le
              (I := I) P (hP.bound k) x v)
          (r, t)
        · intro atom hatom
          have hbaseSelf :
              intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t) =
                intrLaunch3 (I := I) P.metric hEnorm p u a a ((r, 0), t) := by
            simp only [intrLaunch3, zero_smul, add_zero]
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
                    (intrLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))) <= U
              rw [show P.metric.inner
                    (intrLaunch3
                      (I := I) P.metric hEnorm p u a b ((r, 0), t))
                    ((IntrJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t))
                    ((IntrJetAtom.pathT).eval
                      (I := I) P.metric hEnorm p u a b (r, t)) =
                  P.metric.inner p (u + r • a) (u + r • a) by
                simp only [IntrJetAtom.eval, intrLaunch3, varSnd]
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
              rw [IntrJetAtom.pathDt_zero]
              simpa only [jetLeafCap, map_zero, Real.sqrt_zero] using
                (le_refl (0 : Real))
          | aJet k =>
              rw [IntrJetAtom.aJet_eq_self]
              rw [hbaseSelf]
              simpa only [jetLeafCap] using hself.1 k hatom t ⟨ht.1, ht.2.le⟩
          | aTime k =>
              rw [IntrJetAtom.aTime_eq_self]
              rw [hbaseSelf]
              simpa only [jetLeafCap] using hself.2 k hatom t ⟨ht.1, ht.2.le⟩
          | bJet k =>
              simpa only [jetLeafCap] using hprev.1 k hatom t ⟨ht.1, ht.2.le⟩
          | bTime k =>
              simpa only [jetLeafCap] using hprev.2 k hatom t ⟨ht.1, ht.2.le⟩
        · exact intrResidual_atoms n
      have hpair :=
        intrJet_pair_of (I := I) P hcomplete hconn
          (C0 := hP.C 0) (U := U)
          (eps := jetEps hP.C U (jetCap hP.C U D n) n) (delta := 0)
          (hP.nonneg 0) (hP.bound 0) p u a b (n + 1) r
          hU hspeed heps hres
          (by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrJetAtom.bJet_time0]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
          (by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), 0))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, 0))) <= 0
            rw [IntrJetAtom.bTime_succ_time0]
            simpa only [map_zero, Real.sqrt_zero] using
              (le_refl (0 : Real)))
      have hrate : 0 <= jetRate hP.C U := (jetRate_pos hP.C U).le
      have hnewPos : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jetCap hP.C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bJet (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jetRate hP.C U)
                (jetEps hP.C U (jetCap hP.C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (intrLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))
                (intrLaunchJet
                  (I := I) P.metric hEnorm p u a b (n + 1) (r, t))) <=
                gronwallBound 0 (jetRate hP.C U)
                  (jetEps hP.C U (jetCap hP.C U D n) n) t
            simpa only [jetRate] using hpair.1 t ht
          _ <= gronwallBound 0 (jetRate hP.C U)
              (jetEps hP.C U (jetCap hP.C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jetCap hP.C U D (n + 1) :=
            jetCap_step_le hP.C U D n
      have hnewTime : forall t, t ∈ Icc (0 : Real) 1 ->
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
            jetCap hP.C U D (n + 1) := by
        intro t ht
        calc
          Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))
                ((IntrJetAtom.bTime (n + 1)).eval
                  (I := I) P.metric hEnorm p u a b (r, t))) <=
              gronwallBound 0 (jetRate hP.C U)
                (jetEps hP.C U (jetCap hP.C U D n) n) t := by
            change Real.sqrt
              (P.metric.inner
                (intrLaunch3 (I := I) P.metric hEnorm p u a b ((r, 0), t))
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)
                (Geometry.Riemannian.Variation.covSnd
                  (I := I) P.metric
                  (fun s t => intrLaunch3
                    (I := I) P.metric hEnorm p u a b ((s, 0), t))
                  (fun s t => intrLaunchJet
                    (I := I) P.metric hEnorm p u a b (n + 1) (s, t)) r t)) <=
                gronwallBound 0 (jetRate hP.C U)
                  (jetEps hP.C U (jetCap hP.C U D n) n) t
            simpa only [jetRate] using hpair.2 t ht
          _ <= gronwallBound 0 (jetRate hP.C U)
              (jetEps hP.C U (jetCap hP.C U D n) n) 1 :=
            gronwallBound_mono (by norm_num) heps hrate ht.2
          _ <= jetCap hP.C U D (n + 1) :=
            jetCap_step_le hP.C U D n
      constructor
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.1 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jetCap_le_succ hP.C U D n)
        · exact hnewPos t ht
      · intro k hk t ht
        rcases Nat.lt_or_eq_of_le hk with hklt | rfl
        · exact (hprev.2 k (Nat.lt_succ_iff.mp hklt) t ht).trans
            (jetCap_le_succ hP.C U D n)
        · exact hnewTime t ht

end HCGCompactness
end DifferentialGeometry

end
