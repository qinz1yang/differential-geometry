import DifferentialGeometry.Geometry.Comparison.Variation.CurvatureDerivativeAlong

import DifferentialGeometry.Geometry.Exponential.IntrinsicJacobiJets
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.BoundedGeometry
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric
import DifferentialGeometry.Geometry.Metric.InnerExpansion

set_option autoImplicit false

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem curvAlong_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 0 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (γ : Real -> P.M)
      (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real),
      let R :=
        Geometry.Riemannian.Variation.curvAlong (I := I)
          P.metric γ X Y Z t
      Real.sqrt (P.metric.inner (γ t) R R) <=
        C * Real.sqrt (P.metric.inner (γ t) (X t) (X t)) *
          Real.sqrt (P.metric.inner (γ t) (Y t) (Y t)) *
          Real.sqrt (P.metric.inner (γ t) (Z t) (Z t)) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  intro γ X Y Z t
  simpa only [Geometry.Riemannian.Variation.curvAlong] using
    (HasCurvDerivBound.riemannOp_le (I := I) P hP
      (γ t) (X t) (Y t) (Z t))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem curvDerivAlong_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C : Real} (hP : HasCurvDerivBound (I := I) P 1 C) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (γ : Real -> P.M)
      (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real),
      ContMDiff 𝓘(Real, Real) I ∞ γ ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (γ s) (X s) : TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (γ s) (Y s) : TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (γ s) (Z s) : TangentBundle I P.M)) ->
      let R :=
        Geometry.Riemannian.Variation.curvDerivAlong (I := I)
          P.metric γ X Y Z t
      let D :=
        (mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] TangentSpace I (γ t))
          (1 : Real)
      Real.sqrt (P.metric.inner (γ t) R R) <=
        C * Real.sqrt (P.metric.inner (γ t) D D) *
          Real.sqrt (P.metric.inner (γ t) (X t) (X t)) *
          Real.sqrt (P.metric.inner (γ t) (Y t) (Y t)) *
          Real.sqrt (P.metric.inner (γ t) (Z t) (Z t)) := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  intro γ X Y Z t hγ hX hY hZ
  rw [Geometry.Riemannian.Variation.curvDeriv_eq_nabla
    (I := I) P.metric γ X Y Z t hγ hX hY hZ]
  exact HasCurvDerivBound.nablaRiemannOp_le (I := I) P hP
    (γ t)
    ((mfderiv 𝓘(Real, Real) I γ t :
      Real →L[Real] TangentSpace I (γ t)) (1 : Real))
    (X t) (Y t) (Z t)

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem sqrt_six_add_le
    {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (a b c d e f : TangentSpace I x) :
    Real.sqrt (g.inner x (a + b + c + d + e + f)
      (a + b + c + d + e + f)) <=
      Real.sqrt (g.inner x a a) +
        Real.sqrt (g.inner x b b) +
        Real.sqrt (g.inner x c c) +
        Real.sqrt (g.inner x d d) +
        Real.sqrt (g.inner x e e) +
        Real.sqrt (g.inner x f f) := by
  have hab := Geometry.Riemannian.sqrt_inner_add_le (I := I) g x a b
  have habc :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) g x (a + b) c
  have habcd :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) g x (a + b + c) d
  have habcde :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) g x (a + b + c + d) e
  have habcdef :=
    Geometry.Riemannian.sqrt_inner_add_le (I := I) g x
      (a + b + c + d + e) f
  linarith

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] in
theorem jacVarForce_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    {C0 C1 : Real}
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (h1 : HasCurvDerivBound (I := I) P 1 C1) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    ∀ (f : Real -> Real -> P.M)
      (V : ∀ s t : Real, TangentSpace I (f s t)) (t : Real),
      ContMDiff 𝓘(Real, Real) I ∞ (fun v : Real => f 0 v) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f 0 v) (Geometry.Riemannian.Variation.varFst (I := I) f 0 v) :
              TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f 0 v) (Geometry.Riemannian.Variation.varSnd (I := I) f 0 v) :
              TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f 0 v) (V 0 v) : TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I ∞ (fun s : Real => f s t) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f s t) (V s t) : TangentBundle I P.M)) ->
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M -> Type _))
            (f s t) (Geometry.Riemannian.Variation.varSnd (I := I) f s t) :
              TangentBundle I P.M)) ->
      let A := Geometry.Riemannian.Variation.varFst (I := I) f 0 t
      let T := Geometry.Riemannian.Variation.varSnd (I := I) f 0 t
      let J := V 0 t
      let K :=
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
          (fun s v => Geometry.Riemannian.Variation.varFst (I := I) f s v)
          0 t
      let DJ :=
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V 0 t
      let F :=
        Geometry.Riemannian.Variation.jacVarForce (I := I) P.metric f V t
      let L : TangentSpace I (f 0 t) -> Real :=
        fun z => Real.sqrt (P.metric.inner (f 0 t) z z)
      L F <=
        C1 * L T * L A * L T * L J +
          C0 * L K * L T * L J +
          2 * (C0 * L A * L T * L DJ) +
          C1 * L A * L J * L T * L T +
          C0 * L J * L K * L T +
          C0 * L J * L T * L K := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  intro f V t hγt hAt hTt hJt hγs hJs hTs
  let A := Geometry.Riemannian.Variation.varFst (I := I) f 0 t
  let T := Geometry.Riemannian.Variation.varSnd (I := I) f 0 t
  let J := V 0 t
  let K :=
    Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
      (fun s v => Geometry.Riemannian.Variation.varFst (I := I) f s v) 0 t
  let DJ :=
    Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V 0 t
  let L : TangentSpace I (f 0 t) -> Real :=
    fun z => Real.sqrt (P.metric.inner (f 0 t) z z)
  let F1 :=
    Geometry.Riemannian.Variation.curvDerivAlong (I := I) P.metric
      (fun v : Real => f 0 v)
      (fun v : Real => Geometry.Riemannian.Variation.varFst (I := I) f 0 v)
      (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
      (fun v : Real => V 0 v) t
  let F2 :=
    Geometry.Riemannian.Variation.curvAlong (I := I) P.metric
      (fun v : Real => f 0 v)
      (fun v : Real =>
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
          (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
          0 v)
      (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
      (fun v : Real => V 0 v) t
  let F3 :=
    Geometry.Riemannian.Variation.varCurv (I := I) P.metric f
      (fun s v =>
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V s v)
      0 t
  let F4 :=
    Geometry.Riemannian.Variation.curvDerivAlong (I := I) P.metric
      (fun s : Real => f s t) (fun s : Real => V s t)
      (fun s : Real => Geometry.Riemannian.Variation.varSnd (I := I) f s t)
      (fun s : Real => Geometry.Riemannian.Variation.varSnd (I := I) f s t)
      0
  let F5 :=
    Geometry.Riemannian.Variation.curvAlong (I := I) P.metric
      (fun v : Real => f 0 v) (fun v : Real => V 0 v)
      (fun v : Real =>
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
          (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
          0 v)
      (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v) t
  let F6 :=
    Geometry.Riemannian.Variation.curvAlong (I := I) P.metric
      (fun v : Real => f 0 v) (fun v : Real => V 0 v)
      (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
      (fun v : Real =>
        Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
          (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
          0 v) t
  have hF1 : L F1 <= C1 * L T * L A * L T * L J := by
    simpa only [F1, L, T, A, J,
      Geometry.Riemannian.Variation.varSnd] using
      (curvDerivAlong_le (I := I) P h1
        (fun v : Real => f 0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varFst (I := I) f 0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
        (fun v : Real => V 0 v) t hγt hAt hTt hJt)
  have hF2 : L F2 <= C0 * L K * L T * L J := by
    simpa only [F2, L, K, T, J] using
      (curvAlong_le (I := I) P h0 (fun v : Real => f 0 v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
            (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
            0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
        (fun v : Real => V 0 v) t)
  have hF3 : L F3 <= C0 * L A * L T * L DJ := by
    simpa only [F3, L, A, T, DJ,
      Geometry.Riemannian.Variation.varCurv] using
      (curvAlong_le (I := I) P h0 (fun v : Real => f 0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varFst (I := I) f 0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V 0 v) t)
  have hF4 : L F4 <= C1 * L A * L J * L T * L T := by
    simpa only [F4, L, A, J, T,
      Geometry.Riemannian.Variation.varFst] using
      (curvDerivAlong_le (I := I) P h1
        (fun s : Real => f s t) (fun s : Real => V s t)
        (fun s : Real => Geometry.Riemannian.Variation.varSnd (I := I) f s t)
        (fun s : Real => Geometry.Riemannian.Variation.varSnd (I := I) f s t)
        0 hγs hJs hTs hTs)
  have hF5 : L F5 <= C0 * L J * L K * L T := by
    simpa only [F5, L, J, K, T] using
      (curvAlong_le (I := I) P h0 (fun v : Real => f 0 v)
        (fun v : Real => V 0 v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
            (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
            0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
        t)
  have hF6 : L F6 <= C0 * L J * L T * L K := by
    simpa only [F6, L, J, T, K] using
      (curvAlong_le (I := I) P h0 (fun v : Real => f 0 v)
        (fun v : Real => V 0 v)
        (fun v : Real => Geometry.Riemannian.Variation.varSnd (I := I) f 0 v)
        (fun v : Real =>
          Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
            (fun s w => Geometry.Riemannian.Variation.varFst (I := I) f s w)
            0 v) t)
  have hF3two : L ((2 : Real) • F3) <=
      2 * (C0 * L A * L T * L DJ) := by
    rw [show L ((2 : Real) • F3) = 2 * L F3 from by
      simpa only [L, abs_of_nonneg (by norm_num : (0 : Real) <= 2)] using
        (Geometry.Riemannian.sqrt_inner_smul
          (I := I) P.metric (f 0 t) (2 : Real) F3)]
    exact mul_le_mul_of_nonneg_left hF3 (by norm_num)
  have hsum :
      L (F1 + F2 + (2 : Real) • F3 + F4 + F5 + F6) <=
        L F1 + L F2 + L ((2 : Real) • F3) + L F4 + L F5 + L F6 := by
    exact sqrt_six_add_le (I := I) P.metric (f 0 t)
      F1 F2 ((2 : Real) • F3) F4 F5 F6
  have hneg :
      L (-(F1 + F2 + (2 : Real) • F3 + F4 + F5 + F6)) =
        L (F1 + F2 + (2 : Real) • F3 + F4 + F5 + F6) := by
    simpa only [L, neg_one_smul, abs_neg, abs_one, one_mul] using
      (Geometry.Riemannian.sqrt_inner_smul (I := I) P.metric (f 0 t)
        (-1 : Real) (F1 + F2 + (2 : Real) • F3 + F4 + F5 + F6))
  change
    L (Geometry.Riemannian.Variation.jacVarForce
      (I := I) P.metric f V t) <=
      C1 * L T * L A * L T * L J +
        C0 * L K * L T * L J +
        2 * (C0 * L A * L T * L DJ) +
        C1 * L A * L J * L T * L T +
        C0 * L J * L K * L T +
        C0 * L J * L T * L K
  rw [show Geometry.Riemannian.Variation.jacVarForce
      (I := I) P.metric f V t =
        -(F1 + F2 + (2 : Real) • F3 + F4 + F5 + F6) from rfl,
    hneg]
  linarith

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem intrJacForce_le
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    {C0 C1 : Real}
    (h0 : HasCurvDerivBound (I := I) P 0 C0)
    (h1 : HasCurvDerivBound (I := I) P 1 C1)
    (p : P.M) (u a b : E) (t : Real) :
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
    let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v)
    let f : Real → Real → P.M := fun s v =>
      Geometry.Riemannian.Exponential.intrLaunch3
        (I := I) P.metric hEnorm p u a b ((s, 0), v)
    let V : ∀ s v : Real, TangentSpace I (f s v) := fun s v =>
      Geometry.Riemannian.Exponential.intrLaunchJ
        (I := I) P.metric hEnorm p u a b (s, v)
    let A := Geometry.Riemannian.Variation.varFst (I := I) f 0 t
    let T := Geometry.Riemannian.Variation.varSnd (I := I) f 0 t
    let J := V 0 t
    let K :=
      Geometry.Riemannian.Variation.covSnd (I := I) P.metric f
        (fun s v => Geometry.Riemannian.Variation.varFst (I := I) f s v)
        0 t
    let DJ :=
      Geometry.Riemannian.Variation.covSnd (I := I) P.metric f V 0 t
    let F :=
      Geometry.Riemannian.Variation.jacVarForce (I := I) P.metric f V t
    let L : TangentSpace I (f 0 t) → Real :=
      fun z => Real.sqrt (P.metric.inner (f 0 t) z z)
    L F <=
      C1 * L T * L A * L T * L J +
        C0 * L K * L T * L J +
        2 * (C0 * L A * L T * L DJ) +
        C1 * L A * L J * L T * L T +
        C0 * L J * L K * L T +
        C0 * L J * L T * L K := by
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
  let hEnorm : ∀ (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) P.metric x v)
  let f : Real → Real → P.M := fun s v =>
    Geometry.Riemannian.Exponential.intrLaunch3
      (I := I) P.metric hEnorm p u a b ((s, 0), v)
  let V : ∀ s v : Real, TangentSpace I (f s v) := fun s v =>
    Geometry.Riemannian.Exponential.intrLaunchJ
      (I := I) P.metric hEnorm p u a b (s, v)
  let Q := (modelWithCornersSelf Real Real).prod
    (modelWithCornersSelf Real Real)
  have hf :
      ContMDiff Q I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff Q
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact
      (Geometry.Riemannian.Exponential.intrLaunch3_smooth
        (I := I) P.metric hEnorm p u a b).comp hincl
  have hV :
      ContMDiff Q I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f q.1 q.2) (V q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f, V] using
      Geometry.Riemannian.Exponential.intrLaunchJ_smooth
        (I := I) P.metric hEnorm p u a b
  have hA :
      ContMDiff Q I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f q.1 q.2)
            (Geometry.Riemannian.Variation.varFst
              (I := I) f q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f,
      Geometry.Riemannian.Exponential.intrLaunchA_eq] using
      (Geometry.Riemannian.Exponential.intrLaunchDir_smooth
        (I := I) P.metric hEnorm p u a b ((1, 0), 0))
  have hT :
      ContMDiff Q I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f q.1 q.2)
            (Geometry.Riemannian.Variation.varSnd
              (I := I) f q.1 q.2) : TangentBundle I P.M)) := by
    simpa only [f,
      Geometry.Riemannian.Exponential.intrLaunchT_eq] using
      (Geometry.Riemannian.Exponential.intrLaunchDir_smooth
        (I := I) P.metric hEnorm p u a b ((0, 0), 1))
  have hzero :
      ContMDiff (modelWithCornersSelf Real Real) Q ∞
        (fun v : Real => ((0 : Real), v)) :=
    contMDiff_const.prodMk contMDiff_id
  have ht :
      ContMDiff (modelWithCornersSelf Real Real) Q ∞
        (fun s : Real => (s, t)) :=
    contMDiff_id.prodMk contMDiff_const
  have hγt :
      ContMDiff (modelWithCornersSelf Real Real) I ∞
        (fun v : Real => f 0 v) :=
    hf.comp hzero
  have hAt :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f 0 v)
            (Geometry.Riemannian.Variation.varFst
              (I := I) f 0 v) : TangentBundle I P.M)) :=
    hA.comp hzero
  have hTt :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f 0 v)
            (Geometry.Riemannian.Variation.varSnd
              (I := I) f 0 v) : TangentBundle I P.M)) :=
    hT.comp hzero
  have hJt :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun v : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f 0 v) (V 0 v) : TangentBundle I P.M)) :=
    hV.comp hzero
  have hγs :
      ContMDiff (modelWithCornersSelf Real Real) I ∞
        (fun s : Real => f s t) :=
    hf.comp ht
  have hJs :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f s t) (V s t) : TangentBundle I P.M)) :=
    hV.comp ht
  have hTs :
      ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : P.M → Type _))
            (f s t)
            (Geometry.Riemannian.Variation.varSnd
              (I := I) f s t) : TangentBundle I P.M)) :=
    hT.comp ht
  exact jacVarForce_le (I := I) P h0 h1 f V t
    hγt hAt hTt hJt hγs hJs hTs

end HCGCompactness
end DifferentialGeometry

end
