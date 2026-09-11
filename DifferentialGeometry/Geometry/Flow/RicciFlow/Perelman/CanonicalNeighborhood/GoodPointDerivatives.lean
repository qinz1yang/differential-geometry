import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.LaplacianInputRegularWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.IntervalTransport
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Pointwise
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]



section WitnessData

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {x : M}
variable {t eps kappa : ℝ}


def witnessGhat (W : KappaModelWitness.{u, uE, uH} (I := I) eps kappa S x t) :
    ℝ → SmoothRiemannianMetric I M :=
  rescaledMetric (I := I) S t (S.scalar t x) W.scalar_pos

def witnessModelBall (W : KappaModelWitness.{u, uE, uH} (I := I) eps kappa S x t) :
    Set W.model.M :=
  letI : TopologicalSpace W.model.M := W.model.topology
  letI : ChartedSpace H W.model.M := W.model.charted
  letI : IsManifold I ∞ W.model.M := W.model.smooth
  letI : IsManifold I 1 W.model.M :=
    IsManifold.of_le (I := I) (M := W.model.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) W.model.M := by
    change IsManifold I ∞ W.model.M
    infer_instance
  letI : SigmaCompactSpace W.model.M := W.model.sigmaCompact
  letI : T2Space W.model.M := W.model.t2
  riemannianClosedBallOf (I := I) (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps)


def witnessImage (W : KappaModelWitness.{u, uE, uH} (I := I) eps kappa S x t) : Set M :=
  letI : TopologicalSpace W.model.M := W.model.topology
  letI : ChartedSpace H W.model.M := W.model.charted
  (W.embedding : W.model.M → M) '' witnessModelBall (I := I) W

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem scalar_pos_of_isGoodPoint
    (hgood : IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t) : 0 < S.scalar t x :=
  hgood.elim fun W => W.scalar_pos

end WitnessData



section Interfaces

def ModelCurvatureBoundNearBase (I : ModelWithCorners ℝ E H) (kappa : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧
    ∀ L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
      IsAncientKappaSolution (I := I) kappa L →
        PointedFlowScalarAtBase (I := I) L 1 →
        ∀ s ∈ Set.Icc (-(4 : ℝ)) 0,
          ∀ y : L.M,
            (letI : TopologicalSpace L.M := L.topology
             letI : ChartedSpace H L.M := L.charted
             letI : IsManifold I ∞ L.M := L.smooth
             letI : IsManifold I 1 L.M :=
               IsManifold.of_le (I := I) (M := L.M) (n := (∞ : WithTop ℕ∞))
                 (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
             letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
               change IsManifold I ∞ L.M
               infer_instance
             letI : SigmaCompactSpace L.M := L.sigmaCompact
             letI : T2Space L.M := L.t2
             y ∈ riemannianClosedBallOf (I := I) (L.S.base.metric 0) L.basepoint 3) →
              L.rmNormSq (I := I) s y ≤ K ^ 2

def WitnessSourceBallCapture (I : ModelWithCorners ℝ E H) (kappa : ℝ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {x : M} {t : ℝ}
    (W : KappaModelWitness.{u, uE, uH} (I := I) (1 / 4) kappa S x t),
    IsCompact (riemannianClosedBallOf (I := I) (witnessGhat (I := I) W (-2)) x 1) ∧
      riemannianClosedBallOf (I := I) (witnessGhat (I := I) W (-2)) x 1 ⊆
        witnessImage (I := I) W

def LocalShiUniformConstant (I : ModelWithCorners ℝ E H) : Prop :=
  ∀ (m : ℕ) (T K R : ℝ), 0 < T → 0 < K → 0 < R →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle ℝ E (TangentSpace I : M → Type _)]
        {alpha omega : ℝ} {halphaomega : alpha < omega}
        (Sc : SolutionOn (I := I) (M := M)
          (RealTimeInterval.closedOpen alpha omega halphaomega)),
        IsSolutionOn (I := I) Sc → ∀ p : M, alpha < 0 → T < omega →
        IsCompact {y : M |
          DifferentialGeometry.riemannianEDistOf (I := I) (Sc.base.metric 0) p y ≤
            ENNReal.ofReal (R / Real.sqrt K)} →
        (∀ s ∈ Set.Icc (0 : ℝ) T, ∀ y : M,
          DifferentialGeometry.riemannianEDistOf (I := I) (Sc.base.metric 0) p y ≤
              ENNReal.ofReal (R / Real.sqrt K) →
            nablaKRm04NormSqIntrinsic (I := I) Sc 0 s y ≤ K ^ 2) →
        ∀ tau ∈ Set.Ioc (0 : ℝ) T, ∀ z : M,
          DifferentialGeometry.riemannianEDistOf (I := I) (Sc.base.metric 0) p z ≤
              ENNReal.ofReal (R / (2 * Real.sqrt K)) →
            Real.sqrt (tau ^ m * nablaKRm04NormSqIntrinsic (I := I) Sc m tau z) ≤ C * K

def ScalarLaplacianCurvatureJetBound (I : ModelWithCorners ℝ E H) (c : ℝ) :
    Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (Sc : SolutionOn (I := I) (M := M) D),
    IsSolutionOn (I := I) Sc → ∀ tau ∈ D.carrier, ∀ z : M,
      |laplacianAt (I := I) (flowG (I := I) Sc) tau (Sc.scalar tau) z| ≤
        c * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) Sc 2 tau z)

end Interfaces



section OperatorNorm

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [IsManifold I 1 M] [T2Space M] in
theorem abs_inner_le_sqrt_mul_sqrt (g : SmoothRiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    |g.inner x u v| ≤ Real.sqrt (g.inner x u u) * Real.sqrt (g.inner x v v) := by
  let D := (tangentMetricDataGen (I := I) g x).metric
  let _ : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let _ : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let _ : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have hnorm : ∀ z : TangentSpace I x, Real.sqrt (g.inner x z z) = ‖z‖ := by
    intro z
    rw [← TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen (I := I) g x) z z]
    change Real.sqrt (D.inner z z) = ‖z‖
    rw [← MetricFiberData.toCore_inner D z z, real_inner_self_eq_norm_sq,
      Real.sqrt_sq_eq_abs, abs_norm]
  have hinner : g.inner x u v = (inner ℝ u v : ℝ) := by
    rw [← TangentMetricDataGen.inner_eq_gen (tangentMetricDataGen (I := I) g x) u v]
    exact (MetricFiberData.toCore_inner D u v).symm
  rw [hnorm, hnorm, hinner]
  exact abs_real_inner_le_norm u v

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannOp_normSq_le_of_rmNormSq_le (g : SmoothRiemannianMetric I M) (z : M)
    {Kb : ℝ} (h : normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) ≤ Kb)
    (a b c : TangentSpace I z) :
    g.inner z (riemannOp (cov := LeviCivita (I := I) g) z a b c)
        (riemannOp (cov := LeviCivita (I := I) g) z a b c) ≤
      Kb * g.inner z a a * g.inner z b b * g.inner z c c := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g z
  set R := riemannOp (cov := LeviCivita (I := I) g) z a b c with hR
  set N := Real.sqrt (normSq0S (I := I) g z 4 (metricRm04At (I := I) g z)) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hkey : g.inner z R R ≤
      N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) * Real.sqrt (g.inner z c c)) *
        Real.sqrt (g.inner z R R) := by
    have heval : g.inner z R R = metricRm04At (I := I) g z (vec4 (I := I) a b c R) := by
      rw [hR, ← metricRm04StandardAt_eq_inner_riemannOp (I := I) g z a b c R]
      rfl
    have habs := abs_apply_le_sqrt_normSq0S (I := I) g z 4 basis hON
      (metricRm04At (I := I) g z) (vec4 (I := I) a b c R)
    have hprod : (∏ i : Fin 4, Real.sqrt (g.inner z (vec4 (I := I) a b c R i)
        (vec4 (I := I) a b c R i))) =
        Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
          Real.sqrt (g.inner z c c) * Real.sqrt (g.inner z R R) := by
      have h0 : vec4 (I := I) a b c R 0 = a := rfl
      have h1 : vec4 (I := I) a b c R 1 = b := rfl
      have h2 : vec4 (I := I) a b c R 2 = c := rfl
      have h3 : vec4 (I := I) a b c R 3 = R := rfl
      rw [Fin.prod_univ_four, h0, h1, h2, h3]
    rw [hprod] at habs
    calc g.inner z R R = metricRm04At (I := I) g z (vec4 (I := I) a b c R) := heval
      _ ≤ |metricRm04At (I := I) g z (vec4 (I := I) a b c R)| := le_abs_self _
      _ ≤ N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
            Real.sqrt (g.inner z c c) * Real.sqrt (g.inner z R R)) := habs
      _ = N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
            Real.sqrt (g.inner z c c)) * Real.sqrt (g.inner z R R) := by ring
  have hRR : 0 ≤ g.inner z R R := inner_self_nonneg (I := I) g z R
  have hroot : Real.sqrt (g.inner z R R) ≤
      N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
        Real.sqrt (g.inner z c c)) := by
    rcases eq_or_lt_of_le (Real.sqrt_nonneg (g.inner z R R)) with hz | hz
    · have hprodnn : 0 ≤ N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
          Real.sqrt (g.inner z c c)) := by positivity
      rw [← hz]
      exact hprodnn
    · have hsq : Real.sqrt (g.inner z R R) * Real.sqrt (g.inner z R R) = g.inner z R R :=
        Real.mul_self_sqrt hRR
      nlinarith [hkey, hsq]
  have hsqNsq : N ^ 2 = normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) :=
    Real.sq_sqrt (normSq0S_nonneg (I := I) g z 4 _)
  have haa : Real.sqrt (g.inner z a a) ^ 2 = g.inner z a a :=
    Real.sq_sqrt (inner_self_nonneg (I := I) g z a)
  have hbb : Real.sqrt (g.inner z b b) ^ 2 = g.inner z b b :=
    Real.sq_sqrt (inner_self_nonneg (I := I) g z b)
  have hcc : Real.sqrt (g.inner z c c) ^ 2 = g.inner z c c :=
    Real.sq_sqrt (inner_self_nonneg (I := I) g z c)
  have hsqrt : g.inner z R R ≤
      (N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
        Real.sqrt (g.inner z c c))) ^ 2 := by
    have hsq : Real.sqrt (g.inner z R R) ^ 2 = g.inner z R R :=
      Real.sq_sqrt hRR
    nlinarith [hroot, Real.sqrt_nonneg (g.inner z R R)]
  have hexpand : (N * (Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
      Real.sqrt (g.inner z c c))) ^ 2 =
      normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) *
        g.inner z a a * g.inner z b b * g.inner z c c := by
    rw [mul_pow, mul_pow, mul_pow, hsqNsq, haa, hbb, hcc]
    ring
  rw [hexpand] at hsqrt
  refine le_trans hsqrt ?_
  have h1 : 0 ≤ g.inner z a a := inner_self_nonneg (I := I) g z a
  have h2 : 0 ≤ g.inner z b b := inner_self_nonneg (I := I) g z b
  have h3 : 0 ≤ g.inner z c c := inner_self_nonneg (I := I) g z c
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h h1) h2) h3
  exact this

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem rmNormSq_le_of_riemannOp_norm_le (g : SmoothRiemannianMetric I M) (z : M)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a b c : TangentSpace I z,
      Real.sqrt (g.inner z (riemannOp (cov := LeviCivita (I := I) g) z a b c)
          (riemannOp (cov := LeviCivita (I := I) g) z a b c)) ≤
        C * Real.sqrt (g.inner z a a) * Real.sqrt (g.inner z b b) *
          Real.sqrt (g.inner z c c)) :
    normSq0S (I := I) g z 4 (metricRm04At (I := I) g z) ≤
      (Module.finrank ℝ E : ℝ) ^ 4 * C ^ 2 := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g z
  have hinv : MetricInverseInBasis (I := I) g z basis
      (identityInvMetric (Idx := Fin (Module.finrank ℝ (TangentSpace I z)))) :=
    metricInverseInBasis_of_orthonormal (I := I) g basis hON
  have hcomp : ∀ slots : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I z)),
      |component0S (I := I) basis (metricRm04At (I := I) g z) slots| ≤ C := by
    intro slots
    have hunit : ∀ i, Real.sqrt (g.inner z (basis i) (basis i)) = 1 := by
      intro i
      rw [hON i i]
      simp
    have heq : component0S (I := I) basis (metricRm04At (I := I) g z) slots =
        g.inner z (basis (slots 3))
          (riemannOp (cov := LeviCivita (I := I) g) z (basis (slots 0)) (basis (slots 1))
            (basis (slots 2))) := by
      rw [← metricRm04StandardAt_eq_inner_riemannOp (I := I) g z (basis (slots 0)) (basis (slots 1))
        (basis (slots 2)) (basis (slots 3))]
      change metricRm04At (I := I) g z (fun a => basis (slots a)) = _
      congr 1
      funext a
      fin_cases a <;> rfl
    rw [heq]
    refine le_trans (abs_inner_le_sqrt_mul_sqrt (I := I) g z _ _) ?_
    rw [hunit, one_mul]
    have hb := h (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
    rw [hunit, hunit, hunit] at hb
    simpa using hb
  have hcard := normSq0S_le_card_of_component_bound (I := I) g z 4 basis hinv
    (metricRm04At (I := I) g z) C hC hcomp
  refine le_trans hcard (le_of_eq ?_)
  have hfr : Module.finrank ℝ (TangentSpace I z) = Module.finrank ℝ E := rfl
  have hc : (Fintype.card (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I z))) : ℝ) =
      (Module.finrank ℝ E : ℝ) ^ 4 := by
    rw [Fintype.card_fun]
    simp [hfr]
  rw [hc]

end OperatorNorm



section Naturality

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [IsManifold I 1 N] [T2Space N] [SigmaCompactSpace N]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem metricRm04At_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [T2Space U] [IsManifold I 1 U]
    (y : U) :
    metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y =
      metricRm04At (I := I) (M := M) g (y : M) := by
  ext w
  have hw : w = vec4 (I := I) (w 0) (w 1) (w 2) (w 3) := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  have h := metricRm04StandardAt_restrictOpen (I := I) g U y (w 0) (w 1) (w 2) (w 3)
  simp only [mfderiv_subtype_val_apply] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem rmNormSq_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) [T2Space U] [IsManifold I 1 U]
    (y : U) :
    normSq0S (I := I) (M := U) (g.restrictOpen (I := I) U) y 4
        (metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y) =
      normSq0S (I := I) (M := M) g (y : M) 4 (metricRm04At (I := I) (M := M) g (y : M)) := by
  rw [normSq0S_restrictOpen_apply (I := I) g U 4 y
    (metricRm04At (I := I) (M := U) (g.restrictOpen (I := I) U) y),
    metricRm04At_restrictOpen (I := I) g U y]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 1 N]
  [SigmaCompactSpace N] in
theorem rmNormSq_openPullbackMetric
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞))
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    [T2Space U] [IsManifold I 1 U]
    (g : SmoothRiemannianMetric I M) (y : U)
    [T2Space (⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ : TopologicalSpace.Opens M)]
    [IsManifold I 1
      (⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ : TopologicalSpace.Opens M)] :
    normSq0S (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y 4
        (metricRm04At (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y) =
      normSq0S (I := I) (M := M) g ((F : N → M) (y : N)) 4
        (metricRm04At (I := I) (M := M) g ((F : N → M) (y : N))) := by
  classical
  set W' : TopologicalSpace.Opens M :=
    ⟨(F : N → M) '' (U : Set N), image_opens_isOpen F hU⟩ with hW'
  set Phi := PartialDiffeomorph.toOpensDiffeo F hU with hPhi
  obtain ⟨basis, hON⟩ :=
    exists_orthonormal_basis (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y
  have hval : ((Phi y : W') : M) = (F : N → M) (y : N) := rfl
  have hT : ∀ slots : Fin 4 → TangentSpace I y,
      metricRm04At (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y slots =
        metricRm04At (I := I) (M := W') (g.restrictOpen (I := I) W') (Phi y)
          (fun q : Fin 4 => mfderiv I I (Phi : U → W') y (slots q)) := by
    intro slots
    have hs : slots = vec4 (I := I) (slots 0) (slots 1) (slots 2) (slots 3) := by
      funext i
      fin_cases i <;> rfl
    have hs' : (fun q : Fin 4 => mfderiv I I (Phi : U → W') y (slots q)) =
        vec4 (I := I) (mfderiv I I (Phi : U → W') y (slots 0))
          (mfderiv I I (Phi : U → W') y (slots 1))
          (mfderiv I I (Phi : U → W') y (slots 2))
          (mfderiv I I (Phi : U → W') y (slots 3)) := by
      funext i
      fin_cases i <;> rfl
    rw [hs', hs]
    exact metricRm04Standard_pullback (I := I) (g.restrictOpen (I := I) W') Phi y
      (slots 0) (slots 1) (slots 2) (slots 3)
  have h1 : normSq0S (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y 4
        (metricRm04At (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y) =
      normSq0S (I := I) (M := W') (g.restrictOpen (I := I) W') (Phi y) 4
        (metricRm04At (I := I) (M := W') (g.restrictOpen (I := I) W') (Phi y)) :=
    normSq0S_pullback_eval_of_orthonormal (I := I) (M := U) (N := W')
      (g.restrictOpen (I := I) W') Phi y 4 basis hON
      (metricRm04At (I := I) (M := U) (openPullbackMetric (I := I) F U hU g) y)
      (metricRm04At (I := I) (M := W') (g.restrictOpen (I := I) W') (Phi y)) hT
  rw [h1, rmNormSq_restrictOpen (I := I) g W' (Phi y), hval]

end Naturality



section ScalarGradient

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [SigmaCompactSpace M] in
theorem scalarDifferential_eq_frame_trace (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    (v : TangentSpace I x) :
    scalarDifferential (I := I) S t x v =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) v
            (smoothOrthoFrame (I := I) (S.base.metric t) x i x)
            (smoothOrthoFrame (I := I) (S.base.metric t) x k x)
            (smoothOrthoFrame (I := I) (S.base.metric t) x k x)
            (smoothOrthoFrame (I := I) (S.base.metric t) x i x)) := by
  classical
  set g := S.base.metric t with hgdef
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hBdef
  have hBsm : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)) :=
    fun i => smoothOrthoFrame_smooth (I := I) g x i
  set V : Π b : M, TangentSpace I b := smoothExtensionTangent (I := I) x v with hVdef
  have hVsm : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hVx : V x = v := smoothExtensionTangent_eq (I := I) x v
  have hstep1 : scalarDifferential (I := I) S t x v = nablaScalar (I := I) g V x := by
    have hfun : (fun y : M => S.scalar t y) = scalarCurv (I := I) g := by
      funext y
      change metricScalarAt (I := I) g y = scalarCurv (I := I) g y
      exact metricScalar_eq_scal (I := I) g y
    rw [nablaScalar_def, hVx]
    change mfderiv I (modelWithCornersSelf ℝ ℝ) (fun y : M => S.scalar t y) x v = _
    rw [hfun]
    rfl
  have hstep2 : nablaScalar (I := I) g V x =
      ∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
        g.inner x (nablaCurvSec (LeviCivita (I := I) g) V (B i) (B k) (B k) x) (B i x) := by
    rw [nablaScalar_eq_frame_trace_nablaRicci (I := I) g]
    exact Finset.sum_congr rfl fun k _ =>
      nablaRicci_eq_frame_trace_nablaCurvSec (I := I) g hVsm (hBsm k) (hBsm k)
  have hterm : ∀ k i : Fin (Module.finrank ℝ E),
      g.inner x (nablaCurvSec (LeviCivita (I := I) g) V (B i) (B k) (B k) x) (B i x) =
        nablaKRm04Field (I := I) S t 1 x
          (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x)) := by
    intro k i
    have hsec : nablaCurvSec (LeviCivita (I := I) g) V (B i) (B k) (B k) x =
        nablaRiemannOp (I := I) g x v (B i x) (B k x) (B k x) := by
      rw [LeviCivita_eq_leviCivitaConnectionOfMetric, ← hVx]
      exact (nablaRiemannOp_sec (I := I) g (ContMDiffSection.mk V hVsm)
        (ContMDiffSection.mk (B i) (hBsm i)) (ContMDiffSection.mk (B k) (hBsm k))
        (ContMDiffSection.mk (B k) (hBsm k)) x).symm
    have hrm : totalNabla0SFun (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 4
          (leviCivitaConnectionOfMetric (I := I) g)
          (CovariantDerivative.rm04Section (I := I) g (leviCivitaConnectionOfMetric (I := I) g)
            (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally (I := I) g)) x
          (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x)) =
        g.inner x (B i x) (nablaRiemannOp (I := I) g x v (B i x) (B k x) (B k x)) :=
      nablaRm04_apply (I := I) g x v (B i x) (B k x) (B k x) (B i x)
    rw [hsec, g.symm x _ (B i x), ← hrm]
    rfl
  rw [hstep1, hstep2]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => hterm k i

omit [SigmaCompactSpace M] in
theorem abs_scalarDifferential_le (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M)
    (v : TangentSpace I x) :
    |scalarDifferential (I := I) S t x v| ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := by
  classical
  set g := S.base.metric t with hgdef
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hBdef
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
  set N := Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) with hN
  have hunit : ∀ i, Real.sqrt (g.inner x (B i x) (B i x)) = 1 := by
    intro i
    have h := smoothOrthoFrame_orthonormal_at_center (I := I) g x i i
    rw [hBdef]
    simp [h]
  have hbound : ∀ k i : Fin (Module.finrank ℝ E),
      |nablaKRm04Field (I := I) S t 1 x
        (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x))| ≤
      N * Real.sqrt (g.inner x v v) := by
    intro k i
    have habs := abs_apply_le_sqrt_normSq0S (I := I) g x (4 + 1) basis hON
      (nablaKRm04Field (I := I) S t 1 x) (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x))
    have hprod : (∏ a : Fin (4 + 1),
        Real.sqrt (g.inner x (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) a)
          (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) a))) =
        Real.sqrt (g.inner x v v) := by
      have h0 : vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) 0 = v := rfl
      have h1 : vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) 1 = B i x := rfl
      have h2 : vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) 2 = B k x := rfl
      have h3 : vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) 3 = B k x := rfl
      have h4 : vec5 (I := I) v (B i x) (B k x) (B k x) (B i x) 4 = B i x := rfl
      rw [Fin.prod_univ_five, h0, h1, h2, h3, h4, hunit, hunit]
      ring
    rw [hprod] at habs
    exact habs
  rw [scalarDifferential_eq_frame_trace (I := I) S t x v]
  calc |∑ k : Fin (Module.finrank ℝ E), ∑ i : Fin (Module.finrank ℝ E),
          nablaKRm04Field (I := I) S t 1 x
            (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x))|
      ≤ ∑ k : Fin (Module.finrank ℝ E), |∑ i : Fin (Module.finrank ℝ E),
          nablaKRm04Field (I := I) S t 1 x
            (vec5 (I := I) v (B i x) (B k x) (B k x) (B i x))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin (Module.finrank ℝ E), ∑ _i : Fin (Module.finrank ℝ E),
          N * Real.sqrt (g.inner x v v) := by
        refine Finset.sum_le_sum fun k _ => le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        exact Finset.sum_le_sum fun i _ => hbound k i
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * N * Real.sqrt (g.inner x v v) := by
        simp [Finset.sum_const, Finset.card_univ]
        ring

end ScalarGradient



section Transport

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} {x : M} {t : ℝ}

def sourceCurvatureBound (n : ℕ) (K : ℝ) : ℝ := (n : ℝ) ^ 2 * (10 + 2 * K) + 1

theorem sourceCurvatureBound_pos (n : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    0 < sourceCurvatureBound n K := by
  have h : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (10 + 2 * K) := by positivity
  unfold sourceCurvatureBound
  linarith

omit [NeZero (Module.finrank ℝ E)] in
theorem witnessSourceCurvature {kappa K : ℝ} (hK0 : 0 ≤ K)
    (W : KappaModelWitness.{u, uE, uH} (I := I) (1 / 4) kappa S x t)
    (hmodel : ∀ s ∈ Set.Icc (-(4 : ℝ)) 0, ∀ y : W.model.M,
      y ∈ witnessModelBall (I := I) W → W.model.rmNormSq (I := I) s y ≤ K ^ 2)
    {s : ℝ} (hs : s ∈ Set.Icc (-(4 : ℝ)) 0) {z : M} (hz : z ∈ witnessImage (I := I) W) :
    normSq0S (I := I) (witnessGhat (I := I) W s) z 4
        (metricRm04At (I := I) (witnessGhat (I := I) W s) z) ≤
      sourceCurvatureBound (Module.finrank ℝ E) K ^ 2 := by
  classical
  let : TopologicalSpace W.model.M := W.model.topology
  let : ChartedSpace H W.model.M := W.model.charted
  let : IsManifold I ∞ W.model.M := W.model.smooth
  let : IsManifold I 1 W.model.M :=
    IsManifold.of_le (I := I) (M := W.model.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) W.model.M := by
    change IsManifold I ∞ W.model.M
    infer_instance
  let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
  let : T2Space W.model.M := W.model.t2
  obtain ⟨y, hyball, hyz⟩ := hz
  set F := W.embedding with hF
  set h : ℝ → SmoothRiemannianMetric I W.model.M := fun sigma => W.model.S.base.metric sigma
    with hh
  set ghat := witnessGhat (I := I) W with hghat
  have hC : ModelComparison (I := I) (M := M) (N := W.model.M) (1 / 4) h ghat
      W.model.basepoint x F := W.comparison
  have hysrc : y ∈ F.source := by
    refine hC.buffered_ball_subset ?_
    exact riemannianClosedBallOf_mono (I := I) (h 0) W.model.basepoint
      (by linarith : modelRadius (1 / 4 : ℝ) ≤ modelRadius (1 / 4 : ℝ) + 1) hyball
  let : SigmaCompactSpace ↥(sourceOpen (I := I) F) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (sourceOpen (I := I) F).isOpen)
  let : SigmaCompactSpace
      ↥(⟨(F : W.model.M → M) '' ((sourceOpen (I := I) F) : Set W.model.M),
        image_opens_isOpen F (sourceOpen_subset (I := I) F)⟩ : TopologicalSpace.Opens M) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I (image_opens_isOpen F (sourceOpen_subset (I := I) F)))
  set y' : ↥(sourceOpen (I := I) F) := ⟨y, hysrc⟩ with hy'def
  have hy' : y' ∈ witnessWindow (I := I) F (1 / 4) h W.model.basepoint := hyball
  have hdepth : modelDepth (1 / 4 : ℝ) = 4 := by
    unfold modelDepth
    norm_num
  have hs' : s ∈ Set.Icc (-(modelDepth (1 / 4 : ℝ))) (0 : ℝ) := by
    rw [hdepth]
    exact hs
  have hmodelnorm : normSq0S (I := I) (witnessModelMetric (I := I) F h s) y' 4
      (metricRm04At (I := I) (witnessModelMetric (I := I) F h s) y') ≤ K ^ 2 := by
    rw [witnessModelMetric, rmNormSq_restrictOpen (I := I) (h s) (sourceOpen (I := I) F) y']
    exact hmodel s hs y hyball
  have hKb : ∀ a b c : TangentSpace I y',
      (witnessModelMetric (I := I) F h s).inner y'
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s)) y' a b c)
          (riemannOp (cov := LeviCivita (I := I) (witnessModelMetric (I := I) F h s))
            y' a b c) ≤
        K ^ 2 * (witnessModelMetric (I := I) F h s).inner y' a a *
          (witnessModelMetric (I := I) F h s).inner y' b b *
          (witnessModelMetric (I := I) F h s).inner y' c c := fun a b c =>
    riemannOp_normSq_le_of_rmNormSq_le (I := I) (witnessModelMetric (I := I) F h s) y'
      hmodelnorm a b c
  set Cop := witnessLambda (1 / 4 : ℝ) ^ 2 * (witnessRiemannC (1 / 4 : ℝ) + Real.sqrt (K ^ 2))
    with hCop
  have hT2 : ∀ a b c : TangentSpace I y',
      Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y'
          (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y' a b c)
          (riemannOp (cov := LeviCivita (I := I) (witnessPullbackMetric (I := I) F ghat s))
            y' a b c)) ≤
        Cop * Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y' a a) *
          Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y' b b) *
          Real.sqrt ((witnessPullbackMetric (I := I) F ghat s).inner y' c c) := fun a b c =>
    modelComparison_riemannOp_norm_le (I := I) (by norm_num) (by norm_num) hC hs' hy'
      (by positivity) hKb a b c
  have hCop0 : 0 ≤ Cop := by
    have h1 : (0 : ℝ) ≤ witnessRiemannC (1 / 4 : ℝ) :=
      witnessRiemannC_nonneg (by norm_num) (by norm_num)
    have h2 : (0 : ℝ) ≤ Real.sqrt (K ^ 2) := Real.sqrt_nonneg _
    have h3 : (0 : ℝ) ≤ witnessLambda (1 / 4 : ℝ) ^ 2 := sq_nonneg _
    rw [hCop]
    positivity
  have hCople : Cop ≤ 10 + 2 * K := by
    have hL1 : (1 : ℝ) ≤ witnessLambda (1 / 4 : ℝ) :=
      one_le_witnessLambda (by norm_num) (by norm_num)
    have hL : witnessLambda (1 / 4 : ℝ) ≤ 4 / 3 := witnessLambda_le (by norm_num)
    have hR : witnessRiemannC (1 / 4 : ℝ) ≤ 20 * (1 / 4 : ℝ) :=
      witnessRiemannC_le (by norm_num) (by norm_num)
    have hRt : Real.sqrt (K ^ 2) = K := by
      rw [Real.sqrt_sq hK0]
    have hC0 : (0 : ℝ) ≤ witnessRiemannC (1 / 4 : ℝ) :=
      witnessRiemannC_nonneg (by norm_num) (by norm_num)
    have hLsq : witnessLambda (1 / 4 : ℝ) ^ 2 ≤ 16 / 9 := by nlinarith [hL1, hL]
    have hsum : witnessRiemannC (1 / 4 : ℝ) + K ≤ 5 + K := by linarith
    have hsum0 : (0 : ℝ) ≤ witnessRiemannC (1 / 4 : ℝ) + K := by linarith
    have hstep : witnessLambda (1 / 4 : ℝ) ^ 2 * (witnessRiemannC (1 / 4 : ℝ) + K) ≤
        16 / 9 * (5 + K) :=
      mul_le_mul hLsq hsum hsum0 (by norm_num)
    rw [hCop, hRt]
    linarith [hstep]
  have hpull : normSq0S (I := I) (witnessPullbackMetric (I := I) F ghat s) y' 4
      (metricRm04At (I := I) (witnessPullbackMetric (I := I) F ghat s) y') ≤
      (Module.finrank ℝ E : ℝ) ^ 4 * Cop ^ 2 :=
    rmNormSq_le_of_riemannOp_norm_le (I := I) (witnessPullbackMetric (I := I) F ghat s) y'
      hCop0 hT2
  have hnat : normSq0S (I := I) (witnessPullbackMetric (I := I) F ghat s) y' 4
      (metricRm04At (I := I) (witnessPullbackMetric (I := I) F ghat s) y') =
      normSq0S (I := I) (ghat s) z 4 (metricRm04At (I := I) (ghat s) z) := by
    rw [witnessPullbackMetric,
      rmNormSq_openPullbackMetric (I := I) F (sourceOpen (I := I) F)
        (sourceOpen_subset (I := I) F) (ghat s) y']
    rw [hyz]
  rw [hnat] at hpull
  refine le_trans hpull ?_
  have hbase : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (10 + 2 * K) := by positivity
  have hsq : Cop ^ 2 ≤ (10 + 2 * K) ^ 2 := by nlinarith [hCop0, hCople]
  have hfin : (Module.finrank ℝ E : ℝ) ^ 4 * Cop ^ 2 ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * (10 + 2 * K)) ^ 2 := by nlinarith [sq_nonneg ((Module.finrank ℝ E : ℝ) ^ 2)]
  refine le_trans hfin ?_
  unfold sourceCurvatureBound
  nlinarith [hbase]

end Transport



section MainTheorem

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem modelRadius_quarter : modelRadius (1 / 4 : ℝ) = 2 := by
  have h : (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
  unfold modelRadius
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem le_sq_of_sqrt_le {a c : ℝ} (ha : 0 ≤ a) (h : Real.sqrt a ≤ c) : a ≤ c ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

def goodPointConst (n : ℕ) (clap C1 C2 K : ℝ) : ℝ :=
  max ((n : ℝ) ^ 2 * (C1 * sourceCurvatureBound n K))
    (clap * (C2 * sourceCurvatureBound n K) +
      2 * (n : ℝ) ^ 4 * sourceCurvatureBound n K ^ 2)

theorem goodPointConst_nonneg {n : ℕ} {clap C1 C2 K : ℝ} (_hclap : 0 ≤ clap) (hC1 : 0 ≤ C1)
    (_hC2 : 0 ≤ C2) (hK : 0 ≤ K) : 0 ≤ goodPointConst n clap C1 C2 K := by
  have hK0 : 0 ≤ sourceCurvatureBound n K := (sourceCurvatureBound_pos n hK).le
  have h1 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * (C1 * sourceCurvatureBound n K) := by positivity
  exact le_trans h1 (le_max_left _ _)

theorem goodPointBoundsOn_of_modelCurvatureBound
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] {kappa clap : ℝ} (hclap : 0 ≤ clap)
    (hmod : ModelCurvatureBoundNearBase.{u, uE, uH} I kappa)
    (hcap : WitnessSourceBallCapture.{u, uE, uH} I kappa)
    (hshi : LocalShiUniformConstant.{u, uE, uH} I)
    (hlap : ScalarLaplacianCurvatureJetBound.{u, uE, uH} I clap) :
    ∃ CStar : ℝ, 0 ≤ CStar ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [IsManifold I 1 M] [IsManifold I 2 M] [T2Space M] [SigmaCompactSpace M]
        [VectorBundle ℝ E (TangentSpace I : M → Type _)]
        {T : ℝ} {hT : (0 : ℝ) < T}
        (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)),
        IsSolutionOn (I := I) S → ∀ (x : M) (t eps : ℝ), 0 < eps → eps ≤ 1 / 4 →
          IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
            (∀ v : TangentSpace I x,
                |scalarDifferential (I := I) S t x v| ≤
                  2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                    Real.sqrt ((S.base.metric t).inner x v v)) ∧
              |deriv (fun tau : ℝ => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2 := by
  classical
  obtain ⟨K, hK0, hKmodel⟩ := hmod
  set K0 := sourceCurvatureBound (Module.finrank ℝ E) K with hK0def
  have hK0pos : 0 < K0 := sourceCurvatureBound_pos _ hK0
  have hsqrtK0 : 0 < Real.sqrt K0 := Real.sqrt_pos.2 hK0pos
  obtain ⟨C1, hC10, hC1⟩ := hshi 1 2 K0 (Real.sqrt K0) (by norm_num) hK0pos hsqrtK0
  obtain ⟨C2, hC20, hC2⟩ := hshi 2 2 K0 (Real.sqrt K0) (by norm_num) hK0pos hsqrtK0
  refine ⟨goodPointConst (Module.finrank ℝ E) clap C1 C2 K,
    goodPointConst_nonneg hclap hC10 hC20 hK0, ?_⟩
  intro M _ _ _ _ _ _ _ _ T hT S hS x t eps heps0 heps4 hgood
  obtain ⟨W⟩ := isGoodPoint_mono (I := I) heps4 (by norm_num) hgood
  set Q := S.scalar t x with hQdef
  have hQpos : 0 < Q := W.scalar_pos
  have hinv4 : ((1 / 4 : ℝ) * Q)⁻¹ = 4 / Q := by
    field_simp
  have hwin : Set.Icc (t - 4 / Q) t ⊆ Set.Ico (0 : ℝ) T := by
    have h := W.window_mem
    rwa [hinv4] at h
  have h4Q : 0 < 4 / Q := by positivity
  have hlow : (0 : ℝ) ≤ t - 4 / Q :=
    (hwin ⟨le_rfl, by linarith⟩).1
  have htT : t < T := (hwin ⟨by linarith, le_rfl⟩).2
  have hQt : (4 : ℝ) ≤ Q * t := by
    have h : 4 / Q ≤ t := by linarith
    calc (4 : ℝ) = Q * (4 / Q) := by field_simp
      _ ≤ Q * t := by nlinarith
  set tau := t - 2 / Q with htaudef
  have h2Q : 0 < 2 / Q := by positivity
  have h24 : 2 / Q ≤ 4 / Q := by
    have hsum : (2 : ℝ) / Q + 2 / Q = 4 / Q := by ring
    linarith
  have htau_mem : tau ∈ (RealTimeInterval.closedOpen 0 T hT).carrier := by
    refine hwin ⟨by rw [htaudef]; linarith, by rw [htaudef]; linarith⟩
  set P := parabolicSolution (I := I) S tau Q hQpos htau_mem with hPdef
  have hPsol : IsSolutionOn (I := I) P := parabolicSolution_isSolutionOn (I := I) S hS tau Q hQpos htau_mem
  set alpha := -(Q * tau) with halphadef
  set omega := Q * (T - tau) with homegadef
  have halpha : alpha < 0 := by
    have hqt : Q * tau = Q * t - 2 := by rw [htaudef]; field_simp
    rw [halphadef, hqt]
    linarith
  have homega : (2 : ℝ) < omega := by
    have h1 : Q * (T - tau) = Q * (T - t) + 2 := by rw [htaudef]; field_simp; ring
    have h2 : 0 < Q * (T - t) := by nlinarith
    rw [homegadef, h1]
    linarith
  have hao : alpha < omega := by linarith
  have hcarrier : (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) tau Q htau_mem).carrier =
      (RealTimeInterval.closedOpen alpha omega hao).carrier := by
    rw [parabolicInterval_closedOpen_carrier hT hQpos htau_mem]
    rfl
  have hregular : (parabolicInterval (RealTimeInterval.closedOpen 0 T hT) tau Q htau_mem).regular =
      (RealTimeInterval.closedOpen alpha omega hao).regular := by
    rw [parabolicInterval_closedOpen_regular hT hQpos htau_mem]
    rfl
  set S' := P.cast (RealTimeInterval.closedOpen alpha omega hao) with hS'def
  have hS'sol : IsSolutionOn (I := I) S' := isSolutionOn_cast hPsol hcarrier hregular
  have hmetric : ∀ s : ℝ, S'.base.metric s = witnessGhat (I := I) W (s - 2) := by
    intro s
    have hpt : parabolicTime tau Q s = parabolicTime t Q (s - 2) := by
      unfold parabolicTime
      rw [htaudef]
      field_simp
      ring
    simp only [hS'def, SolutionOn.cast_base, hPdef, parabolicSolution_metric, witnessGhat,
      rescaledMetric, hpt]
    rfl
  have hmodelball : ∀ s ∈ Set.Icc (-(4 : ℝ)) 0, ∀ y : W.model.M,
      y ∈ witnessModelBall (I := I) W → W.model.rmNormSq (I := I) s y ≤ K ^ 2 := by
    intro s hs y hy
    let : TopologicalSpace W.model.M := W.model.topology
    let : ChartedSpace H W.model.M := W.model.charted
    let : IsManifold I ∞ W.model.M := W.model.smooth
    let : IsManifold I 1 W.model.M :=
      IsManifold.of_le (I := I) (M := W.model.M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    let : IsManifold I ((∞ : WithTop ℕ∞) + 1) W.model.M := by
      change IsManifold I ∞ W.model.M
      infer_instance
    let : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    let : T2Space W.model.M := W.model.t2
    refine hKmodel W.model W.model_ancient W.model_scalar_base s hs y ?_
    refine riemannianClosedBallOf_mono (I := I) (W.model.S.base.metric 0) W.model.basepoint ?_ hy
    rw [modelRadius_quarter]
    norm_num
  obtain ⟨hcompact, hsub⟩ := hcap M W
  have hballeq : {y : M | DifferentialGeometry.riemannianEDistOf (I := I) (S'.base.metric 0) x y ≤
      ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0)} =
      riemannianClosedBallOf (I := I) (witnessGhat (I := I) W (-2)) x 1 := by
    have hone : Real.sqrt K0 / Real.sqrt K0 = 1 := div_self (ne_of_gt hsqrtK0)
    have hz : (0 : ℝ) - 2 = -2 := by norm_num
    rw [hone, hmetric 0, hz]
    rfl
  have hcompact' : IsCompact {y : M |
      DifferentialGeometry.riemannianEDistOf (I := I) (S'.base.metric 0) x y ≤
        ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0)} := by
    rw [hballeq]
    exact hcompact
  have hu : ∀ s ∈ Set.Icc (0 : ℝ) 2, ∀ y : M,
      DifferentialGeometry.riemannianEDistOf (I := I) (S'.base.metric 0) x y ≤
          ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0) →
        nablaKRm04NormSqIntrinsic (I := I) S' 0 s y ≤ K0 ^ 2 := by
    intro s hs y hy
    have hyimg : y ∈ witnessImage (I := I) W := by
      refine hsub ?_
      rw [← hballeq]
      exact hy
    have hconv : nablaKRm04NormSqIntrinsic (I := I) S' 0 s y =
        normSq0S (I := I) (witnessGhat (I := I) W (s - 2)) y 4
          (metricRm04At (I := I) (witnessGhat (I := I) W (s - 2)) y) := by
      have hzero : nablaKRm04NormSqIntrinsic (I := I) S' 0 s y =
          normSq0S (I := I) (S'.base.metric s) y 4
            (metricRm04At (I := I) (S'.base.metric s) y) := rfl
      rw [hzero, hmetric s]
    rw [hconv]
    exact witnessSourceCurvature (I := I) hK0 W hmodelball
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ hyimg
  have hxdist : DifferentialGeometry.riemannianEDistOf (I := I) (S'.base.metric 0) x x ≤
      ENNReal.ofReal (Real.sqrt K0 / (2 * Real.sqrt K0)) := by
    rw [riemannianEDistOf_self]
    simp
  have hxdist0 : DifferentialGeometry.riemannianEDistOf (I := I) (S'.base.metric 0) x x ≤
      ENNReal.ofReal (Real.sqrt K0 / Real.sqrt K0) := by
    rw [riemannianEDistOf_self]
    simp
  have hshi1 := hC1 M S' hS'sol x halpha homega hcompact' hu 2 ⟨by norm_num, le_rfl⟩ x hxdist
  have hshi2 := hC2 M S' hS'sol x halpha homega hcompact' hu 2 ⟨by norm_num, le_rfl⟩ x hxdist
  have hshi0 := hu 2 ⟨by norm_num, le_rfl⟩ x hxdist0
  have hjet : ∀ k : ℕ, nablaKRm04NormSqIntrinsic (I := I) S k t x =
      Q ^ (2 + k) * nablaKRm04NormSqIntrinsic (I := I) S' k 2 x := by
    intro k
    have hcast : nablaKRm04NormSqIntrinsic (I := I) S' k 2 x =
        nablaKRm04NormSqIntrinsic (I := I) P k 2 x := by
      rw [hS'def]
      exact nablaKRm04NormSqIntrinsic_cast (I := I) P k 2 x
    have hpara := parabolicNablaKRmNormSq (I := I) S tau Q hQpos htau_mem k 2 x
    have hpt : parabolicTime tau Q 2 = t := by
      unfold parabolicTime
      rw [htaudef]
      field_simp
      ring
    rw [hpt, ← hPdef] at hpara
    rw [hcast, hpara, ← mul_assoc, ← mul_pow]
    rw [mul_inv_cancel₀ (ne_of_gt hQpos), one_pow, one_mul]
  have hjet0 : nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤ Q ^ 2 * K0 ^ 2 := by
    rw [hjet 0]
    have hQ2 : (0 : ℝ) ≤ Q ^ (2 + 0) := by positivity
    calc Q ^ (2 + 0) * nablaKRm04NormSqIntrinsic (I := I) S' 0 2 x
        ≤ Q ^ (2 + 0) * K0 ^ 2 := mul_le_mul_of_nonneg_left hshi0 hQ2
      _ = Q ^ 2 * K0 ^ 2 := by norm_num
  have hjet1 : nablaKRm04NormSqIntrinsic (I := I) S 1 t x ≤ Q ^ 3 * (C1 * K0) ^ 2 := by
    have hnn : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x := by
      unfold nablaKRm04NormSqIntrinsic
      exact normSq0S_nonneg (I := I) _ _ _ _
    have hb : nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x ≤ (C1 * K0) ^ 2 := by
      have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (1 : ℕ) * nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x := by
        positivity
      have h := le_sq_of_sqrt_le hA hshi1
      have h2 : (2 : ℝ) ^ (1 : ℕ) * nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x =
          2 * nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x := by norm_num
      rw [h2] at h
      linarith
    rw [hjet 1]
    have hQ3 : (0 : ℝ) ≤ Q ^ (2 + 1) := by positivity
    calc Q ^ (2 + 1) * nablaKRm04NormSqIntrinsic (I := I) S' 1 2 x
        ≤ Q ^ (2 + 1) * (C1 * K0) ^ 2 := mul_le_mul_of_nonneg_left hb hQ3
      _ = Q ^ 3 * (C1 * K0) ^ 2 := by norm_num
  have hjet2 : nablaKRm04NormSqIntrinsic (I := I) S 2 t x ≤ Q ^ 4 * (C2 * K0) ^ 2 := by
    have hnn : 0 ≤ nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x := by
      unfold nablaKRm04NormSqIntrinsic
      exact normSq0S_nonneg (I := I) _ _ _ _
    have hb : nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x ≤ (C2 * K0) ^ 2 := by
      have hA : (0 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) * nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x := by
        positivity
      have h := le_sq_of_sqrt_le hA hshi2
      have h2 : (2 : ℝ) ^ (2 : ℕ) * nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x =
          4 * nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x := by norm_num
      rw [h2] at h
      linarith
    rw [hjet 2]
    have hQ4 : (0 : ℝ) ≤ Q ^ (2 + 2) := by positivity
    calc Q ^ (2 + 2) * nablaKRm04NormSqIntrinsic (I := I) S' 2 2 x
        ≤ Q ^ (2 + 2) * (C2 * K0) ^ 2 := mul_le_mul_of_nonneg_left hb hQ4
      _ = Q ^ 4 * (C2 * K0) ^ 2 := by norm_num
  constructor
  · intro v
    have hgrad := abs_scalarDifferential_le (I := I) S t x v
    have hroot : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
        Q * Real.sqrt Q * (C1 * K0) := by
      have h1 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) ≤
          Real.sqrt (Q ^ 3 * (C1 * K0) ^ 2) := Real.sqrt_le_sqrt hjet1
      have h2 : Real.sqrt (Q ^ 3 * (C1 * K0) ^ 2) = Q * Real.sqrt Q * (C1 * K0) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have h3 : Q ^ 3 = Q ^ 2 * Q := by ring
        rw [h3, Real.sqrt_mul (by positivity), Real.sqrt_sq hQpos.le]
      linarith [h1, h2]
    have hnn : 0 ≤ Real.sqrt ((S.base.metric t).inner x v v) := Real.sqrt_nonneg _
    have hCle : (Module.finrank ℝ E : ℝ) ^ 2 * (C1 * K0) ≤
        2 * goodPointConst (Module.finrank ℝ E) clap C1 C2 K := by
      have h := le_max_left ((Module.finrank ℝ E : ℝ) ^ 2 * (C1 * sourceCurvatureBound
        (Module.finrank ℝ E) K))
        (clap * (C2 * sourceCurvatureBound (Module.finrank ℝ E) K) +
          2 * (Module.finrank ℝ E : ℝ) ^ 4 * sourceCurvatureBound (Module.finrank ℝ E) K ^ 2)
      have hpos : 0 ≤ goodPointConst (Module.finrank ℝ E) clap C1 C2 K :=
        goodPointConst_nonneg hclap hC10 hC20 hK0
      unfold goodPointConst at hpos ⊢
      rw [← hK0def] at h
      linarith
    calc |scalarDifferential (I := I) S t x v|
        ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
            Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 1 t x) *
            Real.sqrt ((S.base.metric t).inner x v v) := hgrad
      _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Q * Real.sqrt Q * (C1 * K0)) *
            Real.sqrt ((S.base.metric t).inner x v v) := by
          have hfr : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hroot hfr
          exact mul_le_mul_of_nonneg_right this hnn
      _ ≤ 2 * goodPointConst (Module.finrank ℝ E) clap C1 C2 K * (Q * Real.sqrt Q) *
            Real.sqrt ((S.base.metric t).inner x v v) := by
          have hq : (0 : ℝ) ≤ Q * Real.sqrt Q := by positivity
          have hmul := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCle hq) hnn
          have e1 : (Module.finrank ℝ E : ℝ) ^ 2 * (Q * Real.sqrt Q * (C1 * K0)) *
              Real.sqrt ((S.base.metric t).inner x v v) =
              (Module.finrank ℝ E : ℝ) ^ 2 * (C1 * K0) * (Q * Real.sqrt Q) *
                Real.sqrt ((S.base.metric t).inner x v v) := by ring
          rw [e1]
          exact hmul
  · have hreg : t ∈ (RealTimeInterval.closedOpen 0 T hT).regular := by
      refine ⟨?_, htT⟩
      linarith
    have hevol := scalar_curvature_evolution (I := I) S hS ⟨t, hreg⟩ x
    have hnhds : (RealTimeInterval.closedOpen 0 T hT).carrier ∈ nhds t :=
      (RealTimeInterval.closedOpen 0 T hT).regular_mem_nhds hreg
    have hderiv : deriv (fun tau : ℝ => S.scalar tau x) t =
        laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x +
          2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) :=
      (hevol.hasDerivAt hnhds).deriv
    have hlapbound : |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x| ≤
        clap * Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) :=
      hlap M S hS t (RealTimeInterval.regular_subset _ hreg) x
    have hric : normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) ≤
        (Module.finrank ℝ E : ℝ) ^ 4 * nablaKRm04NormSqIntrinsic (I := I) S 0 t x :=
      ricciSq_le_rm04 (I := I) (S.base.metric t) (S.base.metric t) x
    have hroot2 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ≤
        Q ^ 2 * (C2 * K0) := by
      have h1 : Real.sqrt (nablaKRm04NormSqIntrinsic (I := I) S 2 t x) ≤
          Real.sqrt (Q ^ 4 * (C2 * K0) ^ 2) := Real.sqrt_le_sqrt hjet2
      have h2 : Real.sqrt (Q ^ 4 * (C2 * K0) ^ 2) = Q ^ 2 * (C2 * K0) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        have h3 : Q ^ 4 = (Q ^ 2) ^ 2 := by ring
        rw [h3, Real.sqrt_sq (by positivity)]
      linarith [h1, h2]
    have hCle2 : clap * (C2 * K0) + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * K0 ^ 2 ≤
        goodPointConst (Module.finrank ℝ E) clap C1 C2 K := by
      have h := le_max_right ((Module.finrank ℝ E : ℝ) ^ 2 * (C1 * sourceCurvatureBound
        (Module.finrank ℝ E) K))
        (clap * (C2 * sourceCurvatureBound (Module.finrank ℝ E) K) +
          2 * (Module.finrank ℝ E : ℝ) ^ 4 * sourceCurvatureBound (Module.finrank ℝ E) K ^ 2)
      unfold goodPointConst
      rw [← hK0def] at h
      linarith
    have hQ2 : (0 : ℝ) ≤ Q ^ 2 := by positivity
    have hfr4 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) ^ 4 := by positivity
    rw [hderiv]
    calc |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x +
            2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)|
        ≤ |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x| +
            |2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)| := abs_add_le _ _
      _ ≤ clap * (Q ^ 2 * (C2 * K0)) +
            2 * ((Module.finrank ℝ E : ℝ) ^ 4 * (Q ^ 2 * K0 ^ 2)) := by
          have hb1 : |laplacianAt (I := I) (flowG (I := I) S) t (S.scalar t) x| ≤
              clap * (Q ^ 2 * (C2 * K0)) := by
            refine le_trans hlapbound ?_
            exact mul_le_mul_of_nonneg_left hroot2 hclap
          have hric0 : 0 ≤ normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) :=
            normSq0S_nonneg (I := I) _ _ _ _
          have hb2 : |2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)| ≤
              2 * ((Module.finrank ℝ E : ℝ) ^ 4 * (Q ^ 2 * K0 ^ 2)) := by
            rw [abs_of_nonneg (by linarith)]
            have h3 : (Module.finrank ℝ E : ℝ) ^ 4 *
                nablaKRm04NormSqIntrinsic (I := I) S 0 t x ≤
                (Module.finrank ℝ E : ℝ) ^ 4 * (Q ^ 2 * K0 ^ 2) :=
              mul_le_mul_of_nonneg_left hjet0 hfr4
            linarith
          linarith
      _ ≤ goodPointConst (Module.finrank ℝ E) clap C1 C2 K * Q ^ 2 := by
          have e : clap * (Q ^ 2 * (C2 * K0)) +
              2 * ((Module.finrank ℝ E : ℝ) ^ 4 * (Q ^ 2 * K0 ^ 2)) =
              (clap * (C2 * K0) + 2 * (Module.finrank ℝ E : ℝ) ^ 4 * K0 ^ 2) * Q ^ 2 := by
            ring
          rw [e]
          exact mul_le_mul_of_nonneg_right hCle2 hQ2

section InverseForm

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem inverseCurvatureDerivatives_of_goodPointBounds
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t eps kappa CStar : ℝ}
    (hgood : IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t)
    (hgrad : ∀ v : TangentSpace I x, |scalarDifferential (I := I) S t x v| ≤
      2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
        Real.sqrt ((S.base.metric t).inner x v v))
    (htime : |deriv (fun tau : ℝ => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2) :
    (∀ v : TangentSpace I x,
        1 / 2 * |scalarDifferential (I := I) S t x v| /
            (S.scalar t x * Real.sqrt (S.scalar t x)) ≤
          CStar * Real.sqrt ((S.base.metric t).inner x v v)) ∧
      |deriv (fun tau : ℝ => S.scalar tau x) t| / S.scalar t x ^ 2 ≤ CStar :=
  inverse_curvature_derivative_bounds (I := I)
    (scalar_pos_of_isGoodPoint (I := I) hgood) hgrad htime

end InverseForm

end MainTheorem

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
