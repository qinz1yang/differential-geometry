import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1MetricLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepB1MetricReverse
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivError
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivMetric
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivPullbackCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricDerivNormFlat

set_option autoImplicit false

/-!
# Component covariant-derivative tails for Step B1

This file upgrades the moving pullback-metric coefficient convergence to the
complete finite component covariant-derivative tower on the producer-owned
finite source-chart cover.  Intrinsic tensor norms and pullback-field carriers
remain downstream.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Filter Topology
open Set Bundle Manifold
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

private noncomputable def constTangentSection (v : E) :
    ContMDiffSection 𝓘(Real, E) E (∞ : WithTop ℕ∞)
      (TangentSpace 𝓘(Real, E) : E → Type _) where
  toFun := fun x : E => (show TangentSpace 𝓘(Real, E) x from v)
  contMDiff_toFun := contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

omit [NeZero (Module.finrank Real E)] in
private theorem constBasis_isLocalFrame_open
    {Idx : Type*} [Fintype Idx]
    (U : TopologicalSpace.Opens E) [SigmaCompactSpace U] [T2Space U]
    (e : Module.Basis Idx Real E) :
    IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      (fun i (x : U) => (show TangentSpace 𝓘(Real, E) x from e i)) Set.univ := by
  constructor
  · intro _x _hx
    change LinearIndependent Real e
    exact e.linearIndependent
  · intro _x _hx
    change ⊤ ≤ Submodule.span Real (Set.range e)
    rw [e.span_eq]
  · intro i
    have hsmooth : ContMDiff 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (fun y : U => (Integral.Connection.restrictOpenTangentSection
          (I := 𝓘(Real, E)) U (constTangentSection (E := E) (e i))) y)) :=
      (Integral.Connection.restrictOpenTangentSection
        (I := 𝓘(Real, E)) U (constTangentSection (E := E) (e i))).contMDiff.of_le
          (by simp : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    have hsec : ContMDiffOn 𝓘(Real, E)
        (𝓘(Real, E).prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
        (T% (fun y : U => (Integral.Connection.restrictOpenTangentSection
          (I := 𝓘(Real, E)) U (constTangentSection (E := E) (e i))) y))
        Set.univ := hsmooth.contMDiffOn
    simpa only [Integral.Connection.restrictOpenTangentSection_apply,
      constTangentSection] using hsec

/-- The fixed Euclidean metric used only to read constant-frame components on
normal-coordinate open subtypes. -/
private noncomputable def flatModelMetricB1 :
    SmoothRiemannianMetric 𝓘(Real, E) E where
  inner := (riemannianMetricVectorSpace E).inner
  symm := (riemannianMetricVectorSpace E).symm
  pos := (riemannianMetricVectorSpace E).pos
  isVonNBounded := (riemannianMetricVectorSpace E).isVonNBounded
  contMDiff := (riemannianMetricVectorSpace E).contMDiff.of_le le_top

omit [NeZero (Module.finrank Real E)] in
private theorem metric_norm_le_comp
    (V : TopologicalSpace.Opens E) [SigmaCompactSpace V] [T2Space V]
    (G g : SmoothRiemannianMetric 𝓘(Real, E) V) (a : Nat) (z : V)
    {B : Real} (hB : 0 ≤ B)
    (hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ g.inner z v v ∧
        g.inner z v v ≤ 2 * ‖v‖ ^ 2)
    (hcomp : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (M := V)
          (fun i _ ↦ (stdOrthonormalBasis Real E).toBasis i)
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Integral.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g)
            (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i)
            (constBasis_isLocalFrame_open V
              (stdOrthonormalBasis Real E).toBasis) y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
            (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i))
          a z slots| ≤ B) :
    metricDerivNorm (I := 𝓘(Real, E)) a G g g z ≤
      Real.sqrt (2 ^ (2 + a)) *
        (Real.sqrt
          (Fintype.card
            (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * B) := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let frame : Fin (Module.finrank Real E) →
      (y : V) → TangentSpace 𝓘(Real, E) y := fun i _ ↦ e i
  let hframe : IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      frame Set.univ := constBasis_isLocalFrame_open V e
  let g0 := (flatModelMetricB1 (E := E)).restrictOpen (I := 𝓘(Real, E)) V
  have hON0 : ∀ i j : Fin (Module.finrank Real E),
      g0.inner z (e i) (e j) = if i = j then (1 : Real) else 0 := by
    intro i j
    simpa only [g0, SmoothRiemannianMetric.restrictOpen_inner,
      flatModelMetricB1, riemannianMetricVectorSpace] using
        (stdOrthonormalBasis Real E).inner_eq_ite i j
  have hinv0 : Tensor0SBundle.MetricInverseInBasis_gen
      (I := 𝓘(Real, E)) g0 z e
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real E))) := by
    have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := 𝓘(Real, E)) g0 e hON0
    simpa [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric] using h
  have hequiv' : ∀ v : TangentSpace 𝓘(Real, E) z,
      (2 : Real)⁻¹ * g0.inner z v v ≤ g.inner z v v ∧
        g.inner z v v ≤ 2 * g0.inner z v v := by
    intro v
    change E at v
    have hg0 : g0.inner z v v = ‖v‖ ^ 2 := by
      simpa only [g0, SmoothRiemannianMetric.restrictOpen_inner,
        flatModelMetricB1, riemannianMetricVectorSpace] using
          real_inner_self_eq_norm_sq v
    rw [hg0]
    simpa only [one_div] using hequiv v
  obtain ⟨b, hbON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := 𝓘(Real, E)) g z
  have hbinv : Tensor0SBundle.MetricInverseInBasis_gen
      (I := 𝓘(Real, E)) g z b
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace 𝓘(Real, E) z)))) := by
    have h := DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
      (I := 𝓘(Real, E)) g b hbON
    simpa [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric] using h
  rw [metricDerivNorm_eq_iterCov (I := 𝓘(Real, E)) G g g a b hbinv]
  apply sqrt_norm_le_comp (I := 𝓘(Real, E)) g0 g z (2 + a) e hinv0
    (C := 2) (B := B) (by norm_num) hequiv' _ hB
  intro slots
  rw [Tensor0SBundle.component0S_apply]
  have ht := iterCovComp_eq_iterCov (I := 𝓘(Real, E)) g
    (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
      Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
    frame hframe isOpen_univ a (Set.mem_univ z) slots
  have ht' :
      iterCovComp (I := 𝓘(Real, E)) frame
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Integral.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g) frame hframe y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g) frame)
          a z slots =
        iterCov (I := 𝓘(Real, E)) g 2
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
          a z (fun q ↦ e (slots q)) := by
    simpa only [frameTuple, frame] using ht
  calc
    |iterCov (I := 𝓘(Real, E)) g 2
        (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
          Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g)
        a z (fun q ↦ e (slots q))| =
        |iterCovComp (I := 𝓘(Real, E)) frame
          (fun y ↦ Tensor.Coordinates.christoffelSymbolInFrame
            (Integral.Connection.leviCivitaConnectionOfMetric
              (I := 𝓘(Real, E)) g) frame hframe y)
          (frameComp0S (I := 𝓘(Real, E))
            (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) G -
              Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) g) frame)
          a z slots| := congrArg abs ht'.symm
    _ ≤ B := by simpa only [e, frame, hframe] using hcomp slots

private noncomputable def quarterPull
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
      normalQuarterImageSigma (I := I) Y x
    SmoothRiemannianMetric I Y.M →
      SmoothRiemannianMetric 𝓘(Real, E) (normalQuarter (I := I) Y x) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  intro G
  exact Diffeomorph.pullbackMetricCross
    (G.restrictOpen (I := I) (normalQuarterImage (I := I) Y x))
    (normalQuarterDiffeo (I := I) Y x)

private theorem quarterPull_inner
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
      normalQuarterImageSigma (I := I) Y x
    ∀ (G : SmoothRiemannianMetric I Y.M)
      (z : normalQuarter (I := I) Y x) (v w : E),
      (quarterPull (I := I) Y x G).inner z v w =
        G.inner (framedExpDiffeo (I := I) Y.metric x (z : E))
          (mfderiv 𝓘(Real, E) I
            (fun u : E ↦ framedExpDiffeo (I := I) Y.metric x u) (z : E) v)
          (mfderiv 𝓘(Real, E) I
            (fun u : E ↦ framedExpDiffeo (I := I) Y.metric x u) (z : E) w) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  intro G z v w
  rw [quarterPull, Diffeomorph.pullbackMetricCross_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  rw [quarterDiffeo_apply, quarterDiffeo_mfd, quarterDiffeo_mfd]

private theorem quarter_norm_eq
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
      normalQuarterImageSigma (I := I) Y x
    ∀ (G : SmoothRiemannianMetric I Y.M) (a : Nat)
      (z : normalQuarter (I := I) Y x),
      metricDerivNorm (I := 𝓘(Real, E)) a
          (quarterPull (I := I) Y x G)
          ((normalTotal (I := I) Y x).restrictOpen
            (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x))
          ((normalTotal (I := I) Y x).restrictOpen
            (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x)) z =
        metricDerivNorm (I := I) a G Y.metric Y.metric
          (framedExpDiffeo (I := I) Y.metric x (z : E)) := by
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  letI : SigmaCompactSpace (normalQuarterImage (I := I) Y x) :=
    normalQuarterImageSigma (I := I) Y x
  intro G a z
  rw [quarterPull, normalTotal_quarter (I := I) Y x]
  rw [metricDerivNorm_pullbackCross (I := 𝓘(Real, E)) (J := I)]
  rw [metricDerivNorm_restrictOpen (I := I) G Y.metric Y.metric]
  rw [quarterDiffeo_apply]

private theorem normal_christoffel
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    ∀ (V : TopologicalSpace.Opens E) [SigmaCompactSpace V] [T2Space V]
      (_hVQ : V ≤ normalQuarter (I := I) Y x)
      (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
      (z : V) (hco : IsCoercive (normalCoordMetric (I := I) Y x (z : E)))
      (i j m : Fin (Module.finrank Real E)),
      Tensor.Coordinates.christoffelSymbolInFrame
          (Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
            ((normalTotal (I := I) Y x).restrictOpen (I := 𝓘(Real, E)) V))
          (fun q (y : V) => (show TangentSpace 𝓘(Real, E) y from e q))
          (constBasis_isLocalFrame_open V e) z i j m =
        e.coord m
          (MetricKoszul.koszulVec hco
            (fderiv Real (normalCoordMetric (I := I) Y x) (z : E))
            (e i) (e j)) := by
  classical
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  dsimp only
  intro V _ _ hVQ e z hco i j m
  let frame : Fin (Module.finrank Real E) →
      (y : V) → TangentSpace 𝓘(Real, E) y := fun q _ => e q
  let hframe : IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      frame Set.univ := constBasis_isLocalFrame_open V e
  have hfield : Integral.Connection.restrictOpenTangentField
      (I := 𝓘(Real, E)) V
      (fun y : E => (constTangentSection (E := E) (e j)) y) =
        fun y : V => (show TangentSpace 𝓘(Real, E) y from e j) := by
    funext y
    simpa only [constTangentSection] using
      (Integral.Connection.restrictOpenTangentField_apply
        (I := 𝓘(Real, E)) V
        (fun y : E => (constTangentSection (E := E) (e j)) y) y)
  have hres := Integral.Connection.metricCov_restrictOpen_globalSection
    (I := 𝓘(Real, E)) (normalTotal (I := I) Y x) V
    (constTangentSection (E := E) (e j)) z (e i)
  rw [hfield] at hres
  have hres' :
      ((Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
          ((normalTotal (I := I) Y x).restrictOpen (I := 𝓘(Real, E)) V)
          (frame j) z) (e i)) =
        ((Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
          (normalTotal (I := I) Y x) (fun _ : E => e j) (z : E)) (e i)) := by
    simpa only [Integral.Connection.metricCov, frame, constTangentSection] using hres
  have hcov :
      ((Integral.Connection.leviCivitaConnectionOfMetric (I := 𝓘(Real, E))
          ((normalTotal (I := I) Y x).restrictOpen (I := 𝓘(Real, E)) V)
          (frame j) z) (frame i z)) =
        MetricKoszul.koszulVec hco
          (fderiv Real (normalCoordMetric (I := I) Y x) (z : E))
          (e i) (e j) := by
    rw [hres']
    exact normal_cov_eq (I := I) Y x (z : E) (hVQ z.2) hco (e i) (e j)
  have hbasis : hframe.toBasisAt (Set.mem_univ z) = e := by
    ext q
    simp only [IsLocalFrameOn.toBasisAt_coe, frame]
    rfl
  change hframe.coeff m z _ = _
  rw [hcov]
  simp only [IsLocalFrameOn.coeff, Set.mem_univ, dite_true, hbasis]
  rfl

private theorem stagePull_coeff
    (Yk Yl : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (ck : Yk.M) (cl : Yl.M) :
    letI : TopologicalSpace Yk.M := Yk.topology
    letI : ChartedSpace H Yk.M := Yk.charted
    letI : IsManifold I ∞ Yk.M := Yk.smooth
    letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
    letI : T2Space Yk.M := Yk.t2
    letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
    letI : TopologicalSpace Yl.M := Yl.topology
    letI : ChartedSpace H Yl.M := Yl.charted
    letI : IsManifold I ∞ Yl.M := Yl.smooth
    letI : T2Space Yl.M := Yl.t2
    letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Yk ck) :=
      normalQuarterSigma (I := I) Yk ck
    ∀ (F : Yk.M → Yl.M) (G : SmoothRiemannianMetric I Yk.M)
      (z : normalQuarter (I := I) Yk ck),
      F (framedExpDiffeo (I := I) Yk.metric ck (z : E)) ∈
          (framedChartAt (I := I) Yl.metric cl).source →
      MDifferentiableAt I I F
          (framedExpDiffeo (I := I) Yk.metric ck (z : E)) →
      (∀ v w : TangentSpace I
          (framedExpDiffeo (I := I) Yk.metric ck (z : E)),
        G.inner (framedExpDiffeo (I := I) Yk.metric ck (z : E)) v w =
          Yl.metric.inner
            (F (framedExpDiffeo (I := I) Yk.metric ck (z : E)))
            (mfderiv I I F
              (framedExpDiffeo (I := I) Yk.metric ck (z : E)) v)
            (mfderiv I I F
              (framedExpDiffeo (I := I) Yk.metric ck (z : E)) w)) →
      ∀ u v : E,
        let A : E → E := fun q =>
          framedChartAt (I := I) Yl.metric cl
            (F (framedExpDiffeo (I := I) Yk.metric ck q))
        (quarterPull (I := I) Yk ck G).inner z u v =
          _root_.DifferentialGeometry.HCGCompactness.pullbackForm
            (normalCoordMetric (I := I) Yl cl (A (z : E)),
              fderiv Real A (z : E)) u v := by
  classical
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Yk ck) :=
    normalQuarterSigma (I := I) Yk ck
  intro F G z htarget hF hG u v
  dsimp only
  let eK := framedExpDiffeo (I := I) Yk.metric ck
  let eL := framedExpDiffeo (I := I) Yl.metric cl
  let chiL := framedChartAt (I := I) Yl.metric cl
  let A : E → E := fun q => chiL (F (eK q))
  have hzBall : (z : E) ∈ normalBall (I := I) Yk ck :=
    normalInner_sub (I := I) Yk ck z.2
  have hzNorm : ‖(z : E)‖ < expRadiusGp (I := I) Yk.metric ck := by
    change (z : E) ∈ Metric.ball (0 : E) (expRadiusGp (I := I) Yk.metric ck) at hzBall
    rw [Metric.mem_ball, dist_zero_right] at hzBall
    exact hzBall
  have hzK : (z : E) ∈ eK.source := by
    change (z : E) ∈ (framedExpDiffeo (I := I) Yk.metric ck).source
    rw [framedExp_source]
    apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
    apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
    simpa only [normalFrame_sqrt] using hzNorm
  have hK : MDifferentiableAt 𝓘(Real, E) I (eK : E → Yk.M) (z : E) :=
    ((eK.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ hzK).mdifferentiableAt
      (eK.open_source.mem_nhds hzK))
  have hFK : MDifferentiableAt 𝓘(Real, E) I (F ∘ eK) (z : E) :=
    hF.comp (z : E) hK
  have hchi : MDifferentiableAt I 𝓘(Real, E) chiL (F (eK (z : E))) :=
    ((chiL.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ htarget).mdifferentiableAt
      (chiL.open_source.mem_nhds htarget))
  have hA : MDifferentiableAt 𝓘(Real, E) 𝓘(Real, E) A (z : E) := by
    simpa only [A, Function.comp_apply] using hchi.comp (z : E) hFK
  have hzL : A (z : E) ∈ eL.source := by
    change chiL (F (eK (z : E))) ∈ chiL.target
    exact chiL.map_source htarget
  have hL : MDifferentiableAt 𝓘(Real, E) I (eL : E → Yl.M) (A (z : E)) :=
    ((eL.contMDiffOn_toFun.mdifferentiableOn one_ne_zero _ hzL).mdifferentiableAt
      (eL.open_source.mem_nhds hzL))
  have hnear : ∀ᶠ q in nhds (z : E), F (eK q) ∈ chiL.source :=
    hFK.continuousAt.eventually (chiL.open_source.mem_nhds htarget)
  have heq : eL ∘ A =ᶠ[nhds (z : E)] F ∘ eK := by
    filter_upwards [hnear] with q hq
    change chiL.symm (chiL (F (eK q))) = F (eK q)
    exact chiL.left_inv hq
  have hcomp :
      (mfderiv 𝓘(Real, E) I eL (A (z : E))).comp
          (fderiv Real A (z : E)) =
        (mfderiv I I F (eK (z : E))).comp
          (mfderiv 𝓘(Real, E) I eK (z : E)) := by
    have hderiv := Filter.EventuallyEq.mfderiv_eq
      (I := 𝓘(Real, E)) (I' := I) heq
    rw [mfderiv_comp (z : E) hL hA, mfderiv_comp (z : E) hF hK] at hderiv
    rw [mfderiv_eq_fderiv] at hderiv
    simpa only [A] using hderiv
  have hbase : eL (A (z : E)) = F (eK (z : E)) := heq.self_of_nhds
  have hu := DFunLike.congr_fun hcomp u
  have hv := DFunLike.congr_fun hcomp v
  rw [quarterPull_inner (I := I) Yk ck G z u v]
  rw [hG]
  rw [_root_.DifferentialGeometry.HCGCompactness.pullbackForm_apply]
  rw [normalCoordMetric_apply (I := I), hbase]
  exact congrArg₂
    (fun a b => Yl.metric.inner (F (eK (z : E))) a b) hu.symm hv.symm

private theorem local_norm_le
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (x : Y.M) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : SigmaCompactSpace Y.M := Y.sigmaCompact
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
      normalQuarterSigma (I := I) Y x
    ∀ (V : TopologicalSpace.Opens E) [SigmaCompactSpace V] [T2Space V]
      (hVQ : V ≤ normalQuarter (I := I) Y x)
      (G : SmoothRiemannianMetric I Y.M)
      (Q : E → (E →L[Real] E →L[Real] Real))
      (a : Nat) (z : V) {bnd : Real},
      0 ≤ bnd →
      (∀ w : V, ∀ u v : E,
        (quarterPull (I := I) Y x G).inner
            (TopologicalSpace.Opens.inclusion hVQ w) u v =
          Q (w : E) u v) →
      (∀ w : E, w ∈ V →
        IsCoercive (normalCoordMetric (I := I) Y x w)) →
      (∀ v : E,
        (1 / 2 : Real) * ‖v‖ ^ 2 ≤
            normalCoordMetric (I := I) Y x (z : E) v v ∧
          normalCoordMetric (I := I) Y x (z : E) v v ≤
            2 * ‖v‖ ^ 2) →
      (let e := (stdOrthonormalBasis Real E).toBasis
       let B := normalCoordMetric (I := I) Y x
       let Gamma := fun w i j m ↦ e.coord m
         (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
           (e i) (e j))
       let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
         (Q w - B w) (e (slots 0)) (e (slots 1))
       ∀ q : Nat, ∀ w : V,
         ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
           MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
             (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
               (fun i _ ↦ e i) Gamma base q y slots) (w : E)) →
      (let e := (stdOrthonormalBasis Real E).toBasis
       let B := normalCoordMetric (I := I) Y x
       let Gamma := fun w i j m ↦ e.coord m
         (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
           (e i) (e j))
       let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
         (Q w - B w) (e (slots 0)) (e (slots 1))
       ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
         |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
            Gamma base a (z : E) slots| ≤ bnd) →
      metricDerivNorm (I := 𝓘(Real, E)) a
          ((quarterPull (I := I) Y x G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVQ)
          (((normalTotal (I := I) Y x).restrictOpen
            (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x)).restrictOpenOfSubset
              (I := 𝓘(Real, E)) hVQ)
          (((normalTotal (I := I) Y x).restrictOpen
            (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x)).restrictOpenOfSubset
              (I := 𝓘(Real, E)) hVQ) z ≤
        Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * bnd) := by
  classical
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : SigmaCompactSpace Y.M := Y.sigmaCompact
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  letI : SigmaCompactSpace (normalQuarter (I := I) Y x) :=
    normalQuarterSigma (I := I) Y x
  intro V _ _ hVQ G Q a z bnd hbnd hQ hco hequiv hdiff hcomp
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let B := normalCoordMetric (I := I) Y x
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w) (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - B w) (e (slots 0)) (e (slots 1))
  let GQ := quarterPull (I := I) Y x G
  let gQ := (normalTotal (I := I) Y x).restrictOpen
    (I := 𝓘(Real, E)) (normalQuarter (I := I) Y x)
  let Gv := GQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ
  let gv := gQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ
  have hgv : gv = (normalTotal (I := I) Y x).restrictOpen
      (I := 𝓘(Real, E)) V := by
    simp only [gv, gQ, SmoothRiemannianMetric.restrictOpen_flat]
  have hequivV : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gv.inner z v v ∧
        gv.inner z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    rw [hgv, SmoothRiemannianMetric.restrictOpen_inner,
      normalTotal_inner (I := I) Y x (z : E) (hVQ z.2) v v]
    exact hequiv v
  apply metric_norm_le_comp V Gv gv a z hbnd hequivV
  intro slots
  let frame : Fin (Module.finrank Real E) →
      (w : V) → TangentSpace 𝓘(Real, E) w := fun i _ ↦ e i
  let hframe : IsLocalFrameOn 𝓘(Real, E) E (1 : WithTop ℕ∞)
      frame Set.univ := constBasis_isLocalFrame_open V e
  have hchrEq :
      (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
        (Integral.Connection.leviCivitaConnectionOfMetric
          (I := 𝓘(Real, E)) gv) frame hframe w) =
        fun (w : V) ↦ Gamma (w : E) := by
    funext w i j m
    rw [hgv]
    have hnormal := normal_christoffel (I := I) Y x V hVQ e w
      (hco (w : E) w.2) i j m
    rw [hnormal]
    exact congrArg (e.coord m)
      (MetricKoszul.raisedKoszulOp_eq (hco (w : E) w.2)
        (fderiv Real B (w : E)) (e i) (e j)).symm
  have hbaseEq :
      frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv) frame =
        fun (w : V) ↦ base (w : E) := by
    funext w s
    change Gv.inner w (e (s 0)) (e (s 1)) -
        gv.inner w (e (s 0)) (e (s 1)) =
      (Q (w : E) - B (w : E)) (e (s 0)) (e (s 1))
    rw [show Gv.inner w (e (s 0)) (e (s 1)) =
        Q (w : E) (e (s 0)) (e (s 1)) by
      exact hQ w (e (s 0)) (e (s 1))]
    rw [hgv, SmoothRiemannianMetric.restrictOpen_inner,
      normalTotal_inner (I := I) Y x (w : E) (hVQ w.2)
        (e (s 0)) (e (s 1))]
    rfl
  have hres := DifferentialGeometry.PDE.RicciFlow.iterCovComp_restrict
    V (fun i ↦ e i) Gamma base hdiff a z slots
  calc
    |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ (stdOrthonormalBasis Real E).toBasis i)
        (fun w ↦ Tensor.Coordinates.christoffelSymbolInFrame
          (Integral.Connection.leviCivitaConnectionOfMetric
            (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i)
          (constBasis_isLocalFrame_open V
            (stdOrthonormalBasis Real E).toBasis) w)
        (frameComp0S (I := 𝓘(Real, E))
          (Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) Gv -
            Tensor0SBundle.metricTensorField (I := 𝓘(Real, E)) gv)
          (fun i (_ : V) ↦ (stdOrthonormalBasis Real E).toBasis i))
        a z slots| =
      |iterCovComp (I := 𝓘(Real, E)) (M := V)
        (fun i _ ↦ e i) (fun w ↦ Gamma (w : E))
        (fun w ↦ base (w : E)) a z slots| := by
          simp only [e, frame, hchrEq, hbaseEq]
    _ = |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
        Gamma base a (z : E) slots| := congrArg abs hres
    _ ≤ bnd := by simpa only [e, B, Gamma, base] using hcomp slots

omit [NeZero (Module.finrank Real E)] in
omit [NeZero (Module.finrank Real E)] in
/-- Smooth coefficient fields make every level of their metric covariant
component tower differentiable on the same open coordinate buffer. -/
private theorem metricTower_mdiff
    (V : TopologicalSpace.Opens E)
    (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (B Q : E → (E →L[Real] E →L[Real] Real))
    (hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) B V)
    (hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V)
    (hBco : ∀ z : E, z ∈ V → IsCoercive (B z)) :
    let Gamma := fun z i j m ↦ e.coord m
      (MetricKoszul.raisedKoszulOp (B z) (fderiv Real B z)
        (e i) (e j))
    let base := fun z (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
      (Q z - B z) (e (slots 0)) (e (slots 1))
    ∀ q : Nat, ∀ z : V,
      ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q y slots) (z : E) := by
  dsimp only
  let raised : E → E →L[Real] E →L[Real] E := fun z =>
    MetricKoszul.raisedKoszulOp (B z) (fderiv Real B z)
  have hraised : ContDiffOn Real (∞ : WithTop ℕ∞) raised V := by
    simpa only [raised] using MetricKoszul.raisedOp_smooth V.2 hBcd hBco
  have hchr : ∀ d i j : Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (fun z => e.coord j (raised z (e d) (e i))) V := by
    intro d i j
    rw [contMDiffOn_iff_contDiffOn]
    exact (e.coord j).toContinuousLinearMap.contDiff.comp_contDiffOn
      ((hraised.clm_apply contDiffOn_const).clm_apply contDiffOn_const)
  have hbase : ∀ slots : Fin 2 → Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) 𝓘(Real, Real) ∞
        (fun z => (Q z - B z) (e (slots 0)) (e (slots 1))) V := by
    intro slots
    rw [contMDiffOn_iff_contDiffOn]
    exact ((hQcd.sub hBcd).clm_apply contDiffOn_const).clm_apply contDiffOn_const
  have hframe : ∀ d : Fin (Module.finrank Real E),
      ContMDiffOn 𝓘(Real, E) (𝓘(Real, E).prod 𝓘(Real, E)) ∞
        (fun (y : E) => TotalSpace.mk' E (E := TangentSpace 𝓘(Real, E)) y
          (show TangentSpace 𝓘(Real, E) y from e d)) V := by
    intro d
    simpa only [constTangentSection] using
      (constTangentSection (E := E) (e d)).contMDiff_toFun.contMDiffOn
  intro q z slots
  exact DifferentialGeometry.PDE.RicciFlow.iterCovComp_mdiffAt V.2
    (fun i (_ : E) ↦ e i)
    (fun z i j m => e.coord m (raised z (e i) (e j)))
    (fun z s => (Q z - B z) (e (s 0)) (e (s 1)))
    hframe hchr hbase z.2 q slots

/-- On a smaller source ball, one rectangular pair-index tail controls every
component of every finite covariant-derivative tower of the actual pullback
metric error, in a chart supplied by the finite buffered source cover. -/
theorem HasStageJetData.cov_comp_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {R S : Real} (hRS : R < S) (hSr : S < r)
    (e : Module.Basis (Fin (Module.finrank Real E)) Real E)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    let Lphi := L.subseq hphi
    let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
      fun alpha k l z =>
        let Yk := X.obj (Lphi.φ k)
        let Yl := X.obj (Lphi.φ l)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
          (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
        chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
    let B : LiveSlot L inp.pack r → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
      normalCoordMetric (I := I) (X.obj (Lphi.φ k))
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
    let Q : LiveSlot L inp.pack r → Nat → Nat →
        E → (E →L[Real] E →L[Real] Real) := fun alpha k l z =>
      _root_.DifferentialGeometry.HCGCompactness.pullbackForm
        (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
    let Gamma : LiveSlot L inp.pack r → Nat → E →
        Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
          Fin (Module.finrank Real E) → Real := fun alpha k z i j m =>
      e.coord m
        (MetricKoszul.raisedKoszulOp
          (B alpha k z) (fderiv Real (B alpha k) z)
          (e i) (e j))
    let tower : (alpha : LiveSlot L inp.pack r) →
        (k l a : Nat) → E →
          (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
      fun alpha k l a =>
        iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i) (Gamma alpha k)
          (fun z slots => (Q alpha k l z - B alpha k z)
            (e (slots 0)) (e (slots 1))) a
    ∃ eta : LiveSlot L inp.pack r → Real,
      (∀ alpha, 0 < eta alpha) ∧
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
          ∃ (alpha : LiveSlot L inp.pack r) (z : E),
            (NormalCoordinates.framedChartAt (I := I) Yk.metric
              (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))).symm z = y ∧
            Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) ∧
            ∀ a ≤ p, ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
              |tower alpha k l a z slots| < eps := by
  classical
  letI : NormedAddCommGroup (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  letI : NormedAddCommGroup (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace Real (E →L[Real] E →L[Real] Real) :=
    ContinuousLinearMap.toNormedSpace
  dsimp only
  let Lphi := L.subseq hphi
  let A : LiveSlot L inp.pack r → Nat → Nat → E → E :=
    fun alpha k l z =>
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
        (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
      let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric
        (seqCenterD inp.decay P Lphi l (alpha.1 : Nat))
      chiL (stageComparisonMap inp P Lphi r hr hconn k l (chiK.symm z))
  let B : LiveSlot L inp.pack r → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k =>
    normalCoordMetric (I := I) (X.obj (Lphi.φ k))
      (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  let Q : LiveSlot L inp.pack r → Nat → Nat →
      E → (E →L[Real] E →L[Real] Real) := fun alpha k l z =>
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (B alpha l (A alpha k l z), fderiv Real (A alpha k l) z)
  let Gamma : LiveSlot L inp.pack r → Nat → E →
      Fin (Module.finrank Real E) → Fin (Module.finrank Real E) →
        Fin (Module.finrank Real E) → Real := fun alpha k z i j m =>
    e.coord m
      (MetricKoszul.raisedKoszulOp
        (B alpha k z) (fderiv Real (B alpha k) z)
        (e i) (e j))
  let tower : (alpha : LiveSlot L inp.pack r) →
      (k l a : Nat) → E →
        (Fin (2 + a) → Fin (Module.finrank Real E)) → Real :=
    fun alpha k l a =>
      iterCovComp (I := 𝓘(Real, E))
        (fun i _ => e i) (Gamma alpha k)
        (fun z slots => (Q alpha k l z - B alpha k z)
          (e (slots 0)) (e (slots 1))) a
  rcases hstage with ⟨hdata, hmetric, hjets, hbase⟩
  obtain ⟨eta, heta, hcover⟩ :=
    hdata.buffer_cover inp P L r hr U C0 C1 aInf Jinf Jbarinf
  have hlocal : ∀ (alpha : LiveSlot L inp.pack r) (a : Fin (p + 1)),
      ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N, ∀ z : E,
        Metric.closedBall z (eta alpha) ⊆ interior (C0 alpha) →
        let Yk := X.obj (Lphi.φ k)
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
        chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k →
          ∀ slots : Fin (2 + (a : Nat)) → Fin (Module.finrank Real E),
            |tower alpha k l a z slots| < eps := by
    intro alpha a
    obtain ⟨hUopen, hC0compact, _hC1compact, hC01, hC1U⟩ :=
      hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
    have hIntU : interior (C0 alpha) ⊆ U alpha :=
      interior_subset.trans (hC01.trans (interior_subset.trans hC1U))
    by_contra htail
    push Not at htail
    choose k hk l hl z hbuffer hrest using htail
    have hrest' : ∀ n,
        let Yk := X.obj (Lphi.φ (k n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
        chiK.symm (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) ∧
          ∃ slots : Fin (2 + (a : Nat)) → Fin (Module.finrank Real E),
            eps ≤ |tower alpha (k n) (l n) a (z n) slots| := by
      intro n
      have hn := hrest n
      dsimp only at hn ⊢
      push Not at hn
      exact hn
    have hsource : ∀ n,
        let Yk := X.obj (Lphi.φ (k n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (k n))).ms
        let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (k n) (alpha.1 : Nat))
        chiK.symm (z n) ∈ Lphi.hatSourceBall inp.decay P R (k n) :=
      fun n => (hrest' n).1
    choose slots hbad using fun n => (hrest' n).2
    have hzC0 : ∀ n, z n ∈ C0 alpha := by
      intro n
      exact interior_subset (hbuffer n
        (Metric.mem_closedBall_self (heta alpha).le))
    obtain ⟨zInf, _hzInf, ψ, hψ, hzconv⟩ :=
      hC0compact.tendsto_subseq hzC0
    let kn : Nat → Nat := fun n => k (ψ n)
    let ln : Nat → Nat := fun n => l (ψ n)
    let zn : Nat → E := fun n => z (ψ n)
    let slotn : Nat → (Fin (2 + (a : Nat)) → Fin (Module.finrank Real E)) :=
      fun n => slots (ψ n)
    have hkn : Tendsto kn atTop atTop :=
      (tendsto_atTop_mono hk tendsto_id).comp hψ.tendsto_atTop
    have hln : Tendsto ln atTop atTop :=
      (tendsto_atTop_mono hl tendsto_id).comp hψ.tendsto_atTop
    have hzn : Tendsto zn atTop (𝓝 zInf) := by
      simpa only [zn] using hzconv
    have hbuffer' : ∀ n, Metric.closedBall (zn n) (eta alpha) ⊆
        interior (C0 alpha) := fun n => hbuffer (ψ n)
    have hsource' : ∀ n,
        let Yk := X.obj (Lphi.φ (kn n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
        (NormalCoordinates.framedChartAt (I := I) Yk.metric
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm (zn n) ∈
            Lphi.hatSourceBall inp.decay P R (kn n) := by
      intro n
      simpa only [kn, zn, Lphi] using hsource (ψ n)
    obtain ⟨q, hq, hVopen, hVcompact, hVW, hWint, hstay⟩ :=
      hdata.source_stay inp P L hr phi hphi U C0 C1 aInf Jinf Jbarinf
        alpha hRS (heta alpha) kn zn zInf hzn hbuffer' hsource'
    let V : Set E := Metric.ball zInf q
    let W : Set E := Metric.ball zInf (2 * q)
    have hstay' : ∀ᶠ n in atTop,
        let Yk := X.obj (Lphi.φ (kn n))
        letI : TopologicalSpace Yk.M := Yk.topology
        letI : ChartedSpace H Yk.M := Yk.charted
        letI : IsManifold I ∞ Yk.M := Yk.smooth
        letI : T2Space Yk.M := Yk.t2
        letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
        letI : MetricSpace Yk.M := (P (Lphi.φ (kn n))).ms
        Set.MapsTo
          (NormalCoordinates.framedChartAt (I := I) Yk.metric
            (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).symm
          W (Lphi.hatSourceBall inp.decay P S (kn n)) := by
      simpa only [V, W, Lphi] using hstay
    have hQconv : MapCInfConvOnCompacts V
        (fun n => Q alpha (kn n) (ln n)) (gInf alpha) := by
      simpa only [V, W, Q, B, A, Lphi] using
        HasStageJetData.pb_conv (I := I) inp P L hr phi hphi hconn
          U C0 C1 aInf Jinf Jbarinf gInf
          ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha V W hVopen hVcompact
          hVW hWint kn ln hkn hln hstay'
    let Ralpha : Real := L.rInf (alpha.1 : Nat) + 1
    let D : Set E := Metric.ball (0 : E) (inp.normalRadius.phaseRadius Ralpha)
    obtain ⟨hC1D, hgInf, hBconv, hgEquiv⟩ := hmetric alpha
    have hWD : W ⊆ D := by
      intro z hz
      exact hC1D (interior_subset (hC01 (interior_subset (hWint hz))))
    have hVD : V ⊆ D := subset_closure.trans (hVW.trans hWD)
    have hclosureD : closure V ⊆ D := hVW.trans hWD
    have hVU : V ⊆ U alpha := by
      intro z hz
      exact hIntU (hWint (hVW (subset_closure hz)))
    have hGconvD : MapCInfConvOnCompacts D
        (fun n => B alpha (kn n)) (gInf alpha) := by
      simpa only [D, Ralpha, B, Lphi] using hBconv.comp_tendsto_atTop hkn
    have hGconvV : MapCInfConvOnCompacts V
        (fun n => B alpha (kn n)) (gInf alpha) := by
      intro K hK hKV p'
      exact hGconvD K hK (hKV.trans hVD) p'
    have hBcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞)
        (B alpha (kn n)) V := by
      intro n
      have hgeomK := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf
        (kn n) alpha
      simpa only [B, Lphi] using
        (normalCoordMetric_contDiffOn_expBall (I := I)
          (X.obj (Lphi.φ (kn n)))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat))).mono
            (hVU.trans hgeomK.2.1)
    have hBco : ∀ n z, z ∈ V → IsCoercive (B alpha (kn n) z) := by
      intro n z hz
      have hgeomK := hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf
        (kn n) alpha
      have hEquiv : NormalCoordMetricEquivOn (I := I)
          (X.obj (Lphi.φ (kn n)))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)) (U alpha) := by
        intro w hw v
        exact inp.normalBounds.metric_equiv (Lphi.φ (kn n))
          (seqCenterD inp.decay P Lphi (kn n) (alpha.1 : Nat)) w
          (hgeomK.1 hw) v
      simpa only [B, Lphi] using hEquiv.coercive (hVU hz)
    have hgInfV : ContDiffOn Real (∞ : WithTop ℕ∞) (gInf alpha) V :=
      hgInf.mono hVD
    have hgInfCo : ∀ z, z ∈ V → IsCoercive (gInf alpha z) := by
      intro z hz
      refine ⟨1 / 2, by norm_num, ?_⟩
      intro v
      simpa only [pow_two, mul_assoc] using (hgEquiv z (hVD hz) v).1
    obtain ⟨rho, hrho, hthick⟩ :=
      hVcompact.exists_cthickening_subset_open Metric.isOpen_ball hclosureD
    have hAconvW : MapCInfConvOnCompacts W
        (fun n => A alpha (kn n) (ln n)) id := by
      simpa only [A, Lphi] using
        HasStageJetData.chart_conv (I := I) inp P L hr phi hphi hconn
          U C0 C1 aInf Jinf Jbarinf gInf
          ⟨hdata, hmetric, hjets, hbase⟩ S hSr alpha W hWint
          kn ln hkn hln hstay'
    obtain ⟨Nclose, hNclose⟩ :=
      hAconvW (closure V) hVcompact hVW 0 (rho / 2) (by positivity)
    obtain ⟨Njet, hNjet⟩ := hjets S hSr 0 1 (by norm_num)
    have hcenters : ∀ᶠ n in atTop,
        inp.decay.dist (Lphi.φ (ln n))
          (seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat))
          (X.obj (Lphi.φ (ln n))).basepoint < Ralpha := by
      have hall := liveCenters_rInf inp.decay P inp.realizes Lphi inp.pack r
      filter_upwards [hln.eventually hall] with n hn
      simpa only [Ralpha, Lphi, NetLimitData.subseq] using hn alpha
    have hgood : ∀ᶠ n in atTop,
        ContDiffOn Real (∞ : WithTop ℕ∞) (A alpha (kn n) (ln n)) V ∧
        Set.MapsTo (A alpha (kn n) (ln n)) V D ∧
        ContDiffOn Real (∞ : WithTop ℕ∞) (B alpha (ln n)) D := by
      filter_upwards [hkn.eventually_ge_atTop Njet,
        hln.eventually_ge_atTop Njet, hstay', hcenters,
        eventually_atTop.2 ⟨Nclose, hNclose⟩] with n hnk hnl hsrc hcenter hclose
      have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
          (A alpha (kn n) (ln n)) V := by
        intro z hzV
        have hzW : z ∈ W := hVW (subset_closure hzV)
        have hzInt : z ∈ interior (C0 alpha) := hWint hzW
        have hjet := hNjet (kn n) hnk (ln n) hnl alpha z
          (interior_subset hzInt)
        have hsrcz := hsrc hzW
        simpa only [A, Lphi] using (hjet hzInt hsrcz).2.1.contDiffWithinAt
      have hAmap : Set.MapsTo (A alpha (kn n) (ln n)) V D := by
        intro z hzV
        have hzClosure : z ∈ closure V := subset_closure hzV
        have hzero := hclose 0 le_rfl z hzClosure
        have hdist : dist (A alpha (kn n) (ln n) z) z ≤ rho / 2 := by
          simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
            dist_eq_norm, A, Lphi] using hzero
        have hdistRho : dist (A alpha (kn n) (ln n) z) z < rho := by
          linarith
        exact hthick (Metric.mem_cthickening_of_dist_le
          (A alpha (kn n) (ln n) z) z rho (closure V) hzClosure hdistRho.le)
      have hBtarget : ContDiffOn Real (∞ : WithTop ℕ∞)
          (B alpha (ln n)) D := by
        let Yl := X.obj (Lphi.φ (ln n))
        letI : TopologicalSpace Yl.M := Yl.topology
        letI : ChartedSpace H Yl.M := Yl.charted
        letI : IsManifold I ∞ Yl.M := Yl.smooth
        letI : T2Space Yl.M := Yl.t2
        letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
        let cl := seqCenterD inp.decay P Lphi (ln n) (alpha.1 : Nat)
        have hquarter := inp.normalRadius.phaseRadius_exp hcenter.le
        have hDexp : D ⊆ Metric.ball (0 : E)
            (expRadiusGp (I := I) Yl.metric cl) := by
          have hquarter' : D ⊆ Metric.ball (0 : E)
              (expRadiusGp (I := I) Yl.metric cl / 4) := by
            simpa only [D, Ralpha, Yl, cl, Lphi] using hquarter
          exact hquarter'.trans (Metric.ball_subset_ball (by
            nlinarith [expRadiusGp_pos (I := I) Yl.metric cl]))
        simpa only [B, Yl, cl, Lphi] using
          (normalCoordMetric_contDiffOn_expBall (I := I) Yl cl).mono hDexp
      exact ⟨hAcd, hAmap, hBtarget⟩
    obtain ⟨Nsm, hNsm⟩ := eventually_atTop.mp hgood
    have hQsmooth : ∀ n, Nsm ≤ n →
        ContDiffOn Real (∞ : WithTop ℕ∞) (Q alpha (kn n) (ln n)) V := by
      intro n hn
      have hBAc : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun z => B alpha (ln n) (A alpha (kn n) (ln n) z)) V := by
        simpa only [Function.comp_def] using
          ContDiffOn.comp (hNsm n hn).2.2 (hNsm n hn).1 (hNsm n hn).2.1
      have hDAc : ContDiffOn Real (∞ : WithTop ℕ∞)
          (fun z => fderiv Real (A alpha (kn n) (ln n)) z) V := by
        intro z hz
        exact ((((hNsm n hn).1).contDiffAt (hVopen.mem_nhds hz)).fderiv_right
          (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt
      have hpull := (_root_.DifferentialGeometry.HCGCompactness.pullbackForm.contDiff
        (E := E) (F := E)).comp_contDiffOn (hBAc.prodMk hDAc)
      simpa only [Q] using hpull
    let Qp : Nat → E → (E →L[Real] E →L[Real] Real) := fun n =>
      if Nsm ≤ n then Q alpha (kn n) (ln n) else gInf alpha
    have hQpconv : MapCInfConvOnCompacts V Qp (gInf alpha) := by
      apply hQconv.congr_eventually hVopen
      · filter_upwards [eventually_atTop.2 ⟨Nsm, fun n hn => hn⟩] with n hn
        intro z _hz
        simp only [Qp, if_pos hn]
      · exact Set.eqOn_refl (gInf alpha) V
    have hQpcd : ∀ n, ContDiffOn Real (∞ : WithTop ℕ∞) (Qp n) V := by
      intro n
      by_cases hn : Nsm ≤ n
      · simpa only [Qp, if_pos hn] using hQsmooth n hn
      · simpa only [Qp, if_neg hn] using hgInfV
    have htower := metric_tower_conv hVopen e
      (fun n => B alpha (kn n)) Qp (gInf alpha)
      hGconvV hQpconv hBcd hQpcd hgInfV hBco hgInfCo (a : Nat)
    let K : Set E := Metric.closedBall zInf (q / 2)
    have hKcompact : IsCompact K := isCompact_closedBall zInf (q / 2)
    have hKV : K ⊆ V := Metric.closedBall_subset_ball (by linarith)
    obtain ⟨Ntower, hNtower⟩ :=
      htower K hKcompact hKV 0 (eps / 2) (by positivity)
    obtain ⟨Nz, hNz⟩ := Metric.tendsto_atTop.1 hzn (q / 2) (by positivity)
    let n := max (max Ntower Nz) Nsm
    have hnTower : Ntower ≤ n := (le_max_left Ntower Nz).trans (le_max_left _ _)
    have hnZ : Nz ≤ n := (le_max_right Ntower Nz).trans (le_max_left _ _)
    have hnSm : Nsm ≤ n := le_max_right _ _
    have hznK : zn n ∈ K := by
      change dist (zn n) zInf ≤ q / 2
      exact (hNz n hnZ).le
    have hnorm :
        ‖iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun z i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (kn n) z) (fderiv Real (B alpha (kn n)) z)
                (e i) (e j)))
          (fun z (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n z - B alpha (kn n) z)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (zn n)‖ ≤ eps / 2 := by
      have hraw := hNtower n hnTower 0 le_rfl (zn n) hznK
      simp only [mapDerivNorm, norm_iteratedFDeriv_zero] at hraw
      rw [show (fun _ : Fin (2 + (a : Nat)) →
        Fin (Module.finrank Real E) => (0 : Real)) = 0 by rfl, sub_zero] at hraw
      exact hraw
    have hcomponent :
        ‖tower alpha (kn n) (ln n) a (zn n) (slotn n)‖ ≤ eps / 2 := by
      have hpi := (norm_le_pi_norm
        (iterCovComp (I := 𝓘(Real, E))
          (fun i _ => e i)
          (fun z i j m =>
            e.coord m
              (MetricKoszul.raisedKoszulOp
                (B alpha (kn n) z) (fderiv Real (B alpha (kn n)) z)
                (e i) (e j)))
          (fun z (slots : Fin 2 → Fin (Module.finrank Real E)) =>
            (Qp n z - B alpha (kn n) z)
            (e (slots 0)) (e (slots 1)))
          (a : Nat) (zn n)) (slotn n)).trans hnorm
      simpa only [Qp, if_pos hnSm, tower, Gamma] using hpi
    have hsmall :
        |tower alpha (kn n) (ln n) a (zn n) (slotn n)| < eps := by
      have habs : |tower alpha (kn n) (ln n) a (zn n) (slotn n)| ≤ eps / 2 := by
        simpa only [Real.norm_eq_abs] using hcomponent
      linarith
    have hbadn := hbad (ψ n)
    have hbadn' : eps ≤
        |tower alpha (kn n) (ln n) a (zn n) (slotn n)| := by
      simpa only [kn, ln, zn, slotn] using hbadn
    exact (not_lt_of_ge hbadn') hsmall
  choose Naa hNaa using hlocal
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  let Nalpha : LiveSlot L inp.pack r → Nat := fun alpha =>
    Finset.univ.sup (fun a : Fin (p + 1) => Naa alpha a)
  refine ⟨eta, heta, Finset.univ.sup Nalpha, ?_⟩
  intro k hk l hl
  let Yk := X.obj (Lphi.φ k)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  intro y hy
  have hyBig : y ∈ Lphi.hatSourceBall inp.decay P r k :=
    cball_subset_of_le (hRS.trans hSr).le hy
  obtain ⟨alpha, z, hzy, hzbuffer⟩ := hcover k y hyBig
  let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric
    (seqCenterD inp.decay P Lphi k (alpha.1 : Nat))
  have hzy' : chiK.symm z = y := by
    simpa only [chiK, Yk, Lphi] using hzy
  have hzSource : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P R k := by
    simpa only [hzy'] using hy
  have hAlpha : Nalpha alpha ≤ Finset.univ.sup Nalpha :=
    Finset.le_sup (f := Nalpha) (Finset.mem_univ alpha)
  have hkAlpha : Nalpha alpha ≤ k := hAlpha.trans hk
  have hlAlpha : Nalpha alpha ≤ l := hAlpha.trans hl
  refine ⟨alpha, z, hzy', hzbuffer, ?_⟩
  intro a ha slots
  let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
  have hAfin : Naa alpha afin ≤ Nalpha alpha :=
    Finset.le_sup (f := fun b : Fin (p + 1) => Naa alpha b)
      (Finset.mem_univ afin)
  have hkAfin : Naa alpha afin ≤ k := hAfin.trans hkAlpha
  have hlAfin : Naa alpha afin ≤ l := hAfin.trans hlAlpha
  simpa only [chiK, Yk, Lphi, afin] using
    hNaa alpha afin k hkAfin l hlAfin z hzbuffer hzSource slots

/-- A pair-local smooth realization of the actual pullback metric on a larger
source collar has uniformly small intrinsic metric-difference seminorms on
every strictly smaller retained source ball. -/
theorem HasStageJetData.fwd_norm_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {R S : Real} (hRS : R < S) (hSr : S < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      let F := stageComparisonMap inp P Lphi r hr hconn k l
      ∀ (G : SmoothRiemannianMetric I Yk.M),
        (∀ y ∈ Lphi.hatSourceBall inp.decay P S k,
          ∀ v w : TangentSpace I y,
            G.inner y v w =
              Yl.metric.inner (F y) (mfderiv I I F y v)
                (mfderiv I I F y w)) →
        ∀ a ≤ p, ∀ y ∈ Lphi.hatSourceBall inp.decay P R k,
          metricDerivNorm (I := I) a G Yk.metric Yk.metric y ≤ eps := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let fac : Fin (p + 1) → Real := fun a ↦
    Real.sqrt (2 ^ (2 + (a : Nat))) *
      Real.sqrt
        (Fintype.card
          (Fin (2 + (a : Nat)) → Fin (Module.finrank Real E)) : Real)
  let Cmax : Real := Finset.univ.sup' Finset.univ_nonempty fac
  have hfac_nonneg : ∀ a, 0 ≤ fac a := by
    intro a
    dsimp only [fac]
    positivity
  have hfac_le : ∀ a, fac a ≤ Cmax := by
    intro a
    exact Finset.le_sup' fac (Finset.mem_univ a)
  have hCmax_nonneg : 0 ≤ Cmax := by
    let a0 : Fin (p + 1) := ⟨0, Nat.zero_lt_succ p⟩
    exact (hfac_nonneg a0).trans (hfac_le a0)
  let epsComp := eps / (Cmax + 1)
  have hden : 0 < Cmax + 1 := by linarith
  have hepsComp : 0 < epsComp := div_pos heps hden
  have hbudget : ∀ a, fac a * epsComp ≤ eps := by
    intro a
    refine (mul_le_mul_of_nonneg_right (hfac_le a) hepsComp.le).trans ?_
    dsimp only [epsComp]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  obtain ⟨eta, heta, Ncomp, hcomp⟩ :=
    hstage.cov_comp_tail inp P L hr phi hphi hconn U C0 C1 aInf
      Jinf Jbarinf gInf hRS hSr e p epsComp hepsComp
  obtain ⟨Njet, hjet⟩ :=
    hstage.2.2.1 S hSr 0 1 (by norm_num)
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hr phi hphi hconn U C0 C1 aInf
      Jinf Jbarinf gInf S hSr
  obtain ⟨Ncenter, hcenter⟩ := eventually_atTop.mp
    (liveCenters_rInf inp.decay P inp.realizes (L.subseq hphi) inp.pack r)
  refine ⟨max Ncomp (max Njet (max Nloc Ncenter)), ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  let F := stageComparisonMap inp P Lphi r hr hconn k l
  have hkComp : Ncomp ≤ k := (Nat.le_max_left _ _).trans hk
  have hlComp : Ncomp ≤ l := (Nat.le_max_left _ _).trans hl
  have hkJet : Njet ≤ k :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Ncomp _).trans hk)
  have hlJet : Njet ≤ l :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right Ncomp _).trans hl)
  have hkLoc : Nloc ≤ k :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right Njet _).trans ((Nat.le_max_right Ncomp _).trans hk))
  have hlLoc : Nloc ≤ l :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right Njet _).trans ((Nat.le_max_right Ncomp _).trans hl))
  have hkCenter : Ncenter ≤ k :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right Njet _).trans ((Nat.le_max_right Ncomp _).trans hk))
  have hjetKL := hjet k hkJet l hlJet
  have hlocKL := hloc k hkLoc l hlLoc
  intro G hG a ha y hy
  obtain ⟨alpha, z, hzy, hbuffer, hcompZ⟩ :=
    hcomp k hkComp l hlComp y hy
  rcases hstage with ⟨hdata, hmetric, _hjets, _hbase⟩
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric cl
  let A : E → E := fun q => chiL (F (chiK.symm q))
  let B : E → (E →L[Real] E →L[Real] Real) :=
    normalCoordMetric (I := I) Yk ck
  let Q : E → (E →L[Real] E →L[Real] Real) := fun q =>
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (normalCoordMetric (I := I) Yl cl (A q), fderiv Real A q)
  let Ralpha : Real := L.rInf (alpha.1 : Nat) + 1
  let D : Set E := Metric.ball (0 : E)
    (inp.normalRadius.phaseRadius Ralpha)
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hC1D, _hgInf, _hBconv, _hgEquiv⟩ := hmetric alpha
  let Bmid : Set Yk.M := Metric.ball Yk.basepoint S
  have hBopen : IsOpen Bmid := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          Bmid := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  let Vset : Set E :=
    interior (C0 alpha) ∩ (chiK.target ∩ chiK.symm ⁻¹' Bmid)
  have hVopen : IsOpen Vset := by
    dsimp only [Vset]
    exact isOpen_interior.inter
      (chiK.toOpenPartialHomeomorph.continuousOn_invFun.isOpen_inter_preimage
        chiK.open_target hBopen)
  let V : TopologicalSpace.Opens E := ⟨Vset, hVopen⟩
  letI : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(Real, E) V.isOpen)
  have hzV : z ∈ V := by
    refine ⟨hbuffer (Metric.mem_closedBall_self (heta alpha).le), ?_⟩
    have hyBall : y ∈ Bmid := by
      exact Metric.closedBall_subset_ball hRS
        (by simpa only [Bmid, NetLimitData.hatSourceBall, Yk] using hy)
    have hzy' : chiK.symm z = y := by
      simpa only [chiK, ck, Yk, Lphi] using hzy
    have hzU : z ∈ U alpha :=
      hC1U (interior_subset (hC01
        (interior_subset (hbuffer (Metric.mem_closedBall_self (heta alpha).le)))))
    have hgeomK :=
      hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
    have hzNorm : ‖z‖ < expRadiusGp (I := I) Yk.metric ck := by
      simpa only [Metric.mem_ball, dist_zero_right, Yk, ck, Lphi] using
        hgeomK.2.1 hzU
    refine ⟨?_, ?_⟩
    · change z ∈ (framedExpDiffeo (I := I) Yk.metric ck).source
      rw [framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
      simpa only [normalFrame_sqrt] using hzNorm
    · change chiK.symm z ∈ Bmid
      rw [hzy']
      exact hyBall
  have hVQ : V ≤ normalQuarter (I := I) Yk ck := by
    intro w hw
    have hwC0 : (w : E) ∈ C0 alpha := interior_subset hw.1
    have hwD : (w : E) ∈ D := hC1D (interior_subset (hC01 hwC0))
    have hquarter := inp.normalRadius.phaseRadius_exp
      (hcenter k hkCenter alpha).le
    simpa only [V, D, Ralpha, normalQuarter, Yk, ck, Lphi] using hquarter hwD
  have hjetAt (w : V) :
      F (chiK.symm (w : E)) ∈ (normalExpPD (I := I) Yl cl).target ∧
        ContDiffAt Real ∞ A (w : E) := by
    have hwS : chiK.symm (w : E) ∈
        Lphi.hatSourceBall inp.decay P S k := by
      exact Metric.ball_subset_closedBall
        (by simpa only [V, Vset, Bmid] using w.2.2.2)
    have hout := hjetKL alpha (w : E) (interior_subset w.2.1)
      w.2.1 hwS
    simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using
      ⟨hout.1, hout.2.1⟩
  have hsmallTarget : ∀ q : Yl.M,
      q ∈ (normalExpPD (I := I) Yl cl).target → q ∈ chiL.source := by
    intro q hq
    rcases hq with ⟨v, hv, rfl⟩
    have hvNorm : ‖v‖ < expRadiusGp (I := I) Yl.metric cl := by
      change v ∈ Metric.ball (0 : E)
        (expRadiusGp (I := I) Yl.metric cl) at hv
      simpa only [Metric.mem_ball, dist_zero_right] using hv
    have hvSource : v ∈ (framedExpDiffeo
        (I := I) Yl.metric cl).source := by
      rw [framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yl.metric cl
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yl.metric cl
      simpa only [normalFrame_sqrt] using hvNorm
    have hmap :=
      (framedExpDiffeo (I := I) Yl.metric cl).map_source hvSource
    simpa only [normalExpPD, chiL] using hmap
  have hsourceS (w : V) : chiK.symm (w : E) ∈
      Lphi.hatSourceBall inp.decay P S k := by
    exact Metric.ball_subset_closedBall
      (by simpa only [V, Vset, Bmid] using w.2.2.2)
  have hQcoeff : ∀ (w : V) (u v : E),
      (quarterPull (I := I) Yk ck G).inner
          (TopologicalSpace.Opens.inclusion hVQ w) u v =
        Q (w : E) u v := by
    intro w u v
    have hFdiff : MDifferentiableAt I I F (chiK.symm (w : E)) :=
      (hlocKL ⟨chiK.symm (w : E), hsourceS w⟩).mdifferentiableAt (by simp)
    have hmetricEq : ∀ v' w' : TangentSpace I (chiK.symm (w : E)),
        G.inner (chiK.symm (w : E)) v' w' =
          Yl.metric.inner (F (chiK.symm (w : E)))
            (mfderiv I I F (chiK.symm (w : E)) v')
            (mfderiv I I F (chiK.symm (w : E)) w') :=
      hG _ (hsourceS w)
    have hout := stagePull_coeff (I := I) Yk Yl ck cl F G
      (TopologicalSpace.Opens.inclusion hVQ w)
      (hsmallTarget _ (hjetAt w).1) hFdiff (by
        simpa only [chiK] using hmetricEq) u v
    simpa only [Q, A, chiK] using hout
  have hVU : ∀ w : V, (w : E) ∈ U alpha := by
    intro w
    exact hC1U (interior_subset (hC01 (interior_subset w.2.1)))
  have hgeomK :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hBco : ∀ w : E, w ∈ V → IsCoercive (B w) := by
    intro w hw
    have hEquiv : NormalCoordMetricEquivOn (I := I) Yk ck (U alpha) := by
      intro q hq v
      exact inp.normalBounds.metric_equiv (Lphi.φ k) ck q (hgeomK.1 hq) v
    simpa only [B] using hEquiv.coercive (hVU ⟨w, hw⟩)
  have hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ B z v v ∧
        B z v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    have hraw := inp.normalBounds.metric_equiv (Lphi.φ k) ck z
      (hgeomK.1 (hVU ⟨z, hzV⟩)) v
    simpa only [B] using hraw
  have hBcd : ContDiffOn Real (∞ : WithTop ℕ∞) B V := by
    have hVexp : (V : Set E) ⊆ Metric.ball (0 : E)
        (expRadiusGp (I := I) Yk.metric ck) := by
      intro w hw
      have hwq := hVQ hw
      exact Metric.ball_subset_ball (by
        nlinarith [expRadiusGp_pos (I := I) Yk.metric ck]) hwq
    simpa only [B] using
      (normalCoordMetric_contDiffOn_expBall (I := I) Yk ck).mono hVexp
  have hAcd : ContDiffOn Real (∞ : WithTop ℕ∞) A V := by
    intro w hw
    exact (hjetAt ⟨w, hw⟩).2.contDiffWithinAt
  have hAmap : Set.MapsTo A V (normalBall (I := I) Yl cl) := by
    intro w hw
    have hout := (normalExpPD (I := I) Yl cl).map_target
      (hjetAt ⟨w, hw⟩).1
    simpa only [A, chiL, normalExpPD_source] using hout
  have hBAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => normalCoordMetric (I := I) Yl cl (A w)) V := by
    have htarget : ContDiffOn Real (∞ : WithTop ℕ∞)
        (normalCoordMetric (I := I) Yl cl) (normalBall (I := I) Yl cl) := by
      simpa only [normalBall] using
        normalCoordMetric_contDiffOn_expBall (I := I) Yl cl
    simpa only [Function.comp_def] using htarget.comp hAcd hAmap
  have hDAcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => fderiv Real A w) V := by
    intro w hw
    exact (((hAcd.contDiffAt (hVopen.mem_nhds hw)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt)
  have hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V := by
    have hpull :=
      (_root_.DifferentialGeometry.HCGCompactness.pullbackForm.contDiff
        (E := E) (F := E)).comp_contDiffOn (hBAcd.prodMk hDAcd)
    simpa only [Q] using hpull
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (B w) (fderiv Real B w)
      (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - B w) (e (slots 0)) (e (slots 1))
  have hdiff : ∀ q : Nat, ∀ w : V,
      ∀ slots : Fin (2 + q) → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun y : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q y slots) (w : E) := by
    simpa only [Gamma, base] using
      metricTower_mdiff V e B Q hBcd hQcd hBco
  have hcompLe : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
          Gamma base a z slots| ≤ epsComp := by
    intro slots
    have hraw := (hcompZ a ha slots).le
    simpa only [Gamma, base, B, Q, A, chiK, chiL, F, ck, cl, Yk, Yl,
      Lphi] using hraw
  let zV : V := ⟨z, hzV⟩
  letI : SigmaCompactSpace (normalQuarter (I := I) Yk ck) :=
    normalQuarterSigma (I := I) Yk ck
  let gQ := (normalTotal (I := I) Yk ck).restrictOpen
    (I := 𝓘(Real, E)) (normalQuarter (I := I) Yk ck)
  have hlocal := local_norm_le (I := I) Yk ck V hVQ G Q a zV
    hepsComp.le hQcoeff hBco hequiv hdiff hcompLe
  have hpoint : framedExpDiffeo (I := I) Yk.metric ck
      (TopologicalSpace.Opens.inclusion hVQ zV : E) = y := by
    change chiK.symm z = y
    simpa only [chiK, ck, Yk, Lphi] using hzy
  calc
    metricDerivNorm (I := I) a G Yk.metric Yk.metric y =
        metricDerivNorm (I := I) a G Yk.metric Yk.metric
          (framedExpDiffeo (I := I) Yk.metric ck
            (TopologicalSpace.Opens.inclusion hVQ zV : E)) :=
      congrArg (fun q => metricDerivNorm (I := I) a G Yk.metric Yk.metric q)
        hpoint.symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          (quarterPull (I := I) Yk ck G) gQ gQ
          (TopologicalSpace.Opens.inclusion hVQ zV) :=
      (quarter_norm_eq (I := I) Yk ck G a
        (TopologicalSpace.Opens.inclusion hVQ zV)).symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          ((quarterPull (I := I) Yk ck G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVQ)
          (gQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ)
          (gQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ) zV :=
      (metricDerivNorm_flat (I := 𝓘(Real, E)) hVQ
        (quarterPull (I := I) Yk ck G) gQ gQ a zV).symm
    _ ≤ Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * epsComp) :=
      hlocal
    _ ≤ eps := by
      let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
      simpa only [fac, afin, mul_assoc] using hbudget afin

/-- A pair-local smooth realization of the exact `invFunOn` pullback metric on
the target image has uniformly small intrinsic metric-difference seminorms on
the image of every strictly smaller retained source ball. -/
theorem HasStageJetData.inv_norm_tail
    (inp : MetricCompactnessInputs (I := I) X)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData inp.decay inp.D P) {r : Real} (hr : 0 ≤ r)
    (phi : Nat → Nat) (hphi : StrictMono phi)
    (hcomplete : ∀ j, MetricComplete (I := I) (X.obj j))
    (hconn : ∀ j,
      letI : TopologicalSpace (X.obj j).M := (X.obj j).topology
      ConnectedSpace (X.obj j).M)
    (U C0 C1 : LiveSlot L inp.pack r → Set E)
    (aInf : (alpha : LiveSlot L inp.pack r) →
      Fin (inp.pack.A r) → E → Real)
    (Jinf Jbarinf : (alpha : LiveSlot L inp.pack r) →
      InterSlot L inp.pack r alpha → E → E)
    (gInf : LiveSlot L inp.pack r →
      E → (E →L[Real] E →L[Real] Real))
    (hstage : HasStageJetData (I := I) inp P L hr phi hphi hconn
      U C0 C1 aInf Jinf Jbarinf gInf)
    {R S T Vrad : Real} (hRS : R < S) (hST : S < T)
    (hroom : T + (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 < Vrad)
    (hVr : Vrad < r)
    (p : Nat) (eps : Real) (heps : 0 < eps) :
    ∃ N : Nat, ∀ k ≥ N, ∀ l ≥ N,
      let Lphi := L.subseq hphi
      let Yk := X.obj (Lphi.φ k)
      let Yl := X.obj (Lphi.φ l)
      letI : TopologicalSpace Yk.M := Yk.topology
      letI : ChartedSpace H Yk.M := Yk.charted
      letI : IsManifold I ∞ Yk.M := Yk.smooth
      letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
      letI : T2Space Yk.M := Yk.t2
      letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
      letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
      letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
      letI : TopologicalSpace Yl.M := Yl.topology
      letI : ChartedSpace H Yl.M := Yl.charted
      letI : IsManifold I ∞ Yl.M := Yl.smooth
      letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
      letI : T2Space Yl.M := Yl.t2
      letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
      letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
      let F := stageComparisonMap inp P Lphi r hr hconn k l
      let Hinv := Function.invFunOn F (Metric.ball Yk.basepoint T)
      ∀ (G : SmoothRiemannianMetric I Yl.M),
        (∀ y ∈ F '' Lphi.hatSourceBall inp.decay P S k,
          ∀ v w : TangentSpace I y,
            G.inner y v w =
              Yk.metric.inner (Hinv y) (mfderiv I I Hinv y v)
                (mfderiv I I Hinv y w)) →
        ∀ a ≤ p, ∀ y ∈ F '' Lphi.hatSourceBall inp.decay P R k,
          metricDerivNorm (I := I) a G Yl.metric Yl.metric y ≤ eps := by
  classical
  let e : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    (stdOrthonormalBasis Real E).toBasis
  let fac : Fin (p + 1) → Real := fun a ↦
    Real.sqrt (2 ^ (2 + (a : Nat))) *
      Real.sqrt
        (Fintype.card
          (Fin (2 + (a : Nat)) → Fin (Module.finrank Real E)) : Real)
  let Cmax : Real := Finset.univ.sup' Finset.univ_nonempty fac
  have hfac_nonneg : ∀ a, 0 ≤ fac a := by
    intro a
    dsimp only [fac]
    positivity
  have hfac_le : ∀ a, fac a ≤ Cmax := by
    intro a
    exact Finset.le_sup' fac (Finset.mem_univ a)
  have hCmax_nonneg : 0 ≤ Cmax := by
    let a0 : Fin (p + 1) := ⟨0, Nat.zero_lt_succ p⟩
    exact (hfac_nonneg a0).trans (hfac_le a0)
  let epsComp := eps / (Cmax + 1)
  have hden : 0 < Cmax + 1 := by linarith
  have hepsComp : 0 < epsComp := div_pos heps hden
  have hbudget : ∀ a, fac a * epsComp ≤ eps := by
    intro a
    refine (mul_le_mul_of_nonneg_right (hfac_le a) hepsComp.le).trans ?_
    dsimp only [epsComp]
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  have hgap : 0 ≤
      (4 + 8 * Real.sqrt 2) * inp.decay.lambda inp.D 0 :=
    mul_nonneg (by positivity) (inp.decay.lambda_pos inp.hD 0).le
  have hTr : T < r := by linarith
  have hSr : S < r := hST.trans hTr
  obtain ⟨eta, heta, Ncomp, hcomp⟩ :=
    hstage.inv_cov_comp_tail inp P L hr phi hphi hcomplete hconn
      U C0 C1 aInf Jinf Jbarinf gInf hRS hST hroom hVr e p epsComp hepsComp
  have hmove : ∀ alpha : LiveSlot L inp.pack r,
      HasStageJetTail (I := I) inp P L hr phi hphi hconn C0 S 0
        (eta alpha / 2) := by
    intro alpha
    exact hstage.2.2.1 S hSr 0 (eta alpha / 2)
      (div_pos (heta alpha) (by norm_num))
  choose Nmove hNmove using hmove
  letI := Fintype.ofFinite (LiveSlot L inp.pack r)
  let NmoveAll : Nat := Finset.univ.sup Nmove
  obtain ⟨Nloc, hloc⟩ :=
    hstage.hloc_tail inp P L hr phi hphi hconn U C0 C1 aInf
      Jinf Jbarinf gInf T hTr
  obtain ⟨Ninj, hinj⟩ :=
    hstage.inj_tail inp P L hr phi hphi hcomplete hconn U C0 C1
      aInf Jinf Jbarinf gInf T Vrad hroom hVr
  obtain ⟨Ncenter, hcenter⟩ := eventually_atTop.mp
    (liveCenters_rInf inp.decay P inp.realizes (L.subseq hphi) inp.pack r)
  let N := max Ncomp (max Nloc (max Ninj (max Ncenter NmoveAll)))
  refine ⟨N, ?_⟩
  intro k hk l hl
  dsimp only
  let Lphi := L.subseq hphi
  let Yk := X.obj (Lphi.φ k)
  let Yl := X.obj (Lphi.φ l)
  letI : TopologicalSpace Yk.M := Yk.topology
  letI : ChartedSpace H Yk.M := Yk.charted
  letI : IsManifold I ∞ Yk.M := Yk.smooth
  letI : SigmaCompactSpace Yk.M := Yk.sigmaCompact
  letI : T2Space Yk.M := Yk.t2
  letI : T2Space (TangentBundle I Yk.M) := Yk.t2TangentBundle
  letI : MetricSpace Yk.M := (P (Lphi.φ k)).ms
  letI : Nonempty Yk.M := ⟨Yk.basepoint⟩
  letI : TopologicalSpace Yl.M := Yl.topology
  letI : ChartedSpace H Yl.M := Yl.charted
  letI : IsManifold I ∞ Yl.M := Yl.smooth
  letI : SigmaCompactSpace Yl.M := Yl.sigmaCompact
  letI : T2Space Yl.M := Yl.t2
  letI : T2Space (TangentBundle I Yl.M) := Yl.t2TangentBundle
  letI : MetricSpace Yl.M := (P (Lphi.φ l)).ms
  let F := stageComparisonMap inp P Lphi r hr hconn k l
  let Hinv := Function.invFunOn F (Metric.ball Yk.basepoint T)
  have hkComp : Ncomp ≤ k := by dsimp only [N] at hk; omega
  have hlComp : Ncomp ≤ l := by dsimp only [N] at hl; omega
  have hkLoc : Nloc ≤ k := by dsimp only [N] at hk; omega
  have hlLoc : Nloc ≤ l := by dsimp only [N] at hl; omega
  have hkInj : Ninj ≤ k := by dsimp only [N] at hk; omega
  have hlInj : Ninj ≤ l := by dsimp only [N] at hl; omega
  have hlCenter : Ncenter ≤ l := by dsimp only [N] at hl; omega
  have hmoveLe (alpha : LiveSlot L inp.pack r) : Nmove alpha ≤ NmoveAll :=
    Finset.le_sup (f := Nmove) (Finset.mem_univ alpha)
  have hlocKL := hloc k hkLoc l hlLoc
  have hinjKL := hinj k hkInj l hlInj
  intro G hG a ha q hq
  rcases hq with ⟨y, hy, rfl⟩
  obtain ⟨alpha, z, hzy, hbuffer, hcompZ⟩ :=
    hcomp k hkComp l hlComp y hy
  rcases hstage with ⟨hdata, hmetric, _hjets, _hbase⟩
  let ck := seqCenterD inp.decay P Lphi k (alpha.1 : Nat)
  let cl := seqCenterD inp.decay P Lphi l (alpha.1 : Nat)
  let chiK := NormalCoordinates.framedChartAt (I := I) Yk.metric ck
  let chiL := NormalCoordinates.framedChartAt (I := I) Yl.metric cl
  let A : E → E := fun w => chiL (F (chiK.symm w))
  let Grev : E → E := fun w => chiK (Hinv (chiL.symm w))
  let BK : E → (E →L[Real] E →L[Real] Real) :=
    normalCoordMetric (I := I) Yk ck
  let BL : E → (E →L[Real] E →L[Real] Real) :=
    normalCoordMetric (I := I) Yl cl
  let Q : E → (E →L[Real] E →L[Real] Real) := fun w =>
    _root_.DifferentialGeometry.HCGCompactness.pullbackForm
      (BK (Grev w), fderiv Real Grev w)
  have hzInt : z ∈ interior (C0 alpha) :=
    hbuffer (Metric.mem_closedBall_self (heta alpha).le)
  have hyS : chiK.symm z ∈ Lphi.hatSourceBall inp.decay P S k := by
    have hzy' : chiK.symm z = y := by
      simpa only [chiK, ck, Yk, Lphi] using hzy
    rw [hzy']
    exact cball_subset_of_le hRS.le hy
  have hkMove : Nmove alpha ≤ k := by
    exact (hmoveLe alpha).trans (by dsimp only [N] at hk; omega)
  have hlMove : Nmove alpha ≤ l := by
    exact (hmoveLe alpha).trans (by dsimp only [N] at hl; omega)
  have hjetZraw := hNmove alpha k hkMove l hlMove alpha z
    (interior_subset hzInt) hzInt hyS
  have hjetZ :
      F (chiK.symm z) ∈ (normalExpPD (I := I) Yl cl).target ∧
        ContDiffAt Real ∞ A z ∧
        ∀ j ≤ 0, mapDerivNorm j A id z ≤ eta alpha / 2 := by
    simpa only [A, F, chiK, chiL, ck, cl, Yk, Yl, Lphi] using hjetZraw
  have hAzDist : dist (A z) z ≤ eta alpha / 2 := by
    have hraw := hjetZ.2.2 0 le_rfl
    simpa only [mapDerivNorm, norm_iteratedFDeriv_zero, id_eq,
      dist_eq_norm] using hraw
  have hAzInt : A z ∈ interior (C0 alpha) := by
    apply hbuffer
    change dist (A z) z ≤ eta alpha
    linarith [heta alpha]
  obtain ⟨_hUopen, _hC0compact, _hC1compact, hC01, hC1U⟩ :=
    hdata.core_on inp P L r hr U C0 C1 aInf Jinf Jbarinf alpha
  obtain ⟨hC1D, _hgInf, _hBconv, _hgEquiv⟩ := hmetric alpha
  let Ralpha : Real := L.rInf (alpha.1 : Nat) + 1
  let D : Set E := Metric.ball (0 : E)
    (inp.normalRadius.phaseRadius Ralpha)
  have hAzD : A z ∈ D :=
    hC1D (interior_subset (hC01 (interior_subset hAzInt)))
  have hAzQ : A z ∈ normalQuarter (I := I) Yl cl := by
    have hquarter := inp.normalRadius.phaseRadius_exp
      (hcenter l hlCenter alpha).le
    simpa only [D, Ralpha, normalQuarter, Yl, cl, Lphi] using hquarter hAzD
  have hgeomK :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf k alpha
  have hzU : z ∈ U alpha :=
    hC1U (interior_subset (hC01 (interior_subset hzInt)))
  have hzNormal : z ∈ normalBall (I := I) Yk ck := by
    simpa only [normalBall, Yk, ck, Lphi] using hgeomK.2.1 hzU
  let dK := normalExpPD (I := I) Yk ck
  let dL := normalExpPD (I := I) Yl cl
  have hyDK : y ∈ dK.target := by
    refine ⟨z, ?_, ?_⟩
    · simpa only [dK, normalExpPD_source] using hzNormal
    · simpa only [dK, normalExpPD, chiK, ck, Yk, Lphi] using hzy
  have hBallOpen : IsOpen (Metric.ball Yk.basepoint T) := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.ball Yk.basepoint T) := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  have hlocBall : IsLocalDiffeomorphOn I I (∞ : WithTop ℕ∞) F
      (Metric.ball Yk.basepoint T) := by
    rintro ⟨x, hx⟩
    exact hlocKL ⟨x, Metric.ball_subset_closedBall hx⟩
  have hinjBall : Set.InjOn F (Metric.ball Yk.basepoint T) :=
    hinjKL.mono Metric.ball_subset_closedBall
  obtain ⟨Phi, hPhiSrc, hPhiTgt, hPhiEq⟩ :=
    exists_diffeo_of_injOn hlocBall hBallOpen hinjBall
  have hsymmEq : Set.EqOn (Phi.symm : Yl.M → Yk.M) Hinv Phi.target := by
    intro q hq
    rw [hPhiTgt] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hPhix : (Phi : Yk.M → Yl.M) x = F x := hPhiEq hx
    have hleft : (Phi.symm : Yl.M → Yk.M) (F x) = x := by
      rw [← hPhix]
      exact Phi.toPartialEquiv.left_inv (by rw [hPhiSrc]; exact hx)
    have hinv : Hinv (F x) = x := by
      exact hinjBall.leftInvOn_invFunOn hx
    rw [hleft, hinv]
  have hBallSOpen : IsOpen (Metric.ball Yk.basepoint S) := by
    have hb :
        @IsOpen Yk.M
          (P (Lphi.φ k)).ms.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
          (Metric.ball Yk.basepoint S) := Metric.isOpen_ball
    rw [ProperMetricOn.top_eq Yk (P (Lphi.φ k))] at hb
    exact hb
  have hBallSsub : Metric.ball Yk.basepoint S ⊆ Phi.source := by
    rw [hPhiSrc]
    exact Metric.ball_subset_ball hST.le
  have hImageOpen : IsOpen ((Phi : Yk.M → Yl.M) ''
      Metric.ball Yk.basepoint S) :=
    Phi.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      hBallSOpen hBallSsub
  let Wphi : Set Yl.M :=
    (Phi : Yk.M → Yl.M) '' Metric.ball Yk.basepoint S ∩
      (Phi.target ∩ (Phi.symm : Yl.M → Yk.M) ⁻¹' dK.target)
  have hWphiOpen : IsOpen Wphi := by
    dsimp only [Wphi]
    exact hImageOpen.inter
      (Phi.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
        Phi.open_target dK.open_target)
  let Wcoord : Set E := dL.source ∩ (dL : E → Yl.M) ⁻¹' Wphi
  have hWcoordOpen : IsOpen Wcoord := by
    dsimp only [Wcoord]
    exact dL.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      dL.open_source hWphiOpen
  let Vset : Set E := interior (C0 alpha) ∩ Wcoord
  have hVopen : IsOpen Vset := isOpen_interior.inter hWcoordOpen
  let V : TopologicalSpace.Opens E := ⟨Vset, hVopen⟩
  letI : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen 𝓘(Real, E) V.isOpen)
  have hySopen : y ∈ Metric.ball Yk.basepoint S := by
    have hyR : dist y Yk.basepoint ≤ R := by
      simpa only [NetLimitData.hatSourceBall, Yk] using hy
    rw [Metric.mem_ball]
    exact hyR.trans_lt hRS
  have hPhiY : (Phi : Yk.M → Yl.M) y = F y :=
    hPhiEq (Metric.ball_subset_ball hST.le hySopen)
  have hPhiSymmY : (Phi.symm : Yl.M → Yk.M) (F y) = y := by
    rw [← hPhiY]
    exact Phi.toPartialEquiv.left_inv (hBallSsub hySopen)
  have hsmallTarget : ∀ q : Yl.M,
      q ∈ dL.target → q ∈ chiL.source := by
    intro q hq
    rcases hq with ⟨v, hv, rfl⟩
    have hvNorm : ‖v‖ < expRadiusGp (I := I) Yl.metric cl := by
      change v ∈ Metric.ball (0 : E)
        (expRadiusGp (I := I) Yl.metric cl) at hv
      simpa only [Metric.mem_ball, dist_zero_right] using hv
    have hvSource : v ∈ (framedExpDiffeo
        (I := I) Yl.metric cl).source := by
      rw [framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yl.metric cl
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yl.metric cl
      simpa only [normalFrame_sqrt] using hvNorm
    have hmap :=
      (framedExpDiffeo (I := I) Yl.metric cl).map_source hvSource
    simpa only [dL, normalExpPD, chiL] using hmap
  have hdecode : chiL.symm (A z) = F y := by
    have hzy' : chiK.symm z = y := by
      simpa only [chiK, ck, Yk, Lphi] using hzy
    have hsrc : F y ∈ chiL.source := by
      exact hsmallTarget _ (by simpa only [hzy'] using hjetZ.1)
    simpa only [A, hzy'] using chiL.left_inv hsrc
  have hAzV : A z ∈ V := by
    refine ⟨hAzInt, ?_⟩
    have hAzSrc : A z ∈ dL.source :=
      normalQuarter_sub (I := I) Yl cl hAzQ
    refine ⟨hAzSrc, ?_⟩
    have hdLA : dL (A z) = F y := by
      simpa only [dL, normalExpPD, chiL] using hdecode
    change dL (A z) ∈ Wphi
    rw [hdLA]
    refine ⟨⟨y, hySopen, hPhiY⟩, ?_, ?_⟩
    · rw [hPhiTgt]
      exact ⟨y, Metric.ball_subset_ball hST.le hySopen, rfl⟩
    · change Phi.symm (F y) ∈ dK.target
      rw [hPhiSymmY]
      exact hyDK
  have hVQ : V ≤ normalQuarter (I := I) Yl cl := by
    intro w hw
    have hwD : (w : E) ∈ D :=
      hC1D (interior_subset (hC01 (interior_subset hw.1)))
    have hquarter := inp.normalRadius.phaseRadius_exp
      (hcenter l hlCenter alpha).le
    simpa only [V, Vset, D, Ralpha, normalQuarter, Yl, cl, Lphi] using
      hquarter hwD
  have hImageEq : (Phi : Yk.M → Yl.M) '' Metric.ball Yk.basepoint S =
      F '' Metric.ball Yk.basepoint S :=
    Set.EqOn.image_eq (fun x hx =>
      hPhiEq (Metric.ball_subset_ball hST.le hx))
  have hHcdOn : ContMDiffOn I I ∞ Hinv Phi.target :=
    Phi.symm.contMDiffOn_toFun.congr
      (fun q hq => (hsymmEq hq).symm)
  let Gaux : E → E := fun w => dK.symm (Phi.symm (dL w))
  have hauxMD : ContMDiffOn 𝓘(Real, E) 𝓘(Real, E) ∞ Gaux V := by
    have h1 := dL.contMDiffOn_toFun.mono
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.1)
    have h2 := Phi.symm.contMDiffOn_toFun.comp h1
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.2.2.1)
    have h3 := dK.symm.contMDiffOn_toFun.comp h2
      (fun (w : E) (hw : w ∈ (V : Set E)) => hw.2.2.2.2)
    simpa only [Gaux] using h3
  have hauxEq : Set.EqOn Gaux Grev V := by
    intro w hw
    have heq := hsymmEq hw.2.2.2.1
    simpa only [Gaux, Grev, dK, dL, normalExpPD, chiK, chiL] using
      congrArg (fun q => chiK q) heq
  have hGrevcd : ContDiffOn Real (∞ : WithTop ℕ∞) Grev V := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hauxMD.congr (fun w hw => (hauxEq hw).symm)
  have hGrevMap : Set.MapsTo Grev V (normalBall (I := I) Yk ck) := by
    intro w hw
    rw [← hauxEq hw]
    simpa only [Gaux, dK, normalExpPD_source] using
      dK.map_target hw.2.2.2.2
  have hsmallSource : ∀ q : Yk.M,
      q ∈ dK.target → q ∈ chiK.source := by
    intro q hq
    rcases hq with ⟨v, hv, rfl⟩
    have hvNorm : ‖v‖ < expRadiusGp (I := I) Yk.metric ck := by
      change v ∈ Metric.ball (0 : E)
        (expRadiusGp (I := I) Yk.metric ck) at hv
      simpa only [Metric.mem_ball, dist_zero_right] using hv
    have hvSource : v ∈ (framedExpDiffeo
        (I := I) Yk.metric ck).source := by
      rw [framedExp_source]
      apply mem_expMapDiffeo_source_of_norm_lt_radius (I := I) Yk.metric ck
      apply norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Yk.metric ck
      simpa only [normalFrame_sqrt] using hvNorm
    have hmap :=
      (framedExpDiffeo (I := I) Yk.metric ck).map_source hvSource
    simpa only [dK, normalExpPD, chiK] using hmap
  have hQcoeff : ∀ (w : V) (u v : E),
      (quarterPull (I := I) Yl cl G).inner
          (TopologicalSpace.Opens.inclusion hVQ w) u v =
        Q (w : E) u v := by
    intro w u v
    have hPhiTarget : dL (w : E) ∈ Phi.target := w.2.2.2.2.1
    have hInvTarget : Hinv (chiL.symm (w : E)) ∈ dK.target := by
      have hmem := w.2.2.2.2.2
      change Phi.symm (dL (w : E)) ∈ dK.target at hmem
      rw [hsymmEq hPhiTarget] at hmem
      simpa only [dL, normalExpPD, chiL] using hmem
    have hInvSource : Hinv (chiL.symm (w : E)) ∈ chiK.source :=
      hsmallSource _ hInvTarget
    have hHdiff : MDifferentiableAt I I Hinv (chiL.symm (w : E)) := by
      have hraw := (hHcdOn.contMDiffAt
        (Phi.open_target.mem_nhds hPhiTarget)).mdifferentiableAt (by simp)
      simpa only [dL, normalExpPD, chiL] using hraw
    have hstageBall : chiL.symm (w : E) ∈
        F '' Metric.ball Yk.basepoint S := by
      have hraw := w.2.2.2.1
      rw [hImageEq] at hraw
      simpa only [dL, normalExpPD, chiL] using hraw
    have hstageClosed : chiL.symm (w : E) ∈
        F '' Lphi.hatSourceBall inp.decay P S k := by
      apply Set.image_mono _ hstageBall
      intro x hx
      simpa only [NetLimitData.hatSourceBall, Yk] using
        Metric.ball_subset_closedBall hx
    have hmetricEq :
        ∀ v' w' : TangentSpace I (chiL.symm (w : E)),
          G.inner (chiL.symm (w : E)) v' w' =
            Yk.metric.inner (Hinv (chiL.symm (w : E)))
              (mfderiv I I Hinv (chiL.symm (w : E)) v')
              (mfderiv I I Hinv (chiL.symm (w : E)) w') :=
      hG _ hstageClosed
    have hout := stagePull_coeff (I := I) Yl Yk cl ck Hinv G
      (TopologicalSpace.Opens.inclusion hVQ w) hInvSource hHdiff (by
        simpa only [chiL] using hmetricEq) u v
    simpa only [Q, Grev, chiL] using hout
  have hVU : ∀ w : V, (w : E) ∈ U alpha := by
    intro w
    exact hC1U (interior_subset (hC01 (interior_subset w.2.1)))
  have hgeomL :=
    hdata.geom_on inp P L r hr U C0 C1 aInf Jinf Jbarinf l alpha
  have hBLco : ∀ w : E, w ∈ V → IsCoercive (BL w) := by
    intro w hw
    have hEquiv : NormalCoordMetricEquivOn (I := I) Yl cl (U alpha) := by
      intro q hq v
      exact inp.normalBounds.metric_equiv (Lphi.φ l) cl q (hgeomL.1 hq) v
    simpa only [BL] using hEquiv.coercive (hVU ⟨w, hw⟩)
  have hequiv : ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ BL (A z) v v ∧
        BL (A z) v v ≤ 2 * ‖v‖ ^ 2 := by
    intro v
    have hraw := inp.normalBounds.metric_equiv (Lphi.φ l) cl (A z)
      (hgeomL.1 (hVU ⟨A z, hAzV⟩)) v
    simpa only [BL] using hraw
  have hBLcd : ContDiffOn Real (∞ : WithTop ℕ∞) BL V := by
    simpa only [BL] using
      (normalCoordMetric_contDiffOn_expBall (I := I) Yl cl).mono
        (fun w hw => hgeomL.2.1 (hVU ⟨w, hw⟩))
  have hBKcd : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => BK (Grev w)) V := by
    have hsource : ContDiffOn Real (∞ : WithTop ℕ∞) BK
        (normalBall (I := I) Yk ck) := by
      simpa only [BK, normalBall] using
        normalCoordMetric_contDiffOn_expBall (I := I) Yk ck
    simpa only [Function.comp_def] using hsource.comp hGrevcd hGrevMap
  have hDGrev : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun w => fderiv Real Grev w) V := by
    intro w hw
    exact (((hGrevcd.contDiffAt (hVopen.mem_nhds hw)).fderiv_right
      (m := (∞ : WithTop ℕ∞)) (by simp)).contDiffWithinAt)
  have hQcd : ContDiffOn Real (∞ : WithTop ℕ∞) Q V := by
    have hpull :=
      (_root_.DifferentialGeometry.HCGCompactness.pullbackForm.contDiff
        (E := E) (F := E)).comp_contDiffOn (hBKcd.prodMk hDGrev)
    simpa only [Q] using hpull
  let Gamma := fun w i j m ↦ e.coord m
    (MetricKoszul.raisedKoszulOp (BL w) (fderiv Real BL w)
      (e i) (e j))
  let base := fun w (slots : Fin 2 → Fin (Module.finrank Real E)) ↦
    (Q w - BL w) (e (slots 0)) (e (slots 1))
  have hdiff : ∀ q' : Nat, ∀ w : V,
      ∀ slots : Fin (2 + q') → Fin (Module.finrank Real E),
        MDifferentiableAt 𝓘(Real, E) 𝓘(Real, Real)
          (fun x : E ↦ iterCovComp (I := 𝓘(Real, E))
            (fun i _ ↦ e i) Gamma base q' x slots) (w : E) := by
    simpa only [Gamma, base] using
      metricTower_mdiff V e BL Q hBLcd hQcd hBLco
  have hcompLe : ∀ slots : Fin (2 + a) → Fin (Module.finrank Real E),
      |iterCovComp (I := 𝓘(Real, E)) (fun i _ ↦ e i)
          Gamma base a (A z) slots| ≤ epsComp := by
    intro slots
    have hraw := (hcompZ a ha slots).le
    simpa only [Gamma, base, BL, BK, Q, Grev, A, F, Hinv, chiK, chiL,
      ck, cl, Yk, Yl, Lphi] using hraw
  let wV : V := ⟨A z, hAzV⟩
  letI : SigmaCompactSpace (normalQuarter (I := I) Yl cl) :=
    normalQuarterSigma (I := I) Yl cl
  let gQ := (normalTotal (I := I) Yl cl).restrictOpen
    (I := 𝓘(Real, E)) (normalQuarter (I := I) Yl cl)
  have hlocal := local_norm_le (I := I) Yl cl V hVQ G Q a wV
    hepsComp.le hQcoeff hBLco hequiv hdiff hcompLe
  have hpoint : framedExpDiffeo (I := I) Yl.metric cl
      (TopologicalSpace.Opens.inclusion hVQ wV : E) = F y := by
    change chiL.symm (A z) = F y
    exact hdecode
  calc
    metricDerivNorm (I := I) a G Yl.metric Yl.metric (F y) =
        metricDerivNorm (I := I) a G Yl.metric Yl.metric
          (framedExpDiffeo (I := I) Yl.metric cl
            (TopologicalSpace.Opens.inclusion hVQ wV : E)) :=
      congrArg (fun q' => metricDerivNorm (I := I) a G
        Yl.metric Yl.metric q') hpoint.symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          (quarterPull (I := I) Yl cl G) gQ gQ
          (TopologicalSpace.Opens.inclusion hVQ wV) :=
      (quarter_norm_eq (I := I) Yl cl G a
        (TopologicalSpace.Opens.inclusion hVQ wV)).symm
    _ = metricDerivNorm (I := 𝓘(Real, E)) a
          ((quarterPull (I := I) Yl cl G).restrictOpenOfSubset
            (I := 𝓘(Real, E)) hVQ)
          (gQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ)
          (gQ.restrictOpenOfSubset (I := 𝓘(Real, E)) hVQ) wV :=
      (metricDerivNorm_flat (I := 𝓘(Real, E)) hVQ
        (quarterPull (I := I) Yl cl G) gQ gQ a wV).symm
    _ ≤ Real.sqrt (2 ^ (2 + a)) *
          (Real.sqrt
            (Fintype.card
              (Fin (2 + a) → Fin (Module.finrank Real E)) : Real) * epsComp) :=
      hlocal
    _ ≤ eps := by
      let afin : Fin (p + 1) := ⟨a, Nat.lt_succ_iff.mpr ha⟩
      simpa only [fac, afin, mul_assoc] using hbudget afin

end HCGCompactness
end DifferentialGeometry
