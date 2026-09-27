import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Topology.Morse.EuclideanModel

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff



namespace DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

open DifferentialGeometry.Geometry.Riemannian

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Inhabited N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace N] [ConnectedSpace N] in
theorem liftedMetric_transContinuousLinearEquiv
    (g : SmoothRiemannianMetric I N) (e : E ≃L[ℝ] F) :
    liftedMetric (I := I.transContinuousLinearEquiv e) (g.transContinuousLinearEquiv e) =
      (liftedMetric (I := I) g).transContinuousLinearEquiv e := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hL : (g.transContinuousLinearEquiv e).inner (proj x) v w =
      g.inner (proj x) (e.symm v) (e.symm w) := by
    have h := SmoothRiemannianMetric.transContinuousLinearEquiv_inner (I := I) g e (proj x) v w
    exact h
  have hR : ((liftedMetric (I := I) g).transContinuousLinearEquiv e).inner x v w =
      g.inner (proj x) (e.symm v) (e.symm w) := by
    have h := SmoothRiemannianMetric.transContinuousLinearEquiv_inner (I := I)
      (liftedMetric (I := I) g) e x v w
    exact h.trans rfl
  rw [show (liftedMetric (I := I.transContinuousLinearEquiv e)
        (g.transContinuousLinearEquiv e)).inner x v w =
        (g.transContinuousLinearEquiv e).inner (proj x) v w from rfl]
  exact hL.trans hR.symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace N] [ConnectedSpace N] in
theorem liftedMetric_transContinuousLinearEquiv_symm
    (g : SmoothRiemannianMetric I N) (e : E ≃L[ℝ] F) :
    Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g)
        (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e).symm =
      liftedMetric (I := I.transContinuousLinearEquiv e)
        (g.transContinuousLinearEquiv e) :=
  (liftedMetric_transContinuousLinearEquiv (I := I) g e).symm

end DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Topology.Morse

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
  [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Nonempty N]

private local instance inhabitedOfNonempty : Inhabited N :=
  ⟨Classical.choice (inferInstance : Nonempty N)⟩

private theorem flatModelMetric_inner_mul (s a c : ℝ) :
    (flatModelMetric ℝ).inner s a c = a * c := by
  change inner ℝ a c = a * c
  rw [RCLike.inner_apply]
  simp
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space N] [SigmaCompactSpace N]
  [ConnectedSpace N] [Nonempty N] in
theorem TerminalSurfaceProduct.pullbackMetricCross_Phi [Inhabited N]
    {g : SmoothRiemannianMetric I N} (P : TerminalSurfaceProduct (I := I) g) :
    Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) P.Phi =
      P.h.prod (flatModelMetric ℝ) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  obtain ⟨y, s⟩ := z
  have h1 := Diffeomorph.pullbackMetricCross_inner (liftedMetric (I := I) g) P.Phi (y, s) v w
  have h2 := P.product y s v.1 w.1 v.2 w.2
  have h3 := SmoothRiemannianMetric.prod_inner P.h (flatModelMetric ℝ) (y, s)
    (v.1, v.2) (w.1, w.2)
  have h4 := flatModelMetric_inner_mul s v.2 w.2
  calc (Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) P.Phi).inner (y, s) v w
      = (liftedMetric (I := I) g).inner (P.Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (P.Phi : P.S × ℝ → UniversalCover N) (y, s) v)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (P.Phi : P.S × ℝ → UniversalCover N) (y, s) w) :=
        h1
    _ = (liftedMetric (I := I) g).inner (P.Phi (y, s))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (P.Phi : P.S × ℝ → UniversalCover N) (y, s)
            (v.1, v.2))
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I (P.Phi : P.S × ℝ → UniversalCover N) (y, s)
            (w.1, w.2)) := by
        rw [show v = (v.1, v.2) from (Prod.eta v).symm,
          show w = (w.1, w.2) from (Prod.eta w).symm]
    _ = P.h.inner y v.1 w.1 + v.2 * w.2 := h2
    _ = (P.h.prod (flatModelMetric ℝ)).inner (y, s) (v.1, v.2) (w.1, w.2) := by
        rw [h3, h4]
    _ = (P.h.prod (flatModelMetric ℝ)).inner (y, s) v w := by
        rw [show (v.1, v.2) = v from Prod.eta v, show (w.1, w.2) = w from Prod.eta w]

omit [CompleteSpace F] [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace N]
  [ConnectedSpace N] in
theorem TerminalSurfaceProduct.pullbackMetricCross_Phi_transContinuousLinearEquiv
    {g : SmoothRiemannianMetric I N} (P : TerminalSurfaceProduct (I := I) g)
    (e : E ≃L[ℝ] F) :
    Diffeomorph.pullbackMetricCross
        (liftedMetric (I := I.transContinuousLinearEquiv e)
          (g.transContinuousLinearEquiv e))
        (P.Phi.trans
          (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e)) =
      P.h.prod (flatModelMetric ℝ) := by
  rw [← Diffeomorph.pullbackMetricCross_trans,
    liftedMetric_transContinuousLinearEquiv,
    SmoothRiemannianMetric.pullback_transContinuousLinearEquiv,
    P.pullbackMetricCross_Phi]

def TerminalSurfaceProduct.transContinuousLinearEquiv
    {g : SmoothRiemannianMetric I N} (P : TerminalSurfaceProduct (I := I) g)
    (e : E ≃L[ℝ] F) :
    TerminalSurfaceProduct (I := I.transContinuousLinearEquiv e)
      (g.transContinuousLinearEquiv e) where
  S := P.S
  topology := P.topology
  charted := P.charted
  smooth := P.smooth
  t2 := P.t2
  sigmaCompact := P.sigmaCompact
  connected := P.connected
  h := P.h
  Phi := P.Phi.trans
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e)
  product := by
    intro y s v w a c
    have hkey := congrArg (fun k : SmoothRiemannianMetric
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) (P.S × ℝ) => k.inner (y, s) (v, a) (w, c))
      (P.pullbackMetricCross_Phi_transContinuousLinearEquiv e)
    have hpb := Diffeomorph.pullbackMetricCross_inner
      (liftedMetric (I := I.transContinuousLinearEquiv e)
        (g.transContinuousLinearEquiv e))
      (P.Phi.trans (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e))
      (y, s) (v, a) (w, c)
    have hprod : (P.h.prod (flatModelMetric ℝ)).inner (y, s) (v, a) (w, c) =
        P.h.inner y v w + (flatModelMetric ℝ).inner s a c :=
      SmoothRiemannianMetric.prod_inner P.h (flatModelMetric ℝ) (y, s) (v, a) (w, c)
    exact hpb.symm.trans (hkey.trans (hprod.trans (by
      rw [flatModelMetric_inner_mul])))
  complete := P.complete
  positive := P.positive

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ E] [I.Boundaryless]
  [SigmaCompactSpace N] [ConnectedSpace N] in
theorem TerminalSurfaceProduct.pullbackMetricCross_Phi_transContinuousLinearEquiv_symm
    {g : SmoothRiemannianMetric I N} (e : E ≃L[ℝ] F)
    (P : TerminalSurfaceProduct (I := I.transContinuousLinearEquiv e)
      (g.transContinuousLinearEquiv e)) :
    Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g)
        (P.Phi.trans
          (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e).symm) =
      P.h.prod (flatModelMetric ℝ) := by
  rw [← Diffeomorph.pullbackMetricCross_trans,
    liftedMetric_transContinuousLinearEquiv_symm,
    P.pullbackMetricCross_Phi]

def TerminalSurfaceProduct.ofTransContinuousLinearEquiv
    {g : SmoothRiemannianMetric I N} (e : E ≃L[ℝ] F)
    (P : TerminalSurfaceProduct (I := I.transContinuousLinearEquiv e)
      (g.transContinuousLinearEquiv e)) :
    TerminalSurfaceProduct (I := I) g where
  S := P.S
  topology := P.topology
  charted := P.charted
  smooth := P.smooth
  t2 := P.t2
  sigmaCompact := P.sigmaCompact
  connected := P.connected
  h := P.h
  Phi := P.Phi.trans
    (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e).symm
  product := by
    intro y s v w a c
    have hkey := congrArg (fun k : SmoothRiemannianMetric
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) (P.S × ℝ) => k.inner (y, s) (v, a) (w, c))
      (P.pullbackMetricCross_Phi_transContinuousLinearEquiv_symm (I := I) (g := g) e)
    have hpb := Diffeomorph.pullbackMetricCross_inner
      (liftedMetric (I := I) g)
      (P.Phi.trans (ContinuousLinearEquiv.toTransContinuousLinearEquiv I (UniversalCover N) e).symm)
      (y, s) (v, a) (w, c)
    have hprod : (P.h.prod (flatModelMetric ℝ)).inner (y, s) (v, a) (w, c) =
        P.h.inner y v w + (flatModelMetric ℝ).inner s a c :=
      SmoothRiemannianMetric.prod_inner P.h (flatModelMetric ℝ) (y, s) (v, a) (w, c)
    exact hpb.symm.trans (hkey.trans (hprod.trans (by
      rw [flatModelMetric_inner_mul])))
  complete := P.complete
  positive := P.positive

omit [CompleteSpace E] [CompleteSpace F] [I.Boundaryless] [SigmaCompactSpace N] [ConnectedSpace N] in
theorem nonempty_terminalSurfaceProduct_transContinuousLinearEquiv_iff
    (g : SmoothRiemannianMetric I N) (e : E ≃L[ℝ] F) :
    Nonempty (TerminalSurfaceProduct (I := I.transContinuousLinearEquiv e)
        (g.transContinuousLinearEquiv e)) ↔
      Nonempty (TerminalSurfaceProduct (I := I) g) :=
  ⟨fun ⟨P⟩ => ⟨P.ofTransContinuousLinearEquiv e⟩,
    fun ⟨P⟩ => ⟨P.transContinuousLinearEquiv e⟩⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem nonempty_terminalSurfaceProduct_of_morseModel_hasCurvatureSurfaceProductSplitting
    (e : E ≃L[ℝ] MorseModel 3) (g : SmoothRiemannianMetric I N)
    (hS : DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
      (I := I.transContinuousLinearEquiv e) (M := N)
      (g.transContinuousLinearEquiv e)) :
    Nonempty (TerminalSurfaceProduct (I := I) g) :=
  (nonempty_terminalSurfaceProduct_of_hasCurvatureSurfaceProductSplitting
    (I := I.transContinuousLinearEquiv e) (g.transContinuousLinearEquiv e) hS).elim
    fun P => ⟨P.ofTransContinuousLinearEquiv e⟩

theorem nonempty_terminalSurfaceProduct_euclideanSpace_of_morseModelSurfaceProductSplitting
    {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) H} [I.Boundaryless]
    {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
    [LocallyPathConnectedSpace N] [SemilocallySimplyConnectedSpace N] [Nonempty N]
    (g : SmoothRiemannianMetric I N)
    (hS : DifferentialGeometry.Geometry.Curvature.DimensionThree.HasCurvatureSurfaceProductSplitting
      (I := I.transContinuousLinearEquiv (morseModelEuclideanModelEquiv 3).symm) (M := N)
      (g.transContinuousLinearEquiv (morseModelEuclideanModelEquiv 3).symm)) :
    Nonempty (TerminalSurfaceProduct (I := I) g) :=
  nonempty_terminalSurfaceProduct_of_morseModel_hasCurvatureSurfaceProductSplitting
    (morseModelEuclideanModelEquiv 3).symm g hS

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
