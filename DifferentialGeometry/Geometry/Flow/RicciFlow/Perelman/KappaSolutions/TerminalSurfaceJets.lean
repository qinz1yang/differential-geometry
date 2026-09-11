import DifferentialGeometry.Geometry.Metric.UniversalCover.ProductCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NormalizedKLimSpatialJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossModelBallTransport
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Manifold MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

section Transport

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem edistOf_le_of_pullback_inner
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    (f : M₁ → M₂) (hf : ContMDiff I₁ I₂ ∞ f)
    (hmetric : ∀ (x : M₁) (v w : TangentSpace I₁ x),
      h.inner (f x) (mfderiv I₁ I₂ f x v) (mfderiv I₁ I₂ f x w) = g.inner x v w)
    (x y : M₁) :
    riemannianEDistOf (I := I₂) h (f x) (f y) ≤ riemannianEDistOf (I := I₁) g x y := by
  rw [edistOf_iInf, edistOf_iInf]
  refine le_iInf fun gamma => le_iInf fun hgamma => ?_
  have hmap : ContMDiff (𝓡∂ 1) I₂ 1 (gamma.map hf.continuous) := by
    change ContMDiff (𝓡∂ 1) I₂ 1 (f ∘ gamma)
    exact (hf.of_le (by simp)).comp hgamma
  refine iInf_le_of_le (gamma.map hf.continuous) (iInf_le_of_le hmap ?_)
  apply le_of_eq
  apply lintegral_congr
  intro t
  have hderiv : mfderiv (𝓡∂ 1) I₂ (gamma.map hf.continuous) t 1 =
      mfderiv I₁ I₂ f (gamma t) (mfderiv (𝓡∂ 1) I₁ gamma t 1) := by
    change mfderiv (𝓡∂ 1) I₂ (f ∘ gamma) t 1 = _
    exact mfderiv_comp_apply t (hf.mdifferentiable (by simp) (gamma t))
      (hgamma.mdifferentiable one_ne_zero t) 1
  change ENNReal.ofReal (Real.sqrt (h.inner (f (gamma t))
    (mfderiv (𝓡∂ 1) I₂ (gamma.map hf.continuous) t 1)
    (mfderiv (𝓡∂ 1) I₂ (gamma.map hf.continuous) t 1))) = _
  rw [hderiv, hmetric]


private theorem riemannianEDistOf_proj_le [LocallyPathConnectedSpace M₁]
    [SemilocallySimplyConnectedSpace M₁] [Inhabited M₁]
    (g : SmoothRiemannianMetric I₁ M₁) (x' y' : UniversalCover M₁) :
    riemannianEDistOf (I := I₁) g (UniversalCover.proj x') (UniversalCover.proj y') ≤
      riemannianEDistOf (I := I₁) (UniversalCover.liftedMetric (I := I₁) g) x' y' := by
  refine edistOf_le_of_pullback_inner (UniversalCover.liftedMetric (I := I₁) g) g
    UniversalCover.proj UniversalCover.proj_contMDiff ?_ x' y'
  intro z v w
  rw [(UniversalCover.hasMFDerivAt_proj (I := I₁) (M := M₁) z).mfderiv]
  rfl


private theorem riemannianEDistOf_prodMk_le
    (h : SmoothRiemannianMetric I₁ M₁)
    (gP : SmoothRiemannianMetric (I₁.prod 𝓘(ℝ, ℝ)) (M₁ × ℝ)) (b : ℝ)
    (hproduct : ∀ (z : M₁) (s : ℝ) (v w : TangentSpace I₁ z) (a c : ℝ),
      gP.inner (z, s) (v, a) (w, c) = h.inner z v w + b * (a * c))
    (s : ℝ) (z y : M₁) :
    riemannianEDistOf (I := I₁.prod 𝓘(ℝ, ℝ)) gP (z, s) (y, s) ≤
      riemannianEDistOf (I := I₁) h z y := by
  refine edistOf_le_of_pullback_inner h gP (fun p : M₁ => (p, s))
    (contMDiff_id.prodMk contMDiff_const) ?_ z y
  intro p v w
  have hd : ∀ t : TangentSpace I₁ p,
      mfderiv I₁ (I₁.prod 𝓘(ℝ, ℝ)) (fun r : M₁ => (r, s)) p t = (t, (0 : ℝ)) := by
    intro t
    rw [mfderiv_prod_left]
    rfl
  rw [hd v, hd w]
  exact (hproduct p s v w 0 0).trans (by ring)


private theorem liftedMetric_scaleMetric_inner [LocallyPathConnectedSpace M₁]
    [SemilocallySimplyConnectedSpace M₁] [Inhabited M₁]
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric I₁ M₁)
    (x' : UniversalCover M₁) (v w : TangentSpace I₁ x') :
    (UniversalCover.liftedMetric (I := I₁) (scaleMetric c hc g)).inner x' v w =
      c * (UniversalCover.liftedMetric (I := I₁) g).inner x' v w :=
  rfl

end Transport

section Flow

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance terminalJetsTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance terminalJetsCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance terminalJetsSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance terminalJetsC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalJetsT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2
private local instance terminalJetsSigma {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SigmaCompactSpace F.M := F.sigmaCompact
private local instance terminalJetsTangentT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle
private local instance terminalJetsInhabited {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Inhabited F.M := ⟨F.basepoint⟩
private local instance terminalJetsLocallyPathConnected {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M
private local instance terminalJetsSemilocallySimplyConnected {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

omit [I.Boundaryless] in
private theorem klim_rescaled_terminal_jet_bound {kappa : ℝ} (hK : KLim (I := I) kappa F)
    {K : ℝ → ℝ}
    (hKbound : ∀ (D' : RealTimeInterval) (G : PointedFlowData.{u, uE, uH} (I := I) D'),
      KLim kappa G → G.S.scalar 0 G.basepoint = 1 →
      ∀ A : ℝ, 0 ≤ A → ∀ s : ℝ, s ≤ 0 → ∀ m : ℕ, ∀ z : G.M,
        riemannianEDistOf (I := I) (G.S.base.metric 0) G.basepoint z ≤ ENNReal.ofReal A →
        curvDerivNorm (I := I) m (G.S.base.metric s) z ≤
          shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (x : F.M) (c : ℝ) (hc : 0 < c)
    (hvalue : F.S.scalar 0 x = c) (z : F.M)
    (hz : riemannianEDistOf (I := I) (scaleMetric c hc (F.S.base.metric 0)) x z ≤
      ENNReal.ofReal A) :
    curvDerivNorm (I := I) m (scaleMetric c hc (F.S.base.metric 0)) z ≤
      shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A := by
  have h0 : (0 : ℝ) ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
  have hGmetric :
      (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 c hc h0 x).S.base.metric 0 =
        scaleMetric c hc (F.S.base.metric 0) := by
    change scaleMetric c hc (F.S.base.metric (parabolicTime 0 c 0)) = _
    rw [parabolicTime_zero]
  have hKG : KLim kappa (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 c hc h0 x) :=
    KLim.curvatureNormalizedFlow F hK 0 c hc h0 x hvalue
  have hbase :
      (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 c hc h0 x).S.scalar 0
        (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 c hc h0 x).basepoint = 1 :=
    curvatureNormalizedFlow_scalar_base F hK.carrier_eq hK.regular_eq 0 c hc h0 x hvalue
  have hres := hKbound ancientTimeInterval
    (curvatureNormalizedFlow F hK.carrier_eq hK.regular_eq 0 c hc h0 x) hKG hbase A hA 0 le_rfl
    m z (by rw [hGmetric]; exact hz)
  rwa [hGmetric] at hres


private theorem terminal_surface_factor_jet_le {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) {K : ℝ → ℝ}
    (hKbound : ∀ (D' : RealTimeInterval) (G : PointedFlowData.{u, uE, uH} (I := I) D'),
      KLim kappa G → G.S.scalar 0 G.basepoint = 1 →
      ∀ A : ℝ, 0 ≤ A → ∀ s : ℝ, s ≤ 0 → ∀ m : ℕ, ∀ z : G.M,
        riemannianEDistOf (I := I) (G.S.base.metric 0) G.basepoint z ≤ ENNReal.ofReal A →
        curvDerivNorm (I := I) m (G.S.base.metric s) z ≤
          shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A)
    (A : ℝ) (hA : 0 ≤ A) (m : ℕ) (q : P.S)
    (hQ : 0 < metricScalarAt (I := 𝓡 2) P.h q) (y : P.S)
    (hy : riemannianEDistOf (I := 𝓡 2)
      (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) q y ≤ ENNReal.ofReal A) :
    curvDerivNorm (I := 𝓡 2) m
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) y ≤
      shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A := by
  classical
  let _ : ConnectedSpace F.M := hK.connected
  have hx : metricScalarAt (I := I) (F.S.base.metric 0)
      (UniversalCover.proj (P.Phi (q, 0))) = metricScalarAt (I := 𝓡 2) P.h q :=
    universalCover_product_scalar_eq (F.S.base.metric 0) P.h P.Phi P.product q 0
  have hgP : ∀ (z : P.S) (s : ℝ) (v w : TangentSpace (𝓡 2) z) (a c : ℝ),
      (Diffeomorph.pullbackMetricCross
          (UniversalCover.liftedMetric (I := I)
            (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0)))
          P.Phi).inner (z, s) (v, a) (w, c) =
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h).inner z v w +
          metricScalarAt (I := 𝓡 2) P.h q * (a * c) := by
    intro z s v w a c
    have hA := Diffeomorph.pullbackMetricCross_inner
      (UniversalCover.liftedMetric (I := I)
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0)))
      P.Phi (z, s) (v, a) (w, c)
    have hB := liftedMetric_scaleMetric_inner (I₁ := I)
      (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0) (P.Phi (z, s))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi (z, s) (v, a))
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I P.Phi (z, s) (w, c))
    have hD : metricScalarAt (I := 𝓡 2) P.h q * (P.h.inner z v w + a * c) =
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h).inner z v w +
          metricScalarAt (I := 𝓡 2) P.h q * (a * c) := by
      rw [scaleMetric_inner]
      ring
    exact hA.trans (hB.trans
      ((congrArg (fun t : ℝ => metricScalarAt (I := 𝓡 2) P.h q * t)
        (P.product z s v w a c)).trans hD))
  have hdist : riemannianEDistOf (I := I)
      (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0))
      (UniversalCover.proj (P.Phi (q, 0)))
      (UniversalCover.proj (P.Phi (y, 0))) ≤ ENNReal.ofReal A := by
    refine le_trans (riemannianEDistOf_proj_le _ (P.Phi (q, 0)) (P.Phi (y, 0))) ?_
    rw [← riemannianEDistOf_pullbackMetricCross
      (UniversalCover.liftedMetric (I := I)
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0)))
      P.Phi (q, 0) (y, 0)]
    exact le_trans (riemannianEDistOf_prodMk_le
      (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) _
      (metricScalarAt (I := 𝓡 2) P.h q) hgP 0 q y) hy
  calc
    curvDerivNorm (I := 𝓡 2) m
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) y ≤
        curvDerivNorm (I := (𝓡 2).prod 𝓘(ℝ, ℝ)) m
          (Diffeomorph.pullbackMetricCross
            (UniversalCover.liftedMetric (I := I)
              (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0)))
            P.Phi) (y, 0) :=
      curvDerivNorm_le_product_real_of_inner_eq
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) _
        (metricScalarAt (I := 𝓡 2) P.h q) hQ hgP m y 0
    _ = curvDerivNorm (I := I) m
        (UniversalCover.liftedMetric (I := I)
          (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0)))
        (P.Phi (y, 0)) :=
      curvDerivNorm_pullbackMetricCross _ P.Phi m (y, 0)
    _ = curvDerivNorm (I := I) m
        (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ (F.S.base.metric 0))
        (UniversalCover.proj (P.Phi (y, 0))) :=
      curvDerivNorm_liftedMetric _ m (P.Phi (y, 0))
    _ ≤ shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A :=
      klim_rescaled_terminal_jet_bound hK hKbound A hA m
        (UniversalCover.proj (P.Phi (q, 0))) (metricScalarAt (I := 𝓡 2) P.h q) hQ hx _ hdist


theorem terminal_surface_factor_local_jets {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) (P : TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) :
    ∀ A : ℝ, 0 < A → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : P.S) (r : ℝ) (hQ : 0 < metricScalarAt (I := 𝓡 2) P.h q),
        (∀ z, (riemannianEDistOf (I := 𝓡 2) P.h z q).toReal < r →
          metricScalarAt (I := 𝓡 2) P.h z ≤ 4 * metricScalarAt (I := 𝓡 2) P.h q) →
        A + 1 / 2 < r * Real.sqrt (metricScalarAt (I := 𝓡 2) P.h q) →
        ∀ y : P.S,
          riemannianEDistOf (I := 𝓡 2)
              (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) q y ≤
            ENNReal.ofReal A →
          curvDerivNorm (I := 𝓡 2) m
            (scaleMetric (metricScalarAt (I := 𝓡 2) P.h q) hQ P.h) y ≤ C := by
  classical
  obtain ⟨K, _hKpos, hKbound⟩ :=
    exists_normalized_klim_spatial_jet_constants (I := I) hdim kappa
  intro A hA m
  refine ⟨max 0 (shiLocalUniformBound 3 m (K A) (Real.sqrt (K A)) * K A), le_max_left _ _, ?_⟩
  intro q _r hQ _hlocal _hexpand y hy
  exact le_trans
    (terminal_surface_factor_jet_le hK P hKbound A hA.le m q hQ y hy) (le_max_right _ _)

end Flow

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
