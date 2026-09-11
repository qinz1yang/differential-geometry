import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessModelRecenter


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance recenterConstructionC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem WindowedModelWitness.exists_recentered_strict_of_time_towers
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (z : W.model.M) (t' : ℝ)
    (hc : 0 < W.model.S.scalar 0 z) (hQ : 0 < S.scalar t' (W.embedding z))
    (ht' : t' ∈ D.carrier)
    (hwindow : Icc (t' - (eps * S.scalar t' (W.embedding z))⁻¹) t' ⊆ D.carrier)
    (U : Set W.model.M) (hU : U ⊆ W.embedding.source)
    (hbuffer : riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z
      (modelRadius eps + 1) ⊆ W.embedding.source)
    (hcompare : riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z
      (modelRadius eps) ⊆ U)
    (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := W.model.M) (n := ∞) 2)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I3 y,
      A 0 s y v = (S.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)))
    (hB₀ : ∀ s, B 0 s = metricTensorField (W.model.S.base.metric s))
    (J L : Set ℝ)
    (hA : ∀ q s, s ∈ J → ∀ y,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ L → ∀ y,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s)
    (hsourceMap : MapsTo (parabolicTime t' (S.scalar t' (W.embedding z))) (Icc (-modelDepth eps) 0) J)
    (hmodelMap : MapsTo (parabolicTime 0 (W.model.S.scalar 0 z)) (Icc (-modelDepth eps) 0) L)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps),
        tensor02CovDerivNormWith (I := I3) a
          (rescaledTensorTimeTower A t' (S.scalar t' (W.embedding z)) b s -
            rescaledTensorTimeTower B 0 (W.model.S.scalar 0 z) b s)
          (rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc s)
          (rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc s) y < eps) :
    ∃ W' : WindowedModelWitness eps kappa S (W.embedding z) t',
      ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (W'.model.S.base.metric 0) W'.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith (I := I3) a (W'.comparison.jet b s)
            (W'.model.S.base.metric s) (W'.model.S.base.metric s) y < eps := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := curvatureNormalizedFlow W.model W.model_ancient.carrier_eq
    W.model_ancient.regular_eq 0 (W.model.S.scalar 0 z) hc
    (by change (0 : ℝ) ≤ 0; exact le_rfl) z
  have hP : IsAncientKappaSolution kappa P :=
    isAncientKappaSolution_curvatureNormalizedFlow W.model W.model_ancient
      0 _ hc (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl
  have hPbase : PointedFlowScalarAtBase P 1 :=
    curvatureNormalizedFlow_scalar_base W.model W.model_ancient.carrier_eq
      W.model_ancient.regular_eq 0 _ hc (by change (0 : ℝ) ≤ 0; exact le_rfl) z rfl
  let h := rescaledMetric W.model.S 0 (W.model.S.scalar 0 z) hc
  let g := rescaledMetric S t' (S.scalar t' (W.embedding z)) hQ
  let A' := rescaledTensorTimeTower A t' (S.scalar t' (W.embedding z))
  let B' := rescaledTensorTimeTower B 0 (W.model.S.scalar 0 z)
  let V := riemannianClosedBallOf (h 0) z (modelRadius eps)
  have hVU : V ⊆ U := by
    simpa only [V, h, rescaledMetric, parabolicTime_zero] using hcompare
  have hbuff : riemannianClosedBallOf (h 0) z (modelRadius eps + 1) ⊆ W.embedding.source := by
    simpa only [h, rescaledMetric, parabolicTime_zero] using hbuffer
  have hA'₀ (s : ℝ) (y : W.model.M) (hy : y ∈ V) (v : Fin 2 → TangentSpace I3 y) :
      A' 0 s y v = (g s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)) := by
    simp only [A', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hA₀ _ y (hVU hy) v,
      g, rescaledMetric, scaleMetric_inner]
  have hB'₀ (s : ℝ) (y : W.model.M) (v : Fin 2 → TangentSpace I3 y) :
      B' 0 s y v = (h s).inner y (v 0) (v 1) := by
    simp only [B', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hB₀, metricTensorField_apply,
      h, rescaledMetric, scaleMetric_inner]
  have hA' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => A' q r y) (A' (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower A t' _ hsourceMap hA q s hs y
  have hB' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => B' q r y) (B' (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower B 0 _ hmodelMap hB q s hs y
  have hbound (a b : ℕ) (hab : a + 2 * b ≤ modelOrder eps)
      (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) (hy : y ∈ V) :
      tensor02CovDerivNormWith a (A' b s - B' b s) (h s) (h s) y ≤ eps := by
    have hy' : y ∈ riemannianClosedBallOf
        (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps) := by
      simpa only [V, h, rescaledMetric, parabolicTime_zero] using hy
    exact (hstrict a b hab s hs y hy').le
  let C := metricComparisonOnOfGenuineTimeTowers h g W.embedding V (Icc (-modelDepth eps) 0)
    (uniqueDiffOn_Icc (neg_lt_zero.mpr (inv_pos.mpr W.eps_pos))) (modelOrder eps) eps
    A' B' hA'₀ hB'₀ (fun q s hs y _hy => hA' q s hs y)
    (fun q s hs y _hy => hB' q s hs y) hbound
  have hcomplete : RiemannianMetricComplete (I := I3) (h 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (P.atTime 0) (hP.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  have htime : (0 : ℝ) ∈ Icc (-modelDepth eps) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  obtain ⟨eta, heta, hcapture⟩ := MetricComparisonOn.exists_source_capture_reserve h g W.embedding z
    htime W.eps_pos W.eps_lt_one C
    (RiemannianMetricComplete.closedEBall_isCompact hcomplete z (modelRadius eps)) (hVU.trans hU)
  let W' : WindowedModelWitness eps kappa S (W.embedding z) t' := {
    eps_pos := W.eps_pos
    eps_lt_one := W.eps_lt_one
    time_mem := ht'
    scalar_pos := hQ
    window_mem := hwindow
    model := P
    model_ancient := hP
    model_scalar_base := hPbase
    embedding := W.embedding
    buffered_ball := hbuff
    base_map := rfl
    comparison := C
    source_capture := by
      intro q hq
      have hq' : q ∈ riemannianClosedBallOf (g 0) (W.embedding z) (modelRadius eps - 1 + eta) := by
        change riemannianEDistOf (g 0) (W.embedding z) q ≤ ENNReal.ofReal (modelRadius eps - 1 + eta)
        exact (le_of_lt hq).trans (ENNReal.ofReal_le_ofReal (by linarith))
      obtain ⟨y, hy, hyq⟩ := hcapture hq'
      exact ⟨y, hU (hVU hy), hyq⟩ }
  refine ⟨W', ?_⟩
  intro a b hab s hs y hy
  change y ∈ V at hy
  have hy' : y ∈ riemannianClosedBallOf
      (scaleMetric (W.model.S.scalar 0 z) hc (W.model.S.base.metric 0)) z (modelRadius eps) := by
    simpa only [V, h, rescaledMetric, parabolicTime_zero] using hy
  exact hstrict a b hab s hs y hy'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
