import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessClosedBallJets


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance originalErrorC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem WindowedModelWitness.strict_original_error_of_time_towers
    {eps kappa : ℝ} {x : M} {t : ℝ} (W : WindowedModelWitness eps kappa S x t)
    (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := W.model.M) (n := ∞) 2)
    (U : Set W.model.M)
    (hball : riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps) ⊆ U)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I3 y,
      A 0 s y v = (S.base.metric s).inner (W.embedding y)
        (mfderiv I3 I3 W.embedding y (v 0)) (mfderiv I3 I3 W.embedding y (v 1)))
    (hB₀ : ∀ s, B 0 s = metricTensorField (W.model.S.base.metric s))
    (J L : Set ℝ)
    (hA : ∀ q s, s ∈ J → ∀ y,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ L → ∀ y,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) L s)
    (hsourceMap : MapsTo (parabolicTime t (S.scalar t x)) (Icc (-modelDepth eps) 0) J)
    (hmodelSub : Icc (-modelDepth eps) 0 ⊆ L)
    (hstrict : ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a (W.comparison.jet b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps) :
    ∀ a b, a + 2 * b ≤ modelOrder eps → ∀ s ∈ Icc (-modelDepth eps) 0,
      ∀ y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps),
        tensor02CovDerivNormWith a
          ((S.scalar t x * (S.scalar t x)⁻¹ ^ b) • A b (t + s / S.scalar t x) - B b s)
          (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let A' := rescaledTensorTimeTower A t (S.scalar t x)
  have hJ : UniqueDiffOn ℝ (Icc (-modelDepth eps) 0) :=
    uniqueDiffOn_Icc (neg_lt_zero.mpr (inv_pos.mpr W.eps_pos))
  have hA' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => A' q r y) (A' (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    hasDerivWithinAt_rescaledTensorTimeTower A t _ hsourceMap hA q s hs y
  have hB' (q : ℕ) (s : ℝ) (hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M) :
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) (Icc (-modelDepth eps) 0) s :=
    (hB q s (hmodelSub hs) y).mono hmodelSub
  have hzero (s : ℝ) (_hs : s ∈ Icc (-modelDepth eps) 0) (y : W.model.M)
      (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius eps))
      (v : Fin 2 → TangentSpace I3 y) :
      W.comparison.pullback s y v - (W.model.S.base.metric s).inner y (v 0) (v 1) =
        A' 0 s y v - B 0 s y v := by
    rw [W.comparison.pullback_eq s y hy v]
    simp only [A', rescaledTensorTimeTower, pow_zero, mul_one, ContMDiffSection.coe_smul,
      Pi.smul_apply, Tensor0SSpace.smul_apply, smul_eq_mul, hA₀ _ y (hball hy) v,
      hB₀, metricTensorField_apply, rescaledMetric, scaleMetric_inner]
  have hjet := W.comparison.jet_eq_of_genuine_towers hJ A' B
    (fun q s hs y _hy => hA' q s hs y) (fun q s hs y _hy => hB' q s hs y) hzero
  have hcomplete : RiemannianMetricComplete (I := I3) (W.model.S.base.metric 0) := by
    refine ⟨?_⟩
    exact MetricComplete.complete (W.model.atTime 0)
      (W.model_ancient.complete 0 (by change (0 : ℝ) ≤ 0; exact le_rfl))
  intro a b hab s hs y hy
  have heq := tensor02CovDerivNormWith_eq_on_riemannianClosedBall
    (W.model.S.base.metric 0) hcomplete W.model.basepoint
    (inv_pos.mpr (Real.sqrt_pos.mpr W.eps_pos))
    (W.model.S.base.metric s) (W.model.S.base.metric s)
    (W.comparison.jet b s) (A' b s - B b s) (fun z hz => hjet b s hs z hz) a hy
  change tensor02CovDerivNormWith a (A' b s - B b s)
    (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps
  rw [← heq]
  exact hstrict a b hab s hs y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
