import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalNeckTransport

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem WindowedModelWitness.exists_strongNeck_of_model
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa alpha : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (nk : StrongNeck W.model.S (neckModelTolerance alpha) W.model.basepoint 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hdelta : delta ≤ neckSourceTolerance alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ modelOrder delta)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹,
      nk.map y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta)) :
    ∃ nk' : StrongNeck S (2 * alpha) x t,
      nk'.map = partialDiffeomorphTransMixed nk.map W.embedding := by
  have hdepth : 1 < modelDepth delta := (one_lt_inv₀ W.eps_pos).mpr W.eps_lt_one
  have htimes : Icc (-1 : ℝ) 0 ⊆ Icc (-modelDepth delta) 0 := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hmodel (s : ℝ) :
      rescaledMetric W.model.S 0 (W.model.S.scalar 0 W.model.basepoint) nk.Q_pos s =
        W.model.S.base.metric s := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    have hscalar : W.model.S.scalar 0 W.model.basepoint = 1 := W.model_scalar_base
    simp only [rescaledMetric, scaleMetric_inner, hscalar, parabolicTime, div_one, zero_add,
      one_mul]
  let cmp : MetricComparisonOn
      (rescaledMetric W.model.S 0 (W.model.S.scalar 0 W.model.basepoint) nk.Q_pos)
      (rescaledMetric S t (S.scalar t x) W.scalar_pos) W.embedding
      (riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta)) (Icc (-1 : ℝ) 0) (modelOrder delta) delta :=
    { pullback := W.comparison.pullback
      pullback_eq := W.comparison.pullback_eq
      jet := W.comparison.jet
      jet_zero := by
        intro s y v
        rw [hmodel s]
        exact W.comparison.jet_zero s y v
      jet_succ := by
        intro b s hs y hy v
        exact ((W.hasDerivWithinAt_comparison_jet_unit hS hreg b hs y hy v).derivWithin
          (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0) s hs)).symm
      equivalence := by
        intro s hs y hy v
        rw [hmodel s]
        exact W.comparison.equivalence s (htimes hs) y hy v
      close := by
        intro a b hab s hs y hy
        rw [hmodel s]
        exact W.comparison.close a b hab s (htimes hs) y hy }
  have hVsource : riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (by linarith : modelRadius delta ≤ modelRadius delta + 1)).trans
      W.buffered_ball
  have htime : Icc (t - (S.scalar t x)⁻¹) t ⊆ D.carrier := by
    have hinv : (S.scalar t x)⁻¹ ≤ (delta * S.scalar t x)⁻¹ :=
      inv_anti₀ (mul_pos W.eps_pos W.scalar_pos)
        (mul_le_of_le_one_left W.scalar_pos.le W.eps_lt_one.le)
    intro s hs
    exact W.window_mem ⟨by linarith [hs.1], hs.2⟩
  apply nk.exists_transport_of_local_comparisons W.scalar_pos W.embedding cmp ha hsmall
    W.eps_pos.le hdelta horder W.base_map houter hVsource htime
  · intro b s hs z hz v
    obtain ⟨y, hy, rfl⟩ := hz
    exact (W.hasDerivWithinAt_comparison_jet_unit hS hreg b hs (nk.map y)
      (houter y hy) v).differentiableWithinAt
  · intro b s hs _hu y hy v
    have hsub := neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact (nk.hasDerivWithinAt_comparison_jet_of_ancient W.model.isSolution b hs y
      (hsub hy) v).differentiableWithinAt

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
