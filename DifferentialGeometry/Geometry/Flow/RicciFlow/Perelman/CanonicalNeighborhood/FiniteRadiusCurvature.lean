import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornStructure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalScalarJets

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Geometry.Curvature CheegerGromovCompactness
open Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem FiniteControlledRadius.exists_scalar_upper_bound_on_closedBall
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    (F : FiniteControlledRadius X) {r : ℝ} (hr : 0 ≤ r) (hrF : r < F.radius) :
    ∃ A : ℝ, 0 < A ∧ ∀ i, ∀ y ∈
      riemannianClosedBallOf ((X.term i).S.base.metric 0) (X.term i).basepoint r,
        (X.term i).S.scalar 0 y ≤ A := by
  obtain ⟨A, hA⟩ := F.inner_bound ((r + F.radius) / 2) (by linarith) (by linarith)
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro i y hy
  apply (hA i y ?_).trans (le_max_left _ _)
  have hdist := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  rw [ENNReal.toReal_ofReal hr] at hdist
  change metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y < _
  change (riemannianEDistOf ((X.term i).S.base.metric 0) (X.term i).basepoint y).toReal < _
  linarith

theorem exists_eventually_curvature_bound_below_controlled_radius
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ F : FiniteControlledRadius X, ∀ r : ℝ, 0 ≤ r → r < F.radius →
            ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧ ∀ᶠ i in atTop,
              Icc (-delta) 0 ⊆ (X.interval i).carrier ∧
              Ioo (-delta) 0 ⊆ (X.interval i).regular ∧
              ∀ t ∈ Icc (-delta) 0, ∀ y ∈
                riemannianClosedBallOf ((X.term i).S.base.metric 0) (X.term i).basepoint r,
                curvDerivNormSq (I := I3) 0 ((X.term i).S.base.metric t) y ≤ K := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_eventually_curvature_bound_of_terminal_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hsmall sigma Phi hPhi X F r hr hrF
  obtain ⟨A, _hA, hA⟩ := F.exists_scalar_upper_bound_on_closedBall hr hrF
  have hsigma : 0 < sigma :=
    pos_of_mul_pos_right (X.noncollapse 0).1 (Real.sqrt_nonneg _)
  obtain ⟨delta, K, hdelta, hK, hcurv⟩ :=
    hbound eps heps hsmall sigma hsigma Phi hPhi A
  refine ⟨delta, K, hdelta, hK, ?_⟩
  filter_upwards [hcurv X, X.depth_tendsto.eventually_ge_atTop delta] with i hi hdepth
  refine ⟨?_, ?_, fun t ht y hy => (hi y (hA i y hy)).2 t ht⟩
  · intro t ht
    rw [X.carrier_eq i]
    exact ⟨by linarith [ht.1], ht.2⟩
  · intro t ht
    rw [X.regular_eq i]
    exact ⟨by linarith [ht.1], ht.2⟩

theorem exists_eventually_curvDerivNorm_bound_below_controlled_radius
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          ∀ F : FiniteControlledRadius X, ∀ r : ℝ, 0 ≤ r → r < F.radius →
            ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
              ∀ m : ℕ, ∀ y ∈
                riemannianClosedBallOf ((X.term i).S.base.metric 0) (X.term i).basepoint r,
                curvDerivNorm (I := I3) m ((X.term i).S.base.metric 0) y ≤ C m := by
  obtain ⟨epsStar, hepsStar, hbound⟩ :=
    exists_eventually_curvDerivNorm_bound_of_terminal_scalar_le hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hsmall sigma Phi hPhi X F r hr hrF
  obtain ⟨A, _hA, hA⟩ := F.exists_scalar_upper_bound_on_closedBall hr hrF
  obtain ⟨C, hC, hcurv⟩ := hbound eps heps hsmall sigma Phi hPhi A
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcurv X] with i hi m y hy
  exact hi m y (hA i y hy)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
