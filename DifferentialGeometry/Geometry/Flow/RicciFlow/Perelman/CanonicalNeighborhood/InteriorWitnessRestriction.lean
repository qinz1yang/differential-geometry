import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessRestriction


set_option autoImplicit false

noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}


def WindowedModelWitness.mono_of_interior_regular
    (hS : IsSolutionOn S) (hregular : interior D.carrier ⊆ D.regular)
    {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hde : delta ≤ eps) (he : eps < 1) :
    WindowedModelWitness eps kappa S x t := by
  apply W.mono_of_regular hS hde he
  intro s hs
  apply hregular
  apply interior_mono W.window_mem
  rw [interior_Icc]
  have hl := div_lt_div_of_pos_right hs.1 W.scalar_pos
  have hr := div_neg_of_neg_of_pos hs.2 W.scalar_pos
  constructor
  · simpa only [parabolicTime, modelDepth, div_eq_mul_inv, mul_inv, neg_mul, sub_eq_add_neg]
      using add_lt_add_right hl t
  · change t + s / S.scalar t x < t
    linarith


theorem WindowedModelWitness.mono_strict_of_interior_regular
    (hS : IsSolutionOn S) (hregular : interior D.carrier ⊆ D.regular)
    {delta eps kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hde : delta ≤ eps) (he : eps < 1)
    (hstrict : ∀ a b : ℕ, a + 2 * b ≤ modelOrder delta →
      ∀ s ∈ Set.Icc (-modelDepth delta) 0,
        ∀ y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius delta),
          tensor02CovDerivNormWith (I := I3) a (W.comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < delta) :
    ∀ a b : ℕ, a + 2 * b ≤ modelOrder eps →
      ∀ s ∈ Set.Icc (-modelDepth eps) 0,
        ∀ y ∈ riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
          W.model.basepoint (modelRadius eps),
          tensor02CovDerivNormWith (I := I3) a
            ((W.mono_of_interior_regular hS hregular hde he).comparison.jet b s)
            (W.model.S.base.metric s) (W.model.S.base.metric s) y < eps := by
  intro a b hab s hs y hy
  have ht : s ∈ Set.Icc (-modelDepth delta) 0 :=
    ⟨(neg_le_neg (modelDepth_anti W.eps_pos hde)).trans hs.1, hs.2⟩
  have hy' := riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
    (modelRadius_anti W.eps_pos hde) hy
  exact (hstrict a b (hab.trans (modelOrder_anti W.eps_pos hde)) s ht y hy').trans_le hde


theorem orientedWitness_mono_of_interior_regular
    (hS : IsSolutionOn S) (hregular : interior D.carrier ⊆ D.regular)
    (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1)
    {x : M} {t : ℝ} (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  obtain ⟨W, oN, hO⟩ := hw
  exact ⟨W.mono_of_interior_regular hS hregular hde he, oN, hO⟩


theorem orientedWitness_mono_closedOpen {a b : ℝ} {hab : a < b}
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen a b hab))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M)
    {delta eps kappa : ℝ} (hde : delta ≤ eps) (he : eps < 1)
    {x : M} {t : ℝ} (hw : OrientedWitness S o delta kappa x t) :
    OrientedWitness S o eps kappa x t := by
  apply orientedWitness_mono_of_interior_regular hS ?_ o hde he hw
  change interior (Set.Ico a b) ⊆ Set.Ioo a b
  rw [interior_Ico]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
