import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardSpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.UniversalKappaConstant

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff ENNReal Topology

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

open DifferentialGeometry.CheegerGromovCompactness

theorem isAncientKappaSolution_of_kappa_le
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {F : PointedFlowData.{u, uE, uH} (I := I) D}
    {kappa kappa' : ℝ} (hF : IsAncientKappaSolution (I := I) kappa F)
    (hpos : 0 < kappa') (hle : kappa' ≤ kappa) :
    IsAncientKappaSolution (I := I) kappa' F := by
  refine
    { kappa_pos := hpos
      carrier_eq := hF.carrier_eq
      regular_eq := hF.regular_eq
      connected := hF.connected
      complete := hF.complete
      nonnegativeCurvatureOperator := hF.nonnegativeCurvatureOperator
      globalScalarBound := hF.globalScalarBound
      noncollapsed := ?_
      notFlat := hF.notFlat }
  intro time B hB
  exact ⟨hpos, (mul_le_mul' (ENNReal.ofReal_le_ofReal hle) le_rfl).trans
    (hF.noncollapsed time B hB).2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

theorem kappaUniformCanonicalClassification_of_ancientModelClassification
    (hgap : ∀ (kappa : ℝ), 0 < kappa →
      ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
        IsAncientKappaSolution (I := I3) kappa P →
          IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P)
    (hclass : ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 44 →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          (IsShrinkingSphericalSpaceFormFlow (I := I3) P ∨
            IsAncientKappaSolution (I := I3) universalKappaConstant P) →
          PointedFlowScalarAtBase (I := I3) P 1 →
            Nonempty (CanonicalWitness P.S (eps / 2) C1 C2 P.basepoint 0))
    (htransfer : ∀ (eps C1 C2 kappa delta : ℝ)
      (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
      (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
      (x : M) (t : ℝ) (W : WindowedModelWitness delta kappa S x t),
      Nonempty (CanonicalWitness W.model.S (eps / 2) C1 C2 W.model.basepoint 0) →
        Nonempty (CanonicalWitness S (eps / 2) C1 C2 x t)) :
    kappaUniformCanonicalClassification.{u} := by
  intro eps heps heps44
  obtain ⟨C1, C2, hC1, hC2, hmain⟩ := hclass eps heps heps44
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa => ?_⟩
  refine ⟨1 / 2, by norm_num, by norm_num, fun M _ _ _ _ _ D S o x t hw => ?_⟩
  obtain ⟨W, _oN, _hO⟩ := hw
  exact htransfer eps C1 C2 kappa (1 / 2) M D S x t W
    (hmain W.model (hgap kappa hkappa W.model W.model_ancient) W.model_scalar_base)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
