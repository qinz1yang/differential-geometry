import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientAscrInfinite
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AscrCurvatureNormalization

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientAscrAllTimesTopology : TopologicalSpace F.M := F.topology
local instance ancientAscrAllTimesCharted : ChartedSpace H F.M := F.charted
local instance ancientAscrAllTimesSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientAscrAllTimesC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem ancientKappaThree_ascr_eq_top {kappa : ℝ}
    (hF : IsAncientKappaSolution (I := I) kappa F) (hdim : Module.finrank ℝ E = 3)
    (hnoncompact : NoncompactSpace F.M) (t0 : ℝ) (ht0 : t0 ∈ D.carrier) (p : F.M) :
    asymptoticScalarCurvatureRatio (I := I) (F.S.base.metric t0) p = ⊤ := by
  have ht0le : t0 ≤ 0 := by
    simpa only [hF.carrier_eq, Set.mem_Iic] using ht0
  obtain ⟨hQ, hdata⟩ :=
    ancientKappa_exists_curvatureNormalization_ascr F hdim hF t0 ht0le p
  let G := curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
    t0 (F.S.scalar t0 p) hQ ht0 p
  have hG : IsAncientKappaSolution (I := I) kappa G := hdata.1
  have hnoncompactG : @NoncompactSpace G.M G.topology := by
    change @NoncompactSpace F.M F.topology
    exact hnoncompact
  have hascr :
      @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
      (G.S.base.metric 0) p =
      asymptoticScalarCurvatureRatio (F.S.base.metric t0) p := hdata.2.2 p
  calc
    asymptoticScalarCurvatureRatio (F.S.base.metric t0) p =
        @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
          (G.S.base.metric 0) p :=
      hascr.symm
    _ = ⊤ := ancientKappaThree_terminal_ascr_eq_top G hG hdim hnoncompactG p

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
