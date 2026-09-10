import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticScalarRatio
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal

universe u uE uH

section Solution

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

private local instance ascrNormalizationSolutionC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem curvatureNormalizedSolution_ascr
    (S : SolutionOn (I := I) (M := M) D)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (s : ℝ) (p : M) :
    asymptoticScalarCurvatureRatio (I := I) (M := M)
        ((curvatureNormalizedSolution S t0 Q hQ ht0).family.metric s) p =
      asymptoticScalarCurvatureRatio (S.family.metric (parabolicTime t0 Q s)) p := by
  change asymptoticScalarCurvatureRatio
    (scaleMetric Q hQ (S.base.metric (parabolicTime t0 Q s))) p =
      asymptoticScalarCurvatureRatio (S.base.metric (parabolicTime t0 Q s)) p
  exact asymptoticScalarCurvatureRatio_scaleMetric
    (S.base.metric (parabolicTime t0 Q s)) Q hQ p

end Solution

section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ascrNormalizationTopology : TopologicalSpace F.M := F.topology
local instance ascrNormalizationCharted : ChartedSpace H F.M := F.charted
local instance ascrNormalizationSmooth : IsManifold I ∞ F.M := F.smooth
local instance ascrNormalizationC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem curvatureNormalizedFlow_ascr
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier)
    (x0 : F.M) (s : ℝ) (p : F.M) :
    @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
        ((curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0).S.family.metric s) p =
      asymptoticScalarCurvatureRatio (F.S.family.metric (parabolicTime t0 Q s)) p :=
  curvatureNormalizedSolution_ascr F.S t0 Q hQ ht0 s p

theorem curvatureNormalizedFlow_ascr_zero
    (hcar : D.carrier = Set.Iic 0) (hreg : D.regular = Set.Iio 0)
    (t0 Q : ℝ) (hQ : 0 < Q) (ht0 : t0 ∈ D.carrier) (x0 p : F.M) :
    @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
        ((curvatureNormalizedFlow F hcar hreg t0 Q hQ ht0 x0).S.family.metric 0) p =
      asymptoticScalarCurvatureRatio (F.S.family.metric t0) p := by
  rw [curvatureNormalizedFlow_ascr, parabolicTime_zero]

end Pointed

section Ancient

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] ascrNormalizationTopology ascrNormalizationCharted
  ascrNormalizationSmooth ascrNormalizationC1

theorem ancientKappa_exists_curvatureNormalization_ascr {kappa : ℝ}
    (hdim : Module.finrank ℝ E = 3) (hF : IsAncientKappaSolution (I := I) kappa F)
    (t0 : ℝ) (ht0 : t0 ≤ 0) (x0 : F.M) :
    ∃ hQ : 0 < F.S.scalar t0 x0,
      let G := curvatureNormalizedFlow F hF.carrier_eq hF.regular_eq
        t0 (F.S.scalar t0 x0) hQ
        (by simpa only [hF.carrier_eq, Set.mem_Iic] using ht0) x0
      IsAncientKappaSolution (I := I) kappa G ∧
        PointedFlowScalarAtBase (I := I) G 1 ∧
        ∀ p : F.M,
          @asymptoticScalarCurvatureRatio E _ _ _ _ H _ I F.M F.topology F.charted F.smooth
            (G.S.family.metric 0) p =
          asymptoticScalarCurvatureRatio (F.S.family.metric t0) p := by
  have hQ : 0 < F.S.scalar t0 x0 := ancientKappa_scalar_pos F hdim hF ht0 x0
  refine ⟨hQ, ?_⟩
  dsimp only
  refine ⟨isAncientKappaSolution_curvatureNormalizedFlow
      F hF t0 (F.S.scalar t0 x0) hQ _ x0 rfl,
    curvatureNormalizedFlow_scalar_base F hF.carrier_eq hF.regular_eq
      t0 (F.S.scalar t0 x0) hQ _ x0 rfl, ?_⟩
  intro p
  exact curvatureNormalizedFlow_ascr_zero F hF.carrier_eq hF.regular_eq
    t0 (F.S.scalar t0 x0) hQ _ x0 p

end Ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
