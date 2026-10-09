import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.SourceScalarContinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem PointedCGHMaps.eventually_continuousOn_poleEndpoint_scalar_in_chart
    (Φ : PointedCGHMaps Y P phi) (η : ℕ → ℕ) (hη : Tendsto η atTop atTop)
    (x : P.M) {K : Set E} (hK : IsCompact K)
    (hKchart : K ⊆ (extChartAt I x).target) {a c : ℝ} (ha : 1 ≤ a) :
    ∀ᶠ k in atTop,
      ContinuousOn
        (fun z : E × ℝ =>
          ((U).term (phi (η k))).S.scalar (-z.2)
            (Φ.map (η k) ((extChartAt I x).symm z.1)))
        (K ×ˢ Icc a c) := by
  have hchart : ContinuousOn (extChartAt I x).symm K :=
    (continuousOn_extChartAt_symm (I := I) x).mono hKchart
  have hcompact : IsCompact ((extChartAt I x).symm '' K) :=
    hK.image_of_continuousOn hchart
  have hsource := Φ.eventually_continuousOn_scalar η hη
    (J := (Y).D.carrier) Subset.rfl hcompact
  filter_upwards [hsource] with k hk
  have hpair : ContinuousOn
      (fun z : E × ℝ => (1 - z.2, (extChartAt I x).symm z.1))
      (K ×ˢ Icc a c) :=
    (continuousOn_const.sub continuousOn_snd).prodMk
      (hchart.comp continuousOn_fst (fun _ hz => hz.1))
  have hmaps : MapsTo
      (fun z : E × ℝ => (1 - z.2, (extChartAt I x).symm z.1))
      (K ×ˢ Icc a c) ((Y).D.carrier ×ˢ ((extChartAt I x).symm '' K)) := by
    intro z hz
    refine ⟨?_, mem_image_of_mem _ hz.1⟩
    change 1 - z.2 ∈ ancientTimeInterval.carrier
    rw [ancientTimeInterval_carrier]
    change 1 - z.2 ≤ 0
    linarith [hz.2.1]
  have hpull : ContinuousOn
      (fun z : E × ℝ =>
        ((Y).term (phi (η k))).S.scalar (1 - z.2)
          (Φ.map (η k) ((extChartAt I x).symm z.1)))
      (K ×ˢ Icc a c) := by
    simpa only [Function.comp_def] using hk.comp hpair hmaps
  apply hpull.congr
  intro z _
  change metricScalarAt (((U).term (phi (η k))).S.base.metric (-z.2))
      (Φ.map (η k) ((extChartAt I x).symm z.1)) =
    metricScalarAt (((Y).term (phi (η k))).S.base.metric (1 - z.2))
      (Φ.map (η k) ((extChartAt I x).symm z.1))
  rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
  have htime : 1 - z.2 - 1 = -z.2 := by ring
  rw [htime]
  rfl

end DifferentialGeometry.CheegerGromovCompactness
