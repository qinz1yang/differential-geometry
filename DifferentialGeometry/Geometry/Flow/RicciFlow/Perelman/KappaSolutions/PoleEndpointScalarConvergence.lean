import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.ClosedIntervalScalarConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RegularPoleRescalings
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
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
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

theorem HalfLineMetricConvergenceData.tendstoUniformlyOn_poleEndpoint_scalar
    (Phi : PointedCGHMaps Y P phi) (R : SmoothRiemannianMetric I P.M)
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {a c : ℝ} (ha : 1 ≤ a) {K : Set P.M} (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun k (z : ℝ × P.M) =>
        ((U).term (phi (co.φ k))).S.scalar (-z.1) (Phi.map (co.φ k) z.2))
      (fun z => metricScalarAt (co.gInf (1 - z.1)) z.2) atTop (Icc a c ×ˢ K) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨n, hn⟩ := exists_nat_ge (c - 1)
  have hslab : Icc (-(n : ℝ)) 0 ⊆ (Y).D.carrier := by
    intro s hs
    change s ∈ ancientTimeInterval.carrier
    simpa only [ancientTimeInterval_carrier, mem_Iic] using hs.2
  have hregular : Ico (-(n : ℝ)) 0 ⊆ (Y).D.regular := by
    intro s hs
    change s ∈ ancientTimeInterval.regular
    simpa only [ancientTimeInterval_regular, mem_Iio] using hs.2
  have hconv := FlowMetricConvergenceData.tendstoUniformlyOn_scalar_on_closed_interval
    Phi R bf hsrc htgt (HalfLineMetricConvergenceData.atWindow Phi co n) hslab hregular hK
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro epsilon hepsilon
  filter_upwards [hconv epsilon hepsilon] with k hk
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  have hs : (1 - t, x) ∈ Icc (-(n : ℝ)) 0 ×ˢ K := by
    exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hx⟩
  have hscalar : ((Y).term (phi (co.φ k))).S.scalar (1 - t)
        (Phi.map (co.φ k) x) =
      ((U).term (phi (co.φ k))).S.scalar (-t) (Phi.map (co.φ k) x) := by
    change metricScalarAt (((Y).term (phi (co.φ k))).S.base.metric (1 - t))
        (Phi.map (co.φ k) x) =
      metricScalarAt (((U).term (phi (co.φ k))).S.base.metric (-t))
        (Phi.map (co.φ k) x)
    rw [poleEndpointRescaledFlowSeq_metric_eq_shift]
    have htime : 1 - t - 1 = -t := by ring
    rw [htime]
    rfl
  simpa only [HalfLineMetricConvergenceData.atWindow, Function.comp_apply, hscalar] using
    hk (1 - t, x) hs

end DifferentialGeometry.CheegerGromovCompactness
