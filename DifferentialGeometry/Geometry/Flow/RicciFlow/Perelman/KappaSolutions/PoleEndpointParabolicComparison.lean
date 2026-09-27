import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonTimeReflection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointMetricNormalization

section
set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood CanonicalNeighborhood.FiniteHorn
open Surgery.Topology (ThreeSpace)

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem poleEndpointRescaledFlowSeq_parabolicRescale_metric
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (q : ℕ → F.M)
    (hsigma : ∀ i, 0 < tau i + b) (i : ℕ) (s : ℝ) :
    scaleMetric ((tau i + b) / tau i) (div_pos (hsigma i) (htau i))
      (((poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma).term i).S.base.metric
        (s / ((tau i + b) / tau i))) =
      scaleMetric (tau i)⁻¹ (inv_pos.mpr (htau i))
        (F.S.base.metric (-tau i + tau i * s)) := by
  erw [poleEndpointRescaledFlowSeq_metric]
  have htime : -tau i + (tau i + b) * (s / ((tau i + b) / tau i)) =
      -tau i + tau i * s := by field_simp [(htau i).ne', (hsigma i).ne']
  rw [htime]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  change ((tau i + b) / tau i) * ((tau i + b)⁻¹ *
    (F.S.base.metric (-tau i + tau i * s)).inner x v w) =
      (tau i)⁻¹ * (F.S.base.metric (-tau i + tau i * s)).inner x v w
  field_simp [(htau i).ne', (hsigma i).ne']

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_backwardSlice_parabolic_comparison
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {phi : ℕ → ℕ}
    (hphi : StrictMono phi)
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma) P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (T : ℝ) (hT : 0 < T) (K : Set P.M) (hK : IsCompact K)
    (order : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn
      co.gInf
      (fun s => scaleMetric (tau (phi (co.φ i)))⁻¹ (inv_pos.mpr (htau (phi (co.φ i))))
        (F.S.base.metric (-tau (phi (co.φ i)) + tau (phi (co.φ i)) * s)))
      (Phi.map (co.φ i)) K (Icc (-T) 0) order eps) := by
  let c : ℕ → ℝ := fun i => (tau (phi (co.φ i)) + b) / tau (phi (co.φ i))
  have hc (i : ℕ) : 0 < c i := div_pos (hsigma (phi (co.φ i))) (htau (phi (co.φ i)))
  have htauTop : Tendsto (fun i => tau (phi (co.φ i))) atTop atTop :=
    hescape.comp (hphi.tendsto_atTop.comp co.strictMono.tendsto_atTop)
  have hctop : Tendsto c atTop (𝓝 1) := by
    have heq : c = fun i => 1 + b / tau (phi (co.φ i)) := by
      funext i
      dsimp only [c]
      rw [add_div, div_self (htau (phi (co.φ i))).ne']
    rw [heq]
    simpa only [add_zero] using tendsto_const_nhds.add (htauTop.const_div_atTop b)
  filter_upwards [co.eventually_parabolicRescale_fixed_metric_comparison Phi rfl rfl
    c hc hctop T hT K hK order eps heps] with i hi
  obtain ⟨C⟩ := hi
  have hsource : (fun s => scaleMetric (c i) (hc i)
      (((poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma).term
        (phi (co.φ i))).S.base.metric (s / c i))) =
      (fun s => scaleMetric (tau (phi (co.φ i)))⁻¹ (inv_pos.mpr (htau (phi (co.φ i))))
        (F.S.base.metric (-tau (phi (co.φ i)) + tau (phi (co.φ i)) * s))) := by
    funext s
    exact poleEndpointRescaledFlowSeq_parabolicRescale_metric F b hbmem tau htau q hsigma
      (phi (co.φ i)) s
  rw [hsource] at C
  exact ⟨C⟩

theorem _root_.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.eventually_backwardScaledMetric_comparison
    (F : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (b : ℝ) (hbmem : b ∈ ancientTimeInterval.carrier)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {phi : ℕ → ℕ}
    (hphi : StrictMono phi)
    (Phi : PointedCGHMaps
      (poleEndpointRescaledFlowSeq F rfl rfl b hbmem tau q hsigma) P phi)
    {R : SmoothRiemannianMetric I3 P.M} {bf : BumpFamily Phi}
    {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn (fun theta => co.gInf (1 - theta))
      (backwardScaledMetric F.S (tau (phi (co.φ i))) (htau (phi (co.φ i))))
      (Phi.map (co.φ i)) K (Icc (1 : ℝ) 3) order eps) := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let L : SolutionOn (I := I3) (M := P.M) ancientTimeInterval := { base := { metric := co.gInf } }
  have hL : IsSolutionOn L := co.isSolutionOn Phi rfl Subset.rfl
  filter_upwards [co.eventually_backwardSlice_parabolic_comparison F b hbmem tau htau hescape
    q hsigma hphi Phi 2 (by norm_num) K hK order eps heps] with i hi
  obtain ⟨C⟩ := hi
  let v := phi (co.φ i)
  have htime : -tau v ∈ ancientTimeInterval.carrier := neg_nonpos.mpr (htau v).le
  let S := curvatureNormalizedSolution F.S (-tau v) (tau v)⁻¹ (inv_pos.mpr (htau v)) htime
  have hS : IsSolutionOn S := isSolutionOn_curvatureNormalizedSolution F.S F.isSolution rfl rfl
    (-tau v) (tau v)⁻¹ (inv_pos.mpr (htau v)) htime
  have hsource : S.base.metric = fun s => scaleMetric (tau v)⁻¹ (inv_pos.mpr (htau v))
      (F.S.base.metric (-tau v + tau v * s)) := by
    funext s
    change scaleMetric (tau v)⁻¹ (inv_pos.mpr (htau v))
      (F.S.base.metric (parabolicTime (-tau v) (tau v)⁻¹ s)) = _
    rw [parabolicTime, div_inv_eq_mul, mul_comm s]
  have hmap : MapsTo (fun s : ℝ => 1 - s) (Icc (1 : ℝ) 3) (Icc (-2 : ℝ) 0) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  let C0 : MetricComparisonOn L.base.metric S.base.metric (Phi.map (co.φ i)) K
      (Icc (-2 : ℝ) 0) order eps := by rw [hsource]; exact C
  have hdiff : ∀ n s, s ∈ Icc (1 : ℝ) 3 → ∀ y ∈ K,
      ∀ w : Fin 2 → TangentSpace I3 y,
        DifferentiableWithinAt ℝ (fun r => C0.jet n r y w) (Icc (-2 : ℝ) 0) (1 - s) := by
    intro n s hs y hy w
    exact (metricComparison_hasDerivWithinAt S hS L hL rfl rfl C0 (by norm_num)
      le_rfl n _ (hmap hs) y hy w).differentiableWithinAt
  let C' := C0.reflectTime 1 (Icc (1 : ℝ) 3) (uniqueDiffOn_Icc (by norm_num)) hmap hdiff
  have heq : (fun s => scaleMetric (tau v)⁻¹ (inv_pos.mpr (htau v))
      (F.S.base.metric (-tau v + tau v * (1 - s)))) = backwardScaledMetric F.S (tau v) (htau v) := by
    funext s
    dsimp only [backwardScaledMetric]
    congr 2
    ring
  change MetricComparisonOn (fun s => co.gInf (1 - s))
    (fun s => S.base.metric (1 - s)) (Phi.map (co.φ i)) K (Icc (1 : ℝ) 3) order eps at C'
  rw [hsource, heq] at C'
  exact ⟨C'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
