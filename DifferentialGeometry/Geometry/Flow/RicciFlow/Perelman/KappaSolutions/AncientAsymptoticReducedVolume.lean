import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AsymptoticShrinkerNormalizationReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientReducedVolumeLowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.UpperBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Asymptotic

set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped ContDiff _root_.Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

private theorem ancient_reducedVolume_le_one_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T < 0) (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume F.S T p tau ≤ 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : NeZero (Module.finrank ℝ E) := neZero_finrank_of_isAncientKappaSolution F hF
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric T) :=
    ⟨hF.complete T hT.le⟩
  apply Perelman.redVolume_le_one_of_rm F.S F.isSolution T hcomplete p
    (fun sigma _ hreg => ancientKappa_regularSlabBound_finrank F hF (T - sigma) T hreg) htau
  exact fun t ht => ht.2.trans_lt hT

theorem ancient_reducedVolume_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {T : ℝ} (hT : T ≤ 0) (p : F.M) {tau : ℝ} (htau : 0 < tau) :
    intrinsicReducedVolume F.S T p tau ≤ 1 := by
  rcases hT.lt_or_eq with hT | rfl
  · exact ancient_reducedVolume_le_one_of_regular_base F hF hT p htau
  · let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
    apply le_of_tendsto (ancient_reducedVolume_tendsto_terminal F hF htau p)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ancient_reducedVolume_le_one_of_regular_base F hF ht p htau

theorem ancient_reducedVolume_tendsto_atTop
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    Tendsto (intrinsicReducedVolume F.S 0 p) atTop
      (𝓝 (asymptoticReducedVolume F.S 0 p)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact redVolume_tendsto_atTop_of_antitone F.S 0 p (ancient_reducedVolume_antitone F hF p)

theorem ancient_reducedVolume_tendsto_rescaled
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {α : Type*} {l : Filter α} {tau : α → ℝ} (hescape : Tendsto tau l atTop)
    {theta : ℝ} (htheta : 0 < theta) :
    Tendsto (fun i => intrinsicReducedVolume F.S 0 p (tau i * theta)) l
      (𝓝 (asymptoticReducedVolume F.S 0 p)) :=
  (ancient_reducedVolume_tendsto_atTop F hF p).comp (hescape.atTop_mul_const htheta)

theorem ancient_asymptoticReducedVolume_le_one
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    asymptoticReducedVolume F.S 0 p ≤ 1 :=
  (asymptoticReducedVolume_le_redVolume F.S 0 p one_pos).trans
    (ancient_reducedVolume_le_one F hF le_rfl p one_pos)

theorem ancient_asymptoticReducedVolume_pos
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M) :
    0 < asymptoticReducedVolume F.S 0 p := by
  obtain ⟨v, hv, hbound⟩ := exists_pos_le_ancient_reducedVolume F hF
  exact (ENNReal.ofReal_pos.mpr hv).trans_le
    (le_iInf fun tau : Set.Ioi (0 : ℝ) => hbound p tau tau.property)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
