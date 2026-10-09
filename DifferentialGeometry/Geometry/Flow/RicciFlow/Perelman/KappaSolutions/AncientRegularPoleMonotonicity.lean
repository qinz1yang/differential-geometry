import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ReducedVolumeNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Monotonicity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open Filter Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions (intrinsicReducedVolume)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem reducedVolume_antitone_of_regular_base
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p : F.M)
    {T : ℝ} (hT : T ∈ D.regular) :
    AntitoneOn (intrinsicReducedVolume F.S T p) (Ioi 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, _, x, hx⟩ := hF.notFlat
    exact ⟨finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by decide : 0 < 4) (F.S.base.rm04 t x) hx⟩
  let _ : ConnectedSpace F.M := hF.connected
  have hTneg : T < 0 := by simpa only [hF.regular_eq, mem_Iio] using hT
  have hcomplete : RiemannianMetricComplete (I := I) (F.S.base.metric T) :=
    ⟨hF.complete T (D.regular_subset hT)⟩
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  intro tau₁ h₁ tau₂ _ h₁₂
  have hslab : Icc (T - tau₂) T ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, mem_Iio] using ht.2.trans_lt hTneg
  exact DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_anti_of_rm
    (I := I) (D := D) F.S F.isSolution T hcomplete p
    (fun sigma _ hreg => ⟨K, fun t ht x => hK t (D.regular_subset (hreg ht)) x⟩)
    h₁ h₁₂ hslab

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution
