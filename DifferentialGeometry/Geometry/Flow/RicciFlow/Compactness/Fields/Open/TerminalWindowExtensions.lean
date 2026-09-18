import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.WindowRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.TimeLipschitz

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def StaticTerminalLimit.windowSequence {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (hdepth : 0 ≤ depthBound) :
    PointedFlowSeq.{u, 0, 0} I3 :=
  X.timeRestrict (RealTimeInterval.closed (-depthBound) 0 (neg_nonpos.mpr hdepth))
    L.carrier_window L.regular_window

@[simp] theorem StaticTerminalLimit.windowSequence_atTime
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    (hdepth : 0 ≤ depthBound) (t : ℝ) :
    (L.windowSequence hdepth).atTime t = X.atTime t := rfl

theorem StaticTerminalLimit.exists_metric_extensions_on_window
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound) :
    let Y := L.windowSequence (hw.le.trans hwd.le)
    let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
    ∃ (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
      (htgt : TargetIsSigmaCompact Phi),
      let G := gSeqExt Phi L.space.metric bf hsrc htgt
      (∀ K : Set L.space.M, IsCompact K → ∀ᶠ i in atTop,
        ∃ U : Set L.space.M, IsOpen U ∧ K ⊆ U ∧
          U ⊆ (L.maps.partialDiffeomorph i).source ∧
          ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
            (G i t).inner x v w = ((X.term (L.subseq i)).S.base.metric t).inner
              (L.maps.partialDiffeomorph i x)
              (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x v)
              (mfderiv I3 I3 (L.maps.partialDiffeomorph i) x w)) ∧
      ∀ i : ℕ, ∀ K : Set L.space.M, IsCompact K → ∀ p : ℕ,
        ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (-width) 0, ∀ t ∈ Icc (-width) 0,
          ∀ q ≤ p, ∀ x ∈ K,
            metricDerivNorm q (G i s) (G i t) L.space.metric x ≤ C * |s - t| := by
  classical
  let Y := L.windowSequence (hw.le.trans hwd.le)
  let Phi := pointedCGHMapsOfManifold Y L.space L.subseq L.maps
  have hsrc : SourceIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Phi.source_open i)
  have htgt : TargetIsSigmaCompact Phi := fun i =>
    DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I3 (Phi.target_open i)
  obtain ⟨bf⟩ := nonempty_bumpFamily Phi
  refine ⟨bf, hsrc, htgt, ?_, ?_⟩
  · intro K hK
    obtain ⟨N, hN⟩ := bf.grow_cover K hK
    filter_upwards [eventually_ge_atTop N] with i hi
    obtain ⟨W, hW, hgrow, hchi⟩ := bf.chi_one i
    refine ⟨W ∩ Phi.source i, hW.inter (Phi.source_open i),
      fun x hx => ⟨hgrow (hN i hi hx), bf.grow_subset i (hN i hi hx)⟩,
      inter_subset_right, ?_⟩
    intro t x hx v w
    have heq := gSeqExt_inner_of_mem Phi L.space.metric bf hsrc htgt i t x hx.2 v w
    rw [hchi x hx.1, one_smul, sub_self, zero_smul, add_zero] at heq
    exact heq.trans
      (KappaSolutions.pointed_srcMetric_inner_eq_pullback Phi hsrc htgt i t x hx.2 v w)
  · intro i K hK p
    let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
    exact exists_metric_extension_time_lipschitz_constant_on_closed_interval
      Phi L.space.metric bf hsrc htgt (a := -width) (b := 0)
      (by linarith)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩) i K hK p

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
