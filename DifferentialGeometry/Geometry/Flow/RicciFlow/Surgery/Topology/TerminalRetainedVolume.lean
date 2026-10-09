import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Neck.RetainedVolume

noncomputable section
open Set Filter Manifold MeasureTheory TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : LocallyPathConnectedSpace P.Carrier :=
  DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners ThreeModel
private local instance : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance : BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

theorem TerminalLimitMetric.retained_core_union_negative_bands_volume_le
    (L : G.TerminalLimitMetric) {ι : Type*} [Finite ι] {δ : ι → ℝ}
    (x₀ : ι → G.terminalRegularOpen) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum L.metric (x₀ i) (δ i) (order i))
    (f : ∀ i, bufferedCylinder (δ i) → P.Carrier)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise fun i j => Disjoint (range (f i)) (range (f j)))
    (R : Set (ConnectedComponents (cutCore f)))
    (hRet : MapsTo (Subtype.val : cutCore f → P.Carrier) (retainedCore f R) G.terminalRegularOpen)
    {V : ℝ≥0∞}
    (hV : ∀ᶠ t in 𝓝[<] s,
      riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t) univ ≤ V) :
    riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric
      (range (retainedCoreDomainMap f R G.terminalRegularOpen hRet) ∪
        ⋃ i : ι, (d i).map '' {q | q.val.2 ∈ Icc (-(δ i)⁻¹) (-1 : ℝ)}) ≤ V := by
  apply L.volume_compact_le_of_eventually_volume_le _ hV
  exact isCompact_retained_core_union_negative_bands G.terminalRegularOpen L.metric
    x₀ order d f hf hdisj R hRet

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
