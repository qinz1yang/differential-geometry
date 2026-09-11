import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapOpenChart
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCoreInteriorChart
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]

def modelThreeHomeomorph (hdim : Module.finrank ℝ E = 3) : H ≃ₜ E3 :=
  I.toHomeomorph.trans ((LinearEquiv.ofFinrankEq (R := ℝ) E E3 (by simpa using hdim)).toContinuousLinearEquiv.toHomeomorph)

variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

def finiteCoreThreeChart (x : coreInteriorDomain f) : OpenPartialHomeomorph Q E3 :=
  (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).transHomeomorph (modelThreeHomeomorph I hdim)

theorem finiteCoreThreeChart_source (x : coreInteriorDomain f) :
    (finiteCoreThreeChart I hdim hL hδ f hf hdisj x).source =
      (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x).source := rfl

theorem finiteCoreThreeChart_apply (x p : coreInteriorDomain f) :
    finiteCoreThreeChart I hdim hL hδ f hf hdisj x
      (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj p) =
        modelThreeHomeomorph I hdim (chartAt H x.val p.val) := by
  change modelThreeHomeomorph I hdim
    (finiteCoreOpenChart (H := H) hL hδ f hf hdisj x
      (finiteCoreInteriorMap hL hδ f (fun i => (hf i).injective) hdisj p)) = _
  rw [finiteCoreOpenChart_apply]

def finiteCapAtlas : Set (OpenPartialHomeomorph Q E3) :=
  range (finiteCoreThreeChart I hdim hL hδ f hf hdisj) ∪ range (finiteCapOpenChart hL hδ f hf hdisj)

theorem finiteCapAtlas_covers (q : Q) :
    ∃ e ∈ finiteCapAtlas I hdim hL hδ f hf hdisj, q ∈ e.source := by
  have hq := eq_univ_iff_forall.mp (finiteCapOpenChart_source_cover hL hδ f hf hdisj) q
  rcases hq with hq | hq
  · rw [← finiteCoreOpenChart_source_cover (H := H) hL hδ f hf hdisj] at hq
    obtain ⟨x, hx⟩ := mem_iUnion.mp hq
    exact ⟨finiteCoreThreeChart I hdim hL hδ f hf hdisj x, Or.inl ⟨x, rfl⟩, hx⟩
  · obtain ⟨b, hb⟩ := mem_iUnion.mp hq
    exact ⟨finiteCapOpenChart hL hδ f hf hdisj b, Or.inr ⟨b, rfl⟩, hb⟩

@[instance_reducible] def finiteCapChartedSpace : ChartedSpace E3 Q where
  atlas := finiteCapAtlas I hdim hL hδ f hf hdisj
  chartAt q := Classical.choose (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)
  mem_chart_source q := (Classical.choose_spec (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)).2
  chart_mem_atlas q := (Classical.choose_spec (finiteCapAtlas_covers I hdim hL hδ f hf hdisj q)).1

theorem finiteCapChartedSpace_atlas :
    @ChartedSpace.atlas E3 _ Q _ (finiteCapChartedSpace I hdim hL hδ f hf hdisj) =
      finiteCapAtlas I hdim hL hδ f hf hdisj := rfl

theorem finiteCapQuotient_topological_properties [CompactSpace M] :
    let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    CompactSpace Q ∧ T2Space Q ∧ SecondCountableTopology Q ∧
      LocallyCompactSpace Q ∧ LocallyPathConnectedSpace Q := by
  let : ChartedSpace E3 Q := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : CompactSpace Q := finiteCapQuotient_compactSpace hL hδ f hf hdisj
  exact ⟨inferInstance, finiteCapQuotient_t2Space hL hδ f hf hdisj,
    ChartedSpace.secondCountable_of_sigmaCompact E3 Q,
    ChartedSpace.locallyCompactSpace E3 Q, ChartedSpace.locallyPathConnectedSpace E3 Q⟩
end DifferentialGeometry.Topology.ThreeManifold.Surgery
