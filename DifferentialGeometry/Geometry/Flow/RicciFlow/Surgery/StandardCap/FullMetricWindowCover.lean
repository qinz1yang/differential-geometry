import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CanonicalStaticWindow
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteFullWitnessMap
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapExhaustiveness

noncomputable section
open Set Function TopologicalSpace Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Topology.ThreeManifold.Surgery
open DifferentialGeometry.Topology.Manifold.Attachment
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (standardCapWindow)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {ι : Type*} [Finite ι] {precision : ι → ℝ}
  (hδ : ∀ i, 0 < precision i) (f : ∀ i : ι, bufferedCylinder (precision i) → M)
  (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
  (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
  (hs : ∀ i, IsLocalDiffeomorph IC I ∞ (f i))
  (R : Set (ConnectedComponents (cutCore f))) (c : ℝ) (hc : 4 ≤ c)

local notation "Q" => FiniteCapQuotient transitionEnd_pos hδ f
  (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "Ret" => finiteCapRetained transitionEnd_pos hδ f hf hdisj R
local notation "Boundary" => {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}

variable (U : Opens M) (g : SmoothRiemannianMetric I U)
  (x₀ : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → U) (order : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R} → ℕ)
  (d : ∀ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R}, normalizedDatum g (x₀ b) (c * precision b.val.1) (order b))
  {A D ε : ℝ} {hA : 0 < A} {m : ℕ}

theorem finiteFullWitnessMap_exists_window_preimage_of_notMem_retainedInterior
    (w : ∀ b : Boundary, CanonicalStaticInsertionWitness (d b) A hA D m ε)
    (hD : transitionEnd < D + 1) :
    let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
    let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
    ∀ q : Ret,
      q ∉ interior (range (finiteRetainedCoreInclusion transitionEnd_pos hδ f hf hdisj R)) →
      ∃ b : Boundary, ∃ x : standardCapWindow D,
        ‖x.val‖ ≤ transitionEnd ∧
        finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
          ((w b).window x) = q := by
  let : LocallyPathConnectedSpace M := originalModel_locallyPathConnected I Fact.out
  let : ChartedSpace E3 Q := finiteCapChartedSpace I Fact.out transitionEnd_pos hδ f hf hdisj
  dsimp only
  intro q hq
  have hcap : q ∈ ⋃ b : Boundary,
      range (fun x : {x : E3 // ‖x‖ ≤ transitionEnd} =>
        (⟨finiteCapInclusion transitionEnd_pos hδ f (fun i => (hf i).injective) hdisj
          ⟨b.val, x⟩, b.property⟩ : Ret)) := by
    rw [← finiteRetained_compl_interior_core transitionEnd_pos hδ f hf hdisj R]
    exact hq
  obtain ⟨b, x, hx⟩ := mem_iUnion.mp hcap
  have hplaced : finiteFullWitnessMap I Fact.out transitionEnd_pos hδ f hf hdisj hs R c hc b
      ((w b).data.capMap x) = q := by
    rw [(w b).properties.capMap_eq, (w b).properties.capInclusion_eq]
    apply Subtype.ext
    exact (congrArg (fun p : finiteCapRestrictedNeighborhood transitionEnd_pos hδ f hf hdisj
        b.val ((c * precision b.val.1)⁻¹) => p.val)
      (finiteCapFullInsertionDiffeomorph_symm_cap I Fact.out transitionEnd_pos hδ f hf hdisj
        hs b.val (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).2.le
        (preparedFullCapWidth_bounds c (precision b.val.1) hc (hδ b.val.1)).1 x)).trans
          (congrArg Subtype.val hx)
  have hxD : ‖x.val‖ < D + 1 := x.property.trans_lt hD
  refine ⟨b, ⟨x.val, hxD⟩, x.property, ?_⟩
  have hwindow : (w b).window ⟨x.val, hxD⟩ = (w b).data.capMap x := by
    change (w b).data.windowMap ⟨x.val, hxD⟩ = (w b).data.capMap x
    rw [(w b).properties.windowMap_eq, (w b).properties.capMap_eq,
      (w b).properties.capInclusion_eq]
    exact modelWindowMap_agrees_cap _ _ x hxD
  rw [hwindow]
  exact hplaced

end DifferentialGeometry.PDE.RicciFlow.StandardCap
