import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapChart
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
private abbrev Collar (δ : ℝ) := S2 × Ico (0 : ℝ) (cuttingCollarWidth δ)
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (b : ι × Bool)
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "N" => finiteCapNeighborhood hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj b

private def radialCoordinate (p : N) : E3 := (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p).val
private theorem radialCoordinate_openEmbedding : _root_.Topology.IsOpenEmbedding
    (radialCoordinate hL hδ f hf hdisj b) := by
  have ho : IsOpen {x : E3 | ‖x‖ < L + cuttingCollarWidth (precision b.1)} :=
    isOpen_lt continuous_norm continuous_const
  exact ho.isOpenEmbedding_subtypeVal.comp
    (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).isOpenEmbedding
omit [Finite ι] [T2Space M] in
private theorem neighborhood_nonempty : Nonempty N :=
  ⟨⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, ⟨0, by simp [hL.le]⟩⟩,
    Or.inl ⟨⟨0, by simp [hL.le]⟩, rfl⟩⟩⟩

def finiteCapOpenChart : OpenPartialHomeomorph Q E3 := by
  let : Nonempty N := neighborhood_nonempty hL hδ f hf hdisj b
  let e := (radialCoordinate_openEmbedding hL hδ f hf hdisj b).toOpenPartialHomeomorph
    (radialCoordinate hL hδ f hf hdisj b)
  exact e.lift_openEmbedding (isOpen_finiteCapNeighborhood hL hδ f hf hdisj b).isOpenEmbedding_subtypeVal

theorem finiteCapOpenChart_source : (finiteCapOpenChart hL hδ f hf hdisj b).source = N := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_source,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, image_univ, Subtype.range_coe]

theorem finiteCapOpenChart_target : (finiteCapOpenChart hL hδ f hf hdisj b).target =
    {x : E3 | ‖x‖ < L + cuttingCollarWidth (precision b.1)} := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_target,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  change range (Subtype.val ∘ finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b) = _
  rw [range_comp, (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b).surjective.range_eq,
    image_univ]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem finiteCapOpenChart_apply (p : N) :
    finiteCapOpenChart hL hδ f hf hdisj b p.val =
      (finiteCapNeighborhoodHomeomorph hL hδ f hf hdisj b p).val := by
  simp only [finiteCapOpenChart, OpenPartialHomeomorph.lift_openEmbedding_apply,
    _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply, radialCoordinate]

theorem finiteCapOpenChart_cap (x : Cap L) :
    finiteCapOpenChart hL hδ f hf hdisj b
      (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) = x.val := by
  have he := finiteCapOpenChart_apply hL hδ f hf hdisj b
    ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩, Or.inl ⟨x, rfl⟩⟩
  exact he.trans (finiteCapNeighborhoodHomeomorph_cap hL hδ f hf hdisj b x)

theorem finiteCapOpenChart_collar (q : Collar (precision b.1)) :
    finiteCapOpenChart hL hδ f hf hdisj b
      (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q)) = (L + q.2.val) • q.1.val := by
  have he := finiteCapOpenChart_apply hL hδ f hf hdisj b
    ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q), Or.inr ⟨q, rfl⟩⟩
  exact he.trans (finiteCapNeighborhoodHomeomorph_collar hL hδ f hf hdisj b q)

theorem finiteCapOpenChart_symm_cap (x : Cap L) :
    (finiteCapOpenChart hL hδ f hf hdisj b).symm x.val =
      finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ := by
  have hs : finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ ∈
      (finiteCapOpenChart hL hδ f hf hdisj b).source := by
    rw [finiteCapOpenChart_source]
    exact Or.inl ⟨x, rfl⟩
  have hi := (finiteCapOpenChart hL hδ f hf hdisj b).left_inv hs
  rw [finiteCapOpenChart_cap] at hi
  exact hi

theorem finiteCapOpenChart_symm_collar (q : Collar (precision b.1)) :
    (finiteCapOpenChart hL hδ f hf hdisj b).symm ((L + q.2.val) • q.1.val) =
      finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) := by
  have hs : finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q) ∈
      (finiteCapOpenChart hL hδ f hf hdisj b).source := by
    rw [finiteCapOpenChart_source]
    exact Or.inr ⟨q, rfl⟩
  have hi := (finiteCapOpenChart hL hδ f hf hdisj b).left_inv hs
  rw [finiteCapOpenChart_collar] at hi
  exact hi

theorem pairwise_disjoint_finiteCapOpenChart_sources :
    Pairwise (fun b c : ι × Bool => Disjoint
      (finiteCapOpenChart hL hδ f hf hdisj b).source (finiteCapOpenChart hL hδ f hf hdisj c).source) := by
  simp_rw [finiteCapOpenChart_source]
  exact pairwise_disjoint_finiteCapNeighborhoods hL hδ f (fun i => (hf i).injective) hdisj

theorem finiteCapOpenChart_source_cover :
    finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ∪
      (⋃ b : ι × Bool, (finiteCapOpenChart hL hδ f hf hdisj b).source) = univ := by
  simp_rw [finiteCapOpenChart_source]
  exact finiteCapNeighborhood_cover hL hδ f hf hdisj
end DifferentialGeometry.Topology.ThreeManifold.Surgery
