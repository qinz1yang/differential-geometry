import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapLocalInsertion

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev FullE3 := EuclideanSpace ℝ (Fin 3)
private abbrev FullS2 := Metric.sphere (0 : FullE3) 1
private abbrev FullIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev FullAttachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)

theorem preparedFullCapWidth_bounds (c δ : ℝ) (hc : 4 ≤ c) (hδ : 0 < δ) :
    0 < (c * δ)⁻¹ ∧ (c * δ)⁻¹ < cuttingCollarWidth δ := by
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have htwo : 0 < (2 : ℝ) * δ := mul_pos (by norm_num) hδ
  have hlt : 2 * δ < c * δ := mul_lt_mul_of_pos_right (by linarith) hδ
  refine ⟨inv_pos.mpr (mul_pos hcpos hδ), ?_⟩
  have h := (inv_lt_inv₀ (mul_pos hcpos hδ) htwo).mpr hlt
  simpa only [cuttingCollarWidth, mul_inv_rev, div_eq_mul_inv] using h

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L B : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph FullIC I ∞ (f i))
variable (b : ι × Bool) (hfit : B ≤ cuttingCollarWidth (precision b.1)) (hB : 0 < B)
local notation "FullQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "FullPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b B

def finiteCapFullInsertionDiffeomorph :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    FullPatch ≃ₘ⟮𝓡 3, 𝓡 3⟯ FullAttachment hL hB := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  exact (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b B hfit).trans
    (radialCapAttachmentDiffeomorph hL hB).symm

theorem finiteCapFullInsertionDiffeomorph_apply (q : FullPatch) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB q =
      finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl q := rfl

theorem finiteCapFullInsertionDiffeomorph_symm_cap (x : {v : FullE3 // ‖v‖ ≤ L}) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB).symm
      (adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x) =
        ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩,
          finiteCapInclusion_mem_restrictedNeighborhood hL hδ f hf hdisj b hB x⟩ := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB
  apply D.injective
  exact (D.apply_symm_apply _).trans
    ((finiteCapFullInsertionDiffeomorph_apply I hdim hL hδ f hf hdisj hs b hfit hB _).trans
      (finiteCapInsertionMap_cap I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl hB x)).symm

theorem finiteCapFullInsertionDiffeomorph_symm_collar (q : FullS2 × Ico (0 : ℝ) B) :
    let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    (finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB).symm
      (adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB) q) =
        ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b
            (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩)),
          (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b B _).mpr q.2.property.2⟩ := by
  let : ChartedSpace FullE3 FullQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace FullE3 (FullAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let D := finiteCapFullInsertionDiffeomorph I hdim hL hδ f hf hdisj hs b hfit hB
  apply D.injective
  exact (D.apply_symm_apply _).trans
    ((finiteCapFullInsertionDiffeomorph_apply I hdim hL hδ f hf hdisj hs b hfit hB _).trans
      (finiteCapInsertionMap_collar I hdim hL hδ f hf hdisj hs b B hfit hB le_rfl
        (q.1, ⟨q.2.val, q.2.property.1, q.2.property.2.trans_le hfit⟩) q.2.property.2)).symm
end DifferentialGeometry.Topology.ThreeManifold.Surgery
