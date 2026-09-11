import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapRestrictedSmooth
import DifferentialGeometry.Topology.Manifold.Attachment.RadialManifold
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev LocalE3 := EuclideanSpace ℝ (Fin 3)
private abbrev LocalS2 := Metric.sphere (0 : LocalE3) 1
private abbrev LocalIC := (𝓡 2).prod 𝓘(ℝ)
private abbrev LocalAttachment {L B : ℝ} (hL : 0 < L) (hB : 0 < B) :=
  AdjunctionSpace (radialCapBoundary hL) (retainedBoundary hB)
private theorem radialSubset {L r B : ℝ} (h : r ≤ B) :
    finiteCapRestrictedBall L r ≤ finiteCapRestrictedBall L B :=
  fun _ hx => (show ‖_‖ < L + r from hx).trans_le (add_le_add le_rfl h)
private def radialInclusion {L r B : ℝ} (h : r ≤ B) :
    finiteCapRestrictedBall L r → finiteCapRestrictedBall L B := Opens.inclusion (radialSubset h)
private theorem radialInclusion_smooth {L r B : ℝ} (h : r ≤ B) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (radialInclusion (L := L) h) := contMDiff_inclusion (radialSubset h)
private theorem radialInclusion_local {L r B : ℝ} (h : r ≤ B) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (radialInclusion (L := L) h) := by
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _ (radialInclusion_smooth h) _ rfl
  intro x
  change Injective (mfderiv (𝓡 3) (𝓡 3) (Opens.inclusion (radialSubset (L := L) h)) x)
  rw [mfderiv_opens_incl]
  exact fun _ _ he => he

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
variable {ι : Type*} [Finite ι] {precision : ι → ℝ} {L B : ℝ}
variable (hdim : Module.finrank ℝ E = 3) (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
variable (hs : ∀ i, IsLocalDiffeomorph LocalIC I ∞ (f i))
variable (b : ι × Bool) (r : ℝ) (hfit : r ≤ cuttingCollarWidth (precision b.1))
variable (hB : 0 < B) (hstatic : r ≤ B)
local notation "LocalQ" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj
local notation "LocalPatch" => finiteCapRestrictedNeighborhood hL hδ f hf hdisj b r

def finiteCapInsertionMap :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    LocalPatch → LocalAttachment hL hB := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D : LocalAttachment hL hB ≃ₘ⟮𝓡 3, 𝓡 3⟯ finiteCapRestrictedBall L B :=
    radialCapAttachmentDiffeomorph hL hB
  exact D.symm ∘ radialInclusion hstatic ∘ P

theorem contMDiff_finiteCapInsertionMap :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    ContMDiff (𝓡 3) (𝓡 3) ∞ (finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic) := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  exact (radialCapAttachmentDiffeomorph hL hB).symm.contMDiff.comp
    ((radialInclusion_smooth hstatic).comp
      (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).contMDiff)

theorem injective_finiteCapInsertionMap :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    Injective (finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic) := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  have hj : Injective (radialInclusion (L := L) hstatic) := fun _ _ he => Subtype.ext (congrArg (fun x : finiteCapRestrictedBall L B => x.val) he)
  exact (radialCapAttachmentDiffeomorph hL hB).symm.injective.comp
    (hj.comp (finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit).injective)

theorem isLocalDiffeomorph_finiteCapInsertionMap :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic) := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  let P := finiteCapRestrictedDiffeomorph I hdim hL hδ f hf hdisj hs b r hfit
  let D : LocalAttachment hL hB ≃ₘ⟮𝓡 3, 𝓡 3⟯ finiteCapRestrictedBall L B := radialCapAttachmentDiffeomorph hL hB
  dsimp only
  intro q
  exact ((P.isLocalDiffeomorph q).comp (𝓡 3) (finiteCapRestrictedBall L B)
    (radialInclusion_local hstatic (P q))).comp (𝓡 3) (LocalAttachment hL hB)
      (D.symm.isLocalDiffeomorph (radialInclusion hstatic (P q)))

theorem finiteCapInsertionMap_radial (q : LocalPatch) :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    (radialCapAttachmentDiffeomorph hL hB
      (finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic q)).val =
        finiteCapOpenChart hL hδ f hf hdisj b q.val := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  exact congrArg Subtype.val ((radialCapAttachmentDiffeomorph hL hB).apply_symm_apply _)

theorem finiteCapInsertionMap_cap (hr : 0 < r) (x : {v : LocalE3 // ‖v‖ ≤ L}) :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic
      ⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩,
        finiteCapInclusion_mem_restrictedNeighborhood hL hδ f hf hdisj b hr x⟩ =
          adjunctionCell (radialCapBoundary hL) (retainedBoundary hB) x := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  apply (radialCapAttachmentDiffeomorph hL hB).injective
  apply Subtype.ext
  exact (finiteCapInsertionMap_radial I hdim hL hδ f hf hdisj hs b r hfit hB hstatic _).trans
    (finiteCapOpenChart_cap hL hδ f hf hdisj b x)

theorem finiteCapInsertionMap_collar
    (q : LocalS2 × Ico (0 : ℝ) (cuttingCollarWidth (precision b.1))) (hq : q.2.val < r) :
    let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
    let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
    finiteCapInsertionMap I hdim hL hδ f hf hdisj hs b r hfit hB hstatic
      ⟨finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
        (cuttingCollarMap hδ f (fun i => (hf i).injective) hdisj b q),
        (finiteCapRestrictedNeighborhood_collar_iff hL hδ f hf hdisj b r q).mpr hq⟩ =
          adjunctionLower (i := radialCapBoundary hL) (retainedBoundary hB)
            (q.1, ⟨q.2.val, q.2.property.1, hq.trans_le hstatic⟩) := by
  let : ChartedSpace LocalE3 LocalQ := finiteCapChartedSpace I hdim hL hδ f hf hdisj
  let : ChartedSpace LocalE3 (LocalAttachment hL hB) := radialCapAttachmentChartedSpace hL hB
  apply (radialCapAttachmentDiffeomorph hL hB).injective
  apply Subtype.ext
  exact (finiteCapInsertionMap_radial I hdim hL hδ f hf hdisj hs b r hfit hB hstatic _).trans
    (finiteCapOpenChart_collar hL hδ f hf hdisj b q)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
