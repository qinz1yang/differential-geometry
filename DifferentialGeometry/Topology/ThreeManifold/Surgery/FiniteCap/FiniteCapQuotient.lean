import DifferentialGeometry.Topology.Manifold.Attachment.AdjunctionInjectivity
import DifferentialGeometry.Topology.Manifold.Attachment.RadialCap
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.CuttingSphereAttachment

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Manifold.Attachment DifferentialGeometry.Geometry.Neck
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Cap (L : ℝ) := {x : E3 // ‖x‖ ≤ L}

abbrev IndexedCaps (ι : Type*) (L : ℝ) := Σ _b : ι × Bool, Cap L

def indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) : CuttingSpheres ι → IndexedCaps ι L :=
  fun p => ⟨p.1, radialCapBoundary hL p.2⟩

theorem injective_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) :
    Injective (indexedCapBoundary (ι := ι) hL) := by
  rintro ⟨i, y⟩ ⟨j, z⟩ he
  have hij : i = j := congrArg Sigma.fst he
  subst j
  have hs : radialCapBoundary hL y = radialCapBoundary hL z := eq_of_heq (Sigma.mk.inj he).2
  have hv := congrArg (fun x : Cap L => L⁻¹ • x.val) hs
  change L⁻¹ • (L • y.val) = L⁻¹ • (L • z.val) at hv
  simp only [smul_smul, inv_mul_cancel₀ hL.ne', one_smul] at hv
  exact congrArg (Sigma.mk i) (Subtype.ext hv)

theorem norm_indexedCapBoundary {ι : Type*} {L : ℝ} (hL : 0 < L) (p : CuttingSpheres ι) :
    ‖(indexedCapBoundary hL p).2.val‖ = L := by
  change ‖L • p.2.val‖ = L
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hp : ‖p.2.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using p.2.property
  rw [hp, mul_one]

variable {ι M : Type*} {precision : ι → ℝ} {L : ℝ}

abbrev FiniteCapQuotient (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :=
  AdjunctionSpace (indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

def finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    IndexedCaps ι L → FiniteCapQuotient hL hδ f hf hdisj :=
  adjunctionCell (indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

def finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    cutCore f → FiniteCapQuotient hL hδ f hf hdisj :=
  adjunctionLower (i := indexedCapBoundary hL) (cuttingSphereAttachment hδ f hf hdisj)

theorem finiteCapQuotient_coherence (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) (p : CuttingSpheres ι) :
    finiteCapInclusion hL hδ f hf hdisj (indexedCapBoundary hL p) =
      finiteCoreInclusion hL hδ f hf hdisj (cuttingSphereAttachment hδ f hf hdisj p) :=
  adjunction_coherence _ _ p

theorem injective_finiteCoreInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Injective (finiteCoreInclusion hL hδ f hf hdisj) :=
  adjunctionLower_injective _ _ (injective_indexedCapBoundary hL)

theorem injective_finiteCapInclusion (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    Injective (finiteCapInclusion hL hδ f hf hdisj) := by
  apply adjunctionCell_injective _ _ (injective_indexedCapBoundary hL)
  intro p q he
  exact injective_cuttingSphereMap hδ f hf hdisj (congrArg Subtype.val he)

theorem finiteCapQuotient_cover (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    range (finiteCapInclusion hL hδ f hf hdisj) ∪ range (finiteCoreInclusion hL hδ f hf hdisj) = univ :=
  adjunction_inclusions_cover _ _

theorem finiteCapQuotient_inter (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    range (finiteCapInclusion hL hδ f hf hdisj) ∩ range (finiteCoreInclusion hL hδ f hf hdisj) =
      range (finiteCapInclusion hL hδ f hf hdisj ∘ indexedCapBoundary hL) :=
  adjunction_inclusions_inter _ _ (injective_indexedCapBoundary hL)

theorem finiteCapQuotient_different_indices (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b c : ι × Bool) (hbc : b ≠ c) (x y : Cap L) :
    finiteCapInclusion hL hδ f hf hdisj ⟨b, x⟩ ≠ finiteCapInclusion hL hδ f hf hdisj ⟨c, y⟩ := by
  intro he
  exact hbc (congrArg Sigma.fst (injective_finiteCapInclusion hL hδ f hf hdisj he))

theorem finiteCapInclusion_not_mem_core_of_norm_lt (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M) (hf : ∀ i, Injective (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
    (b : ι × Bool) (x : Cap L) (hx : ‖x.val‖ < L) :
    finiteCapInclusion hL hδ f hf hdisj ⟨b, x⟩ ∉ range (finiteCoreInclusion hL hδ f hf hdisj) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, _⟩ := (adjunctionCell_eq_lower_iff _ _
    (injective_indexedCapBoundary hL) ⟨b, x⟩ y).mp hy.symm
  have he := congrArg (fun p : IndexedCaps ι L => ‖p.2.val‖) ha
  rw [norm_indexedCapBoundary hL a] at he
  exact (ne_of_lt hx) he.symm

variable [TopologicalSpace M]

theorem finiteCapQuotient_compactSpace [CompactSpace M] [Finite ι]
    (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
    (f : ∀ i : ι, bufferedCylinder (precision i) → M)
    (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
    (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j)))) :
    CompactSpace (FiniteCapQuotient hL hδ f (fun i => (hf i).injective) hdisj) := by
  let : CompactSpace (cutCore f) := isCompact_iff_compactSpace.mp (isCompact_cutCore f hf)
  have hcap : IsCompact {x : E3 | ‖x‖ ≤ L} := by
    simpa only [Metric.closedBall, dist_zero_right] using isCompact_closedBall (0 : E3) L
  let : CompactSpace (Cap L) := isCompact_iff_compactSpace.mp hcap
  infer_instance
end DifferentialGeometry.Topology.ThreeManifold.Surgery
