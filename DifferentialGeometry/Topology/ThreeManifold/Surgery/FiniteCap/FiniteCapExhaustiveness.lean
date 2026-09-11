import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapNeighborhood
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapSeparation
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.FiniteCapComponentIncidence
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.RetainedCoreMaps
import Mathlib.Analysis.Normed.Module.RCLike.Real

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.Manifold.Attachment
namespace DifferentialGeometry.Topology.ThreeManifold.Surgery
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev Ball (L : ℝ) := {x : E3 // ‖x‖ ≤ L}
variable {ι M : Type*} [Finite ι] [TopologicalSpace M] [T2Space M]
variable {precision : ι → ℝ} {L : ℝ}
variable (hL : 0 < L) (hδ : ∀ i, 0 < precision i)
variable (f : ∀ i : ι, bufferedCylinder (precision i) → M)
variable (hf : ∀ i, _root_.Topology.IsOpenEmbedding (f i))
variable (hdisj : Pairwise (fun i j => Disjoint (range (f i)) (range (f j))))
local notation "Q" => FiniteCapQuotient hL hδ f (fun i => _root_.Topology.IsEmbedding.injective (_root_.Topology.IsOpenEmbedding.toIsEmbedding (hf i))) hdisj

omit [Finite ι] [T2Space M] in
theorem finiteCap_core_inter_ball (b : ι × Bool) :
    range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) ∩
      range (fun x : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩) =
        range (fun y : S2 => finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
          (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)) := by
  ext q
  constructor
  · rintro ⟨⟨p, hp⟩, ⟨x, hx⟩⟩
    obtain ⟨⟨c, y⟩, hc, hy⟩ := (adjunctionCell_eq_lower_iff (indexedCapBoundary hL)
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj)
      (injective_indexedCapBoundary hL) ⟨b, x⟩ p).mp (hx.trans hp.symm)
    have hcb : c = b := congrArg Sigma.fst hc
    subst c
    exact ⟨y, (congrArg (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) hy).trans hp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨radialCapBoundary hL y,
      finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩⟩⟩

omit [Finite ι] [T2Space M] in
theorem finiteCap_core_sphere_eq_cap_boundary (b : ι × Bool) :
    range (fun y : S2 => finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
      (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩)) =
      range (fun y : S2 => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj
        ⟨b, radialCapBoundary hL y⟩) := by
  congr 1
  funext y
  exact (finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩).symm

omit [Finite ι] [T2Space M] in
theorem finiteCap_ball_images_disjoint :
    Pairwise (fun b c : ι × Bool => Disjoint
      (range (fun x : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩))
      (range (fun x : Ball L => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨c, x⟩))) := by
  intro b c hbc
  rw [Set.disjoint_left]
  rintro q ⟨x, hx⟩ ⟨y, hy⟩
  exact finiteCapQuotient_different_indices hL hδ f (fun i => (hf i).injective) hdisj b c hbc x y (hx.trans hy.symm)

private theorem closure_ball_inner (hL : 0 < L) :
    closure {x : Ball L | ‖x.val‖ < L} = univ := by
  rw [_root_.Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have he : (Subtype.val : Ball L → E3) '' {x : Ball L | ‖x.val‖ < L} = Metric.ball (0 : E3) L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change ‖y.val‖ < L at hy
      simpa only [Metric.mem_ball, dist_zero_right] using hy
    · intro hx
      have h : ‖x‖ < L := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact ⟨⟨x, h.le⟩, h, rfl⟩
  rw [he, closure_ball (0 : E3) hL.ne']
  ext x
  simp only [mem_preimage, mem_univ, iff_true]
  simpa only [Metric.mem_closedBall, dist_zero_right] using x.property

private theorem cap_not_mem_interior_core (b : ι × Bool) (x : Ball L) :
    finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, x⟩ ∉
      interior (range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)) := by
  let c : Ball L → Q := fun y => finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b, y⟩
  let K := range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)
  have hc : Continuous c := (isClosedEmbedding_finiteCapInclusion hL hδ f hf hdisj).continuous.comp continuous_sigmaMk
  have hx : x ∈ closure {y : Ball L | ‖y.val‖ < L} := by rw [closure_ball_inner hL]; trivial
  have hm : c x ∈ closure (c '' {y : Ball L | ‖y.val‖ < L}) :=
    image_closure_subset_closure_image hc ⟨x, hx, rfl⟩
  have hs : c '' {y : Ball L | ‖y.val‖ < L} ⊆ Kᶜ := by
    rintro q ⟨y, hy, rfl⟩
    exact finiteCapInclusion_not_mem_core_of_norm_lt hL hδ f (fun i => (hf i).injective) hdisj b y hy
  have hn := closure_mono hs hm
  rw [closure_compl] at hn
  exact hn

private theorem old_or_cap (q : Q) :
    q ∈ finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj ∨
      q ∈ range (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  have h := eq_univ_iff_forall.mp (finiteCapQuotient_cover hL hδ f (fun i => (hf i).injective) hdisj) q
  rcases h with h | ⟨p, rfl⟩
  · exact Or.inr h
  · by_cases hp : p.val ∈ interior (cutCore f)
    · exact Or.inl ⟨p, hp, rfl⟩
    · have hfront : p.val ∈ frontier (cutCore f) := ⟨subset_closure p.property, hp⟩
      have hr : p ∈ range (cuttingSphereAttachment hδ f (fun i => (hf i).injective) hdisj) := by
        rw [range_cuttingSphereAttachment hδ f hf hdisj]
        exact hfront
      obtain ⟨a, ha⟩ := hr
      exact Or.inr ⟨indexedCapBoundary hL a,
        (finiteCapQuotient_coherence hL hδ f (fun i => (hf i).injective) hdisj a).trans
          (congrArg (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj) ha)⟩

theorem finiteCoreInclusion_interior_range :
    interior (range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)) =
      finiteCoreInterior hL hδ f (fun i => (hf i).injective) hdisj := by
  apply Subset.antisymm
  · intro q hq
    rcases old_or_cap hL hδ f hf hdisj q with h | ⟨⟨b, x⟩, rfl⟩
    · exact h
    · exact (cap_not_mem_interior_core hL hδ f hf hdisj b x hq).elim
  · exact interior_maximal (image_subset_range _ _) (isOpen_finiteCoreInterior hL hδ f hf hdisj)

theorem finiteCap_compl_interior_core :
    (interior (range (finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj)))ᶜ =
      range (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj) := by
  ext q
  constructor
  · intro hq
    rcases old_or_cap hL hδ f hf hdisj q with h | h
    · rw [finiteCoreInclusion_interior_range hL hδ f hf hdisj] at hq
      exact (hq h).elim
    · exact h
  · rintro ⟨⟨b, x⟩, rfl⟩
    exact cap_not_mem_interior_core hL hδ f hf hdisj b x

variable [LocallyPathConnectedSpace M]

theorem finiteRetained_compl_interior_core (R : Set (ConnectedComponents (cutCore f))) :
    (interior (range (finiteRetainedCoreInclusion hL hδ f hf hdisj R)))ᶜ =
      ⋃ b : {b : ι × Bool // cuttingSphereComponent hδ f hf hdisj b ∈ R},
        range (fun x : Ball L => (⟨finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj ⟨b.val, x⟩, b.property⟩ :
          finiteCapRetained hL hδ f hf hdisj R)) := by
  let U := finiteCapRetained hL hδ f hf hdisj R
  let j := finiteCoreInclusion hL hδ f (fun i => (hf i).injective) hdisj
  have hr : range (finiteRetainedCoreInclusion hL hδ f hf hdisj R) = (Subtype.val : U → Q) ⁻¹' range j := by
    ext q
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.val, rfl⟩
    · rintro ⟨p, hp⟩
      have hpr : p ∈ retainedCore f R := by
        have hq := q.property
        change q.val ∈ (U : Set Q) at hq
        rw [← hp] at hq
        exact hq
      exact ⟨⟨p, hpr⟩, Subtype.ext hp⟩
  have hi := U.isOpen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
    continuous_subtype_val (s := range j)
  have hi' : interior (range (finiteRetainedCoreInclusion hL hδ f hf hdisj R)) =
      (Subtype.val : U → Q) ⁻¹' interior (range j) := (congrArg interior hr).trans hi.symm
  have hc : (interior (range (finiteRetainedCoreInclusion hL hδ f hf hdisj R)))ᶜ =
      (Subtype.val : U → Q) ⁻¹' range (finiteCapInclusion hL hδ f (fun i => (hf i).injective) hdisj) :=
    (congrArg (fun s : Set U => sᶜ) hi').trans
      (congrArg (fun s : Set Q => (Subtype.val : U → Q) ⁻¹' s) (finiteCap_compl_interior_core hL hδ f hf hdisj))
  apply hc.trans
  ext q
  constructor
  · rintro ⟨⟨b, x⟩, hx⟩
    have hb : cuttingSphereComponent hδ f hf hdisj b ∈ R := by
      have hq := q.property
      change q.val ∈ (U : Set Q) at hq
      rw [← hx] at hq
      exact hq
    exact mem_iUnion.mpr ⟨⟨b, hb⟩, x, Subtype.ext hx⟩
  · intro hq
    obtain ⟨b, x, hx⟩ := mem_iUnion.mp hq
    exact ⟨⟨b.val, x⟩, congrArg Subtype.val hx⟩

theorem finiteCapRetained_nonempty_iff_core (R : Set (ConnectedComponents (cutCore f))) :
    Nonempty (finiteCapRetained hL hδ f hf hdisj R) ↔ Nonempty (retainedCore f R) := by
  constructor
  · rintro ⟨q⟩
    obtain ⟨p, _⟩ := finiteCapRetained_component_meets_original_core hL hδ f hf hdisj R q
    exact ⟨p⟩
  · exact Nonempty.map (finiteRetainedCoreInclusion hL hδ f hf hdisj R)
end DifferentialGeometry.Topology.ThreeManifold.Surgery
