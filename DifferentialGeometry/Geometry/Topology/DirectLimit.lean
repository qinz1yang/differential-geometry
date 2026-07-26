import Mathlib.Topology.Constructions
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

/-!
# Sequential topological direct limit

The direct limit of a sequence of topological spaces along open embeddings
(MSM135 Chapter 4, "Review of direct limits", `lbl376`–`lbl381`): the quotient of
`Σ k, A k` identifying points that agree at a common later stage, with the quotient
topology.  The stage inclusions `incl ℓ` are injective open embeddings whose ranges
form a monotone open cover; compact subsets of the limit factor through a stage; the
limit of Hausdorff spaces is Hausdorff and of σ-compact spaces is σ-compact.  This is
the topological substrate for the limit manifold `(M∞, g∞)` of Hamilton–Cheeger–Gromov
compactness (MSM135 Theorem 3.9, Step D).

The system is bundled as `SeqSystem`: the transition maps `F h : A k → A ℓ` for
`h : k ≤ ℓ` with `map_self`, `map_map`, and open-embedding fields, mirroring the
algebraic `DirectedSystem` shape.
-/

noncomputable section

universe u

namespace DifferentialGeometry

open Set Topology

/-- A sequence of topological spaces with open-embedding transition maps, bundled with
the directed-system laws.  This is the input of the sequential direct limit.

The open-embedding hypothesis is structural, not cosmetic: it makes the stage ranges open in the
limit.  A merely embedded image would not supply the open cover needed by the direct-limit topology
or by the manifold charts in `DirectLimitManifold`. -/
structure SeqSystem (A : ℕ → Type u) [∀ k, TopologicalSpace (A k)] where
  F : ∀ {k ℓ : ℕ}, k ≤ ℓ → A k → A ℓ
  map_self : ∀ (k : ℕ) (x : A k), F (le_refl k) x = x
  map_map : ∀ {k ℓ m : ℕ} (h1 : k ≤ ℓ) (h2 : ℓ ≤ m) (x : A k),
    F h2 (F h1 x) = F (h1.trans h2) x
  isOpenEmb : ∀ {k ℓ : ℕ} (h : k ≤ ℓ), IsOpenEmbedding (F h)

namespace SeqSystem

variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] (S : SeqSystem A)

/-- Compose adjacent maps from stage `k` to any later stage using `Nat.leRecOn`. -/
def succMap (f : ∀ k, A k → A (k + 1)) {k ℓ : ℕ} (h : k ≤ ℓ) : A k → A ℓ :=
  fun x => Nat.leRecOn h (@fun k => f k) x

/-- The composite of adjacent open embeddings is an open embedding. -/
theorem succMap_isOpenEmb (f : ∀ k, A k → A (k + 1))
    (hf : ∀ k, IsOpenEmbedding (f k)) {k ℓ : ℕ} (h : k ≤ ℓ) :
    IsOpenEmbedding (succMap f h) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      change IsOpenEmbedding (succMap f (Nat.le_refl k))
      have hfun : succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      exact IsOpenEmbedding.id
  | succ ℓ hkℓ ih =>
      have hfun : succMap f (Nat.le.step hkℓ) = f ℓ ∘ succMap f hkℓ := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      exact (hf ℓ).comp ih

/-- Build a sequential direct system from adjacent open embeddings. -/
def ofSucc (f : ∀ k, A k → A (k + 1)) (hf : ∀ k, IsOpenEmbedding (f k)) : SeqSystem A where
  F h := succMap f h
  map_self _ x := Nat.leRecOn_self x
  map_map h₁ h₂ x := (Nat.leRecOn_trans h₁ h₂ x).symm
  isOpenEmb h := succMap_isOpenEmb f hf h

/-- Transition maps do not depend on the proof of `k ≤ ℓ`.  This keeps rewrites across
common-stage choices such as `max k ℓ` from depending on proof-term accidents. -/
theorem F_proof_irrel {k ℓ : ℕ} (h₁ h₂ : k ≤ ℓ) :
    S.F h₁ = S.F h₂ := by
  rw [Subsingleton.elim h₁ h₂]

/-- Pointwise form of `F_proof_irrel`. -/
theorem F_apply_irrel {k ℓ : ℕ} (h₁ h₂ : k ≤ ℓ) (x : A k) :
    S.F h₁ x = S.F h₂ x := by
  rw [S.F_proof_irrel h₁ h₂]

/-- Two stage-points are related when they agree at some common later stage. -/
def Rel (p q : Σ k, A k) : Prop :=
  ∃ (m : ℕ) (hp : p.1 ≤ m) (hq : q.1 ≤ m), S.F hp p.2 = S.F hq q.2

theorem rel_refl (p : Σ k, A k) : S.Rel p p :=
  ⟨p.1, le_refl _, le_refl _, rfl⟩

theorem rel_symm {p q : Σ k, A k} (h : S.Rel p q) : S.Rel q p := by
  obtain ⟨m, hp, hq, he⟩ := h
  exact ⟨m, hq, hp, he.symm⟩

theorem rel_trans {p q r : Σ k, A k} (h1 : S.Rel p q) (h2 : S.Rel q r) : S.Rel p r := by
  obtain ⟨m1, hp1, hq1, e1⟩ := h1
  obtain ⟨m2, hq2, hr2, e2⟩ := h2
  refine ⟨max m1 m2, hp1.trans (le_max_left _ _), hr2.trans (le_max_right _ _), ?_⟩
  have e1' := congrArg (S.F (le_max_left m1 m2)) e1
  have e2' := congrArg (S.F (le_max_right m1 m2)) e2
  rw [S.map_map, S.map_map] at e1'
  rw [S.map_map, S.map_map] at e2'
  exact e1'.trans e2'

/-- The setoid of the sequential direct limit. -/
def setoid : Setoid (Σ k, A k) :=
  ⟨S.Rel, fun p => S.rel_refl p, fun h => S.rel_symm h, fun h1 h2 => S.rel_trans h1 h2⟩

/-- The sequential direct limit: stage-points identified when they agree at a common
later stage, with the quotient topology. -/
def Lim : Type u := Quotient S.setoid

instance : TopologicalSpace S.Lim :=
  instTopologicalSpaceQuotient

/-- The stage inclusion `Iₗ : A ℓ → Lim`. -/
def incl (ℓ : ℕ) : A ℓ → S.Lim :=
  fun x => Quotient.mk S.setoid ⟨ℓ, x⟩

/-- Compatibility: `Iₖ = Iₗ ∘ F` (MSM135 `lbl378` lemma, second half). -/
theorem incl_comp {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k) :
    S.incl ℓ (S.F h x) = S.incl k x := by
  refine Quotient.sound ⟨ℓ, le_refl ℓ, h, ?_⟩
  rw [S.map_self]

/-- The stage inclusions are injective (MSM135 `lbl378` lemma, first half). -/
theorem incl_injective (ℓ : ℕ) : Function.Injective (S.incl ℓ) := by
  intro x y h
  obtain ⟨m, h1, h2, he⟩ := Quotient.exact h
  have h12 : h1 = h2 := rfl
  rw [h12] at he
  exact (S.isOpenEmb h2).injective he

/-- Every point of the limit comes from some stage (MSM135 `lbl381` (1)). -/
theorem exists_incl_eq (z : S.Lim) : ∃ (ℓ : ℕ) (x : A ℓ), S.incl ℓ x = z := by
  obtain ⟨⟨ℓ, x⟩, rfl⟩ := Quotient.exists_rep z
  exact ⟨ℓ, x, rfl⟩

theorem continuous_incl (ℓ : ℕ) : Continuous (S.incl ℓ) :=
  continuous_quot_mk.comp continuous_sigmaMk

/-- The stage inclusions are open maps (MSM135 "an open cover for the direct limit"):
the saturation of `Iₗ(U)` meets stage `m` in the open set
`⋃_{p ≥ m, ℓ} (F_{mp})⁻¹(F_{ℓp}(U))`. -/
theorem incl_isOpenMap (ℓ : ℕ) : IsOpenMap (S.incl ℓ) := by
  intro U hU
  have hsat : IsOpen (Quotient.mk S.setoid ⁻¹' (S.incl ℓ '' U)) := by
    rw [isOpen_sigma_iff]
    intro m
    have hfib : Sigma.mk m ⁻¹' (Quotient.mk S.setoid ⁻¹' (S.incl ℓ '' U)) =
        ⋃ (p : ℕ) (hmp : m ≤ p) (hℓp : ℓ ≤ p), S.F hmp ⁻¹' (S.F hℓp '' U) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_iUnion]
      constructor
      · rintro ⟨x, hxU, heq⟩
        obtain ⟨p, hℓp, hmp, he⟩ := Quotient.exact heq
        exact ⟨p, hmp, hℓp, x, hxU, he⟩
      · rintro ⟨p, hmp, hℓp, x, hxU, he⟩
        exact ⟨x, hxU, Quotient.sound ⟨p, hℓp, hmp, he⟩⟩
    rw [hfib]
    exact isOpen_iUnion fun p => isOpen_iUnion fun hmp => isOpen_iUnion fun hℓp =>
      ((S.isOpenEmb hℓp).isOpenMap U hU).preimage (S.isOpenEmb hmp).continuous
  exact isOpen_coinduced.mpr hsat

/-- The stage inclusions are open embeddings. -/
theorem incl_isOpenEmb (ℓ : ℕ) : IsOpenEmbedding (S.incl ℓ) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap (S.continuous_incl ℓ)
    (S.incl_injective ℓ) (S.incl_isOpenMap ℓ)

/-- The stage ranges grow monotonically. -/
theorem range_incl_mono {k ℓ : ℕ} (h : k ≤ ℓ) :
    Set.range (S.incl k) ⊆ Set.range (S.incl ℓ) := by
  rintro - ⟨x, rfl⟩
  exact ⟨S.F h x, S.incl_comp h x⟩

/-- The stage ranges form a monotone open cover of the limit. -/
theorem iUnion_range_incl : ⋃ ℓ : ℕ, Set.range (S.incl ℓ) = Set.univ := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨ℓ, x, hx⟩ := S.exists_incl_eq z
  exact ⟨ℓ, x, hx⟩

/-- Final-topology criterion for the direct limit: a set is open iff all stage preimages are open. -/
theorem isOpen_iff_incl {U : Set S.Lim} :
    IsOpen U ↔ ∀ k : ℕ, IsOpen (S.incl k ⁻¹' U) := by
  constructor
  · intro hU k
    exact (S.continuous_incl k).isOpen_preimage U hU
  · intro hU
    apply isOpen_coinduced.mpr
    rw [isOpen_sigma_iff]
    intro k
    simpa [incl] using hU k

/-- MSM135 `lbl379` (compact sets in the direct limit): a compact subset of the limit
is the embedded image of a compact subset of some stage. -/
theorem isCompact_exists {K : Set S.Lim} (hK : IsCompact K) :
    ∃ (k : ℕ) (Kk : Set (A k)), IsCompact Kk ∧ K = S.incl k '' Kk := by
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun ℓ : ℕ => Set.range (S.incl ℓ))
    (fun ℓ => (S.incl_isOpenEmb ℓ).isOpen_range)
    (by rw [S.iUnion_range_incl]; exact Set.subset_univ K)
  have hsub : K ⊆ Set.range (S.incl (t.sup id)) := by
    intro z hz
    obtain ⟨ℓ, hℓt, hzℓ⟩ := Set.mem_iUnion₂.mp (ht hz)
    exact S.range_incl_mono (Finset.le_sup (f := id) hℓt) hzℓ
  refine ⟨t.sup id, S.incl (t.sup id) ⁻¹' K, ?_, (Set.image_preimage_eq_of_subset hsub).symm⟩
  have himg : IsCompact (S.incl (t.sup id) '' (S.incl (t.sup id) ⁻¹' K)) := by
    rwa [Set.image_preimage_eq_of_subset hsub]
  exact ((S.incl_isOpenEmb (t.sup id)).isEmbedding.isCompact_iff).mpr himg

/-- Compact subsets of the direct limit lie in one stage range.  This is the finite-subcover
consequence of the increasing open cover by stage ranges. -/
theorem compact_subset_range {K : Set S.Lim} (hK : IsCompact K) :
    ∃ k : ℕ, K ⊆ Set.range (S.incl k) := by
  obtain ⟨k, Kk, _hKk, hK_eq⟩ := S.isCompact_exists hK
  refine ⟨k, ?_⟩
  rw [hK_eq]
  rintro z ⟨x, _hx, rfl⟩
  exact ⟨x, rfl⟩

/-- MSM135 `lbl380`: a sequential direct limit of σ-compact stages is σ-compact. -/
theorem sigmaCompact [∀ k, SigmaCompactSpace (A k)] : SigmaCompactSpace S.Lim := by
  refine ⟨⟨fun n =>
    S.incl (Nat.unpair n).1 '' compactCovering (A (Nat.unpair n).1) (Nat.unpair n).2,
    fun n => ?_, ?_⟩⟩
  · exact (isCompact_compactCovering _ _).image (S.continuous_incl _)
  · ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨ℓ, x, hx⟩ := S.exists_incl_eq z
    have hxcov : x ∈ ⋃ j, compactCovering (A ℓ) j := by
      rw [iUnion_compactCovering]
      exact Set.mem_univ x
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxcov
    refine ⟨Nat.pair ℓ j, ?_⟩
    rw [Nat.unpair_pair]
    exact ⟨x, hj, hx⟩

/-- MSM135 `lbl381` (2): a sequential direct limit of Hausdorff stages is Hausdorff. -/
theorem t2Space [∀ k, T2Space (A k)] : T2Space S.Lim := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨k, a, rfl⟩ := S.exists_incl_eq x
  obtain ⟨ℓ, b, rfl⟩ := S.exists_incl_eq y
  have hax : S.incl (max k ℓ) (S.F (le_max_left k ℓ) a) = S.incl k a :=
    S.incl_comp (le_max_left k ℓ) a
  have hbx : S.incl (max k ℓ) (S.F (le_max_right k ℓ) b) = S.incl ℓ b :=
    S.incl_comp (le_max_right k ℓ) b
  have hab : S.F (le_max_left k ℓ) a ≠ S.F (le_max_right k ℓ) b := by
    intro h
    apply hxy
    rw [← hax, ← hbx, h]
  obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ := t2_separation hab
  refine ⟨S.incl (max k ℓ) '' U, S.incl (max k ℓ) '' V,
    S.incl_isOpenMap _ U hU, S.incl_isOpenMap _ V hV, ?_, ?_, ?_⟩
  · rw [← hax]
    exact Set.mem_image_of_mem _ haU
  · rw [← hbx]
    exact Set.mem_image_of_mem _ hbV
  · exact (Set.disjoint_image_iff (S.incl_injective _)).mpr hUV

/-- The universal property: compatible stage maps descend to the limit. -/
def lift {X : Type*} (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.F h x) = ψ k x) : S.Lim → X :=
  Quotient.lift (fun p : Σ k, A k => ψ p.1 p.2) (by
    rintro ⟨k, x⟩ ⟨ℓ, y⟩ ⟨m, h1, h2, he⟩
    have h := congrArg (ψ m) he
    rwa [hψ h1 x, hψ h2 y] at h)

theorem lift_incl {X : Type*} (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.F h x) = ψ k x)
    (ℓ : ℕ) (x : A ℓ) : S.lift ψ hψ (S.incl ℓ x) = ψ ℓ x := rfl

theorem continuous_lift {X : Type*} [TopologicalSpace X] (ψ : ∀ k, A k → X)
    (hψ : ∀ {k ℓ : ℕ} (h : k ≤ ℓ) (x : A k), ψ ℓ (S.F h x) = ψ k x)
    (hcont : ∀ k, Continuous (ψ k)) : Continuous (S.lift ψ hψ) := by
  apply Continuous.quotient_lift
  exact continuous_sigma fun k => hcont k

/-- Final-topology continuity criterion: a map out of the direct limit is continuous iff its
restrictions to all stages are continuous. -/
theorem continuous_iff_incl {X : Type*} [TopologicalSpace X] {f : S.Lim → X} :
    Continuous f ↔ ∀ k : ℕ, Continuous (f ∘ S.incl k) := by
  constructor
  · intro hf k
    exact hf.comp (S.continuous_incl k)
  · intro hf
    rw [continuous_def]
    intro U hU
    rw [S.isOpen_iff_incl]
    intro k
    simpa [Function.comp_def] using (hf k).isOpen_preimage U hU

end SeqSystem

end DifferentialGeometry
