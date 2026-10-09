import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base

/-!
# FC39 GROUP G, lane FC39-G-SAFE: saturated tubes of the raw circle bundle

Steps S1 / S6 of the lane sheet (`build-logs/resume/sheet-FC39-G-SAFE.md`; external draft task 58
§一 S1, S6). For `R : CircleBundle W` (`FC39P0Base.lean`), using only the fields `neighborhood`,
`mem_neighborhood`, `trivialization`, `projection_trivialization`:

* `trivInv_GSAFE` — the inverse trivialization at `c` as a continuous map
  `R.neighborhood c × Circle → W`, with `trivInv_mem_fibre_GSAFE` and the surjectivity onto tubes
  `tube_eq_image_GSAFE` (a base set inside the trivialization neighbourhood);
* `fibre_nonempty_GSAFE` — every whole fibre is nonempty;
* `isCompact_tube_GSAFE` — the saturated tube of a COMPACT base set is compact (finitely many
  trivialization neighbourhoods; not "the preimage of a compact set is compact");
* `exists_tube_closure_subset_GSAFE` — **ambient-closure shrinking**: if the whole fibre over `c`
  lies in an open `O ⊆ W`, then inside any open base neighbourhood `V₀ ∋ c` there is an open
  `V ∋ c` whose tube has its closure IN `W` inside `O ∩ tube V₀` (the closure is controlled by the
  compact image of a compact base neighbourhood times the circle);
* `tube_mono_GSAFE`, `tube_disjoint_GSAFE`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}}

namespace CircleBundle

variable (R : CircleBundle W)

theorem tube_mono_GSAFE {V V' : Set R.Base} (h : V ⊆ V') : R.tube V ⊆ R.tube V' :=
  image_mono (preimage_mono h)

theorem tube_disjoint_GSAFE {V V' : Set R.Base} (h : Disjoint V V') :
    Disjoint (R.tube V) (R.tube V') := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
  have hxy : y = x := Subtype.ext hyx
  subst hxy
  exact Set.disjoint_left.1 h hx hy

/-- The inverse trivialization at `c`, as a map into `W`. -/
def trivInv_GSAFE (c : R.Base) : R.neighborhood c × Circle → W.Carrier :=
  fun p => ((R.trivialization c).symm p).1.1

theorem continuous_trivInv_GSAFE (c : R.Base) : Continuous (R.trivInv_GSAFE c) :=
  continuous_subtype_val.comp (continuous_subtype_val.comp (R.trivialization c).symm.continuous)

theorem trivInv_mem_fibre_GSAFE (c : R.Base) (p : R.neighborhood c × Circle) :
    R.trivInv_GSAFE c p ∈ R.fibre (p.1 : R.Base) := by
  refine ⟨((R.trivialization c).symm p).1, ?_, rfl⟩
  have h := R.projection_trivialization c ((R.trivialization c).symm p)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

/-- Every point of the domain over the trivialization neighbourhood is a value of the inverse
trivialization, with the first coordinate its projection. -/
theorem exists_trivInv_eq_GSAFE (c : R.Base) (y : R.domain) (hy : R.proj y ∈ R.neighborhood c) :
    ∃ p : R.neighborhood c × Circle, (p.1 : R.Base) = R.proj y ∧ R.trivInv_GSAFE c p = y := by
  let z : TopologicalSpace.Opens.comap R.proj (R.neighborhood c) := ⟨y, hy⟩
  refine ⟨R.trivialization c z, R.projection_trivialization c z, ?_⟩
  change ((R.trivialization c).symm (R.trivialization c z)).1.1 = y
  rw [Diffeomorph.symm_apply_apply]

theorem tube_eq_image_GSAFE (c : R.Base) {K : Set R.Base} (hK : K ⊆ R.neighborhood c) :
    R.tube K = R.trivInv_GSAFE c '' ((Subtype.val ⁻¹' K) ×ˢ univ) := by
  apply subset_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨p, hp, hpy⟩ := R.exists_trivInv_eq_GSAFE c y (hK hy)
    refine ⟨p, ⟨?_, mem_univ _⟩, hpy⟩
    change (p.1 : R.Base) ∈ K
    rw [hp]
    exact hy
  · rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
    obtain ⟨y, hy, hyx⟩ := R.trivInv_mem_fibre_GSAFE c p
    refine ⟨y, ?_, hyx⟩
    change R.proj y ∈ K
    rw [mem_preimage, mem_singleton_iff] at hy
    rw [hy]
    exact hp

/-- Every whole fibre of the circle bundle is nonempty. -/
theorem fibre_nonempty_GSAFE (c : R.Base) : (R.fibre c).Nonempty :=
  ⟨_, R.trivInv_mem_fibre_GSAFE c (⟨c, R.mem_neighborhood c⟩, 1)⟩

theorem isCompact_tube_of_subset_GSAFE (c : R.Base) {K : Set R.Base} (hKc : IsCompact K)
    (hK : K ⊆ R.neighborhood c) : IsCompact (R.tube K) := by
  rw [R.tube_eq_image_GSAFE c hK]
  refine IsCompact.image (IsCompact.prod ?_ isCompact_univ) (R.continuous_trivInv_GSAFE c)
  rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe,
    inter_eq_left.2 hK]
  exact hKc

/-- **The saturated tube of a compact base set is compact.** -/
theorem isCompact_tube_GSAFE {K : Set R.Base} (hK : IsCompact K) : IsCompact (R.tube K) := by
  have : LocallyCompactSpace R.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) R.Base
  have hloc : ∀ c ∈ K, ∃ L : Set R.Base, IsCompact L ∧ c ∈ interior L ∧
      L ⊆ R.neighborhood c := fun c _ =>
    exists_compact_subset (R.neighborhood c).isOpen (R.mem_neighborhood c)
  choose! L hLc hcL hLN using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover (fun c => interior (L c))
    (fun c hc => isOpen_interior.mem_nhds (hcL c hc))
  have heq : R.tube K = ⋃ c ∈ t, R.tube (K ∩ L c) := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.1 (hcover hy)
      exact mem_iUnion₂.2 ⟨c, hc, y, ⟨hy, interior_subset hyc⟩, rfl⟩
    · exact iUnion₂_subset fun c _ => R.tube_mono_GSAFE inter_subset_left
  rw [heq]
  exact t.isCompact_biUnion fun c hc =>
    R.isCompact_tube_of_subset_GSAFE c (hK.inter_right (hLc c (htK c hc)).isClosed)
      (inter_subset_right.trans (hLN c (htK c hc)))

/-- **Ambient-closure shrinking of saturated tubes.** If the whole fibre over `c` lies in the open
set `O` of `W`, then inside every open base neighbourhood `V₀` of `c` there is an open `V ∋ c`
whose tube has its closure in `W` contained in `O ∩ tube V₀`. -/
theorem exists_tube_closure_subset_GSAFE (c : R.Base) {O : Set W.Carrier} (hO : IsOpen O)
    (hcO : R.fibre c ⊆ O) {V₀ : Set R.Base} (hV₀ : IsOpen V₀) (hc : c ∈ V₀) :
    ∃ V : Set R.Base, IsOpen V ∧ c ∈ V ∧ V ⊆ V₀ ∧ closure (R.tube V) ⊆ O ∩ R.tube V₀ := by
  have : LocallyCompactSpace R.Base :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 2)) R.Base
  let c' : R.neighborhood c := ⟨c, R.mem_neighborhood c⟩
  have hA : IsOpen (R.trivInv_GSAFE c ⁻¹' O) := hO.preimage (R.continuous_trivInv_GSAFE c)
  have hsub : ({c'} : Set (R.neighborhood c)) ×ˢ (univ : Set Circle) ⊆
      R.trivInv_GSAFE c ⁻¹' O := by
    rintro ⟨m, z⟩ ⟨hm, -⟩
    rw [mem_singleton_iff] at hm
    subst hm
    exact hcO (R.trivInv_mem_fibre_GSAFE c (c', z))
  obtain ⟨u, v, hu, -, hcu, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hA hsub
  have hu' : IsOpen (Subtype.val '' u : Set R.Base) :=
    (R.neighborhood c).isOpen.isOpenMap_subtype_val u hu
  obtain ⟨K, hK, hcK, hKsub⟩ :=
    exists_compact_subset (hV₀.inter hu') ⟨hc, c', hcu (mem_singleton c'), rfl⟩
  have hKN : K ⊆ R.neighborhood c := fun x hx => by
    obtain ⟨m, -, rfl⟩ := (hKsub hx).2
    exact m.2
  refine ⟨interior K, isOpen_interior, hcK,
    interior_subset.trans (hKsub.trans inter_subset_left), ?_⟩
  have hcl : closure (R.tube (interior K)) ⊆ R.tube K :=
    closure_minimal (R.tube_mono_GSAFE interior_subset)
      (R.isCompact_tube_of_subset_GSAFE c hK hKN).isClosed
  refine hcl.trans (subset_inter ?_ (R.tube_mono_GSAFE (hKsub.trans inter_subset_left)))
  rw [R.tube_eq_image_GSAFE c hKN]
  rintro _ ⟨p, ⟨hp, -⟩, rfl⟩
  have hpu : p.1 ∈ u := by
    obtain ⟨m, hm, hm'⟩ := (hKsub hp).2
    have hmp : m = p.1 := Subtype.ext hm'
    rw [← hmp]
    exact hm
  exact huv ⟨hpu, hv (mem_univ _)⟩

end CircleBundle

end GC.GraphManifold.Assembly.FC39P0
