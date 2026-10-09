import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcTraceComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcAnnulus

/-!
# FC39 GROUP G arcs (A5, A7, A8): the arc layer — `stub_exists_arcLayer` proved

Lane FC39-G-ARC (external draft 58 §四 A5–A8, disposition D58-5). For ANY `A`, `sf` and ANY
handle-end layer `HE` (the frozen target keeps all parameters):

* A5 — the arcs and loops are enumerated ONCE: for each partitioned face `f` the unrounded trace of
  its defining function (`traceIdx_GARC`) is split into embedded arcs and circles
  (`CircleRegion.exists_trace_arcs_loops_GARC`); the global index is `Σ f, Fin (count f)`; owners,
  defining functions and faces are read from the same enumeration;
* A6 — the annuli (`CircleRegion.exists_annulus_GARC`);
* A7 — the endpoint map `arcEnd_GARC` (an end of an arc is a second zero, hence the corner point of
  an end whose handle face is the owner: `exists_handle_of_traceBd_GARC`) is a BIJECTION
  `arcs × Bool ≃ ends` (`arcEndEquiv_GARC`), and `handleArc` is read from its inverse;
  `endDisk ∩ R = ` the fibre over the corner point;
* A8 — disjointness and the two partition fields.

`exists_arcLayer_GARC` is the frozen statement `stub_exists_arcLayer` (`Targets.lean.txt:349–356`).
Never through FC40; cheap regression `arcFaceCount_eq_handleCount_GARC` from the bijection.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
  {Pr : FC39PreparedV2 W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
  {V : VertexLayer W} {vlink : VertexModelLink Pr.rows V} {O : PortLayer W E V}
  {circ' : CircleRegion W} {S : SeamLayer W V circ'} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-! ## A5: the per-face arcs and loops -/

/-- The partitioned faces. -/
abbrev PFace_GARC (F : FaceLayer W E V S O) : Type :=
  {f : Fin F.faceCount // F.faceKind f = .partitioned}

noncomputable instance instFintypePFace_GARC : Fintype (PFace_GARC F) :=
  Fintype.ofFinite _

/-- The defining function of the trace of a partitioned face. -/
def AdaptedEdgeRimDataV2.traceIdx_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) : Fin A.circ.definingCount :=
  A.defIndex_GARC (sf.resLabel_GARC f)

/-- Number of arcs of the face `f`. -/
def AdaptedEdgeRimDataV2.fArcN_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) : ℕ :=
  (A.circ.exists_trace_arcs_loops_GARC (A.traceIdx_GARC sf f)).choose

/-- Number of loops of the face `f`. -/
def AdaptedEdgeRimDataV2.fLoopN_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) : ℕ :=
  (A.circ.exists_trace_arcs_loops_GARC (A.traceIdx_GARC sf f)).choose_spec.choose

/-- The arcs of the face `f`. -/
def AdaptedEdgeRimDataV2.fArc_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) :
    Fin (A.fArcN_GARC sf f) → Icc (0 : ℝ) 1 → A.circ.Base :=
  (A.circ.exists_trace_arcs_loops_GARC (A.traceIdx_GARC sf f)).choose_spec.choose_spec.choose

/-- The loops of the face `f`. -/
def AdaptedEdgeRimDataV2.fLoop_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) :
    Fin (A.fLoopN_GARC sf f) → Circle → A.circ.Base :=
  (A.circ.exists_trace_arcs_loops_GARC
    (A.traceIdx_GARC sf f)).choose_spec.choose_spec.choose_spec.choose

theorem AdaptedEdgeRimDataV2.fArc_spec_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) :
    (∀ a, IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (A.fArc_GARC sf f a)) ∧
      (∀ a, IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (A.fLoop_GARC sf f a)) ∧
      (Pairwise fun a a' =>
        Disjoint (range (A.fArc_GARC sf f a)) (range (A.fArc_GARC sf f a'))) ∧
      (Pairwise fun a a' =>
        Disjoint (range (A.fLoop_GARC sf f a)) (range (A.fLoop_GARC sf f a'))) ∧
      (∀ a a', Disjoint (range (A.fArc_GARC sf f a)) (range (A.fLoop_GARC sf f a'))) ∧
      (⋃ a, range (A.fArc_GARC sf f a)) ∪ (⋃ a, range (A.fLoop_GARC sf f a)) =
        A.circ.traceSet_GARC (A.traceIdx_GARC sf f) ∧
      (∀ a t, A.circ.traceBd_GARC (A.traceIdx_GARC sf f) (A.fArc_GARC sf f a t) ↔
        (t = iccEnd false ∨ t = iccEnd true)) ∧
      ∀ a z, ¬ A.circ.traceBd_GARC (A.traceIdx_GARC sf f) (A.fLoop_GARC sf f a z) :=
  (A.circ.exists_trace_arcs_loops_GARC
    (A.traceIdx_GARC sf f)).choose_spec.choose_spec.choose_spec.choose_spec

theorem AdaptedEdgeRimDataV2.range_fArc_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) (a : Fin (A.fArcN_GARC sf f)) :
    range (A.fArc_GARC sf f a) ⊆ A.circ.traceSet_GARC (A.traceIdx_GARC sf f) := by
  rw [← (A.fArc_spec_GARC sf f).2.2.2.2.2.1]
  exact fun x hx => Or.inl (mem_iUnion.2 ⟨a, hx⟩)

theorem AdaptedEdgeRimDataV2.range_fLoop_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F)
    (a : Fin (A.fLoopN_GARC sf f)) :
    range (A.fLoop_GARC sf f a) ⊆ A.circ.traceSet_GARC (A.traceIdx_GARC sf f) := by
  rw [← (A.fArc_spec_GARC sf f).2.2.2.2.2.1]
  exact fun x hx => Or.inr (mem_iUnion.2 ⟨a, hx⟩)

/-! ## The global enumeration -/

/-- The arc index: a partitioned face and one of its arcs. -/
abbrev AdaptedEdgeRimDataV2.ArcIdx_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) : Type :=
  Σ f : PFace_GARC F, Fin (A.fArcN_GARC sf f)

/-- The loop index. -/
abbrev AdaptedEdgeRimDataV2.LoopIdx_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) : Type :=
  Σ f : PFace_GARC F, Fin (A.fLoopN_GARC sf f)

theorem AdaptedEdgeRimDataV2.arc_range_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) {p q : A.ArcIdx_GARC sf} (hpq : p ≠ q) :
    Disjoint (range (A.fArc_GARC sf p.1 p.2)) (range (A.fArc_GARC sf q.1 q.2)) := by
  obtain ⟨f, a⟩ := p
  obtain ⟨f', a'⟩ := q
  by_cases hff : f = f'
  · subst hff
    have haa : a ≠ a' := fun h => hpq (h ▸ rfl)
    exact (A.fArc_spec_GARC sf f).2.2.1 haa
  · exact (A.traceSet_disjoint_GARC sf hff).mono (A.range_fArc_subset_GARC sf f a)
      (A.range_fArc_subset_GARC sf f' a')

theorem AdaptedEdgeRimDataV2.loop_range_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) {p q : A.LoopIdx_GARC sf} (hpq : p ≠ q) :
    Disjoint (range (A.fLoop_GARC sf p.1 p.2)) (range (A.fLoop_GARC sf q.1 q.2)) := by
  obtain ⟨f, a⟩ := p
  obtain ⟨f', a'⟩ := q
  by_cases hff : f = f'
  · subst hff
    have haa : a ≠ a' := fun h => hpq (h ▸ rfl)
    exact (A.fArc_spec_GARC sf f).2.2.2.1 haa
  · exact (A.traceSet_disjoint_GARC sf hff).mono (A.range_fLoop_subset_GARC sf f a)
      (A.range_fLoop_subset_GARC sf f' a')

theorem AdaptedEdgeRimDataV2.arc_loop_range_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (p : A.ArcIdx_GARC sf) (q : A.LoopIdx_GARC sf) :
    Disjoint (range (A.fArc_GARC sf p.1 p.2)) (range (A.fLoop_GARC sf q.1 q.2)) := by
  obtain ⟨f, a⟩ := p
  obtain ⟨f', a'⟩ := q
  by_cases hff : f = f'
  · subst hff
    exact (A.fArc_spec_GARC sf f).2.2.2.2.1 a a'
  · exact (A.traceSet_disjoint_GARC sf hff).mono (A.range_fArc_subset_GARC sf f a)
      (A.range_fLoop_subset_GARC sf f' a')

/-- The global arcs. -/
def AdaptedEdgeRimDataV2.gArc_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    Icc (0 : ℝ) 1 → A.circ.Base :=
  A.fArc_GARC sf ((Fintype.equivFin _).symm j).1 ((Fintype.equivFin _).symm j).2

/-- The global loops. -/
def AdaptedEdgeRimDataV2.gLoop_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    Circle → A.circ.Base :=
  A.fLoop_GARC sf ((Fintype.equivFin _).symm j).1 ((Fintype.equivFin _).symm j).2

/-- The owner face of a global arc. -/
def AdaptedEdgeRimDataV2.gArcOwner_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    PFace_GARC F :=
  ((Fintype.equivFin _).symm j).1

/-- The owner face of a global loop. -/
def AdaptedEdgeRimDataV2.gLoopOwner_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    PFace_GARC F :=
  ((Fintype.equivFin _).symm j).1

theorem AdaptedEdgeRimDataV2.gArc_embedding_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    IsSmoothEmbedding (𝓡∂ 1) (𝓡 2) ∞ (A.gArc_GARC sf j) :=
  (A.fArc_spec_GARC sf _).1 _

theorem AdaptedEdgeRimDataV2.gLoop_embedding_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (A.gLoop_GARC sf j) :=
  (A.fArc_spec_GARC sf _).2.1 _

theorem AdaptedEdgeRimDataV2.range_gArc_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    range (A.gArc_GARC sf j) ⊆ A.circ.traceSet_GARC (A.traceIdx_GARC sf (A.gArcOwner_GARC sf j)) :=
  A.range_fArc_subset_GARC sf _ _

theorem AdaptedEdgeRimDataV2.range_gLoop_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    range (A.gLoop_GARC sf j) ⊆
      A.circ.traceSet_GARC (A.traceIdx_GARC sf (A.gLoopOwner_GARC sf j)) :=
  A.range_fLoop_subset_GARC sf _ _

theorem AdaptedEdgeRimDataV2.gArc_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) :
    Pairwise fun j j' : Fin (Fintype.card (A.ArcIdx_GARC sf)) =>
      Disjoint (range (A.gArc_GARC sf j)) (range (A.gArc_GARC sf j')) := fun _ _ h =>
  A.arc_range_disjoint_GARC sf ((Fintype.equivFin _).symm.injective.ne h)

theorem AdaptedEdgeRimDataV2.gLoop_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) :
    Pairwise fun j j' : Fin (Fintype.card (A.LoopIdx_GARC sf)) =>
      Disjoint (range (A.gLoop_GARC sf j)) (range (A.gLoop_GARC sf j')) := fun _ _ h =>
  A.loop_range_disjoint_GARC sf ((Fintype.equivFin _).symm.injective.ne h)

theorem AdaptedEdgeRimDataV2.gArc_gLoop_disjoint_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf)))
    (j' : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    Disjoint (range (A.gArc_GARC sf j)) (range (A.gLoop_GARC sf j')) :=
  A.arc_loop_range_disjoint_GARC sf _ _

/-- Every point of the trace of a partitioned face is on one of its global arcs or loops. -/
theorem AdaptedEdgeRimDataV2.mem_traceSet_cases_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) {c : A.circ.Base}
    (hc : c ∈ A.circ.traceSet_GARC (A.traceIdx_GARC sf f)) :
    (∃ j, A.gArcOwner_GARC sf j = f ∧ c ∈ range (A.gArc_GARC sf j)) ∨
      ∃ j, A.gLoopOwner_GARC sf j = f ∧ c ∈ range (A.gLoop_GARC sf j) := by
  rw [← (A.fArc_spec_GARC sf f).2.2.2.2.2.1] at hc
  rcases hc with hc | hc
  · obtain ⟨a, ha⟩ := mem_iUnion.1 hc
    refine Or.inl ⟨Fintype.equivFin _ ⟨f, a⟩, ?_, ?_⟩
    · unfold AdaptedEdgeRimDataV2.gArcOwner_GARC
      rw [Equiv.symm_apply_apply]
    · unfold AdaptedEdgeRimDataV2.gArc_GARC
      rw [Equiv.symm_apply_apply]
      exact ha
  · obtain ⟨a, ha⟩ := mem_iUnion.1 hc
    refine Or.inr ⟨Fintype.equivFin _ ⟨f, a⟩, ?_, ?_⟩
    · unfold AdaptedEdgeRimDataV2.gLoopOwner_GARC
      rw [Equiv.symm_apply_apply]
    · unfold AdaptedEdgeRimDataV2.gLoop_GARC
      rw [Equiv.symm_apply_apply]
      exact ha

theorem AdaptedEdgeRimDataV2.traceBd_gArc_iff_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf)))
    {t : Icc (0 : ℝ) 1} :
    A.circ.traceBd_GARC (A.traceIdx_GARC sf (A.gArcOwner_GARC sf j)) (A.gArc_GARC sf j t) ↔
      (t = iccEnd false ∨ t = iccEnd true) :=
  (A.fArc_spec_GARC sf _).2.2.2.2.2.2.1 _ t

theorem AdaptedEdgeRimDataV2.not_traceBd_gLoop_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf)))
    (z : Circle) :
    ¬ A.circ.traceBd_GARC (A.traceIdx_GARC sf (A.gLoopOwner_GARC sf j)) (A.gLoop_GARC sf j z) :=
  (A.fArc_spec_GARC sf _).2.2.2.2.2.2.2 _ z

/-! ## A7: the endpoint bijection -/

theorem AdaptedEdgeRimDataV2.exists_arcEnd_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (e : Bool) :
    ∃ hb : Fin A.edges.handleCount × Bool,
      A.gArc_GARC sf j (iccEnd e) = A.cornerPt_GARC hb.1 hb.2 ∧
        HE.handleFace hb.1 hb.2 = (A.gArcOwner_GARC sf j).1 :=
  A.exists_handle_of_traceBd_GARC sf HE (A.gArcOwner_GARC sf j)
    (A.range_gArc_subset_GARC sf j ⟨_, rfl⟩)
    ((A.traceBd_gArc_iff_GARC sf j).2 (by cases e <;> simp))

/-- The handle end at the end `e` of the global arc `j`. -/
def AdaptedEdgeRimDataV2.arcEnd_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (e : Bool) : Fin A.edges.handleCount × Bool :=
  (A.exists_arcEnd_GARC sf HE j e).choose

theorem AdaptedEdgeRimDataV2.gArc_end_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (e : Bool) :
    A.gArc_GARC sf j (iccEnd e) =
      A.cornerPt_GARC (A.arcEnd_GARC sf HE j e).1 (A.arcEnd_GARC sf HE j e).2 :=
  (A.exists_arcEnd_GARC sf HE j e).choose_spec.1

theorem AdaptedEdgeRimDataV2.arcEnd_face_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (e : Bool) :
    HE.handleFace (A.arcEnd_GARC sf HE j e).1 (A.arcEnd_GARC sf HE j e).2 =
      (A.gArcOwner_GARC sf j).1 :=
  (A.exists_arcEnd_GARC sf HE j e).choose_spec.2

theorem AdaptedEdgeRimDataV2.arcEnd_bijective_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F) :
    Bijective fun p : Fin (Fintype.card (A.ArcIdx_GARC sf)) × Bool =>
      A.arcEnd_GARC sf HE p.1 p.2 := by
  constructor
  · rintro ⟨j, e⟩ ⟨j', e'⟩ h
    change A.arcEnd_GARC sf HE j e = A.arcEnd_GARC sf HE j' e' at h
    have hp : A.gArc_GARC sf j (iccEnd e) = A.gArc_GARC sf j' (iccEnd e') := by
      rw [A.gArc_end_GARC, A.gArc_end_GARC, h]
    have hjj : j = j' := by
      by_contra hne
      exact Set.disjoint_left.1 (A.gArc_disjoint_GARC sf hne) ⟨_, rfl⟩ ⟨_, hp.symm⟩
    subst hjj
    have hee := (A.gArc_embedding_GARC sf j).isEmbedding.injective hp
    rw [iccEnd_injective_GSAFE hee]
  · rintro ⟨h, b⟩
    have hc := A.cornerPt_mem_traceSet_GARC sf HE h b
    rcases A.mem_traceSet_cases_GARC sf (HE.pface_GARC h b) hc with
      ⟨j, hj, t, ht⟩ | ⟨j, hj, z, hz⟩
    · have hbd := A.traceBd_cornerPt_GARC (sf.resLabel_GARC (HE.pface_GARC h b)) h b
      rw [← ht] at hbd
      have hbd' : A.circ.traceBd_GARC (A.traceIdx_GARC sf (A.gArcOwner_GARC sf j))
          (A.gArc_GARC sf j t) := by
        rw [hj]
        exact hbd
      obtain ⟨e, rfl⟩ : ∃ e, t = iccEnd e := by
        rcases (A.traceBd_gArc_iff_GARC sf j).1 hbd' with h0 | h1
        · exact ⟨false, h0⟩
        · exact ⟨true, h1⟩
      refine ⟨(j, e), ?_⟩
      apply A.cornerPt_injective_GARC
      change A.cornerPt_GARC (A.arcEnd_GARC sf HE j e).1 (A.arcEnd_GARC sf HE j e).2 =
        A.cornerPt_GARC h b
      rw [← A.gArc_end_GARC, ht]
    · exfalso
      have hbd := A.traceBd_cornerPt_GARC (sf.resLabel_GARC (HE.pface_GARC h b)) h b
      rw [← hz] at hbd
      refine A.not_traceBd_gLoop_GARC sf j z ?_
      rw [hj]
      exact hbd

/-- **The endpoint bijection** `arcs × Bool ≃ handle ends` (A7). -/
def AdaptedEdgeRimDataV2.arcEndEquiv_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F) :
    Fin (Fintype.card (A.ArcIdx_GARC sf)) × Bool ≃ Fin A.edges.handleCount × Bool :=
  Equiv.ofBijective _ (A.arcEnd_bijective_GARC sf HE)

/-- The arc of a handle end, read from the inverse of the endpoint bijection. -/
def AdaptedEdgeRimDataV2.handleArc_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (h : Fin A.edges.handleCount) (b : Bool) : Fin (Fintype.card (A.ArcIdx_GARC sf)) :=
  ((A.arcEndEquiv_GARC sf HE).symm (h, b)).1

theorem AdaptedEdgeRimDataV2.arcEnd_handleArc_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.arcEnd_GARC sf HE (A.handleArc_GARC sf HE h b)
      ((A.arcEndEquiv_GARC sf HE).symm (h, b)).2 = (h, b) :=
  (A.arcEndEquiv_GARC sf HE).apply_symm_apply (h, b)

/-- The corner point of an end is the corresponding end of its arc. -/
theorem AdaptedEdgeRimDataV2.cornerPt_eq_gArc_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (h : Fin A.edges.handleCount) (b : Bool) :
    A.cornerPt_GARC h b = A.gArc_GARC sf (A.handleArc_GARC sf HE h b)
      (iccEnd ((A.arcEndEquiv_GARC sf HE).symm (h, b)).2) := by
  rw [A.gArc_end_GARC, A.arcEnd_handleArc_GARC]

/-! ## The faces of the arcs and loops -/

/-- The face of a global arc: the whole circle preimage of its base. -/
def AdaptedEdgeRimDataV2.gArcFace_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    Set W.Carrier :=
  Subtype.val '' (A.circ.proj ⁻¹' range (A.gArc_GARC sf j))

/-- The face of a global loop. -/
def AdaptedEdgeRimDataV2.gLoopFace_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    Set W.Carrier :=
  Subtype.val '' (A.circ.proj ⁻¹' range (A.gLoop_GARC sf j))

theorem _root_.GC.GraphManifold.Assembly.CircleRegion.disjoint_tube_GARC (R : CircleRegion W) {K K' : Set R.Base}
    (h : Disjoint K K') :
    Disjoint (Subtype.val '' (R.proj ⁻¹' K)) (Subtype.val '' (R.proj ⁻¹' K')) :=
  (disjoint_image_iff Subtype.val_injective).2 (h.preimage _)

theorem _root_.GC.GraphManifold.Assembly.CircleRegion.fibre_subset_tube_GARC (R : CircleRegion W) {K : Set R.Base} {c : R.Base}
    (hc : c ∈ K) : R.fibre_GARC c ⊆ Subtype.val '' (R.proj ⁻¹' K) := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨y, ?_, rfl⟩
  rw [mem_preimage, show R.proj y = c from hy]
  exact hc

theorem _root_.GC.GraphManifold.Assembly.CircleRegion.tube_subset_region_GARC (R : CircleRegion W) {K : Set R.Base}
    (hK : K ⊆ R.cornerBase) : Subtype.val '' (R.proj ⁻¹' K) ⊆ R.region :=
  image_mono (preimage_mono hK)

theorem AdaptedEdgeRimDataV2.gArcFace_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    A.gArcFace_GARC sf j ⊆ F.face (A.gArcOwner_GARC sf j).1 ∩ A.circ.region := by
  rw [A.face_inter_region_GARC sf]
  exact image_mono (preimage_mono (A.range_gArc_subset_GARC sf j))

theorem AdaptedEdgeRimDataV2.gLoopFace_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    A.gLoopFace_GARC sf j ⊆ F.face (A.gLoopOwner_GARC sf j).1 ∩ A.circ.region := by
  rw [A.face_inter_region_GARC sf]
  exact image_mono (preimage_mono (A.range_gLoop_subset_GARC sf j))

/-- **A8: the part of a partitioned face in the circle region is covered by its arcs and loops.** -/
theorem AdaptedEdgeRimDataV2.face_inter_region_subset_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (f : PFace_GARC F) :
    F.face f.1 ∩ A.circ.region ⊆
      (⋃ (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (_ : (A.gArcOwner_GARC sf j).1 = f.1),
          A.gArcFace_GARC sf j) ∪
        ⋃ (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) (_ : (A.gLoopOwner_GARC sf j).1 = f.1),
          A.gLoopFace_GARC sf j := by
  rw [A.face_inter_region_GARC sf]
  rintro _ ⟨y, hy, rfl⟩
  rcases A.mem_traceSet_cases_GARC sf f hy with ⟨j, hj, hjy⟩ | ⟨j, hj, hjy⟩
  · exact Or.inl (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨congrArg Subtype.val hj, y, hjy, rfl⟩⟩)
  · exact Or.inr (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨congrArg Subtype.val hj, y, hjy, rfl⟩⟩)

/-- The end disk of `(h, b)` meets a global arc face only in the fibre over the corner point. -/
theorem AdaptedEdgeRimDataV2.endDisk_inter_gArcFace_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (h : Fin A.edges.handleCount) (b : Bool)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) :
    (A.edges.handle h).endDisk b ∩ A.gArcFace_GARC sf j ⊆
      A.circ.fibre_GARC (A.cornerPt_GARC h b) := by
  rintro x ⟨hxd, hxa⟩
  rw [← A.endDisk_inter_region_GARC]
  exact ⟨hxd, (A.gArcFace_subset_GARC sf j hxa).2⟩

theorem AdaptedEdgeRimDataV2.endDisk_inter_gLoopFace_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (h : Fin A.edges.handleCount) (b : Bool)
    (j : Fin (Fintype.card (A.LoopIdx_GARC sf))) :
    (A.edges.handle h).endDisk b ∩ A.gLoopFace_GARC sf j ⊆
      A.circ.fibre_GARC (A.cornerPt_GARC h b) := by
  rintro x ⟨hxd, hxa⟩
  rw [← A.endDisk_inter_region_GARC]
  exact ⟨hxd, (A.gLoopFace_subset_GARC sf j hxa).2⟩

/-- The base point of a point of a tube that also lies in a fibre. -/
theorem _root_.GC.GraphManifold.Assembly.CircleRegion.mem_of_fibre_tube_GARC (R : CircleRegion W) {K : Set R.Base} {c : R.Base}
    {x : W.Carrier} (hxf : x ∈ R.fibre_GARC c) (hxK : x ∈ Subtype.val '' (R.proj ⁻¹' K)) :
    c ∈ K := by
  obtain ⟨y, hy, rfl⟩ := hxf
  obtain ⟨y', hy', hyy⟩ := hxK
  have : y' = y := Subtype.ext hyy
  subst this
  rw [← show R.proj y' = c from hy]
  exact hy'

/-- The end disk at the end `e` of the arc `j` meets the arc face in the whole fibre over the end
point of the arc. -/
theorem AdaptedEdgeRimDataV2.endDisk_arcEnd_inter_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F)
    (j : Fin (Fintype.card (A.ArcIdx_GARC sf))) (e : Bool) :
    (A.edges.handle (A.arcEnd_GARC sf HE j e).1).endDisk (A.arcEnd_GARC sf HE j e).2 ∩
        A.gArcFace_GARC sf j = A.circ.fibre_GARC (A.gArc_GARC sf j (iccEnd e)) := by
  apply Subset.antisymm
  · rw [A.gArc_end_GARC]
    exact A.endDisk_inter_gArcFace_GARC sf _ _ j
  · intro x hx
    have hx' := hx
    rw [A.gArc_end_GARC, ← A.endDisk_inter_region_GARC] at hx'
    exact ⟨hx'.1, A.circ.fibre_subset_tube_GARC (K := range (A.gArc_GARC sf j)) ⟨_, rfl⟩ hx⟩

/-! ## The arc layer -/

/-- **`stub_exists_arcLayer` (FC39 GROUP G, P9), proved for ANY adapted data, seam–face link and
handle-end layer.** -/
theorem exists_arcLayer_GARC (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) :
    Nonempty (ArcLayer W A.edges A.circ F HE A.rims) := by
  classical
  choose ann hannC hannI hannR hannP using fun j : Fin (Fintype.card (A.ArcIdx_GARC sf)) =>
    A.circ.exists_annulus_GARC (A.gArc_GARC sf j) (A.gArc_embedding_GARC sf j).contMDiff.continuous
      (A.gArc_embedding_GARC sf j).isEmbedding.injective
  refine ⟨{
    arcFaceCount := Fintype.card (A.ArcIdx_GARC sf)
    arcFace := A.gArcFace_GARC sf
    arcOwner := fun j => (A.gArcOwner_GARC sf j).1
    arcOwner_kind := fun j => (A.gArcOwner_GARC sf j).2
    arcBase := A.gArc_GARC sf
    arcBase_embedding := A.gArc_embedding_GARC sf
    arcFace_eq := fun j => rfl
    arcDefining := fun j => A.traceIdx_GARC sf (A.gArcOwner_GARC sf j)
    arcBase_defining := fun j t => (A.range_gArc_subset_GARC sf j ⟨t, rfl⟩).2
    arcAnnulus := ann
    arcAnnulus_continuous := hannC
    arcAnnulus_injective := hannI
    arcAnnulus_range := hannR
    arcAnnulus_proj := hannP
    loopFaceCount := Fintype.card (A.LoopIdx_GARC sf)
    loopFace := A.gLoopFace_GARC sf
    loopOwner := fun j => (A.gLoopOwner_GARC sf j).1
    loopOwner_kind := fun j => (A.gLoopOwner_GARC sf j).2
    loopBase := A.gLoop_GARC sf
    loopBase_embedding := A.gLoop_embedding_GARC sf
    loopFace_eq := fun j => rfl
    loopDefining := fun j => A.traceIdx_GARC sf (A.gLoopOwner_GARC sf j)
    loopBase_defining := fun j z => (A.range_gLoop_subset_GARC sf j ⟨z, rfl⟩).2
    loopFace_closed := fun j => ?_
    loopFace_nonempty := fun j => ?_
    arcFace_disjoint := fun j j' hjj => A.circ.disjoint_tube_GARC (A.gArc_disjoint_GARC sf hjj)
    loopFace_disjoint := fun j j' hjj => A.circ.disjoint_tube_GARC (A.gLoop_disjoint_GARC sf hjj)
    arc_loop_disjoint := fun j j' => A.circ.disjoint_tube_GARC (A.gArc_gLoop_disjoint_GARC sf j j')
    face_partition := fun f hf => ?_
    face_region_inter := fun f hf => ?_
    handleArc := A.handleArc_GARC sf HE
    handleArc_owner := fun h b => ?_
    handleArc_meets := fun h b j hj => ?_
    endDisk_loop_disjoint := fun h b j => ?_
    endDisk_rim := fun h b => ?_
    arcEnd := A.arcEnd_GARC sf HE
    arcEnd_arc := fun j e => ?_
    arcEnd_injective := fun j e e' hee => ?_
    arcEnd_surjective := fun h b => ⟨((A.arcEndEquiv_GARC sf HE).symm (h, b)).2,
      A.arcEnd_handleArc_GARC sf HE h b⟩
    arcAnnulus_end := fun j e => ?_
    arcBase_end := fun j e => A.gArc_end_GARC sf HE j e }⟩
  · -- loopFace_closed
    change IsClosed (Subtype.val '' (A.circ.proj ⁻¹' range (A.gLoop_GARC sf j)))
    rw [A.tube_eq_GARC]
    refine (Pr.rows.circle.isCompact_tube_GSAFE ?_).isClosed
    exact (isCompact_range (A.gLoop_embedding_GARC sf j).contMDiff.continuous).image
      A.labelled.circleLink.ι_isOpenEmbedding.continuous
  · -- loopFace_nonempty
    obtain ⟨x, hx⟩ := A.circ.fibre_nonempty_GARC (A.gLoop_GARC sf j 1)
    exact ⟨x, A.circ.fibre_subset_tube_GARC (K := range (A.gLoop_GARC sf j)) ⟨1, rfl⟩ hx⟩
  · -- face_partition
    apply Subset.antisymm
    · refine union_subset (union_subset ?_ ?_) ?_
      · intro x hx
        obtain ⟨h, hx⟩ := mem_iUnion.1 hx
        obtain ⟨b, hx⟩ := mem_iUnion.1 hx
        obtain ⟨hhb, hx⟩ := mem_iUnion.1 hx
        rw [← hhb]
        exact HE.handleEnd_face h b hx
      · intro x hx
        obtain ⟨j, hx⟩ := mem_iUnion.1 hx
        obtain ⟨hj, hx⟩ := mem_iUnion.1 hx
        have := (A.gArcFace_subset_GARC sf j hx).1
        rw [hj] at this
        exact this
      · intro x hx
        obtain ⟨j, hx⟩ := mem_iUnion.1 hx
        obtain ⟨hj, hx⟩ := mem_iUnion.1 hx
        have := (A.gLoopFace_subset_GARC sf j hx).1
        rw [hj] at this
        exact this
    · intro x hx
      by_cases hxr : x ∈ A.circ.region
      · rcases A.face_inter_region_subset_GARC sf ⟨f, hf⟩ ⟨hx, hxr⟩ with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
      · exact Or.inl (Or.inl (A.face_diff_region_subset_GARC sf HE ⟨f, hf⟩ ⟨hx, hxr⟩))
  · -- face_region_inter
    apply Subset.antisymm
    · exact A.face_inter_region_subset_GARC sf ⟨f, hf⟩
    · refine union_subset ?_ ?_
      · intro x hx
        obtain ⟨j, hx⟩ := mem_iUnion.1 hx
        obtain ⟨hj, hx⟩ := mem_iUnion.1 hx
        have := A.gArcFace_subset_GARC sf j hx
        rw [hj] at this
        exact this
      · intro x hx
        obtain ⟨j, hx⟩ := mem_iUnion.1 hx
        obtain ⟨hj, hx⟩ := mem_iUnion.1 hx
        have := A.gLoopFace_subset_GARC sf j hx
        rw [hj] at this
        exact this
  · -- handleArc_owner
    have h1 := A.arcEnd_face_GARC sf HE (A.handleArc_GARC sf HE h b)
      ((A.arcEndEquiv_GARC sf HE).symm (h, b)).2
    rw [A.arcEnd_handleArc_GARC] at h1
    exact h1.symm
  · -- handleArc_meets
    obtain ⟨x, hx⟩ := hj
    have hxf := A.endDisk_inter_gArcFace_GARC sf h b j hx
    have hc := A.circ.mem_of_fibre_tube_GARC hxf hx.2
    by_contra hne
    refine Set.disjoint_left.1 (A.gArc_disjoint_GARC sf hne) ?_ hc
    rw [A.cornerPt_eq_gArc_GARC sf HE h b]
    exact ⟨_, rfl⟩
  · -- endDisk_loop_disjoint
    refine Set.disjoint_left.2 fun x hxd hxl => ?_
    have hxf := A.endDisk_inter_gLoopFace_GARC sf h b j ⟨hxd, hxl⟩
    have hc := A.circ.mem_of_fibre_tube_GARC hxf hxl
    refine Set.disjoint_left.1 (A.gArc_gLoop_disjoint_GARC sf (A.handleArc_GARC sf HE h b) j) ?_ hc
    rw [A.cornerPt_eq_gArc_GARC sf HE h b]
    exact ⟨_, rfl⟩
  · -- endDisk_rim
    rw [A.rim_eq_fibre_GARC]
    apply Subset.antisymm
    · intro x hx
      have hx' := hx
      rw [← A.endDisk_inter_region_GARC] at hx'
      refine ⟨hx'.1, A.circ.fibre_subset_tube_GARC ?_ hx⟩
      rw [A.cornerPt_eq_gArc_GARC sf HE h b]
      exact ⟨_, rfl⟩
    · exact A.endDisk_inter_gArcFace_GARC sf h b _
  · -- arcEnd_arc
    change ((A.arcEndEquiv_GARC sf HE).symm ((A.arcEnd_GARC sf HE j e).1,
      (A.arcEnd_GARC sf HE j e).2)).1 = j
    have h1 : (A.arcEndEquiv_GARC sf HE) (j, e) = A.arcEnd_GARC sf HE j e := rfl
    rw [Prod.mk.eta, ← h1, Equiv.symm_apply_apply]
  · -- arcEnd_injective
    have h1 : (A.arcEndEquiv_GARC sf HE) (j, e) = (A.arcEndEquiv_GARC sf HE) (j, e') := hee
    exact congrArg Prod.snd ((A.arcEndEquiv_GARC sf HE).injective h1)
  · -- arcAnnulus_end
    rw [A.endDisk_arcEnd_inter_GARC sf HE j e]
    apply Subset.antisymm
    · intro x hx
      have hxa : x ∈ range (ann j) := by
        rw [hannR]
        exact A.circ.fibre_subset_tube_GARC (K := range (A.gArc_GARC sf j)) ⟨_, rfl⟩ hx
      obtain ⟨q, rfl⟩ := hxa
      refine ⟨q, ?_, rfl⟩
      obtain ⟨hq, hpq⟩ := hannP j q
      obtain ⟨y, hy, hyx⟩ := hx
      have hyq : y = ⟨ann j q, hq⟩ := Subtype.ext hyx
      rw [hyq] at hy
      have h2 : A.gArc_GARC sf j q.2 = A.gArc_GARC sf j (iccEnd e) := hpq.symm.trans hy
      exact (A.gArc_embedding_GARC sf j).isEmbedding.injective h2
    · rintro _ ⟨q, hq2, rfl⟩
      obtain ⟨hq, hpq⟩ := hannP j q
      refine ⟨⟨ann j q, hq⟩, ?_, rfl⟩
      change A.circ.proj ⟨ann j q, hq⟩ = A.gArc_GARC sf j (iccEnd e)
      rw [hpq, show q.2 = iccEnd e from hq2]

/-- **The frozen target `stub_exists_arcLayer`, verbatim.** -/
theorem stub_exists_arcLayer_GARC (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (HE : HandleEndLayer W V A.edges F) :
    Nonempty (ArcLayer W A.edges A.circ F HE A.rims) :=
  exists_arcLayer_GARC Pr safe A V vlink O S F sf HE

/-- **Regression (A8, no FC40): there are exactly as many arcs as handles** — from the endpoint
bijection `arcs × Bool ≃ handle ends`. -/
theorem arcFaceCount_eq_handleCount_GARC (A : AdaptedEdgeRimDataV2 Pr safe)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V A.edges F) :
    Fintype.card (A.ArcIdx_GARC sf) = A.edges.handleCount := by
  have h := Fintype.card_congr (A.arcEndEquiv_GARC sf HE)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
  omega

end GC.GraphManifold.Assembly.FC39P0
