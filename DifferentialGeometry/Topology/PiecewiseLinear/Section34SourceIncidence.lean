/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceArcEndpoints
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDisksDisjoint

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {U : Set M} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M}

private theorem eq_of_source_subset_of_dim_le
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {m l : Section34CutLabelOf 𝒦 𝒦'}
    (hml : src m ⊆ src l) (hd : section34Dim l ≤ section34Dim m) : m = l := by
  obtain ⟨-, -, -, -, -, -, hdim, -⟩ := hcut
  rcases hdim l m hml with heq | hlt
  · exact heq
  · omega

private theorem faceArc_vertex_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (a : Section34ArcIndex 𝒦 𝒦')
    (w : Section34VertexIndex 𝒦 𝒦') (hsub : src (.faceArc a) ⊆ src (.vertexBall w)) :
    a.1.2 = w := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, -, -, -, havoid, -⟩ := id hcut
  have hsf : src (.faceArc a) ⊆ src (.faceDisk a.1.1) := by
    rw [harc a]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.faceArc a)).nonempty
  have hi : Section34Incident w.1 a.1.1.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk a.1.1) ∩ src (.vertexBall w) := ⟨hsf hx, hsub hx⟩
    rw [havoid a.1.1 w hi] at hxm
    exact hxm
  let b : Section34ArcIndex 𝒦 𝒦' := ⟨(a.1.1, w), hi⟩
  have hab : src (.faceArc a) ⊆ src (.faceArc b) := by
    rw [harc b]
    exact fun y hy => ⟨hsub hy, hsf hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hab le_rfl
  exact congrArg (fun r : Section34ArcIndex 𝒦 𝒦' => r.1.2) (Section34Label.faceArc.inj heq)

private theorem patch_vertex_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (p : Section34PatchIndex 𝒦 𝒦')
    (w : Section34VertexIndex 𝒦 𝒦') (hsub : src (.patch p) ⊆ src (.vertexBall w)) :
    p.1.2 = w := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, -, hpatch, -, -, -, havoid, -⟩ := id hcut
  have hst : src (.patch p) ⊆ src (.tetraBall p.1.1) := by
    rw [hpatch p]
    exact inter_subset_left
  obtain ⟨x, hx⟩ := (hcell (.patch p)).nonempty
  have hi : Section34Incident w.1 p.1.1.1 := by
    by_contra hi
    have hxm : x ∈ src (.tetraBall p.1.1) ∩ src (.vertexBall w) := ⟨hst hx, hsub hx⟩
    rw [havoid p.1.1 w hi] at hxm
    exact hxm
  let q : Section34PatchIndex 𝒦 𝒦' := ⟨(p.1.1, w), hi⟩
  have hpq : src (.patch p) ⊆ src (.patch q) := by
    rw [hpatch q]
    exact fun y hy => ⟨hst hy, hsub hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hpq le_rfl
  exact congrArg (fun r : Section34PatchIndex 𝒦 𝒦' => r.1.2) (Section34Label.patch.inj heq)

private theorem patch_tetra_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (p : Section34PatchIndex 𝒦 𝒦')
    (t : Section34SimplexIndex 𝒦 4) (hsub : src (.patch p) ⊆ src (.tetraBall t)) :
    p.1.1 = t := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, -, hpatch, -, -, -, havoid, -⟩ := id hcut
  have hsv : src (.patch p) ⊆ src (.vertexBall p.1.2) := by
    rw [hpatch p]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.patch p)).nonempty
  have hi : Section34Incident p.1.2.1 t.1 := by
    by_contra hi
    have hxm : x ∈ src (.tetraBall t) ∩ src (.vertexBall p.1.2) := ⟨hsub hx, hsv hx⟩
    rw [havoid t p.1.2 hi] at hxm
    exact hxm
  let q : Section34PatchIndex 𝒦 𝒦' := ⟨(t, p.1.2), hi⟩
  have hpq : src (.patch p) ⊆ src (.patch q) := by
    rw [hpatch q]
    exact fun y hy => ⟨hsub hy, hsv hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hpq le_rfl
  exact congrArg (fun r : Section34PatchIndex 𝒦 𝒦' => r.1.1) (Section34Label.patch.inj heq)

private theorem markedPoint_tetra_incident
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (p : Section34MarkIndex 𝒦 𝒦')
    (t : Section34SimplexIndex 𝒦 4) (hsub : src (.markedPoint p) ⊆ src (.tetraBall t)) :
    Section34Incident p.1.1.1 t.1 := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, hmark, -, hedge, -, -, -, havoid, -⟩ := id hcut
  have hse : src (.markedPoint p) ⊆ src (.splitDisk p.1.2) := by
    rw [hmark p]
    exact inter_subset_left
  obtain ⟨x, hx⟩ := (hcell (.markedPoint p)).nonempty
  have hi : Section34Incident p.1.2.1 t.1 := by
    by_contra hi
    have hxm : x ∈ src (.tetraBall t) ∩ src (.splitDisk p.1.2) := ⟨hsub hx, hse hx⟩
    rw [havoid t p.1.2 hi] at hxm
    exact hxm
  let i : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(t, p.1.2), hi⟩
  have hpi : src (.markedPoint p) ⊆ src (.edgeArc i) := by
    rw [hedge i]
    exact fun y hy => ⟨hsub hy, hse hy⟩
  exact ((hcut.markedPoint_subset_edgeArc_iff p i).mp hpi).2

private theorem edgeArc_tetra_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (i : Section34EdgeArcIndex 𝒦 𝒦')
    (t : Section34SimplexIndex 𝒦 4) (hsub : src (.edgeArc i) ⊆ src (.tetraBall t)) :
    i.1.1 = t := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, -, -, hedge, -, -, -, havoid, -⟩ := id hcut
  have hse : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
    rw [hedge i]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.edgeArc i)).nonempty
  have hi : Section34Incident i.1.2.1 t.1 := by
    by_contra hi
    have hxm : x ∈ src (.tetraBall t) ∩ src (.splitDisk i.1.2) := ⟨hsub hx, hse hx⟩
    rw [havoid t i.1.2 hi] at hxm
    exact hxm
  let j : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(t, i.1.2), hi⟩
  have hij : src (.edgeArc i) ⊆ src (.edgeArc j) := by
    rw [hedge j]
    exact fun y hy => ⟨hsub hy, hse hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hij le_rfl
  exact congrArg (fun r : Section34EdgeArcIndex 𝒦 𝒦' => r.1.1) (Section34Label.edgeArc.inj heq)

private theorem faceArc_face_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (a : Section34ArcIndex 𝒦 𝒦')
    (s : Section34SimplexIndex 𝒦 3) (hsub : src (.faceArc a) ⊆ src (.faceDisk s)) :
    a.1.1 = s := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, -, -, -, havoid, -⟩ := id hcut
  have hsv : src (.faceArc a) ⊆ src (.vertexBall a.1.2) := by
    rw [harc a]
    exact inter_subset_left
  obtain ⟨x, hx⟩ := (hcell (.faceArc a)).nonempty
  have hi : Section34Incident a.1.2.1 s.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk s) ∩ src (.vertexBall a.1.2) := ⟨hsub hx, hsv hx⟩
    rw [havoid s a.1.2 hi] at hxm
    exact hxm
  let b : Section34ArcIndex 𝒦 𝒦' := ⟨(s, a.1.2), hi⟩
  have hab : src (.faceArc a) ⊆ src (.faceArc b) := by
    rw [harc b]
    exact fun y hy => ⟨hsv hy, hsub hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hab le_rfl
  exact congrArg (fun r : Section34ArcIndex 𝒦 𝒦' => r.1.1) (Section34Label.faceArc.inj heq)

private theorem markedPoint_face_eq
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (p : Section34MarkIndex 𝒦 𝒦')
    (s : Section34SimplexIndex 𝒦 3) (hsub : src (.markedPoint p) ⊆ src (.faceDisk s)) :
    p.1.1 = s := by
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, hmark, -, -, -, havoid, -⟩ := id hcut
  have hse : src (.markedPoint p) ⊆ src (.splitDisk p.1.2) := by
    rw [hmark p]
    exact inter_subset_left
  obtain ⟨x, hx⟩ := (hcell (.markedPoint p)).nonempty
  have hi : Section34Incident p.1.2.1 s.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk s) ∩ src (.splitDisk p.1.2) := ⟨hsub hx, hse hx⟩
    rw [havoid s p.1.2 hi] at hxm
    exact hxm
  let q : Section34MarkIndex 𝒦 𝒦' := ⟨(s, p.1.2), hi⟩
  have hpq : src (.markedPoint p) ⊆ src (.markedPoint q) := by
    rw [hmark q]
    exact fun y hy => ⟨hse hy, hsub hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hpq le_rfl
  exact congrArg (fun r : Section34MarkIndex 𝒦 𝒦' => r.1.1) (Section34Label.markedPoint.inj heq)

private theorem not_faceDisk_subset_vertexBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3)
    (w : Section34VertexIndex 𝒦 𝒦') : ¬ src (.faceDisk s) ⊆ src (.vertexBall w) := by
  intro hsub
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, -, -, -, havoid, -⟩ := id hcut
  obtain ⟨x, hx⟩ := (hcell (.faceDisk s)).nonempty
  have hi : Section34Incident w.1 s.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk s) ∩ src (.vertexBall w) := ⟨hx, hsub hx⟩
    rw [havoid s w hi] at hxm
    exact hxm
  let a : Section34ArcIndex 𝒦 𝒦' := ⟨(s, w), hi⟩
  have hsa : src (.faceDisk s) ⊆ src (.faceArc a) := by
    rw [harc a]
    exact fun y hy => ⟨hsub hy, hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hsa (by simp [section34Dim])
  cases heq

private theorem not_splitDisk_subset_tetraBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (e : Section34EdgeIndex 𝒦 𝒦')
    (t : Section34SimplexIndex 𝒦 4) : ¬ src (.splitDisk e) ⊆ src (.tetraBall t) := by
  intro hsub
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, -, -, hedge, -, -, -, havoid, -⟩ := id hcut
  obtain ⟨x, hx⟩ := (hcell (.splitDisk e)).nonempty
  have hi : Section34Incident e.1 t.1 := by
    by_contra hi
    have hxm : x ∈ src (.tetraBall t) ∩ src (.splitDisk e) := ⟨hsub hx, hx⟩
    rw [havoid t e hi] at hxm
    exact hxm
  let i : Section34EdgeArcIndex 𝒦 𝒦' := ⟨(t, e), hi⟩
  have hei : src (.splitDisk e) ⊆ src (.edgeArc i) := by
    rw [hedge i]
    exact fun y hy => ⟨hsub hy, hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hei (by simp [section34Dim])
  cases heq

private theorem not_faceArc_subset_splitDisk
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (a : Section34ArcIndex 𝒦 𝒦')
    (e : Section34EdgeIndex 𝒦 𝒦') : ¬ src (.faceArc a) ⊆ src (.splitDisk e) := by
  intro hsub
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, hmark, -, -, -, havoid, -⟩ := id hcut
  have hsf : src (.faceArc a) ⊆ src (.faceDisk a.1.1) := by
    rw [harc a]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.faceArc a)).nonempty
  have hi : Section34Incident e.1 a.1.1.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk a.1.1) ∩ src (.splitDisk e) := ⟨hsf hx, hsub hx⟩
    rw [havoid a.1.1 e hi] at hxm
    exact hxm
  let p : Section34MarkIndex 𝒦 𝒦' := ⟨(a.1.1, e), hi⟩
  have hap : src (.faceArc a) ⊆ src (.markedPoint p) := by
    rw [hmark p]
    exact fun y hy => ⟨hsub hy, hsf hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hap (by simp [section34Dim])
  cases heq

private theorem not_edgeArc_subset_faceDisk
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (i : Section34EdgeArcIndex 𝒦 𝒦')
    (s : Section34SimplexIndex 𝒦 3) : ¬ src (.edgeArc i) ⊆ src (.faceDisk s) := by
  intro hsub
  obtain ⟨-, -, -, hcell, -, -, -, -, -, -, hmark, -, hedge, -, havoid, -⟩ := id hcut
  have hse : src (.edgeArc i) ⊆ src (.splitDisk i.1.2) := by
    rw [hedge i]
    exact inter_subset_right
  obtain ⟨x, hx⟩ := (hcell (.edgeArc i)).nonempty
  have hi : Section34Incident i.1.2.1 s.1 := by
    by_contra hi
    have hxm : x ∈ src (.faceDisk s) ∩ src (.splitDisk i.1.2) := ⟨hsub hx, hse hx⟩
    rw [havoid s i.1.2 hi] at hxm
    exact hxm
  let p : Section34MarkIndex 𝒦 𝒦' := ⟨(s, i.1.2), hi⟩
  have hip : src (.edgeArc i) ⊆ src (.markedPoint p) := by
    rw [hmark p]
    exact fun y hy => ⟨hse hy, hsub hy⟩
  have heq := eq_of_source_subset_of_dim_le hcut hip (by simp [section34Dim])
  cases heq

variable [FiniteDimensional ℝ Ea]

private theorem faceArc_tetra_incident
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (a : Section34ArcIndex 𝒦 𝒦')
    (t : Section34SimplexIndex 𝒦 4) (hsub : src (.faceArc a) ⊆ src (.tetraBall t)) :
    Section34Incident a.1.1.1 t.1 := by
  obtain ⟨-, hdiv, hmap, -⟩ := id hcut
  obtain ⟨e, -, -, hes, -, hwe, -, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hdiv hmap a.1.1 a.1.2 a.2
  let p : Section34MarkIndex 𝒦 𝒦' := ⟨(a.1.1, e), hes⟩
  have hpa : Section34CutStep (.markedPoint p) (.faceArc a) := ⟨rfl, hwe⟩
  exact markedPoint_tetra_incident hcut p t ((hcut.src_subset_of_cutStep hpa).trans hsub)

private theorem exists_markedPoint_of_face
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3) :
    ∃ p : Section34MarkIndex 𝒦 𝒦', p.1.1 = s := by
  classical
  obtain ⟨-, hdiv, hmap, -⟩ := hcut
  obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces s.2.1
  have hvK : {v} ∈ 𝒦.complex.faces :=
    𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v)
  let w : Section34VertexIndex 𝒦 𝒦' := ⟨{v}, hdiv.singleton_mem hvK,
    Finset.card_singleton v, by
      rintro y ⟨x, hx, rfl⟩
      rw [hmap]
      exact mem_iUnion₂.mpr ⟨{v}, ⟨hvK, by simp⟩, x, hx, rfl⟩⟩
  have hws : Section34Incident w.1 s.1 :=
    (Finset.coe_subset.mpr (Finset.singleton_subset_iff.mpr hv)).trans (subset_convexHull ℝ _)
  obtain ⟨e, -, -, hes, -⟩ := exists_section34EdgeIndex_pair_of_incident hdiv hmap s w hws
  exact ⟨⟨(s, e), hes⟩, rfl⟩

private theorem faceDisk_tetra_incident
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3)
    (t : Section34SimplexIndex 𝒦 4) (hsub : src (.faceDisk s) ⊆ src (.tetraBall t)) :
    Section34Incident s.1 t.1 := by
  obtain ⟨p, hp⟩ := exists_markedPoint_of_face hcut s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hmark, -⟩ := id hcut
  have hps : src (.markedPoint p) ⊆ src (.faceDisk s) := by
    rw [hmark p, hp]
    exact inter_subset_right
  have hi := markedPoint_tetra_incident hcut p t (hps.trans hsub)
  simpa only [hp] using hi

theorem Section34CutFrame.cutStep_iff_codimension_one_source_subset
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {m l : Section34CutLabelOf 𝒦 𝒦'}
    (hd : section34Dim l = section34Dim m + 1) : Section34CutStep m l ↔ src m ⊆ src l := by
  refine ⟨hcut.src_subset_of_cutStep, ?_⟩
  intro hsub
  obtain ⟨-, -, -, hcell, -, -, -, -, -, harc, hmark, hpatch, hedge, -, -, -, -, -, -, -, -,
    hvertexEdge, -⟩ := id hcut
  cases m <;> cases l <;> simp [section34Dim] at hd
  · rename_i e w
    obtain ⟨x, hx⟩ := (hcell (.splitDisk e)).nonempty
    exact hvertexEdge w e ⟨x, hsub hx, hx⟩
  · rename_i e t
    exact (not_splitDisk_subset_tetraBall hcut e t hsub).elim
  · rename_i s w
    exact (not_faceDisk_subset_vertexBall hcut s w hsub).elim
  · rename_i s t
    exact faceDisk_tetra_incident hcut s t hsub
  · rename_i p w
    exact patch_vertex_eq hcut p w hsub
  · rename_i p t
    exact patch_tetra_eq hcut p t hsub
  · rename_i a e
    exact (not_faceArc_subset_splitDisk hcut a e hsub).elim
  · rename_i a s
    exact faceArc_face_eq hcut a s hsub
  · rename_i a p
    have hsv : src (.patch p) ⊆ src (.vertexBall p.1.2) := by
      rw [hpatch p]
      exact inter_subset_right
    have hst : src (.patch p) ⊆ src (.tetraBall p.1.1) := by
      rw [hpatch p]
      exact inter_subset_left
    exact ⟨faceArc_vertex_eq hcut a p.1.2 (hsub.trans hsv),
      faceArc_tetra_incident hcut a p.1.1 (hsub.trans hst)⟩
  · rename_i i e
    change i.1.2 = e
    by_contra hne
    obtain ⟨x, hx⟩ := (hcell (.edgeArc i)).nonempty
    have hxe : x ∈ src (.splitDisk i.1.2) := by
      rw [hedge i] at hx
      exact hx.2
    exact disjoint_left.mp (section34_splitDisks_disjoint hcut hne) hxe (hsub hx)
  · rename_i i s
    exact (not_edgeArc_subset_faceDisk hcut i s hsub).elim
  · rename_i i p
    have hsv : src (.patch p) ⊆ src (.vertexBall p.1.2) := by
      rw [hpatch p]
      exact inter_subset_right
    have hst : src (.patch p) ⊆ src (.tetraBall p.1.1) := by
      rw [hpatch p]
      exact inter_subset_left
    obtain ⟨x, hx⟩ := (hcell (.edgeArc i)).nonempty
    have hxe : x ∈ src (.splitDisk i.1.2) := by
      rw [hedge i] at hx
      exact hx.2
    exact ⟨edgeArc_tetra_eq hcut i p.1.1 (hsub.trans hst),
      hvertexEdge p.1.2 i.1.2 ⟨x, hsv (hsub hx), hxe⟩⟩
  · rename_i p a
    have hsv : src (.faceArc a) ⊆ src (.vertexBall a.1.2) := by
      rw [harc a]
      exact inter_subset_left
    have hsf : src (.faceArc a) ⊆ src (.faceDisk a.1.1) := by
      rw [harc a]
      exact inter_subset_right
    obtain ⟨x, hx⟩ := (hcell (.markedPoint p)).nonempty
    have hxe : x ∈ src (.splitDisk p.1.2) := by
      rw [hmark p] at hx
      exact hx.1
    exact ⟨markedPoint_face_eq hcut p a.1.1 (hsub.trans hsf),
      hvertexEdge a.1.2 p.1.2 ⟨x, hsv (hsub hx), hxe⟩⟩
  · rename_i p i
    exact (hcut.markedPoint_subset_edgeArc_iff p i).mp hsub

end DifferentialGeometry.Topology.PiecewiseLinear
