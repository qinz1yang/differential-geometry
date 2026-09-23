import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdges
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDisksDisjoint

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
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

theorem Section34CutFrame.exists_edge_of_vertex_intersection
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) {w w' : Section34VertexIndex 𝒦 𝒦'}
    (hne : w ≠ w') (hmeet : (src (.vertexBall w) ∩ src (.vertexBall w')).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 ∧ w'.1 ⊆ e.1 := by
  obtain ⟨-, -, -, -, -, hinter, -, -, -, -, hmark, -, hedge, -, -, -, -, -, -, -, -,
    hvertexEdge, -⟩ := id hcut
  obtain ⟨x, hx⟩ := hmeet
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp ((hinter (.vertexBall w) (.vertexBall w')).subset hx)
  have hkw : src k ⊆ src (.vertexBall w) := hk.1
  have hkw' : src k ⊆ src (.vertexBall w') := hk.2
  cases k with
  | vertexBall v =>
    have hvw := Section34Label.vertexBall.inj (eq_of_source_subset_of_dim_le hcut hkw le_rfl)
    have hvw' := Section34Label.vertexBall.inj (eq_of_source_subset_of_dim_le hcut hkw' le_rfl)
    exact (hne (hvw.symm.trans hvw')).elim
  | tetraBall t =>
    have he := eq_of_source_subset_of_dim_le hcut hkw le_rfl
    cases he
  | splitDisk e =>
    exact ⟨e, hvertexEdge w e ⟨x, hx.1, hxk⟩, hvertexEdge w' e ⟨x, hx.2, hxk⟩⟩
  | faceDisk s =>
    exact (not_faceDisk_subset_vertexBall hcut s w hkw).elim
  | patch p =>
    exact (hne ((patch_vertex_eq hcut p w hkw).symm.trans
      (patch_vertex_eq hcut p w' hkw'))).elim
  | faceArc a =>
    exact (hne ((faceArc_vertex_eq hcut a w hkw).symm.trans
      (faceArc_vertex_eq hcut a w' hkw'))).elim
  | edgeArc i =>
    have hxD : x ∈ src (.splitDisk i.1.2) := by
      rw [hedge i] at hxk
      exact hxk.2
    exact ⟨i.1.2, hvertexEdge w i.1.2 ⟨x, hx.1, hxD⟩,
      hvertexEdge w' i.1.2 ⟨x, hx.2, hxD⟩⟩
  | markedPoint p =>
    have hxD : x ∈ src (.splitDisk p.1.2) := by
      rw [hmark p] at hxk
      exact hxk.1
    exact ⟨p.1.2, hvertexEdge w p.1.2 ⟨x, hx.1, hxD⟩,
      hvertexEdge w' p.1.2 ⟨x, hx.2, hxD⟩⟩

theorem section34_vertex_cells_intersection_of_ne
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hne : w ≠ w')
    (hmeet : (src (.vertexBall w) ∩ src (.vertexBall w')).Nonempty) :
    ∃ e : Section34EdgeIndex 𝒦 𝒦',
      ((w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) ∧
      src (.vertexBall w) ∩ src (.vertexBall w') = src (.splitDisk e) := by
  obtain ⟨e, hw, hw'⟩ := hcut.exists_edge_of_vertex_intersection hne hmeet
  have hwends := eq_or_eq_of_section34VertexIndex_subset e (hends e).1 hw
  have hwends' := eq_or_eq_of_section34VertexIndex_subset e (hends e).1 hw'
  rcases hwends with rfl | rfl <;> rcases hwends' with rfl | rfl
  · exact (hne rfl).elim
  · exact ⟨e, Or.inl ⟨rfl, rfl⟩, (hends e).2.symm⟩
  · exact ⟨e, Or.inr ⟨rfl, rfl⟩, (inter_comm _ _).trans (hends e).2.symm⟩
  · exact (hne rfl).elim

theorem section34_vertex_cells_disjoint_of_nonadjacent
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    {w w' : Section34VertexIndex 𝒦 𝒦'} (hne : w ≠ w')
    (hnadj : ¬ ∃ e : Section34EdgeIndex 𝒦 𝒦',
      (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1)) :
    Disjoint (src (.vertexBall w)) (src (.vertexBall w')) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨e, he, -⟩ := section34_vertex_cells_intersection_of_ne hcut ends hends hne ⟨x, hx, hx'⟩
  exact hnadj ⟨e, he⟩

theorem section34_vertex_cells_triple_inter_eq_empty
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (ends : Section34EdgeIndex 𝒦 𝒦' →
      Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) ∧
      src (.splitDisk e) = src (.vertexBall (ends e).1) ∩ src (.vertexBall (ends e).2))
    {w₀ w₁ w₂ : Section34VertexIndex 𝒦 𝒦'} (h₀₁ : w₀ ≠ w₁) (h₀₂ : w₀ ≠ w₂)
    (h₁₂ : w₁ ≠ w₂) :
    src (.vertexBall w₀) ∩ src (.vertexBall w₁) ∩ src (.vertexBall w₂) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨e, he, heq⟩ := section34_vertex_cells_intersection_of_ne hcut ends hends h₀₁
    ⟨x, hx.1.1, hx.1.2⟩
  obtain ⟨f, hf, hfq⟩ := section34_vertex_cells_intersection_of_ne hcut ends hends h₀₂
    ⟨x, hx.1.1, hx.2⟩
  have hef : e = f := by
    by_contra hne
    exact Set.disjoint_left.mp (section34_splitDisks_disjoint hcut hne)
      (heq.subset hx.1) (hfq.subset ⟨hx.1.1, hx.2⟩)
  subst f
  apply h₁₂
  rcases he with ⟨he₀, he₁⟩ | ⟨he₀, he₁⟩ <;>
    rcases hf with ⟨hf₀, hf₁⟩ | ⟨hf₀, hf₁⟩ <;> simp_all

end DifferentialGeometry.Topology.PiecewiseLinear
