import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedron

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
def IsCombinatorialManifoldWithBoundary : ℕ → Geometry.SimplicialComplex ℝ E → Prop
  | 0, K => ∀ v, {v} ∈ K.faces → (SimplicialComplex.geometricLink K {v}).faces = ∅
  | n + 1, K => ∀ v, {v} ∈ K.faces → IsPLSphere n (SimplicialComplex.geometricLink K {v}).space ∨
      IsPLBall n (SimplicialComplex.geometricLink K {v}).space

theorem IsCombinatorialManifold.isCombinatorialManifoldWithBoundary {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} (h : IsCombinatorialManifold n K) :
    IsCombinatorialManifoldWithBoundary n K := by
  cases n with
  | zero => exact h
  | succ n => exact fun v hv => Or.inl (h v hv)

open Classical in
theorem IsGlueIso.isCombinatorialManifoldWithBoundary {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    [Finite L.faces] {φ : E → F} {φ' : F → E} (h : IsGlueIso K L φ φ')
    (hK : IsCombinatorialManifoldWithBoundary n K) : IsCombinatorialManifoldWithBoundary n L := by
  cases n with
  | zero =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have := hiso.image₂ t ht
    rw [hK _ hv] at this
    exact this
  | succ n =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    have hpl := hiso.isPLHomeomorphOn
    rcases hK _ hv with hs | hb
    · exact Or.inl (hs.of_isPLHomeomorphOn hpl)
    · exact Or.inr (hb.of_isPLHomeomorphOn hpl)

open Classical in
theorem IsGlueIso.isCombinatorialManifold {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} {L : Geometry.SimplicialComplex ℝ F} [Finite K.faces]
    [Finite L.faces] {φ : E → F} {φ' : F → E} (h : IsGlueIso K L φ φ')
    (hK : IsCombinatorialManifold n K) : IsCombinatorialManifold n L := by
  cases n with
  | zero =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    rw [Set.eq_empty_iff_forall_notMem]
    intro t ht
    have := hiso.image₂ t ht
    rw [hK _ hv] at this
    exact this
  | succ n =>
    intro w hw
    have hv : {φ' w} ∈ K.faces := h.symm.singleton_mem hw
    have hφ : φ (φ' w) = w := h.right _ hw w (Finset.mem_singleton_self w)
    have hiso := h.geometricLink hv
    rw [hφ] at hiso
    exact (hK _ hv).of_isPLHomeomorphOn hiso.isPLHomeomorphOn

section Boundary

variable [DecidableEq E] (n : ℕ) (K : Geometry.SimplicialComplex ℝ E)

def boundaryFaces : Set (Finset E) :=
  {s | s ∈ K.faces ∧ ∃ t ∈ K.faces, s ⊆ t ∧ t.card ≤ n ∧
    IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space}

def boundaryComplex : Geometry.SimplicialComplex ℝ E where
  faces := boundaryFaces n K
  isRelLowerSet_faces := by
    rintro s ⟨hs, t, ht, hst, htn, hball⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun u hus hu =>
      ⟨K.down_closed hs hus hu, t, ht, hus.trans hst, htn, hball⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem mem_boundaryComplex_faces_iff {s : Finset E} :
    s ∈ (boundaryComplex n K).faces ↔ s ∈ K.faces ∧ ∃ t ∈ K.faces, s ⊆ t ∧ t.card ≤ n ∧
      IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space := Iff.rfl

theorem boundaryComplex_faces_subset : (boundaryComplex n K).faces ⊆ K.faces := fun _ hs => hs.1

theorem boundaryComplex_faces_finite [Finite K.faces] : (boundaryComplex n K).faces.Finite :=
  (Set.toFinite K.faces).subset (boundaryComplex_faces_subset n K)

theorem boundaryComplex_space_subset : (boundaryComplex n K).space ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (boundaryComplex n K).mem_space_iff.mp hx
  exact K.convexHull_subset_space hs.1 hxs

theorem mem_boundaryComplex_faces_of_isPLBall {t : Finset E} (ht : t ∈ K.faces) (htn : t.card ≤ n)
    (hball : IsPLBall (n - t.card) (SimplicialComplex.geometricLink K t).space) :
    t ∈ (boundaryComplex n K).faces := ⟨ht, t, ht, subset_rfl, htn, hball⟩

theorem geometricLink_boundaryComplex (v : E) :
    SimplicialComplex.geometricLink (boundaryComplex (n + 1) K) {v} =
      boundaryComplex n (SimplicialComplex.geometricLink K {v}) := by
  ext t
  simp only [SimplicialComplex.mem_geometricLink_singleton, mem_boundaryComplex_faces_iff]
  constructor
  · rintro ⟨htne, hvt, hins, u, hu, hsub, hun, hball⟩
    have hvu : v ∈ u := hsub (Finset.mem_insert_self v t)
    have hne : (u.erase v).Nonempty := by
      obtain ⟨w, hw⟩ := htne
      exact ⟨w, Finset.mem_erase.mpr ⟨fun h => hvt (h ▸ hw), hsub (Finset.mem_insert_of_mem hw)⟩⟩
    refine ⟨⟨htne, hvt, hins⟩, u.erase v,
      ⟨hne, Finset.notMem_erase v u, by rwa [Finset.insert_erase hvu]⟩, ?_, ?_, ?_⟩
    · intro w hw
      exact Finset.mem_erase.mpr ⟨fun h => hvt (h ▸ hw), hsub (Finset.mem_insert_of_mem hw)⟩
    · have := Finset.card_erase_of_mem hvu
      omega
    · have hcard : n - (u.erase v).card = n + 1 - u.card := by
        have := Finset.card_erase_of_mem hvu
        have := Finset.card_pos.mpr ⟨v, hvu⟩
        omega
      rw [hcard, ← geometricLink_insert K (Finset.notMem_erase v u), Finset.insert_erase hvu]
      exact hball
  · rintro ⟨⟨htne, hvt, hins⟩, u, ⟨hune, hvu, hinsu⟩, hsub, hun, hball⟩
    refine ⟨htne, hvt, hins, insert v u, hinsu, Finset.insert_subset_insert v hsub, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvu]
      omega
    · have hcard : n + 1 - (insert v u).card = n - u.card := by
        rw [Finset.card_insert_of_notMem hvu]
        omega
      rw [hcard, geometricLink_insert K hvu]
      exact hball

end Boundary

end DifferentialGeometry.Topology.PiecewiseLinear
