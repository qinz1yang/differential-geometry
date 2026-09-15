import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Classical in
private theorem mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_isSubdivision
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    {K' : Geometry.SimplicialComplex ℝ E} [Finite K'.faces] (hK' : IsSubdivision K' K)
    {x : E} (hx' : {x} ∈ K'.faces) :
    x ∈ (boundaryComplex (n + 1) K).space ↔
      IsPLBall n (SimplicialComplex.geometricLink K' {x}).space := by
  classical
  have hxK : x ∈ K.space := by
    rw [← hK'.space_eq]
    exact K'.convexHull_subset_space hx' (subset_convexHull ℝ _ (by simp))
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex K hxK
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 :=
    ⟨t.card - 1, by have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht); omega⟩
  have hcardle := hK.card_le K ht
  constructor
  · intro hxB
    obtain ⟨s, hs, hxs⟩ := (boundaryComplex (n + 1) K).mem_space_iff.mp hxB
    have hts : t ⊆ s :=
      face_subset_of_mem_openSimplex_of_mem_convexHull K ht hs.1 hxt hxs
    have htB : t ∈ (boundaryComplex (n + 1) K).faces :=
      (boundaryComplex (n + 1) K).down_closed hs hts (K.nonempty_of_mem_faces ht)
    have htB' := (hK.mem_boundaryComplex_faces_iff K).mp htB
    have htcard : t.card ≤ n + 1 := htB'.2.1
    have hball := htB'.2.2
    have hres := isPLBall_geometricLink_of_isPLBall_geometricLink K ht hxt hK' hx' hk hball
    rwa [show k + (n + 1 - t.card) = n by omega] at hres
  · intro hxball
    by_cases hkn : k ≤ n
    · rcases hK.isPLSphere_or_isPLBall_geometricLink K ht hk hkn with hsphere | hball
      · exfalso
        have hres := isPLSphere_geometricLink_of_isPLSphere_geometricLink K ht hxt hK' hx' hk hsphere
        rw [show k + (n - k) = n by omega] at hres
        exact hxball.not_isPLSphere hres
      · refine (boundaryComplex (n + 1) K).convexHull_subset_space
          ((hK.mem_boundaryComplex_faces_iff K).mpr ⟨ht, by omega, ?_⟩)
          (openSimplex_subset_convexHull t hxt)
        rwa [show n + 1 - t.card = n - k by omega]
    · exfalso
      have hres := isPLSphere_geometricLink_of_forall_card_le K
        (fun s hs => hK.card_le K hs) ht (by omega) hxt hK' hx'
      exact hxball.not_isPLSphere hres

open Classical in
theorem mem_boundaryComplex_space_iff_of_isPLHomeomorphOn [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (L : Geometry.SimplicialComplex ℝ F) [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {f : E → F}
    (hf : IsPLHomeomorphOn f K.space L.space) {x : E} (hx : x ∈ K.space) :
    x ∈ (boundaryComplex (n + 1) K).space ↔
      f x ∈ (boundaryComplex (n + 1) L).space := by
  classical
  obtain ⟨K₀, hK₀, hK₀fin, hx₀⟩ := exists_isSubdivision_singleton_mem K hx
  letI : Finite K₀.faces := hK₀fin.to_subtype
  have hf₀ : IsPLHomeomorphOn f K₀.space L.space := by
    rwa [hK₀.space_eq]
  obtain ⟨K₁, L₁, f', hK₁, hK₁fin, hL₁, hL₁fin, hiso, -⟩ :=
    exists_isGlueIso_of_isPLHomeomorphOn K₀ L hf₀
  letI : Finite K₁.faces := hK₁fin.to_subtype
  letI : Finite L₁.faces := hL₁fin.to_subtype
  have hx₁ : {x} ∈ K₁.faces := hK₁.singleton_mem hx₀
  have hfx₁ : {f x} ∈ L₁.faces := hiso.singleton_mem hx₁
  have hL : IsCombinatorialManifoldWithBoundary (n + 1) L := hK.of_isPLHomeomorphOn hf
  rw [mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_isSubdivision K hK
      (hK₁.trans hK₀) hx₁,
    mem_boundaryComplex_space_iff_isPLBall_geometricLink_of_isSubdivision L hL hL₁ hfx₁]
  have hlink := (hiso.geometricLink hx₁).isPLHomeomorphOn
  exact ⟨fun h => h.of_isPLHomeomorphOn hlink,
    fun h => h.of_isPLHomeomorphOn hlink.symm⟩

private theorem boundaryComplex_zero_space [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) : (boundaryComplex 0 K).space = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨s, hs, -⟩ := (boundaryComplex 0 K).mem_space_iff.mp hx
  obtain ⟨-, t, ht, -, hcard, -⟩ := hs
  have := Finset.card_pos.mpr (K.nonempty_of_mem_faces ht)
  omega

open Classical in
private theorem PLPieceIn.image_boundaryComplex_eq {n : ℕ} {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {m : ℕ} {P : Set X}
    (T₁ : PLPieceIn E n X P) (T₂ : PLPieceIn F n X P)
    (hT₁ : IsCombinatorialManifoldWithBoundary (m + 1) T₁.complex) :
    T₁.map '' (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₁.complex).space =
      T₂.map '' (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₂.complex).space := by
  classical
  haveI : Finite T₁.complex.faces := T₁.finite_faces.to_subtype
  haveI : Finite T₂.complex.faces := T₂.finite_faces.to_subtype
  have htrans := T₁.isPLHomeomorphOn_transition T₂
  have hT₂ : IsCombinatorialManifoldWithBoundary (m + 1) T₂.complex :=
    hT₁.of_isPLHomeomorphOn htrans
  apply Subset.antisymm
  · rintro y ⟨x, hxB, rfl⟩
    have hxK := boundaryComplex_space_subset (m + 1) T₁.complex hxB
    let z := Function.invFunOn T₂.map T₂.complex.space (T₁.map x)
    have hzK : z ∈ T₂.complex.space :=
      T₂.bijOn.surjOn.mapsTo_invFunOn (T₁.bijOn.mapsTo hxK)
    have hzB : z ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₂.complex).space :=
      (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn T₁.complex T₂.complex hT₁
        htrans hxK).mp hxB
    exact ⟨z, hzB, T₂.bijOn.invOn_invFunOn.2 (T₁.bijOn.mapsTo hxK)⟩
  · rintro y ⟨z, hzB, rfl⟩
    have hzK := boundaryComplex_space_subset (m + 1) T₂.complex hzB
    let x := Function.invFunOn T₁.map T₁.complex.space (T₂.map z)
    have hxK : x ∈ T₁.complex.space :=
      T₁.bijOn.surjOn.mapsTo_invFunOn (T₂.bijOn.mapsTo hzK)
    have hxB : x ∈ (@boundaryComplex _ _ _ (Classical.decEq _) (m + 1) T₁.complex).space :=
      (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn T₂.complex T₁.complex hT₂
        (T₂.isPLHomeomorphOn_transition T₁) hzK).mp hzB
    exact ⟨x, hxB, T₁.bijOn.invOn_invFunOn.2 (T₂.bijOn.mapsTo hzK)⟩

open Classical in
noncomputable def polyhedralBoundary {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] (m : ℕ) (P : Set X)
    (h : IsPolyhedralManifoldWithBoundary (n := n) m P) : Set X :=
  let T := Classical.choose h
  T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space

open Classical in
theorem polyhedralBoundary_eq_of_piece {n : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {m : ℕ} {P : Set X}
    (h : IsPolyhedralManifoldWithBoundary (n := n) m P) (T : PLPiece n X P) :
    polyhedralBoundary m P h =
      T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space := by
  classical
  let T₀ := Classical.choose h
  have hT₀ : IsCombinatorialManifoldWithBoundary m T₀.piece.complex :=
    Classical.choose_spec h
  change T₀.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T₀.piece.complex).space =
    T.piece.map '' (@boundaryComplex _ _ _ (Classical.decEq _) m T.piece.complex).space
  cases m with
  | zero =>
    have hzero₀ := @boundaryComplex_zero_space _ _ _ (Classical.decEq _)
      T₀.piece.complex
    have hzero := @boundaryComplex_zero_space _ _ _ (Classical.decEq _)
      T.piece.complex
    rw [hzero₀, hzero, image_empty, image_empty]
  | succ m => exact T₀.piece.image_boundaryComplex_eq T.piece hT₀

end DifferentialGeometry.Topology.PiecewiseLinear
