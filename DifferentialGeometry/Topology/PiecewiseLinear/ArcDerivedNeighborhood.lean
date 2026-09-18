import DifferentialGeometry.Topology.PiecewiseLinear.BallChain
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Faces

variable {E : Type*}

open Classical in
noncomputable def arcChainFace (v : ℕ → E) (j : ℕ) : Finset E :=
  {v (j / 2), v ((j + 1) / 2)}

open Classical in
theorem mem_arcChainFace_iff {v : ℕ → E} {j : ℕ} {x : E} :
    x ∈ arcChainFace v j ↔ x = v (j / 2) ∨ x = v ((j + 1) / 2) := by
  simp only [arcChainFace, Finset.mem_insert, Finset.mem_singleton]

open Classical in
theorem arcChainFace_two_mul (v : ℕ → E) (k : ℕ) : arcChainFace v (2 * k) = {v k} := by
  have h₁ : 2 * k / 2 = k := by omega
  have h₂ : (2 * k + 1) / 2 = k := by omega
  simp only [arcChainFace, h₁, h₂, Finset.pair_eq_singleton]

open Classical in
theorem arcChainFace_two_mul_add_one (v : ℕ → E) (k : ℕ) :
    arcChainFace v (2 * k + 1) = {v k, v (k + 1)} := by
  have h₁ : (2 * k + 1) / 2 = k := by omega
  have h₂ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp only [arcChainFace, h₁, h₂]

theorem eq_of_subset_pair [DecidableEq E] {a b : E} {t : Finset E}
    (ht : t ⊆ ({a, b} : Finset E)) (hne : t.Nonempty) :
    t = {a} ∨ t = {b} ∨ t = ({a, b} : Finset E) := by
  have hmem : ∀ x ∈ t, x = a ∨ x = b := fun x hx => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using ht hx
  by_cases ha : a ∈ t
  · by_cases hb : b ∈ t
    · refine Or.inr (Or.inr (Finset.Subset.antisymm ht (fun x hx => ?_)))
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rcases Finset.mem_singleton.mp hx with rfl
        exact hb
    · refine Or.inl (Finset.Subset.antisymm (fun x hx => ?_) (Finset.singleton_subset_iff.mpr ha))
      rcases hmem x hx with rfl | rfl
      · exact Finset.mem_singleton_self _
      · exact absurd hx hb
  · by_cases hb : b ∈ t
    · refine Or.inr (Or.inl (Finset.Subset.antisymm (fun x hx => ?_)
        (Finset.singleton_subset_iff.mpr hb)))
      rcases hmem x hx with rfl | rfl
      · exact absurd hx ha
      · exact Finset.mem_singleton_self _
    · obtain ⟨y, hy⟩ := hne
      rcases hmem y hy with rfl | rfl
      · exact absurd hy ha
      · exact absurd hy hb

open Classical in
theorem exists_eq_arcChainFace_of_subset {n : ℕ} {v : ℕ → E} {j : ℕ} (hj : j ≤ 2 * n)
    {t : Finset E} (ht : t ⊆ arcChainFace v j) (hne : t.Nonempty) :
    ∃ k ≤ 2 * n, t = arcChainFace v k := by
  have ht' : t ⊆ ({v (j / 2), v ((j + 1) / 2)} : Finset E) := ht
  rcases eq_of_subset_pair ht' hne with h | h | h
  · exact ⟨2 * (j / 2), by omega, by rw [h, arcChainFace_two_mul]⟩
  · exact ⟨2 * ((j + 1) / 2), by omega, by rw [h, arcChainFace_two_mul]⟩
  · exact ⟨j, hj, h⟩

open Classical in
theorem arcChainFace_subset_iff {n : ℕ} {v : ℕ → E}
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) {i j : ℕ} (hi : i ≤ 2 * n) (hj : j ≤ 2 * n) :
    arcChainFace v i ⊆ arcChainFace v j ↔
      ((i / 2 = j / 2 ∨ i / 2 = (j + 1) / 2) ∧
        ((i + 1) / 2 = j / 2 ∨ (i + 1) / 2 = (j + 1) / 2)) := by
  constructor
  · intro h
    have h₁ := mem_arcChainFace_iff.mp (h (mem_arcChainFace_iff.mpr (Or.inl rfl)))
    have h₂ := mem_arcChainFace_iff.mp (h (mem_arcChainFace_iff.mpr (Or.inr rfl)))
    exact ⟨h₁.imp (fun hx => hinj _ (by omega) _ (by omega) hx)
        (fun hx => hinj _ (by omega) _ (by omega) hx),
      h₂.imp (fun hx => hinj _ (by omega) _ (by omega) hx)
        (fun hx => hinj _ (by omega) _ (by omega) hx)⟩
  · rintro ⟨h₁, h₂⟩ x hx
    rcases mem_arcChainFace_iff.mp hx with rfl | rfl
    · exact mem_arcChainFace_iff.mpr (h₁.imp (fun h => by rw [h]) (fun h => by rw [h]))
    · exact mem_arcChainFace_iff.mpr (h₂.imp (fun h => by rw [h]) (fun h => by rw [h]))

end Faces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_derivedNeighborhoodCell_of_chain
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {m : ℕ} (F : Fin (m + 1) → Finset E)
    (hF : ∀ j, F j ∈ K.faces)
    (hne : ∀ j : Fin m, F j.castSucc ≠ F j.succ)
    (hcmp : ∀ j : Fin m, F j.castSucc ⊆ F j.succ ∨ F j.succ ⊆ F j.castSucc)
    (hfar : ∀ i j : Fin (m + 1), i.val + 1 < j.val → ¬F i ⊆ F j ∧ ¬F j ⊆ F i) :
    IsPLBall 3 (⋃ j, (derivedNeighborhoodCell K (F j)).space) :=
  hK.isPLBall_iUnion_of_chain (fun j => (derivedNeighborhoodCell K (F j)).space)
    (fun j => hK.isPLBall_derivedNeighborhoodCell (n := 2) (hF j))
    (fun j => derivedNeighborhoodCell_space_subset K (F j))
    (fun j => hK.isPLBall_derivedNeighborhoodCell_inter (n := 1) (hF _) (hF _) (hne j) (hcmp j))
    (fun i j hij => disjoint_derivedNeighborhoodCell_space K (hF i) (hF j)
      (hfar i j hij).1 (hfar i j hij).2)

omit [FiniteDimensional ℝ E] in
open Classical in
theorem arcChainFace_mem_faces {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    {j : ℕ} (hj : j ≤ 2 * n) : arcChainFace v j ∈ K.faces := by
  obtain ⟨k, hk | hk⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · subst hk
    rw [arcChainFace_two_mul]
    exact hvert k (by omega)
  · subst hk
    rw [arcChainFace_two_mul_add_one]
    exact hedge k (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_iUnion_arcChainFace
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) :
    IsPLBall 3 (⋃ j : Fin (2 * n + 1),
      (derivedNeighborhoodCell K (arcChainFace v j.val)).space) := by
  refine hK.isPLBall_iUnion_derivedNeighborhoodCell_of_chain
    (fun j : Fin (2 * n + 1) => arcChainFace v j.val)
    (fun j => arcChainFace_mem_faces hvert hedge (by omega))
    (fun j => ?_) (fun j => ?_) (fun i j hij => ?_)
  · have hlt := j.isLt
    have hc : j.castSucc.val = j.val := Fin.val_castSucc j
    have hs : j.succ.val = j.val + 1 := Fin.val_succ j
    intro heq
    have hsub₁ : arcChainFace v j.castSucc.val ⊆ arcChainFace v j.succ.val := heq ▸ subset_rfl
    have hsub₂ : arcChainFace v j.succ.val ⊆ arcChainFace v j.castSucc.val := heq ▸ subset_rfl
    rw [arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs] at hsub₁
    rw [arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs] at hsub₂
    omega
  · have hlt := j.isLt
    have hc : j.castSucc.val = j.val := Fin.val_castSucc j
    have hs : j.succ.val = j.val + 1 := Fin.val_succ j
    rw [arcChainFace_subset_iff hinj (by omega) (by omega),
      arcChainFace_subset_iff hinj (by omega) (by omega), hc, hs]
    omega
  · have hi := i.isLt
    have hjlt := j.isLt
    rw [arcChainFace_subset_iff hinj (by omega) (by omega),
      arcChainFace_subset_iff hinj (by omega) (by omega)]
    omega

open Classical in
noncomputable def arcComplexIn (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (n : ℕ) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | ∃ j ≤ 2 * n, s = arcChainFace v j}
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
  isRelLowerSet_faces := by
    rintro t ⟨ht, j, hj, rfl⟩
    exact ⟨K.nonempty_of_mem_faces ht, fun t' ht't ht' =>
      ⟨K.down_closed ht ht't ht', exists_eq_arcChainFace_of_subset hj ht't ht'⟩⟩

omit [FiniteDimensional ℝ E] in
open Classical in
theorem arcComplexIn_faces_subset (K : Geometry.SimplicialComplex ℝ E) (v : ℕ → E) (n : ℕ) :
    (arcComplexIn K v n).faces ⊆ K.faces :=
  fun _ hs => hs.1

open Classical in
instance (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (v : ℕ → E) (n : ℕ) :
    Finite (arcComplexIn K v n).faces :=
  ((Set.toFinite K.faces).subset fun _ hs => hs.1).to_subtype

omit [FiniteDimensional ℝ E] in
open Classical in
theorem iUnion_derivedNeighborhoodCell_arcChainFace_eq
    {K : Geometry.SimplicialComplex ℝ E} {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces) :
    (⋃ j : Fin (2 * n + 1), (derivedNeighborhoodCell K (arcChainFace v j.val)).space) =
      (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  rw [← iUnion_derivedNeighborhoodCell_space K (arcComplexIn K v n)
    (arcComplexIn_faces_subset K v n)]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hlt := j.isLt
    exact mem_iUnion₂.mpr ⟨arcChainFace v j.val,
      ⟨arcChainFace_mem_faces hvert hedge (by omega), j.val, by omega, rfl⟩, hj⟩
  · intro x hx
    obtain ⟨s, ⟨-, j, hj, rfl⟩, hxs⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨j, by omega⟩, hxs⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_derivedNeighborhood_arcComplexIn
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {n : ℕ} {v : ℕ → E}
    (hvert : ∀ i ≤ n, ({v i} : Finset E) ∈ K.faces)
    (hedge : ∀ i < n, ({v i, v (i + 1)} : Finset E) ∈ K.faces)
    (hinj : ∀ i ≤ n, ∀ j ≤ n, v i = v j → i = j) :
    IsPLBall 3 (PiecewiseLinear.derivedNeighborhood K (arcComplexIn K v n)).space := by
  rw [← iUnion_derivedNeighborhoodCell_arcChainFace_eq hvert hedge]
  exact hK.isPLBall_iUnion_arcChainFace hvert hedge hinj

end DifferentialGeometry.Topology.PiecewiseLinear
