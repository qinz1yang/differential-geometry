import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldFaces
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryInvariance

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem mem_boundaryComplex_complement_iff {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) (subcomplexGeneratedBy K A.facesᶜ))
    {s : Finset E} (hcard : s.card = n + 1) :
    s ∈ (boundaryComplex (n + 1) (subcomplexGeneratedBy K A.facesᶜ)).faces ↔
      (s ∈ (boundaryComplex (n + 1) K).faces ∧ s ∉ A.faces) ∨
        (s ∈ (boundaryComplex (n + 1) A).faces ∧ s ∉ (boundaryComplex (n + 1) K).faces) := by
  classical
  let R := subcomplexGeneratedBy K A.facesᶜ
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K A.facesᶜ).to_subtype
  by_cases hsK : s ∈ K.faces
  · have htop {t : Finset E} (htcard : t.card = n + 2) :
        t ∈ R.faces ↔ t ∈ K.faces ∧ t ∉ A.faces := by
      constructor
      · rintro ⟨u, ⟨huK, huA⟩, htu, -⟩
        have heq : t = u := Finset.eq_of_subset_of_card_le htu (by
          have := hK.card_le K huK
          omega)
        exact heq.symm ▸ ⟨huK, huA⟩
      · intro ht
        exact ⟨t, ht, Finset.Subset.rfl, K.nonempty_of_mem_faces ht.1⟩
    let VK := {w | w ∉ s ∧ insert w s ∈ K.faces}
    let VA := {w | w ∉ s ∧ insert w s ∈ A.faces}
    let VR := {w | w ∉ s ∧ insert w s ∈ R.faces}
    have hsub : VA ⊆ VK := fun _ hw => ⟨hw.1, hAK hw.2⟩
    have hKcard : VK.ncard = 1 ∨ VK.ncard = 2 := by
      rcases hK.codimension_one_cofaces K hsK hcard with ⟨a, ha⟩ | ⟨a, b, hab, ha⟩
      · exact Or.inl (by dsimp only [VK]; rw [ha, ncard_singleton])
      · exact Or.inr (by dsimp only [VK]; rw [ha, ncard_pair hab])
    have hfin : VK.Finite := finite_of_ncard_pos (by omega)
    have hAmem : s ∈ A.faces ↔ 0 < VA.ncard := by
      rw [ncard_pos (hfin.subset hsub)]
      constructor
      · intro hsA
        rcases hA.codimension_one_cofaces A hsA hcard with ⟨a, ha⟩ | ⟨a, b, -, ha⟩
        · exact ⟨a, by change a ∈ {w | w ∉ s ∧ insert w s ∈ A.faces}; rw [ha]; exact mem_singleton a⟩
        · exact ⟨a, by change a ∈ {w | w ∉ s ∧ insert w s ∈ A.faces}; rw [ha]; exact mem_insert a {b}⟩
      · rintro ⟨w, hw⟩
        exact A.down_closed hw.2 (Finset.subset_insert w s)
          (Finset.card_pos.mp (by omega))
    have hdiff : VR = VK \ VA := by
      ext w
      change (w ∉ s ∧ insert w s ∈ R.faces) ↔
        (w ∉ s ∧ insert w s ∈ K.faces) ∧ ¬(w ∉ s ∧ insert w s ∈ A.faces)
      by_cases hw : w ∈ s
      · simp only [hw, not_true_eq_false, false_and, not_false_eq_true]
      · rw [htop (by rw [Finset.card_insert_of_notMem hw, hcard])]
        tauto
    have hKB : s ∈ (boundaryComplex (n + 1) K).faces ↔ VK.ncard = 1 := by
      rw [hK.mem_boundaryComplex_iff_unique_coface K hcard, ncard_eq_one]
    have hAB : s ∈ (boundaryComplex (n + 1) A).faces ↔ VA.ncard = 1 := by
      rw [hA.mem_boundaryComplex_iff_unique_coface A hcard, ncard_eq_one]
    have hRB : s ∈ (boundaryComplex (n + 1) R).faces ↔ VR.ncard = 1 := by
      rw [hR.mem_boundaryComplex_iff_unique_coface R hcard, ncard_eq_one]
    change s ∈ (boundaryComplex (n + 1) R).faces ↔ _
    rw [hRB, hKB, hAB, hAmem, hdiff, ncard_sdiff' hsub hfin]
    have := ncard_le_ncard hsub hfin
    omega
  · constructor
    · intro hs
      exact (hsK (subcomplexGeneratedBy_faces_subset K A.facesᶜ
        (boundaryComplex_faces_subset (n + 1) R hs))).elim
    · rintro (hs | hs)
      · exact (hsK (boundaryComplex_faces_subset (n + 1) K hs.1)).elim
      · exact (hsK (hAK (boundaryComplex_faces_subset (n + 1) A hs.1))).elim

open Classical in
theorem boundaryComplex_complement_space {n : ℕ}
    (K A : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.faces ⊆ K.faces)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) (subcomplexGeneratedBy K A.facesᶜ)) :
    (boundaryComplex (n + 1) (subcomplexGeneratedBy K A.facesᶜ)).space =
      closure ((boundaryComplex (n + 1) K).space \ A.space) ∪
        closure ((boundaryComplex (n + 1) A).space \ (boundaryComplex (n + 1) K).space) := by
  classical
  let R := subcomplexGeneratedBy K A.facesᶜ
  let B := boundaryComplex (n + 1) K
  let C := boundaryComplex (n + 1) A
  let B' := boundaryComplex (n + 1) R
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K A.facesᶜ).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite (n + 1) K).to_subtype
  let _ : Finite C.faces := (boundaryComplex_faces_finite (n + 1) A).to_subtype
  let _ : Finite B'.faces := (boundaryComplex_faces_finite (n + 1) R).to_subtype
  have hB := isCombinatorialManifold_boundaryComplex K hK
  have hC := isCombinatorialManifold_boundaryComplex A hA
  have hB' := isCombinatorialManifold_boundaryComplex R hR
  have hCK : C.faces ⊆ K.faces := (boundaryComplex_faces_subset (n + 1) A).trans hAK
  have hmem {s : Finset E} (hs : s.card = n + 1) :
      s ∈ B'.faces ↔ (s ∈ B.faces ∧ s ∉ A.faces) ∨ (s ∈ C.faces ∧ s ∉ B.faces) :=
    mem_boundaryComplex_complement_iff K A hK hA hAK hR hs
  change B'.space = closure (B.space \ A.space) ∪ closure (C.space \ B.space)
  rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy K B A
      (boundaryComplex_faces_subset (n + 1) K) hAK,
    closure_space_sdiff_space_eq_subcomplexGeneratedBy K C B hCK
      (boundaryComplex_faces_subset (n + 1) K), subcomplexGeneratedBy_space,
    subcomplexGeneratedBy_space]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := B'.mem_space_iff.mp hx
    obtain ⟨t, ht, hst, htc⟩ := hB'.exists_face_superset_card_eq B' hs
    have hxt := convexHull_mono (Finset.coe_subset.mpr hst) hxs
    rcases (hmem htc).mp ht with ht | ht
    · exact Or.inl (mem_iUnion₂.mpr ⟨t, ht, hxt⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨t, ht, hxt⟩)
  · rintro x (hx | hx)
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, ht, hst, htc⟩ := hB.exists_face_superset_card_eq B hs.1
      have htA : t ∉ A.faces := fun htA =>
        hs.2 (A.down_closed htA hst (B.nonempty_of_mem_faces hs.1))
      exact B'.convexHull_subset_space ((hmem htc).mpr (Or.inl ⟨ht, htA⟩))
        (convexHull_mono (Finset.coe_subset.mpr hst) hxs)
    · obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      obtain ⟨t, ht, hst, htc⟩ := hC.exists_face_superset_card_eq C hs.1
      have htB : t ∉ B.faces := fun htB =>
        hs.2 (B.down_closed htB hst (C.nonempty_of_mem_faces hs.1))
      exact B'.convexHull_subset_space ((hmem htc).mpr (Or.inr ⟨ht, htB⟩))
        (convexHull_mono (Finset.coe_subset.mpr hst) hxs)

open Classical in
theorem boundaryComplex_space_of_closure_sdiff {n : ℕ}
    (K A R : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite A.faces] [Finite R.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hA : IsCombinatorialManifoldWithBoundary (n + 1) A) (hAK : A.space ⊆ K.space)
    (hR : IsCombinatorialManifoldWithBoundary (n + 1) R)
    (hRspace : R.space = closure (K.space \ A.space)) :
    (boundaryComplex (n + 1) R).space =
      closure ((boundaryComplex (n + 1) K).space \ A.space) ∪
        closure ((boundaryComplex (n + 1) A).space \ (boundaryComplex (n + 1) K).space) := by
  classical
  obtain ⟨T, hT, hTfin, hTA⟩ := exists_isSubdivision_restrict_isSubdivision K A hAK
  let _ : Finite T.faces := hTfin.to_subtype
  let B := restrict T A.space
  let _ : Finite B.faces := (restrict_faces_finite T A.space).to_subtype
  let L := subcomplexGeneratedBy T B.facesᶜ
  let _ : Finite L.faces := (subcomplexGeneratedBy_faces_finite T B.facesᶜ).to_subtype
  have hLspace : L.space = R.space := by
    rw [show L.space = (subcomplexGeneratedBy T B.facesᶜ).space from rfl,
      ← closure_space_sdiff_space_eq_subcomplexGeneratedBy T T B Subset.rfl
        (restrict_faces_subset T A.space), hT.space_eq, hTA.space_eq, hRspace]
  have hid : IsPLHomeomorphOn (id : E → E) R.space L.space := by
    rw [hLspace]
    exact (isPolyhedron_space R).isPLHomeomorphOn_id
  have hL := hR.of_isPLHomeomorphOn hid
  have hbd : (boundaryComplex (n + 1) L).space = (boundaryComplex (n + 1) R).space := by
    simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn R L hR hid
  have heq := boundaryComplex_complement_space T B (hK.of_isSubdivision hT)
    (hA.of_isSubdivision hTA) (restrict_faces_subset T A.space) hL
  rw [show (subcomplexGeneratedBy T B.facesᶜ) = L from rfl, hbd,
    boundaryComplex_space_of_isSubdivision K T hK hT,
    boundaryComplex_space_of_isSubdivision A B hA hTA, hTA.space_eq] at heq
  exact heq
end DifferentialGeometry.Topology.PiecewiseLinear
