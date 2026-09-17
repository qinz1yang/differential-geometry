import DifferentialGeometry.Topology.PiecewiseLinear.AmbientPointMove
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem exists_isPLHomeomorphOn_map_disk_of_interior_inter
    {A B U : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsPLBall 2 A) (hB : IsPLBall 2 B)
    (hU : IsOpen U) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hinter : (interior A ∩ interior B).Nonempty) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h '' A = B := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := (hA.isPolyhedron.union hB.isPolyhedron).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let Q : Fin 3 → Set (EuclideanSpace ℝ (Fin 2)) := ![A, B, A ∩ B]
  have hQ : ∀ i, IsPolyhedron (Q i) := by
    intro i
    fin_cases i
    · exact hA.isPolyhedron
    · exact hB.isPolyhedron
    · exact hA.isPolyhedron.inter hB.isPolyhedron
  have hQK : ∀ i, Q i ⊆ K.space := by
    rw [hKspace]
    intro i
    fin_cases i
    · exact subset_union_left
    · exact subset_union_right
    · exact inter_subset_left.trans subset_union_left
  obtain ⟨R, _, hRfin, hRcover⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  let _ : Finite R.faces := hRfin.to_subtype
  let L (i : Fin 3) := restrict R (Q i)
  have hL (i : Fin 3) : (L i).space = Q i := restrict_space_of_eq_biUnion R (Q i) (hRcover i)
  let _ (i : Fin 3) : Finite (L i).faces := (restrict_faces_finite R (Q i)).to_subtype
  obtain ⟨x, hxA, hxB⟩ := hinter
  have hx : x ∈ closure (interior (Q 2)) := by
    apply subset_closure
    change x ∈ interior (A ∩ B)
    rw [interior_inter]
    exact ⟨hxA, hxB⟩
  obtain ⟨t, ht, htcard, _⟩ := exists_face_card_eq_finrank_succ_of_mem_closure (L 2)
    isOpen_interior (show interior (Q 2) ⊆ (L 2).space by rw [hL 2]; exact interior_subset) hx
  have htcard' : t.card = 3 := by simpa using htcard
  have htA : t ∈ (L 0).faces := ⟨ht.1, ht.2.trans inter_subset_left⟩
  have htB : t ∈ (L 1).faces := ⟨ht.1, ht.2.trans inter_subset_right⟩
  obtain ⟨f, hf, hfA, hffix⟩ := exists_isPLHomeomorphOn_straighten_to_face (L 0)
    ((hL 0).symm ▸ hA) htA htcard' hU ((hL 0).trans_le hAU)
  obtain ⟨g, hg, hgB, hgfix⟩ := exists_isPLHomeomorphOn_straighten_to_face (L 1)
    ((hL 1).symm ▸ hB) htB htcard' hU ((hL 1).trans_le hBU)
  rw [hL 0] at hfA
  rw [hL 1] at hgB
  change f '' A = convexHull ℝ (t : Set _) at hfA
  change g '' B = convexHull ℝ (t : Set _) at hgB
  refine ⟨f.trans g.symm, hf.trans hg.homeomorph_symm, ?_, ?_⟩
  · intro z hz
    change g.symm (f z) = z
    exact (congrArg g.symm (hffix hz)).trans (g.symm_apply_eq.mpr (hgfix hz).symm)
  · change (g.symm ∘ f) '' A = B
    rw [image_comp, hfA, ← hgB]
    exact g.symm_image_image B

theorem exists_isPLHomeomorphOn_map_disk_eqOn_compl
    {A B U : Set (EuclideanSpace ℝ (Fin 2))} (hA : IsPLBall 2 A) (hB : IsPLBall 2 B)
    (hU : IsOpen U) (hc : IsPreconnected U) (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ∃ h : EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 2),
      IsPLHomeomorphOn h univ univ ∧ EqOn h id Uᶜ ∧ h '' A = B := by
  obtain ⟨p, hp⟩ := hA.interior_nonempty
  obtain ⟨q, hq⟩ := hB.interior_nonempty
  obtain ⟨f, hf, hffix, hfp⟩ := exists_isPLHomeomorphOn_map_point_eqOn_compl hU hc
    (hAU (interior_subset hp)) (hBU (interior_subset hq))
  have hA' : IsPLBall 2 (f '' A) :=
    hA.of_isPLHomeomorphOn (hf.restrict hA.isPolyhedron (subset_univ A))
  have hfU : f '' U = U := by
    have hcompl : f '' Uᶜ = Uᶜ := hffix.image_eq.trans (image_id _)
    have h := f.image_compl Uᶜ
    simpa only [compl_compl, hcompl] using h
  have hAU' : f '' A ⊆ U := (image_mono hAU).trans hfU.subset
  have hqA : q ∈ interior (f '' A) := by
    rw [← f.image_interior]
    exact ⟨p, hp, hfp⟩
  obtain ⟨g, hg, hgfix, hgA⟩ := exists_isPLHomeomorphOn_map_disk_of_interior_inter hA' hB
    hU hAU' hBU ⟨q, hqA, hq⟩
  refine ⟨f.trans g, hf.trans hg, ?_, ?_⟩
  · intro z hz
    exact (congrArg g (hffix hz)).trans (hgfix hz)
  · exact (image_comp g f A).trans hgA

end DifferentialGeometry.Topology.PiecewiseLinear
