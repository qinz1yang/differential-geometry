/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskInteriorMove
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceDiskNeighborhoodS31

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem exists_disk_in_surface_disk_off_circle
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {N J : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N)
    (hNK : N ⊆ K.space) (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) :
    ∃ B : Set E, IsPLBall 2 B ∧ B ⊆ N \ r '' stdSimplexBoundary 2 ∧ Disjoint B J := by
  classical
  have hN : IsPLBall 2 N := ⟨r, hr⟩
  let P : Bool → Set E := fun b => if b then J else N
  have hP : ∀ b, IsPolyhedron (P b) := by
    intro b
    cases b
    · exact hN.isPolyhedron
    · exact hJ.isPolyhedron
  have hPK : ∀ b, P b ⊆ K.space := by
    intro b
    cases b
    · exact hNK
    · exact hJK
  obtain ⟨R, hR, hRfin, hRP⟩ := exists_isSubdivision_subcomplexes K P hP hPK
  let _ : Finite R.faces := hRfin.to_subtype
  let A := restrict R N
  let C := restrict R J
  let _ : Finite A.faces := (restrict_faces_finite R N).to_subtype
  let _ : Finite C.faces := (restrict_faces_finite R J).to_subtype
  have hAN : A.space = N := restrict_space_of_eq_biUnion R N (hRP false)
  have hCJ : C.space = J := restrict_space_of_eq_biUnion R J (hRP true)
  have hA : IsPLBall 2 A.space := hAN.symm ▸ hN
  have hC : IsPLSphere 1 C.space := hCJ.symm ▸ hJ
  obtain ⟨x, hx⟩ := hA.nonempty
  obtain ⟨s, hs, -⟩ := A.mem_space_iff.mp hx
  obtain ⟨t, ht, -, htc⟩ := exists_face_superset_card_eq_of_isPLBall A hA hs
  let p := t.centroid ℝ id
  have hpt : p ∈ openSimplex t := centroid_mem_openSimplex_of_mem_faces A t ht
  have hpN : p ∈ N := hAN ▸ A.convexHull_subset_space ht (openSimplex_subset_convexHull t hpt)
  have hpJ : p ∉ J := by
    rw [← hCJ]
    apply notMem_space_of_notMem_faces (restrict_faces_subset R J) ht.1 ?_ hpt
    intro htC
    have := card_le_of_isPLSphere C hC htC
    omega
  have hpB : p ∉ (boundaryComplex 2 A).space := by
    apply notMem_space_of_notMem_faces (boundaryComplex_faces_subset 2 A) ht ?_ hpt
    intro htb
    obtain ⟨-, u, -, htu, huc, -⟩ := (mem_boundaryComplex_faces_iff 2 A).mp htb
    have := Finset.card_le_card htu
    omega
  have hb : (boundaryComplex 2 A).space = r '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex A (hAN.symm ▸ hr),
      simplexBoundary_stdVertices_space]
  have hpQ : p ∉ closure (K.space \ N) := by
    intro hpQ
    exact hpB (hb.symm ▸ (hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK ▸
      ⟨hpN, hpQ⟩))
  obtain ⟨B, hB, hBK, -⟩ := hK.exists_isPLBall_subset_of_mem_nhds (hNK hpN)
    ((hJ.isPolyhedron.isClosed.isOpen_compl.inter isClosed_closure.isOpen_compl).mem_nhds
      ⟨hpJ, hpQ⟩)
  refine ⟨B, hB, ?_, disjoint_left.mpr fun x hx => (hBK hx).2.1⟩
  intro x hx
  have hxK := (hBK hx).1
  have hxQ := (hBK hx).2.2
  have hxN : x ∈ N := by
    by_contra hn
    exact hxQ (subset_closure ⟨hxK, hn⟩)
  refine ⟨hxN, ?_⟩
  intro hxb
  exact hxQ ((hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK).symm ▸ hxb).2

private theorem extend_surface_disk_move
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {N : Set E}
    {r : (Fin 3 → ℝ) → E} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) N)
    (hNK : N ⊆ K.space) {f : E → E} (hf : IsPLHomeomorphOn f N N)
    (hfix : EqOn f id (r '' stdSimplexBoundary 2)) :
    ∃ F : E → E, IsPLHomeomorphOn F K.space K.space ∧ EqOn F f N ∧
      EqOn F id (K.space \ N) ∧ ∃ H : unitInterval × K.space → E,
        Continuous H ∧ (∀ x, H (0, x) = x.val) ∧ (∀ x, H (1, x) = F x.val) ∧
        ∀ w, H w ∈ K.space := by
  classical
  have hN : IsPLBall 2 N := ⟨r, hr⟩
  let Q := closure (K.space \ N)
  have hQ : IsPolyhedron Q := (isPolyhedron_space K).closure_sdiff hN.isPolyhedron
  have hQK : Q ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hmeet : N ∩ Q = r '' stdSimplexBoundary 2 :=
    hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK
  have hfixQ : EqOn f id (N ∩ Q) := hmeet.symm ▸ hfix
  have hcover : N ∪ Q = K.space := by
    apply Subset.antisymm (union_subset hNK hQK)
    intro x hx
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · exact Or.inr (subset_closure ⟨hx, hxN⟩)
  let F := N.piecewise f id
  have hF : IsPLHomeomorphOn F K.space K.space := by
    rw [← hcover]
    exact hf.piecewise hQ.isPLHomeomorphOn_id hN.isPolyhedron hQ hfixQ
      (hfixQ.image_eq.trans (image_id _))
  let q := Function.invFunOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
  have hqr : ∀ x ∈ N, r (q x) = x := hr.bijOn.invOn_invFunOn.2
  have hqN : MapsTo q N (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hr.bijOn.surjOn.mapsTo_invFunOn
  let V : Set (unitInterval × K.space) := {w | w.2.val ∈ N}
  let a : unitInterval × K.space → Fin 3 → ℝ := fun w =>
    (1 - (w.1 : ℝ)) • q w.2.val + (w.1 : ℝ) • q (f w.2.val)
  let J : unitInterval × K.space → E := fun w => r (a w)
  have ha : MapsTo a V (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := fun w hw =>
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)) (hqN hw) (hqN (hf.bijOn.mapsTo hw))
      (sub_nonneg.mpr w.1.2.2) w.1.2.1 (sub_add_cancel _ _)
  have ht : Continuous (fun w : unitInterval × K.space => (w.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun w : unitInterval × K.space => w.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hqx : ContinuousOn (fun w : unitInterval × K.space => q w.2.val) V :=
    hr.isPiecewiseAffineOn_invFunOn.continuousOn.comp hx.continuousOn (fun _ hw => hw)
  have hqf : ContinuousOn (fun w : unitInterval × K.space => q (f w.2.val)) V :=
    hr.isPiecewiseAffineOn_invFunOn.continuousOn.comp
      (hf.isPiecewiseAffineOn.continuousOn.comp hx.continuousOn (fun _ hw => hw))
      (fun _ hw => hf.bijOn.mapsTo hw)
  have hJ : ContinuousOn J V := hr.isPiecewiseAffineOn.continuousOn.comp
    (((continuous_const.sub ht).continuousOn.smul hqx).add (ht.continuousOn.smul hqf)) ha
  have hV : IsClosed V := hN.isPolyhedron.isClosed.preimage hx
  have hfront : frontier ((Subtype.val : K.space → E) ⁻¹' N) =
      (Subtype.val : K.space → E) ⁻¹' (r '' stdSimplexBoundary 2) := by
    rw [frontier_eq_closure_inter_closure,
      (hN.isPolyhedron.isClosed.preimage continuous_subtype_val).closure_eq, ← preimage_compl,
      Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      Subtype.image_preimage_coe, ← preimage_inter]
    exact congrArg (preimage (Subtype.val : K.space → E)) hmeet
  have hJfix : EqOn J (fun w => w.2.val) (frontier V) := by
    intro w hw
    have hb := continuous_snd.frontier_preimage_subset
      ((Subtype.val : K.space → E) ⁻¹' N) hw
    rw [hfront] at hb
    have hxN := hV.frontier_subset hw
    change r ((1 - (w.1 : ℝ)) • q w.2.val + (w.1 : ℝ) • q (f w.2.val)) = w.2.val
    rw [hfix hb, id_eq, ← add_smul, sub_add_cancel, one_smul, hqr _ hxN]
  let H : unitInterval × K.space → E := V.piecewise J (fun w => w.2.val)
  have hH : Continuous H := continuous_piecewise hJfix
    (by simpa only [hV.closure_eq] using hJ) hx.continuousOn
  refine ⟨F, hF, N.piecewise_eqOn f id,
    fun x hx => N.piecewise_eq_of_notMem f id hx.2, H, hH, ?_, ?_, ?_⟩
  · intro x
    by_cases hxN : x.val ∈ N
    · rw [show H (0, x) = J (0, x) from ite_eq_left hxN]
      change r ((1 - (0 : ℝ)) • q x.val + (0 : ℝ) • q (f x.val)) = x.val
      simp only [sub_zero, one_smul, zero_smul, add_zero, hqr _ hxN]
    · exact ite_eq_right hxN
  · intro x
    by_cases hxN : x.val ∈ N
    · rw [show H (1, x) = J (1, x) from ite_eq_left hxN]
      change r ((1 - (1 : ℝ)) • q x.val + (1 : ℝ) • q (f x.val)) = F x.val
      simp only [sub_self, zero_smul, one_smul, zero_add, hqr _ (hf.bijOn.mapsTo hxN)]
      exact (N.piecewise_eq_of_mem f id hxN).symm
    · exact (ite_eq_right hxN).trans (N.piecewise_eq_of_notMem f id hxN).symm
  · intro w
    by_cases hw : w.2.val ∈ N
    · rw [show H w = J w from ite_eq_left hw]
      exact hNK (hr.bijOn.mapsTo (ha hw))
    · rw [show H w = w.2.val from ite_eq_right hw]
      exact w.2.property

theorem IsCombinatorialManifold.exists_isPLSphere_one_avoiding_disk
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {D J S U : Set E}
    (hD : IsPLBall 2 D) (hDK : D ⊆ K.space) (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space)
    (hKS : K.space ⊆ S) (hJS : CarriesFirstHomologyOnto J S)
    (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ J' : Set E, IsPLSphere 1 J' ∧ J' ⊆ K.space ∧ Disjoint J' D ∧
      J' ⊆ J ∪ U ∧ CarriesFirstHomologyOnto J' S := by
  classical
  obtain ⟨N, hN, hNKU, hNnhds⟩ := hK.exists_isPLBall_surface_disk_neighborhood hD hDK
    (mem_nhdsSetWithin.mpr ⟨U, hU, hDU, inter_subset_left⟩)
  have hNK : N ⊆ K.space := hNKU.trans inter_subset_left
  have hNU : N ⊆ U := hNKU.trans inter_subset_right
  obtain ⟨r, hr⟩ := id hN
  obtain ⟨O, hO, hDO, hON⟩ := mem_nhdsSetWithin.mp hNnhds
  have hDN : D ⊆ N \ r '' stdSimplexBoundary 2 := by
    intro x hx
    refine ⟨hON ⟨hDO hx, hDK hx⟩, ?_⟩
    intro hxb
    have hxcl := ((hK.inter_closure_sdiff_eq_image_stdSimplexBoundary K hr hNK).symm ▸ hxb).2
    obtain ⟨y, hyO, hy⟩ := mem_closure_iff.mp hxcl O hO (hDO hx)
    exact hy.2 (hON ⟨hyO, hy.1⟩)
  obtain ⟨B, hB, hBN, hBJ⟩ := exists_disk_in_surface_disk_off_circle hK hr hNK hJ hJK
  obtain ⟨f, hf, hfB, hfix⟩ :=
    exists_isPLHomeomorphOn_map_disk_eqOn_boundary hr hB hD hBN hDN
  obtain ⟨F, hF, hFf, hFfix, H, hH, hH0, hH1, hHK⟩ :=
    extend_surface_disk_move hK hr hNK hf hfix
  have hFJ : IsPLHomeomorphOn F J (F '' J) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hJ.isPolyhedron
      (hF.isPiecewiseAffineOn.mono_of_isPolyhedron hJ.isPolyhedron hJK)
      (hF.bijOn.injOn.mono hJK).bijOn_image
  have hJK' : F '' J ⊆ K.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hF.bijOn.mapsTo (hJK hx)
  have hJS' : F '' J ⊆ S := hJK'.trans hKS
  refine ⟨F '' J, hJ.of_isPLHomeomorphOn hFJ, hJK', ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ hxD
    obtain ⟨b, hb, hbf⟩ := hfB.symm ▸ hxD
    have hbN := (hBN hb).1
    have hxb : x = b := hF.bijOn.injOn (hJK hx) (hNK hbN)
      ((hFf hbN).trans hbf).symm
    exact disjoint_left.mp hBJ (hxb ▸ hb) hx
  · rintro _ ⟨x, hx, rfl⟩
    by_cases hxN : x ∈ N
    · exact Or.inr (hNU ((hFf hxN).symm ▸ hf.bijOn.mapsTo hxN))
    · exact Or.inl ((hFfix ⟨hJK hx, hxN⟩).symm ▸ hx)
  · let g : C(J, F '' J) :=
      ⟨fun x => ⟨F x.val, x.val, x.property, rfl⟩,
        ((hF.isPiecewiseAffineOn.continuousOn.mono hJK).domRestrict).subtype_mk _⟩
    apply hJS.of_homotopic hJS' g
    refine ⟨{ toFun := fun w => ⟨H (w.1, inclusion hJK w.2), hKS (hHK _)⟩
              continuous_toFun := ?_
              map_zero_left := fun x => Subtype.ext (hH0 (inclusion hJK x))
              map_one_left := fun x => Subtype.ext (hH1 (inclusion hJK x)) }⟩
    exact (hH.comp (continuous_fst.prodMk
      ((continuous_inclusion hJK).comp continuous_snd))).subtype_mk _

theorem IsCombinatorialManifold.exists_isPLSphere_one_avoiding_disjoint_disks
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {ι : Type*} [Finite ι]
    (D : ι → Set E) (hD : ∀ i, IsPLBall 2 (D i)) (hDK : ∀ i, D i ⊆ K.space)
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j))) {J S : Set E}
    (hJ : IsPLSphere 1 J) (hJK : J ⊆ K.space) (hKS : K.space ⊆ S)
    (hJS : CarriesFirstHomologyOnto J S) :
    ∃ J' : Set E, IsPLSphere 1 J' ∧ J' ⊆ K.space ∧ Disjoint J' (⋃ i, D i) ∧
      CarriesFirstHomologyOnto J' S := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hstep : ∀ s : Finset ι, ∃ J' : Set E, IsPLSphere 1 J' ∧ J' ⊆ K.space ∧
      Disjoint J' (⋃ i ∈ s, D i) ∧ CarriesFirstHomologyOnto J' S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨J, hJ, hJK, by simp, hJS⟩
    | @insert i s hi ih =>
      obtain ⟨J₀, hJ₀, hJ₀K, hJ₀dis, hJ₀S⟩ := ih
      let A := ⋃ j ∈ s, D j
      have hA : IsClosed A := isClosed_biUnion_finset fun j _ => (hD j).isPolyhedron.isClosed
      have hiA : D i ⊆ Aᶜ := by
        intro x hx hxA
        obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxA
        exact disjoint_left.mp (hdis (fun hij : i = j => hi (hij.symm ▸ hj))) hx hxj
      obtain ⟨J₁, hJ₁, hJ₁K, hJ₁i, hJ₁sub, hJ₁S⟩ :=
        hK.exists_isPLSphere_one_avoiding_disk (hD i) (hDK i) hJ₀ hJ₀K hKS hJ₀S
          hA.isOpen_compl hiA
      refine ⟨J₁, hJ₁, hJ₁K, disjoint_left.mpr ?_, hJ₁S⟩
      intro x hx hxD
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxD
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact disjoint_left.mp hJ₁i hx hxj
      · have hxA : x ∈ A := mem_iUnion₂.mpr ⟨j, hj, hxj⟩
        exact (hJ₁sub hx).elim (fun hxJ => disjoint_left.mp hJ₀dis hxJ hxA) (fun hn => hn hxA)
  simpa only [Finset.mem_univ, iUnion_true] using hstep Finset.univ

end DifferentialGeometry.Topology.PiecewiseLinear
