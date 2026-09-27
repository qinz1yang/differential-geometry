/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskMove
import DifferentialGeometry.Topology.PiecewiseLinear.HandleDecompositionOfEdgeCollars
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.BallComplementFamily

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.isConnected_compl {D : Set Plane} (hD : IsPLBall 2 D) :
    IsConnected Dᶜ := by
  obtain ⟨J, rfl⟩ := exists_polygonalCircle_of_isPLBall_two hD
  have heq : J.closedRegionᶜ = J.exteriorRegion := by
    rw [J.closedRegion_eq_union]
    ext x
    constructor
    · intro hx
      have hxJ : x ∈ J.carrierᶜ := fun h => hx (Or.inr h)
      exact (J.interior_union_exterior.symm ▸ hxJ).resolve_left fun h => hx (Or.inl h)
    · intro hx hxunion
      rcases hxunion with hxI | hxJ
      · exact disjoint_left.mp J.disjoint_interior_exterior hxI hx
      · exact J.interior_union_exterior.subset (Or.inr hx) hxJ
  rw [heq]
  exact J.isConnected_exteriorRegion

theorem isPreconnected_sdiff_iUnion_of_disjoint_isPLBall_two
    {ι : Type*} [Finite ι] {U : Set Plane} {D : ι → Set Plane}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hD : ∀ i, IsPLBall 2 (D i)) (hDU : ∀ i, D i ⊆ U)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) :
    IsPreconnected (U \ ⋃ i, D i) := by
  let C : Option ι → Set Plane := fun i => Option.elim i Uᶜ D
  have hC : ∀ i, IsClosed (C i) := by
    rintro (_ | i)
    · exact hU.isClosed_compl
    · exact (hD i).isPolyhedron.isClosed
  have hCd : Pairwise fun i j => Disjoint (C i) (C j) := by
    rintro (_ | i) (_ | j) hne
    · exact (hne rfl).elim
    · exact disjoint_left.mpr fun x hx hxD => hx (hDU j hxD)
    · exact disjoint_left.mpr fun x hxD hx => hx (hDU i hxD)
    · exact hdis (fun hij => hne (congrArg some hij))
  have hCc : ∀ i, IsPreconnected (C i)ᶜ := by
    rintro (_ | i)
    · change IsPreconnected (Uᶜ)ᶜ
      simpa only [compl_compl] using hconn
    · exact (hD i).isConnected_compl.isPreconnected
  have h := isPreconnected_compl_iUnion_of_isPreconnected_compl hC hCd hCc
  have heq : (⋃ i, C i)ᶜ = U \ ⋃ i, D i := by
    rw [iUnion_option]
    change (Uᶜ ∪ ⋃ i, D i)ᶜ = U \ ⋃ i, D i
    simp only [compl_union, compl_compl, sdiff_eq]
  exact heq ▸ h

theorem exists_isPLHomeomorphOn_map_disk_family_eqOn_compl
    {ι : Type*} [Finite ι] {A B : ι → Set Plane} {U : Set Plane}
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (hAU : ∀ i, A i ⊆ U) (hBU : ∀ i, B i ⊆ U)
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j)) :
    ∃ f : Plane ≃ₜ Plane, IsPLHomeomorphOn f univ univ ∧
      EqOn f id Uᶜ ∧ ∀ i, f '' A i = B i := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hind : ∀ d : Finset ι, ∃ f : Plane ≃ₜ Plane,
      IsPLHomeomorphOn f univ univ ∧ EqOn f id Uᶜ ∧ ∀ i ∈ d, f '' A i = B i := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
      have hid : IsPiecewiseAffineOn (id : Plane → Plane) univ :=
        isPiecewiseAffineOn_id isOpen_univ
      refine ⟨Homeomorph.refl Plane, ⟨bijOn_id univ, hid, ?_⟩,
        fun _ _ => rfl, fun i hi => (Finset.notMem_empty i hi).elim⟩
      exact hid.congr fun _ hx => (bijOn_id univ).invOn_invFunOn.1 hx
    | @insert i d hi ih =>
      obtain ⟨f, hf, hfix, hmatch⟩ := ih
      let V : Set Plane := U \ ⋃ j : d, B j
      have hV : IsOpen V :=
        hU.sdiff (isClosed_iUnion_of_finite fun j : d => (hB j).isPolyhedron.isClosed)
      have hVconn : IsPreconnected V :=
        isPreconnected_sdiff_iUnion_of_disjoint_isPLBall_two hU hconn
          (fun j : d => hB j) (fun j : d => hBU j)
          (fun j k hjk => hBdis (fun hjk' => hjk (Subtype.ext hjk')))
      have hfU : f '' U = U := by
        have hcompl : f '' Uᶜ = Uᶜ := hfix.image_eq.trans (image_id _)
        have h := f.image_compl Uᶜ
        simpa only [compl_compl, hcompl] using h
      have hAi : IsPLBall 2 (f '' A i) :=
        (hA i).of_isPLHomeomorphOn (hf.restrict (hA i).isPolyhedron (subset_univ _))
      have hAiV : f '' A i ⊆ V := by
        rintro _ ⟨x, hx, rfl⟩
        refine ⟨hfU.subset ⟨x, hAU i hx, rfl⟩, ?_⟩
        intro hmem
        obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
        obtain ⟨y, hy, heq⟩ := (hmatch j j.2).symm ▸ hj
        have hyx : y = x := f.injective heq
        exact disjoint_left.mp (hAdis (Ne.symm (ne_of_mem_of_not_mem j.2 hi))) hx (hyx ▸ hy)
      have hBiV : B i ⊆ V := by
        intro x hx
        refine ⟨hBU i hx, ?_⟩
        intro hmem
        obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
        exact disjoint_left.mp (hBdis (Ne.symm (ne_of_mem_of_not_mem j.2 hi))) hx hj
      obtain ⟨g, hg, hgfix, hgmatch⟩ :=
        exists_isPLHomeomorphOn_map_disk_eqOn_compl hAi (hB i) hV hVconn hAiV hBiV
      refine ⟨f.trans g, hf.trans hg, ?_, ?_⟩
      · intro x hx
        change g (f x) = x
        rw [hfix hx]
        exact hgfix (fun hxV => hx hxV.1)
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hj
        · subst j
          exact (image_comp g f (A i)).trans hgmatch
        · have hgB : EqOn g id (B j) := by
            intro x hx
            exact hgfix (fun hxV => hxV.2 (mem_iUnion.mpr ⟨⟨j, hj⟩, hx⟩))
          change (g ∘ f) '' A j = B j
          rw [image_comp, hmatch j hj]
          exact hgB.image_eq.trans (image_id _)
  obtain ⟨f, hf, hfix, hmatch⟩ := hind Finset.univ
  exact ⟨f, hf, hfix, fun i => hmatch i (Finset.mem_univ i)⟩

theorem exists_isPLHomeomorphOn_holed_disk_eqOn_outer_boundary
    {ι : Type*} [Finite ι] {D D' : Set Plane} {A B : ι → Set Plane} {φ : Plane → Plane}
    (hD : IsPLBall 2 D) (hD' : IsPLBall 2 D')
    (hA : ∀ i, IsPLBall 2 (A i)) (hB : ∀ i, IsPLBall 2 (B i))
    (hAD : ∀ i, A i ⊆ interior D) (hBD : ∀ i, B i ⊆ interior D')
    (hAdis : Pairwise fun i j => Disjoint (A i) (A j))
    (hBdis : Pairwise fun i j => Disjoint (B i) (B j))
    (hφ : IsPLHomeomorphOn φ (frontier D) (frontier D')) :
    ∃ f : Plane → Plane, IsPLHomeomorphOn f D D' ∧
      IsPLHomeomorphOn f (D \ ⋃ i, interior (A i)) (D' \ ⋃ i, interior (B i)) ∧
      EqOn f φ (frontier D) ∧
      ∀ i, f '' A i = B i ∧ f '' frontier (A i) = frontier (B i) := by
  obtain ⟨r, hr⟩ := id hD
  obtain ⟨r', hr'⟩ := id hD'
  have hφ' : IsPLHomeomorphOn φ (r '' stdSimplexBoundary 2) (r' '' stdSimplexBoundary 2) := by
    rwa [hr.image_stdSimplexBoundary, hr'.image_stdSimplexBoundary]
  obtain ⟨q, hq, hqφ⟩ := exists_isPLHomeomorphOn_of_stdSimplexBoundary hr hr' hφ'
  rw [hr.image_stdSimplexBoundary] at hqφ
  have hAq (i : ι) : IsPLBall 2 (q '' A i) :=
    (hA i).of_isPLHomeomorphOn
      (hq.restrict (hA i).isPolyhedron ((hAD i).trans interior_subset))
  have hAqD (i : ι) : q '' A i ⊆ interior D' :=
    (image_mono (hAD i)).trans (hq.image_interior rfl).subset
  have hAqdis : Pairwise fun i j => Disjoint (q '' A i) (q '' A j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hyx : y = x :=
      hq.bijOn.injOn (interior_subset (hAD j hy)) (interior_subset (hAD i hx)) heq
    exact disjoint_left.mp (hAdis hij) hx (hyx ▸ hy)
  obtain ⟨g, hg, hgfix, hgmatch⟩ := exists_isPLHomeomorphOn_map_disk_family_eqOn_compl
    hAq hB isOpen_interior hD'.isConnected_interior.isPreconnected hAqD hBD hAqdis hBdis
  have hgD : g '' D' = D' := by
    have hcompl : g '' (interior D')ᶜ = (interior D')ᶜ :=
      hgfix.image_eq.trans (image_id _)
    have hinterior : g '' interior D' = interior D' := by
      have h := g.image_compl (interior D')ᶜ
      simpa only [compl_compl, hcompl] using h
    rw [← hD'.closure_interior, g.image_closure, hinterior]
  have hgD' : IsPLHomeomorphOn g D' D' := by
    have h := hg.restrict hD'.isPolyhedron (subset_univ D')
    rwa [hgD] at h
  let f := g ∘ q
  have hf : IsPLHomeomorphOn f D D' := hq.trans hgD'
  have hmatch (i : ι) : f '' A i = B i := (image_comp g q (A i)).trans (hgmatch i)
  have hfi (i : ι) : IsPLHomeomorphOn f (A i) (B i) := by
    rw [← hmatch i]
    exact hf.restrict (hA i).isPolyhedron ((hAD i).trans interior_subset)
  have hinner : f '' (⋃ i, interior (A i)) = ⋃ i, interior (B i) := by
    rw [image_iUnion]
    congr 1
    funext i
    exact (hfi i).image_interior rfl
  have himage : f '' (D \ ⋃ i, interior (A i)) = D' \ ⋃ i, interior (B i) := by
    rw [hf.bijOn.injOn.image_sdiff_subset
      (iUnion_subset fun i => interior_subset.trans ((hAD i).trans interior_subset)),
      hf.image_eq, hinner]
  have hholes := hf.restrict (hD.isPolyhedron.sdiff_iUnion_interior_of_isPLBall hA) sdiff_subset
  rw [himage] at hholes
  refine ⟨f, hf, hholes, ?_, fun i => ⟨hmatch i, ?_⟩⟩
  · intro x hx
    have hqx : q x ∈ frontier D' := by
      rw [hqφ hx]
      exact hφ.bijOn.mapsTo hx
    exact (hgfix hqx.2).trans (hqφ hx)
  · exact (hfi i).image_frontier rfl (hA i).isPolyhedron.isClosed (hB i).isPolyhedron.isClosed

end DifferentialGeometry.Topology.PiecewiseLinear
