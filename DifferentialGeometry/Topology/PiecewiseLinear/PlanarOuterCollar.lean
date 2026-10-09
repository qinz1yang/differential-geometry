/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarBoundaryCollars
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.exists_outer_boundary_collar {D H U : Set Plane}
    (hD : IsPLBall 2 D) (hH : IsPLBall 2 H) (hHD : H ⊆ interior D)
    (hU : IsOpen U) (hJU : frontier H ⊆ U) :
    ∃ (A R : Set Plane) (ρ : Plane × ℝ → Plane),
      IsPolyhedron A ∧ IsPolyhedron R ∧ A ⊆ U ∩ interior D ∧
      D \ interior H = R ∪ A ∧
      IsPLHomeomorphOn ρ (frontier H ×ˢ Icc (0 : ℝ) 1) A ∧
      (∀ x ∈ frontier H, ρ (x, 1) = x) ∧
      A ∩ R = ρ '' (frontier H ×ˢ ({0} : Set ℝ)) ∧
      A ∈ 𝓝ˢ[(interior H)ᶜ] (frontier H) ∧
      MapsTo ρ (frontier H ×ˢ Ico (0 : ℝ) 1) (D \ H) ∧
      frontier A = ρ '' (frontier H ×ˢ ({0, 1} : Set ℝ)) := by
  classical
  obtain ⟨rD, hrD⟩ := id hD
  obtain ⟨rH, hrH⟩ := id hH
  let J := frontier H
  let S : Set (Plane × ℝ) := D ×ˢ ({0, 2} : Set ℝ) ∪ frontier D ×ˢ Icc (0 : ℝ) 2
  let H₀ : Set (Plane × ℝ) := H ×ˢ ({0} : Set ℝ)
  let C := closure (S \ H₀)
  have hJ : IsPLSphere 1 J := hH.isPLSphere_frontier
  have hJH : J ⊆ H := hH.isPolyhedron.isClosed.frontier_subset
  have hS : IsPLSphere 2 S := by
    have h := hrD.isPLSphere_prism_boundary (by norm_num : (0 : ℝ) < 2)
    rwa [hrD.image_stdSimplexBoundary] at h
  have hH₀ : IsPLBall 2 H₀ :=
    hH.of_isPLHomeomorphOn (hH.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hH₀S : H₀ ⊆ S := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inl ⟨interior_subset (hHD hx), Or.inl ht⟩
  let qH := (fun x : Plane => (x, (0 : ℝ))) ∘ rH
  have hqH : IsPLHomeomorphOn qH (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) H₀ :=
    hrH.trans (hH.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hqHJ : qH '' stdSimplexBoundary 2 = J ×ˢ ({0} : Set ℝ) := by
    rw [show qH = (fun x : Plane => (x, (0 : ℝ))) ∘ rH from rfl, image_comp,
      hrH.image_stdSimplexBoundary]
    exact (hJ.isPolyhedron.isPLHomeomorphOn_prod_const 0).image_eq
  have hC : IsPLBall 2 C := hS.isPLBall_closure_sdiff hH₀ hH₀S
  obtain ⟨q, hq⟩ := id hC
  have hqJ : q '' stdSimplexBoundary 2 = J ×ˢ ({0} : Set ℝ) := by
    rw [hS.image_stdSimplexBoundary_complement hH₀ hH₀S hq, inter_comm,
      hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hqH hH₀S, hqHJ]
  have hCS : C ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  have hCformula : C = S \ (H₀ \ (J ×ˢ ({0} : Set ℝ))) := by
    exact (hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary hqH hH₀S).trans
      (congrArg (fun Z => S \ (H₀ \ Z)) hqHJ)
  have hCbottom (x : Plane) : (x, (0 : ℝ)) ∈ C ↔ x ∈ D \ interior H := by
    rw [hCformula]
    constructor
    · rintro ⟨hxS, hxH⟩
      have hxD : x ∈ D := by
        rcases hxS with hx | hx
        · exact hx.1
        · exact hD.isPolyhedron.isClosed.frontier_subset hx.1
      refine ⟨hxD, fun hxI => hxH ⟨⟨interior_subset hxI, rfl⟩, ?_⟩⟩
      exact fun hxJ => hxJ.1.2 hxI
    · rintro ⟨hxD, hxI⟩
      refine ⟨Or.inl ⟨hxD, Or.inl rfl⟩, ?_⟩
      rintro ⟨hxH, hxJ⟩
      exact hxJ ⟨⟨subset_closure hxH.1, hxI⟩, rfl⟩
  let V : Set (Plane × ℝ) := (U ∩ interior D) ×ˢ Ioo (-1 : ℝ) 1
  have hV : IsOpen V := (hU.inter isOpen_interior).prod isOpen_Ioo
  have hJV : J ×ˢ ({0} : Set ℝ) ⊆ V := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact ⟨⟨hJU hx, hHD (hJH hx)⟩, by norm_num⟩
  have hVnhds : V ∈ 𝓝ˢ[C] (q '' stdSimplexBoundary 2) := by
    apply mem_nhdsSetWithin.mpr
    exact ⟨V, hV, hqJ.symm ▸ hJV, inter_subset_left⟩
  obtain ⟨A₀, B₀, σ, hA₀, hB₀, hA₀V, hcover₀, hσ, hσfix, hmeet₀, hnhds₀, hpos₀⟩ :=
    hq.exists_disk_boundary_collar hVnhds
  rw [hqJ] at hσ hσfix hmeet₀ hnhds₀ hpos₀
  have hA₀C : A₀ ⊆ C := fun x hx => hcover₀.symm ▸ Or.inr hx
  have hB₀C : B₀ ⊆ C := fun x hx => hcover₀.symm ▸ Or.inl hx
  have hA₀bottom : A₀ ⊆ D ×ˢ ({0} : Set ℝ) := by
    rintro ⟨x, t⟩ hx
    have hxV := hA₀V hx
    rcases hCS (hA₀C hx) with hxS | hxS
    · rcases hxS.2 with ht | ht
      · exact ⟨hxS.1, ht⟩
      · have ht2 : t = 2 := ht
        have htlt := hxV.2.2
        linarith
    · exact (hxS.1.2 hxV.1.2).elim
  let A := Prod.fst '' A₀
  let R := Prod.fst '' (B₀ ∩ (D ×ˢ ({0} : Set ℝ)))
  have hprojA : IsPLHomeomorphOn Prod.fst A₀ A :=
    (hD.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).restrict hA₀ hA₀bottom
  have hzero : IsPolyhedron ({0} : Set ℝ) := by
    rw [← Icc_self (0 : ℝ)]
    exact isHPolytope_Icc.isPolyhedron
  have hRlift : IsPolyhedron (B₀ ∩ (D ×ˢ ({0} : Set ℝ))) :=
    hB₀.isPolyhedron.inter (hD.isPolyhedron.prod hzero)
  have hprojR : IsPLHomeomorphOn Prod.fst (B₀ ∩ (D ×ˢ ({0} : Set ℝ))) R :=
    (hD.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0).restrict hRlift inter_subset_right
  have hA : IsPolyhedron A := hA₀.image_of_isPiecewiseAffineOn
    hprojA.isPiecewiseAffineOn hprojA.bijOn.injOn
  have hR : IsPolyhedron R := hRlift.image_of_isPiecewiseAffineOn
    hprojR.isPiecewiseAffineOn hprojR.bijOn.injOn
  have hmemA (x : Plane) : x ∈ A ↔ (x, (0 : ℝ)) ∈ A₀ := by
    constructor
    · rintro ⟨⟨y, t⟩, hy, rfl⟩
      have ht0 : t = 0 := (hA₀bottom hy).2
      simpa only [ht0] using hy
    · intro hx
      exact ⟨(x, 0), hx, rfl⟩
  have hmemR (x : Plane) : x ∈ R ↔ (x, (0 : ℝ)) ∈ B₀ ∧ x ∈ D := by
    constructor
    · rintro ⟨⟨y, t⟩, ⟨hy, hyD, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨hy, hyD⟩
    · rintro ⟨hx, hxD⟩
      exact ⟨(x, 0), ⟨hx, hxD, rfl⟩, rfl⟩
  let ρ := Prod.fst ∘ σ ∘ Prod.map (fun x : Plane => (x, (0 : ℝ))) id
  have hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (0 : ℝ) 1) A :=
    (((hJ.isPolyhedron.isPLHomeomorphOn_prod_const 0).prodMap
      isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hσ).trans hprojA
  have hρlift (z : Plane × ℝ) (hz : z ∈ J ×ˢ Icc (0 : ℝ) 1) :
      (ρ z, (0 : ℝ)) = σ ((z.1, 0), z.2) := by
    have hmem := hσ.bijOn.mapsTo (show ((z.1, (0 : ℝ)), z.2) ∈
      (J ×ˢ ({0} : Set ℝ)) ×ˢ Icc (0 : ℝ) 1 from ⟨⟨hz.1, rfl⟩, hz.2⟩)
    exact Prod.ext rfl (hA₀bottom hmem).2.symm
  have hfix (x : Plane) (hx : x ∈ J) : ρ (x, 1) = x := by
    change (σ ((x, 0), 1)).1 = x
    rw [hσfix (x, 0) ⟨hx, rfl⟩]
  have hcover : D \ interior H = R ∪ A := by
    ext x
    rw [mem_union, hmemR, hmemA, ← hCbottom, hcover₀]
    constructor
    · rintro (hxB | hxA)
      · exact Or.inl ⟨hxB, ((hCbottom x).mp (hB₀C hxB)).1⟩
      · exact Or.inr hxA
    · rintro (⟨hxB, -⟩ | hxA)
      · exact Or.inl hxB
      · exact Or.inr hxA
  have hmeet : A ∩ R = ρ '' (J ×ˢ ({0} : Set ℝ)) := by
    ext x
    constructor
    · rintro ⟨hxA, hxR⟩
      have hxAB : (x, (0 : ℝ)) ∈ A₀ ∩ B₀ := ⟨(hmemA x).mp hxA, ((hmemR x).mp hxR).1⟩
      obtain ⟨⟨⟨y, s⟩, t⟩, ⟨⟨hy, hs⟩, ht⟩, heq⟩ := hmeet₀ ▸ hxAB
      have hs0 : s = 0 := hs
      have ht0 : t = 0 := ht
      subst s
      subst t
      exact ⟨(y, 0), ⟨hy, rfl⟩, congrArg Prod.fst heq⟩
    · rintro ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      have hmem : (y, (0 : ℝ)) ∈ J ×ˢ Icc (0 : ℝ) 1 := ⟨hy, by norm_num⟩
      have hσmem : σ ((y, 0), 0) ∈ A₀ ∩ B₀ := hmeet₀.symm ▸
        mem_image_of_mem σ (show ((y, (0 : ℝ)), (0 : ℝ)) ∈
          (J ×ˢ ({0} : Set ℝ)) ×ˢ ({0} : Set ℝ) from ⟨⟨hy, rfl⟩, rfl⟩)
      rw [← hρlift _ hmem] at hσmem
      exact ⟨(hmemA _).mpr hσmem.1, (hmemR _).mpr ⟨hσmem.2, (hA₀bottom hσmem.1).1⟩⟩
  have hnhds : A ∈ 𝓝ˢ[(interior H)ᶜ] J := by
    obtain ⟨O, hO, hJO, hOA⟩ := mem_nhdsSetWithin.mp hnhds₀
    apply mem_nhdsSetWithin.mpr
    refine ⟨(fun x : Plane => (x, (0 : ℝ))) ⁻¹' O ∩ interior D,
      (hO.preimage (continuous_id.prodMk continuous_const)).inter isOpen_interior,
      fun x hx => ⟨hJO ⟨hx, rfl⟩, hHD (hJH hx)⟩, ?_⟩
    rintro x ⟨⟨hxO, hxD⟩, hxH⟩
    exact (hmemA x).mpr (hOA ⟨hxO, (hCbottom x).mpr ⟨interior_subset hxD, hxH⟩⟩)
  have hpositive : MapsTo ρ (J ×ˢ Ico (0 : ℝ) 1) (D \ H) := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have hmem : (x, t) ∈ J ×ˢ Icc (0 : ℝ) 1 := ⟨hx, ht.1, ht.2.le⟩
    have hσpos := hpos₀ (show ((x, (0 : ℝ)), t) ∈
      (J ×ˢ ({0} : Set ℝ)) ×ˢ Ico (0 : ℝ) 1 from ⟨⟨hx, rfl⟩, ht⟩)
    rw [← hρlift _ hmem] at hσpos
    have hp := (hCbottom _).mp hσpos.1
    refine ⟨hp.1, fun hyH => hσpos.2 ⟨⟨subset_closure hyH, hp.2⟩, rfl⟩⟩
  have hfrontier : frontier A = ρ '' (J ×ˢ ({0, 1} : Set ℝ)) := by
    let _ : DecidableEq Plane := Classical.decEq _
    obtain ⟨K, hKfin, hK, -, hKspace, hKbd⟩ := hρ.exists_annulus_complex hJ zero_lt_one
    let _ : Finite K.faces := hKfin.to_subtype
    rw [← hKspace, frontier_space_eq_boundaryComplex_space_of_finrank (by simp) K hK]
    exact hKbd
  refine ⟨A, R, ρ, hA, hR, ?_, hcover, hρ, hfix, hmeet, hnhds, hpositive, hfrontier⟩
  rintro x ⟨z, hz, rfl⟩
  exact (hA₀V hz).1

end DifferentialGeometry.Topology.PiecewiseLinear
