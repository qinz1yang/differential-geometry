/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.ConvexPolytope
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBallPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_pos_forall_le_of_isCompact {Y : Set E3} (hY : IsCompact Y) {φ : E3 → ℝ}
    (hφ : Continuous φ) (hpos : ∀ y ∈ Y, 0 < φ y) : ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Y, δ ≤ φ y := by
  rcases Y.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun _ h => h.elim⟩
  · obtain ⟨y₀, hy₀, hmin⟩ := hY.exists_isMinOn hne hφ.continuousOn
    exact ⟨φ y₀, hpos y₀ hy₀, fun y hy => isMinOn_iff.mp hmin y hy⟩

theorem IsPLBall.exists_subset_disjoint_of_subset_frontier {Q D K U : Set E3}
    (hQ : IsPLBall 3 Q) (hD : IsPLBall 2 D) (hDQ : D ⊆ frontier Q) (hK : IsCompact K)
    (hKQ : K ⊆ interior Q) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ Q' C : Set E3, IsPLBall 3 Q' ∧ Q' ⊆ Q ∧ K ⊆ interior Q' ∧ Disjoint Q' D ∧
      IsCompact C ∧ C ⊆ U ∧ Q ⊆ Q' ∪ C := by
  classical
  obtain ⟨u, hu⟩ := id hQ
  obtain ⟨T, a, f, hT, hTcard, ha, hf, hfD⟩ :=
    exists_isPLHomeomorphOn_sphere_disk_to_simplex hQ.isPLSphere_frontier hD hDQ
  set Δ := convexHull ℝ (T : Set E3) with hΔdef
  have hΔ : IsPLBall 3 Δ := isPLBall_convexHull_of_affineIndependent T hT hTcard
  obtain ⟨g, hg⟩ := id hΔ
  have hfr : u '' stdSimplexBoundary 3 = frontier Q :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hu
  have hgr : g '' stdSimplexBoundary 3 = frontier Δ :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hg
  have hb : IsPLHomeomorphOn f (u '' stdSimplexBoundary 3) (g '' stdSimplexBoundary 3) := by
    rw [hfr, hgr]
    exact hf
  obtain ⟨H, hH, hHf⟩ := exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary (n := 2) hu hg hb
  have hHf' : EqOn H f (frontier Q) := by
    rw [← hfr]
    exact hHf
  have hQc : IsCompact Q := hQ.isPolyhedron.isCompact
  have hDQ' : D ⊆ Q := hDQ.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hHD : H '' D = convexHull ℝ ((T.erase a : Finset E3) : Set E3) := by
    rw [← hfD]
    exact (hHf'.mono hDQ).image_eq
  have hspan : affineSpan ℝ (range ((↑) : T → E3)) = ⊤ :=
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      simpa only [Fintype.card_coe, finrank_euclideanSpace, Fintype.card_fin] using hTcard)
  let b : AffineBasis T ℝ E3 := ⟨(↑), hT, hspan⟩
  have hbr : range b = (T : Set E3) := Subtype.range_coe
  have hΔcoord : Δ = {x | ∀ i, 0 ≤ b.coord i x} := by
    rw [hΔdef, ← hbr, b.convexHull_eq_nonneg_coord]
  have hΔint : interior Δ = {x | ∀ i, 0 < b.coord i x} := by
    rw [hΔdef, ← hbr, b.interior_convexHull]
  set ℓ := b.coord ⟨a, ha⟩ with hℓdef
  have hℓc : Continuous ℓ := ℓ.continuous_of_finiteDimensional
  have hℓa : ℓ a = 1 := b.coord_apply_eq ⟨a, ha⟩
  have hFsub : convexHull ℝ ((T.erase a : Finset E3) : Set E3) ⊆ {x | ℓ x = 0} := by
    refine convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage ℓ)
    intro v hv
    have hvT : v ∈ T := Finset.mem_of_mem_erase hv
    have hva : v ≠ a := Finset.ne_of_mem_erase hv
    exact b.coord_apply_ne (i := ⟨a, ha⟩) (j := ⟨v, hvT⟩)
      (fun h => hva (congrArg Subtype.val h).symm)
  have hFsup : ∀ x ∈ Δ, ℓ x = 0 → x ∈ convexHull ℝ ((T.erase a : Finset E3) : Set E3) := by
    intro x hx hx0
    have hTins : (T : Set E3) = insert a ((T.erase a : Finset E3) : Set E3) := by
      rw [Finset.coe_erase, Set.insert_sdiff_singleton,
        Set.insert_eq_of_mem (Finset.mem_coe.mpr ha)]
    have hne : ((T.erase a : Finset E3) : Set E3).Nonempty := by
      rw [Finset.coe_nonempty, ← Finset.card_pos, Finset.card_erase_of_mem ha, hTcard]
      norm_num
    rw [hΔdef, hTins, convexHull_insert hne] at hx
    obtain ⟨p, hp, y, hy, hxs⟩ := mem_convexJoin.mp hx
    rw [mem_singleton_iff] at hp
    subst hp
    rw [segment_eq_image_lineMap] at hxs
    obtain ⟨θ, -, rfl⟩ := hxs
    have hℓy : ℓ y = 0 := hFsub hy
    rw [AffineMap.apply_lineMap, hℓa, hℓy, AffineMap.lineMap_apply_module] at hx0
    have hθ : θ = 1 := by
      simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at hx0
      linarith
    rw [hθ, AffineMap.lineMap_apply_one]
    exact hy
  have hΔnn : ∀ x ∈ Δ, 0 ≤ ℓ x := fun x hx => by
    rw [hΔcoord] at hx
    exact hx ⟨a, ha⟩
  have hK' : H '' K ⊆ interior Δ := by
    rw [← hH.image_interior (by simp)]
    exact image_mono hKQ
  obtain ⟨δ₁, hδ₁, hK₁⟩ := exists_pos_forall_le_of_isCompact
    (hK.image_of_continuousOn (hH.isPiecewiseAffineOn.continuousOn.mono
      (hKQ.trans interior_subset))) hℓc fun y hy => by
        have hy' := hK' hy
        rw [hΔint] at hy'
        exact hy' ⟨a, ha⟩
  have hY : IsCompact (H '' (Q \ U)) :=
    (hQc.diff hU).image_of_continuousOn (hH.isPiecewiseAffineOn.continuousOn.mono sdiff_subset)
  obtain ⟨δ₂, hδ₂, hY₂⟩ := exists_pos_forall_le_of_isCompact hY hℓc fun y hy => by
    obtain ⟨x, ⟨hxQ, hxU⟩, rfl⟩ := hy
    refine lt_of_le_of_ne (hΔnn _ (hH.bijOn.mapsTo hxQ)) fun h => ?_
    have hF := hFsup _ (hH.bijOn.mapsTo hxQ) h.symm
    rw [← hHD] at hF
    obtain ⟨x', hx', hxx'⟩ := hF
    exact hxU (hH.bijOn.injOn (hDQ' hx') hxQ hxx' ▸ hDU hx')
  set ε := min (min δ₁ δ₂ / 2) (1 / 8) with hεdef
  have hε : 0 < ε := lt_min (half_pos (lt_min hδ₁ hδ₂)) (by norm_num)
  have hε₁ : ε < δ₁ := lt_of_le_of_lt ((min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_left _ _) zero_le_two)) (half_lt_self hδ₁)
  have hε₂ : ε < δ₂ := lt_of_le_of_lt ((min_le_left _ _).trans
    (div_le_div_of_nonneg_right (min_le_right _ _) zero_le_two)) (half_lt_self hδ₂)
  have hε₈ : ε ≤ 1 / 8 := min_le_right _ _
  obtain ⟨hΔcomp, ι, hι, l, c, hΔeq⟩ := isHPolytope_convexHull_of_affineIndependent T hT
  have hℓdecomp : ∀ x, ℓ x = ℓ.linear x + ℓ 0 := fun x => congrFun ℓ.decomp x
  have hΔεH : IsHPolytope (Δ ∩ {x | ε ≤ ℓ x}) := by
    refine ⟨hΔcomp.inter_right (isClosed_le continuous_const hℓc), Option ι, inferInstance,
      fun j => Option.elim j (-ℓ.linear) l, fun j => Option.elim j (ℓ 0 - ε) c, ?_⟩
    ext x
    rw [mem_inter_iff, hΔdef, hΔeq]
    simp only [mem_ofPred_eq, Option.forall, Option.elim, LinearMap.neg_apply]
    rw [hℓdecomp x]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨by linarith, h₁⟩
    · rintro ⟨h₂, h₁⟩
      exact ⟨h₁, by linarith⟩
  have hopen : IsOpen (interior Δ ∩ {x | ε < ℓ x}) :=
    isOpen_interior.inter (isOpen_lt continuous_const hℓc)
  have hopenSub : interior Δ ∩ {x | ε < ℓ x} ⊆ interior (Δ ∩ {x | ε ≤ ℓ x}) :=
    interior_maximal (fun x hx => ⟨interior_subset hx.1, show ε ≤ ℓ x from le_of_lt hx.2⟩) hopen
  have hcent : Finset.univ.centroid ℝ b ∈ interior Δ ∩ {x | ε < ℓ x} := by
    refine ⟨?_, ?_⟩
    · rw [hΔdef, ← hbr]
      exact b.centroid_mem_interior_convexHull
    · change ε < b.coord ⟨a, ha⟩ (Finset.univ.centroid ℝ b)
      rw [b.coord_apply_centroid (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe, hTcard]
      norm_num
      linarith
  have hΔεball : IsPLBall 3 (Δ ∩ {x | ε ≤ ℓ x}) := by
    have h := hΔεH.isPLBall ⟨_, hopenSub hcent⟩
    rwa [finrank_euclideanSpace_fin] at h
  have hΔεsub : Δ ∩ {x | ε ≤ ℓ x} ⊆ Δ := inter_subset_left
  have hinv := hH.symm.restrict hΔεH.isPolyhedron hΔεsub
  set Hi := Function.invFunOn H Q with hHidef
  have hHiH : ∀ x ∈ Q, Hi (H x) = x := fun x hx => hH.bijOn.invOn_invFunOn.1 hx
  have hHHi : ∀ z ∈ Δ, H (Hi z) = z := fun z hz => hH.bijOn.invOn_invFunOn.2 hz
  have hHiQ : ∀ z ∈ Δ, Hi z ∈ Q := fun z hz => hH.symm.bijOn.mapsTo hz
  have hCcomp : IsCompact (Δ ∩ {x | ℓ x ≤ ε}) :=
    hΔcomp.inter_right (isClosed_le hℓc continuous_const)
  refine ⟨Hi '' (Δ ∩ {x | ε ≤ ℓ x}), Hi '' (Δ ∩ {x | ℓ x ≤ ε}),
    hΔεball.of_isPLHomeomorphOn hinv, ?_, ?_, ?_,
    hCcomp.image_of_continuousOn (hH.isPiecewiseAffineOn_invFunOn.continuousOn.mono
      inter_subset_left), ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hHiQ z hz.1
  · rw [← hinv.image_interior (by simp)]
    intro x hx
    have hxQ : x ∈ Q := interior_subset (hKQ hx)
    refine ⟨H x, hopenSub ⟨hK' (mem_image_of_mem H hx), ?_⟩, hHiH x hxQ⟩
    exact lt_of_lt_of_le hε₁ (hK₁ _ (mem_image_of_mem H hx))
  · refine Set.disjoint_left.mpr ?_
    rintro _ ⟨z, hz, rfl⟩ hzD
    have hHz : H (Hi z) ∈ convexHull ℝ ((T.erase a : Finset E3) : Set E3) := by
      rw [← hHD]
      exact mem_image_of_mem H hzD
    rw [hHHi z hz.1] at hHz
    have h0 : ℓ z = 0 := hFsub hHz
    have h1 : ε ≤ ℓ z := hz.2
    rw [h0] at h1
    exact absurd h1 (not_le.mpr hε)
  · rintro _ ⟨z, hz, rfl⟩
    by_contra hzU
    have hzY : z ∈ H '' (Q \ U) := ⟨Hi z, ⟨hHiQ z hz.1, hzU⟩, hHHi z hz.1⟩
    have := hY₂ z hzY
    have h2 : ℓ z ≤ ε := hz.2
    linarith
  · intro x hx
    have hHx : H x ∈ Δ := hH.bijOn.mapsTo hx
    rcases le_total ε (ℓ (H x)) with h | h
    · exact Or.inl ⟨H x, ⟨hHx, h⟩, hHiH x hx⟩
    · exact Or.inr ⟨H x, ⟨hHx, h⟩, hHiH x hx⟩

theorem IsPLBall.exists_compression_of_proper_disk {P D K U : Set E3} (hP : IsPLBall 3 P)
    {q : (Fin 3 → ℝ) → E3} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDP : D ⊆ P)
    (htrace : D ∩ frontier P = q '' stdSimplexBoundary 2) (hK : IsCompact K)
    (hKc : IsPreconnected K) (hKP : K ⊆ interior P) (hKD : Disjoint K D) (hU : IsOpen U)
    (hDU : D ⊆ U) :
    ∃ P' O : Set E3, IsPLBall 3 P' ∧ P' ⊆ P ∧ K ⊆ interior P' ∧ Disjoint P' D ∧ IsOpen O ∧
      P' ∩ O = P ∩ O ∧ frontier P' \ O ⊆ U := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hunion, hinter, hDP₀, hDP₁⟩ :=
    hP.exists_pair_union_eq_inter_eq_of_boundary_trace hq hDP htrace
  have key : ∀ A B : Set E3, IsPLBall 3 A → IsPLBall 3 B → A ∪ B = P → A ∩ B = D →
      D ⊆ frontier A → K ⊆ A →
      ∃ P' O : Set E3, IsPLBall 3 P' ∧ P' ⊆ P ∧ K ⊆ interior P' ∧ Disjoint P' D ∧ IsOpen O ∧
        P' ∩ O = P ∩ O ∧ frontier P' \ O ⊆ U := by
    intro A B hA hB hAB hABi hDA hKA
    have hBc : IsClosed B := hB.isPolyhedron.isClosed
    have hKA' : K ⊆ interior A := by
      intro x hx
      have hxB : x ∉ B := fun hxB =>
        Set.disjoint_left.mp hKD hx (hABi ▸ (⟨hKA hx, hxB⟩ : x ∈ A ∩ B))
      refine interior_maximal (s := A) (t := interior P ∩ Bᶜ) ?_
        (isOpen_interior.inter hBc.isOpen_compl) ⟨hKP hx, hxB⟩
      rintro y ⟨hyP, hyB⟩
      have hy : y ∈ A ∪ B := hAB.symm ▸ interior_subset hyP
      exact hy.resolve_right hyB
    obtain ⟨Q', C, hQ', hQ'A, hKQ', hQ'D, hC, hCU, hAC⟩ :=
      hA.exists_subset_disjoint_of_subset_frontier ⟨q, hq⟩ hDA hK hKA' hU hDU
    have hAP : A ⊆ P := hAB ▸ subset_union_left
    refine ⟨Q', (B ∪ C)ᶜ, hQ', hQ'A.trans hAP, hKQ', hQ'D,
      (hBc.union hC.isClosed).isOpen_compl, ?_, ?_⟩
    · ext x
      constructor
      · rintro ⟨hx, hxO⟩
        exact ⟨hAP (hQ'A hx), hxO⟩
      · rintro ⟨hx, hxO⟩
        have hxB : x ∉ B := fun h => hxO (Or.inl h)
        have hxC : x ∉ C := fun h => hxO (Or.inr h)
        have hxA : x ∈ A := (hAB.symm ▸ hx : x ∈ A ∪ B).resolve_right hxB
        exact ⟨(hAC hxA).resolve_right hxC, hxO⟩
    · rintro x ⟨hx, hxO⟩
      have hxQ' : x ∈ Q' := hQ'.isPolyhedron.isClosed.frontier_subset hx
      have hxBC : x ∈ B ∪ C := not_not.mp hxO
      rcases hxBC with hxB | hxC
      · exact absurd (hABi ▸ (⟨hQ'A hxQ', hxB⟩ : x ∈ A ∩ B))
          (Set.disjoint_left.mp hQ'D hxQ')
      · exact hCU hxC
  have hside : K ⊆ P₀ ∨ K ⊆ P₁ := by
    refine isPreconnected_iff_subset_of_disjoint_closed.mp hKc P₀ P₁
      hP₀.isPolyhedron.isClosed hP₁.isPolyhedron.isClosed ?_ ?_
    · rw [hunion]
      exact hKP.trans interior_subset
    · rw [hinter]
      exact hKD.inter_eq
  rcases hside with h | h
  · exact key P₀ P₁ hP₀ hP₁ hunion hinter hDP₀ h
  · exact key P₁ P₀ hP₁ hP₀ (by rw [union_comm]; exact hunion)
      (by rw [inter_comm]; exact hinter) hDP₁ h

end DifferentialGeometry.Topology.PiecewiseLinear
