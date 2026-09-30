/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskBallNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitPrismChart
import DifferentialGeometry.Topology.PiecewiseLinear.PrismFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
private theorem frontier_simplex_prism_image
    {a b : ℝ} (hab : a < b) {f : (Fin 3 → ℝ) × ℝ → E} {N : Set E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc a b) N)
    (hdim : Module.finrank ℝ E = 3) :
    frontier N = f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {a, b} ∪ stdSimplexBoundary 2 ×ˢ Icc a b) := by
  let _ : DecidableEq (Fin 3 → ℝ) := Classical.decEq _
  obtain ⟨Q, hQfin, hQspace⟩ := (isPLBall_stdSimplex 2).isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 2 Q.space := hQspace.symm ▸ isPLBall_stdSimplex 2
  have hi : IsPLHomeomorphOn id (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q.space := by
    rw [hQspace]
    exact (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id
  have hQbd : (boundaryComplex 2 Q).space = stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex Q hi,
      simplexBoundary_stdVertices_space, image_id]
  have hf' : IsPLHomeomorphOn f (Q.space ×ˢ Icc a b) N := by rwa [hQspace]
  rw [hf'.frontier_prism_image Q hQ hab hdim, hQspace, hQbd]

open Classical in
theorem IsPLBall.exists_centered_prism_subset_of_boundary_neighborhood
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 3 K.space)
    (hdim : Module.finrank ℝ E = 3) {D S : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDK : D ⊆ K.space)
    (hproper : D ∩ frontier K.space = r '' stdSimplexBoundary 2)
    (hSboundary : S ∩ K.space ⊆ frontier K.space)
    (hSnhds : S ∈ 𝓝ˢ[frontier K.space] (r '' stdSimplexBoundary 2)) :
    ∃ (N : Set E) (f : (Fin 3 → ℝ) × ℝ → E),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧
      N ⊆ K.space ∧ (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) ∧
      S ∩ N = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧ D ⊆ N := by
  have hproper' : D ∩ (boundaryComplex 3 K).space = r '' stdSimplexBoundary 2 := by
    rwa [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary]
  obtain ⟨_, _, φ, _, _, _, _, _, _, _, _, hφ, hφzero, _, _⟩ :=
    hK.exists_complex_pair_with_centered_prism_of_boundary_trace K hr hDK hproper'
  have hfront := frontier_simplex_prism_image (by norm_num : (-1 : ℝ) < 1) hφ hdim
  obtain ⟨O, hO, hJO, hOS⟩ := mem_nhdsSetWithin.mp hSnhds
  obtain ⟨V, hV, hpre⟩ :=
    continuousOn_iff'.mp hφ.isPiecewiseAffineOn.continuousOn O hO
  have hJV : stdSimplexBoundary 2 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    change t = 0 at ht
    subst t
    have hxO : φ (x, 0) ∈ O := by
      rw [hφzero x hx.1]
      exact hJO (mem_image_of_mem r hx)
    exact (hpre.subset ⟨hxO, hx.1, by norm_num, by norm_num⟩).1
  have hJstd : IsPLSphere 1 (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPLSphere_simplexBoundary_std 1
  obtain ⟨δ, hδ, hδV⟩ :=
    (hJstd.isPolyhedron.isCompact.prod isCompact_singleton).exists_cthickening_subset_open hV hJV
  let ε : ℝ := min δ 1 / 2
  have hε : 0 < ε := half_pos (lt_min hδ zero_lt_one)
  have hεδ : ε ≤ δ := (half_le_self (le_of_lt (lt_min hδ zero_lt_one))).trans (min_le_left δ 1)
  have hε1 : ε < 1 := by
    dsimp [ε]
    have h := min_le_right δ 1
    linarith
  have hsmall : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-ε) ε ⊆
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨hx, by linarith [ht.1], by linarith [ht.2]⟩
  have hwallS : φ '' (stdSimplexBoundary 2 ×ˢ Icc (-ε) ε) ⊆ S := by
    rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have hxtV : (x, t) ∈ V := by
      apply hδV
      apply Metric.mem_cthickening_of_dist_le (x, t) (x, 0) δ
        (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) ⟨hx, rfl⟩
      rw [dist_prod_same_left, Real.dist_eq, sub_zero]
      exact (abs_le.mpr ht).trans hεδ
    have hxtP := hsmall ⟨hx.1, ht⟩
    exact hOS ⟨(hpre.symm.subset ⟨hxtV, hxtP⟩).1,
      hfront.symm.subset ⟨(x, t), Or.inr ⟨hx, hxtP.2⟩, rfl⟩⟩
  let τ : ℝ →ᵃ[ℝ] ℝ := ε • AffineMap.id ℝ ℝ
  have hτapply (t : ℝ) : τ t = ε * t := rfl
  have hτ : IsPLHomeomorphOn τ (Icc (-1 : ℝ) 1) (Icc (-ε) ε) := by
    apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope τ isHPolytope_Icc)
    refine ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [hτapply]
      exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · intro s _ t _ heq
      rw [hτapply, hτapply] at heq
      exact mul_left_cancel₀ hε.ne' heq
    · intro t ht
      refine ⟨t / ε, ?_, ?_⟩
      · constructor
        · apply (le_div_iff₀ hε).mpr
          linarith [ht.1]
        · apply (div_le_iff₀ hε).mpr
          linarith [ht.2]
      · rw [hτapply]
        field_simp
  let N := φ '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-ε) ε)
  let f := φ ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) τ
  have hPsmall : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-ε) ε) :=
    (isPLBall_three_prod (isPLBall_stdSimplex 2) (isPLBall_Icc (by linarith))).isPolyhedron
  have hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N :=
    ((isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_id.prodMap hτ).trans
      (hφ.restrict hPsmall hsmall)
  have hNK : N ⊆ K.space := (image_mono hsmall).trans hφ.image_eq.subset
  have hzero (x : Fin 3 → ℝ) (hx : x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) : f (x, 0) = r x := by
    change φ (x, τ 0) = r x
    rw [hτapply, mul_zero, hφzero x hx]
  have hwall : f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) =
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (-ε) ε) := by
    change (φ ∘ Prod.map (id : (Fin 3 → ℝ) → (Fin 3 → ℝ)) τ) '' _ = _
    rw [image_comp, prodMap_image_prod, image_id, hτ.image_eq]
  have htrace : S ∩ N = φ '' (stdSimplexBoundary 2 ×ˢ Icc (-ε) ε) := by
    apply Subset.antisymm
    · rintro y ⟨hyS, z, hz, rfl⟩
      have hφz : φ z ∈ frontier K.space := hSboundary ⟨hyS, hφ.bijOn.mapsTo (hsmall hz)⟩
      obtain ⟨w, hw, heq⟩ := hfront.subset hφz
      have hwP : w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
        rcases hw with hw | hw
        · rcases hw.2 with ht | ht
          · exact ⟨hw.1, ht.symm ▸ ⟨le_rfl, by norm_num⟩⟩
          · exact ⟨hw.1, ht.symm ▸ ⟨by norm_num, le_rfl⟩⟩
        · exact ⟨hw.1.1, hw.2⟩
      have hwz : w = z := hφ.bijOn.injOn hwP (hsmall hz) heq
      subst w
      rcases hw with hends | hside
      · rcases hends.2 with ht | ht
        · have ht' : z.2 = -1 := ht
          linarith [hz.2.1]
        · have ht' : z.2 = 1 := ht
          linarith [hz.2.2]
      · exact ⟨z, ⟨hside.1, hz.2⟩, rfl⟩
    · intro y hy
      exact ⟨hwallS hy, (image_mono (prod_mono (fun _ hx => hx.1) Subset.rfl)) hy⟩
  refine ⟨N, f, hf, hNK, hzero, htrace.trans hwall.symm, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hr.bijOn.surjOn hy
  rw [← hzero x hx]
  exact hf.bijOn.mapsTo ⟨hx, by norm_num, by norm_num⟩

open Classical in
theorem IsCombinatorialManifold.exists_centered_prism_neighborhood_of_spanning_disk
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hSc : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) {D U : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hmeet : D ∩ S.space = r '' stdSimplexBoundary 2) (hU : IsOpen U) (hDU : D ⊆ U) :
    ∃ (N : Set E) (f : (Fin 3 → ℝ) × ℝ → E),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N ∧ N ⊆ U ∧
      (∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x) ∧
      S.space ∩ N = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧ D ⊆ N := by
  have hcompact : IsCompact (S.space ∪ D) :=
    (isPolyhedron_space S).isCompact.union (show IsPLBall 2 D from ⟨r, hr⟩).isPolyhedron.isCompact
  obtain ⟨T, hT, hTcard, hCT⟩ :=
    exists_affineIndependent_openSimplex_superset 3 hdim hcompact.isBounded
  let K := simplexComplex T hT
  let _ : Finite K.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hKspace : K.space = convexHull ℝ (T : Set E) :=
    simplexComplex_space T hT (Finset.card_pos.mp (by omega))
  have hK : IsPLBall 3 K.space := hKspace.symm ▸
    isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hint : interior K.space = openSimplex T := by
    rw [hKspace, interior_convexHull_eq_openSimplex hT (by omega)]
  have hCK : S.space ∪ D ⊆ interior K.space := hCT.trans hint.symm.subset
  have hSK : S.space ⊆ K.space \ (boundaryComplex 3 K).space := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary, self_sdiff_frontier]
    exact subset_union_left.trans hCK
  obtain ⟨B, hBfin, hB, _, hBU, hDB, _, hproper, htrace, hnear⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_isPLBall_neighborhood_of_spanning_disk
      hS hdim hSK hK.isConnected.isPreconnected hSc hr hmeet
      (subset_union_right.trans hCK) hU hDU
  let _ : Finite B.faces := hBfin.to_subtype
  obtain ⟨N, f, hf, hNB, hzero, hwall, hDN⟩ :=
    hB.exists_centered_prism_subset_of_boundary_neighborhood B hdim hr hDB hproper htrace hnear
  exact ⟨N, f, hf, hNB.trans hBU, hzero, hwall, hDN⟩

open Classical in
theorem IsPLHomeomorphOn.exists_wall_and_caps_of_centered_prism
    {N D : Set E} {f : (Fin 3 → ℝ) × ℝ → E} {r : (Fin 3 → ℝ) → E}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) N)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hzero : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), f (x, 0) = r x)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ (W D₀ D₁ : Set E) (ρ : E × ℝ → E) (r₀ r₁ : (Fin 3 → ℝ) → E),
      IsPLBall 3 N ∧ D ⊆ N ∧ D \ r '' stdSimplexBoundary 2 ⊆ interior N ∧
      D ∩ frontier N = r '' stdSimplexBoundary 2 ∧
      W = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1) ∧ IsPolyhedron W ∧
      IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W ∧
      (∀ x ∈ r '' stdSimplexBoundary 2, ρ (x, 0) = x) ∧
      (∀ x ∈ stdSimplexBoundary 2, ∀ t ∈ Icc (-1 : ℝ) 1, ρ (r x, t) = f (x, t)) ∧
      IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁ ∧ Disjoint D₀ D₁ ∧
      frontier N = W ∪ D₀ ∪ D₁ ∧
      W ∩ D₀ = r₀ '' stdSimplexBoundary 2 ∧ W ∩ D₁ = r₁ '' stdSimplexBoundary 2 ∧
      r₀ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 : ℝ)}) ∧
      r₁ '' stdSimplexBoundary 2 = ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 : ℝ)}) := by
  have hJstd : IsPLSphere 1 (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPLSphere_simplexBoundary_std 1
  have hJsub : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun _ hx => hx.1
  have hrest := hr.restrict hJstd.isPolyhedron hJsub
  let W := f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)
  have hside := hf.restrict (hJstd.isPolyhedron.prod isHPolytope_Icc.isPolyhedron)
    (prod_mono hJsub Subset.rfl)
  let ρ := f ∘ Prod.map (Function.invFunOn r (stdSimplexBoundary 2)) (id : ℝ → ℝ)
  have hρ : IsPLHomeomorphOn ρ ((r '' stdSimplexBoundary 2) ×ˢ Icc (-1 : ℝ) 1) W :=
    (hrest.symm.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hside
  have hρzero (x : E) (hx : x ∈ r '' stdSimplexBoundary 2) : ρ (x, 0) = x := by
    change f (Function.invFunOn r (stdSimplexBoundary 2) x, 0) = x
    rw [hzero _ (hJsub (hrest.symm.bijOn.mapsTo hx))]
    exact hrest.bijOn.invOn_invFunOn.2 hx
  have hcompatible (x : Fin 3 → ℝ) (hx : x ∈ stdSimplexBoundary 2) (t : ℝ) :
      ρ (r x, t) = f (x, t) := by
    change f (Function.invFunOn r (stdSimplexBoundary 2) (r x), t) = f (x, t)
    rw [hrest.bijOn.invOn_invFunOn.1 hx]
  have hslice (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      IsPLHomeomorphOn (fun x => f (x, t)) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {t})) := by
    have hconst := (isPLBall_stdSimplex 2).isPolyhedron.isPLHomeomorphOn_prod_const t
    exact hconst.trans (hf.restrict
      ((isPLBall_stdSimplex 2).of_isPLHomeomorphOn hconst).isPolyhedron
      (fun z hz => ⟨hz.1, hz.2.symm ▸ ht⟩))
  have hsliceBoundary (t : ℝ) :
      (fun x => f (x, t)) '' stdSimplexBoundary 2 =
        ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {t}) := by
    change _ = (f ∘ Prod.map (Function.invFunOn r (stdSimplexBoundary 2)) id) '' _
    rw [image_comp, prodMap_image_prod, image_id, hrest.symm.image_eq, prod_singleton, image_image]
  have hmeet (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      W ∩ f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {t}) =
        (fun x => f (x, t)) '' stdSimplexBoundary 2 := by
    have hsub : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {t} ⊆
        Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := fun z hz => ⟨hz.1, hz.2.symm ▸ ht⟩
    change f '' _ ∩ f '' _ = _
    rw [← hf.bijOn.injOn.image_inter (prod_mono hJsub Subset.rfl) hsub, prod_inter_prod,
      inter_eq_left.mpr hJsub, inter_eq_right.mpr (singleton_subset_iff.mpr ht),
      prod_singleton, image_image]
  have hN : IsPLBall 3 N :=
    (isPLBall_three_prod (isPLBall_stdSimplex 2)
      (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1))).of_isPLHomeomorphOn hf
  have hDN : D ⊆ N := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hr.bijOn.surjOn hy
    rw [← hzero x hx]
    exact hf.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hfront := frontier_simplex_prism_image (by norm_num : (-1 : ℝ) < 1) hf hdim
  have hproper : D ∩ frontier N = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyD, hyN⟩
      obtain ⟨x, hx, rfl⟩ := hr.bijOn.surjOn hyD
      obtain ⟨z, hz, heq⟩ := hfront.subset hyN
      have hzP : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
        rcases hz with hz | hz
        · exact ⟨hz.1, by rcases hz.2 with h | h <;> rw [h] <;> norm_num⟩
        · exact ⟨hz.1.1, hz.2⟩
      have hzx : z = (x, 0) := hf.bijOn.injOn hzP ⟨hx, by norm_num⟩
        (heq.trans (hzero x hx).symm)
      rw [hzx] at hz
      rcases hz with hz | hz
      · norm_num at hz
      · exact mem_image_of_mem r hz.1
    · rintro y ⟨x, hx, rfl⟩
      refine ⟨hr.bijOn.mapsTo hx.1, hfront.symm.subset ?_⟩
      exact ⟨(x, 0), Or.inr ⟨hx, by norm_num⟩, hzero x hx.1⟩
  have hinside : D \ r '' stdSimplexBoundary 2 ⊆ interior N := by
    rintro x ⟨hxD, hxJ⟩
    rw [← self_sdiff_frontier N]
    exact ⟨hDN hxD, fun hxF => hxJ (hproper.subset ⟨hxD, hxF⟩)⟩
  let D₀ := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(-1 : ℝ)})
  let D₁ := f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 : ℝ)})
  have hdis : Disjoint D₀ D₁ := by
    apply disjoint_left.mpr
    rintro y ⟨z, hz, rfl⟩ ⟨w, hw, heq⟩
    have heq' := hf.bijOn.injOn
      (show w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 from
        ⟨hw.1, hw.2.symm ▸ by norm_num⟩)
      (show z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 from
        ⟨hz.1, hz.2.symm ▸ by norm_num⟩) heq
    have ht := congrArg Prod.snd heq'
    have hw' : w.2 = 1 := hw.2
    have hz' : z.2 = -1 := hz.2
    linarith
  have hfront' : frontier N = W ∪ D₀ ∪ D₁ := by
    rw [hfront, show Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(-1 : ℝ), 1} =
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(-1 : ℝ)} ∪ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {(1 : ℝ)} by
        rw [← prod_union, singleton_union], image_union, image_union]
    ext x
    simp only [W, D₀, D₁, mem_union]
    tauto
  refine ⟨W, D₀, D₁, ρ, (fun x => f (x, -1)), (fun x => f (x, 1)),
    hN, hDN, hinside, hproper, rfl, ?_, hρ, hρzero, (fun x hx t _ => hcompatible x hx t),
    hslice (-1) (by norm_num), hslice 1 (by norm_num), hdis, hfront',
    hmeet (-1) (by norm_num), hmeet 1 (by norm_num), hsliceBoundary (-1), hsliceBoundary 1⟩
  exact (hJstd.isPolyhedron.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
    hside.isPiecewiseAffineOn hside.bijOn.injOn

end DifferentialGeometry.Topology.PiecewiseLinear
