/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Connected.BicollarComplement
import DifferentialGeometry.Topology.FundamentalGroup.Torus
import DifferentialGeometry.Topology.Homology.FundamentalGroupRank
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCapping
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallRegularClosed
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SpanningDiskCompression
import DifferentialGeometry.Topology.PiecewiseLinear.SphereComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceEulerParity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPreconnected.subset_interior_of_disjoint_frontier {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsPreconnected s) (hst : Disjoint s (frontier t))
    (hmeet : (s ∩ interior t).Nonempty) : s ⊆ interior t := by
  refine hs.subset_left_of_subset_union isOpen_interior isClosed_closure.isOpen_compl
    (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) ?_ hmeet
  intro y hy
  by_cases hyt : y ∈ closure t
  · by_contra hyi
    exact disjoint_left.mp hst hy ⟨hyt, fun h => hyi (Or.inl h)⟩
  · exact Or.inr hyt

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.subset_closure_interior_space {n : ℕ}
    {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary n K) (hdim : Module.finrank ℝ E = n) :
    K.space ⊆ closure (interior K.space) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_superset_card_eq hs
  have hxt : x ∈ convexHull ℝ (t : Set E) := convexHull_mono (Finset.coe_subset.mpr hst) hxs
  have hint : (interior (convexHull ℝ (t : Set E))).Nonempty := by
    rw [interior_convexHull_eq_openSimplex (K.indep ht) (by omega)]
    exact ⟨t.centroid ℝ id, centroid_mem_openSimplex (Finset.card_pos.mp (by omega))⟩
  have hcl : x ∈ closure (interior (convexHull ℝ (t : Set E))) := by
    rw [(convex_convexHull ℝ (t : Set E)).closure_interior_eq_closure_of_nonempty_interior hint]
    exact subset_closure hxt
  exact closure_mono (interior_mono (K.convexHull_subset_space ht)) hcl

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isCombinatorialManifold_space_eq_frontier
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hdim : Module.finrank ℝ E = n + 1) :
    ∃ L : Geometry.SimplicialComplex ℝ E,
      L.faces.Finite ∧ IsCombinatorialManifold n L ∧ L.space = frontier K.space :=
  ⟨boundaryComplex (n + 1) K, boundaryComplex_faces_finite (n + 1) K,
    isCombinatorialManifold_boundaryComplex K hK,
    (frontier_space_eq_boundaryComplex_space_of_finrank hdim K hK).symm⟩

open Classical in
theorem IsCombinatorialManifold.isPLSphere_closure_sdiff_union_of_bettiOne_le_two
    (S : Geometry.SimplicialComplex ℝ E) [Finite S.faces]
    (hS : IsCombinatorialManifold 2 S) (hconn : IsConnected S.space)
    (hdim : Module.finrank ℝ E = 3) (hβ : Homology.bettiOne S.space ≤ 2) {J W N : Set E}
    (hJ : IsPLSphere 1 J) (hJS : J ⊆ S.space) {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ x ∈ J, ρ (x, 0) = x)
    (hnon : ¬ (⟨Set.inclusion hJS, continuous_inclusion hJS⟩ : C(J, S.space)).Nullhomotopic)
    (hN : IsPLBall 3 N) (hwall : S.space ∩ N = W)
    {D₀ D₁ : Set E} {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁) (hdis : Disjoint D₀ D₁)
    (hfront : frontier N = W ∪ D₀ ∪ D₁)
    (hmeet₀ : W ∩ D₀ = r₀ '' stdSimplexBoundary 2)
    (hmeet₁ : W ∩ D₁ = r₁ '' stdSimplexBoundary 2)
    (hbd₀ : r₀ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(-1 : ℝ)}))
    (hbd₁ : r₁ '' stdSimplexBoundary 2 = ρ '' (J ×ˢ {(1 : ℝ)})) :
    IsPLSphere 2 (closure (S.space \ W) ∪ D₀ ∪ D₁) := by
  have hWS : W ⊆ S.space := hwall.symm.subset.trans inter_subset_left
  obtain ⟨A, R, _, hRfin, _, hR, hAspace, hRspace, _, hRbd, hAR, hAS⟩ :=
    hS.exists_annulus_complement S hJ (by norm_num : (-1 : ℝ) < 1) hρ hWS
  let _ : Finite R.faces := hRfin.to_subtype
  have htrace : W ∩ R.space = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by rwa [hAspace] at hAR
  have hcover : W ∪ R.space = S.space := by rwa [hAspace] at hAS
  have hends : J ×ˢ {(-1 : ℝ), 1} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    rcases ht with rfl | rfl <;> norm_num
  have hJavoid : J ⊆ R.spaceᶜ := by
    intro x hx hxR
    have hxW : x ∈ W := by
      rw [← hzero x hx]
      exact hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
    obtain ⟨y, hy, hyx⟩ := htrace.subset ⟨hxW, hxR⟩
    have heq := hρ.bijOn.injOn (hends hy) ⟨hx, by norm_num⟩
      (hyx.trans (hzero x hx).symm)
    have ht : y.2 = 0 := congrArg Prod.snd heq
    have hbad : (0 : ℝ) ∈ ({-1, 1} : Set ℝ) := ht ▸ hy.2
    norm_num at hbad
  have hWnhds : W ∈ 𝓝ˢ[S.space] J := by
    refine mem_nhdsSetWithin.mpr ⟨R.spaceᶜ, (isPolyhedron_space R).isClosed.isOpen_compl,
      hJavoid, ?_⟩
    intro x hx
    exact (hcover.symm.subset hx.2).resolve_right hx.1
  have hcaps : D₀ ∪ D₁ ⊆ N := by
    apply Subset.trans _ hN.isPolyhedron.isClosed.frontier_subset
    rw [hfront]
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hRmeet {D C : Set E} (hDN : D ⊆ N) (hWD : W ∩ D = C)
      (hCR : C ⊆ R.space) : R.space ∩ D = C := by
    apply Subset.antisymm
    · intro x hx
      exact hWD.subset ⟨hwall.subset ⟨hcover.subset (Or.inr hx.1), hDN hx.2⟩, hx.2⟩
    · exact fun x hx => ⟨hCR hx, (hWD.symm.subset hx).2⟩
  have hRmeet₀ : R.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 := by
    apply hRmeet (subset_union_left.trans hcaps) hmeet₀
    rw [hbd₀]
    have hsub : J ×ˢ {(-1 : ℝ)} ⊆ J ×ˢ {(-1 : ℝ), 1} :=
      fun _ hx => ⟨hx.1, Or.inl hx.2⟩
    exact (image_mono hsub).trans
      (hRbd.symm.subset.trans (boundaryComplex_space_subset 2 R))
  have hRmeet₁ : R.space ∩ D₁ = r₁ '' stdSimplexBoundary 2 := by
    apply hRmeet (subset_union_right.trans hcaps) hmeet₁
    rw [hbd₁]
    have hsub : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ {(-1 : ℝ), 1} :=
      fun _ hx => ⟨hx.1, Or.inr hx.2⟩
    exact (image_mono hsub).trans
      (hRbd.symm.subset.trans (boundaryComplex_space_subset 2 R))
  rw [← hRspace]
  by_cases hcircle : IsPreconnected (S.space \ J)
  · have hRc := Topology.isConnected_complement_of_bicollar hJ.isConnected
      hJ.isPolyhedron.isCompact (isPolyhedron_space R).isClosed
      (by rwa [union_comm]) (by rwa [inter_comm])
      hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn hzero hcircle
    obtain ⟨P, hPfin, hP, hPc, hPo, -, hPβ, -, hPspace⟩ :=
      hS.exists_capped_annulus_complement S R hconn hdim hR hRc hJ
        (by norm_num : (-1 : ℝ) < 1) hρ hcover htrace hRbd
        hr₀ hr₁ hdis hRmeet₀ hRmeet₁ hbd₀ hbd₁
    let _ : Finite P.faces := hPfin.to_subtype
    have hχ := hP.eulerChar_eq_two_sub_bettiOne_of_isOrientable P hPc hPo
    rw [← hPspace]
    apply hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc
    change eulerChar P = 2
    rw [hχ]
    omega
  · exfalso
    obtain ⟨P, Q, hPfin, hQfin, hP, hQ, hPc, hQc, hPo, hQo, hPs, hQs, -, -, hsum, -, -, -⟩ :=
      hS.exists_capped_pair_of_separating_essential_annulus S R hconn hdim hR hJ hJS hρ hzero
        hWnhds hcover htrace hRbd hcircle hnon hr₀ hr₁ hdis hRmeet₀ hRmeet₁ hbd₀ hbd₁
    let _ : Finite P.faces := hPfin.to_subtype
    let _ : Finite Q.faces := hQfin.to_subtype
    have hPpos := hP.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two P hPc hPo
      (fun h => hPs (hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc h))
    have hQpos := hQ.bettiOne_pos_of_isOrientable_of_eulerChar_ne_two Q hQc hQo
      (fun h => hQs (hQ.isPLSphere_two_of_faceEulerChar_eq_two Q hQc h))
    obtain ⟨m, hm⟩ := hP.even_bettiOne_of_finrank_eq_three P hdim hPc
    obtain ⟨k, hk⟩ := hQ.even_bettiOne_of_finrank_eq_three Q hdim hQc
    omega

end General

theorem IsPLTorus.isPathConnected {T : Set E3} (hT : IsPLTorus T) :
    IsPathConnected T := by
  obtain ⟨-, ⟨e⟩⟩ := hT
  have hS : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
    apply isPathConnected_sphere _ _ zero_le_one
    rw [← Module.finrank_eq_rank]
    norm_num
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hS
  let _ : PathConnectedSpace T := e.symm.surjective.pathConnectedSpace e.symm.continuous
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem IsPLTorus.bettiOne_le_two {T : Set E3} (hT : IsPLTorus T) :
    Homology.bettiOne T ≤ 2 := by
  have hpc := hT.isPathConnected
  obtain ⟨x, hx⟩ := hpc.nonempty
  obtain ⟨-, ⟨e⟩⟩ := hT
  let _ : PathConnectedSpace T := isPathConnected_iff_pathConnectedSpace.mp hpc
  let x₀ : T := ⟨x, hx⟩
  let f : FundamentalGroup T x₀ ≃* Multiplicative (ℤ × ℤ) :=
    ((fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv x₀ (e x₀) rfl).trans
      (fundamentalGroupTorusEquivIntProd (e x₀))).trans (MulEquiv.prodMultiplicative ℤ ℤ).symm
  have hle := fieldSingularHomology_one_finrank_le_of_fundamentalGroup_injective
    (k := ℚ) x₀ f.toMonoidHom f.injective
  change Homology.bettiOne T ≤ Module.finrank ℤ (ℤ × ℤ) at hle
  simpa using hle

theorem IsPLSphere.exists_isPLBall_eq_of_isOpen_sdiff {S : Set E3} (hS : IsPLSphere 2 S) :
    ∃ B : Set E3, IsPLBall 3 B ∧ frontier B = S ∧
      ∀ X : Set E3, IsCompact X → S ⊆ X → IsOpen (X \ S) →
        (X \ S).Nonempty → X = B := by
  obtain ⟨B, hB, hfront, -, hunion, -, hint, hext, hunb⟩ :=
    hS.exists_isPLBall_complement_components
  refine ⟨B, hB, hfront, fun X hX hSX hXo hXne => ?_⟩
  have hBclosed : IsClosed B := hB.isPolyhedron.isClosed
  have hcover : Sᶜ ⊆ (X \ S) ∪ Xᶜ := by
    intro y hy
    by_cases hyX : y ∈ X
    · exact Or.inl ⟨hyX, hy⟩
    · exact Or.inr hyX
  have hXdisj : Disjoint (X \ S) Xᶜ := disjoint_compl_right.mono_left sdiff_subset
  have hSB : S ⊆ B := by
    rw [← hfront]
    exact hBclosed.frontier_subset
  have hext' : Bᶜ ⊆ Xᶜ := by
    rcases hext.isPreconnected.subset_or_subset hXo hX.isClosed.isOpen_compl hXdisj
      ((compl_subset_compl.mpr hSB).trans hcover) with h | h
    · exact (hunb (hX.isBounded.subset (h.trans sdiff_subset))).elim
    · exact h
  have hint' : interior B ⊆ X \ S := by
    have hintS : interior B ⊆ Sᶜ := by
      intro y hy hyS
      rw [← hfront] at hyS
      exact hyS.2 hy
    rcases hint.isPreconnected.subset_or_subset hXo hX.isClosed.isOpen_compl hXdisj
      (hintS.trans hcover) with h | h
    · exact h
    · obtain ⟨y, hyX, hyS⟩ := hXne
      rcases hunion.subset hyS with hy | hy
      · exact (h hy hyX).elim
      · exact (hext' hy hyX).elim
  apply Subset.antisymm
  · exact compl_subset_compl.mp hext'
  · rw [← hBclosed.closure_eq, closure_eq_interior_union_frontier, hfront]
    exact union_subset (hint'.trans sdiff_subset) hSX

theorem IsPLSphere.isPLBall_of_isOpen_sdiff {S X : Set E3}
    (hS : IsPLSphere 2 S) (hX : IsCompact X) (hSX : S ⊆ X) (hXo : IsOpen (X \ S))
    (hXne : (X \ S).Nonempty) : IsPLBall 3 X ∧ frontier X = S := by
  obtain ⟨B, hB, hfront, huniq⟩ := hS.exists_isPLBall_eq_of_isOpen_sdiff
  rw [huniq X hX hSX hXo hXne]
  exact ⟨hB, hfront⟩

theorem IsPLBall.exists_isPLBall_subset_interior_of_isOpen {B U : Set E3}
    (hB : IsPLBall 3 B) (hU : IsOpen U) (hBU : B ⊆ U) :
    ∃ B' : Set E3, IsPLBall 3 B' ∧ B ⊆ interior B' ∧ B' ⊆ U := by
  obtain ⟨-, hsimp⟩ := hB.isPLSphere_frontier.isSimplyEmbedded
  obtain ⟨T, h, hT, hTcard, hh, himage, -⟩ := hsimp univ convex_univ isOpen_univ (subset_univ _)
  set Δ := convexHull ℝ (T : Set E3) with hΔdef
  have hTcard' : T.card = Module.finrank ℝ E3 + 1 := by simp [hTcard]
  have hΔ : IsPLBall 3 Δ := isPLBall_convexHull_of_affineIndependent T hT hTcard
  have hΔc : IsCompact Δ := hΔ.isPolyhedron.isCompact
  have hBc : IsCompact B := hB.isPolyhedron.isCompact
  have hhB : h '' B = Δ := by
    obtain ⟨C, -, -, huniq⟩ := hΔ.isPLSphere_frontier.exists_isPLBall_eq_of_isOpen_sdiff
    have hsub : frontier Δ ⊆ h '' B := by
      rw [← himage]
      exact image_mono hB.isPolyhedron.isClosed.frontier_subset
    have hopen : IsOpen (h '' B \ frontier Δ) := by
      rw [← himage, ← image_sdiff h.injective, self_sdiff_frontier]
      exact h.isOpenMap _ isOpen_interior
    have hne : (h '' B \ frontier Δ).Nonempty := by
      rw [← himage, ← image_sdiff h.injective, self_sdiff_frontier]
      exact hB.interior_nonempty.image h
    rw [huniq _ (hBc.image h.continuous) hsub hopen hne,
      huniq _ hΔc hΔc.isClosed.frontier_subset
        (by rw [self_sdiff_frontier]; exact isOpen_interior)
        (by rw [self_sdiff_frontier]; exact hΔ.interior_nonempty)]
  set c := T.centroid ℝ id with hcdef
  have hc : c ∈ interior Δ := by
    rw [hΔdef, interior_convexHull_eq_openSimplex hT hTcard']
    exact centroid_mem_openSimplex (Finset.card_pos.mp (by omega))
  have hV : IsOpen (h '' U) := h.isOpenMap U hU
  have hΔV : Δ ⊆ h '' U := by
    rw [← hhB]
    exact image_mono hBU
  obtain ⟨ε, hε, hεV⟩ := hΔc.exists_thickening_subset_open hV hΔV
  obtain ⟨M, hM⟩ := hΔc.isBounded.subset_closedBall c
  set δ : ℝ := ε / (|M| + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδM : δ * |M| < ε := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set t : ℝ := 1 + δ with htdef
  have ht0 : t ≠ 0 := by positivity
  have hhinj : Function.Injective (AffineMap.homothety c t) := by
    intro p q hpq
    simpa only [AffineMap.homothety_apply, vadd_right_cancel_iff, smul_right_inj ht0,
      vsub_left_cancel_iff] using hpq
  have hTind : AffineIndependent ℝ ((↑) : T.image (AffineMap.homothety c t) → E3) := by
    convert ((affineIndependent_image_iff T (AffineMap.homothety c t)).mp
      (hT.map' (AffineMap.homothety c t) hhinj)).2
  obtain ⟨T', hT', hT'card, hΔ'eq⟩ : ∃ T' : Finset E3,
      AffineIndependent ℝ ((↑) : T' → E3) ∧ T'.card = 3 + 1 ∧
        convexHull ℝ (T' : Set E3) = AffineMap.homothety c t '' Δ :=
    ⟨T.image (AffineMap.homothety c t), hTind,
      by rw [Finset.card_image_of_injective _ hhinj, hTcard],
      by rw [Finset.coe_image, hΔdef, AffineMap.image_convexHull]⟩
  set Δ' := convexHull ℝ (T' : Set E3) with hΔ'def
  have hΔ' : IsPLBall 3 Δ' := isPLBall_convexHull_of_affineIndependent T' hT' hT'card
  have hint : Δ ⊆ interior Δ' := by
    rw [hΔ'eq]
    exact (convex_convexHull ℝ _).subset_interior_image_homothety_of_one_lt hc t
      (by rw [htdef]; linarith)
  have hthick : Δ' ⊆ h '' U := by
    rw [hΔ'eq]
    rintro _ ⟨x, hx, rfl⟩
    apply hεV
    rw [Metric.mem_thickening_iff]
    refine ⟨x, hx, ?_⟩
    rw [dist_homothety_self, htdef, sub_add_cancel_left, norm_neg, Real.norm_eq_abs,
      abs_of_pos hδ]
    have hxc : dist c x ≤ |M| := by
      rw [dist_comm]
      exact (hM hx).trans (le_abs_self M)
    calc δ * dist c x ≤ δ * |M| := mul_le_mul_of_nonneg_left hxc hδ.le
      _ < ε := hδM
  refine ⟨h ⁻¹' Δ', ?_, ?_, ?_⟩
  · have heq : Function.invFunOn h univ '' Δ' = h ⁻¹' Δ' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        change h (Function.invFunOn h univ z) ∈ Δ'
        rw [Function.invFunOn_eq ⟨h.symm z, mem_univ _, h.apply_symm_apply z⟩]
        exact hz
      · intro hy
        exact ⟨h y, hy, h.injective (Function.invFunOn_eq (f := ⇑h) ⟨y, mem_univ _, rfl⟩)⟩
    rw [← heq]
    exact hΔ'.of_isPLHomeomorphOn (hh.symm.restrict hΔ'.isPolyhedron (subset_univ _))
  · intro y hy
    rw [← h.preimage_interior]
    exact hint (hhB ▸ mem_image_of_mem h hy)
  · intro y hy
    obtain ⟨u, hu, hyu⟩ := hthick hy
    rw [h.injective hyu] at hu
    exact hu

theorem exists_isPLBall_superset_of_exterior_compression
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 3 R) (hT : IsPLTorus (frontier R.space))
    {U D : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U) (hRU : R.space ⊆ U)
    {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D) (hDU : D ⊆ U)
    (hmeet : D ∩ frontier R.space = r '' stdSimplexBoundary 2)
    (hess : ∃ hboundary : r '' stdSimplexBoundary 2 ⊆ frontier R.space,
      ¬ (⟨Set.inclusion hboundary, continuous_inclusion hboundary⟩ :
        C(r '' stdSimplexBoundary 2, frontier R.space)).Nullhomotopic)
    (hext : D \ r '' stdSimplexBoundary 2 ⊆ R.spaceᶜ) :
    ∃ B : Set (EuclideanSpace ℝ (Fin 3)),
      IsPLBall 3 B ∧ R.space ⊆ interior B ∧ B ⊆ U := by
  obtain ⟨K, hKfin, hK, hKR⟩ :=
    hR.exists_isCombinatorialManifold_space_eq_frontier (n := 2) (by simp)
  let _ : Finite K.faces := hKfin.to_subtype
  have hKc : IsConnected K.space := by
    rw [hKR]
    exact hT.isPathConnected.isConnected
  have hβ : Homology.bettiOne K.space ≤ 2 := by
    rw [hKR]
    exact hT.bettiOne_le_two
  rw [← hKR] at hmeet hess
  obtain ⟨hJK, hnon⟩ := hess
  obtain ⟨N, W, D₀, D₁, _, ρ, r₀, r₁, hN, hNU, -, hinside, -, -, -, -, hwall, -, -, -, hρ,
    hρzero, -, hr₀, hr₁, hdis, hfront, hmeet₀, hmeet₁, hbd₀, hbd₁⟩ :=
    hK.exists_compression_neighborhood_of_spanning_disk K hKc (by simp) hr hmeet hU
      hDU
  have hSig := hK.isPLSphere_closure_sdiff_union_of_bettiOne_le_two K hKc (by simp) hβ
    hr.isPLSphere_image_stdSimplexBoundary hJK hρ hρzero hnon hN hwall hr₀ hr₁ hdis hfront
    hmeet₀ hmeet₁ hbd₀ hbd₁
  set P := closure (K.space \ W) ∪ D₀ ∪ D₁ with hPdef
  have hRclosed : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hNclosed : IsClosed N := hN.isPolyhedron.isClosed
  have hKclosed : IsClosed K.space := (isPolyhedron_space K).isClosed
  have hPclosed : IsClosed P := hSig.isPolyhedron.isClosed
  have hKsub : K.space ⊆ R.space := by
    rw [hKR]
    exact hRclosed.frontier_subset
  have hWK : W ⊆ K.space := hwall.symm.subset.trans inter_subset_left
  have hWN : W ⊆ N := hwall.symm.subset.trans inter_subset_right
  have hcapsN : D₀ ∪ D₁ ⊆ frontier N := by
    rw [hfront]
    rintro x (hx | hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  have hNreg : closure (interior N) = N := hN.closure_interior_of_finrank (by simp)
  have hintN : IsConnected (interior N) := hN.isConnected_interior_of_finrank (by simp)
  have hRreg : R.space ⊆ closure (interior R.space) :=
    hR.subset_closure_interior_space (by simp)
  have hintNK : Disjoint (interior N) K.space := by
    rw [disjoint_left]
    intro y hyN hyK
    have hyF : y ∈ frontier N := by
      rw [hfront]
      exact Or.inl (Or.inl (hwall.subset ⟨hyK, interior_subset hyN⟩))
    exact hyF.2 hyN
  have hintNout : interior N ⊆ R.spaceᶜ := by
    obtain ⟨p, hpD, hpJ⟩ := hr.isConnected_sdiff_image_stdSimplexBoundary.nonempty
    have hpK : p ∉ K.space := fun h => hpJ (hmeet.subset ⟨hpD, h⟩)
    have hsub : interior N ⊆ interior R.space ∪ R.spaceᶜ := by
      intro y hy
      by_cases hyR : y ∈ R.space
      · refine Or.inl ((mem_interior_iff_notMem_frontier hyR).mpr ?_)
        rw [← hKR]
        exact disjoint_left.mp hintNK hy
      · exact Or.inr hyR
    rcases hintN.isPreconnected.subset_or_subset isOpen_interior hRclosed.isOpen_compl
        (disjoint_compl_right.mono_left interior_subset) hsub with h | h
    · exact (hext ⟨hpD, hpJ⟩ (interior_subset (h (hinside ⟨hpD, hpK⟩)))).elim
    · exact h
  have hNintR : Disjoint N (interior R.space) := by
    rw [disjoint_left]
    intro y hyN hyR
    have hy : y ∈ closure (R.spaceᶜ) := by
      rw [← hNreg] at hyN
      exact closure_mono hintNout hyN
    rw [closure_compl] at hy
    exact hy hyR
  have hlocal (y : EuclideanSpace ℝ (Fin 3)) (hyW : y ∈ W) (hyP : y ∉ P) :
      R.space ∪ N ∈ 𝓝 y := by
    obtain ⟨C, hC, hCP, A, B, hA, hB, hAB, -, -⟩ :=
      hK.exists_connected_neighborhood_pair_sdiff K (by simp) (hWK hyW)
        (hPclosed.isOpen_compl.mem_nhds hyP)
    have hpieceN (Q : Set (EuclideanSpace ℝ (Fin 3))) (hQ : Q ⊆ C \ K.space) :
        Disjoint Q (frontier N) := by
      rw [disjoint_left, hfront]
      rintro z hz ((hzW | hz₀) | hz₁)
      · exact (hQ hz).2 (hWK hzW)
      · exact hCP (hQ hz).1 (Or.inl (Or.inr hz₀))
      · exact hCP (hQ hz).1 (Or.inr hz₁)
    have hpieceR (Q : Set (EuclideanSpace ℝ (Fin 3))) (hQ : Q ⊆ C \ K.space) :
        Disjoint Q (frontier R.space) := by
      rw [← hKR, disjoint_left]
      exact fun z hz => (hQ hz).2
    have hAsub : A ⊆ C \ K.space := hAB ▸ subset_union_left
    have hBsub : B ⊆ C \ K.space := hAB ▸ subset_union_right
    obtain ⟨a, haC, haN⟩ : (C ∩ interior N).Nonempty := by
      have hyN : y ∈ closure (interior N) := by
        rw [hNreg]
        exact hWN hyW
      exact mem_closure_iff_nhds.mp hyN C hC
    obtain ⟨b, hbC, hbR⟩ : (C ∩ interior R.space).Nonempty :=
      mem_closure_iff_nhds.mp (hRreg (hKsub (hWK hyW))) C hC
    have hab : a ∈ A ∪ B := by
      rw [hAB]
      exact ⟨haC, disjoint_left.mp hintNK haN⟩
    have hbb : b ∈ A ∪ B := by
      rw [hAB]
      refine ⟨hbC, fun hbK => ?_⟩
      have hbF : b ∈ frontier R.space := by
        rw [← hKR]
        exact hbK
      exact hbF.2 hbR
    have hbN : b ∉ interior N := fun h => disjoint_left.mp hNintR (interior_subset h) hbR
    have hcover : A ∪ B ⊆ interior N ∪ interior R.space := by
      rcases hab with haA | haB <;> rcases hbb with hbA | hbB
      · exact (hbN (IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
          (hpieceN A hAsub) ⟨a, haA, haN⟩ hbA)).elim
      · exact union_subset
          ((IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
            (hpieceN A hAsub) ⟨a, haA, haN⟩).trans subset_union_left)
          ((IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
            (hpieceR B hBsub) ⟨b, hbB, hbR⟩).trans subset_union_right)
      · exact union_subset
          ((IsPreconnected.subset_interior_of_disjoint_frontier hA.isPreconnected
            (hpieceR A hAsub) ⟨b, hbA, hbR⟩).trans subset_union_right)
          ((IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
            (hpieceN B hBsub) ⟨a, haB, haN⟩).trans subset_union_left)
      · exact (hbN (IsPreconnected.subset_interior_of_disjoint_frontier hB.isPreconnected
          (hpieceN B hBsub) ⟨a, haB, haN⟩ hbB)).elim
    apply Filter.mem_of_superset hC
    intro z hz
    by_cases hzK : z ∈ K.space
    · exact Or.inl (hKsub hzK)
    · have hz' : z ∈ A ∪ B := by
        rw [hAB]
        exact ⟨hz, hzK⟩
      rcases hcover hz' with h | h
      · exact Or.inr (interior_subset h)
      · exact Or.inl (interior_subset h)
  have hopen : IsOpen ((R.space ∪ N) \ P) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨hyX, hyP⟩
    refine Filter.sdiff_mem ?_ (hPclosed.isOpen_compl.mem_nhds hyP)
    by_cases hyR : y ∈ interior R.space
    · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hyR)
        (interior_subset.trans subset_union_left)
    by_cases hyN : y ∈ interior N
    · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hyN)
        (interior_subset.trans subset_union_right)
    apply hlocal y _ hyP
    rcases hyX with hy | hy
    · have hyK : y ∈ K.space := by
        rw [hKR]
        exact ⟨subset_closure hy, hyR⟩
      by_contra hyW
      exact hyP (Or.inl (Or.inl (subset_closure ⟨hyK, hyW⟩)))
    · have hyF : y ∈ frontier N := ⟨subset_closure hy, hyN⟩
      rw [hfront] at hyF
      rcases hyF with (h | h) | h
      · exact h
      · exact (hyP (Or.inl (Or.inr h))).elim
      · exact (hyP (Or.inr h)).elim
  have hPX : P ⊆ R.space ∪ N := by
    rintro y ((hy | hy) | hy)
    · exact Or.inl (hKsub (closure_minimal sdiff_subset hKclosed hy))
    · exact Or.inr (hNclosed.frontier_subset (hcapsN (Or.inl hy)))
    · exact Or.inr (hNclosed.frontier_subset (hcapsN (Or.inr hy)))
  have hXne : ((R.space ∪ N) \ P).Nonempty := by
    obtain ⟨z, hz⟩ := hN.interior_nonempty
    refine ⟨z, Or.inr (interior_subset hz), ?_⟩
    rintro ((h | h) | h)
    · exact disjoint_left.mp hintNK hz (closure_minimal sdiff_subset hKclosed h)
    · exact (hcapsN (Or.inl h)).2 hz
    · exact (hcapsN (Or.inr h)).2 hz
  obtain ⟨hX, -⟩ := hSig.isPLBall_of_isOpen_sdiff
    ((isPolyhedron_space R).isCompact.union hN.isPolyhedron.isCompact) hPX hopen hXne
  obtain ⟨B, hB, hXB, hBU⟩ :=
    hX.exists_isPLBall_subset_interior_of_isOpen hU (union_subset hRU hNU)
  exact ⟨B, hB, subset_union_left.trans hXB, hBU⟩

end DifferentialGeometry.Topology.PiecewiseLinear
