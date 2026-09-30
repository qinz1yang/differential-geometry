/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLArcChainUnion
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.SphereCellComplement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.image_stdSimplexBoundary_one_of_Icc {β : Set F} {γ : ℝ → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) :
    IsPLHomeomorphOn (γ ∘ Function.invFunOn
        (AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1]) (Icc 0 1))
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) β ∧
      (γ ∘ Function.invFunOn (AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1])
        (Icc 0 1)) '' stdSimplexBoundary 1 = {γ 0, γ 1} := by
  have hL := isPLHomeomorphOn_lineMap_Icc_stdSimplex_two
  refine ⟨hL.symm.trans hγ, ?_⟩
  have hinv0 : Function.invFunOn (AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1])
      (Icc 0 1) ![1, 0] = 0 := by
    have h := hL.bijOn.invOn_invFunOn.1 (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)
    rwa [AffineMap.lineMap_apply_zero] at h
  have hinv1 : Function.invFunOn (AffineMap.lineMap (k := ℝ) (![1, 0] : Fin 2 → ℝ) ![0, 1])
      (Icc 0 1) ![0, 1] = 1 := by
    have h := hL.bijOn.invOn_invFunOn.1 (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
    rwa [AffineMap.lineMap_apply_one] at h
  rw [stdSimplexBoundary_one_eq_pair, image_pair, Function.comp_apply, Function.comp_apply,
    hinv0, hinv1]

theorem IsPLSphere.inter_closure_sdiff_eq_pair_of_Icc {S β : Set F} (hS : IsPLSphere 1 S)
    {γ : ℝ → F} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hβS : β ⊆ S) :
    β ∩ closure (S \ β) = {γ 0, γ 1} := by
  obtain ⟨hr, hrb⟩ := hγ.image_stdSimplexBoundary_one_of_Icc
  rw [hS.inter_closure_sdiff_eq_image_stdSimplexBoundary_one hr hβS, hrb]

theorem IsPLSphere.exists_isPLHomeomorphOn_closure_sdiff {S β : Set F} (hS : IsPLSphere 1 S)
    {γ : ℝ → F} (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hβS : β ⊆ S) :
    ∃ δ : ℝ → F, IsPLHomeomorphOn δ (Icc 0 1) (closure (S \ β)) ∧ δ 0 = γ 0 ∧ δ 1 = γ 1 ∧
      β ∩ closure (S \ β) = {γ 0, γ 1} ∧ β ∪ closure (S \ β) = S := by
  have hone : (0 : ℝ) < 1 := one_pos
  have hβ : IsPLBall 1 β := (isPLBall_Icc hone).of_isPLHomeomorphOn hγ
  have hSc : IsClosed S := hS.isPolyhedron.isClosed
  have hβ' : IsPLBall 1 (closure (S \ β)) := hS.isPLBall_closure_sdiff_one hβ hβS
  have hβ'S : closure (S \ β) ⊆ S := closure_minimal sdiff_subset hSc
  have hmeet : β ∩ closure (S \ β) = {γ 0, γ 1} := hS.inter_closure_sdiff_eq_pair_of_Icc hγ hβS
  have hunion : β ∪ closure (S \ β) = S := by
    refine Subset.antisymm (union_subset hβS hβ'S) fun x hx => ?_
    by_cases hxβ : x ∈ β
    · exact Or.inl hxβ
    · exact Or.inr (subset_closure ⟨hx, hxβ⟩)
  obtain ⟨δ₀, hδ₀⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hβ'
  have hcomp : S \ closure (S \ β) = β \ {γ 0, γ 1} := by
    ext x
    constructor
    · rintro ⟨hxS, hx'⟩
      have hxβ : x ∈ β := by
        by_contra hxβ
        exact hx' (subset_closure ⟨hxS, hxβ⟩)
      exact ⟨hxβ, fun h => hx' ((hmeet.symm.subset h).2)⟩
    · rintro ⟨hxβ, hxe⟩
      exact ⟨hβS hxβ, fun h => hxe (hmeet.subset ⟨hxβ, h⟩)⟩
  have hends : closure (S \ β) ∩ closure (S \ closure (S \ β)) = {γ 0, γ 1} := by
    rw [hcomp, hγ.closure_sdiff_endpoints hone, inter_comm, hmeet]
  have hends' := hS.inter_closure_sdiff_eq_pair_of_Icc hδ₀ hβ'S
  rw [hends] at hends'
  have hδne : δ₀ 0 ≠ δ₀ 1 := fun h => zero_ne_one
    (hδ₀.bijOn.injOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h)
  have h0 : δ₀ 0 = γ 0 ∨ δ₀ 0 = γ 1 := by
    have : δ₀ 0 ∈ ({γ 0, γ 1} : Set F) := hends' ▸ mem_insert _ _
    exact this
  have h1 : δ₀ 1 = γ 0 ∨ δ₀ 1 = γ 1 := by
    have : δ₀ 1 ∈ ({γ 0, γ 1} : Set F) := hends' ▸ mem_insert_of_mem _ (mem_singleton _)
    exact this
  rcases h0 with h0 | h0
  · refine ⟨δ₀, hδ₀, h0, ?_, hmeet, hunion⟩
    rcases h1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hδne
    · exact h1
  · refine ⟨fun x => δ₀ (1 - x), isPLHomeomorphOn_comp_one_sub hδ₀, ?_, ?_, hmeet, hunion⟩
    · simp only [sub_zero]
      rcases h1 with h1 | h1
      · exact h1
      · exact absurd (h0.trans h1.symm) hδne
    · simp only [sub_self]
      exact h0

theorem exists_isPLHomeomorphOn_closure_sdiff_of_cap {D E β : Set F}
    {q r : (Fin 3 → ℝ) → F} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) E) (hED : E ⊆ D) {γ : ℝ → F}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) β) (hβE : β ⊆ r '' stdSimplexBoundary 2)
    (hEDb : E ∩ q '' stdSimplexBoundary 2 = β) :
    ∃ q' : (Fin 3 → ℝ) → F, IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (closure (D \ E)) ∧
      q' '' stdSimplexBoundary 2 = (q '' stdSimplexBoundary 2 \ (β \ {γ 0, γ 1})) ∪
        closure (r '' stdSimplexBoundary 2 \ β) ∧
      closure (D \ E) ∩ E = closure (r '' stdSimplexBoundary 2 \ β) ∧
      closure (D \ E) ∪ E = D := by
  classical
  set Db := q '' stdSimplexBoundary 2 with hDb
  set Eb := r '' stdSimplexBoundary 2 with hEb
  have hone : (0 : ℝ) < 1 := one_pos
  have hEbS : IsPLSphere 1 Eb :=
    ⟨r, hr.restrict isPolyhedron_stdSimplexBoundary_two fun x hx => hx.1⟩
  have hEbE : Eb ⊆ E := by
    rw [hEb, ← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hDbD : Db ⊆ D := by
    rw [hDb, ← hq.image_eq]
    exact image_mono fun x hx => hx.1
  obtain ⟨δ, hδ, hδ0, hδ1, hββ', hβ'Eb⟩ := hEbS.exists_isPLHomeomorphOn_closure_sdiff hγ hβE
  set β' := closure (Eb \ β) with hβ'def
  have hβ'E : β' ⊆ E := (subset_union_right.trans hβ'Eb.subset).trans hEbE
  have hβ'D : β' ⊆ D := hβ'E.trans hED
  have hβ'poly : IsPolyhedron β' := ((isPLBall_Icc hone).of_isPLHomeomorphOn hδ).isPolyhedron
  have hβ'Db : β' ∩ Db = {γ 0, γ 1} := by
    apply Subset.antisymm
    · rintro x ⟨hx', hxD⟩
      have hxβ : x ∈ β := hEDb.subset ⟨hβ'E hx', hxD⟩
      exact hββ'.subset ⟨hxβ, hx'⟩
    · intro x hx
      have hx' := hββ'.symm.subset hx
      exact ⟨hx'.2, (hEDb.symm.subset hx'.1).2⟩
  obtain ⟨T, hTind, hTcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1)
    (0 : EuclideanSpace ℝ (Fin 2)) (Filter.univ_mem : univ ∈ nhds (0 : EuclideanSpace ℝ (Fin 2)))
  set Δ := convexHull ℝ (T : Set (EuclideanSpace ℝ (Fin 2))) with hΔdef
  have hΔ : IsPLBall 2 Δ := isPLBall_convexHull_of_affineIndependent T hTind hTcard
  obtain ⟨p, hp⟩ := hΔ
  have hΔ : IsPLBall 2 Δ := ⟨p, hp⟩
  have hΔc : IsClosed Δ := hΔ.isPolyhedron.isClosed
  set s := p ∘ Function.invFunOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) with hsdef
  have hs : IsPLHomeomorphOn s D Δ := hq.symm.trans hp
  have hsDb : s '' Db = frontier Δ := by
    rw [← IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) hp, hDb, ← image_comp]
    refine image_congr fun x hx => ?_
    simp only [hsdef, Function.comp_apply]
    rw [hq.bijOn.invOn_invFunOn.1 hx.1]
  have hsinj : InjOn s D := hs.bijOn.injOn
  set g := Function.invFunOn s D with hgdef
  have hg : IsPLHomeomorphOn g Δ D := hs.symm
  have hgs : ∀ x ∈ D, g (s x) = x := fun x hx => hs.bijOn.invOn_invFunOn.1 hx
  have hsg : ∀ y ∈ Δ, s (g y) = y := fun y hy => hs.bijOn.invOn_invFunOn.2 hy
  have hgsimg : ∀ X ⊆ D, g '' (s '' X) = X := by
    intro X hX
    rw [← image_comp]
    refine (image_congr fun y hy => ?_).trans (image_id X)
    exact hgs y (hX hy)
  have hsβ' : IsPLHomeomorphOn s β' (s '' β') := hs.restrict hβ'poly hβ'D
  have hA : IsPLBall 1 (s '' β') := (isPLBall_Icc hone).of_isPLHomeomorphOn (hδ.trans hsβ')
  have hmemfr : ∀ y ∈ Db, s y ∈ frontier Δ := fun y hy => hsDb ▸ mem_image_of_mem s hy
  have hcross : Schoenflies.IsCrosscut (frontier Δ) (s '' β') ((s ∘ δ) 0) ((s ∘ δ) 1) := by
    refine IsPLHomeomorphOn.isCrosscut_of_image_Ioo_subset_interior (hδ.trans hsβ') ⟨p, hp⟩
      ?_ ?_ ?_
    · rw [Function.comp_apply, hδ0]
      exact hmemfr _ (hβ'Db.symm.subset (mem_insert _ _)).2
    · rw [Function.comp_apply, hδ1]
      exact hmemfr _ (hβ'Db.symm.subset (mem_insert_of_mem _ (mem_singleton _))).2
    · rintro _ ⟨t, ht, rfl⟩
      have htβ' : δ t ∈ β' := hδ.bijOn.mapsTo (Ioo_subset_Icc_self ht)
      have htne : δ t ∉ ({γ 0, γ 1} : Set F) := by
        rw [← hδ0, ← hδ1]
        have := (hδ.image_Ioo_eq_sdiff_endpoints hone).subset (mem_image_of_mem δ ht)
        exact this.2
      have htD : δ t ∉ Db := fun h => htne (hβ'Db.subset ⟨htβ', h⟩)
      have hin : s (δ t) ∈ Δ := hs.bijOn.mapsTo (hβ'D htβ')
      rw [Function.comp_apply]
      by_contra hint
      have hfr : s (δ t) ∈ frontier Δ := by
        rw [hΔc.frontier_eq]
        exact ⟨hin, hint⟩
      rw [← hsDb] at hfr
      obtain ⟨y, hy, hyeq⟩ := hfr
      exact htD (hsinj (hDbD hy) (hβ'D htβ') hyeq ▸ hy)
  obtain ⟨U, V, hU, hV, hUV, hUiV, hfU, hfV, hAU, hAV, -, -, hside⟩ :=
    exists_isPLBall_pair_with_boundary_arcs_of_isCrosscut hΔ hA hcross
  have hsE : IsPLHomeomorphOn s E (s '' E) :=
    hs.restrict (show IsPLBall 2 E from ⟨r, hr⟩).isPolyhedron hED
  have hsEball : IsPLBall 2 (s '' E) := ⟨s ∘ r, hr.trans hsE⟩
  have hsEfr : frontier (s '' E) = s '' Eb := by
    rw [← IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) (hr.trans hsE), hEb, image_comp]
  have hsEΔ : s '' E ⊆ Δ := hs.image_eq ▸ image_mono hED
  have hdisj : Disjoint (interior (s '' E)) (s '' β') := by
    refine Set.disjoint_left.mpr fun x hx hxA => ?_
    have hxfr : x ∈ frontier (s '' E) := by
      rw [hsEfr]
      exact image_mono (subset_union_right.trans hβ'Eb.subset) hxA
    exact Set.disjoint_left.mp disjoint_interior_frontier hx hxfr
  have hfrU : ∀ W : Set (EuclideanSpace ℝ (Fin 2)), W ⊆ Δ → IsClosed W →
      W ∩ frontier Δ ⊆ frontier W := by
    intro W hWΔ hWc x ⟨hxW, hxfr⟩
    rw [hWc.frontier_eq]
    refine ⟨hxW, fun hxi => ?_⟩
    rw [hΔc.frontier_eq] at hxfr
    exact hxfr.2 (interior_mono hWΔ hxi)
  have key : ∀ U V : Set (EuclideanSpace ℝ (Fin 2)), IsPLBall 2 U → IsPLBall 2 V →
      U ∪ V = Δ → U ∩ V = s '' β' → frontier V ⊆ frontier Δ ∪ s '' β' →
      s '' β' ⊆ frontier U → s '' β' ⊆ frontier V → s '' E ⊆ U →
      ∃ q' : (Fin 3 → ℝ) → F, IsPLHomeomorphOn q' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (closure (D \ E)) ∧
        q' '' stdSimplexBoundary 2 = (Db \ (β \ {γ 0, γ 1})) ∪ β' ∧
        closure (D \ E) ∩ E = β' ∧ closure (D \ E) ∪ E = D := by
    intro U V hU hV hUV hUiV hfV hAU hAV hEU
    have hUΔ : U ⊆ Δ := hUV ▸ subset_union_left
    have hVΔ : V ⊆ Δ := hUV ▸ subset_union_right
    have hUc : IsClosed U := hU.isPolyhedron.isClosed
    have hVc : IsClosed V := hV.isPolyhedron.isClosed
    have hfrsub : frontier (s '' E) ⊆ frontier U := by
      rw [hsEfr, ← hβ'Eb, image_union]
      refine union_subset (fun x hx => ?_) hAU
      obtain ⟨y, hy, rfl⟩ := hx
      exact hfrU U hUΔ hUc ⟨hEU (mem_image_of_mem s (hEDb.symm.subset hy).1),
        hmemfr y (hEDb.symm.subset hy).2⟩
    have hfreq : frontier (s '' E) = frontier U :=
      eq_of_subset_of_isPLSphere_one hsEball.isPLSphere_frontier hU.isPLSphere_frontier hfrsub
    have hEeq : s '' E = U := by
      rw [← hsEball.closure_interior, ← hU.closure_interior, hsEball.interior_eq_inside_frontier,
        hU.interior_eq_inside_frontier, hfreq]
    have hEg : E = g '' U := by
      rw [← hEeq, hgsimg E hED]
    have hgΔ : g '' Δ = D := hg.image_eq
    have hginj : InjOn g Δ := hg.bijOn.injOn
    have hfrV : frontier V = (V ∩ frontier Δ) ∪ s '' β' := by
      apply Subset.antisymm
      · intro x hx
        rcases hfV hx with h | h
        · exact Or.inl ⟨hVc.frontier_subset hx, h⟩
        · exact Or.inr h
      · exact union_subset (hfrU V hVΔ hVc) hAV
    have hVfr : V ∩ frontier Δ = s '' (Db \ (β \ {γ 0, γ 1})) := by
      apply Subset.antisymm
      · rintro x ⟨hxV, hxfr⟩
        rw [← hsDb] at hxfr
        obtain ⟨y, hy, rfl⟩ := hxfr
        refine ⟨y, ⟨hy, fun hyβ => ?_⟩, rfl⟩
        have hyU : s y ∈ U := hEU (mem_image_of_mem s (hEDb.symm.subset hyβ.1).1)
        have hyA : s y ∈ s '' β' := hUiV ▸ ⟨hyU, hxV⟩
        obtain ⟨z, hz, hzy⟩ := hyA
        have hzy' : z = y := hsinj (hβ'D hz) (hDbD hy) hzy
        exact hyβ.2 (hββ'.subset ⟨hyβ.1, hzy' ▸ hz⟩)
      · rintro _ ⟨y, ⟨hy, hyn⟩, rfl⟩
        refine ⟨?_, hmemfr y hy⟩
        by_cases hye : y ∈ ({γ 0, γ 1} : Set F)
        · exact hVc.frontier_subset (hAV ⟨y, (hββ'.symm.subset hye).2, rfl⟩)
        · have hyβ : y ∉ β := fun h => hyn ⟨h, hye⟩
          have hsyU : s y ∉ U := by
            rintro hsyU
            rw [← hEeq] at hsyU
            obtain ⟨z, hz, hzy⟩ := hsyU
            have hzy' : z = y := hsinj (hED hz) (hDbD hy) hzy
            exact hyβ (hEDb.subset ⟨hzy' ▸ hz, hy⟩)
          have hsyΔ : s y ∈ Δ := hs.bijOn.mapsTo (hDbD hy)
          rw [← hUV] at hsyΔ
          exact hsyΔ.resolve_left hsyU
    have hV' := hV
    obtain ⟨v, hv⟩ := hV'
    have hgV : IsPLHomeomorphOn g V (g '' V) := hg.restrict hV.isPolyhedron hVΔ
    have hVA : closure (V \ s '' β') = V := by
      apply Subset.antisymm (closure_minimal sdiff_subset hVc)
      have hint : interior V ⊆ V \ s '' β' := fun x hx =>
        ⟨interior_subset hx, fun hxA => Set.disjoint_left.mp disjoint_interior_frontier hx
          (hAV hxA)⟩
      calc V = closure (interior V) := (IsPLBall.closure_interior (n := 1) hV).symm
        _ ⊆ closure (V \ s '' β') := closure_mono hint
    have hclosure : closure (D \ E) = g '' V := by
      apply Subset.antisymm
      · refine closure_minimal (fun x hx => ?_) ?_
        · have hsx : s x ∈ Δ := hs.bijOn.mapsTo hx.1
          rw [← hUV] at hsx
          have hsxU : s x ∉ U := by
            rw [← hEeq]
            rintro ⟨y, hy, hyx⟩
            exact hx.2 (hsinj (hED hy) hx.1 hyx ▸ hy)
          exact ⟨s x, hsx.resolve_left hsxU, hgs x hx.1⟩
        · exact (hV.isPolyhedron.isCompact.image_of_continuousOn
            (hg.isPiecewiseAffineOn.continuousOn.mono hVΔ)).isClosed
      · rw [← hVA]
        refine (ContinuousOn.image_closure (hg.isPiecewiseAffineOn.continuousOn.mono
          ((closure_minimal sdiff_subset hVc).trans hVΔ))).trans (closure_mono ?_)
        rintro _ ⟨y, ⟨hyV, hyA⟩, rfl⟩
        refine ⟨hg.bijOn.mapsTo (hVΔ hyV), fun hgy => ?_⟩
        have hsy : s (g y) ∈ s '' E := mem_image_of_mem s hgy
        rw [hsg y (hVΔ hyV), hEeq] at hsy
        exact hyA (hUiV ▸ ⟨hsy, hyV⟩)
    refine ⟨g ∘ v, by rw [hclosure]; exact hv.trans hgV, ?_, ?_, ?_⟩
    · rw [image_comp, IsPLHomeomorphOn.image_stdSimplexBoundary (n := 1) hv, hfrV, hVfr,
        image_union, hgsimg _ (sdiff_subset.trans hDbD), hgsimg β' hβ'D]
    · rw [hclosure, hEg, ← hginj.image_inter hVΔ hUΔ, inter_comm, hUiV, hgsimg β' hβ'D]
    · rw [hclosure, hEg, ← image_union, union_comm, hUV, hgΔ]
  rcases hside (s '' E) hsEball hsEΔ hdisj with hEU | hEV
  · exact key U V hU hV hUV hUiV hfV hAU hAV hEU
  · exact key V U hV hU (by rw [union_comm, hUV]) (by rw [inter_comm, hUiV]) hfU hAV hAU hEV

end DifferentialGeometry.Topology.PiecewiseLinear
