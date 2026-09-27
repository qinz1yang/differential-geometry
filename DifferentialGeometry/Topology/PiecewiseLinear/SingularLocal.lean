/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularPasting

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset
    {f : E → F} {P A B : Set E} (hf : ContinuousOn f P) (hAP : A ⊆ P) (hBP : B ⊆ P)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hfA : IsPLHomeomorphOn f A (f '' A)) (hfB : IsPLHomeomorphOn f B (f '' B))
    {y : F} (hy : y ∈ doublePointSet f P) (hcross : HasPLCrossingAt (f '' A) (f '' B) y)
    (hcover : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B) : HasPLDoubleCrossingAt f P y := by
  have hyAB := (mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hAB
    hfA.bijOn.injOn hfB.bijOn.injOn hcover.self_of_nhds).mp hy
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ := hyAB
  refine ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hAB, ?_, ?_, hfA, hfB, hcross, hcover⟩
  · apply mem_nhdsWithin_of_eventually_preimage_subset_union (hf a (hAP ha)) ha hB hAB
    rwa [hfa]
  · apply mem_nhdsWithin_of_eventually_preimage_subset_union (hf b (hBP hb)) hb hA hAB.symm
    rw [hfb]
    simpa only [union_comm] using hcover

theorem hasPLBoundaryDoubleCrossingAt_of_crossing_and_eventually_fiber_subset
    {f : E → F} {P A B : Set E} {M : Set F} (hf : ContinuousOn f P) (hAP : A ⊆ P) (hBP : B ⊆ P)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    (hfA : IsPLHomeomorphOn f A (f '' A)) (hfB : IsPLHomeomorphOn f B (f '' B))
    {y : F} (hy : y ∈ doublePointSet f P) (hcross : HasPLBoundaryCrossingAt M (f '' A) (f '' B) y)
    (hcover : ∀ᶠ z in 𝓝 y, P ∩ f ⁻¹' {z} ⊆ A ∪ B) : HasPLBoundaryDoubleCrossingAt f P M y := by
  have hyAB := (mem_doublePointSet_iff_mem_image_inter_of_injOn f hAP hBP hAB
    hfA.bijOn.injOn hfB.bijOn.injOn hcover.self_of_nhds).mp hy
  obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ := hyAB
  refine ⟨a, b, A, B, ha, hb, hfa, hfb, hAP, hBP, hAB, ?_, ?_, hfA, hfB, hcross, hcover⟩
  · apply mem_nhdsWithin_of_eventually_preimage_subset_union (hf a (hAP ha)) ha hB hAB
    rwa [hfa]
  · apply mem_nhdsWithin_of_eventually_preimage_subset_union (hf b (hBP hb)) hb hA hAB.symm
    rw [hfb]
    simpa only [union_comm] using hcover

open Classical in
theorem exists_small_piecewiseAffineOn_doublePointSet_crossing_neighborhood [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdim : Module.finrank ℝ F = 3)
    (f : E → F) (hf : IsPiecewiseAffineOn f K.space) (hloc : IsLocallyInjective (K.space.domRestrict
        f))
    (hcard : ∀ z, (K.space ∩ f ⁻¹' {z}).encard ≤ 2) {y : F} (hy : y ∈ doublePointSet f K.space)
    {V : Set F} (hV : V ∈ 𝓝 y) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : E → F) (W : Set F) (G : Geometry.SimplicialComplex ℝ F),
      IsPiecewiseAffineOn g K.space ∧ (∀ x, dist (g x) (f x) < ε) ∧
        IsLocallyInjective (K.space.domRestrict g) ∧ (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
          (∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) ∧ IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧
            G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
              (∀ z ∈ W, z ∈ doublePointSet g K.space ↔ z ∈ G.space) ∧
                ∀ z ∈ W ∩ doublePointSet g K.space, HasPLDoubleCrossingAt g K.space z := by
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  obtain ⟨P, Q, B₀, U, hPQ, hP, hQ, _, hB₀Q, hPB₀, hinjP, _, hU, hyU, hUV, hseam, hinjQ,
    _, _, _, _, _, _, hPa, hB₀b⟩ := exists_isPLBall_patches_at_fiber_pair K hK f hf.continuousOn
        hloc hcard
      ha hb hab hfa hfb (A₀ := univ) (B₀ := univ) Filter.univ_mem Filter.univ_mem hV
  obtain ⟨A, Q₁, B, U₁, _, hA, _, hB, _, hAB, hinjA, hinjB, hU₁, hyU₁, hU₁U, _, _,
    hinner, hmapsU, hAP, hBB₀, _, _, _, _⟩ := exists_isPLBall_patches_at_fiber_pair K hK f
        hf.continuousOn
      hloc hcard ha hb hab hfa hfb hPa hB₀b (hU.mem_nhds hyU)
  have hPK : P ⊆ K.space := hPQ ▸ subset_union_left
  have hQK : Q ⊆ K.space := hPQ ▸ subset_union_right
  have hAK : A ⊆ K.space := hAP.trans hPK
  have hBQ : B ⊆ Q := hBB₀.trans hB₀Q
  have hBK : B ⊆ K.space := hBQ.trans hQK
  have hrepresent : ∀ {C : Set E}, IsPLBall 2 C → InjOn f C → C ⊆ K.space →
      ∃ L : Geometry.SimplicialComplex ℝ F, L.faces.Finite ∧ L.space = f '' C ∧
        IsPLHomeomorphOn f C L.space ∧ IsCombinatorialManifoldWithBoundary 2 L := by
    intro C hC hinjC hCK
    obtain ⟨S, hSfinite, hSC⟩ := hC.isPolyhedron.exists_simplicialComplex
    have : Finite S.faces := hSfinite.to_subtype
    have hfS : IsPiecewiseAffineOn f S.space := by
      rw [hSC]
      exact hf.mono_of_isPolyhedron hC.isPolyhedron hCK
    have hinjS : InjOn f S.space := by rwa [hSC]
    obtain ⟨L, hLfinite, hLspace, hfL⟩ := exists_isPLHomeomorphOn_image S hfS hinjS
    have : Finite L.faces := hLfinite.to_subtype
    rw [hSC] at hfL hLspace
    exact ⟨L, hLfinite, hLspace, hfL, (hC.of_isPLHomeomorphOn
        hfL).isCombinatorialManifoldWithBoundary⟩
  obtain ⟨M, hMfinite, hMA, hfA, hMman⟩ := hrepresent hA hinjA hAK
  obtain ⟨N, hNfinite, hNB, hfB, hNman⟩ := hrepresent hB hinjB hBK
  have : Finite M.faces := hMfinite.to_subtype
  have : Finite N.faces := hNfinite.to_subtype
  have hMU : M.space ⊆ U := by
    rw [hMA]
    rintro z ⟨x, hx, rfl⟩
    exact hmapsU (Or.inl hx)
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp (hU₁.mem_nhds hyU₁)
  obtain ⟨h, G, hh, hclose, hfix, hGfinite, hGspace, hGman, hcross⟩ :=
    exists_small_homeomorph_generalPosition M N hMman hNman hdim hU hMU (lt_min hε hη)
  have hhinj : Function.Injective h := fun _ _ heq => hh.bijOn.injOn (mem_univ _) (mem_univ _) heq
  have hfPQ : IsPiecewiseAffineOn f (P ∪ Q) := by rwa [hPQ]
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict f) := by rwa [hPQ]
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ f ⁻¹' {z}).encard ≤ 2 := by rwa [hPQ]
  obtain ⟨g, hg, hgloc, hgcard, hgP, hgQ, hgOffP, hgfiber⟩ :=
    exists_piecewiseAffineOn_postcomp_on_polyhedron_of_locallyInjective hfPQ hP.isPolyhedron hQ
      hlocPQ hcardPQ hinjP hh.isPiecewiseAffineOn hhinj hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  have hgA : IsPLHomeomorphOn g A (h '' M.space) :=
    (hfA.trans (hh.restrict (isPolyhedron_space M) (subset_univ _))).congr (hgP.mono hAP)
  have hgB : IsPLHomeomorphOn g B N.space := hfB.congr (hgQ.mono hBQ)
  let j := Function.invFunOn h univ
  have hjright : ∀ z, h (j z) = z := fun z => hh.bijOn.invOn_invFunOn.2 (mem_univ z)
  have hjcont : Continuous j := continuousOn_univ.mp hh.isPiecewiseAffineOn_invFunOn.continuousOn
  let W := U₁ ∩ j ⁻¹' U₁
  have hW : IsOpen W := hU₁.inter (hU₁.preimage hjcont)
  have hyj : j y ∈ U₁ := by
    apply hηU
    rw [Metric.mem_ball]
    calc dist (j y) y = dist (h (j y)) (j y) := by rw [hjright, dist_comm]
      _ < η := (hclose (j y)).trans_le (min_le_right _ _)
  have hcover : ∀ z ∈ W, K.space ∩ g ⁻¹' {z} ⊆ A ∪ B := by
    intro z hz x hx
    by_cases hxP : x ∈ P
    · have hfx : f x = j z := by
        apply hhinj
        rw [hjright]
        exact (hgP hxP).symm.trans hx.2
      have hxAB := hinner (j z) (subset_closure (show j z ∈ U₁ from hz.2)) ⟨hx.1, hfx⟩
      rcases hxAB with hxA | hxB
      · exact Or.inl hxA
      · exact False.elim (Set.disjoint_left.mp hPB₀ hxP (hBB₀ hxB))
    · have hfx : f x = z := (hgOffP hxP).symm.trans hx.2
      have hxAB := hinner z (subset_closure hz.1) ⟨hx.1, hfx⟩
      exact Or.inr (hxAB.resolve_left (fun hxA => hxP (hAP hxA)))
  have hdouble : ∀ z ∈ W, z ∈ doublePointSet g K.space ↔ z ∈ G.space := by
    intro z hz
    rw [hGspace, ← hgA.image_eq, ← hgB.image_eq]
    exact mem_doublePointSet_iff_mem_image_inter_of_injOn g hAK hBK hAB
      hgA.bijOn.injOn hgB.bijOn.injOn (hcover z hz)
  refine ⟨g, W, G, hg, ?_, hgloc, hgcard, ?_, hW, ⟨hyU₁, hyj⟩, ?_, hGfinite, hGman, hdouble, ?_⟩
  · intro x
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact (hclose (f x)).trans_le (min_le_left _ _)
    · rw [hgOffP hxP, dist_self]
      exact hε
  · intro z hz
    exact hgfiber z (fun hzU => hz (hUV (subset_closure hzU)))
  · exact (closure_mono inter_subset_left).trans (hU₁U.trans (subset_closure.trans hUV))
  · intro z hz
    have hcrossz := hcross z (hGspace ▸ ((hdouble z hz.1).mp hz.2))
    rw [← hgA.image_eq, ← hgB.image_eq] at hcrossz
    apply hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset hg.continuousOn hAK hBK
      hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hAB
      (by rwa [hgA.image_eq]) (by rwa [hgB.image_eq]) hz.2 hcrossz
    filter_upwards [hW.mem_nhds hz.1] with w hw
    exact hcover w hw

end DifferentialGeometry.Topology.PiecewiseLinear
