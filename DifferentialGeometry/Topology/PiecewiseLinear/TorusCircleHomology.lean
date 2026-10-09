/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Homotopy
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.NonseparatingPolygonCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.SeparatingPolygonDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Homology

variable {Y : Type u} [TopologicalSpace Y]

theorem range_integralSingularHomologyMap_inclusion_eq_of_homotopic {S C₀ C₁ : Set Y}
    (h₀ : C₀ ⊆ S) (h₁ : C₁ ⊆ S) (f : C₀ ≃ₜ C₁)
    (hf : ContinuousMap.Homotopic (⟨inclusion h₀, continuous_inclusion h₀⟩ : C(C₀, S))
      ((⟨inclusion h₁, continuous_inclusion h₁⟩ : C(C₁, S)).comp ⟨f, f.continuous⟩)) :
    LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion h₀, continuous_inclusion h₀⟩ : C(C₀, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion h₁, continuous_inclusion h₁⟩ : C(C₁, S))) := by
  rw [integralSingularHomologyMap_homotopic 1 hf, integralSingularHomologyMap_comp]
  apply LinearMap.range_comp_of_range_eq_top
  rw [LinearMap.range_eq_top]
  intro y
  refine ⟨integralSingularHomologyMap 1 ⟨f.symm, f.symm.continuous⟩ y, ?_⟩
  rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
  have hid : (⟨f, f.continuous⟩ : C(C₀, C₁)).comp ⟨f.symm, f.symm.continuous⟩ =
      ContinuousMap.id _ := by
    ext x
    simp
  rw [hid, integralSingularHomologyMap_id, LinearMap.id_apply]

theorem range_integralSingularHomologyMap_eq_of_continuousOn [T2Space Y] {Z : Type*}
    [TopologicalSpace Z] {C : Set Z} (hC : IsCompact C) {S C₀ C₁ : Set Y} (h₀ : C₀ ⊆ S)
    (h₁ : C₁ ⊆ S) {F : Z × ℝ → Y} (hF : ContinuousOn F (C ×ˢ Icc 0 1))
    (hFS : MapsTo F (C ×ˢ Icc 0 1) S) (hinj₀ : InjOn (fun x => F (x, 0)) C)
    (hinj₁ : InjOn (fun x => F (x, 1)) C) (hC₀ : (fun x => F (x, 0)) '' C = C₀)
    (hC₁ : (fun x => F (x, 1)) '' C = C₁) :
    LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion h₀, continuous_inclusion h₀⟩ : C(C₀, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion h₁, continuous_inclusion h₁⟩ : C(C₁, S))) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : C, ((x : Z), t) ∈ C ×ˢ Icc (0 : ℝ) 1 :=
    fun t ht x => ⟨x.2, ht⟩
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  let g₀ : C → C₀ := fun x => ⟨F (x, 0), hC₀ ▸ mem_image_of_mem _ x.2⟩
  let g₁ : C → C₁ := fun x => ⟨F (x, 1), hC₁ ▸ mem_image_of_mem _ x.2⟩
  have hg₀c : Continuous g₀ :=
    (hF.comp_continuous (continuous_subtype_val.prodMk continuous_const) (hmem 0 h0)).subtype_mk _
  have hg₁c : Continuous g₁ :=
    (hF.comp_continuous (continuous_subtype_val.prodMk continuous_const) (hmem 1 h1)).subtype_mk _
  have hg₀ : Function.Bijective g₀ := by
    refine ⟨fun a b hab => Subtype.ext (hinj₀ a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨c, hc⟩
    rw [← hC₀] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact ⟨⟨x, hx⟩, rfl⟩
  have hg₁ : Function.Bijective g₁ := by
    refine ⟨fun a b hab => Subtype.ext (hinj₁ a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨c, hc⟩
    rw [← hC₁] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    exact ⟨⟨x, hx⟩, rfl⟩
  let p₀ : C ≃ₜ C₀ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g₀ hg₀) hg₀c
  let p₁ : C ≃ₜ C₁ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g₁ hg₁) hg₁c
  refine range_integralSingularHomologyMap_inclusion_eq_of_homotopic h₀ h₁ (p₀.symm.trans p₁)
    ⟨{ toFun := fun q => ⟨F (((p₀.symm q.2 : C) : Z), (q.1 : ℝ)), hFS (hmem _ q.1.2 _)⟩
       continuous_toFun := ?_
       map_zero_left := ?_
       map_one_left := ?_ }⟩
  · exact (hF.comp_continuous ((continuous_subtype_val.comp
      (p₀.symm.continuous.comp continuous_snd)).prodMk (continuous_subtype_val.comp continuous_fst))
      fun q => hmem _ q.1.2 _).subtype_mk _
  · intro c
    have hc : ((p₀ (p₀.symm c) : C₀) : Y) = c := congrArg Subtype.val (p₀.apply_symm_apply c)
    exact Subtype.ext hc
  · intro c
    rfl

theorem range_integralSingularHomologyMap_inclusion_eq_bot {S C D : Set Y} (hCS : C ⊆ S)
    (hCD : C ⊆ D) (hDS : D ⊆ S) (hD : Subsingleton (integralSingularHomology 1 D)) :
    LinearMap.range (integralSingularHomologyMap 1
      (⟨inclusion hCS, continuous_inclusion hCS⟩ : C(C, S))) = ⊥ := by
  rw [LinearMap.range_eq_bot]
  have hcomp : (⟨inclusion hCS, continuous_inclusion hCS⟩ : C(C, S)) =
      (⟨inclusion hDS, continuous_inclusion hDS⟩ : C(D, S)).comp
        ⟨inclusion hCD, continuous_inclusion hCD⟩ := rfl
  rw [hcomp, integralSingularHomologyMap_comp]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, Subsingleton.elim (integralSingularHomologyMap 1
    (⟨inclusion hCD, continuous_inclusion hCD⟩ : C(C, D)) x) 0, map_zero, LinearMap.zero_apply]

theorem subsingleton_integralSingularHomology_image_of_convex [T2Space Y] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Set F} (hC : Convex ℝ C) (hCc : IsCompact C)
    (hne : C.Nonempty) {f : F → Y} (hf : ContinuousOn f C) (hfi : InjOn f C) :
    Subsingleton (integralSingularHomology 1 (f '' C)) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hCc
  let g : C → f '' C := fun x => ⟨f x, mem_image_of_mem f x.2⟩
  have hgc : Continuous g :=
    (hf.comp_continuous continuous_subtype_val fun x => x.2).subtype_mk _
  have hg : Function.Bijective g := by
    refine ⟨fun a b hab => Subtype.ext (hfi a.2 b.2 (congrArg Subtype.val hab)), ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : C ≃ₜ f '' C := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg) hgc
  have : ContractibleSpace C := hC.contractibleSpace hne
  have : ContractibleSpace (f '' C) := e.symm.contractibleSpace
  exact integralSingularHomology_subsingleton_of_contractible 1 one_ne_zero _

end Homology

section Torus

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] {φ : E3 → Y} {S : Set Y}

theorem IsPLTorus.range_integralSingularHomologyMap_eq_bot_of_not_isPreconnected {Θ G : Set E3}
    (hΘ : IsPLTorus Θ) (hG : IsPLSphere 1 G) (hGΘ : G ⊆ Θ) (hGsep : ¬ IsPreconnected (Θ \ G))
    (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ) (hS : φ '' Θ ⊆ S) :
    LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hGΘ).trans hS), continuous_inclusion _⟩ : C(φ '' G, S))) =
      ⊥ := by
  obtain ⟨Δ, r, hr, hΔΘ, hGr⟩ :=
    hΘ.exists_isPLHomeomorphOn_disk_of_not_isPreconnected_sdiff hG hGΘ hGsep
  have hmaps : ∀ x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3), r x ∈ Θ := fun x hx => hΔΘ (hr.bijOn.mapsTo hx)
  have himg : (fun x => φ (r x)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) = φ '' Δ := by
    rw [← hr.image_eq, image_image]
  have hsub := subsingleton_integralSingularHomology_image_of_convex (f := fun x => φ (r x))
    (Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)) (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3))
    ⟨_, Convexity.StdSimplex.single_mem_coordinateSet ℝ (0 : Fin 3)⟩ (hφ.comp hr.isPiecewiseAffineOn.continuousOn hmaps)
    (fun a ha b hb hab => hr.bijOn.injOn ha hb (hφi (hmaps a ha) (hmaps b hb) hab))
  rw [himg] at hsub
  have hGΔ : G ⊆ Δ := by
    rw [hGr, ← hr.image_eq]
    exact image_mono fun x hx => hx.1
  exact range_integralSingularHomologyMap_inclusion_eq_bot _ (image_mono hGΔ)
    ((image_mono hΔΘ).trans hS) hsub

open Classical in
theorem IsPLTorus.range_integralSingularHomologyMap_eq_of_disjoint {Θ K G : Set E3}
    (hΘ : IsPLTorus Θ) (hK : IsPLSphere 1 K) (hKΘ : K ⊆ Θ) (hG : IsPLSphere 1 G)
    (hGΘ : G ⊆ Θ) (hGK : Disjoint G K) (hKsep : IsPreconnected (Θ \ K))
    (hGsep : IsPreconnected (Θ \ G)) (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ)
    (hS : φ '' Θ ⊆ S) :
    LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hKΘ).trans hS), continuous_inclusion _⟩ : C(φ '' K, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hGΘ).trans hS), continuous_inclusion _⟩ : C(φ '' G, S))) := by
  obtain ⟨L, hLfin, hL, hLc, hLT⟩ := hΘ.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hLo := hL.isOrientable_euclidean_three L hLc
  have hβ := hΘ.bettiOne_le_two
  rw [← hLT] at hβ
  have hχ := hL.eulerChar_eq_two_sub_bettiOne_of_isOrientable L hLc hLo
  have hGL : G ⊆ L.space := by
    rw [hLT]
    exact hGΘ
  have hnonsep' : IsPreconnected (L.space \ G) := by
    rw [hLT]
    exact hGsep
  have hU : L.space \ K ∈ 𝓝ˢ[L.space] G :=
    mem_nhdsSetWithin.mpr ⟨Kᶜ, hK.isPolyhedron.isClosed.isOpen_compl,
      fun x hx => disjoint_left.mp hGK hx, fun x hx => ⟨hx.2, hx.1⟩⟩
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, hWL, hWU, -, hρ, hzero, -, -, hRbd, -, hcover,
      hGm, hGp, hdis⟩ := hL.exists_connected_annulus_complement L hLo hG hGL hnonsep' hU
  let _ : Finite R.faces := hRfin.to_subtype
  have hRbd' := hRbd.trans (show ρ '' (G ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (G ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G ×ˢ {(1 : ℝ)}) by
    rw [← singleton_union, prod_union, image_union])
  have hRχ0 : eulerChar R = 0 := by
    have hle := hR.eulerChar_nonpos_of_boundary_eq_union R hRc hGm hGp hdis hRbd'
    omega
  obtain ⟨h, hh, hh0, hh1⟩ :=
    hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc hRχ0 hGm hGp hdis hRbd'
  have hρW : ρ '' (G ×ˢ Icc (-1 : ℝ) 1) = W := hρ.image_eq
  have hGIcc : ∀ t ∈ ({(-1 : ℝ), 1} : Set ℝ), t ∈ Icc (-1 : ℝ) 1 := by
    rintro t (rfl | rfl)
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
  have hbdW : ρ '' (G ×ˢ {(-1 : ℝ)}) ∪ ρ '' (G ×ˢ {(1 : ℝ)}) ⊆ W := by
    rw [← hρW]
    rintro _ (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨y, ⟨hy.1, hGIcc _ (Or.inl hy.2)⟩, rfl⟩
    · exact ⟨y, ⟨hy.1, hGIcc _ (Or.inr hy.2)⟩, rfl⟩
  have hKW : Disjoint K W := by
    rw [disjoint_left]
    intro x hxK hxW
    exact (hWU hxW).2 hxK
  have hKL : K ⊆ L.space := by
    rw [hLT]
    exact hKΘ
  have hKR : K ⊆ R.space := by
    intro x hx
    have hxL := hKL hx
    rw [← hcover] at hxL
    exact hxL.resolve_left (disjoint_left.mp hKW hx)
  have hRΘ : R.space ⊆ Θ := by
    intro x hx
    have hxL : x ∈ L.space := by
      rw [← hcover]
      exact Or.inr hx
    rwa [hLT] at hxL
  have hWΘ : W ⊆ Θ := by
    intro x hx
    have hxL : x ∈ L.space := by
      rw [← hcover]
      exact Or.inl hx
    rwa [hLT] at hxL
  have hGmΘ : ρ '' (G ×ˢ {(-1 : ℝ)}) ⊆ Θ := fun x hx => hWΘ (hbdW (Or.inl hx))
  have hhs : IsPLHomeomorphOn (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1))
      R.space (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := hh.symm
  have hK' : IsPLSphere 1 (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) :=
    hK.of_isPLHomeomorphOn (hhs.restrict hK.isPolyhedron hKR)
  have hhK' : h '' (Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K) = K :=
    LeftInvOn.image_image (hh.bijOn.invOn_invFunOn.2.mono hKR)
  have hK'A : Function.invFunOn h (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) '' K ⊆
      stdSimplexBoundary 2 ×ˢ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hyA := hhs.bijOn.mapsTo (hKR hx)
    have hhy := hh.bijOn.invOn_invFunOn.2 (hKR hx)
    refine ⟨hyA.1, lt_of_le_of_ne hyA.2.1 fun h0 => ?_, lt_of_le_of_ne hyA.2.2 fun h1 => ?_⟩
    · have hx0 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ)) := ⟨_, ⟨hyA.1, h0.symm⟩, hhy⟩
      rw [hh0] at hx0
      exact disjoint_left.mp hKW hx (hbdW (Or.inl hx0))
    · have hx1 : x ∈ h '' (stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ)) := ⟨_, ⟨hyA.1, h1⟩, hhy⟩
      rw [hh1] at hx1
      exact disjoint_left.mp hKW hx (hbdW (Or.inr hx1))
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hBcpt : IsCompact (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact (isPolyhedron_space _).isCompact
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hhΘ : ∀ p ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1, h p ∈ Θ :=
    fun p hp => hRΘ (hh.bijOn.mapsTo hp)
  have hGmG : LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hGΘ).trans hS), continuous_inclusion _⟩ : C(φ '' G, S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hGmΘ).trans hS), continuous_inclusion _⟩ :
          C(φ '' (ρ '' (G ×ˢ {(-1 : ℝ)})), S))) := by
    have hmemρ : ∀ p ∈ G ×ˢ Icc (0 : ℝ) 1, (p.1, -p.2) ∈ G ×ˢ Icc (-1 : ℝ) 1 := by
      rintro p ⟨hp1, hp2, hp3⟩
      exact ⟨hp1, by linarith, by linarith⟩
    have hρΘ : ∀ p ∈ G ×ˢ Icc (0 : ℝ) 1, ρ (p.1, -p.2) ∈ Θ :=
      fun p hp => hWΘ (hρ.bijOn.mapsTo (hmemρ p hp))
    have hm1 : ∀ x ∈ G, (x, -(1 : ℝ)) ∈ G ×ˢ Icc (-1 : ℝ) 1 :=
      fun x hx => ⟨hx, le_rfl, by norm_num⟩
    have hi0 : InjOn (fun x => φ (ρ (x, -(0 : ℝ)))) G := by
      intro a ha b hb hab
      simp only [neg_zero, hzero a ha, hzero b hb] at hab
      exact hφi (hGΘ ha) (hGΘ hb) hab
    have hi1 : InjOn (fun x => φ (ρ (x, -(1 : ℝ)))) G := by
      intro a ha b hb hab
      have hab' := hφi (hρΘ (a, 1) ⟨ha, h1mem⟩) (hρΘ (b, 1) ⟨hb, h1mem⟩) hab
      exact congrArg Prod.fst (hρ.bijOn.injOn (hm1 a ha) (hm1 b hb) hab')
    have hc0 : (fun x => φ (ρ (x, -(0 : ℝ)))) '' G = φ '' G :=
      image_congr fun x hx => by simp only [neg_zero, hzero x hx]
    have hc1 : (fun x => φ (ρ (x, -(1 : ℝ)))) '' G = φ '' (ρ '' (G ×ˢ {(-1 : ℝ)})) := by
      rw [prod_singleton, image_image, image_image]
    exact range_integralSingularHomologyMap_eq_of_continuousOn
      (F := fun p : E3 × ℝ => φ (ρ (p.1, -p.2))) hG.isPolyhedron.isCompact _ _
      (hφ.comp (hρ.isPiecewiseAffineOn.continuousOn.comp
        (continuous_fst.prodMk continuous_snd.neg).continuousOn hmemρ) hρΘ)
      (fun p hp => hS (mem_image_of_mem φ (hρΘ p hp))) hi0 hi1 hc0 hc1
  have hKGm : LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hGmΘ).trans hS), continuous_inclusion _⟩ :
          C(φ '' (ρ '' (G ×ˢ {(-1 : ℝ)})), S))) =
      LinearMap.range (integralSingularHomologyMap 1
        (⟨inclusion ((image_mono hKΘ).trans hS), continuous_inclusion _⟩ : C(φ '' K, S))) := by
    rcases hK'.exists_disk_or_annulus_of_subset_prism_lateral hK'A with
      ⟨D, r, hr, hDA, hrb⟩ | ⟨ψ, hψ, hψA, hψ0, hψ1⟩
    · exfalso
      have hhD : IsPLHomeomorphOn h D (h '' D) := hh.restrict (IsPLBall.isPolyhedron ⟨r, hr⟩) hDA
      have hrD := hr.trans hhD
      have hΔΘ : h '' D ⊆ Θ := by
        rintro _ ⟨y, hy, rfl⟩
        exact hhΘ y (hDA hy)
      have hΔL : h '' D ⊆ L.space := by
        rw [hLT]
        exact hΔΘ
      have hsep : h '' D ∩ closure (Θ \ h '' D) = K := by
        have h' : h '' D ∩ closure (L.space \ h '' D) = (h ∘ r) '' stdSimplexBoundary 2 :=
          hL.inter_closure_sdiff_eq_image_stdSimplexBoundary (n := 1) L hrD hΔL
        rw [image_comp, hrb, hhK', hLT] at h'
        exact h'
      have hne : (h '' D \ (h ∘ r) '' stdSimplexBoundary 2).Nonempty :=
        hrD.isConnected_sdiff_image_stdSimplexBoundary.nonempty
      rw [image_comp, hrb, hhK'] at hne
      obtain ⟨z, hzD, hzK⟩ := hne
      have hΔc : IsClosed (h '' D) := (IsPLBall.isPolyhedron ⟨_, hrD⟩).isClosed
      have hKΔ : K ⊆ h '' D := by
        rw [← hsep]
        exact inter_subset_left
      have hΘΔ : (Θ \ h '' D).Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        rw [hemp, closure_empty, inter_empty] at hsep
        exact hK.nonempty.ne_empty hsep.symm
      obtain ⟨y, hyΘ, hyD⟩ := hΘΔ
      have hcov : Θ \ K ⊆ (closure (Θ \ h '' D))ᶜ ∪ (h '' D)ᶜ := by
        intro x hx
        by_cases hxD : x ∈ h '' D
        · refine Or.inl fun hcl => hx.2 ?_
          rw [← hsep]
          exact ⟨hxD, hcl⟩
        · exact Or.inr hxD
      obtain ⟨x, hx, hxu, hxv⟩ := hKsep _ _ isClosed_closure.isOpen_compl hΔc.isOpen_compl hcov
        ⟨z, ⟨hΔΘ hzD, hzK⟩, fun hcl => hzK (by rw [← hsep]; exact ⟨hzD, hcl⟩)⟩
        ⟨y, ⟨hyΘ, fun hyK => hyD (hKΔ hyK)⟩, hyD⟩
      exact hxu (subset_closure ⟨hx.1, hxv⟩)
    · have hi0 : InjOn (fun x => φ (h (ψ (x, 0)))) (stdSimplexBoundary 2) := by
        intro a ha b hb hab
        have hma : (a, (0 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨ha, h0mem⟩
        have hmb : (b, (0 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨hb, h0mem⟩
        simp only [hψ0 a ha, hψ0 b hb] at hab
        exact congrArg Prod.fst (hh.bijOn.injOn hma hmb (hφi (hhΘ _ hma) (hhΘ _ hmb) hab))
      have hi1 : InjOn (fun x => φ (h (ψ (x, 1)))) (stdSimplexBoundary 2) := by
        intro a ha b hb hab
        have hma : (a, (1 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨ha, h1mem⟩
        have hmb : (b, (1 : ℝ)) ∈ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := ⟨hb, h1mem⟩
        have hψa := hψA ⟨_, hma, rfl⟩
        have hψb := hψA ⟨_, hmb, rfl⟩
        have hab' := hh.bijOn.injOn hψa hψb (hφi (hhΘ _ hψa) (hhΘ _ hψb) hab)
        exact congrArg Prod.fst (hψ.bijOn.injOn hma hmb hab')
      have hc0 : (fun x => φ (h (ψ (x, 0)))) '' stdSimplexBoundary 2 =
          φ '' (ρ '' (G ×ˢ {(-1 : ℝ)})) := by
        rw [← hh0, prod_singleton, image_image, image_image]
        exact image_congr fun x hx => by rw [hψ0 x hx]
      have hc1 : (fun x => φ (h (ψ (x, 1)))) '' stdSimplexBoundary 2 = φ '' K := by
        rw [← hhK', ← hψ1, prod_singleton, image_image, image_image, image_image]
      exact range_integralSingularHomologyMap_eq_of_continuousOn
        (F := fun p => φ (h (ψ p))) hBcpt _ _
        (hφ.comp (hh.isPiecewiseAffineOn.continuousOn.comp hψ.isPiecewiseAffineOn.continuousOn
          fun p hp => hψA ⟨p, hp, rfl⟩) fun p hp => hhΘ _ (hψA ⟨p, hp, rfl⟩))
        (fun p hp => hS (mem_image_of_mem φ (hhΘ _ (hψA ⟨p, hp, rfl⟩)))) hi0 hi1 hc0 hc1
  exact (hGmG.trans hKGm).symm

theorem IsPLTorus.carriesFirstHomologyOnto_image_of_disjoint {Θ K G : Set E3}
    (hΘ : IsPLTorus Θ) (hK : IsPLSphere 1 K) (hKΘ : K ⊆ Θ) (hG : IsPLSphere 1 G)
    (hGΘ : G ⊆ Θ) (hGK : Disjoint G K) (hKsep : IsPreconnected (Θ \ K))
    (hGsep : IsPreconnected (Θ \ G)) (hφ : ContinuousOn φ Θ) (hφi : InjOn φ Θ)
    (hS : φ '' Θ ⊆ S) (hKc : CarriesFirstHomologyOnto (φ '' K) S) :
    CarriesFirstHomologyOnto (φ '' G) S := by
  refine ⟨(image_mono hGΘ).trans hS, fun hsub => ?_⟩
  rw [← LinearMap.range_eq_top]
  have hKr := LinearMap.range_eq_top.mpr (hKc.2 ((image_mono hKΘ).trans hS))
  rw [hΘ.range_integralSingularHomologyMap_eq_of_disjoint hK hKΘ hG hGΘ hGK hKsep hGsep hφ hφi
    hS] at hKr
  exact hKr

end Torus

end DifferentialGeometry.Topology.PiecewiseLinear
