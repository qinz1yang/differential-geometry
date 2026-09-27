/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossHalfSpaceNormalForm
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchTube
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.InteriorTwoSided
import DifferentialGeometry.Topology.PiecewiseLinear.TransversePlaneNormalForm

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem eventually_mem_frontier_iff_of_halfPlane_sheet {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {f : EuclideanSpace ℝ (Fin 2) → F}
    {P C : Set (EuclideanSpace ℝ (Fin 2))} {a : EuclideanSpace ℝ (Fin 2)} (haC : a ∈ C)
    (hCP : C ⊆ P) (hCn : C ∈ 𝓝[P] a) (hfC : IsPLHomeomorphOn f C (f '' C)) {U V : Set F}
    {h : F → F} (hU : IsOpen U) (hV : IsOpen V) (hh : IsPLHomeomorphOn h U V)
    {R : Submodule ℝ F} (hR : Module.finrank ℝ R = 2) {ℓ : F →ₗ[ℝ] ℝ} {u : F} (huR : u ∈ R)
    (hℓu : ℓ u ≠ 0)
    (hlocal : ∀ᶠ z in 𝓝 (f a), z ∈ U ∧ (z ∈ f '' C ↔ h z ∈ R ∧ 0 ≤ ℓ (h z))) :
    ∀ᶠ z in 𝓝 (f a), ∀ x ∈ C, f x = z → (x ∈ frontier P ↔ ℓ (h z) = 0) := by
  obtain ⟨N, hNsub, hN, hfaN⟩ := _root_.mem_nhds_iff.mp hlocal
  obtain ⟨O, hO, haO, hOP⟩ := mem_nhdsWithin.mp hCn
  set finv := Function.invFunOn f C with hfinvdef
  have hfinv : ∀ x ∈ C, finv (f x) = x := fun x hx => hfC.bijOn.invOn_invFunOn.1 hx
  have hfinvc : ContinuousOn finv (f '' C) := hfC.isPiecewiseAffineOn_invFunOn.continuousOn
  have hpre : finv ⁻¹' O ∈ 𝓝[f '' C] (f a) :=
    (hfinvc (f a) ⟨a, haC, rfl⟩).preimage_mem_nhdsWithin
      (by rw [hfinv a haC]; exact hO.mem_nhds haO)
  obtain ⟨N₂, hN₂, hN₂sub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
  filter_upwards [hN.mem_nhds hfaN, hN₂] with z hzN hzN₂
  intro x hxC hfx
  subst hfx
  have hxO : x ∈ O := by
    have hmem := hN₂sub ⟨hzN₂, x, hxC, rfl⟩
    rwa [mem_preimage, hfinv x hxC] at hmem
  have hCnx : C ∈ 𝓝[P] x := mem_nhdsWithin.mpr ⟨O, hO, hxO, hOP⟩
  obtain ⟨hxU, hxloc⟩ := hNsub hzN
  have hsheet := hxloc.mp ⟨x, hxC, rfl⟩
  constructor
  · intro hfr
    by_contra hne
    have hpos : 0 < ℓ (h (f x)) := lt_of_le_of_ne hsheet.2 (Ne.symm hne)
    let e₂ : R ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
      ContinuousLinearEquiv.ofFinrankEq (by simpa using hR)
    set hinv := Function.invFunOn h U with hhinvdef
    have hhinv : ∀ w ∈ U, hinv (h w) = w := fun w hw => hh.bijOn.invOn_invFunOn.1 hw
    have hhh : ∀ r ∈ V, h (hinv r) = r := fun r hr => hh.bijOn.invOn_invFunOn.2 hr
    have hhinvc : ContinuousOn hinv V := hh.isPiecewiseAffineOn_invFunOn.continuousOn
    let ι : EuclideanSpace ℝ (Fin 2) → F := fun w => (e₂.symm w : F)
    have hιc : Continuous ι := continuous_subtype_val.comp e₂.symm.continuous
    have hWopen : IsOpen {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)} := by
      have h1 : IsOpen (V ∩ hinv ⁻¹' N) := hhinvc.isOpen_inter_preimage hV hN
      have h2 : IsOpen {r : F | 0 < ℓ r} :=
        isOpen_lt continuous_const (LinearMap.continuous_of_finiteDimensional ℓ)
      have h3 := (h1.inter h2).preimage hιc
      convert h3 using 1
      ext w
      simp only [mem_ofPred_eq, mem_preimage, mem_inter_iff]
      tauto
    have hmaps : ∀ w ∈ {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)}, hinv (ι w) ∈ f '' C := by
      intro w hw
      refine ((hNsub hw.2.1).2).mpr ⟨?_, ?_⟩
      · rw [hhh _ hw.1]
        exact (e₂.symm w).2
      · rw [hhh _ hw.1]
        exact hw.2.2.le
    have hΦc : ContinuousOn (fun w => finv (hinv (ι w)))
        {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)} :=
      hfinvc.comp (hhinvc.comp hιc.continuousOn fun w hw => hw.1) hmaps
    have hΦi : InjOn (fun w => finv (hinv (ι w))) {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)} := by
      intro w hw w' hw' hww
      have h1 := hfC.symm.bijOn.injOn (hmaps w hw) (hmaps w' hw') hww
      have h2 := hh.symm.bijOn.injOn hw.1 hw'.1 h1
      exact e₂.symm.injective (Subtype.ext h2)
    have hΦopen := DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hWopen hΦc hΦi
    have hw₀ : e₂ ⟨h (f x), hsheet.1⟩ ∈ {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)} := by
      simp only [mem_ofPred_eq, ι, ContinuousLinearEquiv.symm_apply_apply]
      refine ⟨hh.bijOn.mapsTo hxU, ?_, hpos⟩
      rw [hhinv _ hxU]
      exact hzN
    have hΦw₀ : (fun w => finv (hinv (ι w))) (e₂ ⟨h (f x), hsheet.1⟩) = x := by
      simp only [ι, ContinuousLinearEquiv.symm_apply_apply]
      rw [hhinv _ hxU, hfinv x hxC]
    have hsub : (fun w => finv (hinv (ι w))) ''
        {w | ι w ∈ V ∧ hinv (ι w) ∈ N ∧ 0 < ℓ (ι w)} ⊆ P := by
      rintro _ ⟨w, hw, rfl⟩
      exact hCP (hfC.symm.bijOn.mapsTo (hmaps w hw))
    have hxint : x ∈ interior P :=
      interior_maximal hsub hΦopen (hΦw₀ ▸ mem_image_of_mem _ hw₀)
    exact (mem_frontier_iff_notMem_interior (hCP hxC)).mp hfr hxint
  · intro hzero
    refine mem_frontier_of_halfPlane_sheet_model (by simp) hxC hCP hCnx rfl hfC
      (V := (fun w => w + -h (f x)) '' V) (h := fun w => h w + -h (f x)) hU hxU ?_
      (by simp) hR huR hℓu ?_
    · exact hh.trans ((isPLHomeomorphOn_add_const (-h (f x))).restrict_isOpen hV (subset_univ _)
        (isOpenMap_add_right _ V hV))
    · filter_upwards [hN.mem_nhds hzN] with w hw
      rw [(hNsub hw).2, R.add_mem_iff_left (R.neg_mem hsheet.1), map_add, map_neg, hzero,
        neg_zero, add_zero]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem exists_boundaryCrossing_straighteningChart (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}, NormalSingularCellData D BdM B →
      ∀ {y : L.space}, y ∈ doublePointSet D D.domain → y ∈ BdM →
        ∃ (e : OpenPartialHomeomorph L.space (EuclideanSpace ℝ (Fin 3)))
          (k : EuclideanSpace ℝ (Fin 3) → (ℝ × ℝ) × ℝ) (U₀ : Set (EuclideanSpace ℝ (Fin 3))),
          e ∈ (plGroupoid 3).maximalAtlas L.space ∧ y ∈ e.source ∧ IsOpen U₀ ∧ e y ∈ U₀ ∧
            U₀ ⊆ e.target ∧ IsOpen (k '' U₀) ∧ IsPLHomeomorphOn k U₀ (k '' U₀) ∧ k (e y) = 0 ∧
            ∀ z ∈ U₀, (e.symm z ∈ D '' D.domain ↔ k z ∈ crossPlanes ∧ 0 ≤ (k z).2) ∧
              (e.symm z ∈ doublePointSet D D.domain ↔ (k z).1 = 0 ∧ 0 ≤ (k z).2) ∧
              (k z ∈ crossPlanes → 0 ≤ (k z).2 → (e.symm z ∈ BdM ↔ (k z).2 = 0)) := by
  let _ := combinatorialChartedSpace L hL
  have _ : HasGroupoid L.space (plGroupoid 3) := combinatorialChartedSpace_hasGroupoid L hL
  intro D BdM B hD y hy hyBd
  obtain ⟨e, he, hye, N, hcross⟩ := hD.exists_boundary_crossing_chart ⟨hy, hyBd⟩
  have hemax : e ∈ (plGroupoid 3).maximalAtlas L.space :=
    StructureGroupoid.subset_maximalAtlas _ he
  obtain ⟨a, b, A, B', haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAn, hBn, hfA, hfB, hbc,
    hfiber⟩ := hcross
  obtain ⟨U, V₁, h, Lq, hU, hV₁, heyU, hh, hh0, hnear⟩ := hbc.exists_linearEquiv_normalForm
  let ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ := (LinearMap.fst ℝ ℝ (ℝ × ℝ)).comp Lq.toLinearMap
  let πA : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).comp Lq.toLinearMap
  let πB : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
    ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).comp Lq.toLinearMap
  have hker : ∀ π : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ, Function.Surjective π →
      Module.finrank ℝ (LinearMap.ker π) = 2 := by
    intro π hπ
    have h := LinearMap.finrank_range_add_finrank_ker π
    rw [LinearMap.range_eq_top.mpr hπ, finrank_top, Module.finrank_self,
      finrank_euclideanSpace_fin] at h
    omega
  have hπA : Function.Surjective πA := fun r => ⟨Lq.symm (0, 0, r), by simp [πA]⟩
  have hπB : Function.Surjective πB := fun r => ⟨Lq.symm (0, r, 0), by simp [πB]⟩
  have huA : Lq.symm (1, 0, 0) ∈ LinearMap.ker πA := by simp [πA]
  have huB : Lq.symm (1, 0, 0) ∈ LinearMap.ker πB := by simp [πB]
  have hℓu : ℓ (Lq.symm (1, 0, 0)) ≠ 0 := by simp [ℓ]
  have hlocA : ∀ᶠ z in 𝓝 ((e ∘ D) a), z ∈ U ∧
      (z ∈ (e ∘ D) '' A ↔ h z ∈ LinearMap.ker πA ∧ 0 ≤ ℓ (h z)) := by
    rw [hfa]
    filter_upwards [hnear, hU.mem_nhds heyU] with z hz hzU
    exact ⟨hzU, hz.2.1⟩
  have hlocB : ∀ᶠ z in 𝓝 ((e ∘ D) b), z ∈ U ∧
      (z ∈ (e ∘ D) '' B' ↔ h z ∈ LinearMap.ker πB ∧ 0 ≤ ℓ (h z)) := by
    rw [hfb]
    filter_upwards [hnear, hU.mem_nhds heyU] with z hz hzU
    exact ⟨hzU, hz.2.2.1⟩
  have hsheetA := eventually_mem_frontier_iff_of_halfPlane_sheet haA hAP hAn hfA hU hV₁ hh
    (hker πA hπA) huA hℓu hlocA
  have hsheetB := eventually_mem_frontier_iff_of_halfPlane_sheet hbB hBP hBn hfB hU hV₁ hh
    (hker πB hπB) huB hℓu hlocB
  rw [hfa] at hsheetA
  rw [hfb] at hsheetB
  have hev : ∀ᶠ z in 𝓝 (e y),
      ((z ∈ (e ∘ D) '' A ↔ (Lq (h z)).2.2 = 0 ∧ 0 ≤ (Lq (h z)).1) ∧
        (z ∈ (e ∘ D) '' B' ↔ (Lq (h z)).2.1 = 0 ∧ 0 ≤ (Lq (h z)).1)) ∧
      (D.domain ∩ D ⁻¹' e.source) ∩ (e ∘ D) ⁻¹' {z} ⊆ A ∪ B' ∧ z ∈ U ∧ z ∈ e.target ∧
      (∀ x ∈ A, (e ∘ D) x = z → (x ∈ frontier (D.domain ∩ D ⁻¹' e.source) ↔ ℓ (h z) = 0)) ∧
      (∀ x ∈ B', (e ∘ D) x = z → (x ∈ frontier (D.domain ∩ D ⁻¹' e.source) ↔ ℓ (h z) = 0)) := by
    filter_upwards [hnear, hfiber, hU.mem_nhds heyU, e.open_target.mem_nhds (e.map_source hye),
      hsheetA, hsheetB] with z h1 h2 h3 h4 h5 h6
    exact ⟨⟨h1.2.1, h1.2.2.1⟩, h2, h3, h4, h5, h6⟩
  obtain ⟨U₀, hU₀sub, hU₀o, heyU₀⟩ := _root_.mem_nhds_iff.mp hev
  have hU₀U : U₀ ⊆ U := fun z hz => (hU₀sub hz).2.2.1
  have hU₀t : U₀ ⊆ e.target := fun z hz => (hU₀sub hz).2.2.2.1
  have hhU₀o : IsOpen (h '' U₀) := hh.isOpen_image_of_isOpen hV₁ hU₀o hU₀U
  have hhU₀ : IsPLHomeomorphOn h U₀ (h '' U₀) := hh.restrict_isOpen hU₀o hU₀U hhU₀o
  obtain ⟨hLo, hLq⟩ := isPLHomeomorphOn_linearEquiv_image Lq hhU₀o
  obtain ⟨hσo, hσ⟩ := isPLHomeomorphOn_linearEquiv_image crossNormalFormEquiv hLo
  have hk : IsPLHomeomorphOn (fun z => crossNormalFormEquiv (Lq (h z))) U₀
      ((fun x => crossNormalFormEquiv x) '' ((fun x => Lq x) '' (h '' U₀))) :=
    (hhU₀.trans hLq).trans hσ
  have himg : (fun z => crossNormalFormEquiv (Lq (h z))) '' U₀ =
      (fun x => crossNormalFormEquiv x) '' ((fun x => Lq x) '' (h '' U₀)) := by
    rw [image_image, image_image]
  have hZz : ∀ z ∈ U₀, e.symm z ∈ D '' D.domain ↔ z ∈ (e ∘ D) '' A ∨ z ∈ (e ∘ D) '' B' := by
    intro z hz
    have hzt := hU₀t hz
    constructor
    · rintro ⟨x, hx, hxz⟩
      have hxP : x ∈ D.domain ∩ D ⁻¹' e.source := ⟨hx, by
        change D x ∈ e.source
        rw [hxz]
        exact e.map_target hzt⟩
      have hfx : (e ∘ D) x = z := by
        change e (D x) = z
        rw [hxz, e.right_inv hzt]
      rcases (hU₀sub hz).2.1 ⟨hxP, hfx⟩ with hxA | hxB
      · exact Or.inl ⟨x, hxA, hfx⟩
      · exact Or.inr ⟨x, hxB, hfx⟩
    · rintro (⟨x, hx, hxz⟩ | ⟨x, hx, hxz⟩)
      · have hxP := hAP hx
        refine ⟨x, hxP.1, ?_⟩
        rw [← hxz]
        exact (e.left_inv hxP.2).symm
      · have hxP := hBP hx
        refine ⟨x, hxP.1, ?_⟩
        rw [← hxz]
        exact (e.left_inv hxP.2).symm
  have hDz : ∀ z ∈ U₀, e.symm z ∈ doublePointSet D D.domain ↔
      z ∈ (e ∘ D) '' A ∧ z ∈ (e ∘ D) '' B' := by
    intro z hz
    have hzt := hU₀t hz
    rw [← mem_inter_iff, ← mem_doublePointSet_iff_mem_image_inter_of_injOn (e ∘ D) hAP hBP hdisj
      hfA.bijOn.injOn hfB.bijOn.injOn (hU₀sub hz).2.1,
      doublePointSet_comp_openPartialHomeomorph D D.domain e]
    constructor
    · intro h1
      exact ⟨e.symm z, ⟨h1, e.map_target hzt⟩, e.right_inv hzt⟩
    · rintro ⟨w, ⟨hw, hwe⟩, hwz⟩
      rw [← hwz, e.left_inv hwe]
      exact hw
  have hproper := hD.preimage_boundary_eq_frontier
  refine ⟨e, _, U₀, hemax, hye, hU₀o, heyU₀, hU₀t, himg ▸ hσo, himg ▸ hk, ?_, fun z hz => ?_⟩
  · rw [hh0, map_zero, map_zero]
  obtain ⟨⟨hsA, hsB⟩, hcov, -, -, hfrA, hfrB⟩ := hU₀sub hz
  refine ⟨?_, ?_, fun hX hX2 => ?_⟩
  · rw [hZz z hz, hsA, hsB]
    change _ ↔ ((Lq (h z)).2.1 = 0 ∨ (Lq (h z)).2.2 = 0) ∧ 0 ≤ (Lq (h z)).1
    tauto
  · rw [hDz z hz, hsA, hsB]
    change _ ↔ ((Lq (h z)).2.1, (Lq (h z)).2.2) = ((0 : ℝ), (0 : ℝ)) ∧ 0 ≤ (Lq (h z)).1
    rw [Prod.mk.injEq]
    tauto
  · have hzt := hU₀t hz
    have hZ : e.symm z ∈ D '' D.domain := (hZz z hz).mpr (by
      rw [hsA, hsB]
      change ((Lq (h z)).2.1 = 0 ∨ (Lq (h z)).2.2 = 0) at hX
      change 0 ≤ (Lq (h z)).1 at hX2
      tauto)
    obtain ⟨x, hx, hxz⟩ := hZ
    have hxP : x ∈ D.domain ∩ D ⁻¹' e.source := ⟨hx, by
      change D x ∈ e.source
      rw [hxz]
      exact e.map_target hzt⟩
    have hfx : (e ∘ D) x = z := by
      change e (D x) = z
      rw [hxz, e.right_inv hzt]
    have hfrP : x ∈ frontier (D.domain ∩ D ⁻¹' e.source) ↔ ℓ (h z) = 0 := by
      rcases hcov ⟨hxP, hfx⟩ with hxA | hxB
      · exact hfrA x hxA hfx
      · exact hfrB x hxB hfx
    have hfrD : x ∈ frontier (D.domain ∩ D ⁻¹' e.source) ↔ x ∈ frontier D.domain := by
      constructor
      · intro h1
        exact ContinuousWithinAt.mem_frontier_of_mem_frontier_inter_preimage
          (D.continuousOn x hx) hx e.open_source hxP.2 h1
      · intro h1
        refine (mem_frontier_iff_notMem_interior hxP).mpr fun h2 => ?_
        exact (mem_frontier_iff_notMem_interior hx).mp h1 (interior_mono inter_subset_left h2)
    rw [← hxz]
    change D x ∈ BdM ↔ (Lq (h z)).1 = 0
    rw [← hfrP.trans (show ℓ (h z) = 0 ↔ (Lq (h z)).1 = 0 from Iff.rfl), hfrD, ← hproper]
    exact ⟨fun h1 => ⟨hx, h1⟩, fun h1 => h1.2⟩

theorem exists_linearEquiv_snd_eq_of_ne_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = 3) {ℓ : F →ₗ[ℝ] ℝ}
    (hℓ : ℓ ≠ 0) : ∃ M : F ≃ₗ[ℝ] (ℝ × ℝ) × ℝ, ∀ v, (M v).2 = ℓ v := by
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra h
    apply hℓ
    ext w
    by_contra hw
    exact h ⟨w, hw⟩
  have hv₀ : ℓ ((ℓ v)⁻¹ • v) = 1 := by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  have hK : Module.finrank ℝ (LinearMap.ker ℓ) = 2 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hℓ
    omega
  let ι : LinearMap.ker ℓ ≃ₗ[ℝ] ℝ × ℝ := LinearEquiv.ofFinrankEq _ _ (by rw [hK]; simp)
  let π : F →ₗ[ℝ] LinearMap.ker ℓ :=
    LinearMap.codRestrict (LinearMap.ker ℓ) (LinearMap.id - ℓ.smulRight ((ℓ v)⁻¹ • v))
      (fun w => by simp [LinearMap.mem_ker, hv₀])
  let Mlin : F →ₗ[ℝ] (ℝ × ℝ) × ℝ := LinearMap.prod (ι.toLinearMap.comp π) ℓ
  have hinj : Function.Injective Mlin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h1 : ℓ w = 0 := congrArg Prod.snd hw
    have h2 : ι (π w) = 0 := congrArg Prod.fst hw
    have h3 : π w = 0 := by rwa [LinearEquiv.map_eq_zero_iff] at h2
    have h4 : w - ℓ w • ((ℓ v)⁻¹ • v) = 0 := congrArg Subtype.val h3
    rwa [h1, zero_smul, sub_zero] at h4
  have hsurj : Function.Surjective Mlin :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hF]; simp)).mp hinj
  exact ⟨LinearEquiv.ofBijective Mlin ⟨hinj, hsurj⟩, fun w => rfl⟩

theorem isPLHomeomorphOn_of_openPartialHomeomorph {F G : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G]
    (τ : OpenPartialHomeomorph F G) (h1 : IsPiecewiseAffineOn τ τ.source)
    (h2 : IsPiecewiseAffineOn τ.symm τ.target) {S : Set F} (hS : IsOpen S)
    (hSs : S ⊆ τ.source) : IsOpen (τ '' S) ∧ IsPLHomeomorphOn τ S (τ '' S) := by
  have hopen : IsOpen (τ '' S) := τ.isOpen_image_of_subset_source hS hSs
  refine ⟨hopen, (τ.injOn.mono hSs).bijOn_image, h1.mono hS hSs, ?_⟩
  refine (h2.mono hopen fun y hy => ?_).congr fun y hy => ?_
  · obtain ⟨x, hx, rfl⟩ := hy
    exact τ.map_source (hSs hx)
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [(τ.injOn.mono hSs).leftInvOn_invFunOn hx, τ.left_inv (hSs hx)]

theorem smul_mem_halfCross_iff {v : (ℝ × ℝ) × ℝ} {s : ℝ} (hs : 0 < s) :
    (s • v ∈ crossPlanes ∧ 0 ≤ (s • v).2) ↔ (v ∈ crossPlanes ∧ 0 ≤ v.2) := by
  change ((s • v).1.1 = 0 ∨ (s • v).1.2 = 0) ∧ 0 ≤ (s • v).2 ↔
    (v.1.1 = 0 ∨ v.1.2 = 0) ∧ 0 ≤ v.2
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_eq_zero, hs.ne', false_or]
  rw [mul_nonneg_iff_of_pos_left hs]

open Classical in
theorem exists_endChart_of_mem_boundary (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ (D : SingularTwoCell L.space) (BdM B W : Set L.space), NormalSingularCellData D BdM B →
      IsPLBoundarySide D W BdM → ∀ y ∈ doublePointSet D D.domain, y ∈ BdM →
        ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set E), IsOpen V ∧ IsOpen Ω ∧
          IsPLHomeomorphOn ψ V (L.space ∩ Ω) ∧ (0 : (ℝ × ℝ) × ℝ) ∈ V ∧ ψ 0 = y ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes ∧ 0 ≤ p.2) ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' doublePointSet D D.domain ↔ p.1 = 0 ∧ 0 ≤ p.2) ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' W ↔ 0 ≤ p.2) ∧
            ∀ p ∈ V, ψ p ∈ Subtype.val '' BdM ↔ p.2 = 0 := by
  let _ := combinatorialChartedSpace L hL
  have _ : HasGroupoid L.space (plGroupoid 3) := combinatorialChartedSpace_hasGroupoid L hL
  intro D BdM B W hD hside y hy hyBd
  obtain ⟨e, k, U₀, hemax, hye, hU₀o, heyU₀, -, -, hk, hk0, hkf⟩ :=
    exists_boundaryCrossing_straighteningChart L hL hD hy hyBd
  obtain ⟨x₀, hx₀, -, -, -, hx₀y, -⟩ := hy
  have hx₀fr : x₀ ∈ frontier D.domain := by
    rw [← hD.preimage_boundary_eq_frontier]
    exact ⟨hx₀, show D x₀ ∈ BdM from hx₀y ▸ hyBd⟩
  obtain ⟨e', ℓ', he', hℓ', hye', hW', hB'⟩ := hside.2.2.2.2 y ⟨x₀, hx₀fr, hx₀y⟩
  obtain ⟨M', hM'⟩ := exists_linearEquiv_snd_eq_of_ne_zero (by simp) hℓ'
  have hℓ'y : ℓ' (e' y) = 0 := (hB' y hye').mp hyBd
  have hτ : e.symm.trans e' ∈ plGroupoid 3 :=
    StructureGroupoid.compatible_of_mem_maximalAtlas hemax he'
  obtain ⟨hτ1, hτ2⟩ := mem_plGroupoid_iff.mp hτ
  have hU₁o : IsOpen (U₀ ∩ (e.symm.trans e').source) := hU₀o.inter (e.symm.trans e').open_source
  have heyU₁ : e y ∈ U₀ ∩ (e.symm.trans e').source := by
    refine ⟨heyU₀, ?_⟩
    rw [OpenPartialHomeomorph.trans_source, e.symm_source]
    exact ⟨e.map_source hye, by rw [mem_preimage, e.left_inv hye]; exact hye'⟩
  have hU₁U₀ : U₀ ∩ (e.symm.trans e').source ⊆ U₀ := inter_subset_left
  have he'src : ∀ z ∈ U₀ ∩ (e.symm.trans e').source, e.symm z ∈ e'.source := by
    intro z hz
    have h1 := hz.2
    rw [OpenPartialHomeomorph.trans_source] at h1
    exact h1.2
  have hkU₁o : IsOpen (k '' (U₀ ∩ (e.symm.trans e').source)) :=
    invariance_of_domain_isOpen_image_of_finrank_eq (by simp) hU₁o
      (hk.isPiecewiseAffineOn.continuousOn.mono hU₁U₀) (hk.bijOn.injOn.mono hU₁U₀)
  have hk₁ := hk.restrict_isOpen hU₁o hU₁U₀ hkU₁o
  obtain ⟨hτU₁o, hτU₁⟩ := isPLHomeomorphOn_of_openPartialHomeomorph _ hτ1 hτ2 hU₁o
    inter_subset_right
  obtain ⟨hMo, hMpl⟩ := isPLHomeomorphOn_linearEquiv_image M' hτU₁o
  have htr := (isPLHomeomorphOn_add_const (-M' (e' y))).restrict_isOpen hMo (subset_univ _)
    (isOpenMap_add_right _ _ hMo)
  have hTo := isOpenMap_add_right (-M' (e' y)) _ hMo
  have hT := hk₁.symm.trans (hτU₁.trans (hMpl.trans htr))
  have hkinv : ∀ p ∈ k '' (U₀ ∩ (e.symm.trans e').source),
      Function.invFunOn k (U₀ ∩ (e.symm.trans e').source) p ∈ U₀ ∩ (e.symm.trans e').source ∧
        k (Function.invFunOn k (U₀ ∩ (e.symm.trans e').source) p) = p :=
    fun p hp => ⟨hk₁.bijOn.surjOn.mapsTo_invFunOn hp, hk₁.bijOn.invOn_invFunOn.2 hp⟩
  have h0k : (0 : (ℝ × ℝ) × ℝ) ∈ k '' (U₀ ∩ (e.symm.trans e').source) := ⟨e y, heyU₁, hk0⟩
  obtain ⟨G, ρT, hρT, hρTsub, hG, hGT, hGhom0⟩ :=
    hT.exists_isPLHomeomorphOn_univ_homogeneous hkU₁o hTo h0k
  have hball : ∀ p ∈ ball (0 : (ℝ × ℝ) × ℝ) ρT, ∃ z ∈ U₀ ∩ (e.symm.trans e').source,
      k z = p ∧ G p = M' (e' (e.symm z)) + -M' (e' y) := by
    intro p hp
    obtain ⟨hz, hkz⟩ := hkinv p (hρTsub hp)
    exact ⟨_, hz, hkz, hGT hp⟩
  have hG0 : G 0 = 0 := by
    obtain ⟨z, hz, hkz, hGz⟩ := hball 0 (mem_ball_self hρT)
    have hze : z = e y := hk.bijOn.injOn (hU₁U₀ hz) heyU₀ (hkz.trans hk0.symm)
    rw [hGz, hze, e.left_inv hye, add_neg_cancel]
  have hGhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ s : ℝ, 0 ≤ s → G (s • v) = s • G v := by
    intro v s hs
    simpa [hG0] using hGhom0 v s hs
  have hsnd : ∀ z, (M' (e' (e.symm z)) + -M' (e' y)).2 = ℓ' (e' (e.symm z)) := by
    intro z
    rw [Prod.snd_add, Prod.snd_neg, hM', hM', hℓ'y, neg_zero, add_zero]
  have hsmall : ∀ p : (ℝ × ℝ) × ℝ, ∃ s : ℝ, 0 < s ∧ s • p ∈ ball (0 : (ℝ × ℝ) × ℝ) ρT := by
    intro p
    refine ⟨ρT / (2 * (‖p‖ + 1)), by positivity, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
      div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg p]
  have hpos : ∀ p ∈ crossPlanes, 0 ≤ p.2 → 0 ≤ (G p).2 := by
    intro p hp hp2
    obtain ⟨s, hs, hsp⟩ := hsmall p
    obtain ⟨z, hz, hkz, hGz⟩ := hball _ hsp
    have hX : k z ∈ crossPlanes ∧ 0 ≤ (k z).2 := by
      rw [hkz]
      exact (smul_mem_halfCross_iff hs).mpr ⟨hp, hp2⟩
    have h0 := (hW' _ (he'src z hz)).mp (hside.1 (((hkf z (hU₁U₀ hz)).1).mpr hX))
    have hsG : 0 ≤ (G (s • p)).2 := by
      rw [hGz, hsnd z]
      exact h0
    rw [hGhom p s hs.le, Prod.smul_snd, smul_eq_mul] at hsG
    exact (mul_nonneg_iff_of_pos_left hs).mp hsG
  have hzero : ∀ p ∈ crossPlanes, 0 ≤ p.2 → ((G p).2 = 0 ↔ p.2 = 0) := by
    intro p hp hp2
    obtain ⟨s, hs, hsp⟩ := hsmall p
    obtain ⟨z, hz, hkz, hGz⟩ := hball _ hsp
    have hX : k z ∈ crossPlanes ∧ 0 ≤ (k z).2 := by
      rw [hkz]
      exact (smul_mem_halfCross_iff hs).mpr ⟨hp, hp2⟩
    have key : (G (s • p)).2 = 0 ↔ (s • p).2 = 0 := by
      rw [hGz, hsnd z, ← hB' _ (he'src z hz), ← hkz]
      exact (hkf z (hU₁U₀ hz)).2.2 hX.1 hX.2
    rw [hGhom p s hs.le, Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul, mul_eq_zero,
      mul_eq_zero, or_iff_right hs.ne', or_iff_right hs.ne'] at key
    exact key
  obtain ⟨Θ, hΘ, hΘ0, -, hΘX, hΘA, hΘP, hΘZ⟩ :=
    exists_homogeneous_normalForm_crossHalfSpace hG hGhom hpos hzero
  have hGinj : Function.Injective G := fun x x' h => hG.bijOn.injOn (mem_univ x) (mem_univ x') h
  set Ginv := Function.invFunOn G univ with hGinvdef
  have hGinvG : ∀ q, Ginv (G q) = q := fun q => hG.bijOn.invOn_invFunOn.1 (mem_univ q)
  have hGGinv : ∀ w, G (Ginv w) = w := fun w => hG.bijOn.invOn_invFunOn.2 (mem_univ w)
  have hGinvc : Continuous Ginv :=
    continuousOn_univ.mp hG.isPiecewiseAffineOn_invFunOn.continuousOn
  have hGinv0 : Ginv 0 = 0 := by
    have h := hGinvG 0
    rwa [hG0] at h
  have hAc : Continuous fun w : (ℝ × ℝ) × ℝ => M'.symm (w + M' (e' y)) :=
    (LinearMap.continuous_of_finiteDimensional M'.symm.toLinearMap).comp
      (continuous_id.add continuous_const)
  have hA0 : M'.symm (0 + M' (e' y)) = e' y := by rw [zero_add, LinearEquiv.symm_apply_apply]
  have hnhds : (fun w : (ℝ × ℝ) × ℝ => M'.symm (w + M' (e' y))) ⁻¹' e'.target ∩
      Ginv ⁻¹' ball (0 : (ℝ × ℝ) × ℝ) ρT ∈ 𝓝 (0 : (ℝ × ℝ) × ℝ) :=
    Filter.inter_mem (hAc.continuousAt.preimage_mem_nhds
      (by rw [hA0]; exact e'.open_target.mem_nhds (e'.map_source hye')))
      (hGinvc.continuousAt.preimage_mem_nhds (by rw [hGinv0]; exact ball_mem_nhds 0 hρT))
  obtain ⟨ρs, hρs, hρsball⟩ := Metric.mem_nhds_iff.mp hnhds
  have hgerm : ∀ w ∈ ball (0 : (ℝ × ℝ) × ℝ) ρs, ∃ z ∈ U₀ ∩ (e.symm.trans e').source,
      e'.symm (M'.symm (w + M' (e' y))) = e.symm z ∧ w = G (k z) := by
    intro w hw
    obtain ⟨z, hz, hkz, hGz⟩ := hball _ (hρsball hw).2
    refine ⟨z, hz, ?_, by rw [hkz, hGGinv]⟩
    have hw' : w = M' (e' (e.symm z)) + -M' (e' y) := by rw [← hGz, hGGinv]
    rw [hw', neg_add_cancel_right, LinearEquiv.symm_apply_apply, e'.left_inv (he'src z hz)]
  have hsndA : ∀ w : (ℝ × ℝ) × ℝ, ℓ' (M'.symm (w + M' (e' y))) = w.2 := by
    intro w
    rw [← hM', LinearEquiv.apply_symm_apply, Prod.snd_add, hM', hℓ'y, add_zero]
  have hVo : IsOpen (Θ ⁻¹' ball (0 : (ℝ × ℝ) × ℝ) ρs) :=
    isOpen_ball.preimage (continuousOn_univ.mp hΘ.isPiecewiseAffineOn.continuousOn)
  have hΘimg : Θ '' (Θ ⁻¹' ball (0 : (ℝ × ℝ) × ℝ) ρs) = ball (0 : (ℝ × ℝ) × ℝ) ρs :=
    image_preimage_eq _ fun w => by
      obtain ⟨p, -, hp⟩ := hΘ.bijOn.surjOn (mem_univ w)
      exact ⟨p, hp⟩
  have hΘV := hΘ.restrict_isOpen hVo (subset_univ _) (by rw [hΘimg]; exact isOpen_ball)
  rw [hΘimg] at hΘV
  have hballo : IsOpen (ball (0 : (ℝ × ℝ) × ℝ) ρs) := isOpen_ball
  have htr₂ := (isPLHomeomorphOn_add_const (M' (e' y))).restrict_isOpen hballo
    (subset_univ _) (isOpenMap_add_right _ _ hballo)
  obtain ⟨hA₁o, hA₁⟩ := isPLHomeomorphOn_linearEquiv_image M'.symm
    (isOpenMap_add_right (M' (e' y)) _ hballo)
  have hA : IsPLHomeomorphOn (fun w : (ℝ × ℝ) × ℝ => M'.symm (w + M' (e' y)))
      (ball (0 : (ℝ × ℝ) × ℝ) ρs) _ := htr₂.trans hA₁
  have hAt : (fun x => M'.symm x) '' ((fun w => w + M' (e' y)) '' ball (0 : (ℝ × ℝ) × ℝ) ρs) ⊆
      e'.target := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact (hρsball hw).1
  obtain ⟨Ω, hΩ, -, hvalPL⟩ :=
    exists_isPLHomeomorphOn_val_symm_of_mem_maximalAtlas (E := E) L hL he' hA₁o hAt
  have hψ := hΘV.trans (hA.trans hvalPL)
  refine ⟨_, _, Ω, hVo, hΩ, hψ, ?_, ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_,
    fun p hp => ?_⟩
  · change Θ 0 ∈ ball (0 : (ℝ × ℝ) × ℝ) ρs
    rw [hΘ0]
    exact mem_ball_self hρs
  · change ((e'.symm (M'.symm (Θ 0 + M' (e' y))) : L.space) : E) = y
    rw [hΘ0, hA0, e'.left_inv hye']
  · obtain ⟨z, hz, hez, hwz⟩ := hgerm _ hp
    change ((e'.symm (M'.symm (Θ p + M' (e' y))) : L.space) : E) ∈
      Subtype.val '' (D '' D.domain) ↔ _
    rw [hez, Subtype.val_injective.mem_set_image, (hkf z (hU₁U₀ hz)).1, ← hΘX p, hwz,
      hGinj.mem_set_image]
    rfl
  · obtain ⟨z, hz, hez, hwz⟩ := hgerm _ hp
    change ((e'.symm (M'.symm (Θ p + M' (e' y))) : L.space) : E) ∈
      Subtype.val '' doublePointSet D D.domain ↔ _
    rw [hez, Subtype.val_injective.mem_set_image, (hkf z (hU₁U₀ hz)).2.1, ← hΘA p, hwz,
      hGinj.mem_set_image]
    rfl
  · change ((e'.symm (M'.symm (Θ p + M' (e' y))) : L.space) : E) ∈ Subtype.val '' W ↔ _
    rw [Subtype.val_injective.mem_set_image, hW' _ (e'.map_target (hρsball hp).1),
      e'.right_inv (hρsball hp).1, hsndA, hΘP]
  · change ((e'.symm (M'.symm (Θ p + M' (e' y))) : L.space) : E) ∈ Subtype.val '' BdM ↔ _
    rw [Subtype.val_injective.mem_set_image, hB' _ (e'.map_target (hρsball hp).1),
      e'.right_inv (hρsball hp).1, hsndA, hΘZ]

end DifferentialGeometry.Topology.PiecewiseLinear
