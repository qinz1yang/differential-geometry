/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraightening
import DifferentialGeometry.Topology.PiecewiseLinear.CommonWallComplex
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularSetOfCrossing

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem isPLHomeomorphOn_linearEquiv_image {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    (T : F ≃ₗ[ℝ] G) {V : Set F} (hV : IsOpen V) :
    IsOpen ((fun x => T x) '' V) ∧ IsPLHomeomorphOn (fun x => T x) V ((fun x => T x) '' V) := by
  have hopen : IsOpen ((fun x => T x) '' V) := by
    have h := T.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
    simpa using h
  refine ⟨hopen, T.injective.injOn.bijOn_image,
    (isPiecewiseAffineOn_of_affine T.toLinearMap.toAffineMap hV).congr fun _ _ => rfl, ?_⟩
  refine (isPiecewiseAffineOn_of_affine T.symm.toLinearMap.toAffineMap hopen).congr
    fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := hy
  change Function.invFunOn (fun x => T x) V (T x) = T.symm (T x)
  rw [T.injective.injOn.leftInvOn_invFunOn hx, LinearEquiv.symm_apply_apply]

open Classical in
theorem isPiecewiseAffineOn_val_symm_of_mem_maximalAtlas (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {e : OpenPartialHomeomorph L.space (EuclideanSpace ℝ (Fin 3))},
      e ∈ (plGroupoid 3).maximalAtlas L.space →
        IsPiecewiseAffineOn (fun x => (e.symm x : E)) e.target := by
  let _ := combinatorialChartedSpace L hL
  intro e he
  refine isPiecewiseAffineOn_of_locally fun x hx => ?_
  set ev := chartAt (EuclideanSpace ℝ (Fin 3)) (e.symm x) with hev
  have hT : e.symm.trans ev ∈ plGroupoid 3 :=
    StructureGroupoid.compatible_of_mem_maximalAtlas_left he
  have hxT : x ∈ (e.symm.trans ev).source := by
    rw [OpenPartialHomeomorph.trans_source, e.symm_source]
    exact ⟨hx, mem_chart_source (EuclideanSpace ℝ (Fin 3)) (e.symm x)⟩
  refine ⟨(e.symm.trans ev).source, (e.symm.trans ev).open_source, hxT, ?_⟩
  obtain ⟨p, hp, hevp⟩ := mem_combinatorialChartedSpace_atlas L hL (chart_mem_atlas _ (e.symm x))
  have hsymm := isPiecewiseAffineOn_vertexChart_symm L hp (hL.isPLSphere_link hp)
  rw [← hevp] at hsymm
  have hTpa : IsPiecewiseAffineOn (e.symm.trans ev) (e.symm.trans ev).source :=
    (mem_plGroupoid_iff.mp hT).1
  have hcomp := hsymm.comp hTpa
  have hsub : (e.symm.trans ev).source ⊆ (e.symm.trans ev) ⁻¹' ev.target := fun z hz => by
    have h := (e.symm.trans ev).map_source hz
    rw [OpenPartialHomeomorph.trans_target] at h
    exact h.1
  rw [inter_eq_left.mpr hsub] at hcomp
  have hsrc : (e.symm.trans ev).source ⊆ e.target := fun z hz => by
    rw [OpenPartialHomeomorph.trans_source, e.symm_source] at hz
    exact hz.1
  rw [inter_eq_right.mpr hsrc]
  refine hcomp.congr fun z hz => ?_
  have hz' := hz
  rw [OpenPartialHomeomorph.trans_source, e.symm_source] at hz'
  change ((e.symm z : L.space) : E) = ((ev.symm (ev (e.symm z)) : L.space) : E)
  rw [ev.left_inv hz'.2]

open Classical in
theorem exists_isPLHomeomorphOn_val_symm_of_mem_maximalAtlas (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {e : OpenPartialHomeomorph L.space (EuclideanSpace ℝ (Fin 3))},
      e ∈ (plGroupoid 3).maximalAtlas L.space →
        ∀ {U₀ : Set (EuclideanSpace ℝ (Fin 3))}, IsOpen U₀ → U₀ ⊆ e.target →
          ∃ Ω : Set E, IsOpen Ω ∧ Subtype.val ⁻¹' Ω = e.symm '' U₀ ∧
            IsPLHomeomorphOn (fun x => (e.symm x : E)) U₀ (L.space ∩ Ω) := by
  let _ := combinatorialChartedSpace L hL
  intro e he U₀ hU₀ hU₀t
  have himgopen : IsOpen (e.symm '' U₀) := e.symm.isOpen_image_of_subset_source hU₀ (by
    rw [e.symm_source]
    exact hU₀t)
  obtain ⟨Ω, hΩ, hΩeq⟩ := isOpen_induced_iff.mp himgopen
  have himg : (fun x => (e.symm x : E)) '' U₀ = L.space ∩ Ω := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(e.symm x).2, ?_⟩
      have : e.symm x ∈ Subtype.val ⁻¹' Ω := by rw [hΩeq]; exact ⟨x, hx, rfl⟩
      exact this
    · rintro ⟨hqL, hqΩ⟩
      have : (⟨q, hqL⟩ : L.space) ∈ Subtype.val ⁻¹' Ω := hqΩ
      rw [hΩeq] at this
      obtain ⟨x, hx, hxq⟩ := this
      exact ⟨x, hx, congrArg Subtype.val hxq⟩
  have hinj : InjOn (fun x => (e.symm x : E)) U₀ := fun x hx z hz hxz =>
    e.symm.injOn (by rw [e.symm_source]; exact hU₀t hx) (by rw [e.symm_source]; exact hU₀t hz)
      (Subtype.ext hxz)
  refine ⟨Ω, hΩ, hΩeq, himg ▸ hinj.bijOn_image,
    (isPiecewiseAffineOn_val_symm_of_mem_maximalAtlas L hL he).mono hU₀ hU₀t, ?_⟩
  have hfwd := isPiecewiseAffineOn_val_of_mem_maximalAtlas L hL he
  have hsub : L.space ∩ Ω ⊆ Subtype.val '' e.source := by
    intro q hq
    rw [← himg] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨e.symm x, e.map_target (hU₀t hx), rfl⟩
  have hseteq : Subtype.val '' e.source ∩ Ω = L.space ∩ Ω := by
    refine Subset.antisymm (fun z hz => ⟨?_, hz.2⟩) fun z hz => ⟨hsub hz, hz.2⟩
    obtain ⟨w, -, hw⟩ := hz.1
    rw [← hw]
    exact w.2
  have hpa : IsPiecewiseAffineOn (fun q => if h : q ∈ L.space then e ⟨q, h⟩ else 0)
      (L.space ∩ Ω) := by
    intro q hq
    have h := (hfwd q (hsub hq)).inter_of_mem_nhds (hΩ.mem_nhds hq.2)
    rwa [hseteq] at h
  refine hpa.congr fun q hq => ?_
  rw [← himg] at hq
  obtain ⟨x, hx, rfl⟩ := hq
  rw [hinj.leftInvOn_invFunOn hx]
  beta_reduce
  rw [dite_eq_left (e.symm x).2, Subtype.coe_eta, e.right_inv (hU₀t hx)]

def crossNormalFormEquiv : (ℝ × ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) × ℝ where
  toFun x := ((x.2.1, x.2.2), x.1)
  invFun p := (p.2, p.1.1, p.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
theorem exists_straighteningChart_of_notMem_boundary (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B : Set L.space}, NormalSingularCellData D BdM B →
      ∀ {y : L.space}, y ∈ doublePointSet D D.domain → y ∉ BdM →
        ∀ {O : Set L.space}, IsOpen O → y ∈ O →
          ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set E),
            IsOpen V ∧ IsOpen Ω ∧ IsPLHomeomorphOn ψ V (L.space ∩ Ω) ∧ (y : E) ∈ Ω ∧
              (∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
              (∀ p ∈ V, ψ p ∈ Subtype.val '' doublePointSet D D.domain ↔ p.1 = 0) ∧
              ∀ p ∈ V, ψ p ∈ Subtype.val '' O := by
  let _ := combinatorialChartedSpace L hL
  have _ : HasGroupoid L.space (plGroupoid 3) := combinatorialChartedSpace_hasGroupoid L hL
  intro D BdM B hD y hy hyBd O hO hyO
  obtain ⟨e, he, hye, hcross⟩ := hD.hasPLTwoSidedDoubleCrossingAt_of_notMem_boundary hy hyBd
  have hemax : e ∈ (plGroupoid 3).maximalAtlas L.space :=
    StructureGroupoid.subset_maximalAtlas _ he
  obtain ⟨a, b, A, B', haA, hbB, hfa, hfb, hAP, hBP, hdisj, hAn, hBn, hfA, hfB, htwo,
    hfiber⟩ := hcross
  obtain ⟨U, V₁, h, Lq, hU, hV₁, heyU, hh, hh0, hnear⟩ := htwo.exists_linearEquiv_normalForm
  have hOnhds : e.symm ⁻¹' O ∈ 𝓝 (e y) :=
    (e.continuousAt_symm (e.map_source hye)).preimage_mem_nhds
      (by rw [e.left_inv hye]; exact hO.mem_nhds hyO)
  have hev : ∀ᶠ z in 𝓝 (e y),
      ((z ∈ (e ∘ D) '' A ↔ (Lq (h z)).2.2 = 0) ∧ (z ∈ (e ∘ D) '' B' ↔ (Lq (h z)).2.1 = 0)) ∧
        (D.domain ∩ D ⁻¹' e.source) ∩ (e ∘ D) ⁻¹' {z} ⊆ A ∪ B' ∧ z ∈ U ∧ z ∈ e.target ∧
          e.symm z ∈ O := by
    filter_upwards [hnear, hfiber, hU.mem_nhds heyU, e.open_target.mem_nhds (e.map_source hye),
      hOnhds] with z h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨U₀, hU₀sub, hU₀o, heyU₀⟩ := _root_.mem_nhds_iff.mp hev
  have hU₀U : U₀ ⊆ U := fun z hz => (hU₀sub hz).2.2.1
  have hU₀t : U₀ ⊆ e.target := fun z hz => (hU₀sub hz).2.2.2.1
  have hhU₀o : IsOpen (h '' U₀) := hh.isOpen_image_of_isOpen hV₁ hU₀o hU₀U
  have hhU₀ : IsPLHomeomorphOn h U₀ (h '' U₀) := hh.restrict_isOpen hU₀o hU₀U hhU₀o
  obtain ⟨hLo, hLq⟩ := isPLHomeomorphOn_linearEquiv_image Lq hhU₀o
  obtain ⟨hσo, hσ⟩ := isPLHomeomorphOn_linearEquiv_image crossNormalFormEquiv hLo
  set V := (fun x => crossNormalFormEquiv x) '' ((fun x => Lq x) '' (h '' U₀)) with hVdef
  set k : EuclideanSpace ℝ (Fin 3) → (ℝ × ℝ) × ℝ := fun z => crossNormalFormEquiv (Lq (h z))
    with hkdef
  have hk : IsPLHomeomorphOn k U₀ V := (hhU₀.trans hLq).trans hσ
  obtain ⟨Ω, hΩ, hΩeq, hvalPL⟩ :=
    exists_isPLHomeomorphOn_val_symm_of_mem_maximalAtlas (E := E) L hL hemax hU₀o hU₀t
  set ψ : (ℝ × ℝ) × ℝ → E :=
    (fun x => ((e.symm x : L.space) : E)) ∘ Function.invFunOn k U₀ with hψdef
  have hψ : IsPLHomeomorphOn ψ V (L.space ∩ Ω) := hk.symm.trans hvalPL
  have hyΩ : (y : E) ∈ Ω := by
    have h1 : y ∈ Subtype.val ⁻¹' Ω := by
      rw [hΩeq]
      exact ⟨e y, heyU₀, e.left_inv hye⟩
    exact h1
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
  have hpt : ∀ p ∈ V, Function.invFunOn k U₀ p ∈ U₀ ∧ k (Function.invFunOn k U₀ p) = p :=
    fun p hp => ⟨hk.bijOn.surjOn.mapsTo_invFunOn hp, hk.bijOn.invOn_invFunOn.2 hp⟩
  refine ⟨ψ, V, Ω, hσo, hΩ, hψ, hyΩ, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨hz, hkz⟩ := hpt p hp
    set z := Function.invFunOn k U₀ p
    have hsh := (hU₀sub hz).1
    change ((e.symm z : L.space) : E) ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes
    rw [Subtype.val_injective.mem_set_image, hZz z hz, hsh.1, hsh.2, ← hkz]
    change _ ↔ (Lq (h z)).2.1 = 0 ∨ (Lq (h z)).2.2 = 0
    exact or_comm
  · obtain ⟨hz, hkz⟩ := hpt p hp
    set z := Function.invFunOn k U₀ p
    have hsh := (hU₀sub hz).1
    change ((e.symm z : L.space) : E) ∈ Subtype.val '' doublePointSet D D.domain ↔ p.1 = 0
    rw [Subtype.val_injective.mem_set_image, hDz z hz, hsh.1, hsh.2, ← hkz]
    change _ ↔ ((Lq (h z)).2.1, (Lq (h z)).2.2) = ((0 : ℝ), (0 : ℝ))
    rw [Prod.mk.injEq]
    exact and_comm
  · obtain ⟨hz, -⟩ := hpt p hp
    exact ⟨_, (hU₀sub hz).2.2.2.2, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
