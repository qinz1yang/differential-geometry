/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.ClosedBallImage
import DifferentialGeometry.Topology.PiecewiseLinear.ConsecutiveCellUnion
import DifferentialGeometry.Topology.PiecewiseLinear.NestedJordanCurves
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeTraces
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsOpenTopologicalCell.exists_planarChart {X : Type*} [TopologicalSpace X] {M : Set X}
    (hM : IsOpenTopologicalCell 2 M) :
    ∃ (Ψ : X → Schoenflies.Plane) (Φ : Schoenflies.Plane → X),
      ContinuousOn Ψ M ∧ ContinuousOn Φ (Metric.ball 0 1) ∧ MapsTo Ψ M (Metric.ball 0 1) ∧
        MapsTo Φ (Metric.ball 0 1) M ∧ (∀ x ∈ M, Φ (Ψ x) = x) ∧
          (∀ p ∈ Metric.ball (0 : Schoenflies.Plane) 1, Ψ (Φ p) = p) ∧
            ∀ W : Set X, IsOpen W → IsOpen (Ψ '' (W ∩ M)) := by
  classical
  obtain ⟨ψ⟩ := hM
  let x₀ : X := ψ.symm ⟨0, Metric.mem_ball_self one_pos⟩
  let Ψ : X → Schoenflies.Plane := fun x =>
    if hx : x ∈ M then (ψ ⟨x, hx⟩ : Schoenflies.Plane) else 0
  let Φ : Schoenflies.Plane → X := fun p =>
    if hp : p ∈ Metric.ball (0 : Schoenflies.Plane) 1 then (ψ.symm ⟨p, hp⟩ : X) else x₀
  have hΨ : ∀ x (hx : x ∈ M), Ψ x = ψ ⟨x, hx⟩ := fun x hx => dite_eq_left hx
  have hΦ : ∀ p (hp : p ∈ Metric.ball (0 : Schoenflies.Plane) 1), Φ p = ψ.symm ⟨p, hp⟩ :=
    fun p hp => dite_eq_left hp
  refine ⟨Ψ, Φ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : M.domRestrict Ψ = fun x => (ψ x : Schoenflies.Plane) := funext fun x => hΨ x.1 x.2
    rw [heq]
    exact continuous_subtype_val.comp ψ.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have heq : (Metric.ball (0 : Schoenflies.Plane) 1).domRestrict Φ = fun p => (ψ.symm p : X) :=
      funext fun p => hΦ p.1 p.2
    rw [heq]
    exact continuous_subtype_val.comp ψ.symm.continuous
  · intro x hx
    rw [hΨ x hx]
    exact (ψ ⟨x, hx⟩).2
  · intro p hp
    rw [hΦ p hp]
    exact (ψ.symm ⟨p, hp⟩).2
  · intro x hx
    rw [hΨ x hx, hΦ _ (ψ ⟨x, hx⟩).2]
    simp
  · intro p hp
    rw [hΦ p hp, hΨ _ (ψ.symm ⟨p, hp⟩).2]
    simp
  · intro W hW
    have heq : Ψ '' (W ∩ M) = Subtype.val '' (ψ '' ((Subtype.val : M → X) ⁻¹' W)) := by
      ext p
      constructor
      · rintro ⟨x, ⟨hxW, hxM⟩, rfl⟩
        exact ⟨ψ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, hxW, rfl⟩, (hΨ x hxM).symm⟩
      · rintro ⟨_, ⟨z, hzW, rfl⟩, rfl⟩
        exact ⟨z.1, ⟨hzW, z.2⟩, hΨ z.1 z.2⟩
    rw [heq]
    exact Metric.isOpen_ball.isOpenMap_subtype_val _
      (ψ.isOpenMap _ (hW.preimage continuous_subtype_val))

theorem isJordanCurve_image_of_isPLSphere_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {J M : Set E} (hJ : IsPLSphere 1 J) (hJM : J ⊆ M)
    {Ψ : E → Schoenflies.Plane} (hΨ : ContinuousOn Ψ M) (hΨi : InjOn Ψ M) :
    Schoenflies.IsJordanCurve (Ψ '' J) := by
  obtain ⟨f, hf⟩ := hJ
  have hmap : MapsTo stdTriangleLoop (Icc 0 1) (stdSimplexBoundary 2) :=
    fun t ht => stdTriangleLoop_image.subset ⟨t, ht, rfl⟩
  have hfM : MapsTo f (stdSimplexBoundary 2) M := fun x hx => hJM (hf.bijOn.mapsTo hx)
  have h01 : stdTriangleLoop 0 = stdTriangleLoop 1 := by norm_num [stdTriangleLoop]
  refine ⟨Ψ ∘ f ∘ stdTriangleLoop, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hΨ.comp (hf.isPiecewiseAffineOn.continuousOn.comp
      continuous_stdTriangleLoop.continuousOn hmap) (hfM.comp hmap)
  · simp only [Function.comp_apply, h01]
  · intro s hs t ht hst
    have hs' := hmap ⟨hs.1, hs.2.le⟩
    have ht' := hmap ⟨ht.1, ht.2.le⟩
    exact injOn_stdTriangleLoop hs ht
      (hf.bijOn.injOn hs' ht' (hΨi (hfM hs') (hfM ht') hst))
  · change (fun t => Ψ (f (stdTriangleLoop t))) '' Icc 0 1 = Ψ '' J
    rw [← image_image Ψ (fun t => f (stdTriangleLoop t)), ← image_image f stdTriangleLoop,
      stdTriangleLoop_image, hf.image_eq]

section OuterTrace

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_outerTrace
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) :
    ∃ J Din O : Set E3, IsPLSphere 1 J ∧ J ⊆ Ec e ∩ frontier XK.space ∧ Din ⊆ Eint e ∧
      Disjoint Din J ∧ (∃ W : Set E3, IsOpen W ∧ Din = W ∩ Eint e) ∧
        h (e.centroid ℝ id) ∈ Din ∧ IsTopologicalCellWithInterior 2 (Din ∪ J) Din ∧
          IsOpen O ∧ J ⊆ O ∧ ∀ y ∈ O ∩ Eint e,
            (y ∈ XK.space ↔ y ∈ Din ∪ J) ∧ (y ∈ frontier XK.space ↔ y ∈ J) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hXcpt : IsCompact XK.space := (isPolyhedron_space XK).isCompact
  have hpc := hd.pseudoCell e he hcard
  have hT := h2.trace_subset hd he hcard
  have hEEc : Eint e ⊆ Ec e := by
    rw [hpc.carrierEq]
    exact subset_union_left
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, hΨo⟩ := hpc.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ (Eint e) := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  obtain ⟨𝒥, h𝒥, h𝒥d, h𝒥U⟩ := h2.exists_traceCircles hd he hcard
  have hJT : ∀ J ∈ 𝒥, J ⊆ Ec e ∩ frontier XK.space := fun J hJ =>
    h𝒥U ▸ subset_iUnion₂ (s := fun J (_ : J ∈ 𝒥) => J) J hJ
  have hJE : ∀ J ∈ 𝒥, J ⊆ Eint e := fun J hJ => (hJT J hJ).trans (hT.trans sdiff_subset)
  let 𝒞 : Finset (Set Schoenflies.Plane) := 𝒥.image fun J => Ψ '' J
  have hU𝒞 : (⋃ γ ∈ 𝒞, γ) = Ψ '' (Ec e ∩ frontier XK.space) := by
    rw [Finset.set_biUnion_finset_image, ← h𝒥U, image_iUnion₂]
  have hmemE : ∀ {A : Set E3}, A ⊆ Eint e → ∀ y ∈ Eint e, Ψ y ∈ Ψ '' A ↔ y ∈ A := by
    intro A hA y hy
    constructor
    · rintro ⟨z, hz, hzy⟩
      rw [← hΨi (hA hz) hy hzy]
      exact hz
    · exact fun hyA => ⟨y, hyA, rfl⟩
  have hEX : Eint e ∩ XK.space = Ec e ∩ XK.space := by
    rw [hpc.carrierEq, union_inter_distrib_right, (h2.rimDisjoint e he hcard).inter_eq,
      union_empty]
  have hTE : Ec e ∩ frontier XK.space ⊆ Eint e ∩ XK.space := fun y hy =>
    ⟨(hT hy).1, hXc.frontier_subset hy.2⟩
  let Cp : Set Schoenflies.Plane := Ψ '' (Eint e ∩ XK.space)
  have hCp : IsCompact Cp := by
    refine IsCompact.image_of_continuousOn ?_ (hΨc.mono inter_subset_left)
    rw [hEX]
    exact hXcpt.inter_left hpc.isClosed
  have hCo : IsOpen (Cp \ ⋃ γ ∈ 𝒞, γ) := by
    have heq : Cp \ ⋃ γ ∈ 𝒞, γ = Ψ '' (interior XK.space ∩ Eint e) := by
      rw [hU𝒞]
      ext p
      constructor
      · rintro ⟨⟨y, ⟨hyE, hyX⟩, rfl⟩, hpT⟩
        exact ⟨y, ⟨(mem_interior_iff_notMem_frontier hyX).mpr fun hfr =>
          hpT ⟨y, ⟨hEEc hyE, hfr⟩, rfl⟩, hyE⟩, rfl⟩
      · rintro ⟨y, ⟨hyi, hyE⟩, rfl⟩
        refine ⟨⟨y, ⟨hyE, interior_subset hyi⟩, rfl⟩, ?_⟩
        rintro ⟨z, hz, hzy⟩
        have hzy' := hΨi (hTE hz).1 hyE hzy
        rw [hzy'] at hz
        exact hz.2.2 hyi
    rw [heq]
    exact hΨo _ isOpen_interior
  have hJor : ∀ J ∈ 𝒥, Schoenflies.IsJordanCurve (Ψ '' J) := fun J hJ =>
    isJordanCurve_image_of_isPLSphere_one (h𝒥 J hJ) (hJE J hJ) hΨc hΨi
  have h𝒞 : ∀ γ ∈ 𝒞, Schoenflies.IsJordanCurve γ := by
    intro γ hγ
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ
    exact hJor J hJ
  have h𝒞d : ∀ γ ∈ 𝒞, ∀ γ' ∈ 𝒞, γ ≠ γ' → Disjoint γ γ' := by
    intro γ hγ γ' hγ' hne
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.mp hγ'
    have hJJ' : J ≠ J' := fun h => hne (h ▸ rfl)
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
    have hxx := hΨi (hJE J' hJ' hx') (hJE J hJ hx) hxx'
    rw [hxx] at hx'
    exact Set.disjoint_left.mp (h𝒥d J hJ J' hJ' hJJ') hx hx'
  have h𝒞C : ∀ γ ∈ 𝒞, γ ⊆ Cp := by
    intro γ hγ
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ
    exact image_mono ((hJT J hJ).trans hTE)
  have hPE : h (e.centroid ℝ id) ∈ Eint e := hpc.centerMem
  have hPint : h (e.centroid ℝ id) ∈ interior XK.space := by
    have hPK : h (e.centroid ℝ id) ∈ h '' K.space := by
      have hmeet : h (e.centroid ℝ id) ∈ Ec e ∩ h '' K.space := by
        rw [hd.meetsGraph e he hcard]
        exact rfl
      exact hmeet.2
    exact subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood hPK
  have hcC : Ψ (h (e.centroid ℝ id)) ∈ Cp := ⟨_, ⟨hPE, interior_subset hPint⟩, rfl⟩
  have hc𝒞 : ∀ γ ∈ 𝒞, Ψ (h (e.centroid ℝ id)) ∉ γ := by
    intro γ hγ hPγ
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ
    have hPJ := (hmemE (hJE J hJ) _ hPE).mp hPγ
    exact (hJT J hJ hPJ).2.2 hPint
  have hside : ∀ γ ∈ 𝒞, ∀ q ∈ γ, ∃ V S₁ S₂ : Set Schoenflies.Plane, IsOpen V ∧ q ∈ V ∧
      V \ (⋃ γ' ∈ 𝒞, γ') ⊆ S₁ ∪ S₂ ∧ Disjoint S₁ γ ∧ Disjoint S₂ Cp ∧
        IsPreconnected S₁ ∧ IsPreconnected S₂ ∧ q ∈ closure S₂ := by
    intro γ hγ q hq
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨x, hxJ, rfl⟩ := hq
    have hxT := hJT J hJ hxJ
    obtain ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, hφU⟩ := h2.exists_sideChart hd he hcard hxT
    let g := Function.invFunOn φ U
    have hgc : ContinuousOn g (Metric.ball 0 ρ) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
    have hgU : ∀ w ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, g w ∈ U ∧ φ (g w) = w := fun w hw =>
      ⟨hφ.bijOn.surjOn.mapsTo_invFunOn hw, hφ.bijOn.invOn_invFunOn.2 hw⟩
    let B₀ : Set (ℝ × ℝ × ℝ) := Metric.ball 0 ρ ∩ {w | w.2.2 = 0}
    let H₁ : Set (ℝ × ℝ × ℝ) := B₀ ∩ {w | 0 < w.2.1}
    let H₂ : Set (ℝ × ℝ × ℝ) := B₀ ∩ {w | w.2.1 < 0}
    have hgE : ∀ w ∈ B₀, g w ∈ Eint e := fun w hw =>
      ((hφU _ (hgU w hw.1).1).1).mpr (by rw [(hgU w hw.1).2]; exact hw.2)
    have hΨg : ContinuousOn (Ψ ∘ g) B₀ := hΨc.comp (hgc.mono inter_subset_left) hgE
    have hlin2 : IsLinearMap ℝ fun w : ℝ × ℝ × ℝ => w.2.2 :=
      ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear
    have hlin1 : IsLinearMap ℝ fun w : ℝ × ℝ × ℝ => w.2.1 :=
      ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear
    have hB₀ : Convex ℝ B₀ := (convex_ball 0 ρ).inter (convex_hyperplane hlin2 0)
    have hH₁ : IsPreconnected H₁ := (hB₀.inter (convex_halfSpace_gt hlin1 0)).isPreconnected
    have hH₂ : IsPreconnected H₂ := (hB₀.inter (convex_halfSpace_lt hlin1 0)).isPreconnected
    have hgx : g 0 = x := by
      have hinv := hφ.bijOn.invOn_invFunOn.1 hxU
      rwa [hφx] at hinv
    refine ⟨Ψ '' (U ∩ Eint e), (Ψ ∘ g) '' H₁, (Ψ ∘ g) '' H₂, hΨo U hU,
      ⟨x, ⟨hxU, hJE J hJ hxJ⟩, rfl⟩, ?_, ?_, ?_, hH₁.image _ (hΨg.mono inter_subset_left),
      hH₂.image _ (hΨg.mono inter_subset_left), ?_⟩
    · rintro _ ⟨⟨y, ⟨hyU, hyE⟩, rfl⟩, hyT⟩
      rw [hU𝒞] at hyT
      have hyfr : y ∉ frontier XK.space := fun hfr => hyT ⟨y, ⟨hEEc hyE, hfr⟩, rfl⟩
      have h0 : (φ y).2.1 ≠ 0 := fun h0 => hyfr (((hφU y hyU).2.1).mpr h0)
      have hw : φ y ∈ B₀ := ⟨hφ.bijOn.mapsTo hyU, ((hφU y hyU).1).mp hyE⟩
      have hgy : g (φ y) = y := hφ.bijOn.invOn_invFunOn.1 hyU
      rcases lt_or_gt_of_ne h0 with hneg | hpos
      · exact Or.inr ⟨φ y, ⟨hw, hneg⟩, by simp only [Function.comp_apply, hgy]⟩
      · exact Or.inl ⟨φ y, ⟨hw, hpos⟩, by simp only [Function.comp_apply, hgy]⟩
    · refine Set.disjoint_left.mpr ?_
      rintro _ ⟨w, hw, rfl⟩ ⟨z, hzJ, hzw⟩
      have heq := hΨi (hJE J hJ hzJ) (hgE w hw.1) hzw
      have hfr : g w ∈ frontier XK.space := heq ▸ (hJT J hJ hzJ).2
      have h0 := ((hφU _ (hgU w hw.1.1).1).2.1).mp hfr
      rw [(hgU w hw.1.1).2] at h0
      exact hw.2.ne' h0
    · refine Set.disjoint_left.mpr ?_
      rintro _ ⟨w, hw, rfl⟩ ⟨z, ⟨hzE, hzX⟩, hzw⟩
      have heq := hΨi hzE (hgE w hw.1) hzw
      have hX : g w ∈ XK.space := heq ▸ hzX
      have h0 := ((hφU _ (hgU w hw.1.1).1).2.2).mp hX
      rw [(hgU w hw.1.1).2] at h0
      exact absurd hw.2 (not_lt.mpr h0)
    · have h0B : (0 : ℝ × ℝ × ℝ) ∈ B₀ := ⟨Metric.mem_ball_self hρ, rfl⟩
      have hlim : Filter.Tendsto (fun τ : ℝ => ((0 : ℝ), -τ, (0 : ℝ))) (𝓝[>] 0)
          (𝓝 ((0 : ℝ), -(0 : ℝ), (0 : ℝ))) :=
        ((by fun_prop : Continuous fun τ : ℝ => ((0 : ℝ), -τ, (0 : ℝ))).tendsto 0).mono_left
          nhdsWithin_le_nhds
      rw [neg_zero, Prod.mk_zero_zero, Prod.mk_zero_zero] at hlim
      have h0cl : (0 : ℝ × ℝ × ℝ) ∈ closure H₂ := by
        refine mem_closure_of_tendsto hlim ?_
        filter_upwards [Ioo_mem_nhdsGT hρ] with τ hτ
        refine ⟨⟨?_, rfl⟩, neg_lt_zero.mpr hτ.1⟩
        rw [mem_ball_zero_iff]
        simp only [Prod.norm_def, max_lt_iff, norm_zero, norm_neg, Real.norm_eq_abs]
        exact ⟨hρ, by rw [abs_of_pos hτ.1]; exact hτ.2, hρ⟩
      have hcl := ((hΨg 0 h0B).mono inter_subset_left).mem_closure_image h0cl
      have hval : (Ψ ∘ g) 0 = Ψ x := by
        simp only [Function.comp_apply, hgx]
      rwa [hval] at hcl
  obtain ⟨γ₀, hγ₀, hcγ₀, hloc⟩ :=
    exists_innermost_jordanCurve_of_sides 𝒞 h𝒞 h𝒞d hCp hCo h𝒞C hcC hc𝒞 hside
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hγ₀
  have hJor₀ := hJor J hJ
  have hsep := Schoenflies.jordan_curve_theorem hJor₀
  have hγball : Ψ '' J ⊆ Metric.ball 0 1 :=
    image_subset_iff.mpr fun x hx => hΨb (hJE J hJ hx)
  have hclball := closure_inside_subset_ball hJor₀ hγball
  have hΦimg : ∀ S ⊆ Metric.ball (0 : Schoenflies.Plane) 1, Φ '' S = Ψ ⁻¹' S ∩ Eint e := by
    intro S hS
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨?_, hΦb (hS hp)⟩
      rw [mem_preimage, hΨΦ p (hS hp)]
      exact hp
    · rintro ⟨hy, hyE⟩
      exact ⟨Ψ y, hy, hΦΨ y hyE⟩
  let Din : Set E3 := Ψ ⁻¹' Schoenflies.inside (Ψ '' J) ∩ Eint e
  obtain ⟨W, hW, hWeq⟩ := continuousOn_iff'.mp hΨc _ hsep.isOpen_inside
  have hcell : IsTopologicalCellWithInterior 2 (Din ∪ J) Din := by
    obtain ⟨θ⟩ := PlanarJordan.nonempty_homeomorph_closure_inside hJor₀
    let f : Metric.closedBall (0 : Schoenflies.Plane) 1 → E3 := fun q => Φ (θ.symm q)
    have hfc : Continuous f := hΦc.comp_continuous
      (continuous_subtype_val.comp θ.symm.continuous) fun q => hclball (θ.symm q).2
    have hfi : Function.Injective f := by
      intro q q' hqq'
      have h1 := congrArg Ψ hqq'
      change Ψ (Φ (θ.symm q)) = Ψ (Φ (θ.symm q')) at h1
      rw [hΨΦ _ (hclball (θ.symm q).2), hΨΦ _ (hclball (θ.symm q').2)] at h1
      exact θ.symm.injective (Subtype.ext h1)
    have _ : CompactSpace (Metric.closedBall (0 : Schoenflies.Plane) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
    have hemb := (hfc.isClosedEmbedding hfi).isEmbedding
    have hrange : range f = Din ∪ J := by
      have h1 : range f = Φ '' closure (Schoenflies.inside (Ψ '' J)) := by
        have hf : f = Φ ∘ (Subtype.val ∘ θ.symm) := rfl
        rw [hf, range_comp, range_comp, θ.symm.surjective.range_eq, image_univ,
          Subtype.range_coe]
      rw [h1, hΦimg _ hclball, closure_inside_eq_union hJor₀, preimage_union,
        union_inter_distrib_right]
      congr 1
      ext y
      constructor
      · rintro ⟨hy, hyE⟩
        exact (hmemE (hJE J hJ) y hyE).mp hy
      · intro hy
        exact ⟨⟨y, hy, rfl⟩, hJE J hJ hy⟩
    refine ⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hrange), ?_⟩
    rw [← image_comp]
    have hcomp : (Subtype.val ∘ (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange))) = f := by
      funext q
      rfl
    rw [hcomp]
    have hfr := PlanarJordan.frontier_closure_inside hJor₀
    have hint : interior (closure (Schoenflies.inside (Ψ '' J))) =
        Schoenflies.inside (Ψ '' J) := by
      have hJfr : Schoenflies.IsJordanCurve (frontier (closure (Schoenflies.inside (Ψ '' J)))) := by
        rw [hfr]
        exact hJor₀
      have hne : (interior (closure (Schoenflies.inside (Ψ '' J)))).Nonempty :=
        hsep.isConnected_inside.nonempty.mono (interior_maximal subset_closure hsep.isOpen_inside)
      have hi := PlanarJordan.interior_eq_inside_frontier_of_isCompact
        hsep.isBounded_inside.isCompact_closure hJfr hne
      rwa [hfr] at hi
    have hball' : (Subtype.val : Metric.closedBall (0 : Schoenflies.Plane) 1 →
        Schoenflies.Plane) ⁻¹' Metric.ball 0 1 =
          {q : Metric.closedBall (0 : Schoenflies.Plane) 1 | ‖(q : Schoenflies.Plane)‖ < 1} := by
      ext q
      simp only [mem_preimage, mem_ball_zero_iff, mem_ofPred_eq]
    calc Din = Φ '' Schoenflies.inside (Ψ '' J) :=
          (hΦimg _ (subset_closure.trans hclball)).symm
      _ = Φ '' (closedBallParam θ '' ((Subtype.val : Metric.closedBall (0 : Schoenflies.Plane) 1 →
            Schoenflies.Plane) ⁻¹' Metric.ball 0 1)) := by
          rw [← interior_eq_image_of_homeomorphClosedBall θ, hint]
      _ = f '' {q | ‖(q : Schoenflies.Plane)‖ < 1} := by
          rw [hball', image_image]
          rfl
  have hloc' : ∀ x ∈ J, ∃ Wx : Set E3, IsOpen Wx ∧ x ∈ Wx ∧ ∀ y ∈ Wx ∩ Eint e,
      (y ∈ XK.space ↔ y ∈ Din ∪ J) ∧ (y ∈ frontier XK.space ↔ y ∈ J) := by
    intro x hx
    have hxE := hJE J hJ hx
    obtain ⟨V, hV, hVeq⟩ := hloc (Ψ x) ⟨x, hx, rfl⟩
    have hpre : Ψ ⁻¹' V ∈ 𝓝[Eint e] x := (hΨc.continuousWithinAt hxE).preimage_mem_nhdsWithin hV
    obtain ⟨u, hu, hux⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hpre
    let Oth : Set E3 := (⋃ J' ∈ 𝒥.erase J, J')ᶜ
    have hOth : IsOpen Oth := (isClosed_biUnion_finset fun J' hJ' =>
      (h𝒥 J' (Finset.mem_of_mem_erase hJ')).isPolyhedron.isCompact.isClosed).isOpen_compl
    have hxOth : x ∈ Oth := by
      simp only [Oth, mem_compl_iff, mem_iUnion, not_exists]
      intro J' hJ' hxJ'
      exact Set.disjoint_left.mp (h𝒥d J' (Finset.mem_of_mem_erase hJ') J hJ
        (Finset.ne_of_mem_erase hJ')) hxJ' hx
    refine ⟨interior u ∩ Oth, isOpen_interior.inter hOth,
      ⟨mem_interior_iff_mem_nhds.mpr hu, hxOth⟩, ?_⟩
    rintro y ⟨⟨hyu, hyO⟩, hyE⟩
    have hyV : Ψ y ∈ V := hux ⟨interior_subset hyu, hyE⟩
    constructor
    · have h1 : y ∈ XK.space ↔ Ψ y ∈ Cp :=
        ⟨fun hyX => ⟨y, ⟨hyE, hyX⟩, rfl⟩, fun hC => ((hmemE inter_subset_left y hyE).mp hC).2⟩
      have h2' : Ψ y ∈ Cp ↔ Ψ y ∈ Schoenflies.inside (Ψ '' J) ∪ Ψ '' J := by
        constructor
        · intro hC
          have hCV : Ψ y ∈ Cp ∩ V := ⟨hC, hyV⟩
          rw [hVeq] at hCV
          exact hCV.1
        · intro hI
          have hIV : Ψ y ∈ (Schoenflies.inside (Ψ '' J) ∪ Ψ '' J) ∩ V := ⟨hI, hyV⟩
          rw [← hVeq] at hIV
          exact hIV.1
      rw [h1, h2']
      constructor
      · rintro (hI | hγ)
        · exact Or.inl ⟨hI, hyE⟩
        · exact Or.inr ((hmemE (hJE J hJ) y hyE).mp hγ)
      · rintro (hD | hJy)
        · exact Or.inl hD.1
        · exact Or.inr ⟨y, hJy, rfl⟩
    · constructor
      · intro hfr
        have hyT : y ∈ Ec e ∩ frontier XK.space := ⟨hEEc hyE, hfr⟩
        rw [← h𝒥U] at hyT
        obtain ⟨J', hJ', hyJ'⟩ := mem_iUnion₂.mp hyT
        by_cases hJJ : J' = J
        · rw [hJJ] at hyJ'
          exact hyJ'
        · exact (hyO (mem_iUnion₂.mpr ⟨J', Finset.mem_erase.mpr ⟨hJJ, hJ'⟩, hyJ'⟩)).elim
      · intro hyJ
        exact (hJT J hJ hyJ).2
  choose! Wx hWxo hxWx hWx using hloc'
  refine ⟨J, Din, ⋃ x ∈ J, Wx x, h𝒥 J hJ, hJT J hJ, inter_subset_right, ?_, ⟨W, hW, hWeq⟩,
    ⟨hcγ₀, hPE⟩, hcell, isOpen_biUnion fun x hx => hWxo x hx,
    fun x hx => mem_iUnion₂.mpr ⟨x, hx, hxWx x hx⟩, ?_⟩
  · refine Set.disjoint_left.mpr fun y hyD hyJ => ?_
    exact Schoenflies.inside_subset_compl hyD.1 ⟨y, hyJ, rfl⟩
  · rintro y ⟨hyO, hyE⟩
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.mp hyO
    exact hWx x hx y ⟨hyx, hyE⟩

end OuterTrace

end DifferentialGeometry.Topology.PiecewiseLinear
