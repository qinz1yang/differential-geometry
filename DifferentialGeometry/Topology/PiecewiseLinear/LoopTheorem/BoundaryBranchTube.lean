/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchTubeCharts
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryBranchArc
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryAdaptation

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem nonempty_plSeamTubeChart_of_isPLHomeomorphOn (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {g : (ℝ × ℝ) × ℝ → E} {N' : Set ((ℝ × ℝ) × ℝ)} {Ω : Set E}
      {chart : (ℝ × ℝ) × ℝ → L.space}, IsOpen N' → IsOpen Ω →
        IsPLHomeomorphOn g N' (L.space ∩ Ω) → spliceCylinder ⊆ N' →
          (∀ p ∈ spliceCylinder, (chart p : E) = g p) →
            Nonempty (PLSeamTubeChart L.space chart) := by
  let _ := combinatorialChartedSpace L hL
  intro g N' Ω chart hN' hΩ hg hcyl hchart
  obtain ⟨K, hKfin, hKspace⟩ := isHPolytope_spliceCylinder.isPolyhedron.exists_simplicialComplex
  have hcylpoly : IsPolyhedron spliceCylinder := isHPolytope_spliceCylinder.isPolyhedron
  have hinj : InjOn chart spliceCylinder := fun p hp q hq hpq =>
    hg.bijOn.injOn (hcyl hp) (hcyl hq) (by
      rw [← hchart p hp, ← hchart q hq, hpq])
  have hcont : ContinuousOn chart spliceCylinder := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact (hg.isPiecewiseAffineOn.continuousOn.mono hcyl).congr fun p hp => hchart p hp
  refine ⟨⟨⟨K, hKfin, chart, hKspace ▸ hinj.bijOn_image, hKspace ▸ hcont, ?_, ?_⟩,
    hKspace, rfl⟩⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := mem_combinatorialChartedSpace_atlas L hL he
    have hpa := isPiecewiseAffineOn_vertexChart L hq (hL.isPLSphere_link hq)
    have hcomp := (hpa.comp hg.isPiecewiseAffineOn).inter_of_isPolyhedron hcylpoly
    rw [hKspace]
    have hseteq : (N' ∩ g ⁻¹' (Subtype.val '' (vertexChart L hq (hL.isPLSphere_link hq)).source))
        ∩ spliceCylinder =
        spliceCylinder ∩ chart ⁻¹' (vertexChart L hq (hL.isPLSphere_link hq)).source := by
      ext p
      constructor
      · rintro ⟨⟨-, hp⟩, hpc⟩
        refine ⟨hpc, ?_⟩
        obtain ⟨w, hw, hwp⟩ := hp
        have hcp : chart p = w := Subtype.ext ((hchart p hpc).trans hwp.symm)
        change chart p ∈ (vertexChart L hq (hL.isPLSphere_link hq)).source
        rw [hcp]
        exact hw
      · rintro ⟨hpc, hp⟩
        exact ⟨⟨hcyl hpc, chart p, hp, hchart p hpc⟩, hpc⟩
    rw [hseteq] at hcomp
    refine hcomp.congr fun p hp => ?_
    have hgp : g p ∈ L.space := (hg.bijOn.mapsTo (hcyl hp.1)).1
    change (vertexChart L hq (hL.isPLSphere_link hq)) (chart p) =
      (if h : g p ∈ L.space then (vertexChart L hq (hL.isPLSphere_link hq)) ⟨g p, h⟩ else 0)
    rw [dite_eq_left hgp]
    congr 1
    exact Subtype.ext (hchart p hp.1)
  · intro e he
    obtain ⟨q, hq, rfl⟩ := mem_combinatorialChartedSpace_atlas L hL he
    set ev := vertexChart L hq (hL.isPLSphere_link hq) with hev
    rw [hKspace]
    have hsymm := isPiecewiseAffineOn_vertexChart_symm L hq (hL.isPLSphere_link hq)
    have hcomp := (hg.isPiecewiseAffineOn_invFunOn.comp hsymm).inter_preimage_of_isPolyhedron
      hcylpoly
    have hseteq : (ev.target ∩ (fun y => (ev.symm y : E)) ⁻¹' (L.space ∩ Ω)) ∩
        (Function.invFunOn g N' ∘ fun y => (ev.symm y : E)) ⁻¹' spliceCylinder =
        ev.target ∩ ev.symm ⁻¹' (chart '' spliceCylinder) := by
      ext y
      constructor
      · rintro ⟨⟨hy, hyΩ⟩, hyc⟩
        refine ⟨hy, _, hyc, ?_⟩
        apply Subtype.ext
        rw [hchart _ hyc]
        exact hg.bijOn.invOn_invFunOn.2 hyΩ
      · rintro ⟨hy, p, hpc, hpy⟩
        have hval : (ev.symm y : E) = g p := by rw [← hpy, hchart p hpc]
        have hmem : (ev.symm y : E) ∈ L.space ∩ Ω := by
          rw [hval]
          exact hg.bijOn.mapsTo (hcyl hpc)
        refine ⟨⟨hy, hmem⟩, ?_⟩
        change Function.invFunOn g N' (ev.symm y : E) ∈ spliceCylinder
        rw [hval, hg.bijOn.injOn.leftInvOn_invFunOn (hcyl hpc)]
        exact hpc
    rw [hseteq] at hcomp
    refine hcomp.congr fun y hy => ?_
    obtain ⟨p, hpc, hpy⟩ := hy.2
    have hval : (ev.symm y : E) = g p := by rw [← hpy, hchart p hpc]
    change Function.invFunOn chart spliceCylinder (ev.symm y) =
      Function.invFunOn g N' (ev.symm y : E)
    rw [hval, hg.bijOn.injOn.leftInvOn_invFunOn (hcyl hpc), ← hpy]
    exact hinj.leftInvOn_invFunOn hpc

theorem norm_fst_le_one_of_mem_spliceCylinder {p : (ℝ × ℝ) × ℝ} (hp : p ∈ spliceCylinder) :
    ‖p.1‖ ≤ 1 := by
  obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hp
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_le (abs_le.mpr ⟨h1, h2⟩) (abs_le.mpr ⟨h3, h4⟩)

open Classical in
theorem exists_plSeamTube_of_straightening (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    ∀ {D : SingularTwoCell L.space} {BdM B W : Set L.space} (hD : NormalSingularCellData D BdM B)
      (c : hD.singularSet.Branch) {Φ : (ℝ × ℝ) × ℝ → E} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set E}
      {τ : ℝ}, IsOpen N → IsOpen Ω → IsPLHomeomorphOn Φ N (L.space ∩ Ω) → 0 < τ →
        coreSegment τ ⊆ N → Φ '' coreSegment τ = Subtype.val '' hD.singularSet.branchCarrier c →
        (∀ p ∈ N, Φ p ∈ Subtype.val '' (D '' D.domain) ↔
          p ∈ crossPlanes ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) →
        (∀ p ∈ N, Φ p ∈ Subtype.val '' doublePointSet D D.domain ↔
          p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ) →
        (∀ p ∈ N, Φ p ∈ Subtype.val '' W ↔ 0 ≤ p.2 ∧ p.2 ≤ τ) →
        (∀ p ∈ N, Φ p ∈ Subtype.val '' BdM ↔ p.2 = 0 ∨ p.2 = τ) →
        (∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) →
        ∃ (U : Set L.space) (T : CrossSeamTubeData hD c U),
          Nonempty (PLSeamTubeChart L.space T.chart) ∧ T.chart '' spliceCylinder ⊆ W ∧
            T.chart '' spliceCylinder ∩ BdM = T.chart '' spliceEndDisks ∧
              ∀ z ∈ T.chart '' spliceEndDisks, B ∈ 𝓝[BdM] z := by
  let _ := combinatorialChartedSpace L hL
  intro D BdM B W hD c Φ N Ω τ hN hΩ hΦ hτ hcore hcoreimg hZ hDP hW hBd hbuf
  have hΦS : ∀ p ∈ N, Φ p ∈ L.space := fun p hp => (hΦ.bijOn.mapsTo hp).1
  have hΦcont : ContinuousOn Φ N := hΦ.isPiecewiseAffineOn.continuousOn
  have hend : ∀ q ∈ coreSegment τ, q.2 = 0 ∨ q.2 = τ → ∃ δ > 0, ∃ u : Set L.space,
      IsOpen u ∧ u ∩ BdM ⊆ B ∧ ∀ p ∈ ball q δ, p ∈ N ∧ Φ p ∈ Subtype.val '' u := by
    intro q hq hq2
    have hqN := hcore hq
    set m : L.space := ⟨Φ q, hΦS q hqN⟩ with hmdef
    have hmBd : m ∈ BdM := by
      obtain ⟨w, hw, hwq⟩ := (hBd q hqN).mpr hq2
      rwa [show m = w from Subtype.ext hwq.symm]
    have hmDP : m ∈ doublePointSet D D.domain := by
      obtain ⟨w, hw, hwq⟩ := (hDP q hqN).mpr ⟨hq.1, hq.2.1, hq.2.2⟩
      rwa [show m = w from Subtype.ext hwq.symm]
    have hmrange : m ∈ Set.range D.boundary := by
      rw [← hD.image_inter_boundary]
      obtain ⟨x, hx, -, -, -, hxm, -⟩ := hmDP
      exact ⟨⟨x, hx, hxm⟩, hmBd⟩
    obtain ⟨u, hu, hmu, huB⟩ := mem_nhdsWithin.mp (hbuf m hmrange)
    obtain ⟨Ωu, hΩu, hΩueq⟩ := isOpen_induced_iff.mp hu
    have hq' : Φ q ∈ Ωu := by
      have : m ∈ Subtype.val ⁻¹' Ωu := by rw [hΩueq]; exact hmu
      exact this
    have hpre : N ∩ Φ ⁻¹' Ωu ∈ 𝓝 q :=
      Filter.inter_mem (hN.mem_nhds hqN) ((hΦcont.continuousAt (hN.mem_nhds hqN)).preimage_mem_nhds
        (hΩu.mem_nhds hq'))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨δ, hδ, u, hu, huB, fun p hp => ⟨(hball hp).1, ?_⟩⟩
    refine ⟨⟨Φ p, hΦS p (hball hp).1⟩, ?_, rfl⟩
    have : (⟨Φ p, hΦS p (hball hp).1⟩ : L.space) ∈ Subtype.val ⁻¹' Ωu := (hball hp).2
    rwa [hΩueq] at this
  obtain ⟨δ₀, hδ₀, u₀, hu₀, hu₀B, hball₀⟩ :=
    hend ((0, 0), 0) ⟨rfl, le_rfl, hτ.le⟩ (Or.inl rfl)
  obtain ⟨δ₁, hδ₁, u₁, hu₁, hu₁B, hball₁⟩ :=
    hend ((0, 0), τ) ⟨rfl, hτ.le, le_rfl⟩ (Or.inr rfl)
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_coreSegment τ).exists_thickening_subset_open hN hcore
  set ε := min δ (min δ₀ δ₁) / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hεδ : ε < δ := by
    have := min_le_left δ (min δ₀ δ₁)
    rw [hεdef]
    linarith
  have hεδ₀ : ε < δ₀ := by
    have := (min_le_right δ (min δ₀ δ₁)).trans (min_le_left δ₀ δ₁)
    rw [hεdef]
    linarith
  have hεδ₁ : ε < δ₁ := by
    have := (min_le_right δ (min δ₀ δ₁)).trans (min_le_right δ₀ δ₁)
    rw [hεdef]
    linarith
  set sc : ((ℝ × ℝ) × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) × ℝ :=
    (LinearEquiv.smulOfNeZero ℝ (ℝ × ℝ) ε hε.ne').prodCongr
      (LinearEquiv.smulOfNeZero ℝ ℝ τ hτ.ne') with hscdef
  have hscapp : ∀ p : (ℝ × ℝ) × ℝ, sc p = (ε • p.1, τ * p.2) := fun p => by
    rw [hscdef, LinearEquiv.prodCongr_apply, LinearEquiv.smulOfNeZero_apply,
      LinearEquiv.smulOfNeZero_apply, smul_eq_mul]
  have hsccont : Continuous (fun p => sc p) := sc.toContinuousLinearEquiv.continuous
  set N' := (fun p => sc p) ⁻¹' N with hN'def
  have hN' : IsOpen N' := hN.preimage hsccont
  have hscN : (fun p => sc p) '' N' = N := image_preimage_eq N sc.surjective
  have hg : IsPLHomeomorphOn (Φ ∘ fun p => sc p) N' (L.space ∩ Ω) := by
    have h := (isPLHomeomorphOn_linearEquiv_image sc hN').2
    rw [hscN] at h
    exact h.trans hΦ
  have hdist : ∀ p ∈ spliceCylinder, sc p ∈ ball (((0 : ℝ), (0 : ℝ)), τ * p.2) δ ∧
      ‖(sc p).1‖ ≤ ε := by
    intro p hp
    have hn := norm_fst_le_one_of_mem_spliceCylinder hp
    have h1 : ‖(sc p).1‖ ≤ ε := by
      rw [hscapp, norm_smul, Real.norm_of_nonneg hε.le]
      nlinarith [norm_nonneg p.1]
    refine ⟨?_, h1⟩
    rw [mem_ball, Prod.dist_eq, hscapp]
    apply max_lt
    · rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
      rw [hscapp] at h1
      linarith
    · rw [dist_self]
      exact hδ
  have hcyl : ∀ p ∈ spliceCylinder, sc p ∈ N ∧ 0 ≤ (sc p).2 ∧ (sc p).2 ≤ τ := by
    intro p hp
    have h2 : 0 ≤ p.2 ∧ p.2 ≤ 1 := hp.2
    have hcoreq : (((0 : ℝ), (0 : ℝ)), τ * p.2) ∈ coreSegment τ :=
      ⟨rfl, mul_nonneg hτ.le h2.1, by nlinarith⟩
    refine ⟨hthick (mem_thickening_iff.mpr ⟨_, hcoreq, (hdist p hp).1⟩), ?_, ?_⟩
    · rw [hscapp]
      exact mul_nonneg hτ.le h2.1
    · rw [hscapp]
      nlinarith
  have hcylN' : spliceCylinder ⊆ N' := fun p hp => (hcyl p hp).1
  set m₀ : L.space := ⟨Φ ((0, 0), 0), hΦS _ (hcore ⟨rfl, le_rfl, hτ.le⟩)⟩
  set chart : (ℝ × ℝ) × ℝ → L.space := fun p =>
    if h : Φ (sc p) ∈ L.space then ⟨Φ (sc p), h⟩ else m₀ with hchartdef
  have hchart : ∀ p ∈ spliceCylinder, (chart p : E) = Φ (sc p) := fun p hp => by
    simp only [hchartdef, dite_eq_left (hΦS _ (hcyl p hp).1)]
  have hX : ∀ p ∈ spliceCylinder, sc p ∈ crossPlanes ↔ p ∈ crossingFigure := by
    intro p hp
    change (ε * p.1.1 = 0 ∨ ε * p.1.2 = 0) ↔ _
    simp only [crossingFigure, crossingArcX, crossingArcY, mem_prod, mem_union, mem_sep_iff,
      mul_eq_zero, hε.ne', false_or]
    exact ⟨fun h => ⟨h.imp (fun h' => ⟨hp.1, h'⟩) fun h' => ⟨hp.1, h'⟩, hp.2⟩,
      fun h => h.1.imp (fun h' => h'.2) fun h' => h'.2⟩
  have hcoreiff : ∀ p ∈ spliceCylinder, (sc p).1 = 0 ↔ p ∈ spliceCore := by
    intro p hp
    rw [hscapp]
    change ε • p.1 = 0 ↔ p.1 ∈ ({((0 : ℝ), (0 : ℝ))} : Set (ℝ × ℝ)) ∧ p.2 ∈ Icc 0 1
    rw [smul_eq_zero, or_iff_right hε.ne', mem_singleton_iff, Prod.mk_zero_zero]
    exact ⟨fun h => ⟨h, hp.2⟩, fun h => h.1⟩
  have hendiff : ∀ p ∈ spliceCylinder, ((sc p).2 = 0 ∨ (sc p).2 = τ) ↔ p ∈ spliceEndDisks := by
    intro p hp
    rw [hscapp]
    change (τ * p.2 = 0 ∨ τ * p.2 = τ) ↔ p.1 ∈ spliceSquare ∧ p.2 ∈ ({0, 1} : Set ℝ)
    rw [mem_insert_iff, mem_singleton_iff, mul_eq_zero, or_iff_right hτ.ne']
    have h1 : τ * p.2 = τ ↔ p.2 = 1 := by
      constructor
      · intro h
        have := mul_left_cancel₀ hτ.ne' (h.trans (mul_one τ).symm)
        exact this
      · intro h
        rw [h, mul_one]
    rw [h1]
    exact ⟨fun h => ⟨hp.1, h⟩, fun h => h.2⟩
  have hinjchart : InjOn chart spliceCylinder := fun p hp q hq hpq =>
    hg.bijOn.injOn (hcylN' hp) (hcylN' hq) (by
      change Φ (sc p) = Φ (sc q)
      rw [← hchart p hp, ← hchart q hq, hpq])
  have hvalimg : ∀ S ⊆ spliceCylinder, Subtype.val '' (chart '' S) = Φ '' ((fun p => sc p) '' S) :=
    fun S hS => by
      rw [image_image, image_image]
      exact image_congr fun p hp => hchart p (hS hp)
  have hcoreS : spliceCore ⊆ spliceCylinder := spliceCore_subset_spliceCylinder
  have hscCore : (fun p => sc p) '' spliceCore = coreSegment τ := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hpc := hcoreS hp
      exact ⟨(hcoreiff p hpc).mpr hp, (hcyl p hpc).2.1, (hcyl p hpc).2.2⟩
    · rintro ⟨hq1, hq2, hq3⟩
      refine ⟨((0, 0), q.2 / τ), ⟨rfl, div_nonneg hq2 hτ.le, (div_le_one hτ).mpr hq3⟩, ?_⟩
      change sc ((0, 0), q.2 / τ) = q
      rw [hscapp]
      refine Prod.ext ?_ ?_
      · change ε • ((0 : ℝ), (0 : ℝ)) = q.1
        rw [hq1, Prod.mk_zero_zero, smul_zero]
      · change τ * (q.2 / τ) = q.2
        field_simp
  refine ⟨Subtype.val ⁻¹' Ω, ⟨chart, ⟨continuous_subtype_val.isOpen_preimage Ω hΩ, ?_,
    hinjchart, ?_, ?_, ?_, ?_⟩⟩, ?_, ?_, ?_, ?_⟩
  · rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    exact ((hΦcont.comp hsccont.continuousOn fun p hp => hp).mono hcylN').congr
      fun p hp => hchart p hp
  · rintro _ ⟨p, hp, rfl⟩
    change (chart p : E) ∈ Ω
    rw [hchart p hp]
    exact (hΦ.bijOn.mapsTo (hcyl p hp).1).2
  · apply Subtype.val_injective.image_injective
    change Subtype.val '' (chart '' spliceCore) = _
    rw [hvalimg _ hcoreS, hscCore, hcoreimg]
  · apply Subtype.val_injective.image_injective
    change Subtype.val '' (chart '' crossingFigure) =
      Subtype.val '' (D '' D.domain ∩ chart '' spliceCylinder)
    rw [hvalimg _ crossingFigure_subset_spliceCylinder,
      image_inter Subtype.val_injective, hvalimg _ subset_rfl]
    ext y
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      have hpc := crossingFigure_subset_spliceCylinder hp
      refine ⟨(hZ _ (hcyl p hpc).1).mpr ⟨(hX p hpc).mpr hp, (hcyl p hpc).2⟩, _,
        ⟨p, hpc, rfl⟩, rfl⟩
    · rintro ⟨hyZ, _, ⟨p, hpc, rfl⟩, rfl⟩
      have h := ((hZ _ (hcyl p hpc).1).mp hyZ).1
      exact ⟨_, ⟨p, (hX p hpc).mp h, rfl⟩, rfl⟩
  · ext z
    constructor
    · rintro ⟨hzD, hzΩ⟩
      have hzmem : (z : E) ∈ L.space ∩ Ω := ⟨z.2, hzΩ⟩
      obtain ⟨p, hpN, hpz⟩ := hΦ.bijOn.surjOn hzmem
      have hpD : Φ p ∈ Subtype.val '' doublePointSet D D.domain := ⟨z, hzD, hpz.symm⟩
      have hpcore := (hDP p hpN).mp hpD
      have hmem : Φ p ∈ Φ '' coreSegment τ := ⟨p, hpcore, rfl⟩
      rw [hcoreimg, hpz] at hmem
      exact (Subtype.val_injective.mem_set_image).mp hmem
    · intro hz
      refine ⟨hD.singularSet.branchCarrier_subset_doublePointSet c hz, ?_⟩
      have hmem : (z : E) ∈ Φ '' coreSegment τ := by
        rw [hcoreimg]
        exact ⟨z, hz, rfl⟩
      obtain ⟨p, hp, hpz⟩ := hmem
      change (z : E) ∈ Ω
      rw [← hpz]
      exact (hΦ.bijOn.mapsTo (hcore hp)).2
  · exact nonempty_plSeamTubeChart_of_isPLHomeomorphOn L hL hN' hΩ hg hcylN' hchart
  · rintro _ ⟨p, hp, rfl⟩
    have h := (hW _ (hcyl p hp).1).mpr (hcyl p hp).2
    rw [← hchart p hp] at h
    exact (Subtype.val_injective.mem_set_image).mp h
  · ext z
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hzB⟩
      have h : Φ (sc p) ∈ Subtype.val '' BdM := by
        rw [← hchart p hp]
        exact ⟨_, hzB, rfl⟩
      exact ⟨p, (hendiff p hp).mp ((hBd _ (hcyl p hp).1).mp h), rfl⟩
    · rintro ⟨p, hp, rfl⟩
      have hpc := spliceEndDisks_subset_spliceCylinder hp
      refine ⟨⟨p, hpc, rfl⟩, ?_⟩
      have h := (hBd _ (hcyl p hpc).1).mpr ((hendiff p hpc).mpr hp)
      rw [← hchart p hpc] at h
      exact (Subtype.val_injective.mem_set_image).mp h
  · rintro _ ⟨p, hp, rfl⟩
    have hpc := spliceEndDisks_subset_spliceCylinder hp
    have hp2 : p.2 = 0 ∨ p.2 = 1 := by
      rcases hp.2 with h | h
      · exact Or.inl h
      · exact Or.inr (mem_singleton_iff.mp h)
    have hn := (hdist p hpc).2
    rcases hp2 with h0 | h1
    · have hb : sc p ∈ ball (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) δ₀ := by
        rw [mem_ball, Prod.dist_eq]
        apply max_lt
        · rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
          linarith
        · rw [hscapp, h0, mul_zero, dist_self]
          exact hδ₀
      obtain ⟨-, w, hw, hwp⟩ := hball₀ _ hb
      have hcw : chart p = w := Subtype.ext ((hchart p hpc).trans hwp.symm)
      change B ∈ 𝓝[BdM] chart p
      rw [hcw]
      exact mem_nhdsWithin.mpr ⟨u₀, hu₀, hw, hu₀B⟩
    · have hb : sc p ∈ ball (((0 : ℝ), (0 : ℝ)), τ) δ₁ := by
        rw [mem_ball, Prod.dist_eq]
        apply max_lt
        · rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
          linarith
        · rw [hscapp, h1, mul_one, dist_self]
          exact hδ₁
      obtain ⟨-, w, hw, hwp⟩ := hball₁ _ hb
      have hcw : chart p = w := Subtype.ext ((hchart p hpc).trans hwp.symm)
      change B ∈ 𝓝[BdM] chart p
      rw [hcw]
      exact mem_nhdsWithin.mpr ⟨u₁, hu₁, hw, hu₁B⟩

open Classical in
theorem isPLBoundaryTubeProducer_of_exists_endChart (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsCombinatorialManifold 3 L) :
    letI := combinatorialChartedSpace L hL
    (∀ (D : SingularTwoCell L.space) (BdM B W : Set L.space), NormalSingularCellData D BdM B →
      IsPLBoundarySide D W BdM → ∀ y ∈ doublePointSet D D.domain, y ∈ BdM →
        ∃ (ψ : (ℝ × ℝ) × ℝ → E) (V : Set ((ℝ × ℝ) × ℝ)) (Ω : Set E), IsOpen V ∧ IsOpen Ω ∧
          IsPLHomeomorphOn ψ V (L.space ∩ Ω) ∧ (0 : (ℝ × ℝ) × ℝ) ∈ V ∧ ψ 0 = y ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes ∧ 0 ≤ p.2) ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' doublePointSet D D.domain ↔ p.1 = 0 ∧ 0 ≤ p.2) ∧
            (∀ p ∈ V, ψ p ∈ Subtype.val '' W ↔ 0 ≤ p.2) ∧
            ∀ p ∈ V, ψ p ∈ Subtype.val '' BdM ↔ p.2 = 0) →
      IsPLBoundaryTubeProducer L.space := by
  let _ := combinatorialChartedSpace L hL
  intro hend D BdM B W hD c hc hside hbuf
  obtain ⟨γ, hγc, hγi, hγimg, hγ0, hγ1, hγint⟩ :=
    hD.singularSet.exists_arc_of_isBoundaryBranch hc
  have hγAc : ContinuousOn (fun r => (γ r : E)) (Icc 0 1) :=
    continuous_subtype_val.comp_continuousOn hγc
  have hγAi : InjOn (fun r => (γ r : E)) (Icc 0 1) := fun r hr s hs h =>
    hγi hr hs (Subtype.ext h)
  have hγDP : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ doublePointSet D D.domain := fun r hr =>
    hD.singularSet.branchCarrier_subset_doublePointSet c (hγimg ▸ mem_image_of_mem γ hr)
  obtain ⟨ψ₀, V₀, Ω₀, hV₀, hΩ₀, hψ₀, h0V₀, hψ₀0, hψ₀Z, hψ₀D, hψ₀W, hψ₀Bd⟩ :=
    hend D BdM B W hD hside (γ 0) (hγDP 0 ⟨le_rfl, zero_le_one⟩) hγ0
  obtain ⟨ψ, V, Ω₁, hV, hΩ₁, hψ, h0V, hψ0, hψZ, hψD, hψW, hψBd⟩ :=
    hend D BdM B W hD hside (γ 1) (hγDP 1 ⟨zero_le_one, le_rfl⟩) hγ1
  have hcont : Continuous axisFlip := continuous_fst.prodMk continuous_snd.neg
  have hψ₁ : IsPLHomeomorphOn (ψ ∘ axisFlip) (axisFlip ⁻¹' V) (L.space ∩ Ω₁) :=
    (isPLHomeomorphOn_axisFlip hV).trans hψ
  have hγ1Ω₁ : (γ 1 : E) ∈ Ω₁ := by
    have h := hψ.bijOn.mapsTo h0V
    rw [hψ0] at h
    exact h.2
  have hint : ∀ r ∈ Ioo (0 : ℝ) 1, ∃ (ψ' : (ℝ × ℝ) × ℝ → E) (V' : Set ((ℝ × ℝ) × ℝ))
      (Ω' : Set E), IsOpen V' ∧ IsOpen Ω' ∧ IsPLHomeomorphOn ψ' V' (L.space ∩ Ω') ∧
        (γ r : E) ∈ Ω' ∧ (∀ p ∈ V', ψ' p ∈ Subtype.val '' (D '' D.domain) ↔ p ∈ crossPlanes) ∧
        (∀ p ∈ V', ψ' p ∈ Subtype.val '' doublePointSet D D.domain ↔ p.1 = 0) ∧
        (∀ p ∈ V', ψ' p ∈ Subtype.val '' W) ∧ ∀ p ∈ V', ψ' p ∉ Subtype.val '' BdM := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
    have hyBd := hγint r hr
    have hO : IsOpen (interior W ∩ BdMᶜ) := isOpen_interior.inter hside.2.2.1.isOpen_compl
    have hyO : γ r ∈ interior W ∩ BdMᶜ := by
      refine ⟨?_, hyBd⟩
      obtain ⟨x, hx, -, -, -, hxy, -⟩ := hγDP r hrI
      apply hside.2.2.2.1
      refine ⟨x, ⟨hx, fun hxf => hyBd ?_⟩, hxy⟩
      rw [← hD.preimage_boundary_eq_frontier] at hxf
      rw [← hxy]
      exact hxf.2
    obtain ⟨ψ', V', Ω', hV', hΩ', hψ', hyΩ', hZ', hD', hO'⟩ :=
      exists_straighteningChart_of_notMem_boundary L hL hD (hγDP r hrI) hyBd hO hyO
    refine ⟨ψ', V', Ω', hV', hΩ', hψ', hyΩ', hZ', hD', fun p hp => ?_, fun p hp => ?_⟩
    · obtain ⟨w, hw, hwp⟩ := hO' p hp
      exact ⟨w, interior_subset hw.1, hwp⟩
    · rintro ⟨w, hw, hwp⟩
      obtain ⟨w', hw', hw'p⟩ := hO' p hp
      have hww : w = w' := Subtype.ext (hwp.trans hw'p.symm)
      exact hw'.2 (hww ▸ hw)
  obtain ⟨Φ, N, Ω, τ, hN, hΩ, hΦ, hτ, hcore, hcoreimg, hZ, hDP, hW, hBd⟩ :=
    exists_arcStraightening (S := L.space) (Z := Subtype.val '' (D '' D.domain))
      (D := Subtype.val '' doublePointSet D D.domain) (W := Subtype.val '' W)
      (Bd := Subtype.val '' BdM) hγAc hγAi (fun r _ => (γ r).2)
      (fun r hr => ⟨γ r, hγDP r hr, rfl⟩) ⟨γ 1, hγ1, rfl⟩ hV₀ hΩ₀ hψ₀ h0V₀ hψ₀0 hψ₀Z hψ₀D
      hψ₀W hψ₀Bd (hV.preimage hcont) hΩ₁ hψ₁ hγ1Ω₁
      (fun p hp => by
        rw [Function.comp_apply, hψZ _ hp]
        exact and_congr Iff.rfl neg_nonneg)
      (fun p hp => by
        rw [Function.comp_apply, hψD _ hp]
        exact and_congr Iff.rfl neg_nonneg)
      (fun p hp => by
        rw [Function.comp_apply, hψW _ hp]
        exact neg_nonneg)
      (fun p hp => by
        rw [Function.comp_apply, hψBd _ hp]
        exact neg_eq_zero)
      hint
  have hcoreimg' : Φ '' coreSegment τ = Subtype.val '' hD.singularSet.branchCarrier c := by
    rw [hcoreimg, ← hγimg, image_image]
  exact exists_plSeamTube_of_straightening L hL hD c hN hΩ hΦ hτ hcore hcoreimg' hZ hDP hW hBd
    hbuf

end DifferentialGeometry.Topology.PiecewiseLinear
