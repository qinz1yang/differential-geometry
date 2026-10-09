/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskCrosscutExtension
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskTheta
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellArcDiskSides

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section ArcStep

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_arcStep
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    {Δ : Set E3} (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, ∃ q : (Fin 2 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S ∧
      q '' stdSimplexBoundary 1 = S ∩ frontier XK.space)
    (hne : Cs.Nonempty) :
    ∃ (Δ' : Set E3) (Cs' : Set (Set E3)),
      IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Cs' ⊆ Cs ∧ Cs' ≠ Cs ∧
        Δ' ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs' := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  obtain ⟨r, hr, hΔsub, hΔB, hb, hnull⟩ := id hΔ
  have hCsI : ∀ S ∈ Cs, ∃ g : ℝ → E3, IsPLHomeomorphOn g (Icc 0 1) S ∧
      ({g 0, g 1} : Set E3) = S ∩ frontier XK.space := fun S hS => by
    obtain ⟨q, hq, hqb⟩ := hCs S hS
    exact exists_isPLHomeomorphOn_Icc_of_stdSimplex_one hq hqb
  have hCsΔ : ∀ S ∈ Cs, S ⊆ Δ := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).1
  have hCsA : ∀ S ∈ Cs, S ⊆ A := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).2
  have hCspoly : ∀ S ∈ Cs, IsPolyhedron S := fun S hS => by
    obtain ⟨g, hg, -⟩ := hCsI S hS
    exact IsPLBall.isPolyhedron (n := 1) ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hg)
  have hCspre : ∀ S ∈ Cs, IsPreconnected S := fun S hS => by
    obtain ⟨g, hg, -⟩ := hCsI S hS
    rw [← hg.image_eq]
    exact (convex_Icc (0 : ℝ) 1).isPreconnected.image g hg.isPiecewiseAffineOn.continuousOn
  have hV : IsOpen (interior N' \ h '' K.space) :=
    isOpen_interior.sdiff hd.tube.isCompact_image_space.isClosed
  obtain ⟨Pl, ρ, hPl, hρ, hρb⟩ := hr.exists_planarModel
  set σρ := Function.invFunOn ρ Pl with hσρdef
  have hσρ : IsPLHomeomorphOn σρ Δ Pl := hρ.symm
  have hρσ : ∀ y ∈ Δ, ρ (σρ y) = y := fun y hy => hρ.bijOn.invOn_invFunOn.2 hy
  have hσρρ : ∀ x ∈ Pl, σρ (ρ x) = x := fun x hx => hρ.bijOn.invOn_invFunOn.1 hx
  have hρc : ContinuousOn ρ Pl := hρ.isPiecewiseAffineOn.continuousOn
  have hσρc : ContinuousOn σρ Δ := hσρ.isPiecewiseAffineOn.continuousOn
  have hρinj : InjOn ρ Pl := hρ.bijOn.injOn
  have hPlc : IsCompact Pl := hPl.isPolyhedron.isCompact
  have hPlcl : IsClosed Pl := hPlc.isClosed
  have hfrPl : frontier Pl ⊆ Pl := hPlcl.frontier_subset
  have hPlΔ : ∀ {T : Set (EuclideanSpace ℝ (Fin 2))}, T ⊆ Pl → ρ '' T ⊆ Δ :=
    fun hT => (image_mono hT).trans hρ.image_eq.subset
  have hbdry : ∀ y ∈ Δ, (y ∈ frontier XK.space ↔ σρ y ∈ frontier Pl) := by
    intro y hy
    constructor
    · intro hyX
      have hy' : y ∈ ρ '' frontier Pl := by
        rw [hρb, ← hΔB]
        exact ⟨hy, hyX⟩
      obtain ⟨x, hx, rfl⟩ := hy'
      rwa [hσρρ x (hfrPl hx)]
    · intro hx
      have h1 : y ∈ Δ ∩ frontier XK.space := by
        rw [hΔB, ← hρb]
        exact ⟨σρ y, hx, hρσ y hy⟩
      exact h1.2
  have hρσimg : ∀ S ∈ Cs, ρ '' (σρ '' S) = S := by
    intro S hS
    rw [image_image]
    exact (image_congr fun y hy => hρσ y (hCsΔ S hS hy)).trans (image_id' S)
  have hside : Δ \ frontier XK.space ⊆ interior XK.space ∨
      Δ \ frontier XK.space ⊆ XK.spaceᶜ := by
    have heq : Δ \ frontier XK.space = ρ '' interior Pl := by
      ext y
      constructor
      · rintro ⟨hy, hyX⟩
        refine ⟨σρ y, ?_, hρσ y hy⟩
        rw [← self_sdiff_frontier]
        exact ⟨hσρ.bijOn.mapsTo hy, fun h' => hyX ((hbdry y hy).mpr h')⟩
      · rintro ⟨x, hx, rfl⟩
        have hxPl := interior_subset hx
        refine ⟨hρ.bijOn.mapsTo hxPl, fun hX => ?_⟩
        have h1 := (hbdry _ (hρ.bijOn.mapsTo hxPl)).mp hX
        rw [hσρρ x hxPl] at h1
        exact Set.disjoint_left.mp disjoint_interior_frontier hx h1
    have hpre : IsPreconnected (Δ \ frontier XK.space) := by
      rw [heq]
      exact hPl.isConnected_interior.isPreconnected.image ρ (hρc.mono interior_subset)
    have hcov : Δ \ frontier XK.space ⊆ interior XK.space ∪ XK.spaceᶜ := fun y hy => by
      by_cases hyi : y ∈ interior XK.space
      · exact Or.inl hyi
      · exact Or.inr fun hyX => hy.2 ⟨subset_closure hyX, hyi⟩
    exact hpre.subset_or_subset isOpen_interior hXc.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcov
  obtain ⟨B₀, hB₀⟩ := hne
  obtain ⟨y₀, hy₀⟩ : B₀.Nonempty := by
    obtain ⟨g, hg, -⟩ := hCsI B₀ hB₀
    exact ⟨g 0, hg.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩⟩
  obtain ⟨e₀, ⟨he₀, hcard₀⟩, hy₀e⟩ := mem_iUnion₂.mp (hCsA B₀ hB₀ hy₀)
  have hB₀e : B₀ ⊆ Ec e₀ := hd.subset_pseudoCell_of_isPreconnected (hCspre B₀ hB₀)
    (hCsA B₀ hB₀) he₀ hcard₀ ⟨y₀, hy₀, hy₀e⟩
  obtain ⟨B, hBCs, B₁, DB, γ₁, rB, hBe, hγ₁, hγ₁e, hB₁X, hBB₁, hrB, hrBb, hDBE, hDBN, hDBX,
    hDBΔ⟩ := h2.exists_arc_eDisk hd h34 he₀ hcard₀ hΔsub hside hfin hdisj hA hCsI hB₀ hB₀e
  obtain ⟨gB, hgB, hgBe⟩ := hCsI B hBCs
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hgB01 : gB 0 ≠ gB 1 := fun h01 => by
    have := hgB.bijOn.injOn h0I h1I h01
    norm_num at this
  obtain ⟨γ₁', hγ₁', hγ₁'0, hγ₁'1⟩ : ∃ γ₁' : ℝ → E3, IsPLHomeomorphOn γ₁' (Icc 0 1) B₁ ∧
      γ₁' 0 = gB 0 ∧ γ₁' 1 = gB 1 := by
    have hset : ({γ₁ 0, γ₁ 1} : Set E3) = {gB 0, gB 1} := hγ₁e.trans hgBe.symm
    have h0 : gB 0 ∈ ({γ₁ 0, γ₁ 1} : Set E3) := hset ▸ Or.inl rfl
    have h1 : gB 1 ∈ ({γ₁ 0, γ₁ 1} : Set E3) := hset ▸ Or.inr rfl
    rcases h0 with h0 | h0
    · refine ⟨γ₁, hγ₁, h0.symm, ?_⟩
      rcases h1 with h1 | h1
      · exact absurd (h0.trans h1.symm) hgB01
      · exact (mem_singleton_iff.mp h1).symm
    · have h0' : gB 0 = γ₁ 1 := mem_singleton_iff.mp h0
      refine ⟨γ₁ ∘ AffineMap.lineMap (k := ℝ) (1 : ℝ) (0 : ℝ), hγ₁.comp_lineMap_one_zero, ?_, ?_⟩
      · simp only [Function.comp_apply, AffineMap.lineMap_apply_zero]
        exact h0'.symm
      · simp only [Function.comp_apply, AffineMap.lineMap_apply_one]
        rcases h1 with h1 | h1
        · exact h1.symm
        · exact absurd (h0'.trans (mem_singleton_iff.mp h1).symm) hgB01
  have hBΔ := hCsΔ B hBCs
  have hBpoly := hCspoly B hBCs
  have hgB' : IsPLHomeomorphOn (σρ ∘ gB) (Icc 0 1) (σρ '' B) :=
    hgB.trans (hσρ.restrict hBpoly hBΔ)
  have hgB0 : gB 0 ∈ B ∩ frontier XK.space := hgBe ▸ Or.inl rfl
  have hgB1 : gB 1 ∈ B ∩ frontier XK.space := hgBe ▸ Or.inr rfl
  have hp'fr : σρ (gB 0) ∈ frontier Pl := (hbdry _ (hBΔ hgB0.1)).mp hgB0.2
  have hq'fr : σρ (gB 1) ∈ frontier Pl := (hbdry _ (hBΔ hgB1.1)).mp hgB1.2
  have hp'q' : σρ (gB 0) ≠ σρ (gB 1) := fun h' =>
    hgB01 (hσρ.bijOn.injOn (hBΔ hgB0.1) (hBΔ hgB1.1) h')
  have harcB' : Schoenflies.IsArcBetween (σρ '' B) (σρ (gB 0)) (σρ (gB 1)) :=
    ⟨σρ ∘ gB, hgB'.isPiecewiseAffineOn.continuousOn, hgB'.bijOn.injOn, hgB'.image_eq, rfl, rfl⟩
  have hBpball : IsPLBall 1 (σρ '' B) := (isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hgB'
  have hBpin : σρ '' B \ {σρ (gB 0), σρ (gB 1)} ⊆ Schoenflies.inside (frontier Pl) := by
    rw [← hPl.interior_eq_inside_frontier]
    rintro _ ⟨⟨y, hy, rfl⟩, hyne⟩
    rw [← self_sdiff_frontier]
    refine ⟨hσρ.bijOn.mapsTo (hBΔ hy), fun hfr => hyne ?_⟩
    have hyX : y ∈ frontier XK.space := (hbdry y (hBΔ hy)).mpr hfr
    have hy2 : y ∈ ({gB 0, gB 1} : Set E3) := hgBe ▸ ⟨hy, hyX⟩
    rcases hy2 with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hJfr : Schoenflies.IsJordanCurve (frontier Pl) :=
    isJordanCurve_of_isPLSphere_one hPl.isPLSphere_frontier
  have hcross : Schoenflies.IsCrosscut (frontier Pl) (σρ '' B) (σρ (gB 0)) (σρ (gB 1)) :=
    ⟨hJfr, harcB', isPolygonal_of_isPLBall_one hBpball, hp'fr, hq'fr, hBpin⟩
  obtain ⟨A₁, A₂, hcutA⟩ := Schoenflies.exists_isCutPair hJfr hp'fr hq'fr hp'q'
  obtain ⟨-, -, hUfr, hVfr⟩ := PlanarJordan.crosscut_regions hJfr harcB' hcutA hBpin
  obtain ⟨hUVu, hUVi⟩ := PlanarJordan.closed_crosscut_regions hJfr harcB' hcutA hBpin
  have hPleq : frontier Pl ∪ Schoenflies.inside (frontier Pl) = Pl := by
    rw [union_comm, ← closure_inside_eq_union hJfr, hPl.closure_inside_frontier]
  rw [hPleq] at hUVu
  have hS₁s := isPLSphere_one_union_of_isCrosscut hPl.isPLSphere_frontier hBpball hcross hcutA
  have hS₂s := isPLSphere_one_union_of_isCrosscut hPl.isPLSphere_frontier hBpball hcross
    hcutA.symm
  have hU := isPLBall_closure_inside_of_isPLSphere_one hS₁s
  have hVb := isPLBall_closure_inside_of_isPLSphere_one hS₂s
  have hfrU := frontier_closure_inside_of_isPLSphere_one hS₁s
  have hfrV := frontier_closure_inside_of_isPLSphere_one hS₂s
  have hssub : ∀ {A₁' A₂' : Set (EuclideanSpace ℝ (Fin 2))},
      Schoenflies.IsCutPair (frontier Pl) (σρ (gB 0)) (σρ (gB 1)) A₁' A₂' → A₁' ⊂ frontier Pl := by
    intro A₁' A₂' hc
    refine ⟨hc.fst_subset, fun hsub => ?_⟩
    obtain ⟨z, hz⟩ := hc.snd.nonempty_diff
    exact hz.2 (hc.inter_eq.subset ⟨hsub (hc.snd_subset hz.1), hz.1⟩)
  have hA₁ball : IsPLBall 1 A₁ :=
    hPl.isPLSphere_frontier.isPLBall_one_of_isClosed_of_isConnected_of_ssubset
      hcutA.fst.isArc.isCompact.isClosed hcutA.fst.isArc.isConnected
      ⟨_, hcutA.fst.left_mem, _, hcutA.fst.right_mem, hp'q'⟩ (hssub hcutA)
  have hA₂ball : IsPLBall 1 A₂ :=
    hPl.isPLSphere_frontier.isPLBall_one_of_isClosed_of_isConnected_of_ssubset
      hcutA.snd.isArc.isCompact.isClosed hcutA.snd.isArc.isConnected
      ⟨_, hcutA.snd.left_mem, _, hcutA.snd.right_mem, hp'q'⟩ (hssub hcutA.symm)
  obtain ⟨a₁, ha₁, ha₁0, ha₁1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA₁ball hcutA.fst
  obtain ⟨a₂, ha₂, ha₂0, ha₂1⟩ := exists_isPLHomeomorphOn_Icc_of_isArcBetween hA₂ball hcutA.snd
  set φ := γ₁' ∘ Function.invFunOn (σρ ∘ gB) (Icc (0 : ℝ) 1) with hφdef
  have hφ : IsPLHomeomorphOn φ (σρ '' B) B₁ := hgB'.symm.trans hγ₁'
  have hφ0 : φ (σρ (gB 0)) = gB 0 := by
    change γ₁' (Function.invFunOn (σρ ∘ gB) (Icc (0 : ℝ) 1) ((σρ ∘ gB) 0)) = gB 0
    rw [hgB'.bijOn.invOn_invFunOn.1 h0I, hγ₁'0]
  have hφ1 : φ (σρ (gB 1)) = gB 1 := by
    change γ₁' (Function.invFunOn (σρ ∘ gB) (Icc (0 : ℝ) 1) ((σρ ∘ gB) 1)) = gB 1
    rw [hgB'.bijOn.invOn_invFunOn.1 h1I, hγ₁'1]
  have hBpfr : σρ '' B ∩ frontier Pl = {σρ (gB 0), σρ (gB 1)} :=
    PlanarJordan.arc_inter_curve_eq_pair harcB' hp'fr hq'fr hBpin
  have hφρ : ∀ x ∈ σρ '' B ∩ frontier Pl, φ x = ρ x := by
    intro x hx
    rw [hBpfr] at hx
    rcases hx with rfl | rfl
    · rw [hφ0, hρσ _ (hBΔ hgB0.1)]
    · rw [hφ1, hρσ _ (hBΔ hgB1.1)]
  have hρX : MapsTo ρ (frontier Pl) (frontier XK.space) := fun x hx =>
    hb (hρb ▸ mem_image_of_mem ρ hx)
  have hS₁X : ρ '' A₁ ∪ B₁ ⊆ frontier XK.space :=
    union_subset ((image_mono hcutA.fst_subset).trans (image_subset_iff.mpr hρX)) hB₁X
  have hS₂X : ρ '' A₂ ∪ B₁ ⊆ frontier XK.space :=
    union_subset ((image_mono hcutA.snd_subset).trans (image_subset_iff.mpr hρX)) hB₁X
  have hSσ : MapsTo σρ (r '' stdSimplexBoundary 2) (frontier Pl) := by
    rw [← hρb]
    rintro _ ⟨x, hx, rfl⟩
    rwa [hσρρ x (hfrPl hx)]
  have hSΔ : r '' stdSimplexBoundary 2 ⊆ Δ := hΔB ▸ inter_subset_left
  have htheta : ¬ (⟨Set.inclusion hS₁X, continuous_inclusion hS₁X⟩ :
      C(↥(ρ '' A₁ ∪ B₁), frontier XK.space)).Nullhomotopic ∨
      ¬ (⟨Set.inclusion hS₂X, continuous_inclusion hS₂X⟩ :
      C(↥(ρ '' A₂ ∪ B₁), frontier XK.space)).Nullhomotopic := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    exact hnull (nullhomotopic_of_crosscut_halves hPl hU hVb hUVu hUVi
      (by rw [hfrU, hUfr]) (by rw [hfrV, hVfr]) hρc hφ.isPiecewiseAffineOn.continuousOn hφρ hρX
      hS₁X hS₂X hb (by rw [hUfr, hφ.image_eq]) (by rw [hVfr, hφ.image_eq])
      (hσρc.mono hSΔ) hSσ (fun y hy => hρσ y (hSΔ hy)) hcon.1 hcon.2)
  obtain ⟨W, W', AW, AW', aW', haW', haW'0, haW'1, hW, hW', hWW', hWi, hfrW, hfrW', hWfr,
      hW'fr, hAWu, -, hSX, hnt⟩ : ∃ (W W' AW AW' : Set (EuclideanSpace ℝ (Fin 2)))
      (aW' : ℝ → EuclideanSpace ℝ (Fin 2)), IsPLHomeomorphOn aW' (Icc 0 1) AW' ∧
      aW' 0 = σρ (gB 0) ∧ aW' 1 = σρ (gB 1) ∧ IsPLBall 2 W ∧ IsPLBall 2 W' ∧ W ∪ W' = Pl ∧
      W ∩ W' = σρ '' B ∧ frontier W = AW ∪ σρ '' B ∧ frontier W' = AW' ∪ σρ '' B ∧
      W ∩ frontier Pl = AW ∧ W' ∩ frontier Pl = AW' ∧ AW ∪ AW' = frontier Pl ∧
      AW ∩ AW' = {σρ (gB 0), σρ (gB 1)} ∧ ∃ hS : ρ '' AW ∪ B₁ ⊆ frontier XK.space,
        ¬ (⟨Set.inclusion hS, continuous_inclusion hS⟩ :
          C(↥(ρ '' AW ∪ B₁), frontier XK.space)).Nullhomotopic := by
    rcases htheta with h' | h'
    · exact ⟨_, _, A₁, A₂, a₂, ha₂, ha₂0, ha₂1, hU, hVb, hUVu, hUVi, hfrU, hfrV, hUfr, hVfr,
        hcutA.union_eq, hcutA.inter_eq, hS₁X, h'⟩
    · exact ⟨_, _, A₂, A₁, a₁, ha₁, ha₁0, ha₁1, hVb, hU, (union_comm _ _).trans hUVu,
        (inter_comm _ _).trans hUVi, hfrV, hfrU, hVfr, hUfr, (union_comm _ _).trans
        hcutA.union_eq, (inter_comm _ _).trans hcutA.inter_eq, hS₂X, h'⟩
  have hWPl : W ⊆ Pl := hWW' ▸ subset_union_left
  have hW'Pl : W' ⊆ Pl := hWW' ▸ subset_union_right
  have hBpW : σρ '' B ⊆ W := hWi ▸ inter_subset_left
  have hBpW' : σρ '' B ⊆ W' := hWi ▸ inter_subset_right
  have hAWW : AW ⊆ W := hWfr ▸ inter_subset_left
  have hAW'W' : AW' ⊆ W' := hW'fr ▸ inter_subset_left
  have hAW'Pl : AW' ⊆ frontier Pl := hW'fr ▸ inter_subset_right
  have hAW'poly : IsPolyhedron AW' :=
    IsPLBall.isPolyhedron (n := 1) ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn haW')
  have hα' : IsPLHomeomorphOn (ρ ∘ aW') (Icc 0 1) (ρ '' AW') :=
    haW'.trans (hρ.restrict hAW'poly (hAW'Pl.trans hfrPl))
  have hα'poly : IsPolyhedron (ρ '' AW') :=
    IsPLBall.isPolyhedron (n := 1) ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hα')
  set ψ := γ₁' ∘ Function.invFunOn (ρ ∘ aW') (Icc (0 : ℝ) 1) with hψdef
  have hψ : IsPLHomeomorphOn ψ (ρ '' AW') B₁ := hα'.symm.trans hγ₁'
  have hρp : ρ (σρ (gB 0)) = gB 0 := hρσ _ (hBΔ hgB0.1)
  have hρq : ρ (σρ (gB 1)) = gB 1 := hρσ _ (hBΔ hgB1.1)
  have hα'0 : (ρ ∘ aW') 0 = gB 0 := by
    simp only [Function.comp_apply, haW'0, hρp]
  have hα'1 : (ρ ∘ aW') 1 = gB 1 := by
    simp only [Function.comp_apply, haW'1, hρq]
  have hψ0 : ψ (gB 0) = gB 0 := by
    calc ψ (gB 0) = γ₁' (Function.invFunOn (ρ ∘ aW') (Icc (0 : ℝ) 1) ((ρ ∘ aW') 0)) := by
          simp only [hα'0, hψdef, Function.comp_apply]
      _ = γ₁' 0 := by rw [hα'.bijOn.invOn_invFunOn.1 h0I]
      _ = gB 0 := hγ₁'0
  have hψ1 : ψ (gB 1) = gB 1 := by
    calc ψ (gB 1) = γ₁' (Function.invFunOn (ρ ∘ aW') (Icc (0 : ℝ) 1) ((ρ ∘ aW') 1)) := by
          simp only [hα'1, hψdef, Function.comp_apply]
      _ = γ₁' 1 := by rw [hα'.bijOn.invOn_invFunOn.1 h1I]
      _ = gB 1 := hγ₁'1
  have hBpimg : σρ '' B ⊆ Pl := hBpW.trans hWPl
  have hAW'Bp : AW' ∩ σρ '' B = {σρ (gB 0), σρ (gB 1)} := by
    rw [← hBpfr]
    ext x
    constructor
    · rintro ⟨hxA, hxB⟩
      exact ⟨hxB, hAW'Pl hxA⟩
    · rintro ⟨hxB, hxfr⟩
      exact ⟨hW'fr ▸ ⟨hBpW' hxB, hxfr⟩, hxB⟩
  have hα'B : ρ '' AW' ∩ B = {gB 0, gB 1} := by
    rw [← hρσimg B hBCs, ← hρinj.image_inter (hAW'Pl.trans hfrPl) hBpimg, hAW'Bp, image_pair,
      hρp, hρq]
  have hB₁B : B₁ ∩ B = {gB 0, gB 1} := by
    rw [inter_comm, hBB₁, hgBe]
  obtain ⟨H₀, hH₀, hH₀ψ, hH₀id⟩ := exists_isPLHomeomorphOn_union hα'poly hBpoly hψ
    hBpoly.isPLHomeomorphOn_id
    (by
      rw [hα'B]
      rintro x (rfl | rfl)
      · exact hψ0
      · exact hψ1)
    (by
      rw [hα'B, hB₁B]
      rintro x (rfl | rfl)
      · exact ⟨gB 0, Or.inl rfl, hψ0⟩
      · exact ⟨gB 1, Or.inr rfl, hψ1⟩)
  obtain ⟨qW', hqW'⟩ := id hW'
  have hrW' : IsPLHomeomorphOn (ρ ∘ qW') (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ρ '' W') :=
    hqW'.trans (hρ.restrict hW'.isPolyhedron hW'Pl)
  have hrW'b : (ρ ∘ qW') '' stdSimplexBoundary 2 = ρ '' AW' ∪ B := by
    rw [image_comp, hqW'.image_stdSimplexBoundary_eq_frontier (n := 1), hfrW', image_union,
      hρσimg B hBCs]
  have hH₀' : IsPLHomeomorphOn H₀ ((ρ ∘ qW') '' stdSimplexBoundary 2)
      (rB '' stdSimplexBoundary 2) := by
    rw [hrW'b, hrBb, union_comm B B₁]
    exact hH₀
  obtain ⟨G, hG, hGH₀⟩ :=
    exists_isPLHomeomorphOn_extension_of_stdSimplexBoundary (n := 1) hrW' hrB hH₀'
  have hGH₀' : EqOn G H₀ (ρ '' AW' ∪ B) := by
    have h1 : EqOn G H₀ ((ρ ∘ qW') '' stdSimplexBoundary 2) := hGH₀
    rwa [hrW'b] at h1
  have hWpoly : IsPolyhedron (ρ '' W) := hW.isPolyhedron.image_of_isPiecewiseAffineOn
    (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron hW.isPolyhedron hWPl) (hρinj.mono hWPl)
  have hW'poly : IsPolyhedron (ρ '' W') := hW'.isPolyhedron.image_of_isPiecewiseAffineOn
    (hρ.isPiecewiseAffineOn.mono_of_isPolyhedron hW'.isPolyhedron hW'Pl) (hρinj.mono hW'Pl)
  have hWW'img : ρ '' W ∩ ρ '' W' = B := by
    rw [← hρinj.image_inter hWPl hW'Pl, hWi, hρσimg B hBCs]
  have hWΔ : ρ '' W ∪ ρ '' W' = Δ := by
    rw [← image_union, hWW', hρ.image_eq]
  have hBW : B ⊆ ρ '' W := by
    rw [← hρσimg B hBCs]
    exact image_mono hBpW
  have hBDB : B ⊆ DB := by
    intro y hy
    have h1 : y ∈ rB '' stdSimplexBoundary 2 := hrBb ▸ Or.inl hy
    obtain ⟨x, hx, rfl⟩ := h1
    exact hrB.bijOn.mapsTo hx.1
  have hWDB : ρ '' W ∩ DB = B := by
    apply Subset.antisymm
    · intro y hy
      rw [← hDBΔ]
      exact ⟨hy.2, hPlΔ hWPl hy.1⟩
    · exact subset_inter hBW hBDB
  obtain ⟨H, hH, hHid, hHG⟩ := exists_isPLHomeomorphOn_union hWpoly hW'poly
    hWpoly.isPLHomeomorphOn_id hG
    (by
      rw [hWW'img]
      intro y hy
      exact ((hGH₀' (Or.inr hy)).trans (hH₀id hy)).symm)
    (by
      rw [hWW'img, hWDB]
      exact surjOn_id B)
  rw [hWΔ] at hH
  have hr₁ : IsPLHomeomorphOn (H ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ρ '' W ∪ DB) := hr.trans hH
  have hr₁b : (H ∘ r) '' stdSimplexBoundary 2 = ρ '' AW ∪ B₁ := by
    rw [image_comp, ← hρb, ← hAWu, image_union, image_union]
    have h1 : H '' (ρ '' AW) = ρ '' AW :=
      ((hHid.mono (image_mono hAWW)).image_eq).trans (image_id _)
    have h2 : H '' (ρ '' AW') = B₁ := by
      rw [(hHG.mono (image_mono hAW'W')).image_eq, (hGH₀'.mono subset_union_left).image_eq,
        hH₀ψ.image_eq, hψ.image_eq]
    rw [h1, h2]
  have hΔ₁sub : ρ '' W ∪ DB ⊆ interior N' \ h '' K.space :=
    union_subset ((hPlΔ hWPl).trans hΔsub) hDBN
  have hΔ₁B : (ρ '' W ∪ DB) ∩ frontier XK.space = ρ '' AW ∪ B₁ := by
    rw [union_inter_distrib_right, hDBX]
    congr 1
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hX⟩
      have h1 := (hbdry _ (hρ.bijOn.mapsTo (hWPl hx))).mp hX
      rw [hσρρ x (hWPl hx)] at h1
      exact ⟨x, hWfr ▸ ⟨hx, h1⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hxW : x ∈ W ∩ frontier Pl := hWfr.symm ▸ hx
      refine ⟨⟨x, hxW.1, rfl⟩, (hbdry _ (hρ.bijOn.mapsTo (hWPl hxW.1))).mpr ?_⟩
      rw [hσρρ x (hWPl hxW.1)]
      exact hxW.2
  have hΔ₁ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) (ρ '' W ∪ DB) :=
    IsLoopTheoremDisk.of_isPLHomeomorphOn hr₁ hΔ₁sub hΔ₁B hr₁b hSX hnt
  have hWcl : IsClosed (ρ '' W) :=
    ((hPlc.of_isClosed_subset hW.isPolyhedron.isClosed hWPl).image_of_continuousOn
      (hρc.mono hWPl)).isClosed
  have hW'cl : IsClosed (ρ '' W') :=
    ((hPlc.of_isClosed_subset hW'.isPolyhedron.isClosed hW'Pl).image_of_continuousOn
      (hρc.mono hW'Pl)).isClosed
  have hSside : ∀ S ∈ Cs, S ≠ B → S ⊆ ρ '' W ∨ S ⊆ ρ '' W' := by
    intro S hS hSB
    have hcov : S ⊆ ρ '' W ∪ ρ '' W' := hWΔ.symm ▸ hCsΔ S hS
    have hdis : S ∩ (ρ '' W ∩ ρ '' W') = ∅ := by
      rw [hWW'img]
      exact (hdisj hS hBCs hSB).inter_eq
    exact (isPreconnected_iff_subset_of_disjoint_closed.mp (hCspre S hS)) _ _ hWcl hW'cl
      hcov hdis
  set Cs' := {S ∈ Cs | S ≠ B ∧ S ⊆ ρ '' W} with hCs'def
  have hWA : ρ '' W ∩ A ⊆ B ∪ ⋃₀ Cs' := by
    rintro y ⟨hyW, hyA⟩
    obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hA.subset ⟨hPlΔ hWPl hyW, hyA⟩)
    by_cases hSB : S = B
    · exact Or.inl (hSB ▸ hyS)
    · rcases hSside S hS hSB with h' | h'
      · exact Or.inr (mem_sUnion_of_mem hyS ⟨hS, hSB, h'⟩)
      · exfalso
        have h3 : y ∈ ρ '' W ∩ ρ '' W' := ⟨hyW, h' hyS⟩
        rw [hWW'img] at h3
        exact Set.disjoint_left.mp (hdisj hS hBCs hSB) hyS h3
  have hCs'fin : Cs'.Finite := hfin.subset fun S hS => hS.1
  have hFc : IsCompact (⋃₀ Cs') :=
    hCs'fin.isCompact_sUnion fun S hS => (hCspoly S hS.1).isCompact
  have hFPc : ⋃₀ Cs' ⊆ ρ '' W := sUnion_subset fun S hS => hS.2.2
  have hFc_disj : Disjoint (⋃₀ Cs') B :=
    Set.disjoint_sUnion_left.mpr fun S hS => hdisj hS.1 hBCs hS.2.1
  have hFA : ⋃₀ Cs' ⊆ A := sUnion_subset fun S hS => hCsA S hS.1
  have hFΔ : ⋃₀ Cs' ⊆ Δ := sUnion_subset fun S hS => hCsΔ S hS.1
  have hσF : IsCompact (σρ '' ⋃₀ Cs') := hFc.image_of_continuousOn (hσρc.mono hFΔ)
  have hBpW₀ : σρ '' B ⊆ (σρ '' ⋃₀ Cs')ᶜ := by
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hzF, hzy⟩
    have hzy' := hσρ.bijOn.injOn (hFΔ hzF) (hBΔ hy) hzy
    exact Set.disjoint_left.mp hFc_disj hzF (hzy' ▸ hy)
  obtain ⟨v, hv, Wo, hWoo, hBpWo, hWov⟩ := hd.exists_handlePiece_near hW (hρc.mono hWPl)
    (fun y hy => (hΔsub (hPlΔ hWPl hy)).1) harcB'.isArc.isConnected.isPreconnected
    harcB'.isArc.nonempty hBpW hσF.isClosed.isOpen_compl hBpW₀
    (fun z hz hzA => by
      have hzW := interior_subset hz.1
      rcases hWA ⟨mem_image_of_mem ρ hzW, hzA⟩ with h' | h'
      · have hzBp : z ∈ σρ '' B := ⟨ρ z, h', hσρρ z (hWPl hzW)⟩
        have hzfr : z ∈ frontier W := hfrW ▸ Or.inr hzBp
        exact Set.disjoint_left.mp disjoint_interior_frontier hz.1 hzfr
      · exact hz.2 ⟨ρ z, h', hσρρ z (hWPl hzW)⟩)
  have hBv : B ⊆ Cpp v := by
    rw [← hρσimg B hBCs]
    exact (image_mono (subset_inter hBpW hBpWo)).trans hWov
  have hve : v ∈ e₀ := by
    by_contra hn
    have h1 := hd.handlePiece_inter_pseudoCell_eq_empty hv he₀ hcard₀ hn
    have h3 : gB 0 ∈ Cpp v ∩ Ec e₀ := ⟨hBv hgB0.1, hBe hgB0.1⟩
    rw [h1] at h3
    exact h3
  have hDBv : DB ⊆ Cpp v := hDBE.trans (hd.pseudoCell_subset_handlePiece he₀ hcard₀ hve)
  have hWcomp : IsCompact (ρ '' (W \ Wo)) :=
    (hPlc.of_isClosed_subset (hW.isPolyhedron.isClosed.sdiff hWoo)
      (sdiff_subset.trans hWPl)).image_of_continuousOn (hρc.mono (sdiff_subset.trans hWPl))
  have hO : IsOpen ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩ (ρ '' (W \ Wo))ᶜ) :=
    (hV.inter hFc.isClosed.isOpen_compl).inter hWcomp.isClosed.isOpen_compl
  have hBWo : Disjoint B (ρ '' (W \ Wo)) := by
    rw [← hρσimg B hBCs]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨z, hz, hzx⟩
    have hzx' := hρinj (hWPl hz.1) (hBpW.trans hWPl hx) hzx
    exact hz.2 (hzx' ▸ hBpWo hx)
  have hDBc : IsCompact DB := by
    rw [← hrB.image_eq]
    exact (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).image_of_continuousOn
      hrB.isPiecewiseAffineOn.continuousOn
  have hDBO : DB ⊆ (interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩ (ρ '' (W \ Wo))ᶜ := by
    intro y hy
    refine ⟨⟨hDBN hy, fun hyF => ?_⟩, fun hyW => ?_⟩
    · have h1 : y ∈ B := hDBΔ ▸ ⟨hy, hFΔ hyF⟩
      exact Set.disjoint_left.mp hFc_disj hyF h1
    · have h1 : y ∈ B := hDBΔ ▸ ⟨hy, hPlΔ (sdiff_subset.trans hWPl) hyW⟩
      exact Set.disjoint_left.mp hBWo h1 hyW
  have hΔ₁O : (ρ '' W ∪ DB) ∩ ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩
      (ρ '' (W \ Wo))ᶜ) ⊆ Cpp v := by
    rintro y ⟨hy | hy, hyO⟩
    · obtain ⟨x, hx, rfl⟩ := hy
      have hxWo : x ∈ Wo := by
        by_contra hn
        exact hyO.2 ⟨x, ⟨hx, hn⟩, rfl⟩
      exact hWov ⟨x, ⟨hx, hxWo⟩, rfl⟩
    · exact hDBv hy
  have hΔ₁Z : (ρ '' W ∪ DB) ∩ ((interior N' \ h '' K.space) ∩ (⋃₀ Cs')ᶜ ∩
      (ρ '' (W \ Wo))ᶜ) ∩ A ⊆ DB := by
    rintro y ⟨⟨hy | hy, hyO⟩, hyA⟩
    · rcases hWA ⟨hy, hyA⟩ with h1 | h1
      · exact hBDB h1
      · exact absurd h1 hyO.1.2
    · exact hy
  obtain ⟨Δ₂, hΔ₂, hΔ₂A⟩ := h2.exists_isLoopTheoremDisk_pushOff hd hv hΔ₁ hO
    (fun y hy => hy.1.1.1) (Set.disjoint_left.mpr fun y hy hyK => hy.1.1.2 hyK) hDBc hDBO hDBv
    hΔ₁O hΔ₁Z
  refine ⟨Δ₂, Cs', hΔ₂, fun S hS => hS.1, fun heq => ?_, ?_⟩
  · have h1 : B ∈ Cs' := heq ▸ hBCs
    exact h1.2.1 rfl
  · rw [hΔ₂A]
    apply Subset.antisymm
    · rintro y ⟨⟨hy1 | hy1, hyO⟩, hyA⟩
      · rcases hWA ⟨hy1, hyA⟩ with h1 | h1
        · exact absurd (hDBO (hBDB h1)) hyO
        · exact h1
      · exact absurd (hDBO hy1) hyO
    · intro y hy
      exact ⟨⟨Or.inl (hFPc hy), fun hyO => hyO.1.2 hy⟩, hFA hy⟩

end ArcStep

end DifferentialGeometry.Topology.PiecewiseLinear
