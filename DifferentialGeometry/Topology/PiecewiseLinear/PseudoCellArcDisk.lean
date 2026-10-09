/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DisplacedArcConnected
import DifferentialGeometry.Topology.PiecewiseLinear.FourArcSphere
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarOutermostCrosscut
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeSinglePolygonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellChartDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLHomeomorphOn.comp_lineMap_one_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {A : Set E} {γ : ℝ → E}
    (hγ : IsPLHomeomorphOn γ (Icc 0 1) A) :
    IsPLHomeomorphOn (γ ∘ AffineMap.lineMap (k := ℝ) (1 : ℝ) (0 : ℝ)) (Icc 0 1) A := by
  have hmaps : ∀ t ∈ Icc (0 : ℝ) 1, AffineMap.lineMap (k := ℝ) (1 : ℝ) (0 : ℝ) t = 1 - t := by
    intro t _
    rw [AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have hrev :
      IsPLHomeomorphOn (AffineMap.lineMap (k := ℝ) (1 : ℝ) (0 : ℝ)) (Icc 0 1) (Icc 0 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      ((isPiecewiseAffineOn_of_affine _ isOpen_univ).mono_of_isPolyhedron
        isHPolytope_Icc.isPolyhedron (subset_univ _)) ⟨?_, ?_, ?_⟩
    · intro t ht
      rw [hmaps t ht]
      exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    · intro s hs t ht hst
      rw [hmaps s hs, hmaps t ht] at hst
      linarith
    · intro t ht
      refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
      rw [hmaps (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩]
      ring
  exact hrev.trans hγ

section ArcDisk

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_arc_eDisk_of_chart
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) {e : Finset E3} (he : e ∈ K.faces)
    (hcard : e.card = 2) {Δ : Set E3} (hΔN : Δ ⊆ interior N' \ h '' K.space)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, ∃ g : ℝ → E3, IsPLHomeomorphOn g (Icc 0 1) S ∧
      ({g 0, g 1} : Set E3) = S ∩ frontier XK.space)
    {B₀ : Set E3} (hB₀ : B₀ ∈ Cs) (hB₀e : B₀ ⊆ Ec e)
    {χ : E3 → Schoenflies.Plane} {ξ : Schoenflies.Plane → E3}
    (hχ : ContinuousOn χ (Eint e \ {h (e.centroid ℝ id)}))
    (hξ : ContinuousOn ξ (χ '' (Eint e \ {h (e.centroid ℝ id)})))
    (hξχ : ∀ x ∈ Eint e \ {h (e.centroid ℝ id)}, ξ (χ x) = x) {a : Schoenflies.Plane}
    (ha : a ∈ Schoenflies.inside (χ '' (Ec e ∩ frontier XK.space)))
    (haM : a ∉ χ '' (Eint e \ {h (e.centroid ℝ id)}))
    (hin : ∀ S ∈ Cs, S ⊆ Ec e →
      χ '' (S \ frontier XK.space) ⊆ Schoenflies.inside (χ '' (Ec e ∩ frontier XK.space)))
    {H : Set Schoenflies.Plane} (hH : IsPreconnected H) (haH : a ∈ H)
    (hHM : Disjoint H (χ '' (Eint e \ {h (e.centroid ℝ id)})))
    (hHcl : closure (Schoenflies.inside (χ '' (Ec e ∩ frontier XK.space))) \ H ⊆
      χ '' (Eint e \ {h (e.centroid ℝ id)})) :
    ∃ B ∈ Cs, ∃ (B₁ DB : Set E3) (γ₁ : ℝ → E3) (rB : (Fin 3 → ℝ) → E3),
      B ⊆ Ec e ∧ IsPLHomeomorphOn γ₁ (Icc 0 1) B₁ ∧
      ({γ₁ 0, γ₁ 1} : Set E3) = B ∩ frontier XK.space ∧ B₁ ⊆ frontier XK.space ∧
      B ∩ B₁ = B ∩ frontier XK.space ∧ IsPLHomeomorphOn rB (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) DB ∧
      rB '' stdSimplexBoundary 2 = B ∪ B₁ ∧ DB ⊆ Ec e ∧ DB ⊆ interior N' \ h '' K.space ∧
      DB ∩ frontier XK.space = B₁ ∧ DB ∩ Δ = B := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  set M := Eint e \ {h (e.centroid ℝ id)} with hMdef
  set J := Ec e ∩ frontier XK.space with hJdef
  have hpc := hd.pseudoCell e he hcard
  have hEEc : Eint e ⊆ Ec e := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hEN : Eint e ⊆ interior N' := hd.interior_pseudoCell_subset_interior he hcard
  have hEK : Ec e ∩ h '' K.space = {h (e.centroid ℝ id)} := hd.meetsGraph e he hcard
  have hJM : J ⊆ M := h2.trace_subset hd he hcard
  have hJs : IsPLSphere 1 J := (h34 e he hcard).1
  have hχi : InjOn χ M := fun x hx y hy hxy => by rw [← hξχ x hx, ← hξχ y hy, hxy]
  have hχξ : ∀ p ∈ χ '' M, χ (ξ p) = p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hξχ x hx]
  have hγ : Schoenflies.IsJordanCurve (χ '' J) :=
    isJordanCurve_image_of_isPLSphere_one hJs hJM hχ hχi
  have hCsΔ : ∀ S ∈ Cs, S ⊆ Δ := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).1
  have hCsA : ∀ S ∈ Cs, S ⊆ A := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).2
  have hSM : ∀ S ∈ Cs, S ⊆ Ec e → S ⊆ M := by
    intro S hS hSe y hy
    have hyN := hΔN (hCsΔ S hS hy)
    refine ⟨?_, fun hyP => hyN.2 ?_⟩
    · have hEc : y ∈ Eint e ∪ Ebd e := hpc.carrierEq ▸ hSe hy
      refine hEc.resolve_right fun hbd => ?_
      rw [← hd.rimFrontier e he hcard] at hbd
      exact Set.disjoint_left.mp disjoint_interior_frontier hyN.1 hbd.2
    · rw [mem_singleton_iff.mp hyP]
      exact (hEK.symm.subset (mem_singleton _)).2
  let ι := {S : Set E3 // S ∈ Cs ∧ S ⊆ Ec e}
  have : Finite ι := Set.Finite.to_subtype (s := {S : Set E3 | S ∈ Cs ∧ S ⊆ Ec e})
    (hfin.subset fun S hS => hS.1)
  have : Nonempty ι := ⟨⟨B₀, hB₀, hB₀e⟩⟩
  choose g hg hgend using fun i : ι => hCs i.1 i.2.1
  have hiM : ∀ i : ι, i.1 ⊆ M := fun i => hSM i.1 i.2.1 i.2.2
  have hgM : ∀ i : ι, ∀ t ∈ Icc (0 : ℝ) 1, g i t ∈ M := fun i t ht =>
    hiM i ((hg i).bijOn.mapsTo ht)
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1I : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hg01 : ∀ i : ι, g i 0 ≠ g i 1 := fun i h01 => by
    have := (hg i).bijOn.injOn h0I h1I h01
    norm_num at this
  have harc : ∀ i : ι, Schoenflies.IsArcBetween (χ '' i.1) (χ (g i 0)) (χ (g i 1)) := by
    intro i
    refine ⟨χ ∘ g i, hχ.comp (hg i).isPiecewiseAffineOn.continuousOn fun t ht => hgM i t ht,
      hχi.comp (hg i).bijOn.injOn fun t ht => hgM i t ht, ?_, rfl, rfl⟩
    rw [image_comp, (hg i).image_eq]
  have hend : ∀ i : ι, ∀ y ∈ i.1, (y ∈ frontier XK.space ↔ y = g i 0 ∨ y = g i 1) := by
    intro i y hy
    constructor
    · intro hyX
      have hmem : y ∈ ({g i 0, g i 1} : Set E3) := (hgend i).symm ▸ ⟨hy, hyX⟩
      exact hmem
    · intro hyg
      have hmem : y ∈ i.1 ∩ frontier XK.space := (hgend i) ▸ hyg
      exact hmem.2
  have hgJ : ∀ i : ι, g i 0 ∈ J ∧ g i 1 ∈ J := by
    intro i
    have h0 : g i 0 ∈ i.1 := (hg i).bijOn.mapsTo h0I
    have h1 : g i 1 ∈ i.1 := (hg i).bijOn.mapsTo h1I
    exact ⟨⟨i.2.2 h0, (hend i _ h0).mpr (Or.inl rfl)⟩, ⟨i.2.2 h1, (hend i _ h1).mpr (Or.inr rfl)⟩⟩
  have hinT : ∀ i : ι, χ '' i.1 \ {χ (g i 0), χ (g i 1)} ⊆
      Schoenflies.inside (χ '' J) := by
    intro i
    rintro _ ⟨⟨y, hy, rfl⟩, hyne⟩
    refine hin i.1 i.2.1 i.2.2 ⟨y, ⟨hy, fun hyX => hyne ?_⟩, rfl⟩
    rcases (hend i y hy).mp hyX with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hdisjT : Pairwise fun i j : ι => Disjoint (χ '' i.1) (χ '' j.1) := by
    intro i j hij
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' := hχi (hiM j hz) (hiM i hy) hzy
    have hne : i.1 ≠ j.1 := fun h' => hij (Subtype.ext h')
    exact Set.disjoint_left.mp (hdisj i.2.1 j.2.1 hne) hy (hzy' ▸ hz)
  have haT : ∀ i : ι, a ∉ χ '' i.1 := fun i hai => haM (image_mono (hiM i) hai)
  obtain ⟨i, β, ⟨β', hcutβ⟩, hβT, hΓ, hRin, haR, hclγ, hothers⟩ :=
    exists_outermost_crosscut hγ ha harc (fun i => mem_image_of_mem χ (hgJ i).1)
      (fun i => mem_image_of_mem χ (hgJ i).2) hinT hdisjT haT
  have hBCs : i.1 ∈ Cs := i.2.1
  have hBe : i.1 ⊆ Ec e := i.2.2
  have hBM := hiM i
  have hβγ : β ⊆ χ '' J := hcutβ.fst_subset
  have hβM : β ⊆ χ '' M := hβγ.trans (image_mono hJM)
  have hΓM : β ∪ χ '' i.1 ⊆ χ '' M := union_subset hβM (image_mono hBM)
  have hHΓ : Disjoint H (β ∪ χ '' i.1) := hHM.mono_right hΓM
  have hclR : closure (Schoenflies.inside (β ∪ χ '' i.1)) ⊆ χ '' M := by
    rcases subset_inside_or_subset_outside hΓ hH hHΓ with h1 | h1
    · exact absurd (h1 haH) haR
    · intro p hp
      refine hHcl ⟨closure_mono hRin hp, fun hpH => ?_⟩
      rw [closure_inside_eq_union hΓ] at hp
      rcases hp with hp | hp
      · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hp (h1 hpH)
      · exact Set.disjoint_left.mp hHΓ hpH hp
  have hB₁J : ξ '' β ⊆ J := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hβγ hp
    rw [hξχ y (hJM hy)]
    exact hy
  have hχB₁ : χ '' (ξ '' β) = β := by
    rw [image_image]
    exact (image_congr fun p hp => hχξ p (hβM hp)).trans (image_id' β)
  have hβc : IsCompact β := hcutβ.fst.isArc.isCompact
  have hB₁cl : IsClosed (ξ '' β) := (hβc.image_of_continuousOn (hξ.mono hβM)).isClosed
  have hB₁conn : IsConnected (ξ '' β) := hcutβ.fst.isArc.isConnected.image ξ (hξ.mono hβM)
  have hξp : ξ (χ (g i 0)) = g i 0 := hξχ _ (hgM i 0 h0I)
  have hξq : ξ (χ (g i 1)) = g i 1 := hξχ _ (hgM i 1 h1I)
  have hpB₁ : g i 0 ∈ ξ '' β := ⟨χ (g i 0), hcutβ.fst.left_mem, hξp⟩
  have hqB₁ : g i 1 ∈ ξ '' β := ⟨χ (g i 1), hcutβ.fst.right_mem, hξq⟩
  have hB₁nt : (ξ '' β).Nontrivial := ⟨g i 0, hpB₁, g i 1, hqB₁, hg01 i⟩
  have hB₁ss : ξ '' β ⊂ J := by
    refine ⟨hB₁J, fun hJB => ?_⟩
    obtain ⟨z, hz⟩ := hcutβ.snd.nonempty_diff
    obtain ⟨y, hy, rfl⟩ := hcutβ.snd_subset hz.1
    obtain ⟨p, hp, hpy⟩ := hJB hy
    have hχy : χ y = p := by rw [← hpy, hχξ p (hβM hp)]
    exact hz.2 (hcutβ.inter_eq.subset ⟨hχy ▸ hp, hz.1⟩)
  have hB₁ball : IsPLBall 1 (ξ '' β) :=
    hJs.isPLBall_one_of_isClosed_of_isConnected_of_ssubset hB₁cl hB₁conn hB₁nt hB₁ss
  obtain ⟨γ₁', hγ₁'⟩ := exists_isPLHomeomorphOn_Icc_of_isPLBall_one hB₁ball
  have hWeq : ξ '' β \ {g i 0, g i 1} = ξ '' (β \ {χ (g i 0), χ (g i 1)}) := by
    ext y
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hpne⟩
      refine ⟨p, ⟨hp, fun hpe => hpne ?_⟩, rfl⟩
      rcases hpe with rfl | rfl
      · exact Or.inl hξp
      · exact Or.inr hξq
    · rintro ⟨p, ⟨hp, hpne⟩, rfl⟩
      refine ⟨⟨p, hp, rfl⟩, fun hpe => hpne ?_⟩
      rcases hpe with hpe | hpe
      · left
        rw [← hχξ p (hβM hp), hpe]
      · right
        have hpe' : ξ p = g i 1 := hpe
        rw [← hχξ p (hβM hp), hpe']
        exact mem_singleton _
  have hW : IsConnected (ξ '' β \ {g i 0, g i 1}) := by
    rw [hWeq]
    exact hcutβ.fst.isConnected_diff.image ξ (hξ.mono (sdiff_subset.trans hβM))
  have hWcl : closure (ξ '' β \ {g i 0, g i 1}) = ξ '' β := by
    refine Subset.antisymm (closure_minimal sdiff_subset hB₁cl) ?_
    rw [hWeq]
    have h1 : ξ '' closure (β \ {χ (g i 0), χ (g i 1)}) ⊆
        closure (ξ '' (β \ {χ (g i 0), χ (g i 1)})) :=
      (hξ.mono (by rw [hcutβ.fst.closure_diff_eq]; exact hβM)).image_closure
    rwa [hcutβ.fst.closure_diff_eq] at h1
  have hends1 := sdiff_subset_endpoints_of_isConnected_of_closure_eq hγ₁' hW hWcl
  have hp1 : g i 0 ∈ ({γ₁' 0, γ₁' 1} : Set E3) := hends1 ⟨hpB₁, fun h' => h'.2 (Or.inl rfl)⟩
  have hq1 : g i 1 ∈ ({γ₁' 0, γ₁' 1} : Set E3) := hends1 ⟨hqB₁, fun h' => h'.2 (Or.inr rfl)⟩
  obtain ⟨γ₁, hγ₁, hγ₁0, hγ₁1⟩ : ∃ γ₁ : ℝ → E3, IsPLHomeomorphOn γ₁ (Icc 0 1) (ξ '' β) ∧
      γ₁ 0 = g i 0 ∧ γ₁ 1 = g i 1 := by
    rcases hp1 with hp1 | hp1
    · refine ⟨γ₁', hγ₁', hp1.symm, ?_⟩
      rcases hq1 with hq1 | hq1
      · exact absurd (hp1.trans hq1.symm) (hg01 i)
      · exact hq1.symm
    · refine ⟨γ₁' ∘ AffineMap.lineMap (k := ℝ) (1 : ℝ) (0 : ℝ), hγ₁'.comp_lineMap_one_zero, ?_, ?_⟩
      · simp only [Function.comp_apply, AffineMap.lineMap_apply_zero]
        exact hp1.symm
      · simp only [Function.comp_apply, AffineMap.lineMap_apply_one]
        rcases hq1 with hq1 | hq1
        · exact hq1.symm
        · exact absurd (hp1.trans hq1.symm) (hg01 i)
  have hBB₁ : i.1 ∩ ξ '' β = {g i 0, g i 1} := by
    apply Subset.antisymm
    · rintro _ ⟨hyB, p, hp, rfl⟩
      have hpB : p ∈ χ '' i.1 := by
        rw [← hχξ p (hβM hp)]
        exact mem_image_of_mem χ hyB
      rcases hβT.subset ⟨hp, hpB⟩ with rfl | rfl
      · exact Or.inl hξp
      · exact Or.inr hξq
    · rintro y (rfl | rfl)
      · exact ⟨(hg i).bijOn.mapsTo h0I, hpB₁⟩
      · exact ⟨(hg i).bijOn.mapsTo h1I, hqB₁⟩
  have hJ₁ : IsPLSphere 1 (i.1 ∪ ξ '' β) :=
    isPLSphere_one_union_of_isPLHomeomorphOn_Icc (hg i) hγ₁ hγ₁0 hγ₁1 hBB₁
  have hJ₁M : i.1 ∪ ξ '' β ⊆ M := union_subset hBM (hB₁J.trans hJM)
  have hχJ₁ : χ '' (i.1 ∪ ξ '' β) = β ∪ χ '' i.1 := by
    rw [image_union, hχB₁, union_comm]
  obtain ⟨rB, hrB, hrBb, hDM, hDmem⟩ := exists_isPLHomeomorphOn_chart_closure_inside
    hpc.regular hχ hξ hξχ hJ₁ hJ₁M (hχJ₁ ▸ hclR)
  rw [hχJ₁] at hrB hDM hDmem
  have hJ₁D : i.1 ∪ ξ '' β ⊆ ξ '' closure (Schoenflies.inside (β ∪ χ '' i.1)) := by
    rw [← hrBb, ← hrB.image_eq]
    exact image_mono fun x hx => hx.1
  have hBX : i.1 ∩ frontier XK.space = {g i 0, g i 1} := (hgend i).symm
  refine ⟨i.1, hBCs, ξ '' β, ξ '' closure (Schoenflies.inside (β ∪ χ '' i.1)), γ₁, rB, hBe,
    hγ₁, by rw [hγ₁0, hγ₁1, hBX], hB₁J.trans inter_subset_right, by rw [hBB₁, hBX], hrB, hrBb,
    fun y hy => hEEc (hDM hy).1, fun y hy => ⟨hEN (hDM hy).1, fun hyK => (hDM hy).2 ?_⟩, ?_, ?_⟩
  · exact hEK.subset ⟨hEEc (hDM hy).1, hyK⟩
  · apply Subset.antisymm
    · rintro y ⟨hyD, hyX⟩
      have hyM := hDM hyD
      have hyJ : y ∈ J := ⟨hEEc hyM.1, hyX⟩
      have hcl := (hDmem y hyM).mp hyD
      have hχβ : χ y ∈ β := hclγ.subset ⟨hcl, mem_image_of_mem χ hyJ⟩
      exact ⟨χ y, hχβ, hξχ y hyM⟩
    · exact subset_inter (subset_union_right.trans hJ₁D) (hB₁J.trans inter_subset_right)
  · apply Subset.antisymm
    · rintro y ⟨hyD, hyΔ⟩
      have hyM := hDM hyD
      obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hA.subset ⟨hyΔ, mem_iUnion₂.mpr
        ⟨e, ⟨he, hcard⟩, hEEc hyM.1⟩⟩)
      have hSpre : IsPreconnected S := by
        obtain ⟨gS, hgS, -⟩ := hCs S hS
        rw [← hgS.image_eq]
        exact (convex_Icc (0 : ℝ) 1).isPreconnected.image gS hgS.isPiecewiseAffineOn.continuousOn
      have hSe : S ⊆ Ec e := hd.subset_pseudoCell_of_isPreconnected hSpre (hCsA S hS) he hcard
        ⟨y, hyS, hEEc hyM.1⟩
      by_cases hSi : (⟨S, hS, hSe⟩ : ι) = i
      · rw [← hSi]
        exact hyS
      · exact absurd ((hDmem y hyM).mp hyD) (Set.disjoint_left.mp (hothers _ hSi)
          (mem_image_of_mem χ hyS))
    · exact subset_inter (subset_union_left.trans hJ₁D) (hCsΔ i.1 hBCs)

end ArcDisk

end DifferentialGeometry.Topology.PiecewiseLinear
