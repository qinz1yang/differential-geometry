/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeSinglePolygonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellChartDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section CircleDisk

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_circle_eDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) {e : Finset E3} (he : e ∈ K.faces)
    (hcard : e.card = 2) {Δ : Set E3} (hΔN : Δ ⊆ interior N' \ h '' K.space)
    {Cs : Set (Set E3)} (hfin : Cs.Finite) (hdisj : Cs.PairwiseDisjoint id)
    (hA : Δ ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs)
    (hCs : ∀ S ∈ Cs, IsPreconnected S ∧
      ((IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) ∨ (S ∩ frontier XK.space).Nonempty))
    {c₀ : Set E3} (hc₀ : c₀ ∈ Cs) (hc₀e : c₀ ⊆ Ec e) (hc₀s : IsPLSphere 1 c₀)
    (hc₀X : Disjoint c₀ (frontier XK.space))
    (hgood : ¬ ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e ∧
      DJ \ DJint = c₀ ∧ h (e.centroid ℝ id) ∈ DJint) :
    ∃ c ∈ Cs, ∃ (Dc : Set E3) (rc : (Fin 3 → ℝ) → E3), IsPLSphere 1 c ∧ c ⊆ Ec e ∧
      Disjoint c (frontier XK.space) ∧ IsPLHomeomorphOn rc (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Dc ∧
      rc '' stdSimplexBoundary 2 = c ∧ Dc ⊆ Ec e ∧ Dc ⊆ interior N' \ h '' K.space ∧
      Disjoint Dc (frontier XK.space) ∧ Dc ∩ Δ = c := by
  classical
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hpc := hd.pseudoCell e he hcard
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hpc.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ (Eint e) := fun x hx y hy hxy => by rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hΦi : InjOn Φ (Metric.ball 0 1) := fun p hp q hq hpq => by
    rw [← hΨΦ p hp, ← hΨΦ q hq, hpq]
  have hEEc : Eint e ⊆ Ec e := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hEN : Eint e ⊆ interior N' := hd.interior_pseudoCell_subset_interior he hcard
  have hPE : h (e.centroid ℝ id) ∈ Eint e := hpc.centerMem
  have hEK : Ec e ∩ h '' K.space = {h (e.centroid ℝ id)} := hd.meetsGraph e he hcard
  have hCsΔ : ∀ S ∈ Cs, S ⊆ Δ := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).1
  have hCsA : ∀ S ∈ Cs, S ⊆ A := fun S hS y hy =>
    ((hA.symm ▸ mem_sUnion_of_mem hy hS : y ∈ Δ ∩ A)).2
  have hSM : ∀ S ∈ Cs, S ⊆ Ec e → S ⊆ Eint e \ {h (e.centroid ℝ id)} := by
    intro S hS hSe y hy
    have hyN := hΔN (hCsΔ S hS hy)
    refine ⟨?_, fun hyP => hyN.2 ?_⟩
    · have hEc : y ∈ Eint e ∪ Ebd e := hpc.carrierEq ▸ hSe hy
      refine hEc.resolve_right fun hbd => ?_
      rw [← hd.rimFrontier e he hcard] at hbd
      exact Set.disjoint_left.mp disjoint_interior_frontier hyN.1 hbd.2
    · rw [mem_singleton_iff.mp hyP]
      exact (hEK.symm.subset (mem_singleton _)).2
  set M := Eint e \ {h (e.centroid ℝ id)} with hMdef
  have hΨM : ContinuousOn Ψ M := hΨc.mono sdiff_subset
  have hΦM : ContinuousOn Φ (Ψ '' M) :=
    hΦc.mono (image_subset_iff.mpr fun x hx => hΨb hx.1)
  have hΦΨM : ∀ x ∈ M, Φ (Ψ x) = x := fun x hx => hΦΨ x hx.1
  have hjordan : ∀ S : Set E3, IsPLSphere 1 S → S ⊆ M →
      Schoenflies.IsJordanCurve (Ψ '' S) := fun S hS hSM =>
    isJordanCurve_image_of_isPLSphere_one hS (hSM.trans sdiff_subset) hΨc hΨi
  have hclball : ∀ S : Set E3, IsPLSphere 1 S → S ⊆ M →
      closure (Schoenflies.inside (Ψ '' S)) ⊆ Metric.ball 0 1 := fun S hS hSM =>
    closure_inside_subset_ball (hjordan S hS hSM)
      (image_subset_iff.mpr fun x hx => hΨb (hSM hx).1)
  set G := {S ∈ Cs | IsPLSphere 1 S ∧ Disjoint S (frontier XK.space) ∧ S ⊆ Ec e ∧
    Ψ (h (e.centroid ℝ id)) ∉ Schoenflies.inside (Ψ '' S)} with hGdef
  have hc₀G : c₀ ∈ G := by
    refine ⟨hc₀, hc₀s, hc₀X, hc₀e, fun hin => hgood ?_⟩
    have hc₀M := hSM c₀ hc₀ hc₀e
    have hγ := hjordan c₀ hc₀s hc₀M
    have hclb := hclball c₀ hc₀s hc₀M
    refine ⟨Φ '' closure (Schoenflies.inside (Ψ '' c₀)), Φ '' Schoenflies.inside (Ψ '' c₀),
      (isTopologicalCellWithInterior_closure_inside hγ).image_of_injOn (hΦc.mono hclb)
        (hΦi.mono hclb), ?_, ?_, ⟨Ψ (h (e.centroid ℝ id)), hin, hΦΨ _ hPE⟩⟩
    · rintro _ ⟨p, hp, rfl⟩
      exact hEEc (hΦb (hclb hp))
    · rw [← (hΦi.mono hclb).image_sdiff_subset subset_closure, closure_inside_eq_union hγ,
        union_sdiff_left, sdiff_eq_left.mpr (Set.disjoint_left.mpr fun p hp hpi =>
          Schoenflies.inside_subset_compl hpi hp), image_image]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change Φ (Ψ x) ∈ c₀
        rw [hΦΨ x (hc₀M hx).1]
        exact hx
      · intro hy
        exact ⟨y, hy, hΦΨ y (hc₀M hy).1⟩
  have hGfin : G.Finite := hfin.subset fun S hS => hS.1
  obtain ⟨c, ⟨hcCs, hcs, hcX, hce, hcgood⟩, hcmin⟩ :=
    hGfin.exists_minimalFor (fun S => Schoenflies.inside (Ψ '' S)) G ⟨c₀, hc₀G⟩
  have hcM := hSM c hcCs hce
  have hγ := hjordan c hcs hcM
  have hclb := hclball c hcs hcM
  have hPcl : Ψ (h (e.centroid ℝ id)) ∉ closure (Schoenflies.inside (Ψ '' c)) := by
    rw [closure_inside_eq_union hγ]
    rintro (h1 | ⟨y, hy, hyP⟩)
    · exact hcgood h1
    · exact (hcM hy).2 (hΨi (hcM hy).1 hPE hyP)
  have hcl : closure (Schoenflies.inside (Ψ '' c)) ⊆ Ψ '' M := by
    intro p hp
    refine ⟨Φ p, ⟨hΦb (hclb hp), fun hpP => hPcl ?_⟩, hΨΦ p (hclb hp)⟩
    rw [← mem_singleton_iff.mp hpP, hΨΦ p (hclb hp)]
    exact hp
  obtain ⟨rc, hrc, hrcb, hDM, hDmem⟩ :=
    exists_isPLHomeomorphOn_chart_closure_inside hpc.regular hΨM hΦM hΦΨM hcs hcM hcl
  have hDX : Disjoint (Φ '' closure (Schoenflies.inside (Ψ '' c))) (frontier XK.space) := by
    refine Set.disjoint_left.mpr fun y hyD hyX => ?_
    have hyM := hDM hyD
    have hT := h2.trace_subset hd he hcard
    have hJs : IsPLSphere 1 (Ec e ∩ frontier XK.space) := (h34 e he hcard).1
    have hγe := hjordan _ hJs hT
    have hPin := h2.center_mem_inside_trace hd h34 he hcard hΨc hΦc hΨb hΦb hΦΨ hΨΦ
    have hdisjγ : Disjoint (Ψ '' (Ec e ∩ frontier XK.space)) (Ψ '' c) := by
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
      have hzw := hΨi (hcM hw).1 (hT hz).1 hwz
      exact Set.disjoint_left.mp hcX (hzw ▸ hw) hz.2
    have hyin : Ψ y ∈ Schoenflies.inside (Ψ '' c) := by
      have h1 := (hDmem y hyM).mp hyD
      rw [closure_inside_eq_union hγ] at h1
      refine h1.resolve_right fun h2' => Set.disjoint_left.mp hdisjγ ⟨y, ⟨hEEc hyM.1, hyX⟩, rfl⟩
        h2'
    rcases subset_inside_or_subset_outside hγ
        ((hJs.isConnected_one.isPreconnected).image Ψ (hΨc.mono (hT.trans sdiff_subset)))
        hdisjγ with hsub | hsub
    · exact hcgood (closure_inside_subset_inside_of_subset_inside hγ hγe hsub
        (subset_closure hPin))
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyin
        (hsub ⟨y, ⟨hEEc hyM.1, hyX⟩, rfl⟩)
  refine ⟨c, hcCs, Φ '' closure (Schoenflies.inside (Ψ '' c)), rc, hcs, hce, hcX, hrc, hrcb,
    fun y hy => hEEc (hDM hy).1, fun y hy => ⟨hEN (hDM hy).1, fun hyK => (hDM hy).2 ?_⟩, hDX,
    ?_⟩
  · exact hEK.subset ⟨hEEc (hDM hy).1, hyK⟩
  · apply Subset.antisymm
    · rintro y ⟨hyD, hyΔ⟩
      have hyM := hDM hyD
      obtain ⟨S, hS, hyS⟩ := mem_sUnion.mp (hA.subset ⟨hyΔ, mem_iUnion₂.mpr
        ⟨e, ⟨he, hcard⟩, hEEc hyM.1⟩⟩)
      by_cases hSc : S = c
      · exact hSc ▸ hyS
      exfalso
      have hSe : S ⊆ Ec e := hd.subset_pseudoCell_of_isPreconnected (hCs S hS).1 (hCsA S hS)
        he hcard ⟨y, hyS, hEEc hyM.1⟩
      have hSM' := hSM S hS hSe
      have hdSc : Disjoint S c := hdisj hS hcCs hSc
      have hdisjS : Disjoint (Ψ '' S) (Ψ '' c) := by
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
        have hzw := hΨi (hcM hw).1 (hSM' hz).1 hwz
        exact Set.disjoint_left.mp hdSc hz (hzw ▸ hw)
      have hyin : Ψ y ∈ Schoenflies.inside (Ψ '' c) := by
        have h1 := (hDmem y hyM).mp hyD
        rw [closure_inside_eq_union hγ] at h1
        exact h1.resolve_right fun h2' => Set.disjoint_left.mp hdisjS ⟨y, hyS, rfl⟩ h2'
      have hSin : Ψ '' S ⊆ Schoenflies.inside (Ψ '' c) := by
        rcases subset_inside_or_subset_outside hγ ((hCs S hS).1.image Ψ
            (hΨc.mono (hSM'.trans sdiff_subset))) hdisjS with hsub | hsub
        · exact hsub
        · exact absurd (hsub ⟨y, hyS, rfl⟩)
            (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyin)
      rcases (hCs S hS).2 with ⟨hSs, hSX⟩ | ⟨z, hzS, hzX⟩
      · have hγS := hjordan S hSs hSM'
        have hle : Schoenflies.inside (Ψ '' S) ⊆ Schoenflies.inside (Ψ '' c) :=
          subset_closure.trans (closure_inside_subset_inside_of_subset_inside hγ hγS hSin)
        have hSG : S ∈ G := ⟨hS, hSs, hSX, hSe, fun hin => hcgood (hle hin)⟩
        have hge := hcmin hSG hle
        exact Schoenflies.inside_subset_compl (hge (hSin ⟨y, hyS, rfl⟩)) ⟨y, hyS, rfl⟩
      · have hzD : z ∈ Φ '' closure (Schoenflies.inside (Ψ '' c)) :=
          (hDmem z (hSM' hzS)).mpr (subset_closure (hSin ⟨z, hzS, rfl⟩))
        exact Set.disjoint_left.mp hDX hzD hzX
    · intro y hy
      refine ⟨?_, hCsΔ c hcCs hy⟩
      rw [← hrcb] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hrc.bijOn.mapsTo hx.1

end CircleDisk

end DifferentialGeometry.Topology.PiecewiseLinear
