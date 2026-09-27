/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellChartDisks

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem central_trace_enclosing_curve (𝒞 : Finset (Set Schoenflies.Plane))
    (h𝒞 : ∀ γ ∈ 𝒞, Schoenflies.IsJordanCurve γ)
    (hdisj : ∀ γ ∈ 𝒞, ∀ γ' ∈ 𝒞, γ ≠ γ' → Disjoint γ γ') {C : Set Schoenflies.Plane}
    (hC : IsCompact C) (hCo : IsOpen (C \ ⋃ γ ∈ 𝒞, γ))
    {c : Schoenflies.Plane} (hc : c ∈ C) (hc𝒞 : ∀ γ ∈ 𝒞, c ∉ γ) :
    ∃ γ ∈ 𝒞, c ∈ Schoenflies.inside γ := by
  classical
  have hcU : c ∉ ⋃ γ ∈ 𝒞, γ := by
    simp only [mem_iUnion, not_exists]
    exact fun γ hγ => hc𝒞 γ hγ
  have hkey : ∀ A : Set Schoenflies.Plane, IsPreconnected A → Disjoint A (⋃ γ ∈ 𝒞, γ) →
      c ∈ A → A ⊆ C := by
    intro A hA hAU hcA
    have hsub := hA.subset_left_of_subset_union hCo hC.isClosed.isOpen_compl
      (Set.disjoint_left.mpr fun z hz hz' => hz' hz.1)
      (fun z hz => by
        by_cases hzC : z ∈ C
        · exact Or.inl ⟨hzC, Set.disjoint_left.mp hAU hz⟩
        · exact Or.inr hzC)
      ⟨c, hcA, hc, hcU⟩
    exact hsub.trans sdiff_subset
  by_contra hnone
  push Not at hnone
  have hA := isPreconnected_compl_union_iUnion_closure_inside 𝒞 h𝒞 hdisj isClosed_empty
    (by rw [compl_empty]; exact isPreconnected_univ) (fun γ _ => Set.empty_disjoint _)
  rw [empty_union] at hA
  have hcA : c ∈ (⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ))ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro γ hγ hcγ
    rw [closure_inside_eq_union (h𝒞 γ hγ)] at hcγ
    rcases hcγ with h | h
    · exact hnone γ hγ h
    · exact hc𝒞 γ hγ h
  have hAU : Disjoint (⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ))ᶜ (⋃ γ ∈ 𝒞, γ) := by
    rw [Set.disjoint_compl_left_iff_subset]
    exact iUnion₂_mono fun γ hγ => by
      rw [closure_inside_eq_union (h𝒞 γ hγ)]
      exact subset_union_right
  have hsub := hkey _ hA hAU hcA
  have hcpt : IsCompact (C ∪ ⋃ γ ∈ 𝒞, closure (Schoenflies.inside γ)) :=
    hC.union (𝒞.isCompact_biUnion fun γ hγ =>
      (Schoenflies.jordan_curve_theorem (h𝒞 γ hγ)).isBounded_inside.isCompact_closure)
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcpt.ne_univ
  exact hz (Or.inl (hsub fun hz' => hz (Or.inr hz')))

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTopologicalCellWithInterior.chart_closure_inside_subset
    {Dc Dcint J : Set E3} (hDc : IsTopologicalCellWithInterior 2 Dc Dcint)
    {Ψ : E3 → Schoenflies.Plane} {Φ : Schoenflies.Plane → E3}
    (hΨc : ContinuousOn Ψ Dc) (hΨi : InjOn Ψ Dc) (hΦΨ : ∀ x ∈ Dc, Φ (Ψ x) = x)
    (hJ : IsPLSphere 1 J) (hJD : J ⊆ Dc) :
    Φ '' closure (Schoenflies.inside (Ψ '' J)) ⊆ Dc := by
  have hJor := isJordanCurve_image_of_isPLSphere_one hJ hJD hΨc hΨi
  have hDc' := hDc.image_of_injOn hΨc hΨi
  obtain ⟨θ⟩ := hDc'.isTopologicalCell
  have : CompactSpace (Metric.closedBall (0 : Schoenflies.Plane) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have hDcpt : IsCompact (Ψ '' Dc) := isCompact_iff_compactSpace.mpr θ.symm.compactSpace
  have hDjor := PlanarJordan.isJordanCurve_frontier_of_homeomorphClosedBall θ
  have hDeq := PlanarJordan.closure_inside_frontier_eq_of_isCompact hDcpt hDjor
    (interior_nonempty_of_homeomorphClosedBall θ)
  have hclD : closure (Schoenflies.inside (Ψ '' J)) ⊆ Ψ '' Dc := by
    rw [← hDeq]
    apply closure_mono
    exact PlanarJordan.inside_subset_of_subset_closure_inside
      (Schoenflies.jordan_curve_theorem hDjor) (Schoenflies.jordan_curve_theorem hJor)
      (hDeq.symm ▸ image_mono hJD)
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hclD hp
  rw [hΦΨ x hx]
  exact hx

theorem IsPseudoCell.exists_central_disk_of_finite_trace
    {Ec Eint Ebd Bl Dc Dcint : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (hBl : IsPLBall 3 Bl) (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hBE : Bl ∩ Ec ⊆ Dc) {n : ℕ} {G : Fin n → Set E3}
    (hG : ∀ i, IsPLSphere 1 (G i)) (hdisj : Pairwise fun i j => Disjoint (G i) (G j))
    (htrace : frontier Bl ∩ Ec = ⋃ i, G i) :
    ∃ (i : Fin n) (DJ DJint : Set E3), IsTopologicalCellWithInterior 2 DJ DJint ∧
      DJ ⊆ Dc ∧ DJ \ DJint = G i ∧ P ∈ DJint := by
  classical
  have hEEc : Eint ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_left
  have hBlc := hBl.isPolyhedron.isClosed
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, hΨo⟩ :=
    hE.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ Eint := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hΦi : InjOn Φ (Metric.ball 0 1) := fun p hp q hq hpq => by
    rw [← hΨΦ p hp, ← hΨΦ q hq, hpq]
  have hGT : ∀ i, G i ⊆ frontier Bl ∩ Ec := by
    intro i x hx
    rw [htrace]
    exact mem_iUnion.mpr ⟨i, hx⟩
  have hGD : ∀ i, G i ⊆ Dc := fun i x hx =>
    hBE ⟨hBlc.frontier_subset (hGT i hx).1, (hGT i hx).2⟩
  have hGE : ∀ i, G i ⊆ Eint := fun i => (hGD i).trans hDcE
  let 𝒞 : Finset (Set Schoenflies.Plane) := Finset.univ.image fun i : Fin n => Ψ '' G i
  have hU𝒞 : (⋃ γ ∈ 𝒞, γ) = Ψ '' (Ec ∩ frontier Bl) := by
    simp only [𝒞, Finset.set_biUnion_finset_image, Finset.mem_univ, iUnion_true]
    rw [← image_iUnion, ← htrace, inter_comm]
  have hEX : Eint ∩ Bl = Ec ∩ Bl := by
    apply Subset.antisymm
    · exact inter_subset_inter_left Bl hEEc
    · exact fun x hx => ⟨hDcE (hBE ⟨hx.2, hx.1⟩), hx.2⟩
  have hTE : Ec ∩ frontier Bl ⊆ Eint ∩ Bl := fun x hx =>
    ⟨hDcE (hBE ⟨hBlc.frontier_subset hx.2, hx.1⟩), hBlc.frontier_subset hx.2⟩
  let Cp : Set Schoenflies.Plane := Ψ '' (Eint ∩ Bl)
  have hCp : IsCompact Cp := by
    refine IsCompact.image_of_continuousOn ?_ (hΨc.mono inter_subset_left)
    rw [hEX]
    exact hBl.isPolyhedron.isCompact.inter_left hE.isClosed
  have hCo : IsOpen (Cp \ ⋃ γ ∈ 𝒞, γ) := by
    have heq : Cp \ ⋃ γ ∈ 𝒞, γ = Ψ '' (interior Bl ∩ Eint) := by
      rw [hU𝒞]
      ext p
      constructor
      · rintro ⟨⟨y, ⟨hyE, hyB⟩, rfl⟩, hpT⟩
        exact ⟨y, ⟨(mem_interior_iff_notMem_frontier hyB).mpr fun hfr =>
          hpT ⟨y, ⟨hEEc hyE, hfr⟩, rfl⟩, hyE⟩, rfl⟩
      · rintro ⟨y, ⟨hyi, hyE⟩, rfl⟩
        refine ⟨⟨y, ⟨hyE, interior_subset hyi⟩, rfl⟩, ?_⟩
        rintro ⟨z, hz, hzy⟩
        have hzy' := hΨi (hTE hz).1 hyE hzy
        rw [hzy'] at hz
        exact hz.2.2 hyi
    rw [heq]
    exact hΨo _ isOpen_interior
  have hJor : ∀ i, Schoenflies.IsJordanCurve (Ψ '' G i) := fun i =>
    isJordanCurve_image_of_isPLSphere_one (hG i) (hGE i) hΨc hΨi
  have h𝒞 : ∀ γ ∈ 𝒞, Schoenflies.IsJordanCurve γ := by
    intro γ hγ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
    exact hJor i
  have h𝒞d : ∀ γ ∈ 𝒞, ∀ γ' ∈ 𝒞, γ ≠ γ' → Disjoint γ γ' := by
    intro γ hγ γ' hγ' hne
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hγ'
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hyx' := hΨi (hGE j hy) (hGE i hx) hyx
    rw [hyx'] at hy
    exact Set.disjoint_left.mp (hdisj hij) hx hy
  have hcC : Ψ P ∈ Cp := ⟨P, ⟨hE.centerMem, interior_subset hP⟩, rfl⟩
  have hc𝒞 : ∀ γ ∈ 𝒞, Ψ P ∉ γ := by
    intro γ hγ hPγ
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨x, hx, hxP⟩ := hPγ
    have hxP' := hΨi (hGE i hx) hE.centerMem hxP
    exact (hGT i hx).1.2 (hxP'.symm ▸ hP)
  obtain ⟨γ, hγ, hcγ⟩ := central_trace_enclosing_curve 𝒞 h𝒞 h𝒞d hCp hCo hcC hc𝒞
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hγ
  have hclb : closure (Schoenflies.inside (Ψ '' G i)) ⊆ Metric.ball 0 1 :=
    closure_inside_subset_ball (hJor i) (image_subset_iff.mpr fun x hx => hΨb (hGE i hx))
  refine ⟨i, Φ '' closure (Schoenflies.inside (Ψ '' G i)),
    Φ '' Schoenflies.inside (Ψ '' G i),
    (isTopologicalCellWithInterior_closure_inside (hJor i)).image_of_injOn
      (hΦc.mono hclb) (hΦi.mono hclb), ?_, ?_, ⟨Ψ P, hcγ, hΦΨ P hE.centerMem⟩⟩
  · exact hDc.chart_closure_inside_subset (hΨc.mono hDcE) (hΨi.mono hDcE)
      (fun x hx => hΦΨ x (hDcE hx)) (hG i) (hGD i)
  · rw [← (hΦi.mono hclb).image_sdiff_subset subset_closure,
      closure_inside_eq_union (hJor i), union_sdiff_left,
      sdiff_eq_left.mpr (Set.disjoint_left.mpr fun p hp hpi =>
        Schoenflies.inside_subset_compl hpi hp), image_image]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change Φ (Ψ x) ∈ G i
      rw [hΦΨ x (hGE i hx)]
      exact hx
    · intro hy
      exact ⟨y, hy, hΦΨ y (hGE i hy)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
