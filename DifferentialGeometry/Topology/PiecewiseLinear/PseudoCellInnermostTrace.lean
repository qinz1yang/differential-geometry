/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellCentralTrace
import DifferentialGeometry.Topology.PiecewiseLinear.TopologicalCellInterior

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsTopologicalCellWithInterior.mem_inside_image_boundary
    {D I : Set E3} (hD : IsTopologicalCellWithInterior 2 D I)
    {Ψ : E3 → Schoenflies.Plane} (hΨc : ContinuousOn Ψ D) (hΨi : InjOn Ψ D)
    {P : E3} (hP : P ∈ I) : Ψ P ∈ Schoenflies.inside (Ψ '' (D \ I)) := by
  have hID : I ⊆ D := by
    obtain ⟨φ, rfl⟩ := hD
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have himg := hD.image_of_injOn hΨc hΨi
  obtain ⟨θ⟩ := himg.isTopologicalCell
  have hcpt := isCompact_of_homeomorphClosedBall θ
  have hJ := PlanarJordan.isJordanCurve_frontier_of_homeomorphClosedBall θ
  have hi := PlanarJordan.interior_eq_inside_frontier_of_isCompact hcpt hJ
    (interior_nonempty_of_homeomorphClosedBall θ)
  have hfr : frontier (Ψ '' D) = Ψ '' (D \ I) := by
    rw [frontier, hcpt.isClosed.closure_eq, himg.interior_eq, ← hΨi.image_sdiff_subset hID]
  rw [← hfr, ← hi, himg.interior_eq]
  exact ⟨P, hP, rfl⟩

theorem IsPseudoCell.exists_innermost_disk_of_noncentral_trace
    {Ec Eint Ebd Dc Dcint Δ : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    {n : ℕ} {G : Fin n → Set E3} (hG : ∀ i, IsPLSphere 1 (G i))
    (hdisj : Pairwise fun i j => Disjoint (G i) (G j)) (htrace : Δ ∩ Ec = ⋃ i, G i)
    (hGD : ∀ i, G i ⊆ Dc) (hGP : ∀ i, P ∉ G i) {i₀ : Fin n}
    (hnot : ¬ ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Dc ∧
      DJ \ DJint = G i₀ ∧ P ∈ DJint) :
    ∃ (i : Fin n) (D : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ r '' stdSimplexBoundary 2 = G i ∧
      D ⊆ Dc ∧ D ⊆ Eint \ {P} ∧ D ∩ Δ = G i ∧
      ¬ ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Dc ∧
        DJ \ DJint = G i ∧ P ∈ DJint := by
  classical
  have hEEc : Eint ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_left
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ :=
    hE.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ Eint := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hΦi : InjOn Φ (Metric.ball 0 1) := fun p hp q hq hpq => by
    rw [← hΨΦ p hp, ← hΨΦ q hq, hpq]
  have hGE : ∀ i, G i ⊆ Eint := fun i => (hGD i).trans hDcE
  have hGM : ∀ i, G i ⊆ Eint \ {P} := by
    intro i x hx
    exact ⟨hGE i hx, fun hxP => hGP i (mem_singleton_iff.mp hxP ▸ hx)⟩
  have hGΔ : ∀ i, G i ⊆ Δ := by
    intro i x hx
    have h : x ∈ Δ ∩ Ec := htrace.symm ▸ mem_iUnion.mpr ⟨i, hx⟩
    exact h.1
  have hJor : ∀ i, Schoenflies.IsJordanCurve (Ψ '' G i) := fun i =>
    isJordanCurve_image_of_isPLSphere_one (hG i) (hGE i) hΨc hΨi
  have hclb : ∀ i, closure (Schoenflies.inside (Ψ '' G i)) ⊆ Metric.ball 0 1 := fun i =>
    closure_inside_subset_ball (hJor i) (image_subset_iff.mpr fun x hx => hΨb (hGE i hx))
  let H : Finset (Fin n) := Finset.univ.filter fun i => Ψ P ∉ Schoenflies.inside (Ψ '' G i)
  have hi₀ : i₀ ∈ H := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hin => hnot ?_⟩
    refine ⟨Φ '' closure (Schoenflies.inside (Ψ '' G i₀)),
      Φ '' Schoenflies.inside (Ψ '' G i₀),
      (isTopologicalCellWithInterior_closure_inside (hJor i₀)).image_of_injOn
        (hΦc.mono (hclb i₀)) (hΦi.mono (hclb i₀)), ?_, ?_,
      ⟨Ψ P, hin, hΦΨ P hE.centerMem⟩⟩
    · exact hDc.chart_closure_inside_subset (hΨc.mono hDcE) (hΨi.mono hDcE)
        (fun x hx => hΦΨ x (hDcE hx)) (hG i₀) (hGD i₀)
    · rw [← (hΦi.mono (hclb i₀)).image_sdiff_subset subset_closure,
        closure_inside_eq_union (hJor i₀), union_sdiff_left,
        sdiff_eq_left.mpr (Set.disjoint_left.mpr fun p hp hpi =>
          Schoenflies.inside_subset_compl hpi hp), image_image]
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change Φ (Ψ x) ∈ G i₀
        rw [hΦΨ x (hGE i₀ hx)]
        exact hx
      · intro hy
        exact ⟨y, hy, hΦΨ y (hGE i₀ hy)⟩
  obtain ⟨i, hmin⟩ := H.exists_minimalFor (fun i => Schoenflies.inside (Ψ '' G i)) ⟨i₀, hi₀⟩
  have hgood := (Finset.mem_filter.mp hmin.1).2
  have hPcl : Ψ P ∉ closure (Schoenflies.inside (Ψ '' G i)) := by
    rw [closure_inside_eq_union (hJor i)]
    rintro (hin | ⟨y, hy, hyP⟩)
    · exact hgood hin
    · exact hGP i (hΨi (hGE i hy) hE.centerMem hyP ▸ hy)
  have hcl : closure (Schoenflies.inside (Ψ '' G i)) ⊆ Ψ '' (Eint \ {P}) := by
    intro p hp
    refine ⟨Φ p, ⟨hΦb (hclb i hp), fun hpP => hPcl ?_⟩, hΨΦ p (hclb i hp)⟩
    rw [← mem_singleton_iff.mp hpP, hΨΦ p (hclb i hp)]
    exact hp
  obtain ⟨r, hr, hrim, hDM, hDmem⟩ :=
    exists_isPLHomeomorphOn_chart_closure_inside hE.regular (hΨc.mono sdiff_subset)
      (hΦc.mono (image_subset_iff.mpr fun x hx => hΨb hx.1))
      (fun x hx => hΦΨ x hx.1) (hG i) (hGM i) hcl
  refine ⟨i, Φ '' closure (Schoenflies.inside (Ψ '' G i)), r, hr, hrim,
    hDc.chart_closure_inside_subset (hΨc.mono hDcE) (hΨi.mono hDcE)
      (fun x hx => hΦΨ x (hDcE hx)) (hG i) (hGD i), hDM, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro y ⟨hyD, hyΔ⟩
      have hyM := hDM hyD
      have hytrace : y ∈ ⋃ j, G j := htrace ▸ (show y ∈ Δ ∩ Ec from ⟨hyΔ, hEEc hyM.1⟩)
      obtain ⟨j, hyj⟩ := mem_iUnion.mp hytrace
      by_cases hji : j = i
      · exact hji ▸ hyj
      exfalso
      have hdisjG : Disjoint (Ψ '' G j) (Ψ '' G i) := by
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨z, hz, rfl⟩ ⟨w, hw, hwz⟩
        have hwz' := hΨi (hGE i hw) (hGE j hz) hwz
        exact Set.disjoint_left.mp (hdisj hji) hz (hwz' ▸ hw)
      have hyin : Ψ y ∈ Schoenflies.inside (Ψ '' G i) := by
        have h := (hDmem y hyM).mp hyD
        rw [closure_inside_eq_union (hJor i)] at h
        exact h.resolve_right fun hyc => Set.disjoint_left.mp hdisjG ⟨y, hyj, rfl⟩ hyc
      have hGin : Ψ '' G j ⊆ Schoenflies.inside (Ψ '' G i) := by
        rcases subset_inside_or_subset_outside (hJor i)
            ((hG j).isConnected_one.isPreconnected.image Ψ (hΨc.mono (hGE j))) hdisjG with
          hsub | hsub
        · exact hsub
        · exact absurd (hsub ⟨y, hyj, rfl⟩)
            (Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hyin)
      have hle : Schoenflies.inside (Ψ '' G j) ⊆ Schoenflies.inside (Ψ '' G i) :=
        subset_closure.trans
          (closure_inside_subset_inside_of_subset_inside (hJor i) (hJor j) hGin)
      have hjH : j ∈ H := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, fun hin => hgood (hle hin)⟩
      have hge := hmin.2 hjH hle
      exact Schoenflies.inside_subset_compl (hge (hGin ⟨y, hyj, rfl⟩)) ⟨y, hyj, rfl⟩
    · intro y hy
      refine ⟨?_, hGΔ i hy⟩
      rw [← hrim] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hr.bijOn.mapsTo hx.1
  · rintro ⟨DJ, DJint, hDJ, hDJD, hrim', hPDJ⟩
    have h := hDJ.mem_inside_image_boundary (hΨc.mono (hDJD.trans hDcE))
      (hΨi.mono (hDJD.trans hDcE)) hPDJ
    rw [hrim'] at h
    exact hgood h

end DifferentialGeometry.Topology.PiecewiseLinear
