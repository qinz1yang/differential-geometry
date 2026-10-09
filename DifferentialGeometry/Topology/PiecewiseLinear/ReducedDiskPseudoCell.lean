/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellCentralSphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellReducedTrace

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_reducedDisk_of_crossesPseudoCell {Ec Eint Ebd Bl Dc Dcint Ω : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) (hBl : IsPLBall 3 Bl) (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint) (hPDc : P ∈ Dcint)
    (hBE : Bl ∩ Ec ⊆ Dc) (hgp : CrossesPseudoCell (frontier Bl) Ec Eint P) (hΩ : IsOpen Ω)
    (hBlΩ : Bl ⊆ Ω) (hDcΩ : Dc ⊆ Ω) :
    ∃ (Δ Δbd : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ Δbd = r '' stdSimplexBoundary 2 ∧
      Δ ⊆ Ω ∧ Δbd = Δ ∩ Ec ∧
      ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec ∧
        DJ \ DJint = Δbd ∧ P ∈ DJint := by
  classical
  have hPE : P ∈ Eint := by
    obtain ⟨φ, hφ⟩ := hDc
    rw [hφ] at hPDc
    obtain ⟨x, -, hxP⟩ := hPDc
    exact hxP ▸ hDcE x.property
  have hE' : IsPseudoCell Ec Eint Ebd P := { hE with centerMem := hPE }
  have hEint : Eint ⊆ Ec := by
    rw [hE.carrierEq]
    exact subset_union_left
  obtain ⟨n, G, hG, hdisj, htrace, hregular, -⟩ := hgp
  have hGD : ∀ i, G i ⊆ Dc := by
    intro i x hx
    have hxtrace : x ∈ frontier Bl ∩ Ec := htrace.symm ▸ mem_iUnion.mpr ⟨i, hx⟩
    exact hBE ⟨hBl.isPolyhedron.isClosed.frontier_subset hxtrace.1, hxtrace.2⟩
  have hGP : ∀ i, P ∉ G i := by
    intro i hPi
    exact (hregular (mem_iUnion.mpr ⟨i, hPi⟩)).2 rfl
  obtain ⟨i₀, Δ, r, DJ, DJint, hr, hΔBl, hrim, hDJ, hDJDc, hDJrim, hPDJ, -, hnoncentral,
      hΔtrace⟩ := hE'.exists_central_sphere_disk hBl hP hDc hDcE hBE hG hdisj htrace
  let S := {i : Fin n | G i ⊆ Δ}
  let m := Fintype.card S
  let e : Fin m ≃ S := (Fintype.equivFin S).symm
  let H : Fin m → Set E3 := fun i => G (e i).1
  have hHtrace : Δ ∩ Ec = ⋃ i, H i := by
    rw [hΔtrace]
    exact (e.surjective.iUnion_comp fun i : S => G i.1).symm
  have hJΔ : G i₀ ⊆ Δ := by
    rw [← hrim, ← hr.image_eq]
    exact image_mono fun x hx => hx.1
  have hHfamily : ∃ i, H i = G i₀ := by
    refine ⟨e.symm ⟨i₀, hJΔ⟩, ?_⟩
    simp only [H, Equiv.apply_symm_apply]
  have hΔΩ : Δ ⊆ Ω :=
    hΔBl.trans (hBl.isPolyhedron.isClosed.frontier_subset.trans hBlΩ)
  obtain ⟨Δ', q, hq, hqbd, hΔ'Ω, hΔ'E⟩ :=
    hE'.exists_reduced_disk_of_finite_trace hDc hDcE hDcΩ hΩ
      ⟨DJ, DJint, hDJ, hDJDc, hDJrim, hPDJ⟩ hr hΔΩ hrim
      (fun i => hG (e i).1)
      (fun i j hij => hdisj fun heq => hij (e.injective (Subtype.ext heq))) hHtrace
      (fun i => hGD (e i).1) (fun i => hGP (e i).1) hHfamily
      (fun i hi => hnoncentral (e i).1 (fun heq => hi (congrArg G heq)) (e i).property)
  exact ⟨Δ', G i₀, q, hq, hqbd.symm, hΔ'Ω, hΔ'E.symm, DJ, DJint, hDJ,
    hDJDc.trans (hDcE.trans hEint), hDJrim, hPDJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
