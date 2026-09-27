/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyPolyhedral

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.isPolyhedron
    {X J₀ J₁ : Set E3} (h : IsPLAnnulusWithEnds X J₀ J₁) :
    IsPolyhedron X := by
  obtain ⟨J, ρ, hJ, hρ, -, -⟩ := h
  have hsource : IsPolyhedron (J ×ˢ Icc (0 : ℝ) 1) :=
    hJ.isPolyhedron.prod isHPolytope_Icc.isPolyhedron
  rw [← hρ.image_eq]
  exact hsource.image_of_isPiecewiseAffineOn hρ.isPiecewiseAffineOn hρ.bijOn.injOn

theorem IsAnnularChain.half_isPolyhedron
    {H B Jlo Jhi S' S'' T'' : ℤ → Set E3} {P' : E3}
    (h : IsAnnularChain H B Jlo Jhi S' S'' T'' P') (i : ℤ) :
    IsPolyhedron (H i) := (h.half i).isPolyhedron

theorem IsAnnularChain.bridge_isPolyhedron
    {H B Jlo Jhi S' S'' T'' : ℤ → Set E3} {P' : E3}
    (h : IsAnnularChain H B Jlo Jhi S' S'' T'' P') (i : ℤ) :
    IsPolyhedron (B i) := (h.bridge i).isPolyhedron

theorem IsAnnularChain.annularChain_subset_interior
    {φ : E3 → E3} {Pt : ℤ → E3}
    {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}
    {Dimg Dbdimg W I : Set E3} {P' : E3}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    annularChain H B P' ⊆ I := by
  rintro x (hx | hx)
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rcases hi with hi | hi
    · exact htw.subsetInterior (2 * i) (hch.halfSubsetTorus i hi)
    · rcases hch.bridgeSubset i hi with (h₀ | h₁) | h₂
      · exact htw.subsetInterior (2 * i) h₀
      · exact htw.subsetInterior (2 * i + 1) h₁
      · exact htw.subsetInterior (2 * i + 2) h₂
  · exact mem_singleton_iff.mp hx ▸ htw.centerMemInterior

open Classical in
theorem IsAnnularChain.locallyPolyhedral_off_center
    {φ : E3 → E3} {Pt : ℤ → E3}
    {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}
    {Dimg Dbdimg W I : Set E3} {P' : E3}
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    IsLocallyPolyhedral (annularChain H B P' \ {P'}) := by
  intro x hx
  have hxI : x ∈ I := hch.annularChain_subset_interior htw hx.1
  have hxP : x ≠ P' := by simpa using hx.2
  obtain ⟨U, hU, hF⟩ := htw.locallyFinite x hxI hxP
  let F : Set ℤ := {j | ((φ '' S j) ∩ U).Nonempty}
  have hfinite (k : ℤ) : {i : ℤ | 2 * i + k ∈ F}.Finite := by
    change ((fun i : ℤ => 2 * i + k) ⁻¹' F).Finite
    apply Set.Finite.preimage (s := F) ?_ hF
    intro i _ j _ hij
    dsimp at hij
    omega
  let L : Set ℤ := {i | 2 * i ∈ F} ∪
    {i | 2 * i + 1 ∈ F} ∪ {i | 2 * i + 2 ∈ F}
  have hL : L.Finite := by
    have h₀ : {i : ℤ | 2 * i ∈ F}.Finite := by simpa using hfinite 0
    exact (h₀.union (hfinite 1)).union (hfinite 2)
  let P : Set E3 := ⋃ i : L, H i ∪ B i
  have hPpoly : IsPolyhedron P := by
    let _ : Finite L := hL.to_subtype
    exact IsPolyhedron.iUnion fun i : L =>
      (hch.half_isPolyhedron i).union (hch.bridge_isPolyhedron i)
  have hPsub : P ⊆ annularChain H B P' \ {P'} := by
    intro y hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hy
    refine ⟨Or.inl (mem_iUnion.mpr ⟨i, hi⟩), ?_⟩
    intro hyP
    have : P' ∈ H i ∪ B i := by simpa only [mem_singleton_iff.mp hyP] using hi
    exact (hch.centerNotMem i) this
  refine ⟨P, hPpoly, hPsub,
    mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨U, hU, ?_⟩⟩
  intro y hy
  obtain ⟨hyU, hychain⟩ := hy
  have hyouter : y ∈ ⋃ i, H i ∪ B i := by
    rcases (show y ∈ (⋃ i, H i ∪ B i) ∪ {P'} from hychain.1) with h | h
    · exact h
    · exact False.elim (hychain.2 h)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hyouter
  have hiL : i ∈ L := by
    rcases hi with hiH | hiB
    · exact Or.inl (Or.inl ⟨y, hch.halfSubsetTorus i hiH, hyU⟩)
    · rcases hch.bridgeSubset i hiB with (h₀ | h₁) | h₂
      · exact Or.inl (Or.inl ⟨y, h₀, hyU⟩)
      · exact Or.inl (Or.inr ⟨y, h₁, hyU⟩)
      · exact Or.inr ⟨y, h₂, hyU⟩
  exact mem_iUnion.mpr ⟨⟨i, hiL⟩, hi⟩

end DifferentialGeometry.Topology.PiecewiseLinear
