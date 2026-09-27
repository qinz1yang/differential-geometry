/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceState

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsCanonicalTower.isClosed_towerSurface_of_even_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (E L : ℤ → Set E3) (hE : ∀ i, IsClosed (E (2 * i)))
    (hET : ∀ i, E (2 * i) ⊆ T'' (2 * i)) (hL : ∀ i, IsClosed (L i))
    (hcarrier : ∀ i, L i ⊆ (φ '' S (2 * i) ∪ φ '' S (2 * i + 1)) ∪
      φ '' S (2 * (i + 1))) :
    IsClosed (((↑) : I → E3) ⁻¹' towerSurface E L P') := by
  have hfinite {U : Set E3} (hU : {k | (φ '' S k ∩ U).Nonempty}.Finite) :
      {i | ((E (2 * i) ∪ L i) ∩ U).Nonempty}.Finite := by
    have h₀ : {i : ℤ | (φ '' S (2 * i) ∩ U).Nonempty}.Finite :=
      hU.preimage (f := fun i : ℤ => 2 * i) (by
        intro a _ b _ hab
        change 2 * a = 2 * b at hab
        omega)
    have h₁ : {i : ℤ | (φ '' S (2 * i + 1) ∩ U).Nonempty}.Finite :=
      hU.preimage (f := fun i : ℤ => 2 * i + 1) (by
        intro a _ b _ hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)
    have h₂ : {i : ℤ | (φ '' S (2 * (i + 1)) ∩ U).Nonempty}.Finite :=
      hU.preimage (f := fun i : ℤ => 2 * (i + 1)) (by
        intro a _ b _ hab
        change 2 * (a + 1) = 2 * (b + 1) at hab
        omega)
    apply ((h₀.union h₁).union h₂).subset
    rintro i ⟨x, hx, hxU⟩
    rcases hx with hxT | hxL
    · exact Or.inl (Or.inl ⟨x, htw.boundary_subset_outer _ (hET i hxT), hxU⟩)
    · rcases hcarrier i hxL with (hxLo | hxMid) | hxHi
      · exact Or.inl (Or.inl ⟨x, hxLo, hxU⟩)
      · exact Or.inl (Or.inr ⟨x, hxMid, hxU⟩)
      · exact Or.inr ⟨x, hxHi, hxU⟩
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have hxP : (x : E3) ≠ P' := fun heq => hx (Or.inr heq)
  obtain ⟨U, hU, hfin⟩ := htw.locallyFinite x x.property hxP
  let F := ⋃ i ∈ {i | ((E (2 * i) ∪ L i) ∩ U).Nonempty}, E (2 * i) ∪ L i
  have hFc : IsClosed F := (hfinite hfin).isClosed_biUnion fun i _ =>
    (hE i).union (hL i)
  have hxF : (x : E3) ∉ F := by
    intro hxF
    obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp hxF
    exact hx (Or.inl (mem_iUnion.mpr ⟨i, hi⟩))
  have hnear : U ∩ Fᶜ ∩ ({P'} : Set E3)ᶜ ∈ 𝓝 (x : E3) :=
    Filter.inter_mem (Filter.inter_mem hU (hFc.isOpen_compl.mem_nhds hxF))
      (isClosed_singleton.isOpen_compl.mem_nhds hxP)
  have hpre : ((↑) : I → E3) ⁻¹' (U ∩ Fᶜ ∩ ({P'} : Set E3)ᶜ) ∈ 𝓝 x :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hnear
  apply Filter.mem_of_superset hpre
  intro y hy hyM
  rcases hyM with hyM | hyP
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hyM
    exact hy.1.2 (mem_iUnion₂.mpr ⟨i, ⟨(y : E3), hi, hy.1.1⟩, hi⟩)
  · exact hy.2 hyP

end DifferentialGeometry.Topology.PiecewiseLinear
