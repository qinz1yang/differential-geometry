/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Torus
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.ToroidalShell

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [TopologicalSpace E] {Y T₀ T₁ : Set E}

private theorem fundamentalGroup_map_slice_bijective
    {M : Type*} [TopologicalSpace M] (φ : (M × unitInterval) ≃ₜ Y)
    (t : unitInterval) {T : Set E}
    (hT : T = Subtype.val '' (φ '' {p | (p.2 : ℝ) = t})) (hTY : T ⊆ Y) (x : T) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hTY, continuous_inclusion hTY⟩ : C(T, Y)) x) := by
  let f : M → E := fun p => (φ (p, t) : E)
  have hf : _root_.Topology.IsEmbedding f :=
    _root_.Topology.IsEmbedding.subtypeVal.comp (φ.isEmbedding.comp (isEmbedding_prodMkLeft t))
  have hrange : Set.range f = T := by
    rw [hT]
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨φ (p, t), ⟨(p, t), rfl, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨p, hp, rfl⟩, rfl⟩
      have ht : p.2 = t := Subtype.ext hp
      exact ⟨p.1, by simp only [f, ← ht]⟩
  let eT := hf.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let e := (φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex M (convex_Icc (0 : ℝ) 1) t)).trans
    eT.toHomotopyEquiv
  apply bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse e
  intro z
  apply Subtype.ext
  have hz : (z : E) ∈ Subtype.val '' (φ '' {p | (p.2 : ℝ) = t}) := by
    simpa only [← hT] using z.property
  obtain ⟨y, ⟨p, hp, rfl⟩, hpz⟩ := hz
  have hiz : Set.inclusion hTY z = φ p := Subtype.ext hpz.symm
  change (φ ((φ.symm (Set.inclusion hTY z)).1, t) : E) = z
  rw [hiz, φ.symm_apply_apply]
  have ht : p.2 = t := Subtype.ext hp
  simpa only [← ht, Prod.mk.eta] using hpz

theorem IsToroidalShell.fundamentalGroup_map_left_bijective
    (hY : IsToroidalShell Y T₀ T₁) (x : T₀) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hY.left_subset, continuous_inclusion hY.left_subset⟩ : C(T₀, Y)) x) := by
  obtain ⟨φ, h₀, _⟩ := hY
  exact fundamentalGroup_map_slice_bijective φ 0 h₀ _ x

theorem IsToroidalShell.fundamentalGroup_map_right_bijective
    (hY : IsToroidalShell Y T₀ T₁) (x : T₁) :
    Function.Bijective (FundamentalGroup.map
      (⟨Set.inclusion hY.right_subset, continuous_inclusion hY.right_subset⟩ : C(T₁, Y)) x) := by
  obtain ⟨φ, _, h₁⟩ := hY
  exact fundamentalGroup_map_slice_bijective φ 1 h₁ _ x

theorem IsToroidalShell.nonempty_fundamentalGroup_mulEquiv_intProd
    (hY : IsToroidalShell Y T₀ T₁) (x : Y) :
    Nonempty (FundamentalGroup Y x ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨φ, _, _⟩ := hY
  let p := φ.symm x
  let e := φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Icc (0 : ℝ) 1) p.2)
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e x p.1 rfl).trans
    (fundamentalGroupTorusEquivIntProd p.1)⟩

theorem IsToroidalShell.isMulCommutative_fundamentalGroup
    (hY : IsToroidalShell Y T₀ T₁) (x : Y) : IsMulCommutative (FundamentalGroup Y x) := by
  obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_mulEquiv_intProd x
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

theorem IsToroidalShell.nonempty_fundamentalGroup_interior_mulEquiv_intProd
    {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (x : interior Y) :
    Nonempty (FundamentalGroup (interior Y) x ≃* Multiplicative ℤ × Multiplicative ℤ) := by
  obtain ⟨φ⟩ := hY.nonempty_homeomorph_interior
  let p := φ.symm x
  let e := φ.symm.toHomotopyEquiv.trans
    (DifferentialGeometry.HomotopyEquiv.productConvex _ (convex_Ioo (0 : ℝ) 1) p.2)
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e x p.1 rfl).trans
    (fundamentalGroupTorusEquivIntProd p.1)⟩

theorem IsToroidalShell.isMulCommutative_fundamentalGroup_interior
    {Y T₀ T₁ : Set (EuclideanSpace ℝ (Fin 3))} (hY : IsToroidalShell Y T₀ T₁)
    (x : interior Y) : IsMulCommutative (FundamentalGroup (interior Y) x) := by
  obtain ⟨e⟩ := hY.nonempty_fundamentalGroup_interior_mulEquiv_intProd x
  apply isMulCommutative_iff.mpr
  intro a b
  apply e.injective
  simp only [map_mul, mul_comm]

end DifferentialGeometry.Topology.PiecewiseLinear
