import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Manifold.BoundaryExtrema
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold

open DifferentialGeometry.Topology.Morse

namespace Poincare.Topology.Ehresmann

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable {W : Type} [TopologicalSpace W] [ChartedSpace H W]

structure RegularIntervalDatum (I : ModelWithCorners ℝ E H)
    (u : W → ℝ) (a b : ℝ) : Prop where
  lt : a < b
  smooth : ContMDiff I 𝓘(ℝ) (↑(⊤ : ℕ∞) : WithTop ℕ∞) u
  range_eq : Set.range u = Set.Icc a b
  boundary_eq :
    I.boundary W = u ⁻¹' ({a} : Set ℝ) ∪ u ⁻¹' ({b} : Set ℝ)
  boundary_disjoint :
    Disjoint (u ⁻¹' ({a} : Set ℝ)) (u ⁻¹' ({b} : Set ℝ))
  noncritical : ∀ x, ¬ IsCriticalPointAt I u x

theorem RegularIntervalDatum.boundary_values
    {I : ModelWithCorners ℝ E H} {u : W → ℝ} {a b : ℝ}
    (h : RegularIntervalDatum I u a b) (w : W) (hw : I.IsBoundaryPoint w) :
    u w = a ∨ u w = b := by
  change w ∈ I.boundary W at hw
  rw [h.boundary_eq] at hw
  exact hw

theorem RegularIntervalDatum.boundary_level_left
    {I : ModelWithCorners ℝ E H} {u : W → ℝ} {a b : ℝ}
    (h : RegularIntervalDatum I u a b) :
    {w : W | I.IsBoundaryPoint w ∧ u w = a} = u ⁻¹' {a} := by
  ext w
  refine ⟨fun hw ↦ hw.2, fun hw ↦ ⟨?_, hw⟩⟩
  change w ∈ I.boundary W
  rw [h.boundary_eq]
  exact Or.inl hw

theorem RegularIntervalDatum.boundary_level_right
    {I : ModelWithCorners ℝ E H} {u : W → ℝ} {a b : ℝ}
    (h : RegularIntervalDatum I u a b) :
    {w : W | I.IsBoundaryPoint w ∧ u w = b} = u ⁻¹' {b} := by
  ext w
  refine ⟨fun hw ↦ hw.2, fun hw ↦ ⟨?_, hw⟩⟩
  change w ∈ I.boundary W
  rw [h.boundary_eq]
  exact Or.inr hw

theorem regularIntervalDatum_of_boundary_values [CompactSpace W] [PreconnectedSpace W]
    {I : ModelWithCorners ℝ E H} {u : W → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ Set.range u) (hb : b ∈ Set.range u) :
    RegularIntervalDatum I u a b where
  lt := hab
  smooth := hu
  range_eq := Poincare.Topology.Manifold.range_eq_Icc_of_boundary_values hab.le hreg hboundary ha hb
  boundary_eq := Poincare.Topology.Manifold.boundary_eq_preimage_endpoints_of_boundary_values
    hab.le hreg hboundary
  boundary_disjoint := by
    apply Set.disjoint_left.mpr
    intro x hxa hxb
    exact hab.ne ((show u x = a from hxa).symm.trans (show u x = b from hxb))
  noncritical := hreg

private theorem one_mem_posTangentConeAt_Ici (x : ℝ) :
    (1 : ℝ) ∈ posTangentConeAt (Set.Ici x) x := by
  rw [one_mem_posTangentConeAt_iff_mem_closure]
  rw [Set.inter_eq_left.mpr Set.Ioi_subset_Ici_self, closure_Ioi]
  exact le_refl x

theorem hasDerivWithinAt_pos_of_localMinOn_Ici
    {g : ℝ → ℝ} {x d : ℝ}
    (hmin : IsLocalMinOn g (Set.Ici x) x)
    (hderiv : HasDerivWithinAt g d (Set.Ici x) x)
    (hne : d ≠ 0) :
    0 < d := by
  have hd : 0 ≤ d := by
    have h := hmin.hasFDerivWithinAt_nonneg hderiv.hasFDerivWithinAt
      (one_mem_posTangentConeAt_Ici x)
    simpa using h
  exact lt_of_le_of_ne hd hne.symm

theorem hasDerivWithinAt_neg_of_localMaxOn_Ici
    {g : ℝ → ℝ} {x d : ℝ}
    (hmax : IsLocalMaxOn g (Set.Ici x) x)
    (hderiv : HasDerivWithinAt g d (Set.Ici x) x)
    (hne : d ≠ 0) :
    d < 0 := by
  have hd : d ≤ 0 := by
    have h := hmax.hasFDerivWithinAt_nonpos hderiv.hasFDerivWithinAt
      (one_mem_posTangentConeAt_Ici x)
    simpa using h
  exact lt_of_le_of_ne hd hne

end Poincare.Topology.Ehresmann
