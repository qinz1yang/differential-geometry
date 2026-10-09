/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Manifold.CornerRounding.RoundedMin
import DifferentialGeometry.Topology.Manifold.AmbientCornerRounding

/-!
# The rounded piece is homeomorphic to the cornered piece

In a product chart `e : M ⊇ U ≅ P × ℝ²` (`P` compact, e.g. the circle fibre) in which the piece is
the quadrant `{a ≥ 0, b ≥ 0}` and the complementary side is `{a ≤ 0} ∪ {b ≤ 0}`, the PC smooth
Schoenflies homeomorphism `PartialDiffeomorph.exists_homeomorph_smoothAbs_corner` carries the piece
ONTO the regularized-minimum piece `{roundedMin ε a b ≥ 0}` and the complementary side ONTO
`{roundedMin ε a b ≤ 0}`.  It is the product of the identity of `P` with a plane homeomorphism, the
identity off a compact subset of the chart, and a local diffeomorphism off the corner `P × {0}`.
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold.CornerRounding

private theorem quadrantSet_eq {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (A : Set X) (ε : ℝ) :
    e.smoothAbsQuadrantSet A ε =
      (A \ e.source) ∪ {x | x ∈ e.source ∧ 0 ≤ roundedMin ε (e x).2.1 (e x).2.2} := by
  ext x
  by_cases hx : x ∈ e.source
  · rw [e.mem_smoothAbsQuadrantSet_iff A ε hx, ← roundedMin_nonneg_iff]
    constructor
    · intro h
      exact Or.inr ⟨hx, h⟩
    · rintro (h | h)
      · exact absurd hx h.2
      · exact h.2
  · rw [e.mem_smoothAbsQuadrantSet_iff_of_notMem_source A ε hx]
    constructor
    · intro h
      exact Or.inl ⟨h, hx⟩
    · rintro (h | h)
      · exact h.1
      · exact absurd h.1 hx

private theorem reflexSet_eq {X P : Type*} [TopologicalSpace X] [TopologicalSpace P]
    (e : OpenPartialHomeomorph X (P × (ℝ × ℝ))) (A : Set X) (ε : ℝ) :
    (A \ e.source) ∪ e.symm ''
        (e.target ∩ {p | p.2.1 + p.2.2 ≤ Real.smoothAbs ε (p.2.1 - p.2.2)}) =
      (A \ e.source) ∪ {x | x ∈ e.source ∧ roundedMin ε (e x).2.1 (e x).2.2 ≤ 0} := by
  congr 1
  ext x
  constructor
  · rintro ⟨p, ⟨hp, hpS⟩, rfl⟩
    refine ⟨e.map_target hp, ?_⟩
    rw [e.right_inv hp, roundedMin_nonpos_iff]
    exact hpS
  · rintro ⟨hx, hS⟩
    refine ⟨e x, ⟨e.map_source hx, ?_⟩, e.left_inv hx⟩
    exact roundedMin_nonpos_iff.mp hS

/-- **Chart form of corner rounding.**  In a product chart in which the piece is the quadrant, the
PC corner homeomorphism maps the piece onto the regularized-minimum piece and the complementary
side onto the rounded complementary side (the same arc on both sides). -/
theorem exists_homeomorph_roundedMin_corner
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G H : Type*} [TopologicalSpace G] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E G} {J : ModelWithCorners ℝ F H}
    {M P : Type*} [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
    [TopologicalSpace P] [ChartedSpace H P] [CompactSpace P]
    (e : PartialDiffeomorph I (J.prod 𝓘(ℝ, ℝ × ℝ)) M (P × (ℝ × ℝ)) ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hstrip : (univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ e.target) :
    ∃ Φ : M ≃ₜ M,
      (∀ x ∈ e.source, Φ x = e.symm ((e x).1, Homeomorph.smoothAbsCorner hε (e x).2)) ∧
      IsCompact (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε)) ∧
      e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε) ⊆ e.source ∧
      EqOn Φ id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      EqOn Φ.symm id (e.symm '' ((univ : Set P) ×ˢ closedBall (0 : ℝ × ℝ) ε))ᶜ ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2) →
        Φ '' A = (A \ e.source) ∪
          {x | x ∈ e.source ∧ 0 ≤ roundedMin ε (e x).2.1 (e x).2.2}) ∧
      (∀ A : Set M, (∀ p ∈ e.target, e.symm p ∈ A ↔ p.2.1 ≤ 0 ∨ p.2.2 ≤ 0) →
        Φ '' A = (A \ e.source) ∪
          {x | x ∈ e.source ∧ roundedMin ε (e x).2.1 (e x).2.2 ≤ 0}) ∧
      ∀ x : M, x ∉ e.symm '' ((univ : Set P) ×ˢ {(0 : ℝ × ℝ)}) →
        IsLocalDiffeomorphAt I I ∞ Φ x ∧ IsLocalDiffeomorphAt I I ∞ Φ.symm (Φ x) := by
  obtain ⟨Φ, hΦ, -, hC, hCs, hfix, hfixi, hquad, hreflex, hloc⟩ :=
    e.exists_homeomorph_smoothAbs_corner hε hstrip
  refine ⟨Φ, hΦ, hC, hCs, hfix, hfixi, fun A hA => ?_, fun A hA => ?_, hloc⟩
  · rw [hquad A hA]
    exact quadrantSet_eq e.toOpenPartialHomeomorph A ε
  · rw [hreflex A hA]
    exact reflexSet_eq e.toOpenPartialHomeomorph A ε

end DifferentialGeometry.Topology.Manifold.CornerRounding
