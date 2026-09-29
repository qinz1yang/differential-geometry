import DifferentialGeometry.Topology.Manifold.RelativeCollarUniqueness
import DifferentialGeometry.Topology.Manifold.HalfLine
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

open Manifold Set Topology
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Collar

universe u

private theorem halfSpaceOneLift_coordinate (t : ℝ) (ht : 0 ≤ t) :
    (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift t).1 0 = t := by
  have h : (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift t).1 0 = max t 0 := rfl
  rw [h, max_eq_left ht]

theorem collarImage_subset_of_supported_matching
    {S M : Type*} (c₀ c₁ : S × EuclideanHalfSpace 1 → M) (Φ : M → M) {δ : ℝ}
    (hinj : Function.Injective Φ)
    (hsupp : Set.EqOn Φ id
      (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ})ᶜ)
    (hmatch : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
      Φ (c₀ (p, t)) = c₁ (p, t)) :
    c₁ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} ⊆
      c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} := by
  have hfix : ∀ z ∈ c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ},
      Φ z ∈ c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} := by
    intro z hz
    by_contra hz'
    have h2 : Φ (Φ z) = Φ z := hsupp hz'
    have h3 : Φ z = z := hinj h2
    exact hz' (h3.symm ▸ hz)
  rintro y ⟨⟨s, t⟩, hq, rfl⟩
  rw [← hmatch s t hq]
  exact hfix _ ⟨(s, t), hq, rfl⟩

theorem not_image_strip_subset_image_strip {S M : Type*}
    (c : S × EuclideanHalfSpace 1 → M) (p : S) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hinj : Set.InjOn c {q : S × EuclideanHalfSpace 1 | q.2.1 0 < b}) :
    ¬ (c '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < b} ⊆
      c '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < a}) := by
  intro hsub
  have hlift : (DifferentialGeometry.Topology.Manifold.halfSpaceOneLift a).1 0 < b := by
    rw [halfSpaceOneLift_coordinate a ha.le]
    exact hab
  have hmem : c (p, DifferentialGeometry.Topology.Manifold.halfSpaceOneLift a) ∈
      c '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < b} :=
    ⟨(p, DifferentialGeometry.Topology.Manifold.halfSpaceOneLift a), hlift, rfl⟩
  obtain ⟨q, hq, hqeq⟩ := hsub hmem
  have hqb : q.2.1 0 < b := lt_trans hq hab
  have heq : q = (p, DifferentialGeometry.Topology.Manifold.halfSpaceOneLift a) :=
    hinj hqb hlift hqeq
  have hcoord : q.2.1 0 = a := by
    rw [heq]
    exact halfSpaceOneLift_coordinate a ha.le
  exact absurd hcoord (ne_of_lt hq)

def BoundaryCollarStraightening (C : ℝ) : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
        ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            Φ (c₀ (p, t)) = c₁ (p, t)) ∧
          Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ})ᶜ

def BoundaryCollarStraighteningWithBoundedSupport : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ BoundaryCollarStraightening.{u} C

theorem not_boundaryCollarRegularization_of_stripNesting
    (S : Type u) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞)
    (hsrc : ∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source)
    (hcore : ∀ p : S, c₀ (p, 0) = c₁ (p, 0))
    (hbdy : ∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M)
    {ε : ℝ} (hε : 0 < ε)
    (hnest : ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      ¬ (c₁ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} ⊆
        c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ})) :
    ¬ BoundaryCollarRegularization.{u} := by
  intro h
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  exact hnest δ hδ hδε
    (collarImage_subset_of_supported_matching c₀ c₁ (⇑Φ) Φ.injective hsupp hmatch)

theorem exists_supported_diffeomorph_of_eqOn_strip (C : ℝ)
    {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hagree : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε → c₀ (p, t) = c₁ (p, t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
        (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
          Φ (c₀ (p, t)) = c₁ (p, t)) ∧
        Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ})ᶜ := by
  refine ⟨ε, hε, le_rfl, Diffeomorph.refl (𝓡∂ 3) M ∞, fun p t ht => hagree p t ht, ?_⟩
  intro x _
  rfl

end DifferentialGeometry.Topology.Collar
