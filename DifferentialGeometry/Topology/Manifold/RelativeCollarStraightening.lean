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

private theorem eqOn_symm_of_eqOn_id {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    {Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞} {X : Set M}
    (h : Set.EqOn Φ id X) : Set.EqOn Φ.symm id X := by
  intro x hx
  have hx' : Φ x = x := h hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [hx']
    _ = x := Diffeomorph.symm_apply_apply Φ x

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

theorem relativeCollarUniqueness_of_boundaryCollarStraightening {C : ℝ} (hC : 1 ≤ C)
    (h : BoundaryCollarStraightening.{u} C) :
    ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ U : Set M, IsOpen U →
        (∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
          c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            (p, t) ∈ c₀.source ∧ (p, t) ∈ c₁.source ∧
              c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) ∧
          ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
            (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
              Φ (c₀ (p, t)) = c₁ (p, t)) ∧
            Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy U _ ⟨ε, hε, hU⟩
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨δsrc, hδsrc, hstrip⟩ := exists_pos_forall_mem_of_compact_zeroSection
    (S := S) (W := c₀.source ∩ c₁.source) (c₀.open_source.inter c₁.open_source)
    (fun p => ⟨(hsrc p).1, (hsrc p).2⟩)
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ :=
    h c₀ c₁ hsrc hcore hbdy (ε / C) (div_pos hε hCpos)
  have hδC : C * δ ≤ ε := by
    have h1 : δ * C ≤ (ε / C) * C := mul_le_mul_of_nonneg_right hδε hCpos.le
    rw [div_mul_cancel₀ ε hCpos.ne'] at h1
    nlinarith [h1]
  have hδε' : δ ≤ ε := by
    have h1 : ε / C ≤ ε := by
      rw [div_le_iff₀ hCpos]
      exact le_mul_of_one_le_right hε.le hC
    exact hδε.trans h1
  have hsub : Uᶜ ⊆ (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ})ᶜ := by
    intro x hx hmem
    obtain ⟨⟨q, s⟩, hq, rfl⟩ := hmem
    exact hx (hU q s (lt_of_lt_of_le hq hδC)).1
  refine ⟨min δ δsrc, lt_min hδ hδsrc, fun p t ht => ?_, Φ, fun p t ht => ?_,
    Set.EqOn.mono hsub hsupp, eqOn_symm_of_eqOn_id (Set.EqOn.mono hsub hsupp)⟩
  · have h1 := lt_of_lt_of_le ht (min_le_right δ δsrc)
    have h2 := lt_of_lt_of_le ht ((min_le_left δ δsrc).trans hδε')
    exact ⟨(hstrip p t h1).1, (hstrip p t h1).2, (hU p t h2).1, (hU p t h2).2⟩
  · exact hmatch p t (lt_of_lt_of_le ht (min_le_left δ δsrc))

theorem boundaryCollarStraightening_of_regularization {C : ℝ} (hC : 1 ≤ C)
    (h : BoundaryCollarRegularization.{u}) : BoundaryCollarStraightening.{u} C := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy ε hε
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  have hstrip_mono : {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} ⊆
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ} := by
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact lt_of_lt_of_le hq (by nlinarith [hC, hδ])
  exact ⟨δ, hδ, hδε, Φ, hmatch,
    Set.EqOn.mono (Set.compl_subset_compl.mpr (Set.image_mono hstrip_mono)) hsupp⟩

theorem boundaryCollarStraightening_one_iff_regularization :
    BoundaryCollarStraightening.{u} 1 ↔ BoundaryCollarRegularization.{u} := by
  constructor
  · intro h
    unfold BoundaryCollarStraightening at h
    simp only [one_mul] at h
    unfold BoundaryCollarRegularization
    exact h
  · intro h
    unfold BoundaryCollarRegularization at h
    unfold BoundaryCollarStraightening
    simp only [one_mul]
    exact h

theorem boundaryCollarStraightening_mono {C C' : ℝ} (hCC' : C ≤ C')
    (h : BoundaryCollarStraightening.{u} C) : BoundaryCollarStraightening.{u} C' := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy ε hε
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  have hstrip_mono : {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ} ⊆
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C' * δ} := by
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq ⊢
    exact lt_of_lt_of_le hq (by nlinarith [hCC', hδ])
  exact ⟨δ, hδ, hδε, Φ, hmatch,
    Set.EqOn.mono (Set.compl_subset_compl.mpr (Set.image_mono hstrip_mono)) hsupp⟩

def BoundaryCollarStraighteningWithBoundedSupport : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ BoundaryCollarStraightening.{u} C

theorem relativeCollarUniqueness_of_boundaryCollarStraighteningWithBoundedSupport
    (h : BoundaryCollarStraighteningWithBoundedSupport.{u}) :
    ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ U : Set M, IsOpen U →
        (∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
          c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) →
        ∃ δ : ℝ, 0 < δ ∧
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            (p, t) ∈ c₀.source ∧ (p, t) ∈ c₁.source ∧
              c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) ∧
          ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
            (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
              Φ (c₀ (p, t)) = c₁ (p, t)) ∧
            Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ := by
  obtain ⟨C, hC, h'⟩ := h
  exact relativeCollarUniqueness_of_boundaryCollarStraightening hC h'

theorem boundaryCollarStraighteningWithBoundedSupport_of_regularization
    (h : BoundaryCollarRegularization.{u}) :
    BoundaryCollarStraighteningWithBoundedSupport.{u} :=
  ⟨1, le_rfl, boundaryCollarStraightening_of_regularization le_rfl h⟩

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
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
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
