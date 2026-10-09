/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TaperedInwardPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Continuity

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]

theorem IsPLOn.continuousOn {f : M → N} {s : Set M} (hf : IsPLOn n m f s) : ContinuousOn f s :=
  fun x hx => (hf x hx).continuousWithinAt

end Continuity

section Composition

variable {n : ℕ} {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M₁] [MetricSpace M₂]

theorem exists_isPLOn_injOn_leftInvOn_dist_lt_of_comp {K : Set M₁} {h : M₁ → M₂}
    {ψ₁ ψ₂ ψ : M₁ → ℝ} {p₁ q₁ p₂ q₂ : M₁ → M₁} {W₁ W₂ : Set M₁} (hW₁ : IsOpen W₁)
    (hW₁K : W₁ ⊆ interior K) (hp₁W : MapsTo p₁ K W₁) (hp₁ : IsPLOn n n p₁ K)
    (hp₁inj : InjOn p₁ K) (hq₁ : IsPLOn n n q₁ W₁) (hq₁K : MapsTo q₁ W₁ K)
    (hinv₁ : LeftInvOn q₁ p₁ K) (hd₁ : ∀ x ∈ K, dist (h (p₁ x)) (h x) < ψ₁ x)
    (hW₂ : IsOpen W₂) (hW₂K : W₂ ⊆ interior K) (hp₂W : MapsTo p₂ K W₂)
    (hp₂ : IsPLOn n n p₂ K) (hp₂inj : InjOn p₂ K) (hq₂ : IsPLOn n n q₂ W₂)
    (hinv₂ : LeftInvOn q₂ p₂ K)
    (hd₂ : ∀ x ∈ K, dist (h (p₂ x)) (h x) < ψ₂ x)
    (hψ : ∀ x ∈ K, ψ₁ x + ψ₂ (p₁ x) ≤ ψ x) :
    ∃ W : Set M₁, IsOpen W ∧ W ⊆ interior K ∧ MapsTo (p₂ ∘ p₁) K W ∧
      IsPLOn n n (p₂ ∘ p₁) K ∧ InjOn (p₂ ∘ p₁) K ∧ IsPLOn n n (q₁ ∘ q₂) W ∧
      MapsTo (q₁ ∘ q₂) W K ∧ LeftInvOn (q₁ ∘ q₂) (p₂ ∘ p₁) K ∧
      ∀ x ∈ K, dist (h ((p₂ ∘ p₁) x)) (h x) < ψ x := by
  have hp₁int : MapsTo p₁ K (interior K) := fun x hx => hW₁K (hp₁W hx)
  have hp₁K : MapsTo p₁ K K := fun x hx => interior_subset (hp₁int hx)
  have hWopen : IsOpen (W₂ ∩ q₂ ⁻¹' W₁) := hq₂.continuousOn.isOpen_inter_preimage hW₂ hW₁
  have hWmap : MapsTo q₂ (W₂ ∩ q₂ ⁻¹' W₁) W₁ := fun _ hx => hx.2
  refine ⟨W₂ ∩ q₂ ⁻¹' W₁, hWopen, inter_subset_left.trans hW₂K, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨hp₂W (hp₁K hx), ?_⟩
    change q₂ (p₂ (p₁ x)) ∈ W₁
    rw [hinv₂ (hp₁K hx)]
    exact hp₁W hx
  · exact (hp₂.mono_of_isOpen isOpen_interior interior_subset).comp_of_isOpen isOpen_interior
      hp₁ hp₁int
  · exact hp₂inj.comp hp₁inj hp₁K
  · exact hq₁.comp_of_isOpen hW₁
      (hq₂.mono_of_isOpen hWopen inter_subset_left) hWmap
  · exact hq₁K.comp hWmap
  · intro x hx
    change q₁ (q₂ (p₂ (p₁ x))) = x
    rw [hinv₂ (hp₁K hx)]
    exact hinv₁ hx
  · intro x hx
    have hstep : dist (h (p₂ (p₁ x))) (h (p₁ x)) < ψ₂ (p₁ x) := hd₂ (p₁ x) (hp₁K hx)
    have hbase : dist (h (p₁ x)) (h x) < ψ₁ x := hd₁ x hx
    have htri : dist (h (p₂ (p₁ x))) (h x) ≤
        dist (h (p₂ (p₁ x))) (h (p₁ x)) + dist (h (p₁ x)) (h x) := dist_triangle _ _ _
    have hsum := hψ x hx
    change dist (h (p₂ (p₁ x))) (h x) < ψ x
    linarith

end Composition

end DifferentialGeometry.Topology.PiecewiseLinear
