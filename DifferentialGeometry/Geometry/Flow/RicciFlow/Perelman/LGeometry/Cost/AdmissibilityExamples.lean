import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MetricFamily
import Mathlib.Topology.Semicontinuity.Defs

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem const_admissible_ne_continuousOn {M : Type*} [TopologicalSpace M]
    (p q : M) (hpq : q ≠ p) (T : ℝ) :
    (fun γ : ℝ → M => γ = fun _ => q) ≠
      (fun γ : ℝ → M => ContinuousOn γ (Icc (0 : ℝ) T) ∧ γ 0 = p) := by
  intro h
  have hq : (fun γ : ℝ → M => γ = fun _ => q) (fun _ => q) := rfl
  rw [h] at hq
  exact hpq hq.2

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) ∞ M]

def reducedActionValueSet
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) : Set ℝ :=
  {r : ℝ | ∃ γ : ℝ → M,
    admissible γ ∧ γ 0 = p ∧ γ τ = x ∧ reducedAction g t₀ τ γ = r}

theorem reducedLength_eq_sInf_reducedActionValueSet
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) :
    reducedLength g t₀ admissible p τ x =
      sInf (reducedActionValueSet g t₀ admissible p τ x) := rfl

theorem reducedActionValueSet_nonempty_iff
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) :
    (reducedActionValueSet g t₀ admissible p τ x).Nonempty ↔
      ∃ γ : ℝ → M, admissible γ ∧ γ 0 = p ∧ γ τ = x := by
  constructor
  · rintro ⟨r, γ, hγ, h0, hτ, _⟩
    exact ⟨γ, hγ, h0, hτ⟩
  · rintro ⟨γ, hγ, h0, hτ⟩
    exact ⟨reducedAction g t₀ τ γ, γ, hγ, h0, hτ, rfl⟩

theorem reducedActionValueSet_eq_empty_of_not_exists
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M)
    (h : ¬ ∃ γ : ℝ → M, admissible γ ∧ γ 0 = p ∧ γ τ = x) :
    reducedActionValueSet g t₀ admissible p τ x = ∅ := by
  ext r
  constructor
  · rintro ⟨γ, hγ, h0, hτ, _⟩
    exact h ⟨γ, hγ, h0, hτ⟩
  · intro hr
    exact absurd hr (Set.notMem_empty r)

theorem reducedLength_eq_zero_of_not_exists
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M)
    (h : ¬ ∃ γ : ℝ → M, admissible γ ∧ γ 0 = p ∧ γ τ = x) :
    reducedLength g t₀ admissible p τ x = 0 := by
  rw [reducedLength_eq_sInf_reducedActionValueSet,
    reducedActionValueSet_eq_empty_of_not_exists g t₀ admissible p τ x h, Real.sInf_empty]

theorem reducedLength_le_reducedAction_of_bddBelow
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) (x : M) (γ : ℝ → M)
    (hγ : admissible γ) (h0 : γ 0 = p) (hτ : γ τ = x)
    (hb : BddBelow (reducedActionValueSet g t₀ admissible p τ x)) :
    reducedLength g t₀ admissible p τ x ≤ reducedAction g t₀ τ γ :=
  csInf_le hb ⟨γ, hγ, h0, hτ, rfl⟩

def regularMinimizingSet
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible regular : (ℝ → M) → Prop) (p : M) (τ : ℝ) : Set M :=
  {x | ∃ γ : ℝ → M,
    admissible γ ∧ regular γ ∧ γ 0 = p ∧ γ τ = x ∧
      reducedAction g t₀ τ γ = reducedLength g t₀ admissible p τ x}

theorem regularMinimizingSet_false
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (admissible : (ℝ → M) → Prop) (p : M) (τ : ℝ) :
    regularMinimizingSet g t₀ admissible (fun _ => False) p τ = ∅ := by
  ext x
  simp [regularMinimizingSet]

theorem reducedLength_false
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p : M) (τ : ℝ) (x : M) :
    reducedLength g t₀ (fun _ => False) p τ x = 0 := by
  simp [reducedLength]

theorem isLeast_reducedLength_false
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p : M) (τ : ℝ) (x : M) :
    IsLeast (range fun y => reducedLength g t₀ (fun _ => False) p τ y)
      (reducedLength g t₀ (fun _ => False) p τ x) := by
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro _ ⟨z, rfl⟩
  simp only [reducedLength_false, le_refl]

theorem lowerSemicontinuousOn_reducedLength_false
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p : M) (τ : ℝ) (s : Set M) :
    LowerSemicontinuousOn (fun x => reducedLength g t₀ (fun _ => False) p τ x) s := by
  have hconst : (fun x => reducedLength g t₀ (fun _ => False) p τ x) =
      fun _ : M => (0 : ℝ) := by
    funext x
    exact reducedLength_false g t₀ p τ x
  rw [hconst]
  exact lowerSemicontinuousOn_const

theorem not_forall_exists_reducedAction_minimizer_false
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p : M) (τ : ℝ) :
    ¬ (∀ x : M,
      IsLeast (range fun y => reducedLength g t₀ (fun _ => False) p τ y)
        (reducedLength g t₀ (fun _ => False) p τ x) →
      ∃ γ : ℝ → M, False ∧ γ 0 = p ∧ γ τ = x ∧
        reducedAction g t₀ τ γ = reducedLength g t₀ (fun _ => False) p τ x) := by
  intro h
  obtain ⟨γ, hγ, _⟩ := h p (isLeast_reducedLength_false g t₀ p τ p)
  exact hγ

theorem reducedLength_const_admissible_of_ne
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p q : M) (hpq : q ≠ p) (τ : ℝ) (x : M) :
    reducedLength g t₀ (fun γ => γ = fun _ => q) p τ x = 0 := by
  simp [reducedLength, hpq]

theorem nonempty_admissible_and_not_exists_reducedAction_minimizer
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p q : M) (hpq : q ≠ p) (τ : ℝ) :
    (∃ γ : ℝ → M, γ = fun _ => q) ∧
      (∀ x : M, reducedLength g t₀ (fun γ => γ = fun _ => q) p τ x = 0) ∧
      ¬ ∃ (x : M) (γ : ℝ → M),
        (γ = fun _ => q) ∧ γ 0 = p ∧ γ τ = x ∧
          reducedAction g t₀ τ γ =
            reducedLength g t₀ (fun γ => γ = fun _ => q) p τ x := by
  refine ⟨⟨fun _ => q, rfl⟩, reducedLength_const_admissible_of_ne g t₀ p q hpq τ, ?_⟩
  rintro ⟨x, γ, hγ, h0, _⟩
  exact hpq ((congrFun hγ 0).symm.trans h0)

theorem reducedActionValueSet_continuousOn_nonempty
    (g : ℝ → SmoothRiemannianMetric (𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) M) (t₀ : ℝ)
    (p : M) (T τ : ℝ) :
    (reducedActionValueSet g t₀
      (fun γ => ContinuousOn γ (Icc (0 : ℝ) T) ∧ γ 0 = p) p τ p).Nonempty :=
  ⟨reducedAction g t₀ τ (fun _ => p), fun _ => p,
    ⟨continuousOn_const, rfl⟩, rfl, rfl, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
