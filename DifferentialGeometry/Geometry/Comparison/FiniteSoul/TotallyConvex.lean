import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import Mathlib.Analysis.Convex.Function

/-!
# Total convexity for a metric of finite order (S-DEF of the finite soul package CM-S)

`IsTotallyConvexFinite g C`: every geodesic-flow arc of `g` (not only a minimizing one) whose two
endpoints lie in `C` stays in `C`. This is the finite-order analogue of the smooth
`IsTotallyConvex` (`Soul/SoulConvexCore.lean`). It is a definition used in conclusions and
internal lemmas, not an assumption-`Prop`. It is meaningful for complete metrics, where the
geodesic flow is defined for all times (`geodesicFlowDomain_eq_univ`).

Closure properties: `univ`, `∅`, intersections, and sublevel sets of functions that are convex
along every geodesic-flow arc.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **S-DEF.** Total convexity for a finite-order metric: every geodesic-flow arc with both
endpoints in `C` stays in `C`. Meaningful for complete metrics (`geodesicFlowDomain = univ`). -/
def IsTotallyConvexFinite {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (C : Set M) : Prop :=
  ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ → p.proj ∈ C → (g.geodesicFlow p ℓ).proj ∈ C →
    ∀ t ∈ Icc 0 ℓ, (g.geodesicFlow p t).proj ∈ C

variable {n : ℕ∞ω} {g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)}

theorem isTotallyConvexFinite_univ
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    IsTotallyConvexFinite g (univ : Set M) :=
  fun _ _ _ _ _ _ _ => mem_univ _

theorem isTotallyConvexFinite_empty
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) :
    IsTotallyConvexFinite g (∅ : Set M) :=
  fun _ _ _ h _ _ _ => h.elim

theorem IsTotallyConvexFinite.inter {C D : Set M} (hC : IsTotallyConvexFinite g C)
    (hD : IsTotallyConvexFinite g D) : IsTotallyConvexFinite g (C ∩ D) :=
  fun p ℓ hℓ h0 h1 t ht => ⟨hC p ℓ hℓ h0.1 h1.1 t ht, hD p ℓ hℓ h0.2 h1.2 t ht⟩

theorem isTotallyConvexFinite_iInter {ι : Sort*} {C : ι → Set M}
    (h : ∀ i, IsTotallyConvexFinite g (C i)) : IsTotallyConvexFinite g (⋂ i, C i) := by
  intro p ℓ hℓ h0 h1 t ht
  rw [mem_iInter] at h0 h1 ⊢
  exact fun i => h i p ℓ hℓ (h0 i) (h1 i) t ht

theorem isTotallyConvexFinite_sInter {S : Set (Set M)}
    (h : ∀ C ∈ S, IsTotallyConvexFinite g C) : IsTotallyConvexFinite g (⋂₀ S) := by
  intro p ℓ hℓ h0 h1 t ht
  rw [mem_sInter] at h0 h1 ⊢
  exact fun C hC => h C hC p ℓ hℓ (h0 C hC) (h1 C hC) t ht

section Sublevel

variable [I.Boundaryless] {r : ℕ∞}
  {g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _)}

/-- Sublevel sets of a function that is convex along every geodesic-flow arc are totally convex. -/
theorem isTotallyConvexFinite_sublevel (hr : 1 ≤ r) {f : M → ℝ}
    (hf : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      ConvexOn ℝ (Icc 0 ℓ) (fun t => f (g.geodesicFlow p t).proj)) (a : ℝ) :
    IsTotallyConvexFinite g {x : M | f x ≤ a} := by
  intro p ℓ hℓ h0 h1 t ht
  have h0' : f (g.geodesicFlow p 0).proj ≤ a := by rw [g.geodesicFlow_zero hr]; exact h0
  exact ((hf p ℓ hℓ).le_max_of_mem_Icc (left_mem_Icc.2 hℓ) (right_mem_Icc.2 hℓ) ht).trans
    (max_le h0' h1)

/-- Strict sublevel sets of a function that is convex along every geodesic-flow arc are totally
convex. -/
theorem isTotallyConvexFinite_strict_sublevel (hr : 1 ≤ r) {f : M → ℝ}
    (hf : ∀ (p : TangentBundle I M) (ℓ : ℝ), 0 ≤ ℓ →
      ConvexOn ℝ (Icc 0 ℓ) (fun t => f (g.geodesicFlow p t).proj)) (a : ℝ) :
    IsTotallyConvexFinite g {x : M | f x < a} := by
  intro p ℓ hℓ h0 h1 t ht
  have h0' : f (g.geodesicFlow p 0).proj < a := by rw [g.geodesicFlow_zero hr]; exact h0
  exact ((hf p ℓ hℓ).le_max_of_mem_Icc (left_mem_Icc.2 hℓ) (right_mem_Icc.2 hℓ) ht).trans_lt
    (max_lt h0' h1)

end Sublevel

end DifferentialGeometry.Geometry.FiniteSoul
