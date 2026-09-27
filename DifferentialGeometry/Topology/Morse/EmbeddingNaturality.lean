import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Morse.CriticalPoint

open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Morse

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H H' : Type} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N] {r : ℕ∞ω}

theorem criticalPoints_comp_diffeomorph_eq_of_fixed
    (φ : Diffeomorph I I M M r) (hr : r ≠ 0) (f : M → ℝ)
    (hfix : ∀ x, IsCriticalPointAt I f x → φ x = x) :
    criticalPoints I (f ∘ φ) = criticalPoints I f := by
  ext x
  change IsCriticalPointAt I (f ∘ φ) x ↔ IsCriticalPointAt I f x
  rw [isCriticalPointAt_comp_diffeomorph_iff φ hr]
  constructor
  · intro hx
    have heq : φ x = x := φ.injective (hfix (φ x) hx)
    rwa [heq] at hx
  · intro hx
    rwa [hfix x hx]

theorem criticalPoints_comp_diffeomorph_comp_eq_of_fixed
    [IsManifold J r N] {e : M → N} (he : Manifold.IsSmoothEmbedding I J r e)
    (Φ : Diffeomorph J J N N r) (hr : r ≠ 0) (h : N → ℝ)
    (himage : Φ '' Set.range e = Set.range e)
    (hfix : ∀ x, IsCriticalPointAt I (h ∘ e) x → Φ (e x) = e x) :
    criticalPoints I (h ∘ Φ ∘ e) = criticalPoints I (h ∘ e) := by
  have hrange : Set.range (Φ ∘ e) = Set.range e := by
    rw [Set.range_comp, himage]
  let φ := (he.diffeomorph_comp Φ).diffeomorphOfRangeEq he hrange
  have hφ (x : M) : e (φ x) = Φ (e x) :=
    (he.diffeomorph_comp Φ).comp_diffeomorphOfRangeEq he hrange x
  have heq : h ∘ Φ ∘ e = (h ∘ e) ∘ φ := by
    funext x
    exact congrArg h (hφ x).symm
  rw [heq]
  apply criticalPoints_comp_diffeomorph_eq_of_fixed φ hr
  intro x hx
  exact he.isEmbedding.injective ((hφ x).trans (hfix x hx))

end DifferentialGeometry.Topology.Morse
