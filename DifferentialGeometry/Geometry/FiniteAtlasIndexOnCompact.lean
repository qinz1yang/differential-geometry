import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic

/-!
# Finite-image chart selection on compact sets

This file introduces the predicate `HasFiniteAtlasIndexOnCompact H M`, expressing
that the canonical chart-selection function `chartAt H : M → OpenPartialHomeomorph M H`
of a `ChartedSpace H M` takes only finitely many distinct values on every compact
subset `K ⊆ M`.

The motivation is to expose, as an honest separable hypothesis, the discrete
combinatorial information sometimes needed to drive uniform estimates over compact
sets in chart-discontinuity settings — namely that the set of distinct chart
values attained on the relevant compact subset is finite.

The predicate is **not** automatically true on `ChartedSpace H M` from
`[CompactSpace M] [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]` alone:
the `ChartedSpace` structure only fixes a chart-selection function `chartAt H`,
and that function's image is in principle arbitrary (it lands in the atlas, which
need not be finite). The predicate must therefore be carried as an explicit
hypothesis, or derived from an additional structural property of the
chart-selection function.

## Main definitions

* `HasFiniteAtlasIndexOnCompact H M` — the predicate.

## Main results

* `hasFiniteAtlasIndexOnCompact_self` — the model space `H`, viewed as a charted
  space over itself, has finite chart-image on every compact set. In fact the
  chart-selection is globally constant, so the image of any set is `{refl H}` or
  empty.

* `HasFiniteAtlasIndexOnCompact.finite_image` — unpacking lemma.
* `HasFiniteAtlasIndexOnCompact.mono` — monotonicity under compact subsets.
* `HasFiniteAtlasIndexOnCompact.union` — additivity over a binary compact union.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace DifferentialGeometry
namespace Geometry

/-- A `ChartedSpace H M` has **finite atlas-index image on compact sets** if the
canonical chart-selection function `chartAt H : M → OpenPartialHomeomorph M H`
takes only finitely many distinct values on every compact subset `K ⊆ M`.

This is **not** automatically derivable from the standard manifold typeclasses
`[ChartedSpace H M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
[IsManifold I ∞ M]`. The `ChartedSpace` structure only fixes a chart-selection
`chartAt H : M → OpenPartialHomeomorph M H`; that function's image is in
principle arbitrary (it lands in the atlas, which need not be finite). The
predicate must be carried as an explicit hypothesis or derived from an
additional structural property of the chart-selection function. -/
def HasFiniteAtlasIndexOnCompact
    (H : Type*) [TopologicalSpace H]
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] : Prop :=
  ∀ K : Set M, IsCompact K → (Set.image (chartAt H) K).Finite

namespace HasFiniteAtlasIndexOnCompact

variable {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Finite image on a compact set, packaged as a `Set.Finite` statement. -/
theorem finite_image
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K : Set M} (hK : IsCompact K) :
    (Set.image (chartAt H) K).Finite :=
  h K hK

/-- Monotonicity: finite image on a compact superset transfers to any compact
subset. -/
theorem mono
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K K' : Set M} (hK : IsCompact K) (hKK' : K' ⊆ K) (_hK' : IsCompact K') :
    (Set.image (chartAt H) K').Finite :=
  (h K hK).subset (Set.image_mono hKK')

/-- Finite image is preserved under binary unions of compact sets. -/
theorem union
    (h : HasFiniteAtlasIndexOnCompact H M)
    {K₁ K₂ : Set M} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) :
    (Set.image (chartAt H) (K₁ ∪ K₂)).Finite := by
  rw [Set.image_union]
  exact (h K₁ hK₁).union (h K₂ hK₂)

/-- Finite image on the empty set: trivial (the empty image is finite). -/
theorem image_empty :
    (Set.image (chartAt H) (∅ : Set M)).Finite := by
  rw [Set.image_empty]
  exact Set.finite_empty

end HasFiniteAtlasIndexOnCompact

/-- The model space `H`, viewed as a charted space over itself via
`chartedSpaceSelf`, has finite chart-image on every compact set. The chart
selection is globally constant equal to `OpenPartialHomeomorph.refl H`. -/
theorem hasFiniteAtlasIndexOnCompact_self
    (H : Type*) [TopologicalSpace H] :
    HasFiniteAtlasIndexOnCompact H H := by
  intro K _hK
  refine Set.Finite.subset (Set.finite_singleton (OpenPartialHomeomorph.refl H))
    ?_
  rintro e ⟨b, _hb, hbe⟩
  have h_eq : chartAt H b = OpenPartialHomeomorph.refl H := chartAt_self_eq
  rw [← hbe, h_eq]
  exact Set.mem_singleton _

end Geometry
end DifferentialGeometry

end
