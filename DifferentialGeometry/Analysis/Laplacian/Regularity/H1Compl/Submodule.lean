import DifferentialGeometry.Analysis.Sobolev.Intrinsic.H1Lp

/-!
# `H¹` as a submodule of `L²`

This file packages the `MemH1Lp` predicate of `IntrinsicH1Lp.lean` as a
`Submodule ℝ (Lp ℝ 2 μ_g)`. The carrier consists of those `Lp ℝ 2 μ_g`
classes that admit a weak Riemannian gradient in the `Lp E 2 μ_g` Banach
space, an `L²`-controlled metric `g`-norm, and the joint AESM pairing
clause. Closure under zero, addition, and scalar multiplication is
delivered by the corresponding theorems on `MemH1Lp`.

## Main definitions

* `H1Submodule g` : the submodule of `Lp ℝ 2 μ_g` consisting of `H¹` classes.

This submodule provides the natural identification of `H¹` with a subset
of `L²`, viewed as scalar functions. The companion file `H1Intrinsic.lean`
provides the bundled Hilbert structure whose inner product is the genuine
`H¹` inner product (rather than the inherited `L²` one).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Function
open scoped Manifold Topology ContDiff ENNReal NNReal Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.IntrinsicH1Lp

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The submodule `H¹(M, g) ⊆ L²(M, μ_g)` of `L²` classes admitting a weak
Riemannian gradient witness in `L² (M, E, μ_g)`. The carrier consists of
those `Lp ℝ 2 μ_g` classes `u` for which the unbundled predicate
`MemH1Lp g u` holds. -/
def H1Submodule [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    Submodule ℝ (Lp ℝ 2 (riemannianVolumeMeasure I M g)) where
  carrier := { u | MemH1Lp (I := I) (M := M) g u }
  add_mem' hu hv := MemH1Lp.add (I := I) (M := M) g hu hv
  zero_mem' := MemH1Lp.zero (I := I) (M := M) g
  smul_mem' c _ hu := MemH1Lp.const_smul (I := I) (M := M) g c hu

@[simp]
lemma mem_H1Submodule_iff
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M] [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    (u : Lp ℝ 2 (riemannianVolumeMeasure I M g)) :
    u ∈ H1Submodule (I := I) (M := M) g ↔ MemH1Lp (I := I) (M := M) g u := Iff.rfl

end Laplacian
end Analysis
end DifferentialGeometry

end
