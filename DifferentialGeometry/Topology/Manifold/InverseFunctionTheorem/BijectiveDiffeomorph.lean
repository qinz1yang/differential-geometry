import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A finite-order bijection with bijective differential is a diffeomorphism

For boundaryless manifolds modelled on finite-dimensional real spaces and a finite order
`1 ≤ n < ∞`:

* `isLocalDiffeomorph_of_bijective_mfderiv`: a `C^n` map whose differential is bijective at every
  point is a `C^n` local diffeomorphism (the tree's manifold inverse function theorem
  `contMDiffAt_isLocalDiffeomorphAt_of_mfderiv`, bijective ⇒ invertible in finite dimension);
* `exists_diffeomorph_of_bijective_mfderiv`: if moreover the map is bijective, it is (the
  underlying map of) a `C^n` diffeomorphism (Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective`).

No continuity of the inverse is assumed. Lane LFR20-CMP (smooth fibre type), general statement.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Coordinates

variable {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J n N]
  {f : M → N}

/-- **A `C^n` map with bijective differential is a local diffeomorphism** (`1 ≤ n < ∞`). -/
theorem isLocalDiffeomorph_of_bijective_mfderiv (hn : 1 ≤ n) (hn' : n ≠ ∞)
    (hf : ContMDiff I J n f) (hbij : ∀ x, Bijective (mfderiv I J f x)) :
    IsLocalDiffeomorph I J n f := by
  intro x
  refine contMDiffAt_isLocalDiffeomorphAt_of_mfderiv hn hn' (hf x) ?_
  let L : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap (hbij x)
  exact ⟨L.toContinuousLinearEquiv, by
    ext v
    rfl⟩

/-- **A `C^n` bijection with bijective differential is a `C^n` diffeomorphism** (`1 ≤ n < ∞`). -/
theorem exists_diffeomorph_of_bijective_mfderiv (hn : 1 ≤ n) (hn' : n ≠ ∞)
    (hf : ContMDiff I J n f) (hf' : Bijective f) (hbij : ∀ x, Bijective (mfderiv I J f x)) :
    ∃ Φ : M ≃ₘ^n⟮I, J⟯ N, ⇑Φ = f :=
  ⟨(isLocalDiffeomorph_of_bijective_mfderiv hn hn' hf hbij).diffeomorphOfBijective hf', rfl⟩

end DifferentialGeometry.Coordinates
