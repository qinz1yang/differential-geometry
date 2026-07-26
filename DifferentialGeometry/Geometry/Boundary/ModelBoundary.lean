import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Defs.Induced
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Abstract typeclass for models with smooth boundary

This file introduces the abstract typeclass `HasSmoothBoundary I`, which packages
the structural data needed to express that a model with corners
`I : ModelWithCorners ℝ E H` admits a smooth `(n-1)`-dimensional boundary
modelled on a strictly smaller pair `(E', H')`. The typeclass collects:

* a smaller model normed space `E'` and topological model space `H'`;
* a *boundaryless* model with corners `J : ModelWithCorners ℝ E' H'` for the
  boundary;
* a topological embedding `inclH : H' → H` whose image, after `I`, parameterises
  the model-level boundary `frontier (Set.range I)`;
* a continuous projection `projE : E → E'`;
* a coordinate-compatibility identity `projE ∘ I ∘ inclH = J`.

The downstream files in the present directory will use this typeclass to
endow `boundary I M` with a smooth `(n-1)`-dimensional manifold structure, to
construct the induced Riemannian metric on the boundary, to build the surface
measure, and to define the outward unit normal vector field — all without
committing to any specific model space (in particular, without specialising to
`EuclideanHalfSpace n`).

## Main definitions

* `HasSmoothBoundary E H I` — the abstract structural typeclass.
* `HasSmoothBoundary.boundaryModelE`, `boundaryModelH`, `boundaryModel` —
  type / model accessors.
* `HasSmoothBoundary.inclH`, `HasSmoothBoundary.projE` — embedding and
  projection accessors.

## Main results

* `HasSmoothBoundary.mem_frontier_range_iff_exists_inclH` — boundary points of
  the model are precisely the image of `inclH`.
* `HasSmoothBoundary.boundaryI_boundaryless` — re-export the
  boundaryless-of-the-boundary instance.
* `HasSmoothBoundary.inclH_continuous`, `inclH_injective`, `inclH_isInducing`,
  `inclH_isEmbedding`, `inclH_isClosedEmbedding` — topological properties of
  the inclusion.
* `HasSmoothBoundary.proj_inclH_compat'` — the explicit identity
  `projE (I (inclH x)) = J x`.
* `HasSmoothBoundary.range_I_inclH_subset_frontier`,
  `frontier_subset_range_I_inclH` — set-theoretic versions of the range
  identity.

## Scope

This typeclass deliberately requires the boundary to be a smooth
`(n-1)`-dimensional submanifold without further strata. It is therefore
**not** appropriate for models with corners (e.g., `EuclideanQuadrant n`),
whose boundary is stratified rather than smooth. A future companion typeclass
could host a stratified-boundary variant without disturbing the present API.

For models without boundary (those satisfying `[I.Boundaryless]`), this
typeclass need not be instantiated — the boundary set
`frontier (Set.range I)` is empty and all downstream with-boundary integrals
collapse to the boundaryless API.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

/-- A model with corners `I : ModelWithCorners ℝ E H` has a *smooth boundary*
when it admits a smaller, boundaryless model `J : ModelWithCorners ℝ E' H'`
together with a topological embedding `inclH : H' → H` and a continuous
projection `projE : E → E'`, satisfying coordinate compatibility
`projE ∘ I ∘ inclH = J` and the range identity
`Set.range (I ∘ inclH) = frontier (Set.range I)`.

Geometrically, `(E', H', J)` provides the local model for the boundary as an
`(n-1)`-dimensional smooth manifold; `inclH` realises this model as a
topological subspace of the ambient model `H`; and `projE` provides the
ambient-space slicing (e.g., dropping the first coordinate of a half-space).

This typeclass is the structural input to the with-boundary smooth-manifold
constructions in the present directory. It encodes the topological /
set-theoretic compatibility needed to build the boundary chart structure
together with the two smoothness requirements
(`projE_contDiff`, `I_inclH_boundaryI_symm_contDiff`) needed to lift the
charted-space structure on `boundary I M` to a full smooth manifold.

### Scope

* The boundary `H'` is required to be **boundaryless** (i.e.,
  `[boundaryI.Boundaryless]`): the boundary of the boundary must be empty.
  This excludes corner models such as `EuclideanQuadrant n`, whose model-level
  boundary is itself a stratified space with corners.
* Models satisfying `[I.Boundaryless]` need not instantiate this class:
  `frontier (Set.range I) = ∅` and the with-boundary infrastructure becomes
  vacuous.
* A future `HasCornerBoundary` (or similarly named) typeclass could relax the
  `[boundaryI.Boundaryless]` requirement, exposing a stratified-boundary API
  without disturbing the present interface.
-/
class HasSmoothBoundary
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Type*) [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) where

  boundaryE : Type*

  [boundaryENormedGroup : NormedAddCommGroup boundaryE]

  [boundaryENormedSpace : NormedSpace ℝ boundaryE]

  [boundaryEInnerProductSpace : InnerProductSpace ℝ boundaryE]

  [boundaryEFiniteDimensional : FiniteDimensional ℝ boundaryE]

  boundaryH : Type*

  [boundaryHTopologicalSpace : TopologicalSpace boundaryH]

  boundaryI : ModelWithCorners ℝ boundaryE boundaryH

  [boundaryIBoundaryless : boundaryI.Boundaryless]

  inclH : boundaryH → H

  inclH_continuous : Continuous inclH

  inclH_injective : Function.Injective inclH

  inclH_isInducing : IsInducing inclH

  inclH_isClosed_image : IsClosed (Set.range (I ∘ inclH))

  projE : E → boundaryE

  projE_continuous : Continuous projE

  projE_contDiff : ContDiff ℝ ∞ projE

  I_inclH_boundaryI_symm_contDiff : ContDiff ℝ ∞ (I ∘ inclH ∘ boundaryI.symm)

  range_I_inclH : Set.range (I ∘ inclH) = frontier (Set.range I)

  proj_inclH_compat : ∀ x : boundaryH, projE (I (inclH x)) = boundaryI x

  inwardCoordE : E

  inwardCoordE_transverse :
    ∀ y : boundaryE, inwardCoordE ∉ Set.range
      (fderiv ℝ ((I : H → E) ∘ inclH ∘ boundaryI.symm) y)

  range_frontier_basis_addHaar_zero :
    ∀ [_h : FiniteDimensional ℝ E],
      letI : MeasurableSpace E := borel E
      haveI : BorelSpace E := ⟨rfl⟩
      ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
          (frontier (Set.range I)) = 0

  finrank_boundaryE_succ :
    ∀ [_h : FiniteDimensional ℝ E],
      Module.finrank ℝ boundaryE + 1 = Module.finrank ℝ E

/-- Normed-additive-group structure on the boundary model space. -/
instance HasSmoothBoundary.instNormedAddCommGroupBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedAddCommGroup hI.boundaryE := hI.boundaryENormedGroup

/-- Real normed-space structure on the boundary model space. -/
instance HasSmoothBoundary.instNormedSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    NormedSpace ℝ hI.boundaryE := hI.boundaryENormedSpace

/-- Inner-product-space structure on the boundary model space. -/
instance HasSmoothBoundary.instInnerProductSpaceBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    InnerProductSpace ℝ hI.boundaryE := hI.boundaryEInnerProductSpace

/-- Finite-dimensionality of the boundary model space. -/
instance HasSmoothBoundary.instFiniteDimensionalBoundaryE
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    FiniteDimensional ℝ hI.boundaryE := hI.boundaryEFiniteDimensional

/-- Topology on the boundary topological model space. -/
instance HasSmoothBoundary.instTopologicalSpaceBoundaryH
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    TopologicalSpace hI.boundaryH := hI.boundaryHTopologicalSpace

/-- Boundarylessness of the boundary model with corners. -/
instance HasSmoothBoundary.instBoundarylessBoundaryI
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [hI : HasSmoothBoundary E H I] :
    hI.boundaryI.Boundaryless := hI.boundaryIBoundaryless

namespace HasSmoothBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]

/-- The normed model space for the boundary, exposed as an abbreviation. -/
abbrev boundaryModelE (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryE

/-- The topological model space for the boundary, exposed as an abbreviation. -/
abbrev boundaryModelH (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    Type _ := hI.boundaryH

/-- The boundary model with corners (boundaryless), exposed as an
abbreviation. -/
abbrev boundaryModel
    (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I] :
    ModelWithCorners ℝ hI.boundaryE hI.boundaryH := hI.boundaryI

section Inclusion

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- The boundary inclusion `inclH` is a topological embedding. Direct
combination of `inclH_isInducing` and `inclH_injective`. -/
theorem inclH_isEmbedding : IsEmbedding hI.inclH where
  toIsInducing := hI.inclH_isInducing
  injective := hI.inclH_injective

/-- The composition `I ∘ inclH : boundaryH → E` is continuous. -/
theorem continuous_I_inclH : Continuous (I ∘ hI.inclH) :=
  I.continuous.comp hI.inclH_continuous

/-- The composition `I ∘ inclH : boundaryH → E` is injective. The first
factor `I` is injective (a model with corners is); the second factor
`inclH` is injective by hypothesis. -/
theorem injective_I_inclH : Function.Injective (I ∘ hI.inclH) :=
  I.injective.comp hI.inclH_injective

end Inclusion

section Range

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- The image of `inclH` after `I` is contained in the model-level boundary. -/
theorem range_I_inclH_subset_frontier :
    Set.range (I ∘ hI.inclH) ⊆ frontier (Set.range I) := by
  rw [hI.range_I_inclH]

/-- Every point of the model-level boundary lies in the image of `inclH`
after `I`. -/
theorem frontier_subset_range_I_inclH :
    frontier (Set.range I) ⊆ Set.range (I ∘ hI.inclH) := by
  rw [hI.range_I_inclH]

/-- A point `y : E` lies in the model-level boundary `frontier (Set.range I)`
if and only if it lies in the image of `inclH` after `I`. This is the
characterisation of boundary points by an explicit boundary-model
parameterisation. -/
theorem mem_frontier_range_iff_exists_inclH (y : E) :
    y ∈ frontier (Set.range I) ↔ ∃ x : hI.boundaryH, y = I (hI.inclH x) := by
  rw [← hI.range_I_inclH]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- The boundary set `frontier (Set.range I)` is precisely the image of the
parameterisation `I ∘ inclH`. -/
theorem frontier_range_eq_range_I_inclH :
    frontier (Set.range I) = Set.range (I ∘ hI.inclH) := hI.range_I_inclH.symm

/-- A point `h : H` lies in the image of the boundary inclusion `inclH` if
and only if its image under `I` lies in the model-level boundary
`frontier (Set.range I)`. -/
theorem mem_range_inclH_iff (h : H) :
    (∃ z : hI.boundaryH, hI.inclH z = h) ↔ I h ∈ frontier (Set.range I) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨z, rfl⟩
    rw [hI.range_I_inclH.symm]
    exact ⟨z, rfl⟩
  · intro hH
    rw [← hI.range_I_inclH] at hH
    obtain ⟨z, hz⟩ := hH
    refine ⟨z, ?_⟩
    have hz' : I (hI.inclH z) = I h := hz
    exact I.injective hz'

end Range

section Compat

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- Restated coordinate compatibility, in pointwise form. -/
theorem proj_inclH_apply (x : hI.boundaryH) :
    hI.projE (I (hI.inclH x)) = hI.boundaryI x := hI.proj_inclH_compat x

/-- Composition form of the coordinate-compatibility identity:
`projE ∘ I ∘ inclH = boundaryI`. -/
theorem projE_comp_I_comp_inclH :
    hI.projE ∘ I ∘ hI.inclH = hI.boundaryI := by
  funext x
  simpa [Function.comp] using hI.proj_inclH_compat x

end Compat

section TopologicalDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- Membership characterisation: a point `y : E` lies in
`Set.range (I ∘ inclH)` iff there is a witness in `boundaryH`. This is
trivial unfolding of `Set.range`, included for convenience at use sites where
`hI.range_I_inclH` rewrites `frontier (Set.range I)` into a `Set.range`. -/
theorem mem_range_I_inclH_iff (y : E) :
    y ∈ Set.range (I ∘ hI.inclH) ↔ ∃ x : hI.boundaryH, I (hI.inclH x) = y := by
  rfl

/-- The image of `inclH` after `I` is closed in `E`. Direct re-export of the
typeclass field; included for use-site convenience after rewriting the
boundary as a `range`. -/
theorem isClosed_range_I_inclH : IsClosed (Set.range (I ∘ hI.inclH)) :=
  hI.inclH_isClosed_image

/-- The model-level boundary `frontier (Set.range I)` is closed in `E`.
Independent of `HasSmoothBoundary` (it follows from
`isClosed_frontier`), but stated here for convenience. -/
theorem isClosed_frontier_range :
    IsClosed (frontier (Set.range I)) := isClosed_frontier

end TopologicalDerived

section EmbeddingDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- `I ∘ inclH` is a topological inducing map onto its image. The composition
of an embedding (the model with corners `I`) with an inducing map (`inclH`)
is again inducing. -/
theorem isInducing_I_inclH : IsInducing (I ∘ hI.inclH) := by
  have hI_inducing : IsInducing (I : H → E) := I.isClosedEmbedding.isEmbedding.isInducing
  exact hI_inducing.comp hI.inclH_isInducing

/-- `I ∘ inclH` is a topological embedding onto its image. -/
theorem isEmbedding_I_inclH : IsEmbedding (I ∘ hI.inclH) where
  toIsInducing := isInducing_I_inclH I
  injective := injective_I_inclH I

/-- `I ∘ inclH` is a topological closed embedding: it is an embedding with
closed image. Combines `isEmbedding_I_inclH` with the closed-image hypothesis
`inclH_isClosed_image`. -/
theorem isClosedEmbedding_I_inclH : IsClosedEmbedding (I ∘ hI.inclH) where
  toIsEmbedding := isEmbedding_I_inclH I
  isClosed_range := hI.inclH_isClosed_image

end EmbeddingDerived

section SmoothnessDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- The projection `projE : E → boundaryE` is `C^∞` as a map between normed
spaces. Direct re-export of the typeclass field. -/
theorem projE_contDiff' : ContDiff ℝ ∞ hI.projE := hI.projE_contDiff

/-- The composite `I ∘ inclH ∘ boundaryI.symm : boundaryE → E` is `C^∞`.
Direct re-export of the typeclass field. -/
theorem I_inclH_boundaryI_symm_contDiff' :
    ContDiff ℝ ∞ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm) :=
  hI.I_inclH_boundaryI_symm_contDiff

/-- A `ContDiffOn` form of `projE_contDiff`, on any subset of `E`. -/
theorem projE_contDiffOn (s : Set E) : ContDiffOn ℝ ∞ hI.projE s :=
  hI.projE_contDiff.contDiffOn

/-- A `ContDiffOn` form of `I_inclH_boundaryI_symm_contDiff`, on any subset of
`boundaryE`. -/
theorem I_inclH_boundaryI_symm_contDiffOn (s : Set hI.boundaryE) :
    ContDiffOn ℝ ∞ ((I : H → E) ∘ hI.inclH ∘ hI.boundaryI.symm) s :=
  hI.I_inclH_boundaryI_symm_contDiff.contDiffOn

end SmoothnessDerived

section NullSetDerived

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]
variable [FiniteDimensional ℝ E]

/-- Re-export of the typeclass field: the model-level boundary
`frontier (Set.range I)` has zero `Module.finBasis`-Haar measure on `E`.

This is the chart-target reference measure used by the with-boundary
divergence theorem; the property here expresses that the boundary stratum is
a smooth codimension-one submanifold. -/
theorem range_frontier_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (frontier (Set.range I)) = 0 := by
  exact hI.range_frontier_basis_addHaar_zero

/-- Re-export form using `Set.range (I ∘ hI.inclH)` (which equals
`frontier (Set.range I)` by `range_I_inclH`). Convenient for files that have
the `range`-form rewritten. -/
theorem range_inclH_basisAddHaar_volume_zero :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E)
        (Set.range ((I : H → E) ∘ hI.inclH)) = 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [hI.range_I_inclH]
  exact hI.range_frontier_basis_addHaar_zero

/-- Subset / monotonicity form: any subset of the model-level boundary has
zero `Module.finBasis`-Haar measure. -/
theorem subset_range_frontier_basisAddHaar_volume_zero
    {S : Set E} (hS : S ⊆ frontier (Set.range I)) :
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    ((Module.finBasis ℝ E).addHaar : MeasureTheory.Measure E) S = 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  exact MeasureTheory.measure_mono_null hS hI.range_frontier_basis_addHaar_zero

end NullSetDerived

section Boundaryless

variable (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

/-- If `I` is boundaryless, the boundary topological model `boundaryH` is
empty. -/
theorem boundaryH_isEmpty_of_boundaryless [I.Boundaryless] :
    IsEmpty hI.boundaryH := by
  refine ⟨fun x => ?_⟩
  have h_in : I (hI.inclH x) ∈ Set.range (I ∘ hI.inclH) := ⟨x, rfl⟩
  rw [hI.range_I_inclH] at h_in
  rw [show frontier (Set.range I) = ∅ from ?_] at h_in
  · exact (Set.notMem_empty _ h_in)
  · rw [I.range_eq_univ, frontier_univ]

end Boundaryless

end HasSmoothBoundary

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
