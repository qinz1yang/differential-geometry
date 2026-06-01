import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolev
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.PartialDerivWithin
import DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.EuclideanHalfSpaceInstance
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Iterated Euclidean Sobolev space `W^{k,p}` on half-space-friendly domains

This module extends the iterated `W^{k,p}` API from
`Analysis/Sobolev/EuclideanIteratedSobolev.lean` to chart-target-style domains
that are *relatively open in the closed half-space* `{y : E | 0 ≤ y 0}`,
rather than open in the full ambient space `E := EuclideanSpace ℝ (Fin d)`.

The construction is uniformly orchestrated as follows: given a half-space-
friendly carrier `Ω ⊆ E` (concretely, `Ω = U ∩ {y | 0 ≤ y 0}` for some open
`U ⊆ E`), let `interiorHalfSpace Ω := Ω ∩ {y | 0 < y 0}`. Then
`interiorHalfSpace Ω` is *open in `E`*, and the Lebesgue measures on `Ω` and
on `interiorHalfSpace Ω` agree, because the two sets differ by the Lebesgue-
null hyperplane `{y | y 0 = 0}`.

Consequently the **Dirichlet (zero-trace) iterated Sobolev space** on a
half-space-friendly `Ω` is captured by
`MemWkp k p u (interiorHalfSpace Ω)`. We package this as
`MemWkpHalfSpace k p u Ω` and re-export the algebraic closure / ae-
invariance / norm theory from the boundaryless module.

## Why "Dirichlet" / "zero-trace"

DeGiorgi's `HasWeakPartialDeriv` quantifies over test functions
`φ : E → ℝ` with `tsupport φ ⊆ Ω`. When `Ω = interiorHalfSpace Ω`, the test-
function support cannot touch the boundary hyperplane `{y | y 0 = 0}`. Hence
`MemWkpHalfSpace` corresponds to the *zero-trace* / *Dirichlet* variant of
the half-space Sobolev space — the appropriate notion for downstream chart-
based Sobolev on manifolds-with-boundary, where chart-pushed compactly
supported scalars vanish at chart-boundary points.

## Main definitions

* `interiorHalfSpace Ω` — the open part of `Ω` strictly above the half-space
  boundary.
* `IsHalfSpaceRelOpen Ω` — the predicate that `Ω = U ∩ closedHalfSpace` for
  some open `U`.
* `MemWkpHalfSpace k p u Ω` — `u ∈ W^{k,p}_0(Ω)` (Dirichlet variant).
* `wkpNormHalfSpace k p u Ω` — the corresponding norm.

## Main results

* `interiorHalfSpace_isOpen` — `interiorHalfSpace Ω` is open in `E` for
  half-space-friendly `Ω`.
* `volume_restrict_interiorHalfSpace_eq` — measure equality.
* `MemWkpHalfSpace.add`, `.const_smul`, `.neg`, `.sub`, `.le_succ`,
  `.le_of_le`, `.zero_iff_memLp` — algebraic / structural closure.
* `MemWkpHalfSpace_zero_fun` — the zero function lies in the space.
* `wkpNormHalfSpace_add_le`, `wkpNormHalfSpace_const_smul`,
  `wkpNormHalfSpace_zero_fun_zero` — norm identities.
* `fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace` — the bridge
  between Fréchet differentiation and DeGiorgi's weak partial, on the open
  interior part of a half-space-friendly carrier.

## Compatibility with the canonical half-space chart-target

`EuclideanHalfSpaceInstance` provides the canonical instance of
`HasSmoothBoundary` for `EuclideanHalfSpace n`. The chart targets
`(extChartAt I α).target` for `M` modelled on `EuclideanHalfSpace n` satisfy
`(extChartAt I α).target = (chart-source-image) ∩ range I`, where
`range I = {y | 0 ≤ y 0} = closedHalfSpace`. Such targets are precisely the
half-space-friendly sets the present API targets. See
`extChartAt_target_isHalfSpaceRelOpen` for the explicit identification.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The *closed* upper half-space `{y : E | 0 ≤ y 0}`. -/
def closedHalfSpace : Set E := {y : E | 0 ≤ y 0}

/-- The *open* upper half-space `{y : E | 0 < y 0}`. -/
def openHalfSpace : Set E := {y : E | 0 < y 0}

/-- The *boundary hyperplane* `{y : E | y 0 = 0}`. -/
def boundaryHyperplane : Set E := {y : E | y 0 = 0}

@[simp] lemma closedHalfSpace_def :
    closedHalfSpace (d := d) = {y : E | 0 ≤ y 0} := rfl

@[simp] lemma openHalfSpace_def :
    openHalfSpace (d := d) = {y : E | 0 < y 0} := rfl

@[simp] lemma boundaryHyperplane_def :
    boundaryHyperplane (d := d) = {y : E | y 0 = 0} := rfl

/-- The closed half-space contains the open half-space. -/
theorem openHalfSpace_subset_closedHalfSpace :
    openHalfSpace (d := d) ⊆ closedHalfSpace := by
  intro y hy
  change (0 : ℝ) ≤ y 0
  exact le_of_lt hy

/-- The closed half-space is the union of the open half-space and the
boundary hyperplane. -/
theorem closedHalfSpace_eq_union :
    closedHalfSpace (d := d) = openHalfSpace ∪ boundaryHyperplane := by
  ext y
  simp only [closedHalfSpace, openHalfSpace, boundaryHyperplane,
    mem_setOf_eq, mem_union]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h.symm

/-- The open half-space is open in `E`, since it is the preimage of `Ioi 0`
under the continuous coordinate-`0` evaluation. -/
theorem isOpen_openHalfSpace [NeZero d] :
    IsOpen (openHalfSpace (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : openHalfSpace (d := d) = (fun y : E => y 0) ⁻¹' Set.Ioi 0 := rfl
  rw [heq]
  exact hcont.isOpen_preimage _ isOpen_Ioi

/-- The boundary hyperplane is closed in `E`. -/
theorem isClosed_boundaryHyperplane [NeZero d] :
    IsClosed (boundaryHyperplane (d := d)) := by
  have hcont : Continuous (fun y : E => y 0) := PiLp.continuous_apply 2 _ 0
  have heq : boundaryHyperplane (d := d) = (fun y : E => y 0) ⁻¹' {0} := rfl
  rw [heq]
  exact isClosed_singleton.preimage hcont

/-- The boundary hyperplane has zero `volume` (Lebesgue measure) on `E`. -/
theorem volume_boundaryHyperplane_eq_zero [NeZero d] :
    (volume : Measure E) (boundaryHyperplane (d := d)) = 0 := by
  classical
  set ker : Submodule ℝ E :=
    (EuclideanSpace.proj (0 : Fin d) :
      E →L[ℝ] ℝ).toLinearMap.ker with hker_def
  have hsubm :
      (boundaryHyperplane (d := d) : Set E) = (ker : Set E) := by
    ext y
    simp [hker_def, boundaryHyperplane, LinearMap.mem_ker,
      EuclideanSpace.proj]
  rw [hsubm]
  refine MeasureTheory.Measure.addHaar_submodule
    (μ := (volume : MeasureTheory.Measure E)) ker ?_
  intro hker_eq
  have h_in_top : EuclideanSpace.single (0 : Fin d) (1 : ℝ) ∈
      (⊤ : Submodule ℝ E) := Submodule.mem_top
  rw [← hker_eq] at h_in_top
  have h_proj_zero :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) = 0 := by
    have := h_in_top
    simp only [hker_def, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe] at this
    exact this
  have h_eval :
      (EuclideanSpace.proj (0 : Fin d) : E →L[ℝ] ℝ)
        (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
      (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 := rfl
  have h_one : (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) 0 = 1 := by
    rw [show (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) =
          PiLp.single 2 (0 : Fin d) (1 : ℝ) from rfl]
    rw [PiLp.single_apply]
    simp
  rw [h_one] at h_eval
  exact one_ne_zero (h_proj_zero.symm.trans h_eval).symm

/-- Given a carrier `Ω ⊆ E`, the *interior part* is the slice strictly above
the boundary hyperplane: `Ω ∩ {y | 0 < y 0}`. For a half-space-friendly `Ω`
(i.e., `Ω = U ∩ closedHalfSpace` for some open `U`), the interior part is
`U ∩ openHalfSpace`, which is open in `E`. -/
def interiorHalfSpace (Ω : Set E) : Set E := Ω ∩ openHalfSpace

@[simp] lemma interiorHalfSpace_def (Ω : Set E) :
    interiorHalfSpace (d := d) Ω = Ω ∩ openHalfSpace := rfl

/-- The interior part is contained in the original carrier. -/
theorem interiorHalfSpace_subset (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ Ω := inter_subset_left

/-- The interior part is contained in the open half-space. -/
theorem interiorHalfSpace_subset_openHalfSpace (Ω : Set E) :
    interiorHalfSpace (d := d) Ω ⊆ openHalfSpace := inter_subset_right

/-- `Ω` is *half-space-friendly* (or: half-space-relatively-open) when it is
an open subset of `E` *intersected with* the closed half-space — i.e., it is
relatively open in `closedHalfSpace`.

Concretely, this captures the shape of chart targets
`(extChartAt I α).target` for a manifold modelled on `EuclideanHalfSpace n`:
such targets are intersections of an open subset of `E` (the model-side
representation of the chart source) with `range (𝓡∂ n) = closedHalfSpace`.

A half-space-friendly carrier need *not* be open in `E`; it is open in `E` if
and only if it is contained in `openHalfSpace`. -/
def IsHalfSpaceRelOpen (Ω : Set E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ Ω = U ∩ closedHalfSpace

/-- An open carrier inside the open half-space is automatically half-space-
friendly. -/
theorem IsHalfSpaceRelOpen.of_isOpen_subset_open
    {Ω : Set E} (hΩ : IsOpen Ω) (hsub : Ω ⊆ openHalfSpace) :
    IsHalfSpaceRelOpen (d := d) Ω := by
  refine ⟨Ω, hΩ, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    refine ⟨hy, ?_⟩
    exact openHalfSpace_subset_closedHalfSpace (hsub hy)
  · intro y ⟨hy, _⟩
    exact hy

/-- A half-space-friendly carrier is contained in the closed half-space. -/
theorem IsHalfSpaceRelOpen.subset_closedHalfSpace
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω ⊆ closedHalfSpace := by
  obtain ⟨U, _hU, hU_eq⟩ := hΩ
  rw [hU_eq]
  exact inter_subset_right

/-- For a half-space-friendly `Ω`, the interior part `Ω ∩ openHalfSpace`
equals `U ∩ openHalfSpace` (where `Ω = U ∩ closedHalfSpace`).

This is the engine identity: chopping by `openHalfSpace ⊆ closedHalfSpace`
is the same as chopping `U` directly. -/
theorem interiorHalfSpace_eq_inter_openHalfSpace
    {Ω : Set E} {U : Set E}
    (hU_eq : Ω = U ∩ closedHalfSpace) :
    interiorHalfSpace (d := d) Ω = U ∩ openHalfSpace := by
  unfold interiorHalfSpace
  rw [hU_eq]
  ext y
  simp only [mem_inter_iff, closedHalfSpace, openHalfSpace, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hU, _⟩, h_open⟩
    exact ⟨hU, h_open⟩
  · rintro ⟨hU, h_open⟩
    exact ⟨⟨hU, le_of_lt h_open⟩, h_open⟩

/-- For a half-space-friendly `Ω`, the interior part is open in `E`. -/
theorem interiorHalfSpace_isOpen [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    IsOpen (interiorHalfSpace (d := d) Ω) := by
  obtain ⟨U, hU, hU_eq⟩ := hΩ
  rw [interiorHalfSpace_eq_inter_openHalfSpace hU_eq]
  exact hU.inter (isOpen_openHalfSpace (d := d))

/-- For a half-space-friendly `Ω`, the symmetric difference between `Ω` and
its interior part is contained in the boundary hyperplane. -/
theorem symmDiff_interiorHalfSpace_subset_boundaryHyperplane
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω \ interiorHalfSpace Ω ⊆ boundaryHyperplane := by
  intro y ⟨hy_in, hy_notIn⟩
  unfold interiorHalfSpace at hy_notIn
  simp only [mem_inter_iff, openHalfSpace, mem_setOf_eq, not_and, not_lt]
    at hy_notIn
  have h_le : y 0 ≤ 0 := hy_notIn hy_in
  have h_ge : 0 ≤ y 0 := hΩ.subset_closedHalfSpace hy_in
  exact le_antisymm h_le h_ge

/-- For a half-space-friendly `Ω`, the carrier and its interior part are
equal almost everywhere with respect to Lebesgue measure. -/
theorem ae_eq_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    Ω =ᵐ[(volume : Measure E)] interiorHalfSpace (d := d) Ω := by
  have h_diff1 : (volume : Measure E) (Ω \ interiorHalfSpace Ω) = 0 := by
    have hsub :=
      symmDiff_interiorHalfSpace_subset_boundaryHyperplane (d := d) hΩ
    have h_zero := volume_boundaryHyperplane_eq_zero (d := d)
    exact MeasureTheory.measure_mono_null hsub h_zero
  have h_diff2 : (volume : Measure E) (interiorHalfSpace Ω \ Ω) = 0 := by
    have h_empty : interiorHalfSpace Ω \ Ω = ∅ := by
      ext y
      simp only [mem_diff, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hy
      exact interiorHalfSpace_subset Ω hy
    rw [h_empty]
    exact measure_empty
  exact (MeasureTheory.ae_eq_set).mpr ⟨h_diff1, h_diff2⟩

/-- For a half-space-friendly `Ω`, the restricted Lebesgue measures on the
carrier and on its interior part coincide. -/
theorem volume_restrict_interiorHalfSpace_eq [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    (volume : Measure E).restrict Ω =
      (volume : Measure E).restrict (interiorHalfSpace (d := d) Ω) :=
  MeasureTheory.Measure.restrict_congr_set (ae_eq_interiorHalfSpace hΩ)

/-- Iterated `W^{k,p}` membership predicate on a half-space-friendly domain.

This is the **Dirichlet (zero-trace) variant**: it is defined as the standard
`MemWkp` membership for the *interior part* of `Ω`, which is open in `E`.
Test functions in the underlying `HasWeakPartialDeriv` cannot reach the
boundary hyperplane (their `tsupport` lies inside `interiorHalfSpace Ω`,
which sits strictly inside the open half-space), so the resulting space is
the zero-trace one.

When `Ω` is itself open in `E` and contained in `openHalfSpace`, this
predicate coincides with the boundaryless `MemWkp`. -/
def MemWkpHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : Prop :=
  MemWkp (d := d) k p u (interiorHalfSpace Ω)

@[simp] lemma MemWkpHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    MemWkpHalfSpace (d := d) k p u Ω ↔
      MemWkp (d := d) k p u (interiorHalfSpace Ω) := Iff.rfl

/-- For an open carrier `Ω ⊆ openHalfSpace`, the half-space-Sobolev membership
coincides with the standard `MemWkp` on `Ω`. -/
theorem MemWkpHalfSpace_iff_memWkp_of_subset_openHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hsub : Ω ⊆ openHalfSpace) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkp (d := d) k p u Ω := by
  unfold MemWkpHalfSpace interiorHalfSpace
  rw [show Ω ∩ openHalfSpace = Ω from inter_eq_self_of_subset_left hsub]

/-- Half-space-Sobolev order `0` reduces to `L^p` of the interior part. -/
theorem MemWkpHalfSpace.zero_iff_memLp
    {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.zero_iff_memLp

/-- Half-space-Sobolev order `0` reduces to `L^p` of the carrier (using the
measure-equality with the interior part). -/
theorem MemWkpHalfSpace.zero_iff_memLp_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω) {u : E → ℝ} :
    MemWkpHalfSpace (d := d) 0 p u Ω ↔
      MemLp u p ((volume : Measure E).restrict Ω) := by
  rw [MemWkpHalfSpace.zero_iff_memLp,
      ← volume_restrict_interiorHalfSpace_eq hΩ]

/-- `W^{k+1,p}_0(Ω) ⊆ W^{k,p}_0(Ω)`. -/
theorem MemWkpHalfSpace.le_succ
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) (k + 1) p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_succ h

/-- `W^{k',p}_0(Ω) ⊆ W^{k,p}_0(Ω)` whenever `k ≤ k'`. -/
theorem MemWkpHalfSpace.le_of_le
    {k k' : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (hk : k ≤ k') (h : MemWkpHalfSpace (d := d) k' p u Ω) :
    MemWkpHalfSpace (d := d) k p u Ω :=
  MemWkp.le_of_le hk h

/-- Membership in `W^{k,p}_0(Ω)` implies membership in `L^p` of the
interior part. -/
theorem MemWkpHalfSpace.memLp
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  MemWkp.memLp h

/-- Membership in `W^{k,p}_0(Ω)` implies membership in `L^p` of the carrier. -/
theorem MemWkpHalfSpace.memLp_of_relOpen [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    MemLp u p ((volume : Measure E).restrict Ω) := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ]
  exact h.memLp

/-- The zero function lies in `W^{k,p}_0(Ω)` for any half-space-friendly
carrier `Ω` and any `1 ≤ p`. -/
theorem MemWkpHalfSpace_zero_fun [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    MemWkpHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω :=
  MemWkp_zero_fun (d := d) hp (interiorHalfSpace_isOpen hΩ)

/-- `MemWkpHalfSpace` is closed under addition. -/
theorem MemWkpHalfSpace.add [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x + v x) Ω :=
  MemWkp.add (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

/-- `MemWkpHalfSpace` is closed under scalar multiplication. -/
theorem MemWkpHalfSpace.const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    MemWkpHalfSpace (d := d) k p (fun x => c * u x) Ω :=
  MemWkp.const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

/-- `MemWkpHalfSpace` is closed under negation. -/
theorem MemWkpHalfSpace.neg [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => - u x) Ω :=
  MemWkp.neg (d := d) hp (interiorHalfSpace_isOpen hΩ) hu

/-- `MemWkpHalfSpace` is closed under subtraction. -/
theorem MemWkpHalfSpace.sub [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    MemWkpHalfSpace (d := d) k p (fun x => u x - v x) Ω :=
  MemWkp.sub (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

/-- `MemWkpHalfSpace k p` is invariant under ae-equality on the interior
part, for `1 ≤ p`. -/
theorem MemWkpHalfSpace_congr_ae [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict (interiorHalfSpace Ω)] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω :=
  MemWkp_congr_ae (d := d) hp (interiorHalfSpace_isOpen hΩ) huv

/-- `MemWkpHalfSpace k p` is invariant under ae-equality on the carrier, for
`1 ≤ p`. -/
theorem MemWkpHalfSpace_congr_ae_of_carrier [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (huv : u =ᵐ[(volume : Measure E).restrict Ω] v) :
    MemWkpHalfSpace (d := d) k p u Ω ↔ MemWkpHalfSpace (d := d) k p v Ω := by
  rw [volume_restrict_interiorHalfSpace_eq hΩ] at huv
  exact MemWkpHalfSpace_congr_ae (d := d) hp hΩ huv

/-- The half-space-Sobolev norm: the iterated `W^{k,p}` norm computed on the
interior part. -/
def wkpNormHalfSpace (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) : ℝ≥0∞ :=
  wkpNorm (d := d) k p u (interiorHalfSpace Ω)

@[simp] lemma wkpNormHalfSpace_def
    (k : ℕ) (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) k p u Ω =
      wkpNorm (d := d) k p u (interiorHalfSpace Ω) := rfl

/-- Order-zero norm: it is just the `eLpNorm` on the interior part. -/
theorem wkpNormHalfSpace_zero
    (p : ℝ≥0∞) (u : E → ℝ) (Ω : Set E) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) :=
  wkpNorm_zero (d := d) p u (interiorHalfSpace Ω)

/-- Order-zero norm equals the `eLpNorm` on the carrier (using the measure
equality with the interior part). -/
theorem wkpNormHalfSpace_zero_of_relOpen [NeZero d]
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (u : E → ℝ) :
    wkpNormHalfSpace (d := d) 0 p u Ω =
      eLpNorm u p ((volume : Measure E).restrict Ω) := by
  rw [wkpNormHalfSpace_zero, ← volume_restrict_interiorHalfSpace_eq hΩ]

/-- The half-space-Sobolev norm of the zero function is zero, for half-
space-friendly `Ω` and `1 ≤ p`. -/
theorem wkpNormHalfSpace_zero_fun_zero [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω) :
    wkpNormHalfSpace (d := d) k p (fun _ : E => (0 : ℝ)) Ω = 0 :=
  wkpNorm_zero_fun_zero (d := d) hp (interiorHalfSpace_isOpen hΩ)

/-- The half-space-Sobolev norm is finite for any function in
`W^{k,p}_0(Ω)`. -/
theorem wkpNormHalfSpace_lt_top_of_memWkpHalfSpace
    {k : ℕ} {p : ℝ≥0∞} {Ω : Set E} {u : E → ℝ}
    (h : MemWkpHalfSpace (d := d) k p u Ω) :
    wkpNormHalfSpace (d := d) k p u Ω < (⊤ : ℝ≥0∞) :=
  wkpNorm_lt_top_of_memWkp h

/-- Triangle inequality for `wkpNormHalfSpace`. -/
theorem wkpNormHalfSpace_add_le [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u v : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω)
    (hv : MemWkpHalfSpace (d := d) k p v Ω) :
    wkpNormHalfSpace (d := d) k p (fun x => u x + v x) Ω ≤
      wkpNormHalfSpace (d := d) k p u Ω +
        wkpNormHalfSpace (d := d) k p v Ω :=
  wkpNorm_add_le (d := d) hp (interiorHalfSpace_isOpen hΩ) hu hv

/-- Scalar-multiplication identity for `wkpNormHalfSpace`. -/
theorem wkpNormHalfSpace_const_smul [NeZero d]
    {k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set E}
    (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ}
    (hu : MemWkpHalfSpace (d := d) k p u Ω) (c : ℝ) :
    wkpNormHalfSpace (d := d) k p (fun x => c * u x) Ω =
      ‖c‖ₑ * wkpNormHalfSpace (d := d) k p u Ω :=
  wkpNorm_const_smul (d := d) hp (interiorHalfSpace_isOpen hΩ) hu c

/-- The Fréchet partial derivative
`y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)` of a smooth function `u` is a
weak partial derivative of `u` on the open interior part of a half-space-
friendly carrier. -/
theorem fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace [NeZero d]
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ 1 u) (i : Fin d) :
    DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1))
      u (interiorHalfSpace Ω) :=
  DeGiorgi.HasWeakPartialDeriv.of_contDiff (interiorHalfSpace_isOpen hΩ)
    hu_smooth

/-- For a smooth function `u`, the Fréchet partial derivative
`y ↦ fderiv ℝ u y (EuclideanSpace.single i 1)` lies in `MemLp` on the open
interior part, provided the function and its partial derivative themselves
do — e.g., for compactly supported smooth functions on the carrier. -/
theorem fderiv_memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E} (_hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) (i : Fin d) :
    MemLp (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p
      ((volume : Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_smooth : ContDiff ℝ ∞
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) := by
    have h_fderiv : ContDiff ℝ ∞ (fun x => fderiv ℝ u x) :=
      hu_smooth.fderiv_right (m := (∞ : WithTop ℕ∞)) (by
        rw [ENat.coe_top_add_one])
    exact h_fderiv.clm_apply contDiff_const
  have h_supp : HasCompactSupport
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
    hu_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have h_global : MemLp
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) p volume :=
    h_smooth.continuous.memLp_of_hasCompactSupport h_supp
  exact h_global.restrict (interiorHalfSpace Ω)

/-- A smooth compactly supported function on the carrier lies in `MemLp` on
the open interior part. -/
theorem memLp_of_smooth_compactSupport
    {p : ℝ≥0∞} {Ω : Set E} (_hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) :
    MemLp u p ((volume : Measure E).restrict (interiorHalfSpace Ω)) := by
  have h_global : MemLp u p (volume : Measure E) :=
    hu_smooth.continuous.memLp_of_hasCompactSupport hu_supp
  exact h_global.restrict (interiorHalfSpace Ω)

/-- A smooth compactly supported function lies in DeGiorgi's `MemW1p` on
the open interior part of a half-space-friendly carrier. -/
theorem memW1p_of_smooth_compactSupport_interiorHalfSpace
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {u : E → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_supp : HasCompactSupport u) :
    DeGiorgi.MemW1p p u (interiorHalfSpace Ω) := by
  refine ⟨memLp_of_smooth_compactSupport hΩ hu_smooth hu_supp, ?_⟩
  intro i
  refine ⟨fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1),
    fderiv_memLp_of_smooth_compactSupport hΩ hu_smooth hu_supp i, ?_⟩
  exact fderiv_isWeakPartialDeriv_of_smooth_interiorHalfSpace hΩ
    (hu_smooth.of_le (by norm_cast)) i

/-- The within-Fréchet partial derivative on the open interior part equals
the ordinary Fréchet partial derivative there. Direct re-export of
`partialDerivWithin_eq_partialDeriv_of_isOpen` specialised to the half-space
setting. -/
theorem partialDerivWithin_interiorHalfSpace_eq_partialDeriv
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) {y : E}
    (hy : y ∈ interiorHalfSpace Ω) :
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin
        (interiorHalfSpace Ω) i u y =
      DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
        i u y :=
  DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.partialDerivWithin_eq_partialDeriv_of_isOpen
    (interiorHalfSpace_isOpen hΩ) hy

section EuclideanHalfSpaceChartTargets

variable {n : ℕ} [NeZero n]

/-- The model-side range of `modelWithCornersEuclideanHalfSpace n` equals
`closedHalfSpace` in the local Sobolev terminology. -/
theorem range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace :
    Set.range (modelWithCornersEuclideanHalfSpace n :
        EuclideanHalfSpace n → EuclideanSpace ℝ (Fin n)) =
      closedHalfSpace (d := n) := by
  rw [range_modelWithCornersEuclideanHalfSpace]
  ext y
  simp [closedHalfSpace]

/-- An `extChartAt` target in a manifold modelled on
`EuclideanHalfSpace n` is half-space-friendly: it is the intersection of
an open subset of `EuclideanSpace ℝ (Fin n)` (the model-side preimage of
the chart-source target) with `closedHalfSpace`. -/
theorem extChartAt_target_isHalfSpaceRelOpen
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M] (α : M) :
    IsHalfSpaceRelOpen (d := n)
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target := by
  refine ⟨(modelWithCornersEuclideanHalfSpace n).symm ⁻¹'
      (chartAt (EuclideanHalfSpace n) α).target, ?_, ?_⟩
  · exact (chartAt (EuclideanHalfSpace n) α).open_target.preimage
      (modelWithCornersEuclideanHalfSpace n).continuous_symm
  · rw [extChartAt_target,
      range_modelWithCornersEuclideanHalfSpace_eq_closedHalfSpace]

end EuclideanHalfSpaceChartTargets

section UsabilityCheck

variable {n : ℕ} [NeZero n]

/-- Example: the zero function lies in `W^{k,p}_0` of any chart target on a
manifold modelled on `EuclideanHalfSpace n`. -/
example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    MemWkpHalfSpace (d := n) k p (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ))
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target :=
  MemWkpHalfSpace_zero_fun (d := n) hp
    (extChartAt_target_isHalfSpaceRelOpen α)

/-- Example: addition closure on chart targets. -/
example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) (k : ℕ) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemWkpHalfSpace (d := n) k p u
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target)
    (hv : MemWkpHalfSpace (d := n) k p v
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target) :
    MemWkpHalfSpace (d := n) k p (fun x => u x + v x)
      (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target :=
  MemWkpHalfSpace.add (d := n) hp
    (extChartAt_target_isHalfSpaceRelOpen α) hu hv

/-- Example: a smooth compactly supported function on the chart target lies
in `MemW1p` on the open interior part. The compactly-supported-strictly-
inside-interior conditions ensure the function is "Dirichlet"-compatible. -/
example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
    (α : M) {p : ℝ≥0∞}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu_smooth : ContDiff ℝ ∞ u) (hu_supp : HasCompactSupport u) :
    DeGiorgi.MemW1p p u
      (interiorHalfSpace (d := n)
        (extChartAt (modelWithCornersEuclideanHalfSpace n) α).target) :=
  memW1p_of_smooth_compactSupport_interiorHalfSpace
    (extChartAt_target_isHalfSpaceRelOpen α) hu_smooth hu_supp

end UsabilityCheck

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
