import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents

/-!
# The tensor Sobolev space `W^{2k, 2}` of an `(r, s)`-tensor section

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner product space `E` and fixed ranks `(r, s)`, this file defines the
**tensor Sobolev space** `W^{2k, 2}`: a smooth compactly-supported
`(r, s)`-tensor section `T : SmoothCcTensor g r s` is in `W^{2k, 2}` when, for
every chart base point `α : M` of the canonical atlas and every pair of
component multi-indices `(Idx, Jdx)`, the scalar chart component
`tensorChartComp g r s T α Idx Jdx` lies in the Euclidean iterated Sobolev space
`W^{2k, 2}` (`MemWkp (2 * k) 2`).

In a chart an `(r, s)`-tensor field is a tuple of `n ^ (r + s)` scalar functions
on the Euclidean model space (`n = finrank ℝ E`); the tensor `W^{2k, 2}` norm is
assembled from the scalar `W^{2k, 2}` norms of these components, aggregated over
the (countable) chart atlas and the finite component-index set, exactly the way
the scalar chart-Sobolev norm `wkpNormChart` aggregates over charts.

## Main definitions

* `MemWtwokTwo g k T` — the predicate that every scalar chart component of `T`
  lies in `MemWkp (2 * k) 2`.
* `wtwokTwoSubmodule g r s k` / `WtwokTwo g r s k` — the `W^{2k, 2}`-tensors as a
  `Submodule ℝ (SmoothCcTensor g r s)`, with the inherited `AddCommGroup` /
  `Module ℝ` structure.
* `wtwokTwoNorm g k T` — the aggregated tensor Sobolev norm: a `tsum` over the
  chart atlas of the finite sum, over component multi-indices, of the scalar
  `wkpNorm (2 * k) 2` of the chart components.

## Main results

* `MemWtwokTwo_def`, `MemWtwokTwo_iff` — unfolding of the predicate.
* `MemWtwokTwo_zero` — every smooth compactly-supported tensor section is in
  `W^{0, 2}`, i.e. `MemWtwokTwo g 0` holds unconditionally (the scalar
  components are `C^∞` with compact support, hence `L²`).
* `MemWtwokTwo_zero_section`, `MemWtwokTwo_add`, `MemWtwokTwo_smul`,
  `MemWtwokTwo_neg`, `MemWtwokTwo_sub` — closure of the predicate under the
  vector-space operations.
* `wtwokTwoNorm_nonneg`, `wtwokTwoNorm_zero_section`, `wtwokTwoNorm_add_le`,
  `wtwokTwoNorm_smul` — basic algebraic properties of the norm.
* `MemWtwokTwo.le_succ`, `MemWtwokTwo.le_of_le` — monotonicity in the
  regularity order `k`.

## Implementation

This file mirrors the scalar chart-Sobolev scaffold of
`Analysis/Sobolev/Chart/Defs.lean`. There the carrier is `M → ℝ` and the
membership predicate quantifies over chart base points `α : M`; here the carrier
is `SmoothCcTensor g r s` and the predicate quantifies over `α : M` *and* over
the finite set of component multi-indices `(Idx, Jdx)`. Each scalar chart
component is fed into the Euclidean iterated Sobolev predicate `MemWkp (2 * k) 2`
of `Analysis/Sobolev/Euclidean/IteratedSobolev.lean`, and the norm aggregates the
corresponding Euclidean Sobolev norms `wkpNorm (2 * k) 2`.

The full `NormedAddCommGroup` / Banach completeness of `W^{2k, 2}` is **not**
developed here: it requires the chart-transition and completeness machinery and
is deferred to later files. This file delivers the membership predicate, the
submodule, the norm function and its basic algebraic inequalities
(non-negativity, triangle inequality, scalar homogeneity), together with the
`k`-monotonicity statements.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- `MemWtwokTwo g k T`: the smooth compactly-supported `(r, s)`-tensor section
`T` is in the tensor Sobolev space `W^{2k, 2}`.

By definition, for every chart base point `α : M` of the canonical atlas and
every pair of component multi-indices

* `Idx : Fin r → Fin n` (contravariant slots),
* `Jdx : Fin s → Fin n` (covariant slots),

with `n = finrank ℝ E`, the scalar chart component
`tensorChartComp g r s T α Idx Jdx` lies in the Euclidean iterated Sobolev space
`W^{2k, 2}` of the chart target — i.e. `MemWkp (2 * k) 2`.

This mirrors the scalar chart-Sobolev predicate `MemWkpChart`, with the extra
quantifier over the finite component-index set. -/
def MemWtwokTwo
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : Prop :=
  ∀ (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)),
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α)

/-- Unfolding lemma for `MemWtwokTwo`. -/
theorem MemWtwokTwo_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

/-- Equivalent membership characterization. -/
theorem MemWtwokTwo_iff
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ (α : M)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) := Iff.rfl

/-- Every smooth compactly-supported `(r, s)`-tensor section lies in the tensor
Sobolev space `W^{0, 2}`: each scalar chart component is `C^∞` with compact
support on the Euclidean model space, hence in particular `L²` on the chart
target. This is the tensor analogue of "`W^{0, 2}` = `L²`". -/
theorem MemWtwokTwo_zero
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g 0 T := by
  intro α Idx Jdx
  have hmul : (2 * 0 : ℕ) = 0 := by norm_num
  rw [hmul, MemWkp_zero]
  have hcont : Continuous
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx
  have hcs : HasCompactSupport
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) :=
    tensorChartComp_hasCompactSupport (I := I) (M := M) g r s T α Idx Jdx
  exact (hcont.memLp_of_hasCompactSupport (μ := volume.restrict
    (chartTargetEuclid (I := I) (M := M) α)) hcs)

/-- The zero tensor section lies in `W^{2k, 2}`. -/
theorem MemWtwokTwo_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    MemWtwokTwo (I := I) (M := M) g k (0 : SmoothCcTensor g r s) := by
  intro α Idx Jdx
  rw [tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- `MemWtwokTwo` is closed under addition. -/
theorem MemWtwokTwo_add
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    MemWtwokTwo (I := I) (M := M) g k (T₁ + T₂) := by
  intro α Idx Jdx
  rw [tensorChartComp_add (I := I) (M := M) g r s T₁ T₂ α Idx Jdx]
  have hfun :
      (tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx) =
      (fun y => tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx y +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx y) := rfl
  rw [hfun]
  exact MemWkp.add (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h₁ α Idx Jdx) (h₂ α Idx Jdx)

/-- `MemWtwokTwo` is closed under real scalar multiplication. -/
theorem MemWtwokTwo_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    (c : ℝ) {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    MemWtwokTwo (I := I) (M := M) g k (c • T) := by
  intro α Idx Jdx
  rw [tensorChartComp_smul (I := I) (M := M) g r s c T α Idx Jdx]
  have hfun :
      (c • tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) =
      (fun y => c * tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact MemWkp.const_smul (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h α Idx Jdx) c

/-- `MemWtwokTwo` is closed under negation. -/
theorem MemWtwokTwo_neg
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    MemWtwokTwo (I := I) (M := M) g k (-T) := by
  have hsmul := MemWtwokTwo_smul (I := I) (M := M) g (-1 : ℝ) h
  rwa [neg_one_smul] at hsmul

/-- `MemWtwokTwo` is closed under subtraction. -/
theorem MemWtwokTwo_sub
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    MemWtwokTwo (I := I) (M := M) g k (T₁ - T₂) := by
  rw [sub_eq_add_neg]
  exact MemWtwokTwo_add (I := I) (M := M) g h₁ (MemWtwokTwo_neg (I := I) (M := M) g h₂)

/-- The tensor Sobolev space `W^{2k, 2}` as a `Submodule ℝ` of the space of
smooth compactly-supported `(r, s)`-tensor sections. The carrier is the set of
sections satisfying `MemWtwokTwo`; closure under `0`, `+` and `•` is provided by
`MemWtwokTwo_zero_section`, `MemWtwokTwo_add` and `MemWtwokTwo_smul`. -/
def wtwokTwoSubmodule
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    Submodule ℝ (SmoothCcTensor g r s) where
  carrier := { T | MemWtwokTwo (I := I) (M := M) g k T }
  zero_mem' := MemWtwokTwo_zero_section (I := I) (M := M) g k
  add_mem' := fun h₁ h₂ => MemWtwokTwo_add (I := I) (M := M) g h₁ h₂
  smul_mem' := fun c _ h => MemWtwokTwo_smul (I := I) (M := M) g c h

@[simp] lemma mem_wtwokTwoSubmodule
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    T ∈ wtwokTwoSubmodule (I := I) (M := M) g r s k ↔
      MemWtwokTwo (I := I) (M := M) g k T := Iff.rfl

/-- The tensor Sobolev space `W^{2k, 2}` of `(r, s)`-tensor sections, implemented
as the underlying subtype of `wtwokTwoSubmodule`. -/
def WtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) : Type _ :=
  ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k)

instance
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    AddCommGroup (WtwokTwo (I := I) (M := M) g r s k) :=
  inferInstanceAs (AddCommGroup ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k))

instance
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    Module ℝ (WtwokTwo (I := I) (M := M) g r s k) :=
  inferInstanceAs (Module ℝ ↥(wtwokTwoSubmodule (I := I) (M := M) g r s k))

/-- The tensor Sobolev norm `wtwokTwoNorm g k T`: the chart-component norms of
`T`, aggregated over the (countable) chart atlas and the finite component-index
set. Concretely, a `tsum` over chart base points `α : M` of the finite double
sum, over multi-indices `(Idx, Jdx)`, of the scalar Euclidean Sobolev norm
`wkpNorm (2 * k) 2` of the chart component `tensorChartComp g r s T α Idx Jdx`.

This mirrors the scalar chart-Sobolev norm `wkpNormChart`: a `tsum` over charts
of the per-chart contribution, the only difference being that the per-chart
contribution is here a finite sum over the `n ^ (r + s)` tensor components. -/
def wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑' α : M,
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)

/-- Decomposition of the tensor Sobolev norm as a `tsum` over charts of a finite
double sum over component multi-indices. -/
theorem wtwokTwoNorm_eq_tsum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑' α : M,
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- The tensor Sobolev norm is non-negative. (It is valued in `ℝ≥0∞`, so this is
the trivial `0 ≤ ·` fact, recorded for downstream convenience.) -/
theorem wtwokTwoNorm_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ wtwokTwoNorm (I := I) (M := M) g k T :=
  zero_le _

/-- The tensor Sobolev norm of the zero tensor section is zero. -/
theorem wtwokTwoNorm_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    wtwokTwoNorm (I := I) (M := M) g k (0 : SmoothCcTensor g r s) = 0 := by
  unfold wtwokTwoNorm
  have hpt : ∀ α : M,
      (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s
              (0 : SmoothCcTensor g r s) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
    intro α
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [tensorChartComp_zero (I := I) (M := M) g r s α Idx Jdx]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  rw [tsum_congr hpt]
  exact tsum_zero

/-- The triangle inequality for the tensor Sobolev norm. -/
theorem wtwokTwoNorm_add_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    wtwokTwoNorm (I := I) (M := M) g k (T₁ + T₂) ≤
      wtwokTwoNorm (I := I) (M := M) g k T₁ +
        wtwokTwoNorm (I := I) (M := M) g k T₂ := by
  unfold wtwokTwoNorm
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum ?_
  intro α
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Idx _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro Jdx _
  rw [tensorChartComp_add (I := I) (M := M) g r s T₁ T₂ α Idx Jdx]
  have hfun :
      (tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx) =
      (fun y => tensorChartComp (I := I) (M := M) g r s T₁ α Idx Jdx y +
        tensorChartComp (I := I) (M := M) g r s T₂ α Idx Jdx y) := rfl
  rw [hfun]
  exact wkpNorm_add_le (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h₁ α Idx Jdx) (h₂ α Idx Jdx)

/-- The scalar-multiplication identity for the tensor Sobolev norm. -/
theorem wtwokTwoNorm_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    (c : ℝ) {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNorm (I := I) (M := M) g k (c • T) =
      ‖c‖ₑ * wtwokTwoNorm (I := I) (M := M) g k T := by
  unfold wtwokTwoNorm
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr ?_
  intro α
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Idx _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro Jdx _
  rw [tensorChartComp_smul (I := I) (M := M) g r s c T α Idx Jdx]
  have hfun :
      (c • tensorChartComp (I := I) (M := M) g r s T α Idx Jdx) =
      (fun y => c * tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y) := by
    funext y
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact wkpNorm_const_smul (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (h α Idx Jdx) c

/-- Membership in `W^{2(k+1), 2}` implies membership in `W^{2k, 2}`: higher
regularity implies lower regularity. Follows componentwise from the Euclidean
iterated-Sobolev monotonicity `MemWkp.le_of_le`, since `2 * k ≤ 2 * (k + 1)`. -/
theorem MemWtwokTwo.le_succ
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g (k + 1) T) :
    MemWtwokTwo (I := I) (M := M) g k T := by
  intro α Idx Jdx
  have hle : 2 * k ≤ 2 * (k + 1) := by omega
  exact MemWkp.le_of_le (d := Module.finrank ℝ E) hle (h α Idx Jdx)

/-- Membership in `W^{2k', 2}` implies membership in `W^{2k, 2}` whenever
`k ≤ k'`. -/
theorem MemWtwokTwo.le_of_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k k' : ℕ}
    {T : SmoothCcTensor g r s}
    (hk : k ≤ k') (h : MemWtwokTwo (I := I) (M := M) g k' T) :
    MemWtwokTwo (I := I) (M := M) g k T := by
  intro α Idx Jdx
  have hle : 2 * k ≤ 2 * k' := by omega
  exact MemWkp.le_of_le (d := Module.finrank ℝ E) hle (h α Idx Jdx)

/-- The tensor Sobolev subspaces are nested: `W^{2(k+1), 2} ⊆ W^{2k, 2}`. -/
theorem wtwokTwoSubmodule_le_succ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    wtwokTwoSubmodule (I := I) (M := M) g r s (k + 1) ≤
      wtwokTwoSubmodule (I := I) (M := M) g r s k := by
  intro T hT
  exact MemWtwokTwo.le_succ (I := I) (M := M) hT

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
