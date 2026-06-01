import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.POUFDerivBound
import DifferentialGeometry.Analysis.Sobolev.Euclidean.MultiplyQuantK
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Density

/-!
# Raw chart-component Sobolev norm for `(r, s)`-tensor sections

For a closed Riemannian manifold `(M, g)` with finite-rank model fibre `E`, and
a smooth compactly-supported `(r, s)`-tensor section `T`, this file introduces a
second tensor Sobolev norm assembled directly from the **raw** chart-frame
scalar components of `T` (without the partition-of-unity weight) and relates it
to the canonical `wtwokTwoNorm` of `Tensor/Defs.lean`.

The standard `wtwokTwoNorm g k T` aggregates `wkpNorm (2 * k) 2` of
`tensorChartComp g r s T α Idx Jdx = chartPushedRaw I α (ρ_α · raw)` over the
chart atlas; the partition-of-unity factor `ρ_α` makes this Euclidean function
globally `C^∞` with compact support inside the chart-target image. The norm
defined here aggregates the same Euclidean Sobolev norm but of the **raw**
chart-pushed function `chartPushedRaw I α raw` (omitting the POU weight) over
the finite POU-support set.

The pointwise factorisation

  `chartPushedRaw I α (ρ_α · raw) = chartSmoothExt α ρ_α · chartPushedRaw I α raw`

(established in this file) is the bridge: the LHS is precisely the
`tensorChartComp` that enters `wtwokTwoNorm`, and the RHS exhibits the per-term
LHS as the pointwise product of a globally `C^∞` compactly-supported smooth
multiplier with the raw chart-pushed component that enters `wkpNormChartRaw`.

## Main definitions

* `wkpNormChartRaw g r s k T` — the `W^{2k, 2}` norm of `T` built from the
  raw (POU-unweighted) chart components, summed over `chartAtlasPOU_finset`
  and the finite component-index set.

## Main results

* `wkpNormChartRaw_zero_section` — vanishing on the zero tensor section.
* `wkpNormChartRaw_nonneg` — non-negativity of the new norm.
* `chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw` — the pointwise
  product factorisation of the Euclidean push-forward of a scalar product.
* `wtwokTwoNorm_eq_finsum_chartAtlasPOU` — the tsum-over-`α` defining
  `wtwokTwoNorm` collapses to a finite sum over `chartAtlasPOU_finset`,
  because off the POU support the chart component vanishes identically.

## Implementation

The pointwise factorisation
`chartPushedRaw I α (ρ_α · raw) = chartSmoothExt α ρ_α · chartPushedRaw I α raw`
holds globally on the Euclidean ambient space: on the chart-target image both
sides equal `ρ_α(x) * raw(x)` (with `x = (extChartAt I α).symm (toEuclidean.symm y)`);
off the target image both sides are zero. This is verified directly from the
definitions of `chartPushedRaw` and `chartSmoothExt`.

The multiplier `chartSmoothExt α (chartAtlasPOU I M α)` is globally `C^∞` with
compact support (via `contDiff_chartSmoothExt_chartAtlasPOU` and
`hasCompactSupport_chartSmoothExt_chartAtlasPOU` of
`Parabolic/TensorSpectral/ChartTensor/POUFDerivBound.lean`); its iterated
derivatives up to any finite order are therefore uniformly bounded on `EuclN`
via `exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport`, providing
the analytic data needed for the quantitative-Leibniz bound
`wkpNorm_smul_smooth_bounded_le`.

Outside the finite POU support, the POU weight vanishes identically, so
`chartPushedRaw I α (ρ_α · raw)` vanishes identically and its `wkpNorm`
contribution is zero, making the tsum over `α : M` (in `wtwokTwoNorm`) collapse
to the finite sum over `chartAtlasPOU_finset` (`wtwokTwoNorm_eq_finsum_chartAtlasPOU`).
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

/-- The `W^{2k, 2}` norm of a smooth compactly-supported `(r, s)`-tensor section
built from the **raw** (POU-unweighted) chart-frame scalar components.

For each chart base point `α ∈ chartAtlasPOU_finset I M` and each pair of
component multi-indices `(Idx, Jdx)`, the raw scalar component
`tensorChartComponentRaw g r s T α Idx Jdx : M → ℝ` is chart-pushed to a
function on the Euclidean model space via `chartPushedRaw I α`, and its
`W^{2k, 2}` Euclidean Sobolev norm `wkpNorm (2 * k) 2 _ Ω_α` (where
`Ω_α = chartTargetEuclid α`) is computed. The norm is the finite sum, over the
POU-support set and the finite component-index set, of these contributions.

This differs from `wtwokTwoNorm g k T` in the placement of the partition-of-
unity weight: `wtwokTwoNorm` measures `wkpNorm` of `chartPushedRaw I α (ρ_α · raw)`,
which is globally `C^∞` and compactly supported on the Euclidean ambient space,
whereas the present norm measures `wkpNorm` of the unweighted `chartPushedRaw I α raw`
on the open chart-target. -/
def wkpNormChartRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) : ℝ≥0∞ :=
  ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
          (chartTargetEuclid (I := I) (M := M) α)

/-- Unfolding lemma for `wkpNormChartRaw`. -/
theorem wkpNormChartRaw_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) :
    wkpNormChartRaw (I := I) (M := M) g r s k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (chartPushedRaw (I := I) (M := M) α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- Non-negativity of the raw chart-component Sobolev norm. -/
theorem wkpNormChartRaw_nonneg
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s) :
    0 ≤ wkpNormChartRaw (I := I) (M := M) g r s k T :=
  zero_le _

/-- The raw chart-component Sobolev norm of the zero tensor section is zero. -/
theorem wkpNormChartRaw_zero_section
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    wkpNormChartRaw (I := I) (M := M) g r s k (0 : SmoothCcTensor g r s) = 0 := by
  classical
  unfold wkpNormChartRaw
  refine Finset.sum_eq_zero ?_
  intro α _
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  have hraw_zero :
      tensorChartComponentRaw (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α Idx Jdx = (fun _ : M => (0 : ℝ)) := by
    funext x
    rw [tensorChartComponentRaw_def]
    have hzero : tensorTrivProj (I := I) (M := M) g r s
        (0 : SmoothCcTensor g r s) α x = 0 := by
      unfold tensorTrivProj
      have hsec : (0 : SmoothCcTensor g r s).toSection x = 0 := rfl
      rw [hsec, map_zero]
    rw [hzero, map_zero]
  rw [hraw_zero]
  have hpush_zero :
      chartPushedRaw (I := I) (M := M) α (fun _ : M => (0 : ℝ)) =
        (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
    funext y
    classical
    by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
    · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
  rw [hpush_zero]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- **Pointwise factorisation.** For any scalar functions `ρ u : M → ℝ` and
chart base point `α : M`, the pointwise identity

  `chartPushedRaw I α (ρ · u) y = chartSmoothExt α ρ y * chartPushedRaw I α u y`

holds for every `y` in the Euclidean ambient space. -/
theorem chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw
    (α : M) (ρ u : M → ℝ)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    chartPushedRaw (I := I) (M := M) α (fun x : M => ρ x * u x) y =
      chartSmoothExt (I := I) (M := M) α ρ y *
        chartPushedRaw (I := I) (M := M) α u y := by
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α u hy]
    have hsymm : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
    change (ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) *
        (u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      (if (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target then
        ρ ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
       else 0) *
      u ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    rw [if_pos hsymm]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]
    rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α u hy]
    rw [mul_zero]

/-- Functional version of the pointwise factorisation. -/
theorem chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw_funext
    (α : M) (ρ u : M → ℝ) :
    (chartPushedRaw (I := I) (M := M) α (fun x : M => ρ x * u x)) =
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartSmoothExt (I := I) (M := M) α ρ y *
          chartPushedRaw (I := I) (M := M) α u y) := by
  funext y
  exact chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw
    (I := I) (M := M) α ρ u y

/-- **Tensor specialisation of the factorisation.** The POU-weighted chart-
pushed tensor scalar component `tensorChartComp` equals, pointwise on the
Euclidean ambient space, the product of the smooth POU multiplier
`chartSmoothExt α (chartAtlasPOU I M α)` and the raw chart-pushed component
`chartPushedRaw I α (tensorChartComponentRaw g r s T α Idx Jdx)`. -/
theorem tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx =
      (fun y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
        chartSmoothExt (I := I) (M := M) α
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
          chartPushedRaw (I := I) (M := M) α
            (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx) y) := by
  classical
  rw [tensorChartComp_def, tensorChartComponent_def]
  have hPouRaw : (tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx) =
      (fun x : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x *
        tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx x) := by
    funext x; rfl
  rw [hPouRaw]
  exact chartPushedRaw_mul_eq_chartSmoothExt_mul_chartPushedRaw_funext
    (I := I) (M := M) α
    (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ))
    (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx)

/-- Off `chartAtlasPOU_finset`, the POU weight vanishes identically, so the
POU-weighted chart-pushed tensor scalar component `tensorChartComp` is the
zero function on the Euclidean ambient space. -/
theorem tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx =
      (fun _ : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) => (0 : ℝ)) := by
  classical
  rw [tensorChartComp_def, tensorChartComponent_def]
  have hpou_zero : ∀ x : M,
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0 := fun x =>
    chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  have hpou_comp_zero :
      (tensorChartComponentPou (I := I) (M := M) g r s T α Idx Jdx) =
      (fun _ : M => (0 : ℝ)) := by
    funext x
    unfold tensorChartComponentPou
    rw [hpou_zero x]
    ring
  rw [hpou_comp_zero]
  funext y
  classical
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
  · rw [chartPushedRaw_apply_of_notMem (I := I) (M := M) α _ hy]

/-- The `wkpNorm` contribution of `tensorChartComp` vanishes outside
`chartAtlasPOU_finset`. -/
theorem wkpNorm_tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ)
    (T : SmoothCcTensor g r s)
    {α : M} (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
  rw [tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (I := I) (M := M) g r s T hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- The tsum-over-`α` defining `wtwokTwoNorm` collapses to a finite sum over
`chartAtlasPOU_finset`. -/
theorem wtwokTwoNorm_eq_finsum_chartAtlasPOU
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wtwokTwoNorm
  refine tsum_eq_sum ?_
  intro α hα
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  exact wkpNorm_tensorChartComp_eq_zero_of_notMem_chartAtlasPOU_finset
    (I := I) (M := M) g r s k T hα Idx Jdx

/-- The smooth POU multiplier `chartSmoothExt α (chartAtlasPOU I M α)` is
globally `C^∞` on the Euclidean ambient space. -/
theorem chartSmoothExt_chartAtlasPOU_contDiff (α : M) :
    ContDiff ℝ (⊤ : ℕ∞)
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  contDiff_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α

/-- The smooth POU multiplier `chartSmoothExt α (chartAtlasPOU I M α)` has
compact support on the Euclidean ambient space. -/
theorem chartSmoothExt_chartAtlasPOU_hasCompactSupport (α : M) :
    HasCompactSupport
      (chartSmoothExt (I := I) (M := M) α
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  hasCompactSupport_chartSmoothExt_chartAtlasPOU (I := I) (M := M) α

/-- **Uniform iterated-derivative bound for the smooth POU multiplier.** For
every chart base point `α : M` and every finite order `m`, there exists a
non-negative constant `C_α,m` such that all iterated derivatives of orders
`j ≤ m` of `chartSmoothExt α (chartAtlasPOU I M α)` are bounded by `C_α,m`
everywhere on the Euclidean ambient space. -/
theorem exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU
    (α : M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (j : ℕ),
        j ≤ m →
        ‖iteratedFDeriv ℝ j
            (chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) y‖ ≤ C :=
  exists_uniform_iteratedFDeriv_bound_of_smooth_compactSupport
    (d := Module.finrank ℝ E)
    (chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α)
    (chartSmoothExt_chartAtlasPOU_hasCompactSupport (I := I) (M := M) α) m

/-- **Per-chart Leibniz multiplier constant.** For each chart base point
`α : M` and each regularity order `k`, there exists a positive constant
`K_α,k` such that for every function `u` on the Euclidean ambient space that
lies in `MemWkp (2 * k) 2` of the chart-α target, the `wkpNorm` of
`(chartSmoothExt α (chartAtlasPOU I M α)) · u` on the chart-α target is
bounded by `K_α,k` times the `wkpNorm` of `u` on the chart-α target. -/
theorem exists_per_chart_leibniz_multiplier_bound
    (α : M) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ},
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2 u
            (chartTargetEuclid (I := I) (M := M) α) →
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (fun y => chartSmoothExt (I := I) (M := M) α
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) y *
              u y)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2 u
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set η : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    chartSmoothExt (I := I) (M := M) α
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) with hη_def
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) η :=
    chartSmoothExt_chartAtlasPOU_contDiff (I := I) (M := M) α
  have hη_cpt : HasCompactSupport η :=
    chartSmoothExt_chartAtlasPOU_hasCompactSupport (I := I) (M := M) α
  obtain ⟨C, hC_nn, hC_bound⟩ :=
    exists_iteratedFDeriv_bound_chartSmoothExt_chartAtlasPOU
      (I := I) (M := M) α (2 * k)
  set Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hη_bound_on_Ω : ∀ j ≤ 2 * k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j η x‖ ≤ C :=
    fun j hj x _ => hC_bound x j hj
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    wkpNorm_smul_smooth_bounded_le (d := Module.finrank ℝ E) (2 * k)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (ENNReal.ofNat_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
      hΩ_open hη_smooth hC_nn hη_bound_on_Ω
  exact ⟨K, hK_pos, fun {u} hu => hK_bound hu⟩

/-- **Conditional per-chart-and-component Leibniz step.** With `MemWkp` of
the raw chart-pushed component supplied as a hypothesis, the per-chart
quantitative-Leibniz bound transfers term-by-term to the Sobolev-norm
inequality at the level of a single `(α, Idx, Jdx)` triple. -/
theorem wkpNorm_tensorChartComp_le_const_mul_wkpNorm_chartPushedRaw_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) (α : M) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (T : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
            (chartPushedRaw (I := I) (M := M) α
              (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
            (chartTargetEuclid (I := I) (M := M) α) →
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal K *
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (chartPushedRaw (I := I) (M := M) α
                (tensorChartComponentRaw (I := I) (M := M) g r s T α Idx Jdx))
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  obtain ⟨K, hK_pos, hK_bound⟩ :=
    exists_per_chart_leibniz_multiplier_bound (I := I) (M := M) α k
  refine ⟨K, hK_pos, ?_⟩
  intro T Idx Jdx hMem
  rw [tensorChartComp_eq_chartSmoothExt_mul_chartPushedRaw_raw
    (I := I) (M := M) g r s T α Idx Jdx]
  exact hK_bound hMem

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
