import DifferentialGeometry.Integral.Connection.RiemannianFiberNormSqLeChartAlphaSummandSum
import DifferentialGeometry.Integral.Measure.Family
import Mathlib.Topology.Order.Compact

/-!
# Uniform bound on the intrinsic Riemannian fiber norm of a smooth tensor section

For a closed Riemannian manifold `(M, g)` and a smooth compactly-supported
`(r, s)`-tensor section `S : SmoothCcTensor g r s`, the intrinsic Riemannian
fiber norm-squared `riemannianFiberNormSq g r s b (S.toSection b)` is bounded
above by a single nonnegative constant `K`, uniformly over all base points
`b : M`.

## Why this is the correct route

The intrinsic fiber norm `riemannianFiberNormSq` is a finite sum of squared
evaluations of the tensor on a `g`-orthonormal frame. A naive control via the
model-fibre operator norm `‖·‖` of the tensor times the ambient `E`-norm of the
`g`-orthonormal frame fails on multi-chart manifolds: the ambient `E`-norm of a
`g`-orthonormal frame (equivalently, the model operator norm of the chart
trivialisation) is genuinely *unbounded* on compact sets as soon as the manifold
needs more than one chart, because the tangent-bundle trivialisation jumps
between chart sources. The correct, chart-locality-free route bounds the intrinsic
fiber norm directly in terms of the *raw chart-frame scalar components* of the
section, which are smooth — hence continuous and bounded on the compact closed
support of each partition-of-unity weight.

## Strategy

On the closed support of the chart-atlas partition-of-unity weight at `α`:

1. `riemannianFiberNormSq_le_chartAlpha_summand_sum_on_pouTsupport` bounds the
   intrinsic fiber norm by a uniform constant times the chart-`α`-frame
   fiber-norm-squared summand sum (intrinsic forward-Gram Rayleigh route, no
   model norm).
2. `fiberNormSqSummand_chartAlpha_le_raw_components_sq` bounds each chart-`α`
   summand by a uniform constant times the sum of squared raw chart-`α`
   components `tensorChartComponentRaw`.
3. The raw chart components are smooth on the chart source
   (`tensorChartComponentRaw_contMDiffOn_chart_source`), hence continuous on the
   compact closed POU support (which is contained in the chart source); the
   continuous nonnegative sum of squares attains a finite supremum there.

Finally, on a compact manifold the partition of unity has finite nonempty
support `chartAtlasPOU_finset`; every base point lies in the support — hence the
closed support — of at least one weight in that finite set
(`SmoothPartitionOfUnity.exists_pos_of_mem`). Taking the maximum of the
per-`α` bounds over the finite set gives the global uniform constant `K`.

## Main results

* `exists_uniform_bound_sum_tensorChartComponentRaw_sq_on_pouTsupport` — on the
  closed POU support at `α`, the sum of squared raw chart-`α` components of a
  smooth section is bounded above by a nonnegative constant.
* `exists_bound_riemannianFiberNormSq_smoothCcTensor_on_pouTsupport` — the
  per-`α` uniform bound on `riemannianFiberNormSq` over the closed POU support.
* `exists_bound_riemannianFiberNormSq_smoothCcTensor` — the global uniform bound
  on a closed manifold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Integral
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The finite sum of squared raw chart-`α` scalar components of a smooth section
is continuous on the closed support of the chart-atlas partition-of-unity weight
at `α`. -/
lemma sum_tensorChartComponentRaw_sq_continuousOn_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_sub :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source := by
    intro b hb
    have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    rwa [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
      at hb_base
  refine ContinuousOn.mono ?_ h_sub
  refine continuousOn_finset_sum _ (fun Idx _ => ?_)
  refine continuousOn_finset_sum _ (fun Jdx _ => ?_)
  have h_raw : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    (tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx).continuousOn
  exact h_raw.pow 2

/-- **Uniform bound on the raw chart-component sum-of-squares over the closed POU
support.** For a smooth section `S : SmoothCcTensor g r s` and chart base point
`α`, the finite sum of squared raw chart-`α` scalar components is bounded above by
a nonnegative constant on the closed support of the chart-atlas partition-of-unity
weight at `α`. -/
lemma exists_uniform_bound_sum_tensorChartComponentRaw_sq_on_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2) ≤ B := by
  classical
  set K : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_def
  have hK_compact : IsCompact K := pouTsupport_isCompact (I := I) (M := M) α
  set f : M → ℝ := fun b =>
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b) ^ 2 with hf_def
  have hf_cont : ContinuousOn f K :=
    sum_tensorChartComponentRaw_sq_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S
  have hf_nonneg : ∀ b, 0 ≤ f b := by
    intro b
    refine Finset.sum_nonneg (fun Idx _ => ?_)
    refine Finset.sum_nonneg (fun Jdx _ => ?_)
    exact sq_nonneg _
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [hKe] at hb
    exact absurd hb (Set.notMem_empty b)
  · obtain ⟨b₀, hb₀_mem, hb₀_max⟩ := hK_compact.exists_isMaxOn hKne hf_cont
    refine ⟨f b₀, hf_nonneg b₀, ?_⟩
    intro b hb
    exact hb₀_max hb

/-- **Per-`α` uniform bound on `riemannianFiberNormSq` over the closed POU support.**
For a closed Riemannian manifold `(M, g)`, smooth section `S : SmoothCcTensor g r s`,
and chart base point `α`, the intrinsic Riemannian fiber norm-squared of `S.toSection b`
is bounded above by a single nonnegative constant for every point `b` in the closed
support of the chart-atlas partition-of-unity weight at `α`. -/
theorem exists_bound_riemannianFiberNormSq_smoothCcTensor_on_pouTsupport
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ∃ Kα : ℝ, 0 ≤ Kα ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤ Kα := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  obtain ⟨C₁, hC₁_nonneg, hC₁_bound⟩ :=
    riemannianFiberNormSq_le_chartAlpha_summand_sum_on_pouTsupport
      (I := I) (M := M) g r s α
  obtain ⟨C₂, hC₂_nonneg, hC₂_bound⟩ :=
    fiberNormSqSummand_chartAlpha_le_raw_components_sq
      (I := I) (M := M) g r s α
  obtain ⟨B, hB_nonneg, hB_bound⟩ :=
    exists_uniform_bound_sum_tensorChartComponentRaw_sq_on_pouTsupport
      (I := I) (M := M) g r s α S
  set Npair : ℝ := (n : ℝ) ^ r * (n : ℝ) ^ s with hNpair_def
  have hNpair_nonneg : 0 ≤ Npair := by
    rw [hNpair_def]
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg n) r) (pow_nonneg (Nat.cast_nonneg n) s)
  refine ⟨C₁ * (Npair * (C₂ * B)), ?_, ?_⟩
  · exact mul_nonneg hC₁_nonneg (mul_nonneg hNpair_nonneg (mul_nonneg hC₂_nonneg hB_nonneg))
  · intro b hb
    have hA := hC₁_bound S hb
    set rawSum : ℝ :=
      ∑ Idx' : Fin r → Fin n, ∑ Jdx' : Fin s → Fin n,
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx' Jdx' b) ^ 2
      with hrawSum_def
    have hsummand_sum_le :
        (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b) n
              (fun i : Fin n => chartBasisVecFiber (I := I) α i b) Idx Jdx) ≤
          Npair * (C₂ * rawSum) := by
      have hper : ∀ (Idx : Fin r → Fin n) (Jdx : Fin s → Fin n),
          fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b) n
              (fun i : Fin n => chartBasisVecFiber (I := I) α i b) Idx Jdx ≤
            C₂ * rawSum := by
        intro Idx Jdx
        exact hC₂_bound S hb Idx Jdx
      calc
        (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
            fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b) n
              (fun i : Fin n => chartBasisVecFiber (I := I) α i b) Idx Jdx)
            ≤ ∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n, (C₂ * rawSum) := by
              refine Finset.sum_le_sum (fun Idx _ => ?_)
              refine Finset.sum_le_sum (fun Jdx _ => ?_)
              exact hper Idx Jdx
        _ = Npair * (C₂ * rawSum) := by
              rw [Finset.sum_const]
              rw [Finset.sum_const]
              simp only [Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
                Fintype.card_fin]
              rw [hNpair_def]
              push_cast
              ring
    have hC : rawSum ≤ B := by
      rw [hrawSum_def]
      exact hB_bound hb
    calc
      riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b)
          ≤ C₁ *
              (∑ Idx : Fin r → Fin n, ∑ Jdx : Fin s → Fin n,
                fiberNormSqSummand (I := I) (M := M) g b r s (S.toSection b) n
                  (fun i : Fin n => chartBasisVecFiber (I := I) α i b) Idx Jdx) := hA
      _ ≤ C₁ * (Npair * (C₂ * rawSum)) :=
            mul_le_mul_of_nonneg_left hsummand_sum_le hC₁_nonneg
      _ ≤ C₁ * (Npair * (C₂ * B)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC₁_nonneg
            refine mul_le_mul_of_nonneg_left ?_ hNpair_nonneg
            exact mul_le_mul_of_nonneg_left hC hC₂_nonneg

/-- **Uniform bound on the intrinsic Riemannian fiber norm of a smooth tensor
section.** Let `g` be a smooth Riemannian metric on a closed manifold `M`, and let
`S : SmoothCcTensor g r s` be a smooth compactly-supported `(r, s)`-tensor section.
Then there is a single nonnegative constant `K` such that for every `b : M`,

```
riemannianFiberNormSq g r s b (S.toSection b) ≤ K.
```

The bound is stated entirely in the intrinsic Riemannian fiber norm; the proof uses
only chart-locality-free ingredients (the forward-Gram Rayleigh route + smoothness of
raw chart components on the compact partition-of-unity supports), never the
model-fibre operator norm of the chart trivialisation (which is genuinely unbounded
on multi-chart manifolds). -/
theorem exists_bound_riemannianFiberNormSq_smoothCcTensor
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : M,
      riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤ K := by
  classical
  set Kα : M → ℝ := fun α =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor_on_pouTsupport
      (I := I) (M := M) g r s α S).choose with hKα_def
  have hKα_nonneg : ∀ α : M, 0 ≤ Kα α := fun α =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor_on_pouTsupport
      (I := I) (M := M) g r s α S).choose_spec.1
  have hKα_bound : ∀ α : M, ∀ {b : M},
      b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      riemannianFiberNormSq (I := I) (M := M) g r s b (S.toSection b) ≤ Kα α := fun α =>
    (exists_bound_riemannianFiberNormSq_smoothCcTensor_on_pouTsupport
      (I := I) (M := M) g r s α S).choose_spec.2
  set K : ℝ := ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), Kα α with hK_def
  have hK_nonneg : 0 ≤ K := by
    rw [hK_def]
    exact Finset.sum_nonneg (fun α _ => hKα_nonneg α)
  refine ⟨K, hK_nonneg, ?_⟩
  intro b
  obtain ⟨α, hα_pos⟩ :=
    (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ b)
  have hα_finset : α ∈ chartAtlasPOU_finset (I := I) (M := M) := by
    rw [chartAtlasPOU_finset_mem]
    exact ⟨b, Function.mem_support.mpr (ne_of_gt hα_pos)⟩
  have hb_tsupport : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) := by
    apply subset_tsupport
    exact Function.mem_support.mpr (ne_of_gt hα_pos)
  refine le_trans (hKα_bound α hb_tsupport) ?_
  rw [hK_def]
  exact Finset.single_le_sum (fun β _ => hKα_nonneg β) hα_finset

end Connection
end Integral
end DifferentialGeometry

end
