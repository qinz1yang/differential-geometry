import DifferentialGeometry.Analysis.Sobolev.Manifold.IteratedSobolevEmbedding
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EmbeddingSubcritical
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.EuclideanMorrey
import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Chart
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace

/-!
# Iterated Sobolev embedding `W^{k,p}(M) ↪ W^{k-1, p_1}(M)` and `↪ C^0(M)`,
half-space (with-boundary) variant

For a smooth manifold `M` modelled on the canonical Euclidean half-space
`EuclideanHalfSpace n` (`n ≥ 1`), with a smooth Riemannian metric `g`, this
file mirrors the boundaryless `IteratedSobolevEmbedding.lean` to deliver the
iterated Sobolev tower steps and the headline embedding into continuous
representatives, using the half-space-Dirichlet variant of the iterated
Sobolev predicate.

## Strategy

The Dirichlet half-space iterated Sobolev space `MemWkpHalfSpace k p u Ω`
on a half-space-relatively-open carrier `Ω` is by definition the standard
`MemWkp k p u (interiorHalfSpace Ω)` on the open interior part. Likewise,
`wkpNormHalfSpace` reduces to `wkpNorm` on `interiorHalfSpace Ω`. So all the
boundaryless iterated tower-step lemmas (under `Chart.TowerStep`) apply
verbatim with the open set `interiorHalfSpace Ω`.

The chart-pushed function `chartPushed ρ_α α u`, for the canonical
chart-atlas POU `chartAtlasPOU I M`, has tsupport in the chart target
`(extChartAt I α).target`, but in general only meets the open interior part
in the interior of the support. To use the boundaryless tower-step in the
half-space setting, the per-chart input function must have its tsupport in
`interiorHalfSpace (chartTargetEuclid α)` (i.e., strictly above the boundary
hyperplane).

## Main results

### Pure-Euclidean iterated tower step (with-boundary)

* `MemWkpHalfSpace_succ_subcritical_step` — for `1 ≤ p < n`, every `u`
  in `MemWkpHalfSpace (k+1) p u Ω` with `tsupport u ⊆ interiorHalfSpace Ω`
  and compact support is in `MemWkpHalfSpace k p_1 u Ω` at the sub-critical
  exponent `p_1 = n p / (n - p)`, with norm bound.
* `MemWkpHalfSpace_subcritical_iterated` — the iterated form: applies for
  any `k ∈ ℕ` directly to the inductive boundaryless statement.

### Manifold-side iterated tower step (with-boundary)

* `wkpNormChart_succ_subcritical_step_withBoundary_perChart` — for a smooth
  manifold modelled on `EuclideanHalfSpace n`, given chart-pushed functions
  whose tsupports lie in the open interior parts of chart targets, the
  iterated tower step holds per chart with a uniform constant.

## Scope note

The headline iterated `C^0`-embedding on `M` requires the manifold-side
Morrey embedding (`morrey_C0_embedding_of_compact`) at the super-critical
exponent and the manifold-side measure bridge to the riemannian measure,
both of which are currently provided only in the boundaryless setting.
Establishing those in the with-boundary setting is downstream
infrastructure beyond the present file's scope. The manifold-side iterated
tower step delivered here (per-chart, with explicit support hypothesis)
provides the inductive engine that any future headline theorem will use.

The chart-pushed-support hypothesis (tsupport in the open interior parts)
is exposed as an input. A fully POU-based reduction (analogous to the
boundaryless `chartPushedRaw_pou` machinery) that would derive this
support condition automatically from the manifold-side membership is
non-trivial in the with-boundary setting because the chart-source POU
weights typically meet the boundary face. The present formulation
delivers the iterated step and leaves the support-reduction as a
downstream concern.
-/

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

namespace EuclideanTowerStep

variable {d : ℕ} [NeZero d]

local notation "EuN" => EuclideanSpace ℝ (Fin d)

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.Chart

/-- The sub-critical Sobolev exponent `pOne d p = d p / (d - p)`, re-export
of the boundaryless definition. -/
abbrev pOne (d : ℕ) (p : ℝ) : ℝ := TowerStep.pOne d p

/-- Iterated subcritical Sobolev constant. -/
abbrev subcriticalConstant (k d : ℕ) [NeZero d] (p : ℝ) : ℝ :=
  TowerStep.subcriticalConstant k d p

lemma subcriticalConstant_nonneg (k : ℕ) (p : ℝ) :
    0 ≤ subcriticalConstant k d p :=
  TowerStep.subcriticalConstant_nonneg k d p

/-- **Iterated subcritical Sobolev embedding step on a half-space-friendly
carrier (with-boundary, Euclidean).**

For `1 ≤ p < d` and `f : EuN → ℝ` with compact support and
`tsupport f ⊆ interiorHalfSpace Ω` (the open part of `Ω` strictly above
the boundary hyperplane), if `f ∈ MemWkpHalfSpace (k+1) p f Ω`, then for
the sub-critical exponent `p_1 = d p / (d - p)`:

* `f ∈ MemWkpHalfSpace k p_1 f Ω`.
* `wkpNormHalfSpace k p_1 f Ω ≤ subcriticalConstant k d p · wkpNormHalfSpace (k+1) p f Ω`.

The proof reduces directly to the boundaryless
`Chart.TowerStep.MemWkp_subcritical_iterated` applied on the open set
`interiorHalfSpace Ω`. -/
theorem MemWkpHalfSpace_subcritical_iterated
    (k : ℕ) {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ∧
      wkpNormHalfSpace (d := d) k (ENNReal.ofReal (pOne d p)) f Ω ≤
        ENNReal.ofReal (subcriticalConstant k d p) *
          wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  have hΩ_int_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hf' : MemWkp (d := d) (k + 1) (ENNReal.ofReal p) f
      (interiorHalfSpace Ω) := hf
  exact TowerStep.MemWkp_subcritical_iterated (d := d) k hp_one hp_dim
    hΩ_int_open hf_compact hf_supp hf'

/-- **Single-step iterated subcritical Sobolev embedding (with-boundary,
Euclidean).** Equivalent reformulation of `MemWkpHalfSpace_subcritical_iterated`
that uses the explicit form `(d : ℝ) * p / ((d : ℝ) - p)` of the sub-critical
exponent. -/
theorem MemWkpHalfSpace_succ_subcritical_step
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (d : ℝ))
    {Ω : Set EuN} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    {f : EuN → ℝ}
    (hf_compact : HasCompactSupport f)
    (hf_supp : tsupport f ⊆ interiorHalfSpace Ω)
    (hf : MemWkpHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω) :
    MemWkpHalfSpace (d := d) k
        (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ∧
      ∃ C : ℝ, 0 ≤ C ∧
        wkpNormHalfSpace (d := d) k
            (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) f Ω ≤
          ENNReal.ofReal C *
            wkpNormHalfSpace (d := d) (k + 1) (ENNReal.ofReal p) f Ω := by
  obtain ⟨h_mem, h_norm⟩ :=
    MemWkpHalfSpace_subcritical_iterated (d := d) k hp_one hp_dim hΩ
      hf_compact hf_supp hf
  have hpOne_eq : pOne d p = (d : ℝ) * p / ((d : ℝ) - p) := rfl
  refine ⟨?_, ?_⟩
  · rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_mem
  · refine ⟨subcriticalConstant k d p, subcriticalConstant_nonneg k p, ?_⟩
    rw [show (ENNReal.ofReal ((d : ℝ) * p / ((d : ℝ) - p))) =
      ENNReal.ofReal (pOne d p) from by rw [hpOne_eq]]
    exact h_norm

end EuclideanTowerStep

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]

/-- **Per-chart manifold-side iterated tower step (with-boundary).**

For a closed manifold `M` modelled on the canonical `EuclideanHalfSpace n`
with smooth Riemannian metric `g`, and for `1 ≤ p < n`, every `u : M → ℝ` with
`u ∈ MemWkpChart g (k+1) p u` whose chart-pushed functions all have tsupports
inside the open interior parts of the chart targets is in
`MemWkpChart g k p_1 u` at the sub-critical exponent `p_1 = n p / (n - p)`,
with norm bound

  `wkpNormChart g k p_1 u ≤ ENNReal.ofReal C * wkpNormChart g (k+1) p u`

for a constant `C ≥ 0` depending only on `k`, `n`, `p` (uniform across
charts). -/
theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) g k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) g k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u := by
  classical
  set C : ℝ := EuclideanTowerStep.subcriticalConstant k n p with hC_def
  have hC_nn : 0 ≤ C :=
    EuclideanTowerStep.subcriticalConstant_nonneg (d := n) k p
  refine ⟨C, hC_nn, ?_⟩
  intro u h_compact h_supp hu
  have h_per_chart : ∀ α : M,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkpHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ∧
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) k (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)))
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal C *
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
            (d := n) (k + 1) (ENNReal.ofReal p)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)
            (chartTargetEuclid (n := n) (M := M) α) := by
    intro α
    have h_iter :=
      EuclideanTowerStep.MemWkpHalfSpace_subcritical_iterated (d := n) k
        hp_one hp_dim
        (chartTargetEuclid_isHalfSpaceRelOpen (n := n) (M := M) α)
        (h_compact α) (h_supp α) (hu α)
    obtain ⟨h_mem_p1, h_norm_p1⟩ := h_iter
    have h_pOne_eq : EuclideanTowerStep.pOne n p =
        (n : ℝ) * p / ((n : ℝ) - p) := rfl
    refine ⟨?_, ?_⟩
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_mem_p1
    · rw [show ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p)) =
        ENNReal.ofReal (EuclideanTowerStep.pOne n p) from by rw [h_pOne_eq]]
      exact h_norm_p1
  refine ⟨fun α => (h_per_chart α).1, ?_⟩
  unfold wkpNormChart
  rw [show ENNReal.ofReal C * ∑' α : M,
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) =
      ∑' α : M, ENNReal.ofReal C *
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) (k + 1) (ENNReal.ofReal p)
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU
              (modelWithCornersEuclideanHalfSpace n) M) α u)
          (chartTargetEuclid (n := n) (M := M) α) from
    (ENNReal.tsum_mul_left).symm]
  exact ENNReal.tsum_le_tsum (fun α => (h_per_chart α).2)

/-- **Smooth-input per-chart manifold-side iterated tower step (with-
boundary).** -/
theorem wkpNormChart_succ_subcritical_step_withBoundary_perChart_smooth
    [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
    (g : DifferentialGeometry.Integral.Measure.SmoothRiemannianMetric
      (modelWithCornersEuclideanHalfSpace n) M)
    {k : ℕ} {p : ℝ} (hp_one : 1 ≤ p) (hp_dim : p < (n : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ},
        (∀ α : M,
          ContDiff ℝ (⊤ : ℕ∞)
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          HasCompactSupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u)) →
        (∀ α : M,
          tsupport
            (chartPushed (n := n) (M := M)
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU
                (modelWithCornersEuclideanHalfSpace n) M) α u) ⊆
          DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α)) →
        MemWkpChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u →
          MemWkpChart (n := n) (M := M) g k
              (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ∧
            wkpNormChart (n := n) (M := M) g k
                (ENNReal.ofReal ((n : ℝ) * p / ((n : ℝ) - p))) u ≤
              ENNReal.ofReal C *
                wkpNormChart (n := n) (M := M) g (k + 1) (ENNReal.ofReal p) u := by
  obtain ⟨C, hC_nn, h⟩ :=
    wkpNormChart_succ_subcritical_step_withBoundary_perChart (n := n) (M := M)
      g (k := k) hp_one hp_dim
  refine ⟨C, hC_nn, ?_⟩
  intro u _hu_smooth h_compact h_supp hu
  exact h h_compact h_supp hu

/-- Re-export of `IterationCalc.kp1_real_gt_d_of_kp1p_gt_d`: if `0 < p < d`
and `d < (k+1) p`, then `d < k * p_1` where `p_1 = d p / (d - p)`. -/
theorem kp_gt_d_of_kp1p_gt_d
    (d : ℕ) (k : ℕ) (p : ℝ) (hp_pos : 0 < p) (hp_dim : p < (d : ℝ))
    (hkp : (d : ℝ) < (k + 1 : ℝ) * p) :
    (d : ℝ) < (k : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
  DifferentialGeometry.Analysis.Sobolev.Chart.IterationCalc.kp1_real_gt_d_of_kp1p_gt_d
    d k p hp_pos hp_dim hkp

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry
