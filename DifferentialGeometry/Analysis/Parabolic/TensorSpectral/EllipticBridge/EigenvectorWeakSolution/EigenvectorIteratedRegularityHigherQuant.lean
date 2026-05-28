import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedRegularityHigher
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedNirenbergWeakenedQuant
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevQuant

/-!
# Quantitative order-raiser for the eigenvector chart-component iterated regularity

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the eigenvector
chart component `eigenvectorChartComponentFun` and its recursive `m`-fold mixed
weak partials `eigenvectorChartIteratedPartial` carry the iterated Sobolev
structure of the resolvent eigenvector.

The structural module `EigenvectorIteratedRegularityHigher` ships the
**qualitative** order-assembly headline
`eigenvectorChartComponent_memWkp_m_plus_two_of_iterated`: from chart-`H²` of
every `m`-fold mixed weak partial and chart-`H¹` of every `j`-fold mixed weak
partial for `j ≤ m`, the eigenvector chart component lies in chart-`H^{m+2}`.

This module supplies the **quantitative** counterpart — the
`wkpNorm`-tracking order-raiser. Every membership conclusion is accompanied by
an explicit, finite `wkpNorm`-bound whose right-hand side is built from the
per-tuple `W^{1,2}`- and `W^{2,2}`-norms of the iterated mixed weak partials,
with an existentially quantified geometric constant.

## Main results

* `eigenvectorChartIteratedPartial_wkpNorm_succ_le` — the order-`(K+2)`
  decomposition step: the order-`(K+2)` iterated Sobolev norm of the `j`-fold
  mixed weak partial is bounded by its `W^{1,2}`-norm plus the sum, over the
  coordinate axes, of the order-`(K+1)` norms of the `(j+1)`-fold mixed weak
  partials along `Fin.snoc dirs a`. This is the quantitative twin of the
  per-direction-count engine
  `eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices`.
* `eigenvectorChartIteratedPartial_wkpNorm_one_two_le` — the quantitative
  `W^{1,2}` bridge: from chart-`H^{m+1}` of the eigenvector chart component,
  every `m`-fold mixed weak partial lies in `W^{1,2}` of the chart target with
  its `W^{1,2}`-norm bounded by the chart-`H^{m+1}`-norm of the chart component.
  This is the quantitative twin of
  `eigenvectorChartIteratedPartial_memWkp_of_memWkp` at `k = 1`.
* `eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le` — the
  quantitative order-raiser: from chart-`H¹` of every `j`-fold mixed weak
  partial (`j ≤ m`) and chart-`H²` of every `m`-fold mixed weak partial, the
  eigenvector chart component lies in chart-`H^{m+2}` *and* its chart-`H^{m+2}`-
  norm is bounded by an explicit geometric constant times the aggregate of the
  per-tuple `W^{1,2}`- and `W^{2,2}`-norms of the iterated mixed weak partials.
  This is the quantitative twin of
  `eigenvectorChartComponent_memWkp_m_plus_two_of_iterated`.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## The quantitative order-`(K+2)` decomposition step

The recursive `eigenvectorChartIteratedPartial` factors the iterated `MemWkp`
predicate: the `(j + 1)`-fold mixed weak partial along `Fin.snoc dirs a` is, by
the recursive definition, the chosen weak `a`-partial of the `j`-fold mixed
weak partial along `dirs`. The campaign-facing `wkpNorm`-recursion
`wkpNorm_succ_le_wkpNorm_add_sum_partial` then bounds the order-`(K+2)` norm of
the `j`-fold mixed weak partial by its `W^{1,2}`-norm plus the sum, over the
coordinate axes, of the order-`(K+1)` norms of the chosen weak partials — which
are exactly the `(j+1)`-fold mixed weak partials along `Fin.snoc dirs a`. -/

omit [CompleteSpace E] in
/-- **Quantitative order-`(K+2)` decomposition step for the eigenvector iterated
mixed weak partial.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, an order `K : ℕ`, a
direction count `j : ℕ`, and a `j`-direction multi-index `dirs`, given:

* `W^{1,2}`-regularity of the `j`-fold mixed weak partial along `dirs`;
* `W^{K+1,2}`-regularity of every `(j + 1)`-fold mixed weak partial along
  `Fin.snoc dirs a`;

the `j`-fold mixed weak partial along `dirs` lies in `W^{K+2,2}` of the chart
target, and its order-`(K+2)` iterated Sobolev norm is bounded by its
`W^{1,2}`-norm plus the sum, over the coordinate axes `a`, of the order-`(K+1)`
norms of the `(j + 1)`-fold mixed weak partials along `Fin.snoc dirs a`.

This is the quantitative twin of the per-direction-count engine
`eigenvectorIteratedPartial_memWkp_of_chartH_at_all_indices`: the
`wkpNorm`-recursion `wkpNorm_succ_le_wkpNorm_add_sum_partial` combined with the
`Fin.snoc` identity expressing the chosen weak partial of the `j`-fold mixed
weak partial as the `(j + 1)`-fold mixed weak partial. -/
theorem eigenvectorChartIteratedPartial_wkpNorm_succ_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K j : ℕ)
    (dirs : Fin j → Fin (Module.finrank ℝ E))
    (h_w1p :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_succ :
      ∀ a : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 2) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ j dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        + ∑ a : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (K + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  -- The `Fin.snoc` identity: the chosen weak `a`-partial of the `j`-fold mixed
  -- weak partial along `dirs` is the `(j + 1)`-fold mixed weak partial along
  -- `Fin.snoc dirs a`.
  have h_succ_eq : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 a
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j dirs) Ω := by
    intro a
    rw [eigenvectorChartIteratedPartial_succ]
    have h_last : (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) (Fin.last j) = a :=
      Fin.snoc_last _ _
    have h_init : Fin.init (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) = dirs := Fin.init_snoc _ _
    rw [h_last, h_init]
  -- First conjunct: the membership, via the qualitative per-direction-count
  -- engine.  Its `W^{1,2}` hypothesis is `h_w1p` at the single index `dirs`;
  -- its `W^{K+1,2}` hypothesis is `h_succ`.
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
    refine ⟨?_, fun a => ?_⟩
    · rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_w1p
      exact h_w1p
    · have h_next := h_succ a
      rw [h_succ_eq a] at h_next
      exact h_next
  refine ⟨h_mem, ?_⟩
  -- Second conjunct: the `wkpNorm`-bound.  The order-`(K+2)` decomposition
  -- `wkpNorm_succ_le` expresses `wkpNorm (K+2) 2` of the `j`-fold mixed weak
  -- partial as `eLpNorm` of it plus the sum, over coordinate axes, of
  -- `wkpNorm (K+1) 2` of the chosen weak partials.  Bounding `eLpNorm` by
  -- `wkpNorm 1 2` and rewriting each chosen weak partial as the `(j+1)`-fold
  -- mixed weak partial yields the stated bound.
  have h_rec := wkpNorm_succ_le (d := Module.finrank ℝ E)
    (K + 1) 2 Ω
    (eigenvectorChartIteratedPartial (I := I) (M := M)
      g r s h_atlas i α P₀ j dirs)
  -- `wkpNorm ((K+1)+1) 2` is identical to `wkpNorm (K + 2) 2`; align indices.
  have h_idx : K + 1 + 1 = K + 2 := by ring
  rw [h_idx] at h_rec
  -- Rewrite the chosen-weak-partial summand via the `Fin.snoc` identity.
  refine h_rec.trans (add_le_add ?_ ?_)
  · -- `eLpNorm u 2 ≤ wkpNorm 1 2 u`.
    exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 1 2 Ω
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ j dirs)
  · -- Each chosen-weak-partial summand equals the `(j+1)`-fold mixed weak
    -- partial summand by the `Fin.snoc` identity `h_succ_eq`.
    refine Finset.sum_le_sum (fun a _ => ?_)
    rw [h_succ_eq a]

/-! ## The quantitative `W^{1,2}` bridge from the parent chart component

The polymorphic membership bridge `eigenvectorChartIteratedPartial_memWkp_of_memWkp`
deduces chart-`H^k` of every `m`-fold mixed weak partial from chart-`H^{k+m}` of
the chart component, by peeling one chosen weak partial per recursion step. The
`wkpNorm`-monotone chosen-weak-partial bound `wkpNorm_chosenWeakPartial_le`
makes this quantitative at `k = 1`: each peel drops one Sobolev order while not
increasing the iterated Sobolev norm, so the `W^{1,2}`-norm of every `m`-fold
mixed weak partial is bounded by the chart-`H^{m+1}`-norm of the chart
component. -/

omit [CompleteSpace E] in
/-- **Polymorphic quantitative regularity bridge for the eigenvector iterated
mixed weak partial.**

From chart-`H^{k+m}` of the eigenvector chart component on the chart target,
every `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s h_atlas
i α P₀ m dirs` lies in chart-`H^k` of the chart target, and its order-`k`
iterated Sobolev norm is bounded by the order-`(k + m)` iterated Sobolev norm of
the chart component.

This is the quantitative twin of
`eigenvectorChartIteratedPartial_memWkp_of_memWkp`: the proof is induction on
`m`, repeatedly applying the `wkpNorm`-monotone chosen-weak-partial bound
`wkpNorm_chosenWeakPartial_le` (each peel drops one Sobolev order and does not
increase the norm). -/
theorem eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ m dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (k + m) 2
              (eigenvectorChartComponentFun (I := I) (M := M)
                g r s h_atlas i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      -- `k + 0 = k`, and the `m = 0` mixed weak partial is the chart component.
      intro k h_parent _dirs
      refine ⟨?_, ?_⟩
      · simpa [eigenvectorChartIteratedPartial_zero] using h_parent
      · rw [eigenvectorChartIteratedPartial_zero, Nat.add_zero]
  | succ m ih =>
      intro k h_parent dirs
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      -- Rewrite `k + (m + 1)` as `(k + 1) + m` on the parent hypothesis.
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      -- Inductive hypothesis with one fewer derivative on the level-`m` partial.
      obtain ⟨h_inner_mem, h_inner_norm⟩ :=
        ih (k + 1) h_parent' (Fin.init dirs)
      -- The level-`(m + 1)` mixed weak partial along `dirs` is the chosen weak
      -- `dirs (Fin.last m)`-partial of the level-`m` partial along `Fin.init dirs`.
      have h_unfold :
          eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) dirs =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m (Fin.init dirs)) Ω :=
        eigenvectorChartIteratedPartial_succ
          g r s h_atlas i α P₀ m dirs
      refine ⟨?_, ?_⟩
      · -- Membership: peel one chosen weak partial.
        rw [h_unfold]
        exact h_inner_mem.chosenWeakPartial_mem (dirs (Fin.last m))
      · -- Norm: the chosen weak partial drops one order and does not increase
        -- the norm; chain with the inductive norm bound.
        rw [h_unfold]
        have h_peel := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          k (p := 2) hΩ_open
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init dirs)) (dirs (Fin.last m))
        -- `h_peel : wkpNorm k 2 (chosenWeakPartial' …) ≤ wkpNorm (k+1) 2 (…)`.
        refine h_peel.trans ?_
        -- `h_inner_norm : wkpNorm (k+1) 2 (level-m partial) ≤ wkpNorm ((k+1)+m) 2 …`.
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq] at h_inner_norm
        exact h_inner_norm

omit [CompleteSpace E] in
/-- **Quantitative `W^{1,2}` bridge for the eigenvector iterated mixed weak
partial.**

From chart-`H^{m+1}` of the eigenvector chart component on the chart target,
every `m`-fold mixed weak partial `eigenvectorChartIteratedPartial g r s h_atlas
i α P₀ m dirs` lies in `W^{1,2}` of the chart target, and its `W^{1,2}`-norm is
bounded by the chart-`H^{m+1}`-norm of the chart component.

This is the quantitative twin of `eigenvectorChartIteratedPartial_memWkp_of_memWkp`
at `k = 1`: it is the campaign-facing `W^{1,2}` bridge consumed at each gap step
of the quantitative order-raiser. -/
theorem eigenvectorChartIteratedPartial_wkpNorm_one_two_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) := by
  -- Apply the polymorphic quantitative bridge with `k = 1`; reindex `1 + m`.
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  obtain ⟨h_mem, h_norm⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp
      (I := I) (M := M) g r s h_atlas i α P₀ m 1 h_parent' dirs
  refine ⟨h_mem, ?_⟩
  -- The bound is in terms of `wkpNorm (1 + m) 2`; reindex to `wkpNorm (m + 1) 2`.
  have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
  rw [h_eq] at h_norm
  exact h_norm

/-! ## The aggregate right-hand side of the quantitative order-raiser

The quantitative order-raiser bounds the chart-`H^{m+2}`-norm of the eigenvector
chart component by a geometric constant times a single finite aggregate. The
aggregate collects, with all summands nonnegative:

* `eigenvectorIteratedW1Aggregate` — the sum, over every direction count
  `j ≤ m` and every `j`-direction multi-index, of the `W^{1,2}`-norm of the
  `j`-fold mixed weak partial;
* `eigenvectorIteratedW2Aggregate` — the sum, over every `m`-direction
  multi-index, of the `W^{2,2}`-norm of the `m`-fold mixed weak partial.

Both are finite (each summand is the `wkpNorm` of a `W^{k,2}` function, hence
`< ⊤`; the index sets `Finset.range (m + 1)` and `Finset.univ` are finite). -/

/-- The aggregate of the `W^{1,2}`-norms of every `j`-fold mixed weak partial,
over every direction count `j ≤ m` and every `j`-direction multi-index. -/
def eigenvectorIteratedW1Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1),
    ∑ idx : Fin j → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α)

/-- The aggregate of the `W^{2,2}`-norms of every `m`-fold mixed weak partial,
over every `m`-direction multi-index. -/
def eigenvectorIteratedW2Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ idx : Fin m → Fin (Module.finrank ℝ E),
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ m idx)
      (chartTargetEuclid (I := I) (M := M) α)

omit [CompleteSpace E] in
/-- A single `W^{1,2}`-norm of a `j`-fold mixed weak partial (`j ≤ m`) is bounded
by the `W^{1,2}` aggregate. -/
private lemma wkpNorm_one_le_eigenvectorIteratedW1Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m j : ℕ} (hj : j ≤ m)
    (dirs : Fin j → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW1Aggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m := by
  classical
  unfold eigenvectorIteratedW1Aggregate
  -- The single term is the `idx = dirs` summand of the `j`-th inner sum, and
  -- the `j`-th inner sum is one summand of the outer sum; all summands `≥ 0`.
  have hj_mem : j ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j' => ∑ idx : Fin j' → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j' idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.range (m + 1)) (fun _ _ => zero_le _) hj_mem)
  exact Finset.single_le_sum
    (f := fun idx : Fin j → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.univ) (fun _ _ => zero_le _) (Finset.mem_univ dirs)

omit [CompleteSpace E] in
/-- A single `W^{2,2}`-norm of an `m`-fold mixed weak partial is bounded by the
`W^{2,2}` aggregate. -/
private lemma wkpNorm_two_le_eigenvectorIteratedW2Aggregate
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW2Aggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m := by
  classical
  unfold eigenvectorIteratedW2Aggregate
  exact Finset.single_le_sum
    (f := fun idx : Fin m → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun _ _ => zero_le _) (Finset.mem_univ dirs)

/-! ## The quantitative order-raiser

The qualitative order-assembly
`eigenvectorChartComponent_memWkp_m_plus_two_of_iterated` proves chart-`H^{m+2}`
of the chart component by a gap-induction: for every `gap` and every direction
count `j` with `j + gap = m`, every `j`-fold mixed weak partial lies in
chart-`H^{gap+2}`. The quantitative order-raiser threads a `wkpNorm`-bound
through that same gap-induction.

At each gap step the decomposition lemma
`eigenvectorChartIteratedPartial_wkpNorm_succ_le` bounds the order-`(gap+2)`
norm of a `j`-fold mixed weak partial by its `W^{1,2}`-norm plus the sum, over
the coordinate axes, of the order-`(gap+1)` norms of the `(j+1)`-fold mixed
weak partials. Bounding the `W^{1,2}`-norm by the `W^{1,2}` aggregate and the
order-`(gap+1)` norms by the inductive bound multiplies the geometric constant
by `(n + 1)` per gap step. The aggregate right-hand side stays fixed throughout;
the constant `(n + 1)^m` absorbs the per-gap accumulation. -/

omit [CompleteSpace E] in
/-- **Gap-induction engine for the quantitative order-raiser.**

For every `gap`, every direction count `j` with `j + gap = m`, and every
`j`-direction multi-index `dirs`, the `j`-fold mixed weak partial lies in
chart-`H^{gap+2}` and its order-`(gap+2)` iterated Sobolev norm is bounded by
`(n + 1)^gap` times the sum of the `W^{1,2}` aggregate and the `W^{2,2}`
aggregate, where `n := Module.finrank ℝ E`.

The proof is induction on `gap`:
* at `gap = 0` (`j = m`) the bound is the single `W^{2,2}`-norm, `≤` the
  `W^{2,2}` aggregate, `≤ 1 ·` the aggregate sum;
* at `gap + 1` the decomposition lemma
  `eigenvectorChartIteratedPartial_wkpNorm_succ_le` bounds the order-`(gap+2)`
  norm by the `W^{1,2}`-norm (`≤` the `W^{1,2}` aggregate, hence `≤` the
  aggregate sum) plus `n` copies of the inductive bound, giving a factor
  `(n + 1)`. -/
private theorem eigenvectorIteratedPartial_wkpNorm_gapInduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ (gap j : ℕ), j + gap = m →
      ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (gap + 2) 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
              (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m
                + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m) := by
  classical
  intro gap
  induction gap with
  | zero =>
      intro j hj dirs
      -- `j + 0 = m`, so `j = m`.
      subst hj
      simp only [Nat.add_zero] at *
      refine ⟨h_top_memWkp_two dirs, ?_⟩
      -- `wkpNorm 2 2 (m-fold partial) ≤ W2-aggregate ≤ W1 + W2 ≤ 1 · (W1 + W2)`.
      have h_single :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ eigenvectorIteratedW2Aggregate (I := I) (M := M)
                g r s h_atlas i α P₀ j :=
        wkpNorm_two_le_eigenvectorIteratedW2Aggregate
          (I := I) (M := M) g r s h_atlas i α P₀ dirs
      refine h_single.trans ?_
      rw [pow_zero, one_mul]
      exact le_add_self
  | succ gap ih =>
      intro j hj dirs
      -- `j + (gap + 1) = m`, so `j ≤ m` and `j + 1 ≤ m`.
      have hj_le : j ≤ m := by omega
      have hj1_eq : (j + 1) + gap = m := by omega
      -- The `W^{1,2}` hypothesis at the single index `dirs`.
      have h_w1p_dirs :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le dirs
      -- The inductive hypothesis at gap `gap`, count `j + 1`, every snoc index.
      have h_ih_snoc : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α)
          ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 2) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
                (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                    g r s h_atlas i α P₀ m
                  + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                    g r s h_atlas i α P₀ m) :=
        fun a => ih (j + 1) hj1_eq (Fin.snoc dirs a)
      -- The `W^{gap+1,2}` hypothesis: every `(j+1)`-fold snoc partial.
      have h_succ_mem : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 1 + 1) 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro a
        have h := (h_ih_snoc a).1
        -- `(gap + 1) + 1 = gap + 2`.
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      -- The decomposition lemma at order `K := gap + 1`.
      obtain ⟨h_mem, h_norm_bound⟩ :=
        eigenvectorChartIteratedPartial_wkpNorm_succ_le
          (I := I) (M := M) g r s h_atlas i α P₀ (gap + 1) j dirs
          h_w1p_dirs h_succ_mem
      -- `(gap + 1) + 2 = (gap + 1 + 1) + 1`; align the membership conclusion.
      refine ⟨h_mem, ?_⟩
      -- Bound the `W^{1,2}` term by the `W^{1,2}` aggregate, hence by the sum.
      set W1 : ℝ≥0∞ :=
        eigenvectorIteratedW1Aggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m with hW1_def
      set W2 : ℝ≥0∞ :=
        eigenvectorIteratedW2Aggregate (I := I) (M := M)
          g r s h_atlas i α P₀ m with hW2_def
      have h_w1_term :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        have h_single : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial (I := I) (M := M)
              g r s h_atlas i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) ≤ W1 :=
          wkpNorm_one_le_eigenvectorIteratedW1Aggregate
            (I := I) (M := M) g r s h_atlas i α P₀ hj_le dirs
        -- `W1 ≤ W1 + W2 ≤ (n+1)^gap · (W1 + W2)` since `1 ≤ (n+1)^gap`.
        refine h_single.trans (le_trans (le_self_add (a := W1) (b := W2)) ?_)
        refine le_mul_of_one_le_left (zero_le _) ?_
        exact one_le_pow₀ (le_add_of_nonneg_left (zero_le _))
      -- Each snoc-partial term is bounded by the inductive bound.
      have h_snoc_term : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 1 + 1) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        intro a
        have h := (h_ih_snoc a).2
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      -- Assemble: `wkpNorm (gap+1+2) 2 ≤ W1-term + ∑_a snoc-term`.
      -- `(gap + 1) + 2` matches `gap + 1 + 1 + 1 = gap + 3`; both reduce to the
      -- same `Nat`.  The decomposition lemma's conclusion is at order
      -- `(gap + 1) + 2`; the `wkpNorm`-summand index is `(gap + 1) + 1`.
      have h_chain :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 1 + 2) 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2)
              + ∑ _a : Fin (Module.finrank ℝ E),
                  ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        refine h_norm_bound.trans (add_le_add h_w1_term ?_)
        exact Finset.sum_le_sum (fun a _ => h_snoc_term a)
      -- The constant sum `∑_a c = n · c`; combine `c + n · c = (n + 1) · c`.
      refine h_chain.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      -- Goal: `(n+1)^gap·(W1+W2) + n · ((n+1)^gap·(W1+W2))`
      --       = (n+1)^(gap+1)·(W1+W2).
      rw [pow_succ]
      ring

omit [CompleteSpace E] in
/-- **Quantitative order-raiser: chart-`H^{m+2}`-norm of the eigenvector chart
component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, and an order
`m : ℕ`, given:

* chart-`H¹` of every chosen `j`-fold mixed weak partial for every `j ≤ m`;
* chart-`H²` of every chosen `m`-fold mixed weak partial;

the eigenvector chart component lies in chart-`H^{m+2}` on the chart target,
and there is a constant `C > 0` for which the chart-`H^{m+2}`-norm of the chart
component is bounded by `ENNReal.ofReal C` times the sum of the two aggregates
`eigenvectorIteratedW1Aggregate` (the per-tuple `W^{1,2}`-norms of the
`j`-fold mixed weak partials, `j ≤ m`) and `eigenvectorIteratedW2Aggregate`
(the per-tuple `W^{2,2}`-norms of the `m`-fold mixed weak partials).

The first conjunct is exactly the qualitative order-assembly
`eigenvectorChartComponent_memWkp_m_plus_two_of_iterated`. The norm bound is
threaded through the same gap-induction by
`eigenvectorChartIteratedPartial_wkpNorm_succ_le`, with the constant
`C := (n + 1)^m` (`n := Module.finrank ℝ E`) absorbing the per-gap-step
geometric accumulation.

This is the quantitative twin of
`eigenvectorChartComponent_memWkp_m_plus_two_of_iterated`. -/
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ ∃ C : ℝ, 0 < C ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
            (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m
              + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                g r s h_atlas i α P₀ m) := by
  classical
  -- The first conjunct is the qualitative order-assembly headline.
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
      g r s h_atlas i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  -- The gap-induction engine at `gap = m`, `j = 0`.
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction
    (I := I) (M := M) g r s h_atlas i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  -- At `j = 0`, the `0`-fold mixed weak partial is the chart component.
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_zero] at h_gap_norm
  -- The geometric constant `C := (n + 1)^m`, positive.
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · -- `0 < (n + 1)^m`.
    have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  · -- `ENNReal.ofReal ((n + 1)^m) = ((n : ℝ≥0∞) + 1)^m`; match the gap bound.
    have h_cast :
        ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
          = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
      rw [ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [h_cast]
    exact h_gap_norm

omit [CompleteSpace E] in
/-- **Eigenbasis-uniform quantitative order-raiser: chart-`H^{m+2}`-norm of the
eigenvector chart component.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, a chart center
`α : M`, a component multi-index `P₀`, and an order `m : ℕ`, there is a single
constant `C > 0` — depending only on the manifold dimension and `m`, never on
the eigenbasis index — such that, for *every* eigenbasis index `i` for which:

* chart-`H¹` holds for every chosen `j`-fold mixed weak partial (`j ≤ m`);
* chart-`H²` holds for every chosen `m`-fold mixed weak partial;

the eigenvector chart component lies in chart-`H^{m+2}` on the chart target and
its chart-`H^{m+2}`-norm is bounded by `ENNReal.ofReal C` times the sum of the
two aggregates `eigenvectorIteratedW1Aggregate` and
`eigenvectorIteratedW2Aggregate`.

This is the eigenbasis-uniform companion of
`eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le`. The per-`i`
statement carries an existential constant *after* the index `i`, hence a
potentially `i`-dependent constant; here the geometric constant
`C := (n + 1)^m` (`n := Module.finrank ℝ E`) is hoisted in front of the index
quantifier. The proof fixes that explicit `i`-free witness, then introduces `i`
together with its regularity hypotheses and threads the bound through the
gap-induction engine `eigenvectorIteratedPartial_wkpNorm_gapInduction` exactly
as in the per-`i` proof — the engine's per-gap accumulation constant `(n + 1)^m`
is itself eigenbasis-uniform. -/
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_uniform
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (_h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α))
        (_h_top_memWkp_two :
          ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial (I := I) (M := M)
                g r s h_atlas i α P₀ m idx)
              (chartTargetEuclid (I := I) (M := M) α)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
              (eigenvectorIteratedW1Aggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m
                + eigenvectorIteratedW2Aggregate (I := I) (M := M)
                  g r s h_atlas i α P₀ m) := by
  classical
  -- The eigenbasis-free geometric constant `C := (n + 1)^m`, positive.
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · -- `0 < (n + 1)^m`.
    have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  -- Witness fixed; now introduce the eigenbasis index and its hypotheses.
  intro i h_intermediate_w1p h_top_memWkp_two
  -- The first conjunct is the qualitative order-assembly headline.
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated
      g r s h_atlas i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  -- The gap-induction engine at `gap = m`, `j = 0`.
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction
    (I := I) (M := M) g r s h_atlas i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  -- At `j = 0`, the `0`-fold mixed weak partial is the chart component.
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_zero] at h_gap_norm
  -- `ENNReal.ofReal ((n + 1)^m) = ((n : ℝ≥0∞) + 1)^m`; match the gap bound.
  have h_cast :
      ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
        = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
    rw [ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [h_cast]
  exact h_gap_norm

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

/-- The order-`(K+2)` decomposition step is available as a paired
membership/norm-bound conclusion. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (K j : ℕ)
    (dirs : Fin j → Fin (Module.finrank ℝ E))
    (h_w1p : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ j dirs)
      (chartTargetEuclid (I := I) (M := M) α))
    (h_succ : ∀ a : Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K + 1) 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ (j + 1) (Fin.snoc dirs a))
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 2) 2
      (eigenvectorChartIteratedPartial (I := I) (M := M)
        g r s h_atlas i α P₀ j dirs)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorChartIteratedPartial_wkpNorm_succ_le
    g r s h_atlas i α P₀ K j dirs h_w1p h_succ).1

/-- The quantitative `W^{1,2}` bridge yields a `W^{1,2}`-norm bound by the
chart-`H^{m+1}`-norm of the chart component. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorChartIteratedPartial_wkpNorm_one_two_le
    g r s h_atlas i α P₀ m dirs h_parent).2

/-- The quantitative order-raiser delivers chart-`H^{m+2}` of the chart component
together with an explicit aggregate `wkpNorm`-bound. -/
example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p : ∀ (j : ℕ), j ≤ m →
      ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial (I := I) (M := M)
            g r s h_atlas i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial (I := I) (M := M)
          g r s h_atlas i α P₀ m idx)
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) :=
  (eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le
    g r s h_atlas i α P₀ m h_intermediate_w1p h_top_memWkp_two).1

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations above are re-keyed onto the intrinsic compact-operator
eigenbasis (`tensorResolventEigenbasisVec_ofCompact` /
`eigenvectorChartComponentFun_ofCompact` /
`eigenvectorChartIteratedPartial_unconditional`), so they hold on every closed
Riemannian manifold without the chart-locality hypothesis. -/

/-- Chart-locality-free twin of `eigenvectorChartIteratedPartial_wkpNorm_succ_le`. -/
theorem eigenvectorChartIteratedPartial_wkpNorm_succ_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (K j : ℕ)
    (dirs : Fin j → Fin (Module.finrank ℝ E))
    (h_w1p :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α))
    (h_succ :
      ∀ a : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ (j + 1) (Fin.snoc dirs a))
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (K + 2) 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ j dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        + ∑ a : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (K + 1) 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have h_succ_eq : ∀ a : Fin (Module.finrank ℝ E),
      eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ (j + 1) (Fin.snoc dirs a) =
        DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
          (d := Module.finrank ℝ E) 2 a
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j dirs) Ω := by
    intro a
    rw [eigenvectorChartIteratedPartial_unconditional_succ]
    have h_last : (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) (Fin.last j) = a :=
      Fin.snoc_last _ _
    have h_init : Fin.init (Fin.snoc dirs a :
        Fin (j + 1) → Fin (Module.finrank ℝ E)) = dirs := Fin.init_snoc _ _
    rw [h_last, h_init]
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K + 2) 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp_succ]
    refine ⟨?_, fun a => ?_⟩
    · rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
        at h_w1p
      exact h_w1p
    · have h_next := h_succ a
      rw [h_succ_eq a] at h_next
      exact h_next
  refine ⟨h_mem, ?_⟩
  have h_rec := wkpNorm_succ_le (d := Module.finrank ℝ E)
    (K + 1) 2 Ω
    (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
      g r s i α P₀ j dirs)
  have h_idx : K + 1 + 1 = K + 2 := by ring
  rw [h_idx] at h_rec
  refine h_rec.trans (add_le_add ?_ ?_)
  · exact eLpNorm_le_wkpNorm (d := Module.finrank ℝ E) 1 2 Ω
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ j dirs)
  · refine Finset.sum_le_sum (fun a _ => ?_)
    rw [h_succ_eq a]

/-- Chart-locality-free twin of
`eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp`. -/
theorem eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) :
    ∀ (k : ℕ),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (k + m) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) →
      ∀ (dirs : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) k 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) k 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ m dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (k + m) 2
              (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
                g r s i α P₀)
              (chartTargetEuclid (I := I) (M := M) α) := by
  induction m with
  | zero =>
      intro k h_parent _dirs
      refine ⟨?_, ?_⟩
      · simpa [eigenvectorChartIteratedPartial_unconditional_zero] using h_parent
      · rw [eigenvectorChartIteratedPartial_unconditional_zero, Nat.add_zero]
  | succ m ih =>
      intro k h_parent dirs
      set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
      have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
      have h_parent' :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) ((k + 1) + m) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α) := by
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq]
        exact h_parent
      obtain ⟨h_inner_mem, h_inner_norm⟩ :=
        ih (k + 1) h_parent' (Fin.init dirs)
      have h_unfold :
          eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) dirs =
            DifferentialGeometry.Analysis.Sobolev.Euclidean.chosenWeakPartial'
              (d := Module.finrank ℝ E) 2 (dirs (Fin.last m))
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ m (Fin.init dirs)) Ω :=
        eigenvectorChartIteratedPartial_unconditional_succ
          g r s i α P₀ m dirs
      refine ⟨?_, ?_⟩
      · rw [h_unfold]
        exact h_inner_mem.chosenWeakPartial_mem (dirs (Fin.last m))
      · rw [h_unfold]
        have h_peel := wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E)
          k (p := 2) hΩ_open
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init dirs)) (dirs (Fin.last m))
        refine h_peel.trans ?_
        have h_eq : (k + 1) + m = k + (m + 1) := by ring
        rw [h_eq] at h_inner_norm
        exact h_inner_norm

/-- Chart-locality-free twin of
`eigenvectorChartIteratedPartial_wkpNorm_one_two_le`. -/
theorem eigenvectorChartIteratedPartial_wkpNorm_one_two_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (dirs : Fin m → Fin (Module.finrank ℝ E))
    (h_parent :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m dirs)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) (m + 1) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) := by
  have h_parent' :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (1 + m) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) := by
    have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
    rw [h_eq]
    exact h_parent
  obtain ⟨h_mem, h_norm⟩ :=
    eigenvectorChartIteratedPartial_wkpNorm_le_of_memWkp_unconditional
      (I := I) (M := M) g r s i α P₀ m 1 h_parent' dirs
  refine ⟨h_mem, ?_⟩
  have h_eq : 1 + m = m + 1 := Nat.add_comm 1 m
  rw [h_eq] at h_norm
  exact h_norm

/-- Chart-locality-free twin of `eigenvectorIteratedW1Aggregate`. -/
def eigenvectorIteratedW1Aggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (m + 1),
    ∑ idx : Fin j → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of `eigenvectorIteratedW2Aggregate`. -/
def eigenvectorIteratedW2Aggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) : ℝ≥0∞ :=
  ∑ idx : Fin m → Fin (Module.finrank ℝ E),
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
      (d := Module.finrank ℝ E) 2 2
      (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
        g r s i α P₀ m idx)
      (chartTargetEuclid (I := I) (M := M) α)

/-- Chart-locality-free twin of
`wkpNorm_one_le_eigenvectorIteratedW1Aggregate`. -/
private lemma wkpNorm_one_le_eigenvectorIteratedW1Aggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m j : ℕ} (hj : j ≤ m)
    (dirs : Fin j → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
          g r s i α P₀ m := by
  classical
  unfold eigenvectorIteratedW1Aggregate_unconditional
  have hj_mem : j ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j' => ∑ idx : Fin j' → Fin (Module.finrank ℝ E),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j' idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.range (m + 1)) (fun _ _ => zero_le _) hj_mem)
  exact Finset.single_le_sum
    (f := fun idx : Fin j → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 1 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ j idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (s := Finset.univ) (fun _ _ => zero_le _) (Finset.mem_univ dirs)

/-- Chart-locality-free twin of
`wkpNorm_two_le_eigenvectorIteratedW2Aggregate`. -/
private lemma wkpNorm_two_le_eigenvectorIteratedW2Aggregate_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) {m : ℕ}
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m dirs)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
          g r s i α P₀ m := by
  classical
  unfold eigenvectorIteratedW2Aggregate_unconditional
  exact Finset.single_le_sum
    (f := fun idx : Fin m → Fin (Module.finrank ℝ E) =>
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
        (d := Module.finrank ℝ E) 2 2
        (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
          g r s i α P₀ m idx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun _ _ => zero_le _) (Finset.mem_univ dirs)

/-- Chart-locality-free twin of
`eigenvectorIteratedPartial_wkpNorm_gapInduction`. -/
private theorem eigenvectorIteratedPartial_wkpNorm_gapInduction_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    ∀ (gap j : ℕ), j + gap = m →
      ∀ (dirs : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (gap + 2) 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j dirs)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
              (eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m
                + eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m) := by
  classical
  intro gap
  induction gap with
  | zero =>
      intro j hj dirs
      subst hj
      simp only [Nat.add_zero] at *
      refine ⟨h_top_memWkp_two dirs, ?_⟩
      have h_single :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
                g r s i α P₀ j :=
        wkpNorm_two_le_eigenvectorIteratedW2Aggregate_unconditional
          (I := I) (M := M) g r s i α P₀ dirs
      refine h_single.trans ?_
      rw [pow_zero, one_mul]
      exact le_add_self
  | succ gap ih =>
      intro j hj dirs
      have hj_le : j ≤ m := by omega
      have hj1_eq : (j + 1) + gap = m := by omega
      have h_w1p_dirs :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) :=
        h_intermediate_w1p j hj_le dirs
      have h_ih_snoc : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 2) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α)
          ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 2) 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap *
                (eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
                    g r s i α P₀ m
                  + eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
                    g r s i α P₀ m) :=
        fun a => ih (j + 1) hj1_eq (Fin.snoc dirs a)
      have h_succ_mem : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
            (d := Module.finrank ℝ E) (gap + 1 + 1) 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ (j + 1) (Fin.snoc dirs a))
            (chartTargetEuclid (I := I) (M := M) α) := by
        intro a
        have h := (h_ih_snoc a).1
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      obtain ⟨h_mem, h_norm_bound⟩ :=
        eigenvectorChartIteratedPartial_wkpNorm_succ_le_unconditional
          (I := I) (M := M) g r s i α P₀ (gap + 1) j dirs
          h_w1p_dirs h_succ_mem
      refine ⟨h_mem, ?_⟩
      set W1 : ℝ≥0∞ :=
        eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
          g r s i α P₀ m with hW1_def
      set W2 : ℝ≥0∞ :=
        eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
          g r s i α P₀ m with hW2_def
      have h_w1_term :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        have h_single : DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) 1 2
            (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
              g r s i α P₀ j dirs)
            (chartTargetEuclid (I := I) (M := M) α) ≤ W1 :=
          wkpNorm_one_le_eigenvectorIteratedW1Aggregate_unconditional
            (I := I) (M := M) g r s i α P₀ hj_le dirs
        refine h_single.trans (le_trans (le_self_add (a := W1) (b := W2)) ?_)
        refine le_mul_of_one_le_left (zero_le _) ?_
        exact one_le_pow₀ (le_add_of_nonneg_left (zero_le _))
      have h_snoc_term : ∀ a : Fin (Module.finrank ℝ E),
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 1 + 1) 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ (j + 1) (Fin.snoc dirs a))
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        intro a
        have h := (h_ih_snoc a).2
        have h_eq : gap + 1 + 1 = gap + 2 := by ring
        rw [h_eq]
        exact h
      have h_chain :
          DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
              (d := Module.finrank ℝ E) (gap + 1 + 2) 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j dirs)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2)
              + ∑ _a : Fin (Module.finrank ℝ E),
                  ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ gap * (W1 + W2) := by
        refine h_norm_bound.trans (add_le_add h_w1_term ?_)
        exact Finset.sum_le_sum (fun a _ => h_snoc_term a)
      refine h_chain.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [pow_succ]
      ring

/-- Chart-locality-free twin of
`eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le`. -/
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (h_intermediate_w1p :
      ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 1 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ j idx)
          (chartTargetEuclid (I := I) (M := M) α))
    (h_top_memWkp_two :
      ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) 2 2
          (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
            g r s i α P₀ m idx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
    ∧ ∃ C : ℝ, 0 < C ∧
        DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal C *
            (eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m
              + eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
                g r s i α P₀ m) := by
  classical
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated_unconditional
      g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction_unconditional
    (I := I) (M := M) g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_unconditional_zero] at h_gap_norm
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  · have h_cast :
        ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
          = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
      rw [ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    rw [h_cast]
    exact h_gap_norm

/-- Chart-locality-free twin of
`eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_uniform`. -/
theorem eigenvectorChartComponent_wkpNorm_m_plus_two_of_iterated_le_uniform_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (_h_intermediate_w1p :
          ∀ (j : ℕ), j ≤ m → ∀ (idx : Fin j → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 1 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ j idx)
              (chartTargetEuclid (I := I) (M := M) α))
        (_h_top_memWkp_two :
          ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
            DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) 2 2
              (eigenvectorChartIteratedPartial_unconditional (I := I) (M := M)
                g r s i α P₀ m idx)
              (chartTargetEuclid (I := I) (M := M) α)),
        DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
          (d := Module.finrank ℝ E) (m + 2) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ∧ DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNorm
            (d := Module.finrank ℝ E) (m + 2) 2
            (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal C *
              (eigenvectorIteratedW1Aggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m
                + eigenvectorIteratedW2Aggregate_unconditional (I := I) (M := M)
                  g r s i α P₀ m) := by
  classical
  refine ⟨((Module.finrank ℝ E : ℝ) + 1) ^ m, ?_, ?_⟩
  · have h_base : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by positivity
    exact pow_pos h_base m
  intro i h_intermediate_w1p h_top_memWkp_two
  have h_first :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 2) 2
        (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartComponent_memWkp_m_plus_two_of_iterated_unconditional
      g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
  refine ⟨h_first, ?_⟩
  have h_gap := eigenvectorIteratedPartial_wkpNorm_gapInduction_unconditional
    (I := I) (M := M) g r s i α P₀ m h_intermediate_w1p h_top_memWkp_two
    m 0 (by omega) Fin.elim0
  obtain ⟨_, h_gap_norm⟩ := h_gap
  rw [eigenvectorChartIteratedPartial_unconditional_zero] at h_gap_norm
  have h_cast :
      ENNReal.ofReal (((Module.finrank ℝ E : ℝ) + 1) ^ m)
        = ((Module.finrank ℝ E : ℝ≥0∞) + 1) ^ m := by
    rw [ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  rw [h_cast]
  exact h_gap_norm

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
