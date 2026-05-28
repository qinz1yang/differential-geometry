import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorIteratedStepRegularity
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp

/-!
# Global `W^{k,2}` regularity of the differentiated chart right-hand side

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, and a component multi-index `P₀`, the level-`m`
differentiated chart right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α
P₀ m l` of the limiting per-component variational identity is the explicit
recursion

* level `0` is the seven-term `eigenvectorChartRHS`;
* level `m + 1` is the indicator, of the compact partition-of-unity kernel, of
  the chart-density-divided differentiated numerator built from the level-`m`
  right-hand side.

This module discharges its **global iterated Euclidean Sobolev regularity**: for
each `K : ℕ`, given the order-`(m + 1 + K)` partition-of-unity regularity input
`h_pou` on every chart center, the level-`m` differentiated right-hand side lies
in `MemWkp K 2` on the open chart target. The `K = 1` corollary restates this as
the vendored `DeGiorgi.MemW1p 2` membership.

## Strategy

The polymorphic-in-`K` headline `eigenvectorChartRHSDiff_memWkp` is proved by
induction on `m`, with `K` universally quantified so the inductive hypothesis
can be invoked at `K + 1`:

* level `0`: `eigenvectorChartRHSDiff … 0 l = eigenvectorChartRHS …`, whose
  `MemWkp K 2` regularity is `eigenvectorChartRHS_memWkp` — its `h_pou`
  requirement is at order `K + 1 = 0 + 1 + K`, matching this theorem's `h_pou`;
* level `m + 1`: writing `l = Fin.snoc (Fin.init l) (l (Fin.last m))`, the
  standalone-step identity `eigenvectorChartIteratedStep_eq_rhsDiff_succ`
  rewrites `eigenvectorChartRHSDiff … (m+1) l` as the level-`(m+1)` standalone
  inductive step over the level-`m` right-hand side. The per-step regularity
  propagator `eigenvectorChartIteratedStep_memWkp_K_two` then delivers `MemWkp K
  2`, discharging its three hypotheses: the eigenvector chart component is
  `MemWkp (m + 2 + K) 2` (supplied by `h_pou`); the level-`m` right-hand side is
  `MemWkp (K + 1) 2` (the inductive hypothesis at order `K + 1`); the level-`m`
  right-hand side is ae-zero off the partition-of-unity kernel (the seven-term
  vanishing `eigenvectorChartRHS_ae_zero_off_chartPouKernel` at level `0`, the
  indicator-vanishing `eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel`
  at positive levels).

The `K = 1` corollary `eigenvectorChartRHSDiff_memW1p` instantiates the headline
at `K = 1` and rewrites `MemWkp 1 2` to `DeGiorgi.MemW1p 2` via
`MemWkp.one_iff_memW1p`.

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

/-! ## The eigenvector chart component is `W^{N,2}` from the partition-of-unity input

The per-step regularity propagator `eigenvectorChartIteratedStep_memWkp_K_two`
consumes the `MemWkp` regularity of the eigenvector chart component
`eigenvectorChartComponentFun`, which is the chart `P₀`-component of the
eigenvector vector `tensorResolventEigenbasisVec h_atlas i`. The genuine
regularity input `h_pou` is phrased for the chart component of the `L²`-coercion
`TensorH1ComplToTensorL2 g r s (eigenvectorResolvent …)` instead. The two chart
components differ by the nonzero scalar `μ⁻¹` (`eigenvector_chartComponent_eq`),
and `MemWkp` is scalar-invariant, so the regularity transfers. -/

/-- The eigenvector chart component `eigenvectorChartComponentFun g r s h_atlas
i α P₀` is `MemWkp N 2` on the chart-`α` target, given that the chart components
of the `L²`-coercion of the eigenvector resolvent are `MemWkp N 2` on every
chart target. The two chart components differ by the nonzero scalar `μ⁻¹`
(`eigenvector_chartComponent_eq`), and `MemWkp` is scalar-invariant. -/
private lemma eigenvectorChartComponentFun_memWkp_of_pou
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `MemWkp N 2` of the resolvent-coercion chart component, from `h_pou`.
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      Ω :=
    h_pou α P₀
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq`). Pass to `coeFn` and rescale.
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_atlas i α P₀
  have h_ae : (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P₀)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    -- `Lp.coeFn_smul`: the coercion of the rescaled `L²` element is `μ⁻¹ •` the
    -- coercion of the original `L²` element, almost everywhere. Rewriting the
    -- rescaled resolvent element back as the eigenvector element via
    -- `eigenvector_chartComponent_eq` exhibits the eigenvector chart-component
    -- coercion as `μ⁻¹ •` the resolvent-coercion chart component.
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) α P₀)
    rw [← h_chart_eq] at h_smul
    -- `eigenvectorChartComponentFun` is, by definition, the coercion-to-function
    -- of the eigenvector chart-component `L²` element; `chartL2Measure α =
    -- volume.restrict Ω` absorbs the measure. The pointwise `•`-to-`*` step
    -- (`Pi.smul_apply`, `smul_eq_mul`) finishes.
    filter_upwards [h_smul] with y hy
    change ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = _
    rw [hy, Pi.smul_apply, smul_eq_mul]
  -- `MemWkp N 2` is scalar-invariant.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-! ## The differentiated chart right-hand side vanishes ae off the kernel

The per-step regularity propagator also consumes the ae-vanishing of the
level-`m` differentiated right-hand side off the compact partition-of-unity
kernel `chartPouKernel α`. At level `0` the right-hand side is the seven-term
`eigenvectorChartRHS`, whose ae-vanishing is `eigenvectorChartRHS_ae_zero_off_chartPouKernel`;
at every positive level it is the indicator of the kernel, so vanishes pointwise
off it (`eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel`). -/

/-- The level-`m` differentiated chart right-hand side `eigenvectorChartRHSDiff g
r s h_atlas i α P₀ m l` is almost everywhere zero on the open complement of the
compact partition-of-unity kernel `chartPouKernel α` inside the chart target. -/
private lemma eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      -- Level `0`: the seven-term `eigenvectorChartRHS`.
      rw [eigenvectorChartRHSDiff_zero]
      exact eigenvectorChartRHS_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀
  | succ m =>
      -- Level `m + 1`: the indicator of the kernel, zero pointwise off it.
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s h_atlas i α P₀ m l hy.2

/-! ## Global `W^{k,2}` regularity of the differentiated chart right-hand side

The polymorphic-in-`K` headline. The proof is induction on `m`, with `K`
universally quantified so the inductive hypothesis is available at `K + 1`. -/

/-- **Global `W^{k,2}` regularity of the differentiated chart right-hand side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, and a
direction multi-index `l : Fin m → Fin n`, the level-`m` differentiated chart
right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` is `MemWkp K
2` — iterated Euclidean Sobolev regular of order `K` — on the chart-`α` target,
given the order-`(m + 1 + K)` partition-of-unity regularity input `h_pou` on
every chart center.

The proof is induction on `m`, with `K` universally quantified:

* level `0` is the seven-term `eigenvectorChartRHS`, whose `MemWkp K 2`
  regularity is `eigenvectorChartRHS_memWkp` at order `K + 1 = 0 + 1 + K`;
* level `m + 1` rewrites the right-hand side as the standalone inductive step
  (`eigenvectorChartIteratedStep_eq_rhsDiff_succ`) and applies the per-step
  regularity propagator `eigenvectorChartIteratedStep_memWkp_K_two`, fed: the
  `MemWkp (m + 2 + K) 2` regularity of the eigenvector chart component (from
  `h_pou`); the inductive hypothesis at order `K + 1`; the ae-vanishing of the
  level-`m` right-hand side off the partition-of-unity kernel. -/
theorem eigenvectorChartRHSDiff_memWkp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Induction on `m`, with `K` and the direction multi-index `l` generalised so
  -- the inductive hypothesis can be invoked at `K + 1`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is `eigenvectorChartRHS`.
      rw [eigenvectorChartRHSDiff_zero]
      -- `eigenvectorChartRHS_memWkp` needs `h_pou` at order `K + 1`; this
      -- theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact eigenvectorChartRHS_memWkp (I := I) (M := M)
        g r s h_atlas i α P₀ K h_pou'
  | succ m ih =>
      -- Level `m + 1`: write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards): the level-`(m+1)`
      -- right-hand side at `Fin.snoc dirs l₀` is the standalone inductive step
      -- over the level-`m` right-hand side.
      rw [← eigenvectorChartIteratedStep_eq_rhsDiff_succ (I := I) (M := M)
        g r s h_atlas i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Apply the per-step regularity propagator.
      -- Hypothesis (a): the eigenvector chart component is `MemWkp (m + 2 + K) 2`.
      -- This theorem's `h_pou` is at order `(m + 1) + 1 + K = m + 2 + K`.
      have h_pou_comp : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + 1 + K = m + 2 + K := by omega
        rw [← h_idx]
        exact h_pou β Q
      have h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponentFun_memWkp_of_pou (I := I) (M := M)
          g r s h_atlas i (m + 2 + K) h_pou_comp α P₀
      -- Hypothesis (b): the level-`m` right-hand side is `MemWkp (K + 1) 2` —
      -- the inductive hypothesis at order `K + 1`. Its `h_pou` requirement is at
      -- order `m + 1 + (K + 1) = m + 2 + K`, supplied by `h_pou`.
      have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou β Q
      have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartRHSDiff (I := I) (M := M)
            g r s h_atlas i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
        ih (K + 1) (Fin.init l) h_pou_prev
      -- Hypothesis (c): the level-`m` right-hand side is ae-zero off the kernel.
      have h_prev_ae_zero :
          eigenvectorChartRHSDiff (I := I) (M := M)
              g r s h_atlas i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) :=
        eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel
          (I := I) (M := M) g r s h_atlas i α P₀ m (Fin.init l)
      -- Conclude via the per-step regularity propagator.
      exact eigenvectorChartIteratedStep_memWkp_K_two (I := I) (M := M)
        g r s h_atlas i α P₀ m K (Fin.init l)
        (fChartEffPrev := eigenvectorChartRHSDiff (I := I) (M := M)
          g r s h_atlas i α P₀ m (Fin.init l))
        (l (Fin.last m)) h_comp h_prev_memWkp_succ h_prev_ae_zero

/-! ## The `K = 1` corollary — global `W^{1,2}` regularity

At `K = 1` the global regularity headline gives `MemWkp 1 2
(eigenvectorChartRHSDiff)`, which `MemWkp.one_iff_memW1p` restates as the
vendored `DeGiorgi.MemW1p 2` membership. This is the final node of the
differentiated-right-hand-side regularity sub-campaign: the level-`m`
differentiated chart right-hand side is globally `W^{1,2}` on the chart target,
given the order-`(m + 2)` partition-of-unity regularity input. -/

/-- **Global `W^{1,2}` regularity of the differentiated chart right-hand side.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i`, a chart center `α : M`, a component multi-index `P₀`, a level `m`, and a
direction multi-index `l : Fin m → Fin n`, the level-`m` differentiated chart
right-hand side `eigenvectorChartRHSDiff g r s h_atlas i α P₀ m l` lies in the
vendored `DeGiorgi.MemW1p 2` on the chart-`α` target, given the order-`(m + 2)`
partition-of-unity regularity input `h_pou` on every chart center.

This is the `K = 1` instance of `eigenvectorChartRHSDiff_memWkp` — at `K = 1` the
`h_pou` requirement is at order `m + 1 + 1 = m + 2`, and `MemWkp.one_iff_memW1p`
restates `MemWkp 1 2` as `DeGiorgi.MemW1p 2`. -/
theorem eigenvectorChartRHSDiff_memW1p
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- `eigenvectorChartRHSDiff_memWkp` at `K = 1`: its `h_pou` requirement is at
  -- order `m + 1 + 1 = m + 2`, matching this theorem's `h_pou`.
  have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := by
    intro β Q
    have h_idx : m + 1 + 1 = m + 2 := by omega
    rw [h_idx]
    exact h_pou β Q
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
      g r s h_atlas i α P₀ m 1 l h_pou'
  rw [MemWkp.one_iff_memW1p] at h_memWkp
  exact h_memWkp

/-! ## Sanity tests -/

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp (I := I) (M := M)
    g r s h_atlas i α P₀ m K l h_pou

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartRHSDiff (I := I) (M := M) g r s h_atlas i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memW1p (I := I) (M := M)
    g r s h_atlas i α P₀ m l h_pou

end ElaborationTests

/-! ## Chart-locality-free twins

The declarations below re-establish the differentiated-right-hand-side regularity
results on the intrinsic compact-operator eigenbasis
`tensorResolventEigenbasisVec_ofCompact (tensorResolventL2_isCompactOperator_intrinsic
g r s) i`, dropping the chart-selection hypothesis carried by their originals. The
regularity input `h_pou` is correspondingly keyed on the chart-locality-free
eigenvector resolvent `eigenvectorResolvent_unconditional`. -/

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorChartComponentFun_memWkp_of_pou`.

The canonical eigenvector chart component `eigenvectorChartComponentFun_ofCompact
g r s i α P₀` is `MemWkp N 2` on the chart-`α` target, given that the chart
components of the `L²`-coercion of the chart-locality-free eigenvector resolvent
are `MemWkp N 2` on every chart target. The two chart components differ by the
nonzero scalar `μ⁻¹` (`eigenvector_chartComponent_eq_unconditional`), and `MemWkp`
is scalar-invariant. -/
private lemma eigenvectorChartComponentFun_memWkp_of_pou_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (eigenvectorChartComponentFun_ofCompact (I := I) (M := M) g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  -- `MemWkp N 2` of the resolvent-coercion chart component, from `h_pou`.
  have h_res : MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      Ω :=
    h_pou α P₀
  -- The eigenvector chart component is `μ⁻¹` times the resolvent-coercion chart
  -- component (`eigenvector_chartComponent_eq_unconditional`). Pass to `coeFn`
  -- and rescale.
  have h_chart_eq := eigenvector_chartComponent_eq_unconditional (I := I) (M := M)
    g r s i α P₀
  have h_ae : (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
        g r s i α P₀)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          α P₀ : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    -- `Lp.coeFn_smul`: the coercion of the rescaled `L²` element is `μ⁻¹ •` the
    -- coercion of the original `L²` element, almost everywhere. Rewriting the
    -- rescaled resolvent element back as the eigenvector element via
    -- `eigenvector_chartComponent_eq_unconditional` exhibits the eigenvector
    -- chart-component coercion as `μ⁻¹ •` the resolvent-coercion chart component.
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) α P₀)
    rw [← h_chart_eq] at h_smul
    -- `eigenvectorChartComponentFun_ofCompact` is, by definition, the
    -- coercion-to-function of the eigenvector chart-component `L²` element;
    -- `chartL2Measure α = volume.restrict Ω` absorbs the measure. The pointwise
    -- `•`-to-`*` step (`Pi.smul_apply`, `smul_eq_mul`) finishes.
    filter_upwards [h_smul] with y hy
    change ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
          i) α P₀ :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y = _
    rw [hy, Pi.smul_apply, smul_eq_mul]
  -- `MemWkp N 2` is scalar-invariant.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-- Chart-locality-free twin of
`eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel`.

The level-`m` chart-locality-free differentiated chart right-hand side
`eigenvectorChartRHSDiff_unconditional g r s i α P₀ m l` is almost everywhere zero
on the open complement of the compact partition-of-unity kernel `chartPouKernel α`
inside the chart target. -/
private lemma eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (m : ℕ) (l : Fin m → Fin (Module.finrank ℝ E)) :
    eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l
      =ᵐ[(volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α)] (fun _ : EuclN => (0 : ℝ)) := by
  cases m with
  | zero =>
      -- Level `0`: the seven-term `eigenvectorChartRHS_unconditional`.
      rw [eigenvectorChartRHSDiff_unconditional_zero]
      exact eigenvectorChartRHS_unconditional_ae_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀
  | succ m =>
      -- Level `m + 1`: the indicator of the kernel, zero pointwise off it.
      have hV_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α \
          chartPouKernel (I := I) (M := M) α) :=
        (chartTargetEuclid_isOpen (I := I) (M := M) α).measurableSet.diff
          (chartPouKernel_measurableSet (I := I) (M := M) α)
      rw [Filter.EventuallyEq, ae_restrict_iff' hV_meas]
      refine Filter.Eventually.of_forall (fun y hy => ?_)
      exact eigenvectorChartRHSDiff_unconditional_succ_eq_zero_off_chartPouKernel
        (I := I) (M := M) g r s i α P₀ m l hy.2

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_memWkp`.

**Global `W^{k,2}` regularity of the chart-locality-free differentiated chart
right-hand side.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an
eigenbasis index `i`, a chart center `α : M`, a component multi-index `P₀`, a
level `m`, and a direction multi-index `l : Fin m → Fin n`, the level-`m`
chart-locality-free differentiated chart right-hand side
`eigenvectorChartRHSDiff_unconditional g r s i α P₀ m l` is `MemWkp K 2` on the
chart-`α` target, given the order-`(m + 1 + K)` partition-of-unity regularity input
`h_pou` (keyed on `eigenvectorResolvent_unconditional`) on every chart center.

The proof is induction on `m`, with `K` universally quantified:

* level `0` is the seven-term `eigenvectorChartRHS_unconditional`, whose `MemWkp K
  2` regularity is `eigenvectorChartRHS_memWkp_unconditional` at order `K + 1 = 0 +
  1 + K`;
* level `m + 1` rewrites the right-hand side as the standalone inductive step
  (`eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ`) and applies the
  per-step regularity propagator `eigenvectorChartIteratedStep_memWkp_K_two_unconditional`,
  fed: the `MemWkp (m + 2 + K) 2` regularity of the eigenvector chart component
  (from `h_pou`); the inductive hypothesis at order `K + 1`; the ae-vanishing of the
  level-`m` right-hand side off the partition-of-unity kernel. -/
theorem eigenvectorChartRHSDiff_memWkp_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  -- Induction on `m`, with `K` and the direction multi-index `l` generalised so
  -- the inductive hypothesis can be invoked at `K + 1`.
  induction m generalizing K with
  | zero =>
      -- Level `0`: the differentiated right-hand side is
      -- `eigenvectorChartRHS_unconditional`.
      rw [eigenvectorChartRHSDiff_unconditional_zero]
      -- `eigenvectorChartRHS_memWkp_unconditional` needs `h_pou` at order `K + 1`;
      -- this theorem's `h_pou` is at order `0 + 1 + K = K + 1`.
      have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (K + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : (0 : ℕ) + 1 + K = K + 1 := by omega
        rw [← h_idx]
        exact h_pou β Q
      exact eigenvectorChartRHS_memWkp_unconditional (I := I) (M := M)
        g r s i α P₀ K h_pou'
  | succ m ih =>
      -- Level `m + 1`: write `l = Fin.snoc (Fin.init l) (l (Fin.last m))`.
      have h_snoc :
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1) l =
            eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ (m + 1)
              (Fin.snoc (Fin.init l) (l (Fin.last m))) := by
        rw [Fin.snoc_init_self]
      rw [h_snoc]
      -- The standalone-step identity (used backwards): the level-`(m+1)`
      -- right-hand side at `Fin.snoc dirs l₀` is the standalone inductive step
      -- over the level-`m` right-hand side.
      rw [← eigenvectorChartIteratedStep_unconditional_eq_rhsDiff_succ
        (I := I) (M := M) g r s i α P₀ m (Fin.init l) (l (Fin.last m))]
      -- Apply the per-step regularity propagator.
      -- Hypothesis (a): the eigenvector chart component is `MemWkp (m + 2 + K) 2`.
      -- This theorem's `h_pou` is at order `(m + 1) + 1 + K = m + 2 + K`.
      have h_pou_comp : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + 1 + K = m + 2 + K := by omega
        rw [← h_idx]
        exact h_pou β Q
      have h_comp : MemWkp (d := Module.finrank ℝ E) (m + 2 + K) 2
          (eigenvectorChartComponentFun_ofCompact (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α) :=
        eigenvectorChartComponentFun_memWkp_of_pou_unconditional (I := I) (M := M)
          g r s i (m + 2 + K) h_pou_comp α P₀
      -- Hypothesis (b): the level-`m` right-hand side is `MemWkp (K + 1) 2` —
      -- the inductive hypothesis at order `K + 1`. Its `h_pou` requirement is at
      -- order `m + 1 + (K + 1) = m + 2 + K`, supplied by `h_pou`.
      have h_pou_prev : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
          MemWkp (d := Module.finrank ℝ E) (m + 1 + (K + 1)) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
              EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β) := by
        intro β Q
        have h_idx : m + 1 + (K + 1) = m + 1 + 1 + K := by omega
        rw [h_idx]
        exact h_pou β Q
      have h_prev_memWkp_succ : MemWkp (d := Module.finrank ℝ E) (K + 1) 2
          (eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
            g r s i α P₀ m (Fin.init l))
          (chartTargetEuclid (I := I) (M := M) α) :=
        ih (K + 1) (Fin.init l) h_pou_prev
      -- Hypothesis (c): the level-`m` right-hand side is ae-zero off the kernel.
      have h_prev_ae_zero :
          eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
              g r s i α P₀ m (Fin.init l)
            =ᵐ[(volume : Measure EuclN).restrict
              (chartTargetEuclid (I := I) (M := M) α \
                chartPouKernel (I := I) (M := M) α)]
            (fun _ : EuclN => (0 : ℝ)) :=
        eigenvectorChartRHSDiff_ae_zero_off_chartPouKernel_unconditional
          (I := I) (M := M) g r s i α P₀ m (Fin.init l)
      -- Conclude via the per-step regularity propagator.
      exact eigenvectorChartIteratedStep_memWkp_K_two_unconditional (I := I) (M := M)
        g r s i α P₀ m K (Fin.init l)
        (fChartEffPrev := eigenvectorChartRHSDiff_unconditional (I := I) (M := M)
          g r s i α P₀ m (Fin.init l))
        (l (Fin.last m)) h_comp h_prev_memWkp_succ h_prev_ae_zero

/-- Chart-locality-free twin of `eigenvectorChartRHSDiff_memW1p`.

**Global `W^{1,2}` regularity of the chart-locality-free differentiated chart
right-hand side.** The level-`m` chart-locality-free differentiated chart
right-hand side `eigenvectorChartRHSDiff_unconditional g r s i α P₀ m l` lies in the
vendored `DeGiorgi.MemW1p 2` on the chart-`α` target, given the order-`(m + 2)`
partition-of-unity regularity input `h_pou` (keyed on
`eigenvectorResolvent_unconditional`) on every chart center.

This is the `K = 1` instance of `eigenvectorChartRHSDiff_memWkp_unconditional` — at
`K = 1` the `h_pou` requirement is at order `m + 1 + 1 = m + 2`, and
`MemWkp.one_iff_memW1p` restates `MemWkp 1 2` as `DeGiorgi.MemW1p 2`. -/
theorem eigenvectorChartRHSDiff_memW1p_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) := by
  -- `eigenvectorChartRHSDiff_memWkp_unconditional` at `K = 1`: its `h_pou`
  -- requirement is at order `m + 1 + 1 = m + 2`, matching this theorem's `h_pou`.
  have h_pou' : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) := by
    intro β Q
    have h_idx : m + 1 + 1 = m + 2 := by omega
    rw [h_idx]
    exact h_pou β Q
  have h_memWkp : MemWkp (d := Module.finrank ℝ E) 1 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
    eigenvectorChartRHSDiff_memWkp_unconditional (I := I) (M := M)
      g r s i α P₀ m 1 l h_pou'
  rw [MemWkp.one_iff_memW1p] at h_memWkp
  exact h_memWkp

/-! ## Sanity tests (chart-locality-free) -/

section ElaborationTestsUnconditional

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)
  (i : TensorEigenIdx (I := I) (M := M) g r s)

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m K : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 1 + K) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memWkp_unconditional (I := I) (M := M)
    g r s i α P₀ m K l h_pou

example (α : M) (P₀ : TensorCompIdx (E := E) r s) (m : ℕ)
    (l : Fin m → Fin (Module.finrank ℝ E))
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) (m + 2) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartRHSDiff_unconditional (I := I) (M := M) g r s i α P₀ m l)
      (chartTargetEuclid (I := I) (M := M) α) :=
  eigenvectorChartRHSDiff_memW1p_unconditional (I := I) (M := M)
    g r s i α P₀ m l h_pou

end ElaborationTestsUnconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
