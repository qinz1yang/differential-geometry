import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCptResolvBounds
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSMemWkp
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartCrossRightDiv
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.CutoffChartComponentWkpNorm

/-!
# Eigenbasis-uniform per-`K'`-family atom converters for the partial,
# component, and cutoff-partial limit-atom Sobolev bounds

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an order ceiling
`N : ℕ`, an eigenbasis-uniform Sobolev hypothesis `hCN_bd` on the eigenvector
chart components at order `N` — a single nonnegative constant `CN`, an exponent
`eN`, with the bound holding β-uniformly over every base point and component
multi-index — and a β-uniform `MemWkp` regularity input for the resolvent chart
components, this file ships three per-`K'`-family atom converters needed to
populate the per-`K`-family atom families of the level-`(m+1)` carrier
hypothesis bundle.

## The three atoms

* `eigenvector_componentLpLimit_perK_from_uniform_β` — the component-limit atom
  `componentLpLimit g r s h_atlas i α p`, at order `K' ≤ N`. The atom is
  `i.fst.val •` the canonical eigenvector chart component; its iterated Sobolev
  norm reduces to that of the chart component (the chart-component converter at
  order `K' ≤ N`) times the scalar `μ := i.fst.val`, which is absorbed into
  `μ⁻¹^eN` via the `μ · μ⁻¹^eN ≤ μ⁻¹^eN` inequality (`μ ∈ (0, 1]`).
* `eigenvector_partialLpLimit_perK_from_uniform_β` — the partial-limit atom
  `partialLpLimit g r s h_atlas i α P k`, at order `K' ≤ N - 1` (or
  equivalently `K' + 1 ≤ N`). The atom is `i.fst.val •` the eigenvector weak
  chart partial; the latter is a genuine weak `k`-th partial of the chart
  component (`eigenvectorChartWeakPartial_hasWeakPartialDeriv`), so it agrees
  almost everywhere with the canonical chosen weak partial of the chart
  component, whose iterated Sobolev norm at order `K'` is at most the order
  `K' + 1` Sobolev norm of the chart component itself
  (`wkpNorm_chosenWeakPartial_le`). The chart-component converter then
  supplies the order-`(K' + 1)` chart-component bound, and the scalar `μ` is
  absorbed exactly as in the component case.
* `eigenvector_cutoffPartialLpLimit_perK_from_uniform_β` — the cutoff
  partial-limit atom `cutoffPartialLpLimit g r s h_atlas i α P l`, at order
  `K' ≤ N - 1`. The atom is `i.fst.val •` the eigenvector cutoff chart
  partial; the latter is a genuine weak `l`-th partial of the cutoff chart
  component (`eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv`). The
  input-uniform cutoff ↔ partition-of-unity iterated-Sobolev bound
  `wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform` bounds the cutoff
  chart component's order-`(K' + 1)` Sobolev norm by a single (α, P₀, K')
  -dependent constant times a finite sum, over transport chart centres `β` and
  component multi-indices `Q`, of order-`(K' + 1)` Sobolev norms of the
  partition-of-unity chart components of the eigenvector. Each summand is then
  dominated by the chart-component converter at `(β, Q)` and order
  `K' + 1 ≤ N`. The resulting output constant depends on `K'` (and on
  `α, P₀, N`), packaged as a function `CN' : ℕ → ℝ`.

## β-uniformity

The output bounds are uniform over the eigenbasis index `i` — the cutoff
multiplier in the third headline is supplied by an `i`-uniform cutoff bridge,
so a single constant per `K'` serves every eigenvector. The absorption identity
`μ · μ⁻¹^eN ≤ μ⁻¹^eN` keeps the exponent stable at `eN` across all three
headlines.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Sobolev.Chart
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.MetricExtension
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-! ## File-local Borel-space instances on `E` and `M` -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Positivity of the resolvent eigenvalue -/

omit [CompleteSpace E] in
/-- The eigenbasis vector has unit norm. -/
private lemma vec_norm_eq_one_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ = 1 :=
  (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s) h_atlas).norm_eq_one i

omit [CompleteSpace E] in
/-- The resolvent eigenvalue is strictly positive. -/
private lemma eigenval_pos_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s h_atlas i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

omit [CompleteSpace E] in
/-- The resolvent eigenvalue is at most `1`. -/
private lemma eigenval_le_one_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_mem (I := I) (M := M) h_atlas i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local
        (I := I) (M := M) g r s h_atlas i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

omit [CompleteSpace E] in
/-- `μ · μ⁻¹^eN ≤ μ⁻¹^eN` whenever `0 < μ ≤ 1`. -/
private lemma mu_mul_inv_pow_le_inv_pow_local
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_le_one : μ ≤ 1) (eN : ℕ) :
    μ * μ⁻¹ ^ eN ≤ μ⁻¹ ^ eN := by
  have hμ_inv_nn : 0 ≤ μ⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_pow_nn : 0 ≤ μ⁻¹ ^ eN := pow_nonneg hμ_inv_nn _
  have h : μ * μ⁻¹ ^ eN ≤ 1 * μ⁻¹ ^ eN :=
    mul_le_mul_of_nonneg_right hμ_le_one hμ_inv_pow_nn
  simpa using h

/-! ## A local copy of the eigenvector-pou-MemWkp bridge

The eigenvector chart-component is `(i.fst.val)⁻¹` times the resolvent
chart-component; so a `MemWkp N 2` hypothesis on the resolvent chart components
transfers to a `MemWkp N 2` statement on the eigenvector chart components. -/

omit [CompleteSpace E] in
private lemma eigenvectorVec_pou_memWkp_local
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
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_res := h_pou β Q
  have h_chart_eq := eigenvector_chartComponent_eq (I := I) (M := M)
    g r s h_atlas i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-! ## Headline 1 — the component-limit atom -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family component-limit-atom Sobolev bound, derived from a
β-uniform order-`N` chart-component Sobolev hypothesis.**

The component-limit atom `componentLpLimit g r s h_atlas i α P` — `i.fst.val`
times the canonical eigenvector chart component — has, at every order `K' ≤ N`
and every eigenbasis index `i`, iterated Sobolev norm on the chart-`α` target
bounded by `ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN)` times
`ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`, with the same `CN`
and `eN` as the input chart-component hypothesis.

The proof rewrites the atom's coercion as `i.fst.val *
eigenvectorChartComponentFun`, factors out `i.fst.val` via
`wkpNorm_const_smul`, applies the chart-component converter at
`(α, P)` and order `K' ≤ N`, and absorbs the `i.fst.val` factor through the
`μ · μ⁻¹^eN ≤ μ⁻¹^eN` inequality. -/
theorem eigenvector_componentLpLimit_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro K' hK' i P
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local (I := I) (M := M) g r s h_atlas i
  -- Express the atom's coercion as `μ *` the eigenvector chart component.
  have h_smul : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae : (fun y => ((componentLpLimit (I := I) (M := M)
        g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M) g r s h_atlas i α P y) := by
    filter_upwards [h_smul] with y hy
    rw [hy, smul_eq_mul]
    rfl
  -- Regularity of the eigenvector chart component at order `K'`, used by
  -- `wkpNorm_const_smul`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω :=
    eigenvectorVec_pou_memWkp_local (I := I) (M := M) g r s h_atlas i K'
      (fun β Q => h_pou_resolv i K' β Q hK') α P
  -- Rewrite the wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((componentLpLimit (I := I) (M := M) g r s h_atlas i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The chart-component converter at `(α, P)` and order `K' ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s h_atlas N CN hCN_nn eN hCN_bd α P K' hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
      h_step2

/-! ## Headline 2 — the partial-limit atom -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family partial-limit-atom Sobolev bound, derived from a
β-uniform order-`N` chart-component Sobolev hypothesis.**

The partial-limit atom `partialLpLimit g r s h_atlas i α P k` — `i.fst.val`
times the eigenvector weak `k`-th chart partial — has, at every order `K'` with
`K' + 1 ≤ N` and every eigenbasis index `i`, iterated Sobolev norm on the
chart-`α` target bounded by `ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN)` times
`ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`, with the same `CN`
and `eN` as the input chart-component hypothesis.

The eigenvector weak chart partial is, almost everywhere, the canonical chosen
weak partial of the eigenvector chart component
(`HasWeakPartialDeriv.ae_eq`, comparing
`eigenvectorChartWeakPartial_hasWeakPartialDeriv` and
`chosenWeakPartial'_isWeakPartial_of_mem`). Its order-`K'` Sobolev norm is
therefore at most the order-`(K' + 1)` Sobolev norm of the chart component
(`wkpNorm_chosenWeakPartial_le`), which is in turn bounded by the
chart-component converter at `(α, P)` and order `K' + 1 ≤ N`. The remaining
`i.fst.val` scaling is absorbed by the `μ · μ⁻¹^eN ≤ μ⁻¹^eN` inequality. -/
theorem eigenvector_partialLpLimit_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro K' hK' i P k
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local (I := I) (M := M) g r s h_atlas i
  -- Order-`(K' + 1)` regularity of the eigenvector chart component at `(α, P)`.
  have h_comp_succ : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω :=
    eigenvectorVec_pou_memWkp_local (I := I) (M := M) g r s h_atlas i (K' + 1)
      (fun β Q => h_pou_resolv i (K' + 1) β Q hK') α P
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω := h_comp_succ.memW1p
  -- The eigenvector weak chart partial is a genuine weak partial of the
  -- canonical eigenvector chart component.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k)
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P k
  -- The chosen weak partial of the chart component is also a genuine weak
  -- partial (since the chart component is `W^{1,2}`).
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω)
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_comp_w1p k
  -- Both weak partials are locally integrable.
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial]
    exact Lp.memLp _
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K' 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω) Ω :=
    h_comp_succ.chosenWeakPartial_mem k
  have h_weak_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k)
      ((volume : Measure EuclN).restrict Ω) :=
    h_weak_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae_weak_eq_chosen :
      eigenvectorChartWeakPartial (I := I) (M := M) g r s h_atlas i α P k
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open h_weak h_chosen_weak
      h_weak_loc h_chosen_loc
  -- Express the atom's coercion as `μ *` the chosen weak partial of the chart cpt.
  have h_smul : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial (I := I) (M := M)
          g r s h_atlas i α P k y) := by
    rw [partialLpLimit, eigenvectorChartWeakPartial]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae_atom : (fun y => ((partialLpLimit (I := I) (M := M)
        g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P) Ω y) := by
    filter_upwards [h_smul, h_ae_weak_eq_chosen] with y hy hy_eq
    rw [hy, smul_eq_mul, hy_eq]
  -- Rewrite the atom's wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((partialLpLimit (I := I) (M := M) g r s h_atlas i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P) Ω y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_atom
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P) Ω y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P) Ω) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_chosen_memWkp i.fst.val
  -- `wkpNorm K' 2 (chosenWeakPartial' ...) ≤ wkpNorm (K' + 1) 2 (chart cpt)`.
  have h_chosen_le : wkpNorm (d := Module.finrank ℝ E) K' 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω) Ω
      ≤ wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P) Ω :=
    wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) K' hΩ_open
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) k
  -- The chart-component converter at `(α, P)` and order `K' + 1 ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s h_atlas N CN hCN_nn eN hCN_bd α P (K' + 1) hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step_chain :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P) Ω) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
    mul_le_mul_of_nonneg_left (h_chosen_le.trans h_eig_bd) (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step_absorb :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P) Ω) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
      h_step_chain
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
      h_step_absorb

/-! ## Headline 3 — the cutoff partial-limit atom

The cutoff partial-limit atom
`cutoffPartialLpLimit g r s h_atlas i α P l` is, by definition, `i.fst.val •`
the eigenvector cutoff chart partial `eigenvectorCutoffChartPartialLp`. The
latter is a genuine weak `l`-th partial of the eigenvector cutoff chart
component `tensorL2ChartComponentCutoff g r s vec α P`, by
`eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv`. The cutoff chart
component is itself `W^{K' + 1, 2}` (from the partition-of-unity bridge
applied with the order-`(K' + 1)` partition-of-unity regularity input), so the
chosen weak partial of the cutoff chart component is also a genuine weak
partial, and the two agree almost everywhere. The order-`K'` Sobolev norm of
the cutoff chart partial is therefore at most the order-`(K' + 1)` Sobolev
norm of the cutoff chart component, which in turn — via the input-uniform
cutoff ↔ partition-of-unity bound — is bounded by a single
`(α, P₀, K')`-dependent constant times a finite sum of order-`(K' + 1)`
Sobolev norms of the partition-of-unity chart components of the eigenvector.
Each summand is bounded by the chart-component converter at the corresponding
`(β, Q)` and order `K' + 1 ≤ N`.

The resulting output constant depends on `K'` (and on `α, P₀, N`), packaged as
a function `CN' : ℕ → ℝ` with `0 ≤ CN' K'` for each `K'`. -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family cutoff partial-limit-atom Sobolev bound, derived from a
β-uniform order-`N` chart-component Sobolev hypothesis.**

The cutoff partial-limit atom
`cutoffPartialLpLimit g r s h_atlas i α P l` — `i.fst.val` times the
eigenvector cutoff chart partial — admits, at every order `K'` with
`K' + 1 ≤ N` and every eigenbasis index `i`, an iterated Sobolev bound on the
chart-`α` target of the form `ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`, with `CN' K' ≥ 0`.
The constant `CN' K'` depends on `(α, P₀, K', N)` and on the input
chart-component constant `CN`, but not on the eigenbasis index `i`.

The eigenvector cutoff chart partial is a genuine weak `l`-th partial of the
eigenvector cutoff chart component
(`eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv`). Combining
`HasWeakPartialDeriv.ae_eq` with the chosen weak partial — together with the
input-uniform quantitative cutoff ↔ partition-of-unity iterated-Sobolev bound
`wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform` and the chart-component
converter at order `K' + 1 ≤ N` — assembles the bound. -/
theorem eigenvector_cutoffPartialLpLimit_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ (CN' : ℕ → ℝ), (∀ K', 0 ≤ CN' K') ∧
      ∀ (K' : ℕ), K' + 1 ≤ N →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (l : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
                g r s h_atlas i α P₀ l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  -- The input-uniform cutoff ↔ partition-of-unity bound, at every order `k`.
  -- The constant produced by the uniform bridge is independent of `u`.
  set Cu : ℕ → ℝ := fun k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose with hCu_def
  have hCu_nn : ∀ k, 0 ≤ Cu k := fun k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose_spec.1
  have hCu_bd : ∀ k (u : TensorL2 r s g),
      (∀ (β : M) (Q : TensorCompIdx (E := E) r s),
        MemWkp (d := d) k 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)) →
      wkpNorm (d := d) k 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cu k) *
          (∑ β ∈ S,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := d) k 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    u β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) := fun k u h_pou_u =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose_spec.2 u h_pou_u
  -- Output constant per `K'`: `Cu (K' + 1) * |S| * |TensorCompIdx| * CN`.
  set CT : ℕ := S.card * (Finset.univ : Finset (TensorCompIdx (E := E) r s)).card
    with hCT_def
  set CN' : ℕ → ℝ := fun K' => Cu (K' + 1) * (CT : ℝ) * CN
    with hCN'_def
  have hCN'_nn : ∀ K', 0 ≤ CN' K' := fun K' => by
    rw [hCN'_def]
    have hCT_nn : (0 : ℝ) ≤ (CT : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ Cu (K' + 1) * (CT : ℝ) :=
      mul_nonneg (hCu_nn _) hCT_nn
    exact mul_nonneg h1 hCN_nn
  refine ⟨CN', hCN'_nn, ?_⟩
  intro K' hK' i l
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local (I := I) (M := M) g r s h_atlas i
  -- The eigenvector chart components are `MemWkp (K' + 1) 2` at every `(β, Q)`.
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp_local
      (I := I) (M := M) g r s h_atlas i (K' + 1)
      (fun β' Q' => h_pou_resolv i (K' + 1) β' Q' hK') β Q
  -- The cutoff chart component is `MemWkp (K' + 1) 2` at `(α, P₀)` via the
  -- non-uniform bridge — needed to invoke `chosenWeakPartial'_isWeakPartial_of_mem`.
  -- (We use the non-uniform bridge for membership; the uniform one is reserved
  -- for the explicit norm bound.)
  have h_cutoff_succ : MemWkp (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ (K' + 1)
      h_pou_eigen
  have h_cutoff_w1p : DeGiorgi.MemW1p (d := d) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    h_cutoff_succ.memW1p
  -- The eigenvector cutoff chart partial is a genuine weak `l`-th partial of
  -- the eigenvector cutoff chart component.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := d) l
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv (I := I) (M := M)
      g r s h_atlas i α P₀ l
  -- The chosen weak partial of the cutoff chart component is also a genuine
  -- weak partial.
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := d) l
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_cutoff_w1p l
  -- Both weak partials are locally integrable.
  have h_weak_memLp : MemLp
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict Ω) := Lp.memLp _
  have h_chosen_memWkp : MemWkp (d := d) K' 2
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω) Ω :=
    h_cutoff_succ.chosenWeakPartial_mem l
  have h_weak_loc : LocallyIntegrable
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      ((volume : Measure EuclN).restrict Ω) :=
    h_weak_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae_weak_eq_chosen :
      ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open h_weak h_chosen_weak
      h_weak_loc h_chosen_loc
  -- Express the atom's coercion as `μ *` (chosen weak partial of cutoff chart cpt).
  have h_smul : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((eigenvectorCutoffChartPartialLp (I := I) (M := M)
          g r s h_atlas i α P₀ l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [cutoffPartialLpLimit]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae_atom : (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        chosenWeakPartial' (d := d) 2 l
          (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) := by
    filter_upwards [h_smul, h_ae_weak_eq_chosen] with y hy hy_eq
    rw [hy, smul_eq_mul, hy_eq]
  -- Rewrite the atom's wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := d) K' 2
      (fun y => ((cutoffPartialLpLimit (I := I) (M := M)
        g r s h_atlas i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := d) K' 2
        (fun y => i.fst.val *
          chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) Ω :=
    wkpNorm_congr_ae (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_atom
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := d) K' 2
      (fun y => i.fst.val *
        chosenWeakPartial' (d := d) 2 l
          (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω :=
    wkpNorm_const_smul (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_chosen_memWkp i.fst.val
  -- `wkpNorm K' 2 (chosenWeakPartial' ...) ≤ wkpNorm (K' + 1) 2 (cutoff chart cpt)`.
  have h_chosen_le : wkpNorm (d := d) K' 2
      (chosenWeakPartial' (d := d) 2 l
        (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
      ≤ wkpNorm (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    wkpNorm_chosenWeakPartial_le (d := d) K' hΩ_open
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) l
  -- Bound the cutoff chart component norm by the double sum via the uniform
  -- cutoff bridge.
  have h_cutoff_le : wkpNorm (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu (K' + 1)) *
        (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := d) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) :=
    hCu_bd (K' + 1) (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i)
      h_pou_eigen
  -- The eigenvector chart-component bound at every `(β, Q)` and order `K' + 1`.
  have h_each_cpt_le : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      wkpNorm (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    intro β Q
    exact eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s h_atlas N CN hCN_nn eN hCN_bd β Q (K' + 1) hK' i
  -- Bound the double sum by `|S| * |TensorCompIdx| * (CN * μ⁻¹^eN * ‖vec‖)`.
  set RHS_each : ℝ≥0∞ := ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
    ENNReal.ofReal ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
    with hRHS_each_def
  have h_double_sum_le :
      (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := d) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      ≤ (CT : ℝ≥0∞) * RHS_each := by
    calc (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := d) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ∑ _β ∈ S, ∑ _Q : TensorCompIdx (E := E) r s, RHS_each :=
          Finset.sum_le_sum (fun β _hβ =>
            Finset.sum_le_sum (fun Q _hQ => h_each_cpt_le β Q))
      _ = (CT : ℝ≥0∞) * RHS_each := by
          simp only [Finset.sum_const, hCT_def, nsmul_eq_mul, Nat.cast_mul]
          ring
  -- Combine the cutoff bound and the chart-cpt sum bound.
  have h_cutoff_le_final : wkpNorm (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each) := by
    refine h_cutoff_le.trans ?_
    exact mul_le_mul_of_nonneg_left h_double_sum_le (zero_le _)
  -- Now assemble: `wkpNorm K' 2 atom = ‖μ‖ₑ * wkpNorm K' 2 (chosenWeakPartial')`
  -- ≤ ‖μ‖ₑ * wkpNorm (K' + 1) 2 (cutoff chart cpt) ≤ ‖μ‖ₑ * (Cu(K'+1) * CT * RHS_each).
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  -- Chain: bound the chosenWeakPartial norm.
  have h_step_chain :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each)) :=
    mul_le_mul_of_nonneg_left (h_chosen_le.trans h_cutoff_le_final) (zero_le _)
  -- Rearrange `μ * Cu * CT * RHS_each` into the headline form.
  -- RHS_each := ENNReal.ofReal (CN * μ⁻¹^eN) * ENNReal.ofReal ‖vec‖.
  -- Goal RHS:
  -- ENNReal.ofReal (CN' K' * μ⁻¹^eN) * ENNReal.ofReal ‖vec‖
  -- = ENNReal.ofReal (Cu(K'+1) * CT * CN * μ⁻¹^eN) * ENNReal.ofReal ‖vec‖.
  -- We want to show:
  -- μ * (Cu(K'+1) * (CT : ℝ≥0∞) * RHS_each) ≤ goal_RHS.
  -- Use `μ · μ⁻¹^eN ≤ μ⁻¹^eN` and pull the constants together.
  have hCu_nn_K1 : 0 ≤ Cu (K' + 1) := hCu_nn _
  have hCT_real_nn : (0 : ℝ) ≤ (CT : ℝ) := Nat.cast_nonneg _
  have hRHS_each_eq :
      RHS_each = ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := rfl
  -- Factor the constants: `μ * Cu * CT * (ofReal (CN * μ⁻¹^eN)) = ofReal (μ * (Cu * CT * CN) * μ⁻¹^eN)`.
  -- We separate the algebra in ℝ≥0∞ via `ENNReal.ofReal_mul` (requires nonneg).
  have h_packCT : (CT : ℝ≥0∞) = ENNReal.ofReal (CT : ℝ) := by
    simp [hCT_def, ENNReal.ofReal_natCast]
  have h_pack_left :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (Cu (K' + 1)) *
          ((CT : ℝ≥0∞) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖))) =
      ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    rw [h_packCT]
    have hμ_nn : (0 : ℝ) ≤ i.fst.val := hμ_pos.le
    have hCN_pow_nn : (0 : ℝ) ≤ CN * (i.fst.val)⁻¹ ^ eN := by
      have hinv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      exact mul_nonneg hCN_nn (pow_nonneg hinv_nn _)
    have hμCu_nn : (0 : ℝ) ≤ i.fst.val * Cu (K' + 1) :=
      mul_nonneg hμ_nn hCu_nn_K1
    have hμCuCT_nn : (0 : ℝ) ≤ i.fst.val * Cu (K' + 1) * (CT : ℝ) :=
      mul_nonneg hμCu_nn hCT_real_nn
    have hμCu_real_eq :
        ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu (K' + 1)) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1)) :=
      (ENNReal.ofReal_mul hμ_nn).symm
    have hCT_real_eq :
        ENNReal.ofReal (i.fst.val * Cu (K' + 1)) * ENNReal.ofReal (CT : ℝ) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) :=
      (ENNReal.ofReal_mul hμCu_nn).symm
    have hCN_pow_eq :
        ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
            ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) :=
      (ENNReal.ofReal_mul hμCuCT_nn).symm
    calc
      ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu (K' + 1)) *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)))
          = (ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu (K' + 1))) *
              (ENNReal.ofReal (CT : ℝ) *
                (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                  ENNReal.ofReal
                    ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1)) *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)) := by
            rw [hμCu_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu (K' + 1)) * ENNReal.ofReal (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) := by
            rw [hCT_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
              ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
            rw [hCN_pow_eq]
  -- Bound the packed scalar by `CN' K' * μ⁻¹^eN = Cu(K'+1) * CT * CN * μ⁻¹^eN`.
  have h_scalar_le :
      i.fst.val * Cu (K' + 1) * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) ≤
        CN' K' * (i.fst.val)⁻¹ ^ eN := by
    rw [hCN'_def]
    -- LHS = μ * Cu(K'+1) * CT * CN * μ⁻¹^eN, reorder to CN * (Cu(K'+1) * CT) * (μ * μ⁻¹^eN).
    have h_reorder :
        i.fst.val * Cu (K' + 1) * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) =
          (Cu (K' + 1) * (CT : ℝ) * CN) * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by
      ring
    rw [h_reorder]
    -- RHS = (Cu(K'+1) * CT * CN) * μ⁻¹^eN.
    have hCC_nn : 0 ≤ Cu (K' + 1) * (CT : ℝ) * CN := by
      have h1 : 0 ≤ Cu (K' + 1) * (CT : ℝ) := mul_nonneg hCu_nn_K1 hCT_real_nn
      exact mul_nonneg h1 hCN_nn
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCC_nn
  -- Convert the scalar inequality to an ENNReal inequality on the packed form.
  have h_packed_le :
      ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖
      ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    exact ENNReal.ofReal_le_ofReal h_scalar_le
  -- Final chain.
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each)) := h_step_chain
    _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := h_pack_left
    _ ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := h_packed_le

/-! ## Chart-locality-free twins

The headline atom converters above are keyed on the chart-selection witness
`HasLocallyConstantChartAt`. We now build the chart-locality-free twins, re-keying
the eigenbasis vector onto the intrinsic compact-operator spectral theorem
(`tensorResolventEigenbasisVec_ofCompact` applied to
`tensorResolventL2_isCompactOperator_intrinsic`) and re-keying every concrete
eigenvector chart object onto its `_unconditional` form. The originals above are
kept intact. -/

/-- Chart-locality-free twin of `vec_norm_eq_one_local`. -/
private lemma vec_norm_eq_one_local_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M) g r s)
        i‖ = 1 :=
  (tensorResolventEigenbasisVec_ofCompact_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
      g r s)).norm_eq_one i

/-- Chart-locality-free twin of `eigenval_pos_local`. -/
private lemma eigenval_pos_local_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    0 < i.fst.val :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local_unconditional
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).1

/-- Chart-locality-free twin of `eigenval_le_one_local`. -/
private lemma eigenval_le_one_local_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i.fst.val ≤ 1 :=
  (tensorResolvent_eigenvalue_mem_unit_interval (I := I) (M := M) g r s
    (tensorResolventEigenbasisVec_ofCompact_mem (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)
    (by
      intro h_zero
      have h_norm := vec_norm_eq_one_local_unconditional
        (I := I) (M := M) g r s i
      rw [h_zero, norm_zero] at h_norm
      exact one_ne_zero h_norm.symm)).2

/-- Chart-locality-free twin of `eigenvectorVec_pou_memWkp_local`. -/
private lemma eigenvectorVec_pou_memWkp_local_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) (N : ℕ)
    (h_pou : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := Module.finrank ℝ E) N 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) N 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  have h_res := h_pou β Q
  have h_chart_eq := eigenvector_chartComponent_eq_unconditional (I := I) (M := M)
    g r s i β Q
  have h_ae : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i) β Q :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
    have h_smul := Lp.coeFn_smul (i.fst.val)⁻¹
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) β Q)
    have h_smul' : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) β Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        =ᵐ[chartL2Measure (I := I) (M := M) β]
        (fun y => (i.fst.val)⁻¹ •
          ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) := by
      rw [h_chart_eq]
      exact h_smul
    filter_upwards [h_smul'] with y hy
    rw [hy, smul_eq_mul]
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mpr
    (MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_res (i.fst.val)⁻¹)

/-- Chart-locality-free twin of
`eigenvector_componentLpLimit_perK_from_uniform_β`. -/
theorem eigenvector_componentLpLimit_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
              g r s i α P :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i P
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local_unconditional (I := I) (M := M) g r s i
  -- Express the atom's coercion as `μ *` the eigenvector chart component.
  have h_smul : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [componentLpLimit_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae : (fun y => ((componentLpLimit_unconditional (I := I) (M := M)
        g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P y) := by
    filter_upwards [h_smul] with y hy
    rw [hy, smul_eq_mul]
    rfl
  -- Regularity of the eigenvector chart component at order `K'`, used by
  -- `wkpNorm_const_smul`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω :=
    eigenvectorVec_pou_memWkp_local_unconditional (I := I) (M := M) g r s i K'
      (fun β Q => h_pou_resolv i K' β Q hK') α P
  -- Rewrite the wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((componentLpLimit_unconditional (I := I) (M := M) g r s i α P :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The chart-component converter at `(α, P)` and order `K' ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd α P K' hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step2 :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖) :=
      h_step1
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
      h_step2

/-- Chart-locality-free twin of
`eigenvector_partialLpLimit_perK_from_uniform_β`. -/
theorem eigenvector_partialLpLimit_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (P : TensorCompIdx (E := E) r s)
        (k : Fin (Module.finrank ℝ E)),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
              g r s i α P k :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  intro K' hK' i P k
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local_unconditional (I := I) (M := M) g r s i
  -- Order-`(K' + 1)` regularity of the eigenvector chart component at `(α, P)`.
  have h_comp_succ : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω :=
    eigenvectorVec_pou_memWkp_local_unconditional (I := I) (M := M) g r s i (K' + 1)
      (fun β Q => h_pou_resolv i (K' + 1) β Q hK') α P
  have h_comp_w1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω := h_comp_succ.memW1p
  -- The eigenvector weak chart partial is a genuine weak partial of the
  -- canonical eigenvector chart component.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k)
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω :=
    eigenvectorChartWeakPartial_hasWeakPartialDeriv_unconditional (I := I) (M := M)
      g r s i α P k
  -- The chosen weak partial of the chart component is also a genuine weak
  -- partial (since the chart component is `W^{1,2}`).
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := Module.finrank ℝ E) k
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω)
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_comp_w1p k
  -- Both weak partials are locally integrable.
  have h_weak_memLp : MemLp
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k) 2
      ((volume : Measure EuclN).restrict Ω) := by
    rw [eigenvectorChartWeakPartial_unconditional]
    exact Lp.memLp _
  have h_chosen_memWkp : MemWkp (d := Module.finrank ℝ E) K' 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω) Ω :=
    h_comp_succ.chosenWeakPartial_mem k
  have h_weak_loc : LocallyIntegrable
      (eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
        g r s i α P k)
      ((volume : Measure EuclN).restrict Ω) :=
    h_weak_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae_weak_eq_chosen :
      eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open h_weak h_chosen_weak
      h_weak_loc h_chosen_loc
  -- Express the atom's coercion as `μ *` the chosen weak partial of the chart cpt.
  have h_smul : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        eigenvectorChartWeakPartial_unconditional (I := I) (M := M)
          g r s i α P k y) := by
    rw [partialLpLimit_unconditional, eigenvectorChartWeakPartial_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae_atom : (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P) Ω y) := by
    filter_upwards [h_smul, h_ae_weak_eq_chosen] with y hy hy_eq
    rw [hy, smul_eq_mul, hy_eq]
  -- Rewrite the atom's wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((partialLpLimit_unconditional (I := I) (M := M)
        g r s i α P k :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P) Ω y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_atom
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P) Ω y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P) Ω) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_chosen_memWkp i.fst.val
  -- `wkpNorm K' 2 (chosenWeakPartial' ...) ≤ wkpNorm (K' + 1) 2 (chart cpt)`.
  have h_chosen_le : wkpNorm (d := Module.finrank ℝ E) K' 2
      (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω) Ω
      ≤ wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P) Ω :=
    wkpNorm_chosenWeakPartial_le (d := Module.finrank ℝ E) K' hΩ_open
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) k
  -- The chart-component converter at `(α, P)` and order `K' + 1 ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd α P (K' + 1) hK' i
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step_chain :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P) Ω) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left (h_chosen_le.trans h_eig_bd) (zero_le _)
  have h_mul_assoc :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖) =
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul hμ_pos.le]
  have h_step_absorb :
      ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    refine ENNReal.ofReal_le_ofReal ?_
    have h_reorder : i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)
        = CN * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by ring
    rw [h_reorder]
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (chosenWeakPartial' (d := Module.finrank ℝ E) 2 k
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P) Ω) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖) :=
      h_step_chain
    _ = ENNReal.ofReal (i.fst.val * (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
      h_mul_assoc
    _ ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ :=
      h_step_absorb

/-- Chart-locality-free twin of
`eigenvector_cutoffPartialLpLimit_perK_from_uniform_β`. -/
theorem eigenvector_cutoffPartialLpLimit_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖)
    (h_pou_resolv : ∀ (i : TensorEigenIdx (I := I) (M := M) g r s) (K' : ℕ)
        (β : M) (Q : TensorCompIdx (E := E) r s),
      K' ≤ N →
      MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β))
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∃ (CN' : ℕ → ℝ), (∀ K', 0 ≤ CN' K') ∧
      ∀ (K' : ℕ), K' + 1 ≤ N →
        ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
          (l : Fin (Module.finrank ℝ E)),
          wkpNorm (d := Module.finrank ℝ E) K' 2
              (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
                g r s i α P₀ l :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) α)
            ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖ := by
  classical
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  set d : ℕ := Module.finrank ℝ E with hd_def
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  set S : Finset M := transportChartCenters (I := I) (M := M) α with hS_def
  -- The input-uniform cutoff ↔ partition-of-unity bound, at every order `k`.
  -- The constant produced by the uniform bridge is independent of `u`.
  set Cu : ℕ → ℝ := fun k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose with hCu_def
  have hCu_nn : ∀ k, 0 ≤ Cu k := fun k =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose_spec.1
  have hCu_bd : ∀ k (u : TensorL2 r s g),
      (∀ (β : M) (Q : TensorCompIdx (E := E) r s),
        MemWkp (d := d) k 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s u β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β)) →
      wkpNorm (d := d) k 2
          (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M)
            g r s u α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (Cu k) *
          (∑ β ∈ S,
            ∑ Q : TensorCompIdx (E := E) r s,
              wkpNorm (d := d) k 2
                (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                    u β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                  EuclN → ℝ) y)
                (chartTargetEuclid (I := I) (M := M) β)) := fun k u h_pou_u =>
    (wkpNorm_tensorL2ChartComponentCutoff_le_of_pou_uniform
      (I := I) (M := M) g r s α P₀ k).choose_spec.2 u h_pou_u
  -- Output constant per `K'`: `Cu (K' + 1) * |S| * |TensorCompIdx| * CN`.
  set CT : ℕ := S.card * (Finset.univ : Finset (TensorCompIdx (E := E) r s)).card
    with hCT_def
  set CN' : ℕ → ℝ := fun K' => Cu (K' + 1) * (CT : ℝ) * CN
    with hCN'_def
  have hCN'_nn : ∀ K', 0 ≤ CN' K' := fun K' => by
    rw [hCN'_def]
    have hCT_nn : (0 : ℝ) ≤ (CT : ℝ) := Nat.cast_nonneg _
    have h1 : 0 ≤ Cu (K' + 1) * (CT : ℝ) :=
      mul_nonneg (hCu_nn _) hCT_nn
    exact mul_nonneg h1 hCN_nn
  refine ⟨CN', hCN'_nn, ?_⟩
  intro K' hK' i l
  have hμ_pos : 0 < i.fst.val :=
    eigenval_pos_local_unconditional (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 :=
    eigenval_le_one_local_unconditional (I := I) (M := M) g r s i
  -- The eigenvector chart components are `MemWkp (K' + 1) 2` at every `(β, Q)`.
  have h_pou_eigen : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      MemWkp (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β) :=
    fun β Q => eigenvectorVec_pou_memWkp_local_unconditional
      (I := I) (M := M) g r s i (K' + 1)
      (fun β' Q' => h_pou_resolv i (K' + 1) β' Q' hK') β Q
  -- The cutoff chart component is `MemWkp (K' + 1) 2` at `(α, P₀)` via the
  -- non-uniform bridge — needed to invoke `chosenWeakPartial'_isWeakPartial_of_mem`.
  -- (We use the non-uniform bridge for membership; the uniform one is reserved
  -- for the explicit norm bound.)
  have h_cutoff_succ : MemWkp (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    tensorL2ChartComponentCutoff_memWkp_of_pou (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i) α P₀ (K' + 1)
      h_pou_eigen
  have h_cutoff_w1p : DeGiorgi.MemW1p (d := d) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    h_cutoff_succ.memW1p
  -- The eigenvector cutoff chart partial is a genuine weak `l`-th partial of
  -- the eigenvector cutoff chart component.
  have h_weak : DeGiorgi.HasWeakPartialDeriv (d := d) l
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    eigenvectorCutoffChartPartialLp_hasWeakPartialDeriv_unconditional (I := I) (M := M)
      g r s i α P₀ l
  -- The chosen weak partial of the cutoff chart component is also a genuine
  -- weak partial.
  have h_chosen_weak : DeGiorgi.HasWeakPartialDeriv (d := d) l
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω)
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem h_cutoff_w1p l
  -- Both weak partials are locally integrable.
  have h_weak_memLp : MemLp
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) 2
      ((volume : Measure EuclN).restrict Ω) := Lp.memLp _
  have h_chosen_memWkp : MemWkp (d := d) K' 2
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω) Ω :=
    h_cutoff_succ.chosenWeakPartial_mem l
  have h_weak_loc : LocallyIntegrable
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
      ((volume : Measure EuclN).restrict Ω) :=
    h_weak_memLp.locallyIntegrable (by norm_num)
  have h_chosen_loc : LocallyIntegrable
      (chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω)
      ((volume : Measure EuclN).restrict Ω) :=
    h_chosen_memWkp.memLp.locallyIntegrable (by norm_num)
  have h_ae_weak_eq_chosen :
      ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
        =ᵐ[(volume : Measure EuclN).restrict Ω]
      chosenWeakPartial' (d := d) 2 l
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ_open h_weak h_chosen_weak
      h_weak_loc h_chosen_loc
  -- Express the atom's coercion as `μ *` (chosen weak partial of cutoff chart cpt).
  have h_smul : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y => i.fst.val •
        ((eigenvectorCutoffChartPartialLp_unconditional (I := I) (M := M)
          g r s i α P₀ l :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) := by
    rw [cutoffPartialLpLimit_unconditional]
    exact Lp.coeFn_smul i.fst.val _
  have h_ae_atom : (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => i.fst.val *
        chosenWeakPartial' (d := d) 2 l
          (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) := by
    filter_upwards [h_smul, h_ae_weak_eq_chosen] with y hy hy_eq
    rw [hy, smul_eq_mul, hy_eq]
  -- Rewrite the atom's wkpNorm through the a.e. equality.
  have h_norm_eq : wkpNorm (d := d) K' 2
      (fun y => ((cutoffPartialLpLimit_unconditional (I := I) (M := M)
        g r s i α P₀ l :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := d) K' 2
        (fun y => i.fst.val *
          chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) Ω :=
    wkpNorm_congr_ae (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae_atom
  -- Factor the scalar out.
  have h_smul_eq : wkpNorm (d := d) K' 2
      (fun y => i.fst.val *
        chosenWeakPartial' (d := d) 2 l
          (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i) α P₀ :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω :=
    wkpNorm_const_smul (d := d)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_chosen_memWkp i.fst.val
  -- `wkpNorm K' 2 (chosenWeakPartial' ...) ≤ wkpNorm (K' + 1) 2 (cutoff chart cpt)`.
  have h_chosen_le : wkpNorm (d := d) K' 2
      (chosenWeakPartial' (d := d) 2 l
        (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
      ≤ wkpNorm (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) α P₀ :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω :=
    wkpNorm_chosenWeakPartial_le (d := d) K' hΩ_open
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) l
  -- Bound the cutoff chart component norm by the double sum via the uniform
  -- cutoff bridge.
  have h_cutoff_le : wkpNorm (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu (K' + 1)) *
        (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
          wkpNorm (d := d) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i) β Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)) :=
    hCu_bd (K' + 1) (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i)
      h_pou_eigen
  -- The eigenvector chart-component bound at every `(β, Q)` and order `K' + 1`.
  have h_each_cpt_le : ∀ (β : M) (Q : TensorCompIdx (E := E) r s),
      wkpNorm (d := d) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i) β Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    intro β Q
    exact eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q (K' + 1) hK' i
  -- Bound the double sum by `|S| * |TensorCompIdx| * (CN * μ⁻¹^eN * ‖vec‖)`.
  set RHS_each : ℝ≥0∞ := ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
    ENNReal.ofReal ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i‖
    with hRHS_each_def
  have h_double_sum_le :
      (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
        wkpNorm (d := d) (K' + 1) 2
          (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
              (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i) β Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
          (chartTargetEuclid (I := I) (M := M) β))
      ≤ (CT : ℝ≥0∞) * RHS_each := by
    calc (∑ β ∈ S, ∑ Q : TensorCompIdx (E := E) r s,
            wkpNorm (d := d) (K' + 1) 2
              (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                      g r s) i) β Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
              (chartTargetEuclid (I := I) (M := M) β))
        ≤ ∑ _β ∈ S, ∑ _Q : TensorCompIdx (E := E) r s, RHS_each :=
          Finset.sum_le_sum (fun β _hβ =>
            Finset.sum_le_sum (fun Q _hQ => h_each_cpt_le β Q))
      _ = (CT : ℝ≥0∞) * RHS_each := by
          simp only [Finset.sum_const, hCT_def, nsmul_eq_mul, Nat.cast_mul]
          ring
  -- Combine the cutoff bound and the chart-cpt sum bound.
  have h_cutoff_le_final : wkpNorm (d := d) (K' + 1) 2
      (fun y => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) α P₀ :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) Ω
      ≤ ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each) := by
    refine h_cutoff_le.trans ?_
    exact mul_le_mul_of_nonneg_left h_double_sum_le (zero_le _)
  -- Now assemble: `wkpNorm K' 2 atom = ‖μ‖ₑ * wkpNorm K' 2 (chosenWeakPartial')`
  -- ≤ ‖μ‖ₑ * wkpNorm (K' + 1) 2 (cutoff chart cpt) ≤ ‖μ‖ₑ * (Cu(K'+1) * CT * RHS_each).
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  -- Chain: bound the chosenWeakPartial norm.
  have h_step_chain :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each)) :=
    mul_le_mul_of_nonneg_left (h_chosen_le.trans h_cutoff_le_final) (zero_le _)
  -- Rearrange `μ * Cu * CT * RHS_each` into the headline form.
  have hCu_nn_K1 : 0 ≤ Cu (K' + 1) := hCu_nn _
  have hCT_real_nn : (0 : ℝ) ≤ (CT : ℝ) := Nat.cast_nonneg _
  have hRHS_each_eq :
      RHS_each = ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := rfl
  -- Factor the constants.
  have h_packCT : (CT : ℝ≥0∞) = ENNReal.ofReal (CT : ℝ) := by
    simp [hCT_def, ENNReal.ofReal_natCast]
  have h_pack_left :
      ENNReal.ofReal i.fst.val *
        (ENNReal.ofReal (Cu (K' + 1)) *
          ((CT : ℝ≥0∞) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖))) =
      ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    rw [h_packCT]
    have hμ_nn : (0 : ℝ) ≤ i.fst.val := hμ_pos.le
    have hCN_pow_nn : (0 : ℝ) ≤ CN * (i.fst.val)⁻¹ ^ eN := by
      have hinv_nn : (0 : ℝ) ≤ (i.fst.val)⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
      exact mul_nonneg hCN_nn (pow_nonneg hinv_nn _)
    have hμCu_nn : (0 : ℝ) ≤ i.fst.val * Cu (K' + 1) :=
      mul_nonneg hμ_nn hCu_nn_K1
    have hμCuCT_nn : (0 : ℝ) ≤ i.fst.val * Cu (K' + 1) * (CT : ℝ) :=
      mul_nonneg hμCu_nn hCT_real_nn
    have hμCu_real_eq :
        ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu (K' + 1)) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1)) :=
      (ENNReal.ofReal_mul hμ_nn).symm
    have hCT_real_eq :
        ENNReal.ofReal (i.fst.val * Cu (K' + 1)) * ENNReal.ofReal (CT : ℝ) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) :=
      (ENNReal.ofReal_mul hμCu_nn).symm
    have hCN_pow_eq :
        ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
            ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) =
          ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) :=
      (ENNReal.ofReal_mul hμCuCT_nn).symm
    calc
      ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (Cu (K' + 1)) *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                      g r s) i‖)))
          = (ENNReal.ofReal i.fst.val * ENNReal.ofReal (Cu (K' + 1))) *
              (ENNReal.ofReal (CT : ℝ) *
                (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                  ENNReal.ofReal
                    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                        g r s) i‖)) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1)) *
            (ENNReal.ofReal (CT : ℝ) *
              (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
                ENNReal.ofReal
                  ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                    (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                      g r s) i‖)) := by
            rw [hμCu_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu (K' + 1)) * ENNReal.ofReal (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖) := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i‖) := by
            rw [hCT_real_eq]
      _ = (ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ)) *
              ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
            ring
      _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
            rw [hCN_pow_eq]
  -- Bound the packed scalar by `CN' K' * μ⁻¹^eN = Cu(K'+1) * CT * CN * μ⁻¹^eN`.
  have h_scalar_le :
      i.fst.val * Cu (K' + 1) * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) ≤
        CN' K' * (i.fst.val)⁻¹ ^ eN := by
    rw [hCN'_def]
    have h_reorder :
        i.fst.val * Cu (K' + 1) * (CT : ℝ) * (CN * (i.fst.val)⁻¹ ^ eN) =
          (Cu (K' + 1) * (CT : ℝ) * CN) * (i.fst.val * (i.fst.val)⁻¹ ^ eN) := by
      ring
    rw [h_reorder]
    have hCC_nn : 0 ≤ Cu (K' + 1) * (CT : ℝ) * CN := by
      have h1 : 0 ≤ Cu (K' + 1) * (CT : ℝ) := mul_nonneg hCu_nn_K1 hCT_real_nn
      exact mul_nonneg h1 hCN_nn
    exact mul_le_mul_of_nonneg_left
      (mu_mul_inv_pow_le_inv_pow_local hμ_pos hμ_le_one eN) hCC_nn
  -- Convert the scalar inequality to an ENNReal inequality on the packed form.
  have h_packed_le :
      ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
          (CN * (i.fst.val)⁻¹ ^ eN)) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖
      ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ := by
    refine mul_le_mul_of_nonneg_right ?_ (zero_le _)
    exact ENNReal.ofReal_le_ofReal h_scalar_le
  -- Final chain.
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := d) K' 2
          (chosenWeakPartial' (d := d) 2 l
            (fun y' => ((tensorL2ChartComponentCutoff (I := I) (M := M) g r s
                (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                    g r s) i) α P₀ :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y') Ω) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (Cu (K' + 1)) * ((CT : ℝ≥0∞) * RHS_each)) := h_step_chain
    _ = ENNReal.ofReal (i.fst.val * Cu (K' + 1) * (CT : ℝ) *
            (CN * (i.fst.val)⁻¹ ^ eN)) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := h_pack_left
    _ ≤ ENNReal.ofReal (CN' K' * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
              (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                g r s) i‖ := h_packed_le

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
