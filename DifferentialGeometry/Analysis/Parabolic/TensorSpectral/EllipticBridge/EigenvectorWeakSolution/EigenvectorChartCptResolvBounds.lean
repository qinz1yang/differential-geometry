import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorDifferentiatedRHS
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorPouWkpNormTwins
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.SmoothApprox
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartRHSEpNorm

/-!
# Eigenbasis-uniform per-`K'`-family atom converters for the chart-component and
# resolvent-chart-component Sobolev bounds

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an order ceiling
`N : ℕ`, an eigenbasis-uniform Sobolev hypothesis `hCN_bd` on the eigenvector
chart components at order `N` — a single nonnegative constant `CN`, an exponent
`eN`, with the bound holding β-uniformly over every base point and component
multi-index — this file ships three per-`K'`-family atom converters needed to
populate the per-`K`-family atom families of the level-`(m+1)` carrier
hypothesis bundle.

## The three atoms

* `eigenvector_chartComponent_perK_from_uniform_β` — chart cpt at `(α, P₀)` at
  order `K' ≤ N`, directly from `hCN_bd` via `wkpNorm_mono_order`.
* `eigenvector_resolventHigh_perK_from_uniform_β` — the high-order resolvent
  chart-component atom at `(β, Q)` at order `K' + 1` with `K' + 1 ≤ N`, via
  the rescale identity `tensorL2ChartComponent_smul` applied to
  `eigenvector_chartComponent_eq` and `wkpNorm_const_smul`.
* `eigenvector_resolventLow_perK_from_uniform_β` — the low-order resolvent
  chart-component atom at `(β, Q)` at order `K' ≤ N`, the same rescale
  argument at order `K'` instead of `K' + 1`.

## The rescale identity

By `resolventL2_eq_mul_eigenvector` (rearranged from
`eigenvector_eq_resolvent_smul`),

```
TensorH1ComplToTensorL2 (eigenvectorResolvent g r s h_atlas i)
  = i.fst.val • tensorResolventEigenbasisVec h_atlas i.
```

Applying the continuous linear chart-component map preserves scalar
multiplication (`tensorL2ChartComponent_smul`), so at every base point `β` and
component multi-index `Q`,

```
tensorL2ChartComponent g r s (TensorH1ComplToTensorL2 (eigenvectorResolvent …))
    β Q
  = (i.fst.val) • tensorL2ChartComponent g r s
      (tensorResolventEigenbasisVec h_atlas i) β Q.
```

Passing to `coeFn` through `Lp.coeFn_smul` exhibits the resolvent chart
component, as an `EuclN → ℝ` function, as almost-everywhere equal to
`i.fst.val` times the eigenvector chart component `eigenvectorChartComponentFun
g r s h_atlas i β Q`. The Sobolev norm is then scalar-homogeneous through
`wkpNorm_const_smul`, producing the resolvent chart-component bound as
`‖i.fst.val‖ = i.fst.val` (positivity) times the eigenvector chart-component
bound. The resolvent eigenvalue `μ := i.fst.val` lies in `(0, 1]`, so
`μ · μ⁻¹^eN ≤ μ⁻¹^eN`; the exponent in the output stays at `eN`.

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

/-! ## File-local Borel-space instances on `E` and `M`

The measurable structure on `E` and `M` is the Borel σ-algebra coming from the
topology; it is installed locally so it does not leak onto the public
signatures. -/

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ## Positivity and unit-interval membership of the resolvent eigenvalue

The resolvent eigenvalue `μ := i.fst.val` of any eigenbasis index `i` lies in
the unit interval `(0, 1]`: a nontrivial eigenspace contains a non-zero
eigenvector, and every resolvent eigenvalue with a non-zero eigenvector lies in
`Ioc 0 1`. -/

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

/-! ## Headline 1 — chart-component bound at order `K' ≤ N`

The first of the three converters: from a β-uniform chart-component Sobolev
bound at the ceiling order `N`, derive a chart-component bound at any lower
order `K' ≤ N`, with the same constant and exponent. The proof is a single
application of `wkpNorm_mono_order` followed by the input bound `hCN_bd` at
`(α, P₀)`. -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family eigenvector chart-component Sobolev bound, derived from a
β-uniform order-`N` chart-component Sobolev hypothesis.**

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an order ceiling `N`,
a constant `CN ≥ 0` and exponent `eN`, and a β-uniform hypothesis `hCN_bd` that
the order-`N` Sobolev norm of every eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i α P₀` on the chart-`α` target is
bounded by `ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) * ENNReal.ofReal
‖tensorResolventEigenbasisVec h_atlas i‖`, the corresponding bound holds at any
lower order `K' ≤ N`, with the same constant `CN` and exponent `eN`.

The proof is monotonicity of `wkpNorm` in the regularity order, followed by the
input bound at `(α, P₀)`. -/
theorem eigenvector_chartComponent_perK_from_uniform_β
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (N : ℕ)
    (CN : ℝ) (_hCN_nn : 0 ≤ CN) (eN : ℕ)
    (hCN_bd : ∀ (α : M) (P₀ : TensorCompIdx (E := E) r s)
        (i : TensorEigenIdx (I := I) (M := M) g r s),
      wkpNorm (d := Module.finrank ℝ E) N 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i α P₀)
          (chartTargetEuclid (I := I) (M := M) α)
        ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
          ENNReal.ofReal
            ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖)
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun (I := I) (M := M)
              g r s h_atlas i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  intro K' hK' i
  -- `wkpNorm K' ≤ wkpNorm N` by monotonicity in the regularity order.
  have h_mono : wkpNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) N 2
        (eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) hK'
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
  exact h_mono.trans (hCN_bd α P₀ i)

/-! ## The chart-component rescale identity

Both Headlines 2 and 3 rely on a single rescale: the resolvent chart component
at `(β, Q)`, viewed as an `EuclN → ℝ` function, is almost-everywhere equal to
`i.fst.val` times the eigenvector chart component
`eigenvectorChartComponentFun g r s h_atlas i β Q`. The rescale follows from
`resolventL2_eq_mul_eigenvector` (rearranged from
`eigenvector_eq_resolvent_smul`) and the `ℝ`-homogeneity of the canonical chart
component map (`tensorL2ChartComponent_smul`), passed through `Lp.coeFn_smul` to
the function level. -/

omit [CompleteSpace E] in
/-- The `L²`-coercion of the resolvent equals the eigenvector vector rescaled by
`i.fst.val`. The companion of `eigenvector_eq_resolvent_smul`, rearranged by
multiplying through by the nonzero resolvent eigenvalue. -/
private lemma resolvent_eq_mul_eigenvector
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i) =
      i.fst.val •
        tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul (I := I) (M := M) g r s h_atlas i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

omit [CompleteSpace E] in
/-- The canonical chart component of the resolvent's `L²`-coercion equals
`i.fst.val` times the canonical chart component of the eigenvector vector. -/
private lemma resolvent_chartComponent_eq_smul
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i)) β Q =
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q := by
  rw [resolvent_eq_mul_eigenvector (I := I) (M := M) g r s h_atlas i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s i.fst.val
    (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q

omit [CompleteSpace E] in
/-- The coercion-to-function of the resolvent chart component agrees almost
everywhere, with respect to the chart-pulled `L²` reference measure, with
`i.fst.val` times the eigenvector chart-component function. -/
private lemma resolvent_chartComponent_coe_ae_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i β Q y) := by
  -- The Lp identity transferred to coeFn.
  have h_smul := Lp.coeFn_smul i.fst.val
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i) β Q)
  have h_eq : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => i.fst.val •
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i β Q y) := by
    rw [resolvent_chartComponent_eq_smul (I := I) (M := M) g r s h_atlas i β Q]
    exact h_smul
  filter_upwards [h_eq] with y hy
  rw [hy, smul_eq_mul]

/-! ## MemWkp of the eigenvector chart component, derived from the resolvent

For Headlines 2 and 3, the rescale identity reduces a `wkpNorm` bound on the
resolvent chart component to a `wkpNorm` bound on the eigenvector chart
component. To apply `wkpNorm_const_smul` for the rescale, we need `MemWkp K' 2`
of the eigenvector chart component. We derive it from a `MemWkp K' 2` hypothesis
on the resolvent chart component via the inverse rescale `eigenvector chart cpt
=ᵐ (i.fst.val)⁻¹ * resolvent chart cpt` and `MemWkp.const_smul`. -/

omit [CompleteSpace E] in
/-- The eigenvector chart-component function is `MemWkp K' 2` whenever the
resolvent chart-component coercion is, at the same order. The bridge is the
inverse rescale `eigenvector chart cpt =ᵐ (i.fst.val)⁻¹ * resolvent chart cpt`,
combined with `MemWkp.const_smul` and `MemWkp_congr_ae`. -/
private lemma eigenvectorChartComponentFun_memWkp_of_resolv
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_atlas : DifferentialGeometry.Geometry.HasLocallyConstantChartAt H M)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ)
    (h_resolv : MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- Scale the resolvent regularity by `(i.fst.val)⁻¹`.
  have h_scaled : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_resolv (i.fst.val)⁻¹
  -- The inverse rescale: `eigenvector chart cpt =ᵐ (i.fst.val)⁻¹ * resolvent chart cpt`.
  have h_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q y) := by
    have h_resc := resolvent_chartComponent_coe_ae_eq
      (I := I) (M := M) g r s h_atlas i β Q
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    filter_upwards [h_resc] with y hy
    rw [hy]
    field_simp
  -- Transfer `MemWkp` through the a.e. equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_scaled

/-! ## A scalar inequality: `μ · μ⁻¹^eN ≤ μ⁻¹^eN`

The rescale multiplies the eigenvector chart-component bound `CN · μ⁻¹^eN` by
`‖μ‖ = μ` (positivity), yielding `CN · μ · μ⁻¹^eN`. Since `μ ∈ (0, 1]`, the
factor `μ` is at most `1` and at most `μ⁻¹`, so
`μ · μ⁻¹^eN = μ⁻¹^(eN - 1) ≤ μ⁻¹^eN` for `eN ≥ 1`, and `μ · 1 = μ ≤ 1` for
`eN = 0`. In both cases the exponent stays at `eN`. -/

omit [CompleteSpace E] in
/-- `μ · μ⁻¹^eN ≤ μ⁻¹^eN` whenever `0 < μ ≤ 1`. -/
private lemma mu_mul_inv_pow_le_inv_pow
    {μ : ℝ} (hμ_pos : 0 < μ) (hμ_le_one : μ ≤ 1) (eN : ℕ) :
    μ * μ⁻¹ ^ eN ≤ μ⁻¹ ^ eN := by
  have hμ_inv_nn : 0 ≤ μ⁻¹ := le_of_lt (inv_pos.mpr hμ_pos)
  have hμ_inv_pow_nn : 0 ≤ μ⁻¹ ^ eN := pow_nonneg hμ_inv_nn _
  have h : μ * μ⁻¹ ^ eN ≤ 1 * μ⁻¹ ^ eN :=
    mul_le_mul_of_nonneg_right hμ_le_one hμ_inv_pow_nn
  simpa using h

/-! ## Headline 2 — high-order resolvent chart-component bound

The second converter: the resolvent chart-component atom at `(β, Q)` at order
`K' + 1`, with `K' + 1 ≤ N`. The proof transfers the resolvent chart component
to the eigenvector chart component via the rescale identity, then applies the
order-`(K' + 1)` eigenvector chart-component bound from Headline 1 at `(β, Q)`,
and absorbs the `μ` factor from the rescale via `mu_mul_inv_pow_le_inv_pow`. -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family high-order resolvent chart-component Sobolev bound,
derived from a β-uniform order-`N` chart-component Sobolev hypothesis.**

The high-order resolvent chart-component atom: under the same hypothesis
`hCN_bd` of Headline 1, plus a β-uniform `MemWkp (K' + 1) 2` regularity input
`h_pou_resolv` for the resolvent chart component (matching the regularity field
of the per-`K'`-family bundle), the order-`(K' + 1)` Sobolev norm of the
resolvent chart component at `(β, Q)` is bounded by `ENNReal.ofReal (CN *
(i.fst.val)⁻¹ ^ eN)` times `ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas
i‖`, with the same constant `CN` and exponent `eN` as in Headline 1.

The proof rewrites the resolvent chart-component coercion as `i.fst.val` times
the eigenvector chart-component function `eigenvectorChartComponentFun` (the
rescale identity `resolvent_chartComponent_coe_ae_eq`), then applies
`wkpNorm_const_smul` to factor out the scalar, applies Headline 1 at order
`K' + 1 ≤ N` and `(β, Q)`, and absorbs the resulting `‖i.fst.val‖ = i.fst.val`
factor through `mu_mul_inv_pow_le_inv_pow`. -/
theorem eigenvector_resolventHigh_perK_from_uniform_β
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
      K' + 1 ≤ N →
      MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s h_atlas i
  -- The resolvent chart-component regularity at order `K' + 1`.
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  -- Derived regularity for the eigenvector chart component at order `K' + 1`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s h_atlas i β Q (K' + 1) h_resolv_mem
  -- The rescale identity at the coeFn level.
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s h_atlas i β Q
  -- Rewrite the `wkpNorm` through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out of the eigenvector-side norm.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The Headline-1 bound at `(β, Q)` at order `K' + 1 ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s h_atlas N CN hCN_nn eN hCN_bd β Q (K' + 1) hK' i
  -- Combine.
  rw [h_norm_eq, h_smul_eq]
  -- `‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val` (since `0 ≤ i.fst.val`).
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  -- The rescaled eigenvector-side bound after multiplying by `μ`.
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  -- Repackage the right-hand side and absorb the `μ` factor.
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
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω
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

/-! ## Headline 3 — low-order resolvent chart-component bound

The third converter: the resolvent chart-component atom at `(β, Q)` at order
`K' ≤ N`. The proof mirrors Headline 2 with the order at `K'` instead of
`K' + 1`. -/

omit [CompleteSpace E] in
/-- **Per-`K'`-family low-order resolvent chart-component Sobolev bound, derived
from a β-uniform order-`N` chart-component Sobolev hypothesis.**

The low-order resolvent chart-component atom: under the same hypothesis `hCN_bd`
of Headline 1, plus a β-uniform `MemWkp K' 2` regularity input `h_pou_resolv`
for the resolvent chart component, the order-`K'` Sobolev norm of the resolvent
chart component at `(β, Q)` is bounded by `ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^
eN)` times `ENNReal.ofReal ‖tensorResolventEigenbasisVec h_atlas i‖`, with the
same constant `CN` and exponent `eN` as in Headlines 1 and 2.

The proof mirrors Headline 2 at order `K'` instead of `K' + 1`: the rescale
identity reduces the resolvent chart-component bound to an eigenvector
chart-component bound, the scalar `i.fst.val` is factored out via
`wkpNorm_const_smul`, Headline 1 supplies the eigenvector chart-component bound
at order `K' ≤ N`, and `mu_mul_inv_pow_le_inv_pow` absorbs the residual `μ`
factor. -/
theorem eigenvector_resolventLow_perK_from_uniform_β
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
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local
    (I := I) (M := M) g r s h_atlas i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local
    (I := I) (M := M) g r s h_atlas i
  -- The resolvent chart-component regularity at order `K'`.
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  -- Derived regularity for the eigenvector chart component at order `K'`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv
      (I := I) (M := M) g r s h_atlas i β Q K' h_resolv_mem
  -- The rescale identity at the coeFn level.
  have h_ae := resolvent_chartComponent_coe_ae_eq
    (I := I) (M := M) g r s h_atlas i β Q
  -- Rewrite the `wkpNorm` through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent (I := I) (M := M) g r s h_atlas i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out of the eigenvector-side norm.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun (I := I) (M := M)
          g r s h_atlas i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The Headline-1 bound at `(β, Q)` at order `K' ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun (I := I) (M := M)
        g r s h_atlas i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec (I := I) (M := M) h_atlas i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β
      (I := I) (M := M) g r s h_atlas N CN hCN_nn eN hCN_bd β Q K' hK' i
  -- Combine.
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω
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
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun (I := I) (M := M)
            g r s h_atlas i β Q) Ω
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

/-! ## Chart-locality-free twins

The declarations below re-key every `h_atlas`-carrying declaration of this file
onto the intrinsic compact-operator eigenbasis. Each twin proves the same
statement without the chart-selection hypothesis, by replacing
`tensorResolventEigenbasisVec h_atlas` with `tensorResolventEigenbasisVec_ofCompact
(tensorResolventL2_isCompactOperator_intrinsic g r s)`, and the concrete
atlas-keyed operators (`eigenvectorChartComponentFun`, `eigenvectorResolvent`)
with their `_unconditional` forms. `[CompleteSpace E]` is a section hypothesis
throughout. -/

section Unconditional

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

/-- Chart-locality-free twin of `vec_norm_eq_one_local`. -/
private lemma vec_norm_eq_one_local_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i‖ = 1 :=
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

/-- Chart-locality-free twin of
`eigenvector_chartComponent_perK_from_uniform_β`. -/
theorem eigenvector_chartComponent_perK_from_uniform_β_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (N : ℕ)
    (CN : ℝ) (_hCN_nn : 0 ≤ CN) (eN : ℕ)
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
    (α : M) (P₀ : TensorCompIdx (E := E) r s) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
              g r s i α P₀)
            (chartTargetEuclid (I := I) (M := M) α)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  intro K' hK' i
  -- `wkpNorm K' ≤ wkpNorm N` by monotonicity in the regularity order.
  have h_mono : wkpNorm (d := Module.finrank ℝ E) K' 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α)
      ≤ wkpNorm (d := Module.finrank ℝ E) N 2
        (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i α P₀)
        (chartTargetEuclid (I := I) (M := M) α) :=
    wkpNorm_mono_order (d := Module.finrank ℝ E) hK'
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i α P₀)
      (chartTargetEuclid (I := I) (M := M) α)
  exact h_mono.trans (hCN_bd α P₀ i)

/-- Chart-locality-free twin of `resolvent_eq_mul_eigenvector`. -/
private lemma resolvent_eq_mul_eigenvector_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    TensorH1ComplToTensorL2 (I := I) (M := M) g r s
        (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i) =
      i.fst.val •
        tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
          (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
            g r s) i := by
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  rw [eigenvector_eq_resolvent_smul_unconditional (I := I) (M := M) g r s i,
    smul_smul, mul_inv_cancel₀ hμ_ne, one_smul]

/-- Chart-locality-free twin of `resolvent_chartComponent_eq_smul`. -/
private lemma resolvent_chartComponent_eq_smul_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    tensorL2ChartComponent (I := I) (M := M) g r s
        (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
          (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i)) β Q =
      i.fst.val •
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i) β Q := by
  rw [resolvent_eq_mul_eigenvector_unconditional (I := I) (M := M) g r s i]
  exact tensorL2ChartComponent_smul (I := I) (M := M) g r s i.fst.val
    (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
      (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
        g r s) i) β Q

/-- Chart-locality-free twin of `resolvent_chartComponent_coe_ae_eq`. -/
private lemma resolvent_chartComponent_coe_ae_eq_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) β)]
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) := by
  -- The Lp identity transferred to coeFn.
  have h_smul := Lp.coeFn_smul i.fst.val
    (tensorL2ChartComponent (I := I) (M := M) g r s
      (tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
        (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
          g r s) i) β Q)
  have h_eq : (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) β]
      (fun y => i.fst.val •
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) := by
    rw [resolvent_chartComponent_eq_smul_unconditional
      (I := I) (M := M) g r s i β Q]
    exact h_smul
  filter_upwards [h_eq] with y hy
  rw [hy, smul_eq_mul]

/-- Chart-locality-free twin of
`eigenvectorChartComponentFun_memWkp_of_resolv`. -/
private lemma eigenvectorChartComponentFun_memWkp_of_resolv_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (β : M) (Q : TensorCompIdx (E := E) r s) (K' : ℕ)
    (h_resolv : MemWkp (d := Module.finrank ℝ E) K' 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q)
      (chartTargetEuclid (I := I) (M := M) β) := by
  classical
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- Scale the resolvent regularity by `(i.fst.val)⁻¹`.
  have h_scaled : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y) Ω :=
    MemWkp.const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_resolv (i.fst.val)⁻¹
  -- The inverse rescale: `eigenvector chart cpt =ᵐ (i.fst.val)⁻¹ * resolvent chart cpt`.
  have h_ae : (fun y => (i.fst.val)⁻¹ *
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
            EuclN → ℝ) y)
      =ᵐ[(volume : Measure EuclN).restrict Ω]
      (fun y => eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q y) := by
    have h_resc := resolvent_chartComponent_coe_ae_eq_unconditional
      (I := I) (M := M) g r s i β Q
    have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
    filter_upwards [h_resc] with y hy
    rw [hy]
    field_simp
  -- Transfer `MemWkp` through the a.e. equality.
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae).mp h_scaled

/-- Chart-locality-free twin of
`eigenvector_resolventHigh_perK_from_uniform_β`. -/
theorem eigenvector_resolventHigh_perK_from_uniform_β_unconditional
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
      K' + 1 ≤ N →
      MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
            (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
              (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
            β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' + 1 ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local_unconditional
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local_unconditional
    (I := I) (M := M) g r s i
  -- The resolvent chart-component regularity at order `K' + 1`.
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  -- Derived regularity for the eigenvector chart component at order `K' + 1`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv_unconditional
      (I := I) (M := M) g r s i β Q (K' + 1) h_resolv_mem
  -- The rescale identity at the coeFn level.
  have h_ae := resolvent_chartComponent_coe_ae_eq_unconditional
    (I := I) (M := M) g r s i β Q
  -- Rewrite the `wkpNorm` through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out of the eigenvector-side norm.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The Headline-1 bound at `(β, Q)` at order `K' + 1 ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q (K' + 1) hK' i
  -- Combine.
  rw [h_norm_eq, h_smul_eq]
  -- `‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val` (since `0 ≤ i.fst.val`).
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  -- The rescaled eigenvector-side bound after multiplying by `μ`.
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
      ≤ ENNReal.ofReal i.fst.val *
          (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖) :=
    mul_le_mul_of_nonneg_left h_eig_bd (zero_le _)
  -- Repackage the right-hand side and absorb the `μ` factor.
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
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) (K' + 1) 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖) :=
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
`eigenvector_resolventLow_perK_from_uniform_β`. -/
theorem eigenvector_resolventLow_perK_from_uniform_β_unconditional
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
        (chartTargetEuclid (I := I) (M := M) β)) :
    ∀ (K' : ℕ), K' ≤ N →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g r s)
        (β : M) (Q : TensorCompIdx (E := E) r s),
        wkpNorm (d := Module.finrank ℝ E) K' 2
            (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
                (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
                  (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
                β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) :
                EuclN → ℝ) y)
            (chartTargetEuclid (I := I) (M := M) β)
          ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
            ENNReal.ofReal
              ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
                  g r s) i‖ := by
  classical
  intro K' hK' i β Q
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) β with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) β
  -- The resolvent eigenvalue lies in `(0, 1]`.
  have hμ_pos : 0 < i.fst.val := eigenval_pos_local_unconditional
    (I := I) (M := M) g r s i
  have hμ_le_one : i.fst.val ≤ 1 := eigenval_le_one_local_unconditional
    (I := I) (M := M) g r s i
  -- The resolvent chart-component regularity at order `K'`.
  have h_resolv_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y)
      Ω :=
    h_pou_resolv i K' β Q hK'
  -- Derived regularity for the eigenvector chart component at order `K'`.
  have h_eig_mem : MemWkp (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω :=
    eigenvectorChartComponentFun_memWkp_of_resolv_unconditional
      (I := I) (M := M) g r s i β Q K' h_resolv_mem
  -- The rescale identity at the coeFn level.
  have h_ae := resolvent_chartComponent_coe_ae_eq_unconditional
    (I := I) (M := M) g r s i β Q
  -- Rewrite the `wkpNorm` through the a.e. equality.
  have h_norm_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => ((tensorL2ChartComponent (I := I) (M := M) g r s
          (TensorH1ComplToTensorL2 (I := I) (M := M) g r s
            (eigenvectorResolvent_unconditional (I := I) (M := M) g r s i))
          β Q : Lp ℝ 2 (chartL2Measure (I := I) (M := M) β)) : EuclN → ℝ) y) Ω
      = wkpNorm (d := Module.finrank ℝ E) K' 2
        (fun y => i.fst.val *
          eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q y) Ω :=
    wkpNorm_congr_ae (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_ae
  -- Factor the scalar out of the eigenvector-side norm.
  have h_smul_eq : wkpNorm (d := Module.finrank ℝ E) K' 2
      (fun y => i.fst.val *
        eigenvectorChartComponentFun_unconditional (I := I) (M := M)
          g r s i β Q y) Ω
      = ‖i.fst.val‖ₑ *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω :=
    wkpNorm_const_smul (d := Module.finrank ℝ E)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hΩ_open h_eig_mem i.fst.val
  -- The Headline-1 bound at `(β, Q)` at order `K' ≤ N`.
  have h_eig_bd : wkpNorm (d := Module.finrank ℝ E) K' 2
      (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
        g r s i β Q) Ω
      ≤ ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
        ENNReal.ofReal
          ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
            (tensorResolventL2_isCompactOperator_intrinsic (I := I) (M := M)
              g r s) i‖ :=
    eigenvector_chartComponent_perK_from_uniform_β_unconditional
      (I := I) (M := M) g r s N CN hCN_nn eN hCN_bd β Q K' hK' i
  -- Combine.
  rw [h_norm_eq, h_smul_eq]
  have h_norm_eq_val : ‖i.fst.val‖ₑ = ENNReal.ofReal i.fst.val := by
    rw [Real.enorm_eq_ofReal hμ_pos.le]
  rw [h_norm_eq_val]
  have h_step1 :
      ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
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
    have h_mu_bd := mu_mul_inv_pow_le_inv_pow hμ_pos hμ_le_one eN
    exact mul_le_mul_of_nonneg_left h_mu_bd hCN_nn
  calc
    ENNReal.ofReal i.fst.val *
        wkpNorm (d := Module.finrank ℝ E) K' 2
          (eigenvectorChartComponentFun_unconditional (I := I) (M := M)
            g r s i β Q) Ω
        ≤ ENNReal.ofReal i.fst.val *
            (ENNReal.ofReal (CN * (i.fst.val)⁻¹ ^ eN) *
              ENNReal.ofReal
                ‖tensorResolventEigenbasisVec_ofCompact (I := I) (M := M)
                  (tensorResolventL2_isCompactOperator_intrinsic
                    (I := I) (M := M) g r s) i‖) :=
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

end Unconditional

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
