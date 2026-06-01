import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorChartLowerOrderLimits

/-!
# The `n → ∞` `L²`-limit of the covariant-gradient Christoffel correction term

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, an eigenbasis index
`i` with nonzero resolvent eigenvalue `μ := i.fst.val`, a chart center `α : M`,
a component multi-index `P₀`, and a chart-coordinate direction `k`, the raw
chart-component formula for the section-level covariant gradient carries, on its
right-hand side, the zeroth-order Christoffel correction term
`covDerivLowerOrderTerm g r s Tₙ α k P₀.1 P₀.2`, evaluated at the
partition-of-unity-weighted smooth approximant
`Tₙ := pouSmul g r s α (eigenvectorSmoothApprox g r s h_atlas i n).toCcTensor`.

This file produces the `n → ∞` `L²`-limit of that term in
`Lp ℝ 2 (chartL2Measure α)`.

## The tracing identity

The Christoffel correction `covDerivLowerOrderTerm` is, by
`covDerivLowerOrderTerm_def`, a finite linear combination — over component
multi-index pairs `p` — of the `C^∞` lower-order correction coefficient
`covDerivLowerOrderCoeff` times the *undifferentiated raw* chart component of
the section. For the partition-of-unity-weighted approximant `Tₙ`, the raw
chart component is the partition-of-unity-weighted chart component
(`tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou`), whose value at
the chart preimage is, on the chart target, the canonical Euclidean chart
component `tensorChartComponent g r s wₙ.toCcTensor α p`. Consequently the
Christoffel correction at `Tₙ`, restricted to the chart target, is a finite
`C^∞`-coefficient-weighted sum of the single `T`-dependent atom

* `tensorChartComponent g r s wₙ.toCcTensor α p` (the bare chart component).

The `L²`-limit of that atom is `componentLpLimit` (companion file
`EigenvectorChartChartComponentL2.lean`), which is `μ` times the canonical chart
component `tensorL2ChartComponent g r s φ α p` of the eigenvector
`φ := tensorResolventEigenbasisVec h_atlas i`. The `μ⁻¹`-rescaling of the
`n`-th term — matching the rescaling convention of every companion eigenvector
chart-component limit object — therefore converges to the finite
`C^∞`-coefficient-weighted sum of the genuine eigenvector chart components.

## Main definitions

* `covGradChristoffelLimit g r s h_atlas i α P₀ k` — the explicit `L²`-limit
  function of the `μ⁻¹`-rescaled Christoffel correction term: a finite
  `C^∞`-coefficient-weighted sum, over component multi-index pairs, of the
  canonical eigenvector chart-component limit object `tensorL2ChartComponent`,
  with each coefficient cut to the partition-of-unity kernel.

## Main results

* `covGradChristoffelLimit_memLp` — the limit function is `L²`.
* `covGradChristoffel_tendsto` — the `n → ∞` `L²`-convergence headline.

## Sign convention

We follow the geometer convention `Δ_∇ = -∇* ∇`, with spectrum `⊆ (-∞, 0]`. The
resolvent is `(1 - Δ_∇)⁻¹` (spectrum `⊆ (0, 1]`).
-/

noncomputable section

set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff BigOperators Matrix ENNReal NNReal
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- On the Euclidean chart target, the zeroth-order Christoffel correction of
the partition-of-unity-weighted approximant is the finite linear combination,
over component multi-index pairs, of the lower-order correction coefficient
times the canonical Euclidean chart component. -/
private lemma covDerivLowerOrderTerm_pouSmul_eqOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (m : Fin (Module.finrank ℝ E))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α S) α m Idx Jdx y =
      ∑ p : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covDerivLowerOrderCoeff (I := I) (M := M) g r s α m Idx p.1 Jdx p.2 y *
          tensorChartComponent (I := I) (M := M) g r s S α p.1 p.2 y := by
  classical
  rw [covDerivLowerOrderTerm_def]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tensorChartComponentRaw_pouSmul_eq_tensorChartComponentPou
    (I := I) (M := M) g r s α S p.1 p.2,
    tensorChartComponent_def,
    chartPushedRaw_apply_of_mem (I := I) (M := M) α
      (tensorChartComponentPou (I := I) (M := M) g r s S α p.1 p.2) hy]

/-- Chart-locality-free twin of `covDerivLowerOrderTerm_pouSmul_memLp`. -/
theorem covDerivLowerOrderTerm_pouSmul_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) (n : ℕ) :
    MemLp
      (covDerivLowerOrderTerm (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α
          (eigenvectorSmoothApprox (I := I) (M := M)
            g r s i n).toCcTensor) α k P₀.1 P₀.2) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  refine (memLp_finset_sum (μ := chartL2Measure (I := I) (M := M) α)
    (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ =>
      memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α p n
        (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
          g r s α k P₀.1 p.1 P₀.2 p.2))).ae_eq ?_
  refine Filter.EventuallyEq.symm ?_
  rw [chartL2Measure]
  refine (ae_restrict_iff'
    (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
  exact Filter.Eventually.of_forall (fun y hy =>
    covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
      (eigenvectorSmoothApprox (I := I) (M := M)
        g r s i n).toCcTensor k P₀.1 P₀.2 hy)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGradChristoffelLimit`. The canonical
eigenvector chart-component limit object is re-keyed onto the chart-locality-free
eigenbasis selector `tensorResolventEigenbasisVec`. -/
noncomputable def covGradChristoffelLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p :
          EuclN → ℝ) y

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `covGradChristoffelLimit_memLp`. -/
theorem covGradChristoffelLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelLimit (I := I) (M := M)
        g r s i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (tensorL2ChartComponent (I := I) (M := M) g r s
        (tensorResolventEigenbasisVec (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M)
            g r s) i) α p))

/-- Chart-locality-free twin of `covGradChristoffelUnscaledLimit`. -/
private noncomputable def covGradChristoffelUnscaledLimit
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) : EuclN → ℝ :=
  fun y =>
    ∑ p : TensorCompIdx (E := E) r s,
      Set.indicator (chartPouKernel (I := I) (M := M) α)
          (covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2) y *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y

/-- Chart-locality-free twin of `covGradChristoffelUnscaledLimit_memLp`. -/
private theorem covGradChristoffelUnscaledLimit_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    MemLp (covGradChristoffelUnscaledLimit (I := I) (M := M)
        g r s i α P₀ k) 2
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  unfold covGradChristoffelUnscaledLimit
  exact memLp_finset_sum (Finset.univ : Finset (TensorCompIdx (E := E) r s))
    (fun p _ => memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s i α p))

/-- Chart-locality-free twin of `covDerivLowerOrderTerm_pouSmul_tendsto`. -/
private theorem covDerivLowerOrderTerm_pouSmul_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
        g r s i α P₀ k n).toLp _)
      atTop
      (𝓝 ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp _)) := by
  classical
  have hf : ∀ (p : TensorCompIdx (E := E) r s) (n : ℕ),
      MemLp (fun y => covDerivLowerOrderCoeff (I := I) (M := M)
            g r s α k P₀.1 p.1 P₀.2 p.2 y *
          tensorChartComponent (I := I) (M := M) g r s
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor α p.1 p.2 y) 2
        (chartL2Measure (I := I) (M := M) α) := fun p n =>
    memLp_factor_mul_componentAtom (I := I) (M := M) g r s i α p n
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
  have hflim : ∀ p : TensorCompIdx (E := E) r s,
      MemLp (fun y => Set.indicator (chartPouKernel (I := I) (M := M) α)
            (covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2) y *
          (componentLpLimit (I := I) (M := M) g r s i α p :
            EuclN → ℝ) y) 2
        (chartL2Measure (I := I) (M := M) α) := fun p =>
    memLp_indicatorFactor_mul_lp (I := I) (M := M) α
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (componentLpLimit (I := I) (M := M) g r s i α p)
  have h_tendsto : ∀ p : TensorCompIdx (E := E) r s,
      Filter.Tendsto (fun n => (hf p n).toLp _) atTop
        (𝓝 ((hflim p).toLp _)) := fun p =>
    tendsto_componentSummand (I := I) (M := M) g r s i α p
      (covDerivLowerOrderCoeff_contDiffOn (I := I) (M := M)
        g r s α k P₀.1 p.1 P₀.2 p.2)
      (fun n => hf p n) (hflim p)
  have hFn_eq : ∀ n : ℕ,
      covDerivLowerOrderTerm (I := I) (M := M) g r s
          (pouSmul (I := I) (M := M) g r s α
            (eigenvectorSmoothApprox (I := I) (M := M)
              g r s i n).toCcTensor) α k P₀.1 P₀.2
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          covDerivLowerOrderCoeff (I := I) (M := M)
              g r s α k P₀.1 p.1 P₀.2 p.2 y *
            tensorChartComponent (I := I) (M := M) g r s
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor α p.1 p.2 y := by
    intro n
    rw [chartL2Measure]
    refine (ae_restrict_iff'
      (chartTargetEuclid_measurableSet (I := I) (M := M) α)).mpr ?_
    exact Filter.Eventually.of_forall (fun y hy =>
      covDerivLowerOrderTerm_pouSmul_eqOn (I := I) (M := M) g r s α
        (eigenvectorSmoothApprox (I := I) (M := M)
          g r s i n).toCcTensor k P₀.1 P₀.2 hy)
  have hFlim_eq :
      covGradChristoffelUnscaledLimit (I := I) (M := M)
          g r s i α P₀ k
        =ᵐ[chartL2Measure (I := I) (M := M) α]
        fun y => ∑ p : TensorCompIdx (E := E) r s,
          Set.indicator (chartPouKernel (I := I) (M := M) α)
              (covDerivLowerOrderCoeff (I := I) (M := M)
                g r s α k P₀.1 p.1 P₀.2 p.2) y *
            (componentLpLimit (I := I) (M := M) g r s i α p :
              EuclN → ℝ) y :=
    Filter.EventuallyEq.rfl
  exact tendsto_toLp_finsetSum (I := I) (M := M) α Finset.univ
    hf hflim h_tendsto
    (fun n => covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
      g r s i α P₀ k n)
    (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s i α P₀ k)
    hFn_eq hFlim_eq

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `smul_componentLpLimit_coeFn_ae`. -/
private lemma smul_componentLpLimit_coeFn_ae
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (p : TensorCompIdx (E := E) r s) :
    (fun y : EuclN => (i.fst.val)⁻¹ *
        (componentLpLimit (I := I) (M := M) g r s i α p :
          EuclN → ℝ) y)
      =ᵐ[chartL2Measure (I := I) (M := M) α]
      (fun y : EuclN =>
        (tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p :
          EuclN → ℝ) y) := by
  classical
  have hμ_ne : i.fst.val ≠ 0 := i.fst.val_ne_zero
  have h_lp_eq :
      (i.fst.val)⁻¹ • componentLpLimit (I := I) (M := M)
          g r s i α p =
        tensorL2ChartComponent (I := I) (M := M) g r s
          (tensorResolventEigenbasisVec (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M)
              g r s) i) α p := by
    rw [componentLpLimit, smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    (componentLpLimit (I := I) (M := M) g r s i α p)).symm.trans ?_
  exact Filter.EventuallyEq.of_eq
    (congrArg (fun z : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) =>
      (z : EuclN → ℝ)) h_lp_eq)

open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral in
/-- Chart-locality-free twin of `smul_unscaledLimit_toLp_eq`. -/
private lemma smul_unscaledLimit_toLp_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    (i.fst.val)⁻¹ •
        (covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
          g r s i α P₀ k).toLp _ =
      (covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp _ := by
  classical
  apply Lp.ext
  refine (Lp.coeFn_smul (i.fst.val)⁻¹
    ((covGradChristoffelUnscaledLimit_memLp (I := I) (M := M)
      g r s i α P₀ k).toLp _)).trans ?_
  refine Filter.EventuallyEq.trans ?_
    (MemLp.coeFn_toLp (covGradChristoffelLimit_memLp (I := I) (M := M)
      g r s i α P₀ k)).symm
  have h_all : ∀ᵐ y ∂(chartL2Measure (I := I) (M := M) α),
      ∀ p : TensorCompIdx (E := E) r s,
        (i.fst.val)⁻¹ *
            (componentLpLimit (I := I) (M := M) g r s i α p :
              EuclN → ℝ) y =
          (tensorL2ChartComponent (I := I) (M := M) g r s
            (tensorResolventEigenbasisVec (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M)
                g r s) i) α p :
            EuclN → ℝ) y :=
    (ae_all_iff).mpr (fun p =>
      smul_componentLpLimit_coeFn_ae (I := I) (M := M)
        g r s i α p)
  filter_upwards [MemLp.coeFn_toLp (covGradChristoffelUnscaledLimit_memLp
    (I := I) (M := M) g r s i α P₀ k), h_all] with y hy hy_all
  rw [Pi.smul_apply, hy]
  rw [covGradChristoffelUnscaledLimit,
    covGradChristoffelLimit, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [mul_left_comm, hy_all p]

/-- **Chart-locality-free twin of `covGradChristoffel_tendsto`.** The
`μ⁻¹`-rescaled `L²` classes of the zeroth-order Christoffel correction term at
the partition-of-unity-weighted approximants converge, as `n → ∞` and in
`Lp ℝ 2 (chartL2Measure α)`, to the `L²` class of the explicit limit function
`covGradChristoffelLimit g r s i α P₀ k`. -/
theorem covGradChristoffel_tendsto
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s)
    (α : M) (P₀ : TensorCompIdx (E := E) r s)
    (k : Fin (Module.finrank ℝ E)) :
    Filter.Tendsto
      (fun n => (i.fst.val)⁻¹ •
        ((covDerivLowerOrderTerm_pouSmul_memLp (I := I) (M := M)
          g r s i α P₀ k n).toLp
          (covDerivLowerOrderTerm (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α
              (eigenvectorSmoothApprox (I := I) (M := M)
                g r s i n).toCcTensor) α k P₀.1 P₀.2) :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)))
      atTop
      (𝓝 ((covGradChristoffelLimit_memLp (I := I) (M := M)
        g r s i α P₀ k).toLp
        (covGradChristoffelLimit (I := I) (M := M)
          g r s i α P₀ k))) := by
  classical
  have h_smul :=
    (covDerivLowerOrderTerm_pouSmul_tendsto (I := I) (M := M)
      g r s i α P₀ k).const_smul (i.fst.val)⁻¹
  rwa [smul_unscaledLimit_toLp_eq (I := I) (M := M)
    g r s i α P₀ k] at h_smul

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
