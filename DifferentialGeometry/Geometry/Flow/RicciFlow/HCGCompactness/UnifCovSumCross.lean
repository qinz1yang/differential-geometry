import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.AllTimesBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCovDerivLinear
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricLapDiff
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Comparison
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.ConnectionDifferenceNorm
import DifferentialGeometry.Geometry.Metric.ChartGram
import DifferentialGeometry.Analysis.Integration.Measure.ChartDensity
import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Covariant-sum cross-metric equivalence (item-6 statement S0) — fiber-level layer

This leaf builds toward item-6 statement **S0** (`covsum_cross_unif`, see
`ShortTime/UNIF_ITEM6_RECON.md` §S0): for `Λ`-comparable metrics `g₀`, `gBase` with
`MetricCovDerivOrderBoundOn` jets `≤ Λ`, the two-sided equivalence of covariant-derivative
sums
`∑_{j≤n} ‖∇^{g₀,j}T‖_{L²(g₀)} ≍_{C(Λ,n)} ∑_{j≤n} ‖∇^{gBase,j}T‖_{L²(gBase)}`.

Per the recon §3 route table, S0 decomposes into three levels: **fiber** (Λ-comparability ⟹
per-slot `√Λ` fibre-norm comparison — routine), **volume** (`dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}` —
a Loewner→determinant estimate the project deliberately avoided, see
`Measure/CompactVolumeEquiv.lean:9`), and **derivative** (the iterated change-of-connection
`∇^{g₀} = ∇^{gBase} + Γ-difference`, the main frontier).  The `volume` and `derivative`
bricks, plus the RS↔0S fibre-norm currency bridge (the sibling `MetricCovDerivBridge` lane's
`normBridge`), are multi-session; see `UnifCovSumCross.md`.

**This file** delivers the sorry-free **fiber-level layer** in the `normSq0S` currency, keyed
on the project comparability predicate `MetricUniformEquivalentOn` (`= Λ`-comparability with
`C = Λ`).  It packages the general-order pointwise fibre comparison and the covariant-*sum*
shell that the eventual L² assembly composes with the connection-change and volume bricks.

## Main results

* `covsumCross_fibSq` — two-sided per-order fibre squared-norm comparison:
  `Λ^{-s}·|A|²_{gBase} ≤ |A|²_{g₀} ≤ Λ^s·|A|²_{gBase}` for a `(0,s)` fibre tensor `A`.
* `covsumCross_fibNorm` — the `√`/norm upper form `|A|_{g₀} ≤ Λ^{s/2}·|A|_{gBase}`.
* `covsumCross_fibSum` — the covariant-sum shell: over a derivative-indexed family of
  `(0, s+j)` tensors, `∑_{j≤n} |A j|_{g₀} ≤ Λ^{(s+n)/2}·∑_{j≤n} |A j|_{gBase}` with a single
  explicit constant `Λ^{(s+n)/2}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators Matrix MatrixOrder
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

/-! ### Matrix determinant building blocks for the volume (Loewner→det) brick

These generic real-matrix lemmas are the pure linear-algebra core of the volume comparison
`dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}` (recon §3 volume level): the chart densities are
`√det(chartGram)`, so the comparison reduces to `det(chartGram g₀) ≤ Λ^n·det(chartGram gBase)`
(Loewner→determinant monotonicity).  Mathlib has no matrix square root, Weyl monotonicity, or
`det`-order lemma, so this is built from the spectral theorem; the reusable core is
`det_le_one_of_rayleigh` (`A ≤ I ⟹ det A ≤ 1`).  Candidate canonical home:
`Geometry/Comparison/Volume/JacobianBounds.lean` `MatrixBounds` (beside the existing
`eigenvalues_ge_of_rayleigh`/`sqrt_pow_le_sqrt_det`); kept private here pending planner hoist. -/
section MatrixDet

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit-vector Rayleigh **upper** bound ⟹ every eigenvalue is `≤ a` (the upper companion of
`Geometry/Comparison/Volume/JacobianBounds.lean`'s `eigenvalues_ge_of_rayleigh`). -/
private lemma eigenvalues_le_of_rayleigh
    {A : Matrix ι ι ℝ} {a : ℝ} (hA : A.IsHermitian)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ a) :
    ∀ i, hA.eigenvalues i ≤ a := by
  intro i
  rw [hA.eigenvalues_eq i]
  exact hray (hA.eigenvectorBasis i) (hA.eigenvectorBasis.norm_eq_one i)

/-- A positive-semidefinite real matrix whose Rayleigh quotient is `≤ 1` on the unit sphere
(i.e. `A ≤ I` in the Loewner order) has `det A ≤ 1`: its eigenvalues lie in `[0,1]` and the
determinant is their product.  This is the `B = I` core of Loewner→determinant monotonicity. -/
private lemma det_le_one_of_rayleigh
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      RCLike.re (dotProduct (star ⇑v) (Matrix.mulVec A ⇑v)) ≤ 1) :
    A.det ≤ 1 := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues]
  refine Finset.prod_le_one (fun i _ => ?_) (fun i _ => ?_)
  · exact_mod_cast hA.eigenvalues_nonneg i
  · exact_mod_cast eigenvalues_le_of_rayleigh hA.isHermitian hray i

/-- Plain-vector form of `det_le_one_of_rayleigh`: if the (real) quadratic form of a
positive-semidefinite matrix `A` is dominated by the Euclidean one (`x ⬝ᵥ A *ᵥ x ≤ x ⬝ᵥ x`,
i.e. `A ≤ I`), then `det A ≤ 1`.  Isolates the `EuclideanSpace`/`star`/`RCLike.re`
bookkeeping so the general Loewner→determinant lemma stays in `ι → ℝ` currency. -/
private lemma det_le_one_of_dotProduct
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hray : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ x) :
    A.det ≤ 1 := by
  refine det_le_one_of_rayleigh hA (fun v hv => ?_)
  have hnorm : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = 1 := by
    have h1 := EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℝ) v v
    rw [star_trivial] at h1
    have h2 : (⇑v : ι → ℝ) ⬝ᵥ ⇑v = ‖v‖ ^ 2 := by
      rw [← h1]; exact real_inner_self_eq_norm_sq v
    rw [h2, hv, one_pow]
  simp only [star_trivial, RCLike.re_to_real]
  exact (hray ⇑v).trans hnorm.le

/-- **General Loewner→determinant monotonicity.**  A positive-semidefinite matrix `A` dominated
(in the quadratic-form / Loewner sense) by a positive-definite matrix `B` has no larger
determinant.  Proof: the congruence `C := B^{-1/2} A B^{-1/2}` satisfies `C ≤ I` (so
`det C ≤ 1`) and `A = B^{1/2} C B^{1/2}`, whence `det A = det B · det C ≤ det B`.  Mathlib has
no matrix Loewner→det lemma; this is built from the CFC matrix square root
(`Analysis/Matrix/Order.lean`).  Reusable core of the volume brick (hoist candidate:
`Geometry/Comparison/Volume/JacobianBounds.lean` `MatrixBounds`). -/
private lemma det_le_of_posSemidef_le
    {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosDef)
    (hAB : ∀ x : ι → ℝ, x ⬝ᵥ (A *ᵥ x) ≤ x ⬝ᵥ (B *ᵥ x)) :
    A.det ≤ B.det := by
  classical
  -- self-adjointness of the quadratic pairing for a symmetric real matrix
  have quad_symm : ∀ (S : Matrix ι ι ℝ), Sᵀ = S → ∀ x z : ι → ℝ,
      x ⬝ᵥ (S *ᵥ z) = (S *ᵥ x) ⬝ᵥ z := by
    intro S hS x z
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]
  -- the positive square root `M = √B` and its basic algebra
  set M := CFC.sqrt B with hM_def
  have hM_nonneg : (0 : Matrix ι ι ℝ) ≤ M := by rw [hM_def]; exact CFC.sqrt_nonneg B
  have hM_psd : M.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hM_nonneg
  have hM_herm : Mᴴ = M := hM_psd.isHermitian
  have hMsymm : Mᵀ = M := by
    ext i j
    simpa [Matrix.transpose_apply, star_trivial] using hM_psd.isHermitian.apply i j
  have hMM : M * M = B := by
    rw [hM_def]; exact CFC.sqrt_mul_sqrt_self B (Matrix.nonneg_iff_posSemidef.mpr hB.posSemidef)
  -- determinant bookkeeping for `M`
  have hdetB_pos : 0 < B.det := hB.det_pos
  have hdetMM : M.det * M.det = B.det := by rw [← Matrix.det_mul, hMM]
  have hdetM_ne : M.det ≠ 0 := fun h0 => hdetB_pos.ne' (by rw [← hdetMM, h0, zero_mul])
  have hdetM_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdetM_ne
  have hMinv_r : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hdetM_unit
  have hMinv_l : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdetM_unit
  have hMinvsymm : (M⁻¹)ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMsymm]
  -- the congruence `C = M⁻¹ A M⁻¹` is PSD with Rayleigh quotient `≤ 1`
  have hC_psd : (M⁻¹ * A * M⁻¹).PosSemidef := by
    have h := hA.conjTranspose_mul_mul_same M⁻¹
    rwa [Matrix.conjTranspose_nonsing_inv, hM_herm] at h
  have hC_ray : ∀ x : ι → ℝ, x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x) ≤ x ⬝ᵥ x := by
    intro x
    have hMw : M *ᵥ (M⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, hMinv_r, Matrix.one_mulVec]
    have e1 : x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x) = (M⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (M⁻¹ *ᵥ x)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact quad_symm M⁻¹ hMinvsymm x (A *ᵥ (M⁻¹ *ᵥ x))
    have e3 : (M⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (M⁻¹ *ᵥ x)) = x ⬝ᵥ x := by
      rw [← hMM, ← Matrix.mulVec_mulVec,
        quad_symm M hMsymm (M⁻¹ *ᵥ x) (M *ᵥ (M⁻¹ *ᵥ x)), hMw]
    calc x ⬝ᵥ ((M⁻¹ * A * M⁻¹) *ᵥ x)
        = (M⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (M⁻¹ *ᵥ x)) := e1
      _ ≤ (M⁻¹ *ᵥ x) ⬝ᵥ (B *ᵥ (M⁻¹ *ᵥ x)) := hAB (M⁻¹ *ᵥ x)
      _ = x ⬝ᵥ x := e3
  have hdetC : (M⁻¹ * A * M⁻¹).det ≤ 1 := det_le_one_of_dotProduct hC_psd hC_ray
  -- reassemble `A = M C M` and conclude `det A = det B · det C ≤ det B`
  have hACM : M * (M⁻¹ * A * M⁻¹) * M = A := by
    rw [show M * (M⁻¹ * A * M⁻¹) * M = (M * M⁻¹) * A * (M⁻¹ * M) by simp only [mul_assoc]]
    rw [hMinv_r, hMinv_l, one_mul, mul_one]
  have hdetA : A.det = B.det * (M⁻¹ * A * M⁻¹).det := by
    have hcongr := congrArg Matrix.det hACM
    rw [Matrix.det_mul, Matrix.det_mul] at hcongr
    rw [← hcongr, ← hdetMM]; ring
  rw [hdetA]
  exact mul_le_of_le_one_right hdetB_pos.le hdetC

end MatrixDet

-- The fibre-level comparison is purely pointwise: it needs only the fibre inner-product /
-- finite-dimensionality on `E` and a charted smooth manifold structure.  The manifold
-- topology instances (`CompactSpace`/`T2Space`/`SigmaCompactSpace`/boundarylessness) and
-- `NeZero (finrank E)` are deliberately dropped (weakest hypotheses); they re-enter only at
-- the L² / volume assembly, not here.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- **Fiber-level squared-norm cross-metric comparison** (S0 fibre atom, both directions).
For `Λ`-comparable `g₀`, `gBase` (as the project predicate `MetricUniformEquivalentOn`) and a
covariant `(0,s)` fibre tensor `A` at `x`, the two `g`-fibre squared norms differ by `Λ^{±s}`
(one `Λ` per tensor slot).  Forwards `normSq0S_le_of_metric_equiv` against the comparability
supplied pointwise by the class hypothesis. -/
theorem covsumCross_fibSq
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s : ℕ) (A : Tensor0SSpace s I x) :
    Λ ^ (-(s : ℤ)) * normSq0S (I := I) gBase x s A ≤ normSq0S (I := I) g₀ x s A ∧
      normSq0S (I := I) g₀ x s A ≤ Λ ^ (s : ℤ) * normSq0S (I := I) gBase x s A :=
  normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hEq.1
    (fun v => hEq.2 x (Set.mem_univ x) v) A

/-- **Fiber-level norm cross-metric comparison** (`√` form of `covsumCross_fibSq`, upper
direction).  `|A|_{g₀} ≤ Λ^{s/2}·|A|_{gBase}` for a covariant `(0,s)` fibre tensor.  This is
the fibre factor consumed term-by-term by the L² covariant-sum comparison. -/
theorem covsumCross_fibNorm
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s : ℕ) (A : Tensor0SSpace s I x) :
    Real.sqrt (normSq0S (I := I) g₀ x s A) ≤
      Real.sqrt (Λ ^ s) * Real.sqrt (normSq0S (I := I) gBase x s A) :=
  sqrt_normSq0S_le_of_metric_equiv (I := I) gBase g₀ x s hEq.1
    (fun v => hEq.2 x (Set.mem_univ x) v) A

/-- **Covariant-sum fibre shell** (the S0-shaped fibre reduction).  Over a derivative-indexed
family `A j : Tensor0SSpace (s + j) I x` (the fibres of the `(0,s)`-base covariant tower up to
order `n`), the `g₀`-fibre-norm sum is bounded by the `gBase`-fibre-norm sum times the single
explicit constant `Λ^{(s+n)/2}` (`= √(Λ^{s+n})`), obtained from the per-order factor
`Λ^{(s+j)/2}` by monotonicity `Λ ≥ 1`, `s+j ≤ s+n`.  The L² statement S0 is this shell
composed with the pointwise connection-change bound and the volume comparison (both frontier;
see `UnifCovSumCross.md`). -/
theorem covsumCross_fibSum
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x : M) (s n : ℕ) (A : (j : ℕ) → Tensor0SSpace (s + j) I x) :
    ∑ j ∈ Finset.range (n + 1), Real.sqrt (normSq0S (I := I) g₀ x (s + j) (A j)) ≤
      Real.sqrt (Λ ^ (s + n)) *
        ∑ j ∈ Finset.range (n + 1),
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hmono : Real.sqrt (Λ ^ (s + j)) ≤ Real.sqrt (Λ ^ (s + n)) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ hEq.1 (by omega))
  calc Real.sqrt (normSq0S (I := I) g₀ x (s + j) (A j))
      ≤ Real.sqrt (Λ ^ (s + j)) *
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) :=
        covsumCross_fibNorm gBase g₀ hEq x (s + j) (A j)
    _ ≤ Real.sqrt (Λ ^ (s + n)) *
          Real.sqrt (normSq0S (I := I) gBase x (s + j) (A j)) :=
        mul_le_mul_of_nonneg_right hmono (Real.sqrt_nonneg _)

/-! ### Derivative level — single-step connection difference (brick T: identity activation)

The generic single-step connection difference `diffStep g₁ g₂ s S = ∇^{g₁}S − ∇^{g₂}S` and the
order-1 telescoping reduction, activating the already-committed (but until now consumer-less)
identity layer `diffStep` / `iterCov` / `iterCov_telescoping`
(`HCGCompactness/MetricCovDerivLinear.lean`, themselves built on the subtraction-route atom
`nabla0SFun_sub_cov`, `Tensor/RSTensor/NablaOnTensors/HigherOrder.lean`).  The recon's "generic
multi-slot connection-difference is not yet a committed lemma" was a FALSE WALL: the identity is
proved sorry-free upstream.

The generic-rank EVALUATION of `diffStep` is now LANDED upstream (`MetricCovDerivLinear.lean`):
`diffStep_apply` (section form) and `diffStep_eval` (pointwise, arbitrary tangent vectors) give
`diffStep g₁ g₂ s S x (Fin.cons v slots) = −∑ₐ (S x)(update slots a ((Γ₁−Γ₂)(slots a))(v))`.  The
Session-4 "tensor-bundle instance diamond" was a false wall: `totalNabla0SFun_apply_section`
elaborates fine at variable rank once `set_option backward.isDefEq.respectTransparency false` is
in scope (this file lacks it; `MetricCovDerivLinear.lean` has it, so the eval was proved there).

The *fibre norm* atom `diffStep_norm_le` — brick T's reusable atom, the `(0,s)` generalization of
`connOut_norm_le` — is now LANDED here:
`√normSq0S(g₂, diffStep g₁ g₂ s S x) ≤ s·n^{(s+1)/2}·√normSqRS(connectionDifferenceTensorAt (LC g₁)(LC g₂) x)·√normSq0S(g₂, S x)`
(`n = finrank ℝ E`).  Its two sub-frontiers are both discharged: (a) the `g₂`-orthonormal frame at
`x` is built internally (`stdOrthonormalBasis` on `(tangentMetricData_gen g₂ x).metric.toCore`);
(b) the raw connection-difference component bound is the public `connDiffVec_norm_le`
(`Tensor/RSTensor/FiberMetric/ConnectionDifferenceNorm.lean`).  Proof = `diffStep_eval` +
`abs_apply_le_sqrt_normSq0S` on `S x` + `connDiffVec_norm_le` on the inserted slot, summed over the
`s` slots (`normSq0S_le_card_of_component_bound`).  REMAINING for the L² S0 assembly: (i) the JET
composition of `diffStep_norm_le` (fold `√normSqRS(connectionDifferenceTensorAt)` into
`metricCovDeriv`/`MetricCovDerivOrderBoundOn` currency via `lcDiff_norm_le`, needing a
`connectionDifferenceTensorAt` argument-order antisymmetry lemma + a `metricDerivNorm` ↔
`metricCovDerivNorm` bridge — see `UnifCovSumCross.md` §"Session 6"); (ii) the T-B base-Leibniz
induction for `j ≥ 2`.

Hoist candidate: `covStep_zero'`, `iterCov_one_eq` → `MetricCovDerivLinear.lean`.  Kept private
here pending planner hoist. -/
section DiffStepNorm

open DifferentialGeometry.Integral.Connection

set_option linter.unusedSectionVars false

-- The connection-difference tower `covStep`/`iterCov`/`diffStep`/`telescAccum` re-enters the
-- manifold/compactness instances the weakest-hypothesis fibre block above deliberately dropped.
-- Session-10 also gave `MetricCovDerivLinear`'s `covStep`/`diffStep`/`diffStep_eval` a
-- `[NeZero (finrank)]` + `[BoundarylessManifold]` requirement, so the whole tower re-adds them here.
variable [T2Space M] [SigmaCompactSpace M] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M]

/-- `covStep` of the zero field vanishes (`R`-linearity, via `covStep_add`). -/
private theorem covStep_zero' (gRef : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) gRef s 0 = 0 := by
  have h := covStep_add (I := I) gRef s 0 0
  rw [add_zero] at h
  have hc : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0 =
      covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hc

/-- The order-1 case of the telescoping identity: `∇^{g₁} T − ∇^{g₂} T` is exactly the
single-step connection difference `diffStep g₁ g₂ r T`. -/
private theorem iterCov_one_eq
    (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    iterCov (I := I) g₁ r T 1 =
      iterCov (I := I) g₂ r T 1 + diffStep (I := I) g₁ g₂ r T := by
  rw [iterCov_telescoping (I := I) g₁ g₂ r T 1]
  congr 1
  change telescAccum (I := I) g₁ g₂ r T 1 = diffStep (I := I) g₁ g₂ r T
  simp only [telescAccum]
  rw [covStep_zero', zero_add]
  rfl

/-- **Fibre norm of the single-step connection difference** (brick T-A, the `(0,s)` analogue of
`connOut_norm_le`).  The `gBase = g₂`-fibre norm of `diffStep g₁ g₂ s S x = ∇^{g₁}S − ∇^{g₂}S` is
bounded by `s · n^{(s+1)/2} · ‖Γ₁−Γ₂‖_{g₂} · ‖S x‖_{g₂}` (`n = finrank ℝ E`), where
`‖Γ₁−Γ₂‖_{g₂} = √normSqRS(connectionDifferenceTensorAt (LC g₁)(LC g₂) x)`.

The dimension factor `n^{(s+1)/2}` comes from bounding each of the `n^{s+1}` frame components of
`diffStep g₁ g₂ s S x` uniformly by `s·‖Γ₁−Γ₂‖_{g₂}·‖S x‖_{g₂}` — via `diffStep_eval`, the slot
Cauchy–Schwarz `abs_apply_le_sqrt_normSq0S` on `S x`, and the atomic per-slot bound
`connDiffVec_norm_le` on the inserted vector — and summing squares
(`normSq0S_le_card_of_component_bound`) over a `g₂`-orthonormal frame; the sharp constant `s`
would instead need a per-component Parseval identity. -/
theorem diffStep_norm_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (diffStep (I := I) g₁ g₂ s S x)) ≤
      (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 1)) *
        Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
          (connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
        Real.sqrt (normSq0S (I := I) g₂ x s (S x)) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  -- internal `g₂`-orthonormal frame at `x`
  let D := (tangentMetricData_gen (I := I) g₂ x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : ∀ i j, g₂.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g₂.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen
      (tangentMetricData_gen (I := I) g₂ x) (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have hbnorm : ∀ i, Real.sqrt (g₂.inner x (basis i) (basis i)) = 1 := by
    intro i; rw [hON i i]; simp
  set NA := Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
    (connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNA
  set NS := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hNS
  have hNSnn : 0 ≤ NS := Real.sqrt_nonneg _
  set B : ℝ := (s : ℝ) * NA * NS with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  -- each frame component of `diffStep g₁ g₂ s S x` is bounded by `B`
  have hcomp : ∀ φ : Fin (s + 1) → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (diffStep (I := I) g₁ g₂ s S x) φ| ≤ B := by
    intro φ
    rw [component0S_apply]
    have hcons : (fun a : Fin (s + 1) => basis (φ a)) =
        Fin.cons (basis (φ 0)) (fun a : Fin s => basis (φ a.succ)) := by
      funext a
      refine Fin.cases ?_ ?_ a
      · rfl
      · intro i; rfl
    rw [hcons, diffStep_eval, abs_neg]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ a : Fin s,
        |(S x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x)
              (basis (φ a.succ))) (basis (φ 0))))| ≤ NA * NS := by
      intro a
      have hins_le :
          Real.sqrt (g₂.inner x
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x)
              (basis (φ a.succ))) (basis (φ 0)))
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x)
              (basis (φ a.succ))) (basis (φ 0)))) ≤ NA := by
        have h := connDiffVec_norm_le (I := I) g₂
          (leviCivitaConnectionOfMetric (I := I) g₁)
          (leviCivitaConnectionOfMetric (I := I) g₂)
          (basis (φ 0)) (basis (φ a.succ))
        rw [hbnorm (φ 0), hbnorm (φ a.succ), mul_one, mul_one, ← hNA] at h
        exact h
      have hcs := abs_apply_le_sqrt_normSq0S (I := I) g₂ x s basis hON (S x)
        (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
          (((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)
            (basis (φ a.succ))) (basis (φ 0))))
      have hprod :
          (∏ b : Fin s, Real.sqrt (g₂.inner x
              ((Function.update (fun a' : Fin s => basis (φ a'.succ)) a
                (((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x)
                  (basis (φ a.succ))) (basis (φ 0)))) b)
              ((Function.update (fun a' : Fin s => basis (φ a'.succ)) a
                (((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x)
                  (basis (φ a.succ))) (basis (φ 0)))) b)))
            = Real.sqrt (g₂.inner x
              (((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x)
                (basis (φ a.succ))) (basis (φ 0)))
              (((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x)
                (basis (φ a.succ))) (basis (φ 0)))) := by
        rw [Finset.prod_eq_single a
          (fun b _ hb => by rw [Function.update_of_ne hb]; exact hbnorm (φ b.succ))
          (fun ha => absurd (Finset.mem_univ a) ha), Function.update_self]
      rw [hprod, ← hNS] at hcs
      calc
        |(S x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
            (((CovariantDerivative.difference
                (leviCivitaConnectionOfMetric (I := I) g₁)
                (leviCivitaConnectionOfMetric (I := I) g₂) x)
              (basis (φ a.succ))) (basis (φ 0))))|
            ≤ NS * Real.sqrt (g₂.inner x
              (((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x)
                (basis (φ a.succ))) (basis (φ 0)))
              (((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x)
                (basis (φ a.succ))) (basis (φ 0)))) := hcs
        _ ≤ NS * NA := mul_le_mul_of_nonneg_left hins_le hNSnn
        _ = NA * NS := by ring
    calc (∑ a : Fin s,
            |(S x) (Function.update (fun a' : Fin s => basis (φ a'.succ)) a
                (((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x)
                  (basis (φ a.succ))) (basis (φ 0))))|)
          ≤ ∑ _a : Fin s, NA * NS := Finset.sum_le_sum (fun a _ => hterm a)
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hB]
          simp [nsmul_eq_mul]; ring
  -- assemble via the component → normSq0S bound and the card computation
  have hcard : normSq0S (I := I) g₂ x (s + 1) (diffStep (I := I) g₁ g₂ s S x) ≤
      (Fintype.card (Fin (s + 1) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) * B ^ 2 :=
    normSq0S_le_card_of_component_bound (I := I) g₂ x (s + 1) basis hinv
      (diffStep (I := I) g₁ g₂ s S x) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin (s + 1) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
        = (Module.finrank ℝ E : ℝ) ^ (s + 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  calc Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (diffStep (I := I) g₁ g₂ s S x))
        ≤ Real.sqrt
            ((Fintype.card (Fin (s + 1) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
              * B ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 1)) * B := by
        rw [hcard_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hBnn]
    _ = (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 1)) * NA * NS := by
        rw [hB]; ring

/-! #### Jet composition of `diffStep_norm_le` — two micro-bridges + the `j = 1` endpoint

Two grep-confirmed-absent micro-bridges fold `diffStep_norm_le`'s output
`√normSqRS(g₂, connectionDifferenceTensorAt (LC g₁)(LC g₂) x)` into the
`MetricCovDerivOrderBoundOn` class currency:

* **Bridge 1** (`connDiffTensor_normSqRS_swap`) — connection-argument-swap antisymmetry
  `normSqRS(g₀, connectionDifferenceTensorAt cov cov' x) =
   normSqRS(g₀, connectionDifferenceTensorAt cov' cov x)`, matching `diffStep_eval`'s `(LC g₁)(LC g₂)`
  order to `lcDiff_norm_le`'s `(LC g₂)(LC g₁)` order.  Built from the `CovariantDerivative.difference`
  argument swap `diff_swap` (`difference cov cov' = −difference cov' cov`, section-value route) lifted
  to the `(1,2)` tensor (`connDiffTensor_neg`), then the Hilbert–Schmidt fibre-norm negation
  invariance `normSqRS_neg`.  Canonical homes: `diff_swap` / `connDiffTensor_neg` beside
  `CovariantDerivative.difference` (Mathlib — not editable, kept private here); `normSqRS_neg` beside
  `normSqRS` (`Tensor/RSTensor/FiberMetric/TensorRSMetric.lean`, where only the algebraic
  `adjointRS`-negation route is in scope — kept private here with the robust component-sum proof).
  All three are hoist candidates.
* **Bridge 2** (`metricDeriv_eq_covDeriv_norm`) — the order-`1` identity
  `metricDerivNorm 1 g₂ g₁ g₁ x = metricCovDerivNorm 1 g₂ g₁ x`.  The two seminorms differ only by
  the reference metric's own covariant derivative, which vanishes by metric compatibility
  (`metricCovDeriv g₁ g₁ 1 x = 0`, via `nabla_metric_zero`), so
  `metricDiffCovDerivAt 1 g₂ g₁ g₁ x = metricCovDeriv g₂ g₁ 1 x` exactly.

`diffStep_jet_one_le` then composes `diffStep_norm_le` + bridge 1 + `lcDiff_norm_le` + bridge 2 +
the class jet bound to the explicit constant `C(Λ,Λ') = (3/2)·√(Λ³)·Λ'` (confirming the
Session-6 estimate). -/

/-- **The `CovariantDerivative.difference` argument-swap antisymmetry**:
`D(cov,cov')(w)(u) = −D(cov',cov)(w)(u)`.  Since `D(cov,cov')(σ x) = ∇^{cov}σ − ∇^{cov'}σ`, swapping
the two connections negates it (each vector is the value at `x` of a smooth section). -/
private theorem diff_swap
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M)
    (w u : TangentSpace I x) :
    ((CovariantDerivative.difference cov cov' x) w) u
      = -(((CovariantDerivative.difference cov' cov x) w) u) := by
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  obtain ⟨σ, hσ⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x w
  have hd1 := IsCovariantDerivativeOn.difference_apply
    (hcov := cov.isCovariantDerivativeOnUniv) (hcov' := cov'.isCovariantDerivativeOnUniv)
    (σ := fun p => (σ p : TangentSpace I p)) (x := x) (hx := trivial)
    (σ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have hd2 := IsCovariantDerivativeOn.difference_apply
    (hcov := cov'.isCovariantDerivativeOnUniv) (hcov' := cov.isCovariantDerivativeOnUniv)
    (σ := fun p => (σ p : TangentSpace I p)) (x := x) (hx := trivial)
    (σ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have h1 : ((CovariantDerivative.difference cov cov' x) w) u
      = (cov (fun p => σ p) x) u - (cov' (fun p => σ p) x) u := by
    have h := congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L u) hd1
    rw [← hσ]; simpa using h
  have h2 : ((CovariantDerivative.difference cov' cov x) w) u
      = (cov' (fun p => σ p) x) u - (cov (fun p => σ p) x) u := by
    have h := congrArg (fun L : TangentSpace I x →L[Real] TangentSpace I x => L u) hd2
    rw [← hσ]; simpa using h
  rw [h1, h2]; abel

/-- **Bridge 1**: swapping the two connection arguments of `connectionDifferenceTensorAt` leaves the
`g₀`-Hilbert–Schmidt fibre norm unchanged (the connection-argument-swap antisymmetry of
`normSqRS(connectionDifferenceTensorAt …)`).  Proved componentwise at a `g₀`-orthonormal basis
(`normSqRS = ∑ component²`): each `(1,2)` component is `basis.coord k (D(cov,cov')(e_j)(e_i))`
(`componentRS_connectionDifferenceTensorAt`), the swap negates it (`diff_swap` + `map_neg`), and the
square is unchanged.  This folds the negation invariance of `normSqRS` and the `difference` swap into
a single component-sum argument (both tensor spaces are non-reducible `def`s, so a standalone
`normSqRS_neg` / `connectionDifferenceTensorAt` negation would fight the coercions). -/
private theorem connDiffTensor_normSqRS_swap
    (g₀ : SmoothRiemannianMetric I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)) (x : M) :
    normSqRS (I := I) (g := g₀) (x := x) 1 2 (connectionDifferenceTensorAt (I := I) cov cov' x)
      = normSqRS (I := I) (g := g₀) (x := x) 1 2 (connectionDifferenceTensorAt (I := I) cov' cov x) := by
  classical
  obtain ⟨basis, hON⟩ := exists_gOrthonormalBasis (I := I) g₀ x
  have hinv : MetricInverseInBasis_gen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSqRS_identity_eq_componentL2SqRS (I := I) g₀ x 1 2 basis hinv
      (connectionDifferenceTensorAt (I := I) cov cov' x),
    normSqRS_identity_eq_componentL2SqRS (I := I) g₀ x 1 2 basis hinv
      (connectionDifferenceTensorAt (I := I) cov' cov x)]
  unfold componentL2SqRS
  refine Finset.sum_congr rfl (fun up _ => Finset.sum_congr rfl (fun low _ => ?_))
  have hup : up = (fun _ : Fin 1 => up 0) := by funext i; fin_cases i; rfl
  have hlow : low = (fun q : Fin 2 => if q = 0 then low 0 else low 1) := by
    funext q; fin_cases q <;> rfl
  have hc1 :
      componentRS_gen (I := I) basis (connectionDifferenceTensorAt (I := I) cov cov' x) up low
        = basis.coord (up 0)
          ((CovariantDerivative.difference cov cov' x (basis (low 1))) (basis (low 0))) := by
    rw [componentRS_gen_congr_slots basis
      (connectionDifferenceTensorAt (I := I) cov cov' x) hup hlow]
    exact componentRS_connectionDifferenceTensorAt (I := I) basis cov cov' (low 0) (low 1) (up 0)
  have hc2 :
      componentRS_gen (I := I) basis (connectionDifferenceTensorAt (I := I) cov' cov x) up low
        = basis.coord (up 0)
          ((CovariantDerivative.difference cov' cov x (basis (low 1))) (basis (low 0))) := by
    rw [componentRS_gen_congr_slots basis
      (connectionDifferenceTensorAt (I := I) cov' cov x) hup hlow]
    exact componentRS_connectionDifferenceTensorAt (I := I) basis cov' cov (low 0) (low 1) (up 0)
  rw [hc1, hc2, diff_swap cov cov' x (basis (low 1)) (basis (low 0)), map_neg]
  ring

/-- The reference metric's own first covariant derivative vanishes (metric compatibility):
`metricCovDeriv g g 1 x = 0`.  Reduces through `metricCovDeriv_one_apply_section` to
`nabla0SFun (LC g) (metricTensorField g) = 0` (`nabla_metric_zero`). -/
private theorem metricCovDeriv_self_one_zero (g : SmoothRiemannianMetric I M) (x : M) :
    metricCovDeriv (I := I) g g 1 x = 0 := by
  classical
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  refine ContinuousMultilinearMap.ext (fun w => ?_)
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at_gen (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (w 0)
  have hw : w = Fin.cons (X x) (Fin.tail w) := by
    rw [hX]; exact (Fin.cons_self_tail w).symm
  have hbase : metricCovDeriv (I := I) g g 0 = metricTensorField (I := I) g := rfl
  conv_lhs => rw [hw]
  erw [metricCovDeriv_one_apply_section (I := I) g g X x (Fin.tail w), hbase,
    nabla_metric_zero (I := I) (leviCivitaConnectionOfMetric (I := I) g) g
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) X x]
  rfl

/-- **Bridge 2**: at order `1` the metric-difference seminorm against the reference metric equals the
metric covariant-derivative seminorm, `metricDerivNorm 1 g₂ g₁ g₁ x = metricCovDerivNorm 1 g₂ g₁ x`. -/
private theorem metricDeriv_eq_covDeriv_norm (g₁ g₂ : SmoothRiemannianMetric I M) (x : M) :
    metricDerivNorm (I := I) 1 g₂ g₁ g₁ x = metricCovDerivNorm (I := I) 1 g₂ g₁ x := by
  unfold metricDerivNorm metricCovDerivNorm metricDiffCovDerivAt
  have h0 : metricCovDeriv (I := I) g₂ g₁ 1 x - metricCovDeriv (I := I) g₁ g₁ 1 x
      = metricCovDeriv (I := I) g₂ g₁ 1 x := by
    rw [metricCovDeriv_self_one_zero (I := I) g₁ x]; abel
  rw [h0]

/-- **The jet-composed `j = 1` endpoint** (brick T, order-1 boundary).  Under Λ-comparability of
`g₁, g₂` and a first-order metric covariant-derivative bound `Λ'` (both on `K`), the single-step
connection-difference `diffStep g₁ g₂ s S = ∇^{g₁}S − ∇^{g₂}S` is bounded fibre-wise at `x ∈ K` by the
explicit constant `C(Λ,Λ') = (3/2)·√(Λ³)·Λ'` times the dimension/slot factor `s·n^{(s+1)/2}`:
`√normSq0S(g₂, diffStep g₁ g₂ s S x) ≤ s·n^{(s+1)/2}·((3/2)·√(Λ³)·Λ')·√normSq0S(g₂, S x)`
(`n = finrank ℝ E`).  Composes `diffStep_norm_le` (fibre atom), the connection-swap bridge
`connDiffTensor_normSqRS_swap`, `lcDiff_norm_le` (Koszul/change-of-connection), the seminorm bridge
`metricDeriv_eq_covDeriv_norm`, and the class jet bound. -/
theorem diffStep_jet_one_le
    [I.Boundaryless] [CompactSpace M]
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    {Λ Λ' : Real}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    {x : M} (hx : x ∈ K) :
    Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (diffStep (I := I) g₁ g₂ s S x)) ≤
      (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 1)) *
        ((3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ')) *
        Real.sqrt (normSq0S (I := I) g₂ x s (S x)) := by
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  -- bound the Koszul connection-difference fibre norm by the jet constant
  have hconn :
      Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
          (connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
        (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') := by
    rw [connDiffTensor_normSqRS_swap g₂ (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x]
    calc
      Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
            (connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₂)
              (leviCivitaConnectionOfMetric (I := I) g₁) x))
          ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * metricDerivNorm (I := I) 1 g₂ g₁ g₁ x) :=
            lcDiff_norm_le (I := I) g₁ g₂ hEq hx
      _ = (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * metricCovDerivNorm (I := I) 1 g₂ g₁ x) := by
            rw [metricDeriv_eq_covDeriv_norm]
      _ ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hjet x hx) (Real.sqrt_nonneg _)) (by norm_num)
  -- compose with the fibre atom
  refine le_trans (diffStep_norm_le (I := I) g₁ g₂ s S x) ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact mul_le_mul_of_nonneg_left hconn (by positivity)

/-! #### Base-Leibniz norm bound for the mixed connection-difference derivative (brick T-B)

The `∇₂A` layer of the base-Leibniz norm recursion, with the order-1 connection-difference-derivative
output-vector bound taken as the **abstract hypothesis `hA1`** (discharged later by B2's
`covDerivConnDiff_fibreNorm_le ∘ P2`, `HCGCompactness/ConnDiffDerivBound.lean`).  The eval identity
`diffStep_leibniz_eval` (`MetricCovDerivLinear.lean`) expands
`covStep g₂ (diffStep g₁ g₂ s S)` — the outer base covariant derivative of the single-step connection
difference — into `(∇₂A) ⋆ S + A ⋆ (∇₂S)`; each `(∇₂A)`-insertion is bounded by `hA1`, each
`A`-insertion by the a=0 atom `connDiffVec_norm_le`, and the frame components are summed as in
`diffStep_norm_le`.

`covStepDiff_norm_le` is the atom (with the `A`-atom fibre norm `NA` explicit); `covStepDiff_jet_le`
folds `NA ≤ (3/2)·√(Λ³)·Λ'` (Koszul, as in `diffStep_jet_one_le`) into the class currency, delivering
the `D_N`-recursion shape `C(CA,Λ,Λ',s,n)·(‖S‖ + ‖∇₂S‖)`.  This is the base-Leibniz norm layer the
`D_N` telescoping recursion consumes (applying `covStep g₂` to a `diffStep` factor is controlled by the
lower-order `iterCov g₂` currency); the three T-B consumers (S0 `j ≥ 2`, 2a-tel comp (b), S1 `hcurv`)
close once B2 discharges `hA1`. -/

/-- **Base-Leibniz norm atom for the mixed connection-difference derivative** (brick T-B, the `∇₂A`
layer, `A`-atom fibre norm `NA` explicit).  Under the abstract order-1 connection-difference-derivative
bound `hA1` (the `covDerivConnDiff` output-vector estimate `√(g₂(∇₂_v A(w,u), ·)) ≤ CA·|v|·|w|·|u|`),
the `g₂`-fibre norm of `covStep g₂ (diffStep g₁ g₂ s S)` — the eval-form `(∇₂A)⋆S + A⋆(∇₂S)` of the
base-Leibniz split (`diffStep_leibniz_eval`) — is bounded by
`s·n^{(s+2)/2}·(CA·‖S‖ + NA·‖∇₂S‖)` (`n = finrank ℝ E`, `NA =
√normSqRS(g₂, connectionDifferenceTensorAt (LC g₁)(LC g₂) x)` the a=0 connection-difference atom). -/
theorem covStepDiff_norm_le
    (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) {CA : ℝ} (hCA : 0 ≤ CA)
    (hA1 : ∀ (v w u : TangentSpace I x),
      Real.sqrt (g₂.inner x
          (covDerivConnDiff (I := I) g₂ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₂ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        CA * Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
          Real.sqrt (g₂.inner x u u)) :
    Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x)) ≤
      (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
        (CA * Real.sqrt (normSq0S (I := I) g₂ x s (S x)) +
          Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
            (connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x)) *
            Real.sqrt (normSq0S (I := I) g₂ x (s + 1)
              (covStep (I := I) g₂ s S x))) := by
  classical
  haveI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  -- internal `g₂`-orthonormal frame at `x` (as in `diffStep_norm_le`)
  let D := (tangentMetricData_gen (I := I) g₂ x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : ∀ i j, g₂.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g₂.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen
      (tangentMetricData_gen (I := I) g₂ x) (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j
    constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  have hbnorm : ∀ i, Real.sqrt (g₂.inner x (basis i) (basis i)) = 1 := by
    intro i; rw [hON i i]; simp
  set NA := Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
    (connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNA
  set NS := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hNS
  set NcovS := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hNcovS
  have hNSnn : 0 ≤ NS := Real.sqrt_nonneg _
  have hNcovS_nn : 0 ≤ NcovS := Real.sqrt_nonneg _
  set B : ℝ := (s : ℝ) * CA * NS + (s : ℝ) * NA * NcovS with hB
  have hBnn : 0 ≤ B := by rw [hB]; positivity
  have hcomp : ∀ φ : Fin (s + 2) → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x) φ| ≤ B := by
    intro φ
    rw [component0S_apply]
    let Wsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ 0)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ 0)))
    let Vsec : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ (Fin.succ 0))))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ (Fin.succ 0))))
    let Zsec : Fin s → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M -> Type _) :=
      fun a => ContMDiffSection.mk (smoothExtensionTangent (I := I) x (basis (φ a.succ.succ)))
        (smoothExtensionTangent_contMDiff (I := I) x (basis (φ a.succ.succ)))
    have hWval : Wsec x = basis (φ 0) := smoothExtensionTangent_eq (I := I) x (basis (φ 0))
    have hVval : Vsec x = basis (φ (Fin.succ 0)) :=
      smoothExtensionTangent_eq (I := I) x (basis (φ (Fin.succ 0)))
    have hZval : ∀ a : Fin s, Zsec a x = basis (φ a.succ.succ) :=
      fun a => smoothExtensionTangent_eq (I := I) x (basis (φ a.succ.succ))
    have htuple : (fun j : Fin (s + 2) => basis (φ j)) =
        Fin.cons (Wsec x) (Fin.cons (Vsec x) (fun a : Fin s => Zsec a x)) := by
      funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact hWval.symm
      · refine Fin.cases ?_ (fun k => ?_) i
        · exact hVval.symm
        · exact (hZval k).symm
    rw [htuple, diffStep_leibniz_eval (I := I) g₁ g₂ s S Wsec Vsec Zsec x]
    -- per-slot bound for the `(∇₂A) ⋆ S` insertion sum
    have hX : ∀ a : Fin s,
        |(S x) (Function.update (fun b : Fin s => Zsec b x) a
            (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
              (fun y : M => Zsec a y) x))| ≤ NS * CA := by
      intro a
      have hcs := abs_apply_le_sqrt_normSq0S (I := I) g₂ x s basis hON (S x)
        (Function.update (fun b : Fin s => Zsec b x) a
          (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
            (fun y : M => Zsec a y) x))
      have hprodX :
          (∏ b : Fin s, Real.sqrt (g₂.inner x
              ((Function.update (fun b' : Fin s => Zsec b' x) a
                  (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
                    (fun y : M => Zsec a y) x)) b)
              ((Function.update (fun b' : Fin s => Zsec b' x) a
                  (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
                    (fun y : M => Zsec a y) x)) b)))
            = Real.sqrt (g₂.inner x
                (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
                  (fun y : M => Zsec a y) x)
                (covDerivConnDiff (I := I) g₂ g₁ (fun y : M => Wsec y) (fun y : M => Vsec y)
                  (fun y : M => Zsec a y) x)) := by
        rw [Finset.prod_eq_single a
          (fun b _ hb => by rw [Function.update_of_ne hb, hZval b]; exact hbnorm (φ b.succ.succ))
          (fun ha => absurd (Finset.mem_univ a) ha), Function.update_self]
      rw [hprodX, ← hNS] at hcs
      refine le_trans hcs (mul_le_mul_of_nonneg_left ?_ hNSnn)
      have h := hA1 (basis (φ 0)) (basis (φ (Fin.succ 0))) (basis (φ a.succ.succ))
      rw [hbnorm (φ 0), hbnorm (φ (Fin.succ 0)), hbnorm (φ a.succ.succ),
        mul_one, mul_one, mul_one] at h
      exact h
    -- per-slot bound for the `A ⋆ (∇₂S)` insertion sum
    have hY : ∀ a : Fin s,
        |(covStep (I := I) g₂ s S x)
            (Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
              ((CovariantDerivative.difference
                  (leviCivitaConnectionOfMetric (I := I) g₁)
                  (leviCivitaConnectionOfMetric (I := I) g₂) x (Zsec a x)) (Vsec x))))|
          ≤ NcovS * NA := by
      intro a
      set tup : Fin (s + 1) → TangentSpace I x :=
        Fin.cons (Wsec x) (Function.update (fun b : Fin s => Zsec b x) a
          ((CovariantDerivative.difference
              (leviCivitaConnectionOfMetric (I := I) g₁)
              (leviCivitaConnectionOfMetric (I := I) g₂) x (Zsec a x)) (Vsec x))) with htup
      have hcs := abs_apply_le_sqrt_normSq0S (I := I) g₂ x (s + 1) basis hON
        (covStep (I := I) g₂ s S x) tup
      have hprodY :
          (∏ b : Fin (s + 1), Real.sqrt (g₂.inner x (tup b) (tup b)))
            = Real.sqrt (g₂.inner x
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x (Zsec a x)) (Vsec x))
                ((CovariantDerivative.difference
                    (leviCivitaConnectionOfMetric (I := I) g₁)
                    (leviCivitaConnectionOfMetric (I := I) g₂) x (Zsec a x)) (Vsec x))) := by
        rw [htup, Fin.prod_univ_succ, Fin.cons_zero, hWval, hbnorm (φ 0), one_mul]
        simp only [Fin.cons_succ]
        rw [Finset.prod_eq_single a
          (fun b _ hb => by rw [Function.update_of_ne hb, hZval b]; exact hbnorm (φ b.succ.succ))
          (fun ha => absurd (Finset.mem_univ a) ha), Function.update_self]
      rw [hprodY, ← hNcovS] at hcs
      refine le_trans hcs (mul_le_mul_of_nonneg_left ?_ hNcovS_nn)
      have h := connDiffVec_norm_le (I := I) g₂
        (leviCivitaConnectionOfMetric (I := I) g₁)
        (leviCivitaConnectionOfMetric (I := I) g₂)
        (basis (φ (Fin.succ 0))) (basis (φ a.succ.succ))
      rw [hbnorm (φ (Fin.succ 0)), hbnorm (φ a.succ.succ), mul_one, mul_one, ← hNA] at h
      rw [hZval a, hVval]
      exact h
    -- assemble the two insertion sums
    rw [sub_eq_add_neg]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg, abs_neg]
    refine le_trans (add_le_add (Finset.abs_sum_le_sum_abs _ _)
      (Finset.abs_sum_le_sum_abs _ _)) ?_
    refine le_trans (add_le_add (Finset.sum_le_sum (fun a _ => hX a))
      (Finset.sum_le_sum (fun a _ => hY a))) ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hB]; apply le_of_eq; ring
  -- assemble via component → normSq0S bound
  have hcard : normSq0S (I := I) g₂ x (s + 2)
      (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x) ≤
      (Fintype.card (Fin (s + 2) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) * B ^ 2 :=
    normSq0S_le_card_of_component_bound (I := I) g₂ x (s + 2) basis hinv
      (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x) B hBnn hcomp
  have hcard_eq :
      (Fintype.card (Fin (s + 2) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
        = (Module.finrank ℝ E : ℝ) ^ (s + 2) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    rfl
  calc Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
          (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x))
        ≤ Real.sqrt
            ((Fintype.card (Fin (s + 2) → Fin (Module.finrank Real (TangentSpace I x))) : ℝ)
              * B ^ 2) := Real.sqrt_le_sqrt hcard
    _ = Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) * B := by
        rw [hcard_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq hBnn]
    _ = (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) * (CA * NS + NA * NcovS) := by
        rw [hB]; ring

/-- **Base-Leibniz jet-composed norm bound for the mixed connection-difference derivative** (brick
T-B, the `D_N`-recursion endpoint).  Folds the a=0 connection-difference atom `NA` of
`covStepDiff_norm_le` into the class jet currency via `NA ≤ (3/2)·√(Λ³)·Λ'` (Koszul, as in
`diffStep_jet_one_le`).  Under `Λ`-comparability of `g₁, g₂` and a first-order metric
covariant-derivative bound `Λ'` on `K`, together with the abstract `∇₂A` output-vector bound `hA1`,
`covStep g₂ (diffStep g₁ g₂ s S)` is bounded at `x ∈ K` by
`s·n^{(s+2)/2}·(CA + (3/2)·√(Λ³)·Λ')·(‖S‖ + ‖∇₂S‖)`.  This is the base-Leibniz norm layer the `D_N`
telescoping recursion consumes; the three T-B consumers close once B2 discharges `hA1`. -/
theorem covStepDiff_jet_le
    [I.Boundaryless] [CompactSpace M]
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (s : ℕ)
    (S : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) {CA Λ Λ' : ℝ} (hCA : 0 ≤ CA)
    (hA1 : ∀ (v w u : TangentSpace I x),
      Real.sqrt (g₂.inner x
          (covDerivConnDiff (I := I) g₂ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)
          (covDerivConnDiff (I := I) g₂ g₁
            (smoothExtensionTangent (I := I) x v)
            (smoothExtensionTangent (I := I) x w)
            (smoothExtensionTangent (I := I) x u) x)) ≤
        CA * Real.sqrt (g₂.inner x v v) * Real.sqrt (g₂.inner x w w) *
          Real.sqrt (g₂.inner x u u))
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hx : x ∈ K) :
    Real.sqrt (normSq0S (I := I) g₂ x (s + 2)
        (covStep (I := I) g₂ (s + 1) (diffStep (I := I) g₁ g₂ s S) x)) ≤
      (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
        (CA + (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ')) *
        (Real.sqrt (normSq0S (I := I) g₂ x s (S x)) +
          Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x))) := by
  haveI : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  haveI : IsManifold I (1 + 1) M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide : ((1 : WithTop ℕ∞) + 1) ≤ ∞)
  haveI : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by change IsManifold I ∞ M; infer_instance
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := 1)
  -- Koszul connection-difference fibre bound by the jet constant (as in `diffStep_jet_one_le`)
  have hconn :
      Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
          (connectionDifferenceTensorAt (I := I)
            (leviCivitaConnectionOfMetric (I := I) g₁)
            (leviCivitaConnectionOfMetric (I := I) g₂) x)) ≤
        (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') := by
    rw [connDiffTensor_normSqRS_swap g₂ (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x]
    calc
      Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
            (connectionDifferenceTensorAt (I := I)
              (leviCivitaConnectionOfMetric (I := I) g₂)
              (leviCivitaConnectionOfMetric (I := I) g₁) x))
          ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * metricDerivNorm (I := I) 1 g₂ g₁ g₁ x) :=
            lcDiff_norm_le (I := I) g₁ g₂ hEq hx
      _ = (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * metricCovDerivNorm (I := I) 1 g₂ g₁ x) := by
            rw [metricDeriv_eq_covDeriv_norm]
      _ ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hjet x hx) (Real.sqrt_nonneg _)) (by norm_num)
  have hmcnn : (0 : ℝ) ≤ metricCovDerivNorm (I := I) 1 g₂ g₁ x := Real.sqrt_nonneg _
  have hΛ'nn : 0 ≤ Λ' := le_trans hmcnn (hjet x hx)
  refine le_trans (covStepDiff_norm_le (I := I) g₁ g₂ s S x hCA hA1) ?_
  set NS := Real.sqrt (normSq0S (I := I) g₂ x s (S x)) with hNS
  set NcovS := Real.sqrt (normSq0S (I := I) g₂ x (s + 1) (covStep (I := I) g₂ s S x)) with hNcovS
  set NA := Real.sqrt (normSqRS (I := I) (g := g₂) (x := x) 1 2
    (connectionDifferenceTensorAt (I := I)
      (leviCivitaConnectionOfMetric (I := I) g₁)
      (leviCivitaConnectionOfMetric (I := I) g₂) x)) with hNAdef
  have hNSnn : 0 ≤ NS := Real.sqrt_nonneg _
  have hNcovS_nn : 0 ≤ NcovS := Real.sqrt_nonneg _
  have hDnn : 0 ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') := by positivity
  have hstep : CA * NS + NA * NcovS ≤
      (CA + (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ')) * (NS + NcovS) := by
    have h1 : NA * NcovS ≤ (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ') * NcovS :=
      mul_le_mul_of_nonneg_right hconn hNcovS_nn
    nlinarith [h1, mul_nonneg hCA hNcovS_nn, mul_nonneg hDnn hNSnn]
  calc (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) * (CA * NS + NA * NcovS)
        ≤ (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
            ((CA + (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ')) * (NS + NcovS)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = (s : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (s + 2)) *
          (CA + (3 / 2 : Real) * (Real.sqrt (Λ ^ 3) * Λ')) * (NS + NcovS) := by ring

end DiffStepNorm

/-! ### Volume level — chart-Gram / chart-density cross-metric comparison

The volume brick `dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}`.  `chartDensity g x₀ x = √det(chartGramMatrix
g x₀ x)`, so the comparison reduces to the Loewner→determinant estimate `det(chartGram g₀) ≤
Λ^n·det(chartGram gBase)` (`det_le_of_posSemidef_le`) fed by the chart-Gram quadratic-form
comparison below.  The measure-level lift (via `chart_lintegral_le` and the POU sum) is the
remaining piece; see `UnifCovSumCross.md`. -/

/-- **Chart-Gram quadratic-form comparison** (volume-brick step 2).  `Λ`-comparability of
`g₀`, `gBase` transfers to a pointwise Loewner bound on their chart-Gram matrices: the
`g₀`-Gram quadratic form is bounded by `Λ` times the `gBase`-Gram quadratic form, at every
point and coefficient vector.  Proved by writing each quadratic form as the fibre inner
product of the same linear combination of chart-basis vectors and applying comparability. -/
theorem chartGram_quad_le_of_equiv
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x₀ x : M) (v : Fin (Module.finrank ℝ E) → ℝ) :
    v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v ≤
      Λ * (v ⬝ᵥ (chartGramMatrix (I := I) gBase x₀ x) *ᵥ v) := by
  have hg₀ : v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v =
      g₀.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
    rw [← chartGramMatrix_dotProduct_mulVec (I := I) g₀ x₀ x v, star_trivial]
  have hgB : v ⬝ᵥ (chartGramMatrix (I := I) gBase x₀ x) *ᵥ v =
      gBase.inner x (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)
        (∑ j, v j • chartBasisVecFiber (I := I) x₀ j x) := by
    rw [← chartGramMatrix_dotProduct_mulVec (I := I) gBase x₀ x v, star_trivial]
  rw [hg₀, hgB]
  exact (hEq.2 x (Set.mem_univ x)
    (∑ i, v i • chartBasisVecFiber (I := I) x₀ i x)).2

/-- **Chart-density cross-metric bound** (volume-brick step 3).  On the tangent trivialization
base set — where both chart-Gram matrices are positive-definite — the `g₀` chart density is
bounded by `√(Λ^n)` times the `gBase` chart density (`n = finrank ℝ E`), the pointwise
`Λ^{n/2}` volume-density comparison.  Combines the chart-Gram quadratic comparison with the
Loewner→determinant estimate and `√`-monotonicity. -/
theorem chartDensity_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ)
    (x₀ : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    chartDensity (I := I) g₀ x₀ x ≤
      Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) gBase x₀ x := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hEq.1
  have hA : (chartGramMatrix (I := I) g₀ x₀ x).PosSemidef :=
    (chartGramMatrix_posDef (I := I) g₀ x₀ hx).posSemidef
  have hB : (Λ • chartGramMatrix (I := I) gBase x₀ x).PosDef :=
    (chartGramMatrix_posDef (I := I) gBase x₀ hx).smul hΛpos
  have hAB : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
      v ⬝ᵥ (chartGramMatrix (I := I) g₀ x₀ x) *ᵥ v ≤
        v ⬝ᵥ (Λ • chartGramMatrix (I := I) gBase x₀ x) *ᵥ v := by
    intro v
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact chartGram_quad_le_of_equiv (I := I) gBase g₀ hEq x₀ x v
  have hdet : (chartGramMatrix (I := I) g₀ x₀ x).det ≤
      Λ ^ Module.finrank ℝ E * (chartGramMatrix (I := I) gBase x₀ x).det := by
    have h := det_le_of_posSemidef_le hA hB hAB
    rwa [Matrix.det_smul, Fintype.card_fin] at h
  change Real.sqrt ((chartGramMatrix (I := I) g₀ x₀ x).det) ≤
    Real.sqrt (Λ ^ Module.finrank ℝ E) *
      Real.sqrt ((chartGramMatrix (I := I) gBase x₀ x).det)
  rw [← Real.sqrt_mul (pow_nonneg hΛpos.le _)]
  exact Real.sqrt_le_sqrt hdet

/-! ### Volume level — measure comparison (volume-brick step 4)

Lifting the pointwise chart-density bound `chartDensity_cross_le` through the finite chart
partition of unity gives the two Riemannian volume *measures* compared with the explicit
constant `√(Λ^n)`.  The compact closed-manifold measure infrastructure enters only here. -/
section VolumeMeasure

open MeasureTheory
open scoped ENNReal

variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Volume-measure cross-metric comparison** (volume-brick step 4).  The two Riemannian
volume measures of `Λ`-comparable metrics are two-sidedly comparable with the explicit constant
`√(Λ^n)` (`n = finrank ℝ E`): `dV_{g₀} ≤ Λ^{n/2}·dV_{gBase}` and symmetrically.  Proved by
lifting `chartDensity_cross_le` through the finite chart partition of unity (`chart_lintegral_le`
+ the POU lower-integral decomposition) and reading off the measure inequality on measurable
sets.  This is the `Λ`-uniform volume comparison the S0 `L²` assembly composes with the fibre
and connection-change bricks. -/
theorem volumeMeasure_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ) :
    riemannianVolumeMeasure (I := I) (M := M) g₀ ≤
        ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := M) gBase ∧
      riemannianVolumeMeasure (I := I) (M := M) gBase ≤
        ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := M) g₀ := by
  classical
  -- POU decomposition of the volume lower-integral, re-derived from public primitives
  have vsum : ∀ (g : SmoothRiemannianMetric I M) (F : M → ℝ≥0∞), Measurable F →
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro g F hF
    rw [riemannianVolumeMeasure_def,
      riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF]
    refine tsum_eq_sum (fun α hα => ?_)
    have hz : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    simp only [hz, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  -- each POU weight is supported inside the trivialization base set
  have hbase : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro α x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) α hx
  -- lower-integral comparison from a directional pointwise chart-density bound
  have lintComp : ∀ (q h : SmoothRiemannianMetric I M),
      (∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
        chartDensity (I := I) h α x ≤
          Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) q α x) →
      ∀ (F : M → ℝ≥0∞), Measurable F →
        ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h) ≤
          ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) *
            ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
    intro q h hdens F hF
    rw [vsum h F hF, vsum q F hF, Finset.mul_sum]
    refine Finset.sum_le_sum (fun α _ => ?_)
    exact chart_lintegral_le (I := I) (M := M) q h α
      (Real.sqrt (Λ ^ Module.finrank ℝ E)) (Real.sqrt_nonneg _) (hdens α) hF
  -- the two directional density bounds from `chartDensity_cross_le`
  have hdens_fwd : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      chartDensity (I := I) g₀ α x ≤
        Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) gBase α x :=
    fun α _ hx => chartDensity_cross_le (I := I) gBase g₀ hEq α (hbase α _ hx)
  have hdens_rev : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      chartDensity (I := I) gBase α x ≤
        Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) g₀ α x :=
    fun α _ hx =>
      chartDensity_cross_le (I := I) g₀ gBase
        (metricUniformEquivalentOn_symm (I := I) hEq) α (hbase α _ hx)
  refine ⟨?_, ?_⟩
  · rw [Measure.le_iff]
    intro s hs
    have h := lintComp gBase g₀ hdens_fwd (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]
  · rw [Measure.le_iff]
    intro s hs
    have h := lintComp g₀ gBase hdens_rev (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]

end VolumeMeasure

end RicciFlow
end PDE
end DifferentialGeometry
