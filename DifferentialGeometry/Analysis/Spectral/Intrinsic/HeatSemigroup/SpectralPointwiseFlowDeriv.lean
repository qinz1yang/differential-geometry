import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralEigenSeriesJointGram
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.PerMode
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs

/-! # Pointwise spectral flow-derivative of a realized symmetrized bilinear form

For a smooth representative family `F : ℝ → SmoothCcTensor g 0 2` whose `L²`
eigen-coordinates on a closed time slab are a `C∞`-in-time family `φ` (with a
`t`-independent, summable-across-modes all-order time-jet spectral-mass majorant), the
chart-evaluated symmetrized bilinear form `s ↦ ccTensorBilinSymm g (F s) x v w` is the
convergent eigen-series `∑' i, φ i s · ψ i` with `ψ i = ccTensorBilinSymm g (eigenSmooth i)
x v w` a fixed (time-independent) scalar.  The eigen-series differentiates term-by-term
(Mathlib's `hasDerivAt_tsum`), so the function has, at every interior slab time, the
`[0, ∞)`-pointwise derivative `∑' i, (deriv (φ i) t) · ψ i`.

This is the pure-spectral soundness bedrock behind the realized Ricci–DeTurck flow
derivative: the genuine analytic content is the chart-`C⁰` spectral convergence
`spectralPartialSum_ccTensorBilinSymm_tendsto` (proved in
`SpectralEigenSeriesJointGram.lean` for the chart-Gram increment, here re-derived in the
arbitrary-`(x, v, w)` form from the same public chart-frame reconstruction
`ccTensorBilinSymm_eq_sum_chartBasis` and the POU-weighted chart-component limit
`spectralChartComponent_tendsto`), and the uniform-in-time summable majorant for the
time-derivative spectral series (assembled from the supplied time-jet mode-mass and the
supercritical Weyl tail `tensorEigen_summable_negpow`).  No fibre-bundle topology is used:
the scalar reconstruction is entirely chart-frame and real-valued. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- **The closed-set / one-sided `tsum` derivative for real series.**  The
`HasDerivWithinAt` analogue of Mathlib's `hasDerivAt_tsum`: on a convex set with a summable
uniform bound on the term within-derivatives and termwise within-differentiability, the
real-valued series `∑' i, f i ·` has within-derivative `∑' i, f' i x` at every point.  The
`HasFDerivWithinAt` engine is `DifferentialGeometry.Analysis.hasFDerivWithinAt_tsum`;
`toSpanSingleton` (a continuous linear map) commutes with the `∑'` (`map_tsum`). -/
theorem hasDerivWithinAt_tsum {α : Type*} {f : α → ℝ → ℝ} {f' : α → ℝ → ℝ}
    {u : α → ℝ} {s : Set ℝ}
    (hf : ∀ (i : α) (z : ℝ), z ∈ s → HasDerivWithinAt (f i) (f' i z) s z)
    (hf' : ∀ (i : α) (z : ℝ), z ∈ s → ‖f' i z‖ ≤ u i) (hu : Summable u) (hs : Convex ℝ s)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (hf0 : Summable fun i => f i x₀) {x : ℝ} (hx : x ∈ s) :
    HasDerivWithinAt (fun y => ∑' i, f i y) (∑' i, f' i x) s x := by
  classical
  have hsumf' : Summable fun i => f' i x :=
    Summable.of_norm_bounded hu (fun i => hf' i x hx)
  have hF : ∀ (i : α) (z : ℝ), z ∈ s →
      HasFDerivWithinAt (f i) (ContinuousLinearMap.toSpanSingleton ℝ (f' i z)) s z :=
    fun i z hz => (hf i z hz).hasFDerivWithinAt
  have hFbd : ∀ (i : α) (z : ℝ), z ∈ s →
      ‖ContinuousLinearMap.toSpanSingleton ℝ (f' i z)‖ ≤ u i := by
    intro i z hz
    rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
    exact hf' i z hz
  have hkey := DifferentialGeometry.Analysis.hasFDerivWithinAt_tsum
    hF hFbd hu hs hx₀ hf0 hx
  have hderiv := hkey.hasDerivWithinAt

  have hsumF : Summable fun i => ContinuousLinearMap.toSpanSingleton ℝ (f' i x) := by
    refine Summable.of_norm_bounded hu (fun i => ?_)
    rw [ContinuousLinearMap.norm_toSpanSingleton, Real.norm_eq_abs]
    exact hf' i x hx
  have heval : (∑' i, ContinuousLinearMap.toSpanSingleton ℝ (f' i x)) (1 : ℝ) =
      ∑' i, f' i x := by
    rw [show (∑' i, ContinuousLinearMap.toSpanSingleton ℝ (f' i x)) (1 : ℝ) =
        (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ))
          (∑' i, ContinuousLinearMap.toSpanSingleton ℝ (f' i x)) from rfl,
      ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) hsumF]
    refine tsum_congr (fun i => ?_)
    simp [ContinuousLinearMap.apply_apply, ContinuousLinearMap.toSpanSingleton_apply]
  rwa [heval] at hderiv

/-- **All-order Sobolev membership of an `L²` tensor with summable weighted coordinate
squares** (public).  If for every `σ ≥ 0` the weighted eigenbasis-coordinate squares of `u`
are summable across modes, then `u` lies, via the chart-locality-free realization
`tensorHsToL2`, in `Hˢ` for every `σ ≥ 0`: the witness `Hˢ`-element is the coordinate
family of `u` itself, whose `tensorHsToL2` image has the same coordinates as `u` (hence
equals `u` by eigenbasis-coordinate faithfulness — `HilbertBasis.repr` injectivity). -/
theorem allHs_of_weighted_summable_pub
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hsum : ∀ σ : ℝ, 0 ≤ σ →
      Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
        tensorSobolevWeight (I := I) (M := M) i σ *
          (tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i) ^ 2)) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u := by
  intro σ hσ
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  set v : tensorHs (I := I) (M := M) g 0 2 σ :=
    { coeff := fun i => tensorL2Coeff (I := I) (M := M) hc u i
      weighted_summable := hsum σ hσ } with hv
  refine ⟨v, ?_⟩
  set b := Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) hc with hb
  apply b.repr.injective
  ext i
  have hlhs : (b.repr (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2) hc hσ v)) i =
      tensorL2Coeff (I := I) (M := M) hc
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2) hc hσ v) i := rfl
  have hrhs : (b.repr u) i = tensorL2Coeff (I := I) (M := M) hc u i := rfl
  rw [hlhs, hrhs, tensorHsToL2_tensorL2Coeff]

/-- **Metric-tag transport of the symmetrized extracted bilinear form.**  The fibre value
`ccTensorBilinSymm g T x v w` depends only on the underlying smooth section `T.toSection`
(the metric tag `g` of `SmoothCcTensor g 0 2` is a pure phantom type parameter, used by
neither `ccTensorMultilinear` nor `ccTensorModel`), so two smooth tensors with equal
sections — even over different metric tags — extract the same bilinear value. -/
theorem ccTensorBilinSymm_toSection_congr
    {g₁ g₂ : SmoothRiemannianMetric I M}
    (S₁ : SmoothCcTensor g₁ 0 2) (S₂ : SmoothCcTensor g₂ 0 2)
    (hsec : S₁.toSection = S₂.toSection)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₁ S₁ x v w = ccTensorBilinSymm (I := I) g₂ S₂ x v w := by
  have hmodel : ∀ (a b : TangentSpace I x),
      ccTensorModel (I := I) g₁ S₁ x ![a, b] = ccTensorModel (I := I) g₂ S₂ x ![a, b] := by
    intro a b
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply, hsec]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
    ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply,
    hmodel v w, hmodel w v]

/-- The fixed (time-independent) per-mode scalar `ψ i = ccTensorBilinSymm g (eigenSmooth i)
x v w`: the symmetrized extracted bilinear form of the `i`-th smooth eigenbasis tensor,
evaluated at the base point `x` on the tangent pair `(v, w)`. -/
def eigenBilinScalar (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ :=
  ccTensorBilinSymm (I := I) g (eigenSmooth (I := I) (M := M) g i) x v w

/-- **The norm of a single eigenbasis tensor in the spectral Sobolev scale.**
`‖smoothCcToTensorHs g σ (eigenSmooth i)‖ = √(tensorSobolevWeight i σ)`: the embedding has
the same coordinate family as the spectral basis vector `tensorHsBasisVec σ i`
(Kronecker `δ`, via `tensorL2Coeff_ofCompact_eigenSmooth`), so it shares its norm
`norm_tensorHsBasisVec`. -/
theorem norm_smoothCcToTensorHs_eigenSmooth (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g σ (eigenSmooth (I := I) (M := M) g i)‖ =
      Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
  classical
  have heq : smoothCcToTensorHs (I := I) (M := M) g σ (eigenSmooth (I := I) (M := M) g i) =
      tensorHsBasisVec (I := I) (M := M) (g := g) (r := 0) (s := 2) σ i := by
    refine tensorHs.ext ?_
    funext j
    rw [smoothCcToTensorHs_coeff, tensorHsBasisVec_coeff,
      show SmoothCcTensor.toL2 (eigenSmooth (I := I) (M := M) g i) =
          (eigenSmooth (I := I) (M := M) g i : TensorL2 0 2 g) from SmoothCcTensor.toL2_apply _,
      tensorL2Coeff_ofCompact_eigenSmooth (I := I) (M := M) g j i]
  rw [heq, norm_tensorHsBasisVec (I := I) (M := M) i]

theorem abs_eigenBilinScalar_le (g : SmoothRiemannianMetric I M) (m : ℕ)
    (h_lossy : 2 * Module.finrank ℝ E + 4 ≤ m)
    (x : M) (v w : TangentSpace I x) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      |eigenBilinScalar (I := I) g x v w i| ≤
        C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) *
          (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g m h_lossy
  refine ⟨C, hC_pos, fun i => ?_⟩
  have hb := hC (eigenSmooth (I := I) (M := M) g i) x v w
  rw [norm_smoothCcToTensorHs_eigenSmooth (I := I) (M := M) g (m : ℝ) i] at hb
  calc |eigenBilinScalar (I := I) g x v w i|
      = |ccTensorBilinSymm (I := I) g (eigenSmooth (I := I) (M := M) g i) x v w| := rfl
    _ ≤ C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) *
          Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := hb
    _ = C * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i (m : ℝ)) *
          (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w)) := by ring

/-- **The `ccTensorBilinSymm` of a finite eigen-combination is the finite coefficient
sum of the per-mode scalars** (arbitrary `(x, v, w)`).  Re-derivation of the (private)
sibling `ccTensorBilinSymm_finiteEigenCombo` from the public additivity
`ccTensorBilinSymm_add` and homogeneity `ccTensorBilinSymm_smul`. -/
theorem ccTensorBilinSymm_finiteEigenCombo'
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (finiteEigenCombo (I := I) (M := M) g F c) x v w =
      ∑ i ∈ F, c i * eigenBilinScalar (I := I) g x v w i := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := by
        rw [zero_smul]
      rw [h0, ccTensorBilinSymm_smul, zero_mul]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ccTensorBilinSymm_add,
        ccTensorBilinSymm_smul, ih]
      rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
open DifferentialGeometry.Analysis.Sobolev.Chart in
/-- **Pointwise chart-`C⁰` spectral convergence of the symmetrized bilinear form**
(arbitrary `(x, v, w)`).  Re-derivation of the (private) sibling
`spectralPartialSum_ccTensorBilinSymm_tendsto` from public chart-frame infrastructure:
the chart-frame fibre reconstruction `ccTensorBilinSymm_eq_sum_chartBasis` and the
POU-weighted chart-component limit `spectralChartComponent_tendsto`, divided by the
positive partition-of-unity weight at a chart where `x` is interior. -/
theorem spectralPartialSum_ccTensorBilinSymm_tendsto'
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u)
    (Trep : SmoothCcTensor g 0 2)
    (hTrep : (Trep : TensorL2 0 2 g) = u)
    (x : M) (v w : TangentSpace I x) :
    Filter.Tendsto
      (fun n => ccTensorBilinSymm (I := I) g
          (spectralPartialSum (I := I) (M := M) g u n) x v w)
      Filter.atTop
      (𝓝 (ccTensorBilinSymm (I := I) g Trep x v w)) := by
  classical
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  have hcauchy : ∀ k : ℕ, CauchySeq (fun n =>
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) (F n)) :=
    fun k => spectralPartialSum_toHs_cauchy (I := I) (M := M) g u hu (2 * k)
  have hF_L2 : Tendsto (fun n => (F n : TensorL2 0 2 g)) atTop (𝓝 u) :=
    spectralPartialSum_toL2_tendsto (I := I) (M := M) g u
  have hsum := chartAtlasPOU_finset_sum_eq_one (I := I) (M := M) x
  have hexists : ∃ β ∈ chartAtlasPOU_finset (I := I) (M := M),
      0 < ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ((chartAtlasPOU I M) β : M → ℝ) x = 0 := by
      intro β hβ
      have hle := hcon β hβ
      have hnn := (chartAtlasPOU I M).nonneg β x
      linarith
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hsum
    exact absurd hsum (by norm_num)
  obtain ⟨β, _hβmem, hβpos⟩ := hexists
  set ρ : ℝ := ((chartAtlasPOU I M) β : C^∞⟮I, M; ℝ⟯) x with hρ_def
  have hx_src : x ∈ (chartAt H β).source := by
    have hsub := chartAtlasPOU_isSubordinate (I := I) (M := M) β
    apply hsub
    exact subset_tsupport _ (Function.mem_support.mpr (ne_of_gt hβpos))
  set yx : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (extChartAt I β x) with hyx_def
  have hyx_mem : yx ∈ chartTargetEuclid (I := I) (M := M) β :=
    toEuclidean_extChartAt_mem_chartTargetEuclid (I := I) (M := M) β hx_src
  have hround : (extChartAt I β).symm (toEuclidean.symm yx) = x := by
    rw [hyx_def, ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I β).left_inv (by rw [extChartAt_source (I := I)]; exact hx_src)
  have hcomp_eq : ∀ (Z : SmoothCcTensor g 0 2) (Q : CompIdx E 0 2),
      tensorChartComponent (I := I) (M := M) g 0 2 Z β Q.1 Q.2 yx =
        ρ * tensorChartComponentRaw (I := I) (M := M) g 0 2 Z β Q.1 Q.2 x := by
    intro Z Q
    rw [tensorChartComponent_def,
      chartPushedRaw_apply_of_mem (I := I) (M := M) β _ hyx_mem, hround]
    rfl
  have hraw_tendsto : ∀ Q : CompIdx E 0 2,
      Tendsto (fun n => tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x)
        atTop (𝓝 (tensorChartComponentRaw (I := I) (M := M) g 0 2 Trep β Q.1 Q.2 x)) := by
    intro Q
    have hct := spectralChartComponent_tendsto (I := I) (M := M) g u hcauchy hF_L2 Trep hTrep
      β Q hyx_mem
    simp only [hcomp_eq] at hct
    have hρne : ρ ≠ 0 := ne_of_gt hβpos
    have hscaled := hct.const_mul ρ⁻¹
    simp only [← mul_assoc, inv_mul_cancel₀ hρne, one_mul] at hscaled
    exact hscaled
  rw [ccTensorBilinSymm_eq_sum_chartBasis (I := I) (M := M) g Trep β hx_src v w]
  have hrw : (fun n => ccTensorBilinSymm (I := I) g (F n) x v w) =
      fun n => ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 (F n) β Q.1 Q.2 x *
          ccBilinSymmFibre (I := I) x
            (chartBasisFiberSection (I := I) (M := M) 0 2 β Q x) v w := by
    funext n
    exact ccTensorBilinSymm_eq_sum_chartBasis (I := I) (M := M) g (F n) β hx_src v w
  rw [hrw]
  refine tendsto_finset_sum _ (fun Q _ => ?_)
  exact (hraw_tendsto Q).mul_const _

/-- **The eigen-series identity for the symmetrized bilinear form** (arbitrary `(x, v, w)`).
For a smooth representative `Trep` of an `L²` tensor `u` that lies in every `Hˢ`, the
symmetrized extracted bilinear form is the convergent eigen-series of the per-mode scalars
weighted by the eigen-coordinates, PROVIDED the eigen-series is summable.  Assembled from
the finite-combination identity, the chart-`C⁰` convergence, and `HasSum`/limit
uniqueness. -/
theorem ccTensorBilinSymm_eigenSeries_eq
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u)
    (Trep : SmoothCcTensor g 0 2) (hTrep : (Trep : TensorL2 0 2 g) = u)
    (x : M) (v w : TangentSpace I x)
    (hsummable : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
        eigenBilinScalar (I := I) g x v w i)) :
    ccTensorBilinSymm (I := I) g Trep x v w =
      ∑' i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
        eigenBilinScalar (I := I) g x v w i := by
  classical
  have hpartial : ∀ n,
      ccTensorBilinSymm (I := I) g (spectralPartialSum (I := I) (M := M) g u n) x v w =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
            eigenBilinScalar (I := I) g x v w i := by
    intro n
    rw [spectralPartialSum, ccTensorBilinSymm_finiteEigenCombo']
  have htend_lhs : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
            eigenBilinScalar (I := I) g x v w i)
      Filter.atTop
      (𝓝 (ccTensorBilinSymm (I := I) g Trep x v w)) := by
    have h := spectralPartialSum_ccTensorBilinSymm_tendsto'
      (I := I) (M := M) g u hu Trep hTrep x v w
    exact h.congr (fun n => hpartial n)
  have htend_tsum : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
            eigenBilinScalar (I := I) g x v w i)
      Filter.atTop
      (𝓝 (∑' i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i *
        eigenBilinScalar (I := I) g x v w i)) :=
    hsummable.hasSum.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)
  exact tendsto_nhds_unique htend_lhs htend_tsum

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
