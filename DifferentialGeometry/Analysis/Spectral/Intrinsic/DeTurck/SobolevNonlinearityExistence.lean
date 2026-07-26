import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RemainderShortTimeExistence
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.ChartDeTurckRemainderPolynomial
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.RawConnLapL2SobolevBounds.RawTensorConnLapIterL2WtwokTwoBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.FaithfulH1Embedding
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LocallyLipschitzTruncation
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingManifoldC0
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingReverseHebeyToHs
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.IteratedCovGradHsJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SpectralPouNormEquiv
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderDefs
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderTameLipschitz
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

/-!
# Short-time existence driven by the continuous (Sobolev) Ricci–DeTurck nonlinearity

This file assembles the **continuous, non-gated** Ricci–DeTurck nonlinearity on the
spectral Sobolev scale by **Nemytskii-by-density / Lipschitz extension**, and feeds it
into the unconditional maximal-regularity engine
`deTurckRemainder_strong_shortTime_exists`
(`Analysis/Spectral/Intrinsic/DeTurck/RemainderShortTimeExistence.lean`).

## The dense-extension architecture (no rough pointwise evaluation, no gating)

A rough Sobolev element of `tensorHs g₀ 0 2 (a+1)` has **no pointwise values**, so it can
neither index the chart polynomial nor be fed to the intrinsic `deTurckRicciRHS` (which
needs a genuine `SmoothRiemannianMetric` and its second chart-derivatives).  The classical
remedy is to define the nonlinearity on **smooth** data and extend by uniform continuity.

* `deTurckSmoothN` — the **smooth-input** nonlinearity.  For a *smooth* compactly-supported
  `(0,2)`-tensor `T : SmoothCcTensor g₀ 0 2` whose symmetrization is `g₀`-fibre small
  (`gFibreOpBound g₀ (ccTensorBilinSymm g₀ T) δ`, `δ < 1`, so `g₀ + T` is a genuine
  `SmoothRiemannianMetric` via `tensorSectionRealizeMetric`), `deTurckSmoothN T` reads off
  the order-`a` spectral coordinates of the **genuine intrinsic remainder**

    `deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`

  as the smooth `(0,2)`-tensor `deTurckRHSSection g_bg (g₀ + T) − rawTensorConnLapSmooth g₀ 0 2 T`.
  Its `tensorHs g₀ 0 2 a` membership is the spectral-scale summability of a smooth
  compactly-supported tensor (`smoothCcTensor_tensorL2Coeff_weighted_summable`).  This uses
  the **sorry-free intrinsic objects directly** — no chart-rough-evaluation and no
  finite-support gating.

* `smoothCcToTensorHs` — the canonical embedding of smooth tensors into the spectral scale
  `tensorHs g₀ 0 2 σ` (the same `L²`-coordinate read-off), with dense range
  (`smoothCcToTensorHs_denseRange`).

* `deTurckSobolevNHa2` — the **total** continuous quasilinear nonlinearity
  `tensorHs g₀ 0 2 (a+2) → tensorHs g₀ 0 2 a`, the dense/uniformly-continuous extension of
  `deTurckSmoothN` (codomain `tensorHs g₀ 0 2 a` is complete), recentred onto the engine
  ball by `recenteredBallRetraction`.  It agrees with `deTurckSmoothN` on smooth fibre-small
  in-ball inputs (`deTurckSobolevNHa2_eq_smoothN`), so the genuine Ricci–DeTurck remainder is
  what the flow sees; it carries no `realizableAt` / finite-support / HLCC gate.

## The analytic core and the extension input

The deep classical input is the **smooth-ball Lipschitz estimate** at the quasilinear
`H^{a+2}` order, `smoothRemainderDiff_ballLipschitz_Ha2`
(`‖N(T) − N(T')‖_{H^a} ≤ K · ‖ι(a+2) T − ι(a+2) T'‖` for smooth fibre-small `T, T'` in the
`H^{a+2}`-ball), proven by majorising the chart-polynomial remainder **difference**
`chartDeTurckRicciRHS_sub_eq` term by term with the Moser / Gagliardo–Nirenberg tame-product
backbone.  It needs the **supercritical** Sobolev-algebra order `2 * (a + 1) > finrank E + 4`
(hypothesis `ha_super`); the order is `H^{a+2}` because the Ricci–DeTurck flow is
**quasilinear** (the difference carries second-order `∂²(T − T')` jet factors).

The rephrased `deTurckSmoothN_ballLipschitz_Ha2`, `smoothCcToTensorHs_denseRange`,
`deTurckSobolevNHa2_eq_smoothN`, and `deTurckSobolevNHa2_lipschitzWith` package the Lipschitz
dense extension to the complete codomain, consumed by the quasilinear maximal-regularity engine
in `DeTurckQuasilinearExistence.lean`.
-/

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace NNReal

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The smooth-input Ricci–DeTurck nonlinearity.**

For a smooth fibre-small `T : SmoothCcTensor g₀ 0 2`, `deTurckSmoothN g₀ g_bg a hδ_lt hδ`
is the order-`a` spectral element whose eigenbasis coordinates are the `L²` coordinates of
the genuine remainder `deTurckSmoothRemainder g₀ g_bg T`
(`= deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`).  Its `H^a` membership is the spectral-scale
summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at every real order).  This is the
**continuous, non-gated** Ricci–DeTurck remainder on the smooth representatives. -/
def deTurckSmoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
      (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g₀
      (a : ℝ) (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)

/-- The eigenbasis coordinate of `deTurckSmoothN` is the `L²` coordinate of the genuine
smooth remainder. -/
@[simp] theorem deTurckSmoothN_coeff (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g₀ 0 2) :
    (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
        (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i :=
  rfl

/-- **Density of the smooth-tensor embedding in the spectral Sobolev scale.**

The textbook fact that smooth compactly-supported tensors are dense in `H^σ`, here for the
intrinsic spectral scale `tensorHs g₀ 0 2 σ`: the spectral coordinates of smooth data exhaust
the weighted-`ℓ²` space (finite-support spectral elements are dense
— `tensorHsFiniteSupportSubmodule_dense` — and each is the embedding of a smooth tensor).

Each finitely-supported spectral element `x` is the embedding `smoothCcToTensorHs g₀ σ` of the
smooth finite eigen-combination `finiteEigenCombo g₀ (support x.coeff) x.coeff`: their spectral
coordinates coincide (`finiteEigenComboHs_coeff_eq`, `finiteEigenCombo_tensorL2Coeff`), so the
range of `smoothCcToTensorHs` contains the dense finite-support submodule and is therefore
dense. -/
theorem smoothCcToTensorHs_denseRange (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) :
    DenseRange (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
  classical
  have hsub :
      (tensorHs.finiteSupportSubmodule (I := I) (M := M) (g := g₀) (r := 0) (s := 2) σ :
          Set (tensorHs (I := I) (M := M) g₀ 0 2 σ)) ⊆
        Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ σ) := by
    intro x hx
    have hxfin : (Function.support x.coeff).Finite :=
      (tensorHs.mem_finiteSupportSubmodule (I := I) (M := M) x).1 hx
    refine ⟨finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff, ?_⟩
    refine tensorHs.ext ?_
    funext i
    rw [smoothCcToTensorHs_coeff]
    have hcoeff :
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2
              (finiteEigenCombo (I := I) (M := M) g₀ hxfin.toFinset x.coeff)) i =
          (if i ∈ hxfin.toFinset then x.coeff i else 0) := by
      rw [SmoothCcTensor.toL2_apply,
        finiteEigenCombo_tensorL2Coeff (I := I) (M := M) g₀ hxfin.toFinset x.coeff i]
    rw [hcoeff]
    by_cases hi : i ∈ hxfin.toFinset
    · rw [if_pos hi]
    · rw [if_neg hi]
      rw [Set.Finite.mem_toFinset] at hi
      exact (Function.notMem_support.mp hi).symm
  exact (tensorHsFiniteSupportSubmodule_dense (I := I) (M := M)).mono hsub

/-- The smooth-tensor embedding `smoothCcToTensorHs` is additive in its tensor argument:
its spectral coordinates are the `L²` coordinates of the tensor, and both `tensorL2Coeff`
and `SmoothCcTensor.toL2` are additive. -/
theorem smoothCcToTensorHs_add (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S + T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S +
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.add_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (S + T) =
        SmoothCcTensor.toL2 S + SmoothCcTensor.toL2 T from map_add _ _ _,
    tensorL2Coeff_add]

/-- The smooth-tensor embedding `smoothCcToTensorHs` is negation-compatible in its tensor
argument. -/
theorem smoothCcToTensorHs_neg (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (-S) =
      -smoothCcToTensorHs (I := I) (M := M) g₀ σ S := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.neg_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (-S) = -SmoothCcTensor.toL2 S from map_neg _ _]
  rw [show (-SmoothCcTensor.toL2 S : TensorL2 0 2 g₀) = (-1 : ℝ) • SmoothCcTensor.toL2 S by
    rw [neg_one_smul]]
  rw [tensorL2Coeff_smul]
  ring

/-- The smooth-tensor embedding `smoothCcToTensorHs` is subtraction-compatible in its tensor
argument: `ι(S − T) = ι S − ι T`. -/
theorem smoothCcToTensorHs_sub (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (S T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (S - T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ σ S -
        smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  rw [sub_eq_add_neg, sub_eq_add_neg, smoothCcToTensorHs_add, smoothCcToTensorHs_neg]

/-- **The smooth nonlinearity difference is the spectral embedding of the genuine remainder
difference.**

For smooth fibre-small `T, T'`, `deTurckSmoothN T − deTurckSmoothN T'` (in `H^a`) is exactly
the order-`a` spectral embedding `smoothCcToTensorHs g₀ a` of the difference of the two genuine
smooth remainders `deTurckSmoothRemainder T − deTurckSmoothRemainder T'`.  Both sides have, at
each eigenbasis index `i`, the `L²` coordinate of the corresponding remainder (read off by the
same compact-resolvent witness), so the identity is the additivity of `tensorL2Coeff` and
`SmoothCcTensor.toL2` over the remainder difference. -/
theorem deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
        deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' =
      smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
        (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') := by
  refine tensorHs.ext ?_
  funext i
  have hsub :
      (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i =
        (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ).coeff i -
          (deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ').coeff i := by
    rw [sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff]
    rfl
  have hcoeff_sub :
      tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
          (SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i =
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ)) i -
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')) i := by
    rw [show SmoothCcTensor.toL2
            (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') =
          SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ) -
            SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ')
        from map_sub _ _ _]
    rw [sub_eq_add_neg, tensorL2Coeff_add]
    rw [show (-SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') :
          TensorL2 0 2 g₀) =
        (-1 : ℝ) • SmoothCcTensor.toL2 (deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ') by
      rw [neg_one_smul]]
    rw [tensorL2Coeff_smul]
    ring
  rw [hsub, deTurckSmoothN_coeff, deTurckSmoothN_coeff, smoothCcToTensorHs_coeff, hcoeff_sub]

/-- **The innermost-peel recursion for the one-minus-connection-Laplacian iterate.**
`(1 − Δ_∇)^{k+1} S = (1 − Δ_∇)^k ((1 − Δ_∇) S)`: peeling one factor off the inside agrees with
peeling it off the outside.  Proved by induction on `k`. -/
private theorem oneMinusConnLapSmoothIter_succ'
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    oneMinusConnLapSmoothIter (I := I) g₀ 0 2 (k + 1) S =
      oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [oneMinusConnLapSmoothIter_succ, ih, ← oneMinusConnLapSmoothIter_succ]

/-- **The single-step `toHs` order-drop for the one-minus-connection-Laplacian** at any fixed
output order `m`.  Since `(1 − Δ_∇) U = U − Δ_∇ U`, the triangle inequality on
`SmoothCcTensor.toHs_sub`, the order monotonicity `toHs_norm_mono` (`‖U‖_{H^m} ≤ ‖U‖_{H^{m+1}}`)
and the single-step rough-Laplacian order-drop `exists_rawConnLapSmooth_toHs_le_toHs_succ` give a
constant `C = 1 + C₁` with `‖(1 − Δ_∇) U‖_{H^m} ≤ C · ‖U‖_{H^{m+1}}`. -/
private theorem exists_oneMinusConnLapSmooth_toHs_le_toHs_succ
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (oneMinusConnLapSmooth (I := I) g₀ 0 2 U)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by
  obtain ⟨C₁, hC₁_nn, hC₁⟩ := exists_rawConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ m
  refine ⟨1 + C₁, by positivity, fun U => ?_⟩
  have hsub : oneMinusConnLapSmooth (I := I) g₀ 0 2 U =
      U - rawTensorConnLapSmooth (I := I) g₀ 0 2 U := rfl
  rw [hsub, SmoothCcTensor.toHs_sub]
  have hmono : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) m U‖ ≤
      ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (m + 1) U‖ :=
    toHs_norm_mono (I := I) g₀ (Nat.le_succ m) U
  have hlap := hC₁ U
  calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) m U -
          DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖
      ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m U‖ +
          ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) m (rawTensorConnLapSmooth (I := I) g₀ 0 2 U)‖ :=
        norm_sub_le _ _
    _ ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ +
          C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := add_le_add hmono hlap
    _ = (1 + C₁) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (m + 1) U‖ := by ring

/-- **The order-dropping `toHs` bound for the genuine smooth one-minus-connection-Laplacian
iterate** (output order fixed at `0`).  For every `k` there is a nonnegative constant `C` with
`‖(1 − Δ_∇)^k S‖_{H^0} ≤ C · ‖S‖_{H^k}` for every smooth `(0,2)`-tensor `S`.  Induction on `k`
peeling the **innermost** factor (`oneMinusConnLapSmoothIter_succ'`): the inductive hypothesis at
output order `0` applied to `(1 − Δ_∇) S` gives `‖(1 − Δ_∇)^k ((1 − Δ_∇) S)‖_{H^0} ≤ Ck · ‖(1 −
Δ_∇) S‖_{H^k}`, and the single-step drop at the **fixed** output order `k`
(`exists_oneMinusConnLapSmooth_toHs_le_toHs_succ`) bounds `‖(1 − Δ_∇) S‖_{H^k} ≤ Cstep · ‖S‖_{H^{k+1}}`
— so the constant `Ck · Cstep` is order-independent. -/
private theorem exists_oneMinusConnLapSmoothIter_toHs_le_toHs
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ ≤
          C * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) k S‖ := by
  induction k with
  | zero =>
      refine ⟨1, zero_le_one, fun S => ?_⟩
      simp only [oneMinusConnLapSmoothIter_zero, one_mul, le_refl]
  | succ k ih =>
      obtain ⟨Ck, hCk_nn, hCk⟩ := ih
      obtain ⟨Cstep, hCstep_nn, hCstep⟩ :=
        exists_oneMinusConnLapSmooth_toHs_le_toHs_succ (I := I) g₀ k
      refine ⟨Ck * Cstep, mul_nonneg hCk_nn hCstep_nn, fun S => ?_⟩
      rw [oneMinusConnLapSmoothIter_succ']
      calc ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) 0
              (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k
                (oneMinusConnLapSmooth (I := I) g₀ 0 2 S))‖
          ≤ Ck * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) k (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)‖ :=
            hCk (oneMinusConnLapSmooth (I := I) g₀ 0 2 S)
        _ ≤ Ck * (Cstep * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖) :=
            mul_le_mul_of_nonneg_left (hCstep S) hCk_nn
        _ = (Ck * Cstep) * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
              (g := g₀) (r := 0) (s := 2) (k + 1) S‖ := by ring

/-- **The spectral-to-covariant-gradient bound (the missing N2 direction at even order).**
For every `k` there is a nonnegative constant `C` such that the even-order spectral norm
`‖smoothCcToTensorHs g₀ (2k) S‖` of a smooth `(0,2)`-tensor `S` is bounded by `C` times the
covariant-`L²` jet sum `∑_{j ≤ 2k} ‖∇^j S‖`:

  `‖smoothCcToTensorHs g₀ (2k) S‖ ≤ C · ∑_{j ≤ 2k} ‖iteratedCovGrad g₀ 0 2 j S‖`.

This is the (otherwise absent) general-order interior-elliptic comparison from the spectral
`H^{2k}` scale to the covariant-gradient `L²` data.  It assembles: the even-order
spectral-norm/Laplacian identity `ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2`
(`‖ccSpectralEmbed g (2k) S‖² = ‖(1 − Δ_∇)^k S‖²_{L²}`), the order-dropping `toHs` bound for the
one-minus-connection-Laplacian iterate `exists_oneMinusConnLapSmoothIter_toHs_le_toHs`
(`‖(1 − Δ_∇)^k S‖_{H^0} ≤ C · ‖S‖_{H^k}`, via `exists_l2Norm_le_toHs_zero` to bridge the `L²` and
`H^0` norms), and the reverse Hebey–Sobolev bridge `exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum`
(`‖S‖_{H^k} ≤ C · ∑_{j ≤ 2k} ‖∇^j S‖`).  The `ccSpectralEmbed = smoothCcToTensorHs` definitional
equality identifies the spectral embeddings. -/
theorem exists_smoothCcToTensorHs_even_le_iteratedCovGrad_sum
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (2 * k + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  obtain ⟨Cl2, hCl2_nn, hCl2⟩ := exists_l2Norm_le_toHs_zero (I := I) g₀
  obtain ⟨Cdrop, hCdrop_nn, hCdrop⟩ := exists_oneMinusConnLapSmoothIter_toHs_le_toHs (I := I) g₀ k
  obtain ⟨Chebey, hChebey_nn, hChebey⟩ :=
    exists_toHs_norm_le_iteratedCovGrad_tensorL2Norm_sum (I := I) (M := M) g₀ 0 2 k
  refine ⟨Cl2 * Cdrop * Chebey, by positivity, fun S => ?_⟩

  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hsq := ccSpectralEmbed_even_norm_sq_eq_oneMinusConnLap_l2 (I := I) (M := M) g₀ k S
  have hnorm_eq : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
      ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
    have h1 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ := by rw [hembed_eq]
    have h2 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ =
        ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := by
      have hnn1 : (0 : ℝ) ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ :=
        norm_nonneg _
      have hnn2 : (0 : ℝ) ≤
          ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := norm_nonneg _
      nlinarith [hsq, hnn1, hnn2]
    rw [h1, h2]
  rw [hnorm_eq]

  have hjet_eq : ∀ j : ℕ,
      tensorL2Norm (I := I) (M := M) g₀ 0 (2 + j) (iteratedCovGrad (I := I) g₀ 0 2 j S).toFun =
        ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := fun j =>
    (SmoothCcTensor.norm_def (iteratedCovGrad (I := I) g₀ 0 2 j S)).symm
  have hl2 := hCl2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)
  have hdrop := hCdrop S
  have hhebey := hChebey S
  have hsum_nn : 0 ≤ ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ :=
    Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have htoHsk_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) k S‖ := norm_nonneg _
  have htoHs0_nn : 0 ≤ ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
      (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ :=
    norm_nonneg _
  have hhebey' : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) k S‖ ≤
      Chebey * ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
    refine le_trans hhebey ?_
    refine mul_le_mul_of_nonneg_left ?_ hChebey_nn
    exact le_of_eq (Finset.sum_congr rfl (fun j _ => hjet_eq j))
  calc ‖SmoothCcTensor.toL2 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖
      ≤ Cl2 * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) 0 (oneMinusConnLapSmoothIter (I := I) g₀ 0 2 k S)‖ := hl2
    _ ≤ Cl2 * (Cdrop * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) k S‖) := mul_le_mul_of_nonneg_left hdrop hCl2_nn
    _ ≤ Cl2 * (Cdrop * (Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ hCl2_nn
        exact mul_le_mul_of_nonneg_left hhebey' hCdrop_nn
    _ = Cl2 * Cdrop * Chebey * ∑ j ∈ Finset.range (2 * k + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by ring

private theorem tensorL2Inner_eq_tsum_tensorL2Coeff_cross
    (g₀ : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g₀ 0 2) :
    tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      ∑' i : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 A) i *
          tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
            (SmoothCcTensor.toL2 B) i := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set b := tensorResolventHilbertEigenbasisSigma (I := I) (M := M) h_compact with hb_def
  have hinner_eq : tensorL2Inner (I := I) (M := M) g₀ 0 2 A.toFun B.toFun =
      (⟪SmoothCcTensor.toL2 A, SmoothCcTensor.toL2 B⟫_ℝ : ℝ) := by
    rw [DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2
      (I := I) (M := M) A B]
    exact (SmoothCcTensor.inner_def (I := I) (M := M) A B).symm
  rw [hinner_eq]
  have h_par := b.tsum_inner_mul_inner (SmoothCcTensor.toL2 A) (SmoothCcTensor.toL2 B)
  rw [← h_par]
  refine tsum_congr (fun i => ?_)
  rw [tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 A) i,
    tensorL2Coeff_eq_inner (I := I) (M := M) h_compact (SmoothCcTensor.toL2 B) i]
  rw [show (⟪SmoothCcTensor.toL2 A, b i⟫_ℝ : ℝ) = ⟪b i, SmoothCcTensor.toL2 A⟫_ℝ from
    real_inner_comm _ _]

private theorem covGrad_rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set U : SmoothCcTensor g₀ 0 2 := rawTensorConnLapIter (I := I) g₀ 0 2 i S with hU_def
  have hnorm_sq : ‖covGrad (I := I) (M := M) g₀ 0 2 U‖ ^ 2 =
      tensorL2Inner (I := I) (M := M) g₀ 0 3
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun
        (covGrad (I := I) (M := M) g₀ 0 2 U).toFun := by
    rw [SmoothCcTensor.norm_def (covGrad (I := I) (M := M) g₀ 0 2 U)]
    exact tensorL2Norm_sq_toFun (I := I) (M := M) g₀ 0 3 (covGrad (I := I) (M := M) g₀ 0 2 U)
  rw [hnorm_sq,
    tensorL2Inner_covGrad_self_eq_neg_rawConnLap_inner_gen (I := I) (M := M) g₀ 2 U]
  have hraw_eq : rawTensorConnLapSmooth (I := I) g₀ 0 2 U =
      rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S := by
    rw [hU_def, rawTensorConnLapIter_succ]
  rw [hraw_eq, tensorL2Inner_eq_tsum_tensorL2Coeff_cross (I := I) (M := M) g₀
    (rawTensorConnLapIter (I := I) g₀ 0 2 (i + 1) S) U, hU_def]
  rw [← tsum_neg]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m (i + 1),
    tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m i]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  have hpow : ((-L) ^ (i + 1) * c) * ((-L) ^ i * c) = (-L) ^ (2 * i + 1) * c ^ 2 := by
    rw [show (2 * i + 1) = (i + 1) + i by ring, pow_add]
    ring
  rw [hpow]
  rw [(odd_two_mul_add_one i).neg_pow L]
  ring

private theorem covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd
    (g₀ : SmoothRiemannianMetric I M) (i : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  have hnn : 0 ≤ ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ :=
    norm_nonneg _
  have hsq :
      ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ^ 2 ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S‖ ^ 2 := by
    rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ i S,
      ccSpectralEmbed_norm_sq_eq_tsum]
    refine Summable.tsum_le_tsum ?_ ?_ ?_
    · intro m
      set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweight_eq]
      have hpow_le : (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) ≤
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) :=
        pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)
      exact mul_le_mul_of_nonneg_right hpow_le (sq_nonneg c)
    · have hsummable := (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
      refine Summable.of_nonneg_of_le ?_ ?_ hsummable
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        positivity
      · intro m
        have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
          tensor_lambda_nonneg (I := I) (M := M) m
        have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
            1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
        have hweight_eq : tensorSobolevWeight (I := I) (M := M) m ((2 * i + 1 : ℕ) : ℝ) =
            (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * i + 1) := by
          unfold tensorSobolevWeight
          rw [Real.rpow_natCast]
        rw [hweight_eq]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hbase_nn hbase_le (2 * i + 1)) (sq_nonneg _)
    · exact (ccSpectralEmbed (I := I) (M := M) g₀ ((2 * i + 1 : ℕ) : ℝ) S).weighted_summable
  exact le_of_sq_le_sq hsq hnn

private theorem norm_iteratedCovGrad_comp_local
    (g₀ : SmoothRiemannianMetric I M) (s j i : ℕ) (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := by
  have hsq :
      ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)‖ ^ 2 =
        ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ ^ 2 := by
    rw [← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 (s + j) i (iteratedCovGrad (I := I) g₀ 0 s j S)),
      ← DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (iteratedCovGrad (I := I) g₀ 0 s (j + i) S),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        ((s + j) + i) (iteratedCovGrad (I := I) g₀ 0 (s + j) i
          (iteratedCovGrad (I := I) g₀ 0 s j S)),
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀
        (s + (j + i)) (iteratedCovGrad (I := I) g₀ 0 s (j + i) S)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 s j i S x
  have h1 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 (s + j) i
      (iteratedCovGrad (I := I) g₀ 0 s j S)‖ := norm_nonneg _
  have h2 : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 s (j + i) S‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

private theorem norm_iteratedCovGrad_order_eq
    (g₀ : SmoothRiemannianMetric I M) (s : ℕ) {n n' : ℕ} (h : n = n')
    (S : SmoothCcTensor g₀ 0 s) :
    ‖iteratedCovGrad (I := I) g₀ 0 s n S‖ = ‖iteratedCovGrad (I := I) g₀ 0 s n' S‖ := by
  subst h
  rfl

private theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd
    (g₀ : SmoothRiemannianMetric I M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (2 * k + 1 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖ := by
  classical
  obtain ⟨Clow, hClow_nn, hClow⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
  obtain ⟨Cgard, hCgard_nn, hCgard⟩ :=
    exists_iteratedCovGrad_l2Norm_le_sum_rawConnLapIter (I := I) (M := M) g₀ 3 k
  obtain ⟨Ceven, hCeven_nn, hCeven⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
  have hcommfam : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          C * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => exists_rawConnLapIter_covGrad_commutator_l2Norm_le (I := I) (M := M) g₀ 2 i
  set Ccomm : ℕ → ℝ := fun i => Classical.choose (hcommfam i) with hCcomm_def
  have hCcomm_nn : ∀ i, 0 ≤ Ccomm i := fun i => (Classical.choose_spec (hcommfam i)).1
  have hCcomm : ∀ i, ∀ S : SmoothCcTensor g₀ 0 2,
      ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
        Ccomm i * ∑ a ∈ Finset.range (2 * i), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
    fun i => (Classical.choose_spec (hcommfam i)).2
  set Ccommsum : ℝ := ∑ i ∈ Finset.range (k + 1), Ccomm i with hCcommsum_def
  have hCcommsum_nn : 0 ≤ Ccommsum :=
    Finset.sum_nonneg (fun i _ => hCcomm_nn i)
  refine ⟨Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven), by positivity,
    fun S => ?_⟩
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S‖
    with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k + 1 : ℕ) : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  have hccmono : ∀ (σ : ℕ), σ ≤ 2 * k + 1 →
      ‖ccSpectralEmbed (I := I) (M := M) g₀ ((σ : ℕ) : ℝ) S‖ ≤ Nspec := by
    intro σ hσ
    rw [hNspec_def, ← hembed_eq]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ S
    have : (σ : ℕ) ≤ (2 * k + 1 : ℕ) := hσ
    exact_mod_cast this

  have hlow_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S‖ ≤ Nspec := by
    have hembed2k : smoothCcToTensorHs (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S =
        ccSpectralEmbed (I := I) (M := M) g₀ ((2 * k : ℕ) : ℝ) S :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed2k]
    exact hccmono (2 * k) (by omega)

  have hlowsum : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Clow * Nspec := by
    refine le_trans (hClow S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hClow_nn

  have heven_le : ∑ j ∈ Finset.range (2 * k + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Ceven * Nspec := by
    refine le_trans (hCeven S) ?_
    exact mul_le_mul_of_nonneg_left hlow_le hCeven_nn

  have hccoeff_le : ∀ i ∈ Finset.range (k + 1),
      ‖rawTensorConnLapIter (I := I) g₀ 0 3 i
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (1 + Ccomm i * Ceven) * Nspec := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hsplit :
        rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S) =
          covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S) +
            (rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)) := by
      abel
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have hmain : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤ Nspec := by
      refine le_trans
        (covGrad_rawConnLapIter_l2_le_ccSpectralEmbed_odd (I := I) (M := M) g₀ i S) ?_
      exact hccmono (2 * i + 1) (by omega)
    have hcomm := hCcomm i S
    have hsub_le : 2 * i ≤ 2 * k + 1 := by omega
    have hsubrange : ∑ a ∈ Finset.range (2 * i),
          ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤
        ∑ a ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun a => ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖)
        (Finset.range_mono hsub_le) (fun a _ _ => norm_nonneg _)
    have hcommterm :
        ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ ≤
          Ccomm i * Ceven * Nspec := by
      calc ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i
              (covGrad (I := I) (M := M) g₀ 0 2 S) -
              covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
          ≤ Ccomm i * ∑ a ∈ Finset.range (2 * i),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := hcomm
        _ ≤ Ccomm i * ∑ a ∈ Finset.range (2 * k + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
            mul_le_mul_of_nonneg_left hsubrange (hCcomm_nn i)
        _ ≤ Ccomm i * (Ceven * Nspec) :=
            mul_le_mul_of_nonneg_left heven_le (hCcomm_nn i)
        _ = Ccomm i * Ceven * Nspec := by ring
    calc ‖covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖ +
          ‖rawTensorConnLapIter (I := I) g₀ 0 (2 + 1) i (covGrad (I := I) (M := M) g₀ 0 2 S) -
            covGrad (I := I) (M := M) g₀ 0 2 (rawTensorConnLapIter (I := I) g₀ 0 2 i S)‖
        ≤ Nspec + Ccomm i * Ceven * Nspec :=
          add_le_add hmain hcommterm
      _ = (1 + Ccomm i * Ceven) * Nspec := by ring

  have htop_le : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ ≤
      Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
    have hbridge : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
        ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have h := norm_iteratedCovGrad_comp_local (I := I) (M := M) g₀ 2 1 (2 * k) S
      have hcov : covGrad (I := I) (M := M) g₀ 0 2 S =
          iteratedCovGrad (I := I) g₀ 0 2 1 S := rfl
      have horder : ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖ =
          ‖iteratedCovGrad (I := I) g₀ 0 2 (1 + 2 * k) S‖ :=
        norm_iteratedCovGrad_order_eq (I := I) (M := M) g₀ 2 (by omega) S
      rw [horder, ← h, hcov]
    rw [hbridge]
    have hgard := hCgard (2 * k) (le_refl _) (covGrad (I := I) (M := M) g₀ 0 2 S)
    have hgard' : ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
          (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        Cgard * ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := by
      have heq1 : tensorL2Norm (I := I) (M := M) g₀ 0 (3 + 2 * k)
            (iteratedCovGrad (I := I) g₀ 0 3 (2 * k)
              (covGrad (I := I) (M := M) g₀ 0 2 S)).toFun =
          ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖ :=
        DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm (I := I) (M := M) g₀
          (iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S))
      rw [← heq1]
      refine le_trans hgard ?_
      refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hCgard_nn
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact DifferentialGeometry.Analysis.Sobolev.Tensor.tensorL2Norm_toFun_eq_norm
        (I := I) (M := M) g₀
        (rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S))
    have hsumcoeff : ∑ i ∈ Finset.range (k + 1),
          ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ ≤
        (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
      calc ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖
          ≤ ∑ i ∈ Finset.range (k + 1), (1 + Ccomm i * Ceven) * Nspec :=
            Finset.sum_le_sum hccoeff_le
        _ = ∑ i ∈ Finset.range (k + 1), (Nspec + (Ccomm i) * (Ceven * Nspec)) :=
            Finset.sum_congr rfl (fun i _ => by ring)
        _ = (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              ← Finset.sum_mul]
            rw [hCcommsum_def]
            ring
    calc ‖iteratedCovGrad (I := I) g₀ 0 3 (2 * k) (covGrad (I := I) (M := M) g₀ 0 2 S)‖
        ≤ Cgard * ∑ i ∈ Finset.range (k + 1),
            ‖rawTensorConnLapIter (I := I) g₀ 0 3 i (covGrad (I := I) (M := M) g₀ 0 2 S)‖ := hgard'
      _ ≤ Cgard * ((((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec) :=
          mul_le_mul_of_nonneg_left hsumcoeff hCgard_nn
      _ = Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec := by ring

  rw [Finset.sum_range_succ (fun j => ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖) (2 * k + 1)]
  calc ∑ j ∈ Finset.range (2 * k + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ +
        ‖iteratedCovGrad (I := I) g₀ 0 2 (2 * k + 1) S‖
      ≤ Clow * Nspec + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven) * Nspec :=
        add_le_add hlowsum htop_le
    _ = (Clow + Cgard * (((k + 1 : ℕ) : ℝ) + Ccommsum * Ceven)) * Nspec := by ring

theorem exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
          C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ := by
  classical
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs (I := I) (M := M) g₀ (2 * k)
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn2k : n = 2 * k := by omega
    subst hn2k
    exact hC S
  · obtain ⟨C, hC_nn, hC⟩ :=
      exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_odd (I := I) (M := M) g₀ k
    refine ⟨C, hC_nn, fun S => ?_⟩
    have hn : n = 2 * k + 1 := by omega
    subst hn
    exact hC S

private theorem rawConnLapIter_l2NormSq_eq_tsum
    (g₀ : SmoothRiemannianMetric I M) (t : ℕ) (S : SmoothCcTensor g₀ 0 2) :
    ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ (2 * t) *
          (tensorL2Coeff (I := I) (M := M)
              (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
              (SmoothCcTensor.toL2 S) m) ^ 2 := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  rw [← tensorParseval_l2Coeff_ofCompact_sq (I := I) (M := M) h_compact
    (SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S))]
  refine tsum_congr (fun m => ?_)
  rw [tensorL2Coeff_ofCompact_rawTensorConnLapIter (I := I) (M := M) g₀ h_compact S m t]
  set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
  set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
  rw [mul_pow, ← pow_mul, mul_comm t 2, (even_two_mul t).neg_pow L]

private theorem exists_spectralModeTsum_le_iteratedCovGrad_sum_sq
    (g₀ : SmoothRiemannianMetric I M) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 ≤
          C * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
  classical
  rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ t 2
    refine ⟨(Cfun 0) ^ 2, by positivity, fun S => ?_⟩
    have hj2t : j = 2 * t := by omega
    have htsum : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
        ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 := by
      rw [rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ t S, hj2t]
    rw [htsum]
    have hnorm_le : ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ≤
        Cfun 0 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := by
      have h := hCfun 0 S
      rw [iteratedCovGrad_zero (I := I) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 t S)] at h
      rw [SmoothCcTensor.norm_toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)]
      have hrange : 2 * t + 0 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hnn : 0 ≤ ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ :=
      norm_nonneg _
    calc ‖SmoothCcTensor.toL2 (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2
        ≤ (Cfun 0 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 0) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 0) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by ring
  · obtain ⟨Cfun, hCfun_nn, hCfun⟩ :=
      exists_iteratedCovGrad_rawConnLapIter_l2Norm_le (I := I) (M := M) g₀ t 2
    refine ⟨(Cfun 1) ^ 2, by positivity, fun S => ?_⟩
    have hj2t : j = 2 * t + 1 := by omega
    have htsum : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M)
                (tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2)
                (SmoothCcTensor.toL2 S) m) ^ 2 =
        ‖covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2 := by
      rw [covGrad_rawConnLapIter_l2NormSq_eq_tsum (I := I) (M := M) g₀ t S, hj2t]
    rw [htsum]
    have hnorm_le : ‖covGrad (I := I) (M := M) g₀ 0 2
          (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ≤
        Cfun 1 * ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ := by
      have h := hCfun 1 S
      have hcov : iteratedCovGrad (I := I) g₀ 0 2 1
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S) =
          covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S) := rfl
      rw [hcov] at h
      have hrange : 2 * t + 1 + 1 = j + 1 := by omega
      rw [hrange] at h
      exact h
    have hsum_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
      Finset.sum_nonneg (fun a _ => norm_nonneg _)
    have hnn : 0 ≤ ‖covGrad (I := I) (M := M) g₀ 0 2
        (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ := norm_nonneg _
    calc ‖covGrad (I := I) (M := M) g₀ 0 2
            (rawTensorConnLapIter (I := I) g₀ 0 2 t S)‖ ^ 2
        ≤ (Cfun 1 * ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by
          apply sq_le_sq'
          · linarith [mul_nonneg (hCfun_nn 1) hsum_nn]
          · exact hnorm_le
      _ = (Cfun 1) ^ 2 * (∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 := by ring

theorem exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general
    (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ ≤
          C * ∑ j ∈ Finset.range (n + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by
  classical
  set h_compact := tensorResolventL2_isCompactOperator (I := I) (M := M) g₀ 0 2
    with hcompact_def
  set Cmode : ℕ → ℝ := fun j =>
    (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose
    with hCmode_def
  have hCmode_nn : ∀ j, 0 ≤ Cmode j := fun j =>
    (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose_spec.1
  have hCmode : ∀ j, ∀ S : SmoothCcTensor g₀ 0 2,
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 ≤
        Cmode j * (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 :=
    fun j => (exists_spectralModeTsum_le_iteratedCovGrad_sum_sq (I := I) (M := M) g₀ j).choose_spec.2
  set Csum : ℝ := ∑ j ∈ Finset.range (n + 1), Cmode j with hCsum_def
  have hCsum_nn : 0 ≤ Csum := Finset.sum_nonneg (fun j _ => hCmode_nn j)
  refine ⟨Real.sqrt ((2 : ℝ) ^ n * Csum), Real.sqrt_nonneg _, fun S => ?_⟩
  set Sall : ℝ := ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
    with hSall_def
  have hSall_nn : 0 ≤ Sall := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hembed_eq : smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S =
      ccSpectralEmbed (I := I) (M := M) g₀ (n : ℝ) S :=
    tensorHs.ext (funext (fun i => rfl))
  set Nspec : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) S‖ with hNspec_def
  have hNspec_nn : 0 ≤ Nspec := norm_nonneg _
  have hweight_eq : ∀ m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
        (I := I) (M := M) g₀ 0 2,
      tensorSobolevWeight (I := I) (M := M) m (n : ℝ) =
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n := by
    intro m
    unfold tensorSobolevWeight
    rw [Real.rpow_natCast]
  have hsq_tsum : Nspec ^ 2 =
      ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2,
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
    rw [hNspec_def, hembed_eq, ccSpectralEmbed_norm_sq_eq_tsum]
    exact tsum_congr (fun m => by rw [hweight_eq m])
  have hmode_summable : ∀ j : ℕ, Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    intro j
    have hfull := (ccSpectralEmbed (I := I) (M := M) g₀ (j : ℝ) S).weighted_summable
    refine Summable.of_nonneg_of_le ?_ ?_ hfull
    · intro m
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      positivity
    · intro m
      have hbase_nn : (0 : ℝ) ≤ TensorEigenIdx.lambda (I := I) (M := M) m :=
        tensor_lambda_nonneg (I := I) (M := M) m
      have hbase_le : TensorEigenIdx.lambda (I := I) (M := M) m ≤
          1 + TensorEigenIdx.lambda (I := I) (M := M) m := by linarith
      have hweightj : tensorSobolevWeight (I := I) (M := M) m (j : ℝ) =
          (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ j := by
        unfold tensorSobolevWeight
        rw [Real.rpow_natCast]
      rw [hweightj, ccSpectralEmbed_coeff]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hbase_nn hbase_le j) (sq_nonneg _)
  have hbinom_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
            (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    apply Summable.mul_left
    exact summable_sum (fun j _ => hmode_summable j)
  have hlhs_summable : Summable
      (fun m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
          (I := I) (M := M) g₀ 0 2 =>
        (1 + TensorEigenIdx.lambda (I := I) (M := M) m) ^ n *
          (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2) := by
    have hfull := (ccSpectralEmbed (I := I) (M := M) g₀ (n : ℝ) S).weighted_summable
    refine (summable_congr (fun m => ?_)).mp hfull
    rw [hweight_eq m, ccSpectralEmbed_coeff]
  have hsq_le : Nspec ^ 2 ≤ (2 : ℝ) ^ n * Csum * Sall ^ 2 := by
    have hstep1 : Nspec ^ 2 ≤
        ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
      rw [hsq_tsum]
      refine Summable.tsum_le_tsum (fun m => ?_) hlhs_summable hbinom_summable
      · set c := tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m with hc_def
        set L := TensorEigenIdx.lambda (I := I) (M := M) m with hL_def
        have hL_nn : 0 ≤ L := tensor_lambda_nonneg (I := I) (M := M) m
        have hbinom : (1 + L) ^ n ≤ (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j := by
          rw [add_comm, add_pow, Finset.mul_sum]
          refine Finset.sum_le_sum (fun p hp => ?_)
          rw [one_pow, mul_one]
          have hch : ((n.choose p : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
            have hbnd := Nat.choose_le_two_pow n p
            calc ((n.choose p : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast hbnd
              _ = (2 : ℝ) ^ n := by push_cast; ring
          calc L ^ p * (n.choose p) ≤ L ^ p * (2 : ℝ) ^ n :=
                mul_le_mul_of_nonneg_left hch (pow_nonneg hL_nn p)
            _ = (2 : ℝ) ^ n * L ^ p := by ring
        have hc2_nn : 0 ≤ c ^ 2 := sq_nonneg c
        calc (1 + L) ^ n * c ^ 2
            ≤ ((2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j) * c ^ 2 :=
              mul_le_mul_of_nonneg_right hbinom hc2_nn
          _ = (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1), L ^ j * c ^ 2 := by
              rw [mul_assoc, Finset.sum_mul]
    have hstep2 : ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
            (I := I) (M := M) g₀ 0 2,
          (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 =
        (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 := by
      rw [tsum_mul_left]
      congr 1
      exact Summable.tsum_finsetSum (fun j _ => hmode_summable j)
    rw [hstep2] at hstep1
    refine hstep1.trans ?_
    have hsum_le : ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2 ≤
        Csum * Sall ^ 2 := by
      have hSmono : ∀ j ∈ Finset.range (n + 1),
          (∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 ≤ Sall ^ 2 := by
        intro j hj
        have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : ∑ a ∈ Finset.range (j + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ ≤ Sall := by
          rw [hSall_def]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => norm_nonneg _)
          intro a ha; rw [Finset.mem_range] at ha ⊢; omega
        have hlow_nn : 0 ≤ ∑ a ∈ Finset.range (j + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖ :=
          Finset.sum_nonneg (fun a _ => norm_nonneg _)
        exact pow_le_pow_left₀ hlow_nn hsub 2
      calc ∑ j ∈ Finset.range (n + 1),
            ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
                (I := I) (M := M) g₀ 0 2,
              (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
                (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2
          ≤ ∑ j ∈ Finset.range (n + 1),
              Cmode j * (∑ a ∈ Finset.range (j + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 a S‖) ^ 2 :=
            Finset.sum_le_sum (fun j _ => hCmode j S)
        _ ≤ ∑ j ∈ Finset.range (n + 1), Cmode j * Sall ^ 2 :=
            Finset.sum_le_sum (fun j hj =>
              mul_le_mul_of_nonneg_left (hSmono j hj) (hCmode_nn j))
        _ = Csum * Sall ^ 2 := by rw [hCsum_def, Finset.sum_mul]
    calc (2 : ℝ) ^ n * ∑ j ∈ Finset.range (n + 1),
          ∑' m : DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
              (I := I) (M := M) g₀ 0 2,
            (TensorEigenIdx.lambda (I := I) (M := M) m) ^ j *
              (tensorL2Coeff (I := I) (M := M) h_compact (SmoothCcTensor.toL2 S) m) ^ 2
        ≤ (2 : ℝ) ^ n * (Csum * Sall ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (2 : ℝ) ^ n * Csum * Sall ^ 2 := by ring
  have hrhs_nn : 0 ≤ Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall :=
    mul_nonneg (Real.sqrt_nonneg _) hSall_nn
  have hsqrt_sq : (Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall) ^ 2 =
      (2 : ℝ) ^ n * Csum * Sall ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hNspec_sq_le : Nspec ^ 2 ≤ (Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall) ^ 2 := by
    rw [hsqrt_sq]; exact hsq_le
  have := Real.sqrt_le_sqrt hNspec_sq_le
  rw [Real.sqrt_sq hNspec_nn, Real.sqrt_sq hrhs_nn] at this
  calc Nspec ≤ Real.sqrt ((2 : ℝ) ^ n * Csum) * Sall := this
    _ = Real.sqrt ((2 : ℝ) ^ n * Csum) * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ := by rw [hSall_def]

set_option linter.unusedVariables false in

theorem smoothRemainderDiff_ballLipschitz_Ha2
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  classical

  have hordB : (((a + 2 : ℕ)) : ℝ) = (a : ℝ) + 2 := by push_cast; ring

  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ a

  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)

  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGradSum_ballLipschitz (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀

  refine ⟨Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def

  set Ndist : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ with hNdist_def
  have hNdist_nn : 0 ≤ Ndist := norm_nonneg _
  have hNdist_eq : Ndist = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W‖ := by
    rw [hNdist_def, hW_def, smoothCcToTensorHs_sub]

  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball

  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTcov hT'cov
  rw [← hD_def] at hcol

  have hWsum := hCb W
  rw [hordB, ← hNdist_eq] at hWsum
  set Wsum : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
    ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ with hWsum_def
  have hWsum_nn : 0 ≤ Wsum :=
    Finset.sum_nonneg fun i _ => norm_nonneg _
  have hWsumsq_le : Wsum ^ 2 ≤ Cb ^ 2 * Ndist ^ 2 := by
    have := mul_le_mul hWsum hWsum hWsum_nn (by positivity)
    calc Wsum ^ 2 = Wsum * Wsum := by ring
      _ ≤ (Cb * Ndist) * (Cb * Ndist) := this
      _ = Cb ^ 2 * Ndist ^ 2 := by ring

  have hsq_le_sumsq : (∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2) ≤ Wsum ^ 2 := by
    rw [hWsum_def]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)

  have hcol' : (∑ q ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2) ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := by
    refine hcol.trans ?_
    calc Ccol * ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i W‖ ^ 2
        ≤ Ccol * Wsum ^ 2 := mul_le_mul_of_nonneg_left hsq_le_sumsq hCcol_nn
      _ ≤ Ccol * (Cb ^ 2 * Ndist ^ 2) := mul_le_mul_of_nonneg_left hWsumsq_le hCcol_nn

  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hDsum_sq : Dsum ^ 2 ≤ ((a : ℝ) + 1) *
      ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := by
    rw [hDsum_def]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := Finset.range (a + 1))
      (f := fun q => ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖)
    rw [Finset.card_range] at hcheb
    refine hcheb.trans (le_of_eq ?_)
    congr 1
    push_cast; ring

  have hbridgeA := hCa D
  rw [← hDsum_def] at hbridgeA

  have hDsum_le : Dsum ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by
    have hDsum_sq_le : Dsum ^ 2 ≤ (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      calc Dsum ^ 2 ≤ ((a : ℝ) + 1) *
            ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ^ 2 := hDsum_sq
        _ ≤ ((a : ℝ) + 1) * (Ccol * (Cb ^ 2 * Ndist ^ 2)) :=
            mul_le_mul_of_nonneg_left hcol' (by positivity)
        _ = (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by ring
    have hrhs_nn : 0 ≤ Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist :=
      mul_nonneg (Real.sqrt_nonneg _) hNdist_nn
    have hsqrt_sq : (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 =
        (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hsqle : Dsum ^ 2 ≤ (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) ^ 2 := by
      rw [hsqrt_sq]; exact hDsum_sq_le
    have := Real.sqrt_le_sqrt hsqle
    rwa [Real.sqrt_sq hDsum_nn, Real.sqrt_sq hrhs_nn] at this
  have hKcoe : (Real.toNNReal (Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2))) : ℝ) =
      Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * Real.sqrt (((a : ℝ) + 1) * (Ccol * Cb ^ 2)) * Ndist := by ring

set_option linter.unusedVariables false in

theorem appCcTwoArmQUniform
    (g₀ : SmoothRiemannianMetric I M) (b₀ s₀ a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℕ), q ≤ a →
      ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ q
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          C * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := by
  classical
  set Kf : ℕ → ℝ := fun k => (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose
    with hKf_def
  have hKf_nn : ∀ k, 0 ≤ Kf k := fun k =>
    (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.1
  have hKf_spec : ∀ k, ∀ (Φ : SmoothCcTensor g₀ b₀ s₀) (W : SmoothCcTensor g₀ 0 b₀) (ΛΦ ΛW : ℝ),
        0 ≤ ΛΦ → 0 ≤ ΛW →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ b₀ s₀ x (Φ.toSection x) ≤ ΛΦ ^ 2) →
        (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 b₀ x (W.toSection x) ≤ ΛW ^ 2) →
        ‖iteratedCovGrad (I := I) g₀ 0 s₀ k
            (appCc (I := I) (M := M) g₀ b₀ s₀ Φ W)‖ ^ 2 ≤
          Kf k * (ΛW ^ 2 * ∑ i ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2
              + ΛΦ ^ 2 * ∑ l ∈ Finset.range (k + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2) := fun k =>
    (appCc_topOrder_l2_twoArm_mixed_ballUniform (I := I) g₀ b₀ s₀ k).choose_spec.2
  refine ⟨(Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf,
    le_trans (hKf_nn 0) (Finset.le_sup' Kf (Finset.mem_range.mpr (Nat.succ_pos a))), ?_⟩
  intro q hq Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup
  have hqmem : q ∈ Finset.range (a + 1) := Finset.mem_range.mpr (by omega)
  have hKq_le : Kf q ≤
      (Finset.range (a + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero a)) Kf :=
    Finset.le_sup' Kf hqmem
  refine le_trans (hKf_spec q Φ W ΛΦ ΛW hΛΦ hΛW hΦsup hWsup) ?_
  refine mul_le_mul_of_nonneg_right hKq_le ?_
  have h1 : 0 ≤ ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ b₀ s₀ i Φ‖ ^ 2 := by positivity
  have h2 : 0 ≤ ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 b₀ l W‖ ^ 2 := by positivity
  linarith

set_option maxHeartbeats 1600000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in

theorem ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy
    (g₀ : SmoothRiemannianMetric I M) (m : ℕ)
    (h_lossy : 2 * Module.finrank ℝ E + 4 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T : SmoothCcTensor g₀ 0 2),
      gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T)
        (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) := by
  classical
  set kE : ℕ := Module.finrank ℝ E / 2 + 1 with hkE_def
  have hkE_super : 2 * kE > Module.finrank ℝ E + 2 * 0 := by
    rw [hkE_def]; omega
  have h4kEm : (4 * kE : ℕ) ≤ m := by
    rw [hkE_def]; omega

  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    DifferentialGeometry.PDE.RicciFlow.tensorPouSobolevHilbert_embedding_Ck_gNorm
      (I := I) (M := M) g₀ 0 2 kE 0 hkE_super

  obtain ⟨C₂, hC₂_nn, hC₂⟩ :=
    tensorPouSobolevHsNorm_le_ccSpectralEmbed (I := I) (M := M) g₀ (2 * kE)
  refine ⟨C₁ * (C₂ + 1), by positivity, fun T => ?_⟩
  letI : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g₀ 0 2

  have hupper : C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
        (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ ≤
      (C₁ * (C₂ + 1)) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ := by
    have hstep2 : ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
          (g := g₀) (r := 0) (s := 2) (2 * kE) T‖ =
        (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal :=
      DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.tensorPouSobolevHilbert_norm_eq
        (I := I) (M := M) g₀ (2 * kE) T
    have hstep3 : (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal ≤
        C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ := hC₂ T
    have hstep4 : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤
        ‖ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T‖ := by
      refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
      have : (2 * (2 * kE) : ℕ) ≤ m := by omega
      exact_mod_cast this
    have hembed_eq : ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T =
        smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    set Nm : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ with hNm_def
    have hNm_nn : 0 ≤ Nm := norm_nonneg _
    have hspec_le : ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖ ≤ Nm := by
      rw [hNm_def, ← hembed_eq]; exact hstep4
    calc C₁ * ‖DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev.SmoothCcTensor.toHs
            (g := g₀) (r := 0) (s := 2) (2 * kE) T‖
        = C₁ * (DifferentialGeometry.Analysis.Sobolev.Tensor.tensorPouSobolevHsNorm (I := I) (M := M) g₀ (2 * kE) T).toReal := by rw [hstep2]
      _ ≤ C₁ * (C₂ * ‖ccSpectralEmbed (I := I) (M := M) g₀ ((2 * (2 * kE) : ℕ) : ℝ) T‖) :=
          mul_le_mul_of_nonneg_left hstep3 hC₁_pos.le
      _ ≤ C₁ * (C₂ * Nm) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hspec_le hC₂_nn) hC₁_pos.le
      _ ≤ (C₁ * (C₂ + 1)) * Nm := by nlinarith [hNm_nn, hC₁_pos.le, hC₂_nn]

  have hfibre := fun x : M => le_trans (hC₁ T x) hupper

  intro x v w
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g₀ T x
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn

  have hvw := hcs v w
  have hwv := hcs w v
  have hfx := hfibre x

  rw [ccTensorBilinSymm_apply]
  have habs : |(1 / 2 : ℝ) *
      (ccTensorBilin (I := I) g₀ T x v w + ccTensorBilin (I := I) g₀ T x w v)| ≤
      (1 / 2 : ℝ) * (|ccTensorBilin (I := I) g₀ T x v w| +
        |ccTensorBilin (I := I) g₀ T x w v|) := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
  refine habs.trans ?_

  nlinarith [hvw, hwv, hfx, hsv_nn, hsw_nn, hmul_nn, mul_nonneg hsw_nn hsv_nn,
    mul_le_mul_of_nonneg_right hfx hmul_nn,
    mul_le_mul_of_nonneg_right hfx (mul_nonneg hsw_nn hsv_nn)]

theorem deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_dataWeighted_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) (hδ₀_nn : 0 ≤ δ₀) :
    ∃ ΛC Γ : ℝ, 0 ≤ ΛC ∧ 0 ≤ Γ ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∃ (C₀ : SmoothCcTensor g₀ 2 2) (C₁ : SmoothCcTensor g₀ 3 2) (C₂ : SmoothCcTensor g₀ 4 2),
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
              deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ') =
            (appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) +
              appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) +
              appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 2 2 x (C₀.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 3 2 x (C₁.toSection x) ≤ ΛC ^ 2) ∧
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 4 2 x (C₂.toSection x) ≤
            (ΛC * max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                 ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖) ^ 2) ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 2 2 i C₀‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 3 2 i C₁‖ ^ 2) ≤ Γ ^ 2 ∧
          (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤ Γ ^ 2 := by
  classical
  obtain ⟨Ksob, hKsob_pos, hKsob⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ (a + 1)
      (by omega)
  obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hfib⟩ :=
    deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_fibreWeighted_ballUniform_of_symm
      (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
  refine ⟨ΛC * (Ksob + 1), Γ, by positivity, hΓ_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  set βT : ℝ := Ksob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 1 : ℕ) : ℝ) T‖ with hβT_def
  set βT' : ℝ := Ksob * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 1 : ℕ) : ℝ) T'‖ with hβT'_def
  have hβT_nn : 0 ≤ βT := by rw [hβT_def]; positivity
  have hβT'_nn : 0 ≤ βT' := by rw [hβT'_def]; positivity
  have hcastord : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hβTfib : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) βT := by
    rw [hβT_def]; exact hKsob T
  have hβT'fib : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') βT' := by
    rw [hβT'_def]; exact hKsob T'
  obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
    hfib T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hβT_nn hβT'_nn hβTfib hβT'fib hTball hT'ball
  set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
  have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
  have hΛle : ΛC ^ 2 ≤ (ΛC * (Ksob + 1)) ^ 2 := by
    refine pow_le_pow_left₀ hΛC_nn ?_ 2
    nlinarith [hΛC_nn, hKsob_pos.le]
  have hβmax_eq : max βT βT' = Ksob * Dm := by
    rw [hβT_def, hβT'_def, hDm_def, hcastord, mul_max_of_nonneg _ _ hKsob_pos.le]
  refine ⟨C₀, C₁, C₂, hid, fun x => le_trans (hC₀sup x) hΛle,
    fun x => le_trans (hC₁sup x) hΛle, ?_, hC₀jet, hC₁jet, hC₂jet⟩
  intro x
  refine le_trans (hC₂sup x) ?_
  rw [hβmax_eq]
  refine pow_le_pow_left₀ (mul_nonneg hΛC_nn (mul_nonneg hKsob_pos.le hDm_nn)) ?_ 2
  nlinarith [hΛC_nn, hKsob_pos.le, hDm_nn, mul_nonneg hKsob_pos.le hDm_nn]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                     ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
                   * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
                       ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
              Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)) := by
  classical
  by_cases hδ₀_nn : 0 ≤ δ₀
  · obtain ⟨ΛC, Γ, hΛC_nn, hΓ_nn, hcoeff⟩ :=
      deTurckSmoothRemainderDiff_threeArm_coeffC0_jetL2_dataWeighted_ballUniform_of_symm
        (I := I) g₀ g_bg a ha_super hR hδ₀ hδ₀_nn
    obtain ⟨K₀, hK₀_nn, hK₀⟩ := appCcTwoArmQUniform (I := I) g₀ 2 2 a
    obtain ⟨K₁, hK₁_nn, hK₁⟩ := appCcTwoArmQUniform (I := I) g₀ 3 2 a
    obtain ⟨K₂, hK₂_nn, hK₂⟩ := appCcTwoArmQUniform (I := I) g₀ 4 2 a
    obtain ⟨Cemb1, hCemb1_nn, hemb1⟩ :=
      deTurckArmDiff_supercritical_pointwise_jet_le_lowerWindow (I := I) g₀ a ha_super
    set Kmax : ℝ := max K₀ (max K₁ K₂) with hKmax_def
    have hKmax_nn : 0 ≤ Kmax := le_trans hK₀_nn (le_max_left _ _)
    have hK₀_le : K₀ ≤ Kmax := le_max_left _ _
    have hK₁_le : K₁ ≤ Kmax := le_trans (le_max_left _ _) (le_max_right _ _)
    have hK₂_le : K₂ ≤ Kmax := le_trans (le_max_right _ _) (le_max_right _ _)
    set base : ℝ := Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1)) with hbase_def
    have hbase_nn : 0 ≤ base := by rw [hbase_def]; positivity
    refine ⟨3 * Real.sqrt base, by positivity, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
    set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
    have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
    set S₂ : ℝ := ∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₂_def
    set S₁ : ℝ := ∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hS₁_def
    have hS₂_nn : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hS₁_nn : 0 ≤ S₁ := Finset.sum_nonneg fun i _ => sq_nonneg _
    obtain ⟨C₀, C₁, C₂, hid, hC₀sup, hC₁sup, hC₂sup, hC₀jet, hC₁jet, hC₂jet⟩ :=
      hcoeff T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
    set A₀ := appCc (I := I) (M := M) g₀ 2 2 C₀ (iteratedCovGrad (I := I) g₀ 0 2 0 (T - T')) with hA₀
    set A₁ := appCc (I := I) (M := M) g₀ 3 2 C₁ (iteratedCovGrad (I := I) g₀ 0 2 1 (T - T')) with hA₁
    set A₂ := appCc (I := I) (M := M) g₀ 4 2 C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T')) with hA₂
    have hN_split : deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
        deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ' =
          A₀ + A₁ + A₂ := by
      rw [hA₀, hA₁, hA₂]; exact hid
    have hWsup1 : ∀ (m : ℕ), m ≤ 2 → ∀ x : M,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x
            ((iteratedCovGrad (I := I) g₀ 0 2 m (T - T')).toSection x) ≤
          (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 := by
      intro m hm x
      rw [Real.sq_sqrt (by positivity)]
      have hembx := hemb1 (T - T') x
      rw [hS₁_def]
      have hmem : m ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
      refine le_trans (Finset.single_le_sum
        (f := fun qq => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + qq) x
          ((iteratedCovGrad (I := I) g₀ 0 2 qq (T - T')).toSection x))
        (fun qq _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + qq) x _) hmem) ?_
      exact hembx
    have hWjet : ∀ (m : ℕ), m ≤ 2 →
        (∑ l ∈ Finset.range (q + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤
          ∑ i ∈ Finset.range (a + m + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 := by
      intro m hm
      have hcomp : ∀ l : ℕ,
          ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
            ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 := by
        intro l
        have hbridgeL : ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + m) + l) x
              ((iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          rw [SmoothCcTensor.norm_def]
          exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ ((2 + m) + l)
            (iteratedCovGrad (I := I) g₀ 0 (2 + m) l (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))
        have hbridgeR : ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 =
            ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (m + l)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
          rw [SmoothCcTensor.norm_def]
          exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (m + l))
            (iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T'))
        rw [hbridgeL, hbridgeR]
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        have hrw := rfns_iteratedCovGrad_comp (I := I) (M := M) g₀ 0 2 m l (T - T') x
        simpa only [Nat.add_assoc] using hrw
      rw [show (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) =
          ∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 (m + l) (T - T')‖ ^ 2 from
        Finset.sum_congr rfl (fun l _ => hcomp l)]
      set f : ℕ → ℝ := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2 with hf_def
      have hf_nn : ∀ i, 0 ≤ f i := fun i => sq_nonneg _
      have himg : (Finset.range (q + 1)).image (fun l => m + l) ⊆ Finset.range (a + m + 1) := by
        intro i hi
        rw [Finset.mem_image] at hi
        obtain ⟨l, hl, rfl⟩ := hi
        rw [Finset.mem_range] at hl ⊢
        omega
      have hinj : ∀ l₁ ∈ Finset.range (q + 1), ∀ l₂ ∈ Finset.range (q + 1),
          m + l₁ = m + l₂ → l₁ = l₂ := fun l₁ _ l₂ _ h => by omega
      calc (∑ l ∈ Finset.range (q + 1), f (m + l))
          = ∑ i ∈ (Finset.range (q + 1)).image (fun l => m + l), f i :=
            (Finset.sum_image hinj).symm
        _ ≤ ∑ i ∈ Finset.range (a + m + 1), f i :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => hf_nn i)
    have hcoeffjet_le : ∀ (m : ℕ) (Cm : SmoothCcTensor g₀ (2 + m) 2) (bnd : ℝ),
        0 ≤ bnd →
        (∑ i ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd →
        (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ bnd := by
      intro m Cm bnd hbnd_nn hjet
      refine le_trans ?_ hjet
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => sq_nonneg _)
      exact Finset.range_mono (by omega)
    have harmTop : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
        Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
      have htame := hK₂ q hq C₂ (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))
        (ΛC * Dm) (Real.sqrt (Cemb1 ^ 2 * S₁)) (mul_nonneg hΛC_nn hDm_nn) (Real.sqrt_nonneg _)
        hC₂sup (hWsup1 2 (by norm_num))
      have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
      have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2) ≤
          Γ ^ 2 :=
        hcoeffjet_le 2 C₂ (Γ ^ 2) (sq_nonneg _) hC₂jet
      have hwjet : (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 4 l (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2) ≤
          S₂ := by
        have h := hWjet 2 (by norm_num)
        rw [hS₂_def]
        exact h
      have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2 ≤ base * (S₁ + Dm ^ 2 * S₂) := by
        rw [hA₂]
        refine le_trans htame ?_
        rw [hΛWsq]
        have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
          mul_le_mul_of_nonneg_left hcjet (by positivity)
        have ha2 : (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 4 l
                (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 ≤ (ΛC * Dm) ^ 2 * S₂ :=
          mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
        have hinner :
            (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + Dm ^ 2 * S₂) := by
          set B : ℝ := (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) with hB_def
          have hB_nn : 0 ≤ B := by rw [hB_def]; positivity
          have hcoeff_le : Cemb1 ^ 2 * Γ ^ 2 ≤ B := by
            rw [hB_def]
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          have hΛC_le : ΛC ^ 2 ≤ B := by
            rw [hB_def]
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg Γ),
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          have hterm1 : (Cemb1 ^ 2 * S₁) * Γ ^ 2 ≤ B * S₁ := by
            rw [show (Cemb1 ^ 2 * S₁) * Γ ^ 2 = (Cemb1 ^ 2 * Γ ^ 2) * S₁ by ring]
            exact mul_le_mul_of_nonneg_right hcoeff_le hS₁_nn
          have hterm2 : (ΛC * Dm) ^ 2 * S₂ ≤ B * (Dm ^ 2 * S₂) := by
            rw [show (ΛC * Dm) ^ 2 * S₂ = ΛC ^ 2 * (Dm ^ 2 * S₂) by ring]
            exact mul_le_mul_of_nonneg_right hΛC_le (by positivity)
          have hsum_le : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * Dm) ^ 2 * S₂ ≤
              B * (S₁ + Dm ^ 2 * S₂) := by
            calc (Cemb1 ^ 2 * S₁) * Γ ^ 2 + (ΛC * Dm) ^ 2 * S₂
                ≤ B * S₁ + B * (Dm ^ 2 * S₂) := add_le_add hterm1 hterm2
              _ = B * (S₁ + Dm ^ 2 * S₂) := by ring
          linarith [ha1, ha2, hsum_le]
        have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
              + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 4 l
                  (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2 := by positivity
        calc K₂ * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 4 2 i C₂‖ ^ 2
                + (ΛC * Dm) ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 4 l
                    (iteratedCovGrad (I := I) g₀ 0 2 2 (T - T'))‖ ^ 2)
            ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * (S₁ + Dm ^ 2 * S₂)) :=
              mul_le_mul hK₂_le hinner hinner_nn hKmax_nn
          _ = base * (S₁ + Dm ^ 2 * S₂) := by rw [hbase_def]; ring
      have hfinal : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
        have hsqrt_le : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
            Real.sqrt (base * (S₁ + Dm ^ 2 * S₂)) := by
          rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ =
              Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ^ 2) from
            (Real.sqrt_sq (norm_nonneg _)).symm]
          exact Real.sqrt_le_sqrt hsq
        refine hsqrt_le.trans ?_
        have hrhs_nn : 0 ≤ Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
          have : 0 ≤ Real.sqrt S₁ + Dm * Real.sqrt S₂ := by
            have := mul_nonneg hDm_nn (Real.sqrt_nonneg S₂)
            have := Real.sqrt_nonneg S₁
            linarith
          exact mul_nonneg (Real.sqrt_nonneg _) this
        have hsq_rhs : (Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2 =
            base * (S₁ + Dm ^ 2 * S₂ + 2 * Dm * (Real.sqrt S₁ * Real.sqrt S₂)) := by
          rw [mul_pow, Real.sq_sqrt hbase_nn, add_sq, mul_pow,
            Real.sq_sqrt hS₁_nn, Real.sq_sqrt hS₂_nn]
          ring
        have hle_sq : base * (S₁ + Dm ^ 2 * S₂) ≤
            (Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2 := by
          rw [hsq_rhs]
          have hcross_nn : 0 ≤ 2 * Dm * (Real.sqrt S₁ * Real.sqrt S₂) := by
            have := mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂)
            linarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hDm_nn)
              (mul_nonneg (Real.sqrt_nonneg S₁) (Real.sqrt_nonneg S₂))]
          nlinarith [hbase_nn, hcross_nn, mul_nonneg hbase_nn hcross_nn]
        calc Real.sqrt (base * (S₁ + Dm ^ 2 * S₂))
            ≤ Real.sqrt ((Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂)) ^ 2) :=
              Real.sqrt_le_sqrt hle_sq
          _ = Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := Real.sqrt_sq hrhs_nn
      exact hfinal
    have harmLow : ∀ (m : ℕ) (hm : m ≤ 1) (Cm : SmoothCcTensor g₀ (2 + m) 2) (Km : ℝ)
        (hKm_le : Km ≤ Kmax)
        (hKm : ∀ (Φ : SmoothCcTensor g₀ (2 + m) 2) (W : SmoothCcTensor g₀ 0 (2 + m)) (ΛΦ ΛW : ℝ),
          0 ≤ ΛΦ → 0 ≤ ΛW →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Φ.toSection x) ≤ ΛΦ ^ 2) →
          (∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + m) x (W.toSection x) ≤ ΛW ^ 2) →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q (appCc (I := I) (M := M) g₀ (2 + m) 2 Φ W)‖ ^ 2 ≤
            Km * (ΛW ^ 2 * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Φ‖ ^ 2
                + ΛΦ ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l W‖ ^ 2))
        (hCmsup : ∀ x : M, riemannianFiberNormSq (I := I) (M := M) g₀ (2 + m) 2 x (Cm.toSection x) ≤ ΛC ^ 2)
        (hCmjet : (∑ i ∈ Finset.range (a + 1),
            ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤ Γ ^ 2),
        ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ≤ Real.sqrt (base * S₁) := by
      intro m hm Cm Km hKm_le hKm hCmsup hCmjet
      have htame := hKm Cm (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))
        ΛC (Real.sqrt (Cemb1 ^ 2 * S₁)) hΛC_nn (Real.sqrt_nonneg _) hCmsup
        (hWsup1 m (by omega))
      have hΛWsq : (Real.sqrt (Cemb1 ^ 2 * S₁)) ^ 2 = Cemb1 ^ 2 * S₁ := Real.sq_sqrt (by positivity)
      have hcjet : (∑ i ∈ Finset.range (q + 1), ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2) ≤
          Γ ^ 2 := hcoeffjet_le m Cm (Γ ^ 2) (sq_nonneg _) hCmjet
      have hwjet : (∑ l ∈ Finset.range (q + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2) ≤ S₁ := by
        have h := hWjet m (by omega)
        refine le_trans h ?_
        rw [hS₁_def]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun i _ _ => sq_nonneg _)
      have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 q
          (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
            (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2 ≤ base * S₁ := by
        refine le_trans htame ?_
        rw [hΛWsq]
        have ha1 : (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2 ≤ (Cemb1 ^ 2 * S₁) * Γ ^ 2 :=
          mul_le_mul_of_nonneg_left hcjet (by positivity)
        have ha2 : ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
              ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 ≤ ΛC ^ 2 * S₁ :=
          mul_le_mul_of_nonneg_left hwjet (sq_nonneg _)
        have hinner :
            (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2
            ≤ (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
          have hsum_le : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ ≤
              (Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁ := by
            have hfactor : (Cemb1 ^ 2 * S₁) * Γ ^ 2 + ΛC ^ 2 * S₁ =
                (Cemb1 ^ 2 * Γ ^ 2 + ΛC ^ 2) * S₁ := by ring
            rw [hfactor]
            refine mul_le_mul_of_nonneg_right ?_ hS₁_nn
            nlinarith [sq_nonneg Cemb1, sq_nonneg Γ, sq_nonneg ΛC,
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg Γ),
              mul_nonneg (sq_nonneg Cemb1) (sq_nonneg ΛC)]
          linarith [ha1, ha2, hsum_le]
        have hinner_nn : 0 ≤ (Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
              + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                  (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2 := by positivity
        calc Km * ((Cemb1 ^ 2 * S₁) * ∑ i ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ (2 + m) 2 i Cm‖ ^ 2
                + ΛC ^ 2 * ∑ l ∈ Finset.range (q + 1),
                  ‖iteratedCovGrad (I := I) g₀ 0 (2 + m) l
                    (iteratedCovGrad (I := I) g₀ 0 2 m (T - T'))‖ ^ 2)
            ≤ Kmax * ((Cemb1 ^ 2 + 1) * (Γ ^ 2 + ΛC ^ 2 + 1) * S₁) :=
              mul_le_mul hKm_le hinner hinner_nn hKmax_nn
          _ = base * S₁ := by rw [hbase_def]; ring
      rw [show ‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ =
          Real.sqrt (‖iteratedCovGrad (I := I) g₀ 0 2 q
            (appCc (I := I) (M := M) g₀ (2 + m) 2 Cm
              (iteratedCovGrad (I := I) g₀ 0 2 m (T - T')))‖ ^ 2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq
    have ha0 := harmLow 0 (by norm_num) C₀ K₀ hK₀_le (hK₀ q hq) hC₀sup hC₀jet
    have ha1 := harmLow 1 (by norm_num) C₁ K₁ hK₁_le (hK₁ q hq) hC₁sup hC₁jet
    have hnorm0 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀‖ ≤ Real.sqrt (base * S₁) := by
      rw [hA₀]; exact ha0
    have hnorm1 : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₁‖ ≤ Real.sqrt (base * S₁) := by
      rw [hA₁]; exact ha1
    have hgoal : ‖iteratedCovGrad (I := I) g₀ 0 2 q
        (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        3 * Real.sqrt base * (Dm * Real.sqrt S₂ + Real.sqrt S₁) := by
      rw [hN_split, iteratedCovGrad_add (I := I) g₀ 0 2 q (A₀ + A₁) A₂,
        iteratedCovGrad_add (I := I) g₀ 0 2 q A₀ A₁]
      have hsqrt_lowfac : Real.sqrt (base * S₁) = Real.sqrt base * Real.sqrt S₁ :=
        Real.sqrt_mul hbase_nn S₁
      have htri : ‖iteratedCovGrad (I := I) g₀ 0 2 q A₀ +
            iteratedCovGrad (I := I) g₀ 0 2 q A₁ +
            iteratedCovGrad (I := I) g₀ 0 2 q A₂‖ ≤
          Real.sqrt (base * S₁) + Real.sqrt (base * S₁) +
            Real.sqrt base * (Real.sqrt S₁ + Dm * Real.sqrt S₂) := by
        refine le_trans (norm_add_le _ _) ?_
        refine add_le_add (le_trans (norm_add_le _ _) (add_le_add hnorm0 hnorm1)) harmTop
      refine htri.trans ?_
      rw [hsqrt_lowfac]
      have hsb_nn : 0 ≤ Real.sqrt base := Real.sqrt_nonneg _
      have hs1_nn : 0 ≤ Real.sqrt S₁ := Real.sqrt_nonneg _
      have hs2_nn : 0 ≤ Real.sqrt S₂ := Real.sqrt_nonneg _
      nlinarith [hsb_nn, hs1_nn, hs2_nn, hDm_nn,
        mul_nonneg hsb_nn hs1_nn, mul_nonneg hsb_nn hs2_nn,
        mul_nonneg (mul_nonneg hDm_nn hsb_nn) hs2_nn]
    refine hgoal.trans (le_of_eq ?_)
    rw [hS₂_def, hS₁_def]
  · refine ⟨0, le_refl 0, ?_⟩
    intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
    have hδ₀_neg : δ₀ < 0 := lt_of_not_ge hδ₀_nn
    have hδ_neg : δ < 0 := lt_of_le_of_lt hδ_le hδ₀_neg
    by_cases hM : Nonempty M
    · obtain ⟨x₀⟩ := hM
      obtain ⟨v, hv⟩ : ∃ v : TangentSpace I x₀, v ≠ 0 := by
        haveI : Nontrivial (TangentSpace I x₀) := by
          have hfr : 0 < Module.finrank ℝ (TangentSpace I x₀) := by
            have : Module.finrank ℝ (TangentSpace I x₀) = Module.finrank ℝ E := rfl
            rw [this]; exact Nat.pos_of_ne_zero (NeZero.ne _)
          exact Module.nontrivial_of_finrank_pos hfr
        exact exists_ne 0
      have hpos : 0 < g₀.inner x₀ v v := g₀.pos x₀ v hv
      have hbound := hδ x₀ v v
      have hsqrt_pos : 0 < Real.sqrt (g₀.inner x₀ v v) := Real.sqrt_pos.mpr hpos
      have habs_nn : 0 ≤ |ccTensorBilinSymm (I := I) g₀ T x₀ v v| := abs_nonneg _
      have hδ_nonneg : 0 ≤ δ := by
        by_contra hδc
        have hδc' : δ < 0 := lt_of_not_ge hδc
        have hrhs_neg : δ * Real.sqrt (g₀.inner x₀ v v) * Real.sqrt (g₀.inner x₀ v v) < 0 := by
          have h1 : δ * Real.sqrt (g₀.inner x₀ v v) < 0 :=
            mul_neg_of_neg_of_pos hδc' hsqrt_pos
          exact mul_neg_of_neg_of_pos h1 hsqrt_pos
        linarith [le_trans habs_nn hbound]
      linarith
    · rw [not_nonempty_iff] at hM
      have hzero : ∀ (r s : ℕ) (P : SmoothCcTensor g₀ r s), ‖P‖ = 0 := by
        intro r s P
        rw [SmoothCcTensor.norm_def, tensorL2Norm_def, tensorL2Inner,
          MeasureTheory.integral_of_isEmpty, Real.sqrt_zero]
      rw [zero_mul]
      exact le_of_eq (hzero _ _ _)

set_option linter.unusedVariables false in

theorem deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (hδ_le : δ ≤ δ₀)
        (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
        (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
        (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
        (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ q : ℕ, q ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 0 2 q
              (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
                deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
            C * (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                     ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
                   * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) := by
  classical
  obtain ⟨Ccov, hCcov_nn, hCcov⟩ :=
    deTurckSmoothRemainderDiff_iteratedCovGrad_l2_dataWeighted_ballUniform_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  obtain ⟨Cb2, hCb2_nn, hCb2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  obtain ⟨Cb1, hCb1_nn, hCb1⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 1)
  refine ⟨Ccov * max Cb2 Cb1, by positivity, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
  set H2 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ with hH2_def
  set H1 : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ with hH1_def
  have hH2_nn : 0 ≤ H2 := norm_nonneg _
  have hH1_nn : 0 ≤ H1 := norm_nonneg _
  set Dm : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
                    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ with hDm_def
  have hDm_nn : 0 ≤ Dm := le_trans (norm_nonneg _) (le_max_left _ _)
  have hsqrt2_le : Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤ max Cb2 Cb1 * H2 := by
    have hsq_le_sum : (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
        (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hcastord : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
    have hsum_le : (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ≤ Cb2 * H2 := by
      have h := hCb2 (T - T')
      rw [hcastord] at h
      exact h
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Real.sqrt ((∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2) := Real.sqrt_le_sqrt hsq_le_sum
      _ = ∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ := Real.sqrt_sq hsum_nn
      _ ≤ Cb2 * H2 := hsum_le
      _ ≤ max Cb2 Cb1 * H2 := mul_le_mul_of_nonneg_right (le_max_left _ _) hH2_nn
  have hsqrt1_le : Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤ max Cb2 Cb1 * H1 := by
    have hsq_le_sum : (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
        (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2 :=
      Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg _)
    have hcastord : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
    have hsum_le : (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ≤ Cb1 * H1 := by
      have h := hCb1 (T - T')
      rw [hcastord] at h
      exact h
    have hsum_nn : 0 ≤ ∑ i ∈ Finset.range (a + 1 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    calc Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Real.sqrt ((∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖) ^ 2) := Real.sqrt_le_sqrt hsq_le_sum
      _ = ∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ := Real.sqrt_sq hsum_nn
      _ ≤ Cb1 * H1 := hsum_le
      _ ≤ max Cb2 Cb1 * H1 := mul_le_mul_of_nonneg_right (le_max_right _ _) hH1_nn
  have hcov := hCcov T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball q hq
  refine hcov.trans ?_
  have hmaxnn : 0 ≤ max Cb2 Cb1 := le_max_of_le_left hCb2_nn
  have hstep : Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
        Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) ≤
      max Cb2 Cb1 * (Dm * H2 + H1) := by
    have ht2 := mul_le_mul_of_nonneg_left hsqrt2_le hDm_nn
    calc Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
          Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2)
        ≤ Dm * (max Cb2 Cb1 * H2) + max Cb2 Cb1 * H1 := add_le_add ht2 hsqrt1_le
      _ = max Cb2 Cb1 * (Dm * H2 + H1) := by ring
  calc Ccov * (Dm * Real.sqrt (∑ i ∈ Finset.range (a + 2 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2) +
          Real.sqrt (∑ i ∈ Finset.range (a + 1 + 1),
            ‖iteratedCovGrad (I := I) g₀ 0 2 i (T - T')‖ ^ 2))
      ≤ Ccov * (max Cb2 Cb1 * (Dm * H2 + H1)) :=
        mul_le_mul_of_nonneg_left hstep hCcov_nn
    _ = Ccov * max Cb2 Cb1 * (Dm * H2 + H1) := by ring

set_option linter.unusedVariables false in

theorem smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
      (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
      (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ)
          (deTurckSmoothRemainder (I := I) g₀ g_bg T (lt_of_le_of_lt hδ_le hδ₀) hδ -
            deTurckSmoothRemainder (I := I) g₀ g_bg T' (lt_of_le_of_lt hδ'_le hδ₀) hδ')‖ ≤
        (K : ℝ) *
          (max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
               ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
             * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖) := by
  classical
  have hordB : (((a + 2 : ℕ)) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ a
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ (a + 2)
  have hR'_nn : (0 : ℝ) ≤ Cb * R := mul_nonneg hCb_nn hR.le
  obtain ⟨Ccol, hCcol_nn, hCcol⟩ :=
    deTurckRemainderDiff_iteratedCovGrad_ballLipschitz_dataWeighted_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR'_nn hδ₀
  refine ⟨Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  set W : SmoothCcTensor g₀ 0 2 := T - T' with hW_def
  set D : SmoothCcTensor g₀ 0 2 :=
    deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ -
      deTurckSmoothRemainder (I := I) g₀ g_bg T' hδ'_lt hδ' with hD_def
  set rhs : ℝ :=
    max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖
      * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ +
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ with hrhs_def
  have hball_conv : ∀ (S : SmoothCcTensor g₀ 0 2),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R →
      ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤ Cb * R := by
    intro S hSball j hj
    have hsum := hCb S
    rw [hordB] at hsum
    have hterm : ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖ ≤
        ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := by
      refine Finset.single_le_sum (f := fun i => ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖)
        (fun i _ => norm_nonneg _) ?_
      rw [Finset.mem_range]; omega
    calc ‖iteratedCovGrad (I := I) g₀ 0 2 j S‖
        ≤ ∑ i ∈ Finset.range (a + 2 + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 i S‖ := hterm
      _ ≤ Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ := hsum
      _ ≤ Cb * R := mul_le_mul_of_nonneg_left hSball hCb_nn
  have hTcov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ Cb * R :=
    hball_conv T hTball
  have hT'cov : ∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ Cb * R :=
    hball_conv T' hT'ball
  have hcol := hCcol T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTcov hT'cov
  set Dsum : ℝ := ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ with hDsum_def
  have hDsum_nn : 0 ≤ Dsum := Finset.sum_nonneg fun q _ => norm_nonneg _
  have hper : ∀ q ∈ Finset.range (a + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ ≤ Ccol * rhs := by
    intro q hq
    have hqa : q ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hb := hcol q hqa
    rw [← hD_def, ← hrhs_def] at hb
    exact hb
  have hDsum_le : Dsum ≤ ((a : ℝ) + 1) * (Ccol * rhs) := by
    calc Dsum = ∑ q ∈ Finset.range (a + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 q D‖ := hDsum_def
      _ ≤ ∑ _q ∈ Finset.range (a + 1), Ccol * rhs := Finset.sum_le_sum hper
      _ = ((a + 1 : ℕ) : ℝ) * (Ccol * rhs) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ((a : ℝ) + 1) * (Ccol * rhs) := by push_cast; ring
  have hbridgeA := hCa D
  rw [← hDsum_def] at hbridgeA
  have hKcoe : (Real.toNNReal (Ca * (((a : ℝ) + 1) * Ccol)) : ℝ) =
      Ca * (((a : ℝ) + 1) * Ccol) :=
    Real.coe_toNNReal _ (by positivity)
  rw [hKcoe]
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (a : ℝ) D‖
      ≤ Ca * Dsum := hbridgeA
    _ ≤ Ca * (((a : ℝ) + 1) * (Ccol * rhs)) :=
        mul_le_mul_of_nonneg_left hDsum_le hCa_nn
    _ = Ca * (((a : ℝ) + 1) * Ccol) * rhs := by ring

theorem tensorHsInclusion_smoothCcToTensorHs (g₀ : SmoothRiemannianMetric I M)
    {τ σ : ℝ} (hτσ : τ ≤ σ) (T : SmoothCcTensor g₀ 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ
        (smoothCcToTensorHs (I := I) (M := M) g₀ σ T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ τ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHsInclusion_coeff_apply, smoothCcToTensorHs_coeff, smoothCcToTensorHs_coeff]

theorem deTurckSmoothN_ballLipschitz_Ha2 (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
        (K : ℝ) * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  exact hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball

theorem deTurckSmoothN_ballLipschitz_Ha2_dataWeighted_of_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    {R : ℝ} (hR : 0 < R) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ K : ℝ≥0, ∀ (T T' : SmoothCcTensor g₀ 0 2)
      {δ : ℝ} (hδ_le : δ ≤ δ₀)
      (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
      {δ' : ℝ} (hδ'_le : δ' ≤ δ₀)
      (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
      (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
      (hT'symm : ∀ (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀ T' x v w = ccTensorBilin (I := I) g₀ T' x w v),
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R →
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R →
      ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T (lt_of_le_of_lt hδ_le hδ₀) hδ -
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' (lt_of_le_of_lt hδ'_le hδ₀) hδ'‖ ≤
        (K : ℝ) *
          (max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)‖
               ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
                  (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T')‖
             * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
                  smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ +
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
                smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T')‖) := by
  obtain ⟨K, hK⟩ :=
    smoothRemainderDiff_ballLipschitz_Ha1_dataWeighted_of_symm
      (I := I) (M := M) g₀ g_bg a ha_super hR hδ₀
  refine ⟨K, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le hδ₀
  have hδ'_lt : δ' < 1 := lt_of_le_of_lt hδ'_le hδ₀
  have hbase := hK T T' hδ_le hδ hδ'_le hδ' hTsymm hT'symm hTball hT'ball
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g₀ g_bg a T T' hδ_lt hδ hδ'_lt hδ']
  refine le_trans hbase (le_of_eq ?_)
  rw [tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ T,
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ T',
    ← smoothCcToTensorHs_sub (I := I) (M := M) g₀ ((a : ℝ) + 2) T T',
    tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ _ (T - T')]

theorem smoothCcToTensorHs_smul (g₀ : SmoothRiemannianMetric I M) (σ : ℝ) (c : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ σ (c • T) =
      c • smoothCcToTensorHs (I := I) (M := M) g₀ σ T := by
  refine tensorHs.ext ?_
  funext i
  rw [tensorHs.smul_coeff]
  simp only [smoothCcToTensorHs_coeff]
  rw [show SmoothCcTensor.toL2 (c • T) = c • SmoothCcTensor.toL2 T from map_smul _ _ _,
    tensorL2Coeff_smul]

/-- The norm of a scalar multiple in the spectral Sobolev scale: `‖c • x‖ = |c| · ‖x‖`.
The scale is a real normed space through the linear isometry `tensorHs.rescaleEquivL2` onto
weighted `ℓ²`, where scalar multiplication is homogeneous. -/
theorem tensorHs_norm_smul (g₀ : SmoothRiemannianMetric I M) {σ : ℝ} (c : ℝ)
    (x : tensorHs (I := I) (M := M) g₀ 0 2 σ) :
    ‖c • x‖ = |c| * ‖x‖ := by
  have h1 : ‖c • x‖ =
      ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) (c • x)‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map (c • x) |>.symm
  have h2 : ‖tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (σ := σ) x‖ = ‖x‖ :=
    (tensorHs.rescaleEquivL2 (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (σ := σ)).norm_map x
  rw [h1, map_smul, norm_smul, Real.norm_eq_abs, h2]

theorem sobolevBall_smooth_fibreSmall (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ ≤ 1 / 3 ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical

  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ m hm_lossy
  refine ⟨1 / (3 * C), by positivity, 1 / 3, le_refl _, fun T hTball => ?_⟩

  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + 2 := by
      have h2 : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
      push_cast at h2
      linarith [h2]
    exact hcast

  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / (3 * C) :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ 1 / 3 := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (1 / (3 * C)) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = 1 / 3 := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ (1 / 3 : ℝ) * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = 1 / 3 * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

theorem sobolevBall_smooth_fibreSmall_of_threshold (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {θ : ℝ} (hθ_pos : 0 < θ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ δ₀ : ℝ, δ₀ ≤ θ ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ₀ := by
  classical
  set m : ℕ := 2 * Module.finrank ℝ E + 4 with hm_def
  have hm_lossy : 2 * Module.finrank ℝ E + 4 ≤ m := by rw [hm_def]
  have hm_le : (m : ℕ) ≤ a + 2 := by rw [hm_def]; omega
  obtain ⟨C, hC_pos, hC⟩ :=
    ccTensorBilinSymm_gFibreOpBound_le_spectral_lossy (I := I) (M := M) g₀ m hm_lossy
  refine ⟨θ / C, by positivity, θ, le_refl _, fun T hTball => ?_⟩
  have hmono : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ := by
    have hembed_m : smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T =
        ccSpectralEmbed (I := I) (M := M) g₀ (m : ℝ) T :=
      tensorHs.ext (funext (fun i => rfl))
    have hembed_a2 : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
        ccSpectralEmbed (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
      tensorHs.ext (funext (fun i => rfl))
    rw [hembed_m, hembed_a2]
    refine ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ ?_ T
    have hcast : (m : ℝ) ≤ (a : ℝ) + (2 : ℕ) := by exact_mod_cast hm_le
    push_cast at hcast
    linarith [hcast]
  intro x v w
  have hlossy := hC T x v w
  have hNm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ θ / C :=
    le_trans hmono hTball
  have hsv_nn : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
  have hsw_nn : 0 ≤ Real.sqrt (g₀.inner x w w) := Real.sqrt_nonneg _
  have hmul_nn : 0 ≤ Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) :=
    mul_nonneg hsv_nn hsw_nn
  refine hlossy.trans ?_
  have hCN_le : C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖ ≤ θ := by
    calc C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖
        ≤ C * (θ / C) := mul_le_mul_of_nonneg_left hNm_le hC_pos.le
      _ = θ := by field_simp
  calc (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
        Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)
      = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ) T‖) *
          (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
    _ ≤ θ * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) :=
        mul_le_mul_of_nonneg_right hCN_le hmul_nn
    _ = θ * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by ring

theorem deTurckSmoothN_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by

  set δ₀ : ℝ := max δ δ' with hδ₀_def
  have hδ₀ : δ₀ < 1 := by rw [hδ₀_def]; exact max_lt hδ_lt hδ'_lt
  have hδ_le : δ ≤ δ₀ := by rw [hδ₀_def]; exact le_max_left _ _
  have hδ'_le : δ' ≤ δ₀ := by rw [hδ₀_def]; exact le_max_right _ _
  set R : ℝ := max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ + 1 with hR_def
  have hR_pos : 0 < R := by
    have : (0 : ℝ) ≤ max ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ :=
      le_trans (norm_nonneg _) (le_max_left _ _)
    rw [hR_def]; linarith
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR_pos hδ₀
  have hTball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R := by
    rw [hR_def]; linarith [le_max_left ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hT'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ ≤ R := by
    rw [hR_def]; linarith [le_max_right ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖]
  have hbound := hK T T' hδ_le hδ hδ'_le hδ' hTball hT'ball
  rw [hTT', sub_self, norm_zero, mul_zero] at hbound
  have hzero : ‖deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ -
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ'‖ = 0 :=
    le_antisymm hbound (norm_nonneg _)
  rw [norm_eq_zero, sub_eq_zero] at hzero
  exact hzero

/-- **The radial scaling of a smooth `(0,2)`-tensor into the spectral `H^{a+2}` ball of radius
`R₀`.**  The smooth tensor `T` is multiplied by `min 1 (R₀ / ‖ι(a+2) T‖)`, which is `≤ 1` and
contracts `T` so that its order-`(a+2)` embedding has norm `≤ R₀`, while leaving it unchanged
when it already lies in the ball. -/
def radialScaleSmooth (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) : SmoothCcTensor g₀ 0 2 :=
  (min 1 (R₀ / ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖)) • T

/-- The radial scaling lands in the `H^{a+2}` ball of radius `R₀` (for `0 ≤ R₀`): its order-`(a+2)`
embedding has norm `≤ R₀`. -/
theorem norm_smoothCcToTensorHs_radialScaleSmooth_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T)‖ ≤ R₀ := by
  set n := ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have hcnn : 0 ≤ min 1 (R₀ / n) := le_min zero_le_one (div_nonneg hR₀ hn0)
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, tensorHs_norm_smul, abs_of_nonneg hcnn]
  rcases eq_or_lt_of_le hn0 with heq | hpos
  · rw [← heq]; simpa using hR₀
  · have hmin_le : min 1 (R₀ / n) ≤ R₀ / n := min_le_right _ _
    calc min 1 (R₀ / n) * n ≤ (R₀ / n) * n :=
          mul_le_mul_of_nonneg_right hmin_le hn0
      _ = R₀ := by field_simp

/-- The order-`(a+2)` embedding of the radial scaling of `T` is the **ball retraction** of the
embedding of `T`: `ι(a+2) (radialScaleSmooth R₀ T) = ballRetraction R₀ (ι(a+2) T)`.  Both sides
are `(min 1 (R₀ / ‖ι T‖)) • ι T`, since the embedding is `ℝ`-homogeneous
(`smoothCcToTensorHs_smul`) and norm-multiplicative (`tensorHs_norm_smul`). -/
theorem smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ) (R₀ : ℝ) (T : SmoothCcTensor g₀ 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ T) =
      ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
  rw [radialScaleSmooth, smoothCcToTensorHs_smul, ballRetraction]

open Classical in
/-- **The total continuous Ricci–DeTurck nonlinearity at the quasilinear `H^{a+2}` order.**

  `N : tensorHs g₀ 0 2 ((a : ℝ) + 2) → tensorHs g₀ 0 2 (a : ℝ)`.

`deTurckSobolevNHa2` is the **total, continuous, non-gated** quasilinear Ricci–DeTurck
nonlinearity on the spectral Sobolev scale.  It is built by **dense Lipschitz extension** of the
genuine smooth-input nonlinearity `deTurckSmoothN`:

* `deTurckSmoothN` is `H^{a+2}`-ball-Lipschitz on smooth fibre-small data
  (`deTurckSmoothN_ballLipschitz_Ha2`), hence uniformly continuous on the **realizability ball**
  `closedBall (0 : H^{a+2}) R₀` where every smooth datum is fibre-small
  (`sobolevBall_smooth_fibreSmall`), in whose dense smooth subset (`smoothCcToTensorHs_denseRange`)
  it lives;
* the codomain `H^a` is complete (`tensorHs.instCompleteSpace`), so the uniformly continuous map
  extends to the closure (`Dense.extend`);
* the **recentred radial retraction** `recenteredBallRetraction 0 R₀` (1-Lipschitz, sorry-free,
  `LocallyLipschitzTruncation.lean`) maps **all** of `H^{a+2}` into the realizability ball, making
  the composite total.

The dense-subset value reads off `deTurckSmoothN` of the radial scaling
(`radialScaleSmooth`) of a chosen smooth representative into the realizability ball, well-defined
on the embedded image by `deTurckSmoothN_embedding_wellDefined`.  It carries no `realizeMetricAt`
/ finite-support / HLCC gate, and on smooth fibre-small in-ball data equals the genuine intrinsic
remainder `deTurckSmoothN` (`deTurckSobolevNHa2_eq_smoothN`). -/
def deTurckSobolevNHa2 (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (Classical.choose x.2))
            (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le (Classical.choose x.2))))
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
          (Classical.choose h).1 v)
    else 0

/-- The realizability existence holds under the supercritical hypothesis `ha_super`: this is the
`∃ p`-witness that drives the `then` branch of `deTurckSobolevNHa2`. -/
theorem deTurckSobolevNHa2_exists_of_super (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
        gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 := by
  obtain ⟨R₀, hR₀, δ₀, hδ₀_le, hball⟩ :=
    sobolevBall_smooth_fibreSmall_of_threshold (I := I) (M := M) g₀ a ha_super
      (deTurckArmContractionThreshold''_pos (Module.finrank ℝ E))
  exact ⟨(R₀, δ₀), hR₀, hδ₀_le, hball⟩

/-- **`deTurckSobolevNHa2` is globally Lipschitz** (under the supercritical order).

The dense-subset function is Lipschitz **in the embedding coordinate**: on the realizability
ball both radial scalings are fibre-small, so `deTurckSmoothN_ballLipschitz_Ha2` controls their
nonlinearity difference by `K` times the `H^{a+2}`-distance of their embeddings, which are the
ball retractions of the underlying points (`smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction`)
and hence `1`-Lipschitz in the point (`lipschitzWith_ballRetraction`).  The dense extension is the
continuous map agreeing with this `K`-Lipschitz function on the dense range, so it is `K`-Lipschitz
on the closure `= univ` (`LipschitzOnWith.closure`); precomposing with the `1`-Lipschitz recentred
retraction keeps the constant. -/
theorem deTurckSobolevNHa2_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀
      hδ₀_lt

  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def

  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]

  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg

  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous

  have hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous

  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl

  refine ⟨K, ?_⟩
  have hretr : LipschitzWith 1 (recenteredBallRetraction
      (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) :=
    recenteredBallRetraction_lipschitzWith hR₀.le _
  have hcomp : LipschitzWith (K * 1)
      ((Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀)) :=
    hext_lip.comp hretr
  rw [mul_one] at hcomp
  have heq_fun : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a =
      (Dense.extend hdense F) ∘ (recenteredBallRetraction
        (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀) := by
    funext v
    rw [deTurckSobolevNHa2]
    rw [dif_pos h]
    rfl
  rw [heq_fun]
  exact hcomp

/-- **The total nonlinearity `deTurckSobolevNHa2` is locally Lipschitz on any engine ball.**

For the Ha2 quasilinear maximal-regularity contraction, the nonlinearity must be Lipschitz on the
closed `H^{a+2}`-ball about the initial datum.  Since `deTurckSobolevNHa2` is **globally**
Lipschitz (`deTurckSobolevNHa2_lipschitzWith`), it is Lipschitz on every closed ball — in
particular on `closedBall u₀ R` about any `H^{a+2}`-datum `u₀` and radius `R`. -/
theorem deTurckSobolevNHa2_lipschitzOnWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (R : ℝ) (u₀ : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) :
    ∃ L_R : ℝ≥0, LipschitzOnWith L_R (deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a)
      (Metric.closedBall u₀ R) := by
  obtain ⟨K, hK⟩ := deTurckSobolevNHa2_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  exact ⟨K, hK.lipschitzOnWith⟩

/-- **`deTurckSobolevNHa2` is the genuine smooth nonlinearity on smooth fibre-small in-ball
inputs.**

On the spectral image `smoothCcToTensorHs g₀ (a+2) T` of a smooth fibre-small `T` whose embedding
lies in **the realizability ball** the construction uses (`hball : ‖ι T‖ ≤ R₀`, with `(R₀, δ₀)`
the realizability witness selected inside `deTurckSobolevNHa2` —
`deTurckSobolevNHa2_realizability`), the total nonlinearity equals
`deTurckSmoothN g₀ g_bg a T hδ_lt hδ` (`= deTurckRicciRHS g_bg (g₀ + T) − Δ_∇ T`).  This pins
`deTurckSobolevNHa2` to the **genuine intrinsic Ricci–DeTurck remainder** on the dense smooth
in-ball subset — the non-vacuity / flow-faithfulness guarantee.

The recentred retraction fixes the in-ball point, the dense extension reads off `F` there
(`Dense.extend_eq`), and `F`'s value is `deTurckSmoothN` of the radial scaling of a chosen smooth
representative whose embedding is the (identity, in-ball) ball retraction of `ι T`; the genuine
value is recovered by the embedding-well-definedness `deTurckSmoothN_embedding_wellDefined`. -/
theorem deTurckSobolevNHa2_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))

  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2) with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
        (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le (Classical.choose x.2))) with hF_def

  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀
      hδ₀_lt
  have hembed : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) =
          ballRetraction R₀ (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec x.2]
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose y.2))‖ := hbound
      _ = (K : ℝ) * ‖ballRetraction R₀
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            ballRetraction R₀ (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [hembed x, hembed y]
      _ ≤ (K : ℝ) * ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
            (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg

  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T)) := by
    rw [deTurckSobolevNHa2, dif_pos h]

  have hfix : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T := by
    refine recenteredBallRetraction_eq_self_of_mem ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hball
  rw [hunfold, hfix, hdense.extend_eq hF_cont ⟨_, hmem⟩]

  change deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀ (Classical.choose hmem)) _ _ =
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super _ T _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, Classical.choose_spec hmem]
  exact ballRetraction_eq_self_of_mem hball

theorem deTurckSobolevNHa2_smoothEmbed_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2) :
    deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a
          (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1 T)
        (lt_of_le_of_lt (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
            (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
              (I := I) (M := M) g₀ a ha_super)).1.le T)) := by
  classical
  set h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super with hh
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  set S := radialScaleSmooth (I := I) (M := M) g₀ a R₀ T with hS_def
  have hSball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ :=
    norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le T
  have hSfibre := (Classical.choose_spec h).2.2 _ hSball
  have hSeq : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) =
        deTurckSmoothN (I := I) (M := M) g₀ g_bg a S
          (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
          hSfibre :=
    deTurckSobolevNHa2_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super S
      (lt_of_le_of_lt (Classical.choose_spec h).2.1 (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
      hSfibre hSball
  have hbr : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S =
      recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    rw [hS_def, smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
      recenteredBallRetraction, sub_zero, zero_add]
  have hSmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S ∈
      Metric.closedBall (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀ := by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hSball
  have hrecS : recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) =
        recenteredBallRetraction (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) R₀
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    rw [recenteredBallRetraction_eq_self_of_mem hSmem, hbr]
  have hNeq : deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
        deTurckSobolevNHa2 (I := I) (M := M) g₀ g_bg a
          (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S) := by
    rw [deTurckSobolevNHa2, deTurckSobolevNHa2, dif_pos h, dif_pos h, hrecS]
  rw [hNeq, hSeq]

theorem ccTensorBilinSymm_symmS_apply (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x v w =
      ccTensorBilinSymm (I := I) g₀ T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_symm (I := I) g₀ T x w v, ccTensorBilinSymm_apply]
  ring

theorem gFibreOpBound_symmS (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ) :
    gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ := by
  intro x v w
  rw [ccTensorBilinSymm_symmS_apply (I := I) (M := M) g₀ T x v w]
  exact hδ x v w

theorem ccTensorBilin_symmS_symm' (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x v w =
      ccTensorBilin (I := I) g₀ (symmS (I := I) (M := M) g₀ T) x w v := by
  rw [ccTensorBilin_symmS, ccTensorBilin_symmS, ccTensorBilinSymm_symm]

theorem norm_iteratedCovGrad_domDomCongrSection (g₀ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 2)) (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ_def
  have hbridge : ∀ (W : SmoothCcTensor g₀ 0 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 k W‖ ^ 2 =
        ∫ x, riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k W).toSection x) ∂μ := by
    intro W
    rw [SmoothCcTensor.norm_def (I := I) (M := M) (iteratedCovGrad (I := I) g₀ 0 2 k W), hμ_def]
    exact tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq (I := I) (M := M) g₀ (2 + k)
      (iteratedCovGrad (I := I) g₀ 0 2 k W)
  have hintegrand : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k
            (domDomCongrSection (I := I) g₀ σ T)).toSection x) =
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + k) x
          ((iteratedCovGrad (I := I) g₀ 0 2 k T).toSection x) := fun x =>
    riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection
      (I := I) (M := M) g₀ (s := 2) σ T k x
  have hsq : ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ ^ 2 =
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ ^ 2 := by
    rw [hbridge (domDomCongrSection (I := I) g₀ σ T), hbridge T]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hintegrand)
  have hnnA : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k (domDomCongrSection (I := I) g₀ σ T)‖ :=
    norm_nonneg _
  have hnnB : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  exact (sq_eq_sq₀ hnnA hnnB).mp hsq

theorem norm_iteratedCovGrad_symmS_le (g₀ : SmoothRiemannianMetric I M)
    (T : SmoothCcTensor g₀ 0 2) (k : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T)‖ ≤
      ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := by
  classical
  set Tsw : SmoothCcTensor g₀ 0 2 :=
    domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) T with hTsw_def
  have hiter_eq : iteratedCovGrad (I := I) g₀ 0 2 k (symmS (I := I) (M := M) g₀ T) =
      (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k T +
        (1 / 2 : ℝ) • iteratedCovGrad (I := I) g₀ 0 2 k Tsw := by
    rw [hTsw_def]; exact iteratedCovGrad_symmS_eq (I := I) g₀ T k
  rw [hiter_eq]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_smul, norm_smul]
  have habs : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by rw [Real.norm_eq_abs]; norm_num
  rw [habs, hTsw_def,
    norm_iteratedCovGrad_domDomCongrSection (I := I) (M := M) g₀ (Equiv.swap (0 : Fin 2) 1) T k]
  have hnn : 0 ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 k T‖ := norm_nonneg _
  linarith

theorem exists_norm_smoothCcToTensorHs_symmS_le (g₀ : SmoothRiemannianMetric I M) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) (symmS (I := I) (M := M) g₀ T)‖ ≤
        C * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g₀ n
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g₀ n
  refine ⟨Ca * Cb, mul_nonneg hCa_nn hCb_nn, fun T => ?_⟩
  have h1 := hCa (symmS (I := I) (M := M) g₀ T)
  have hterm : ∑ j ∈ Finset.range (n + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ ≤
      ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
    Finset.sum_le_sum fun j _ => norm_iteratedCovGrad_symmS_le (I := I) (M := M) g₀ T j
  have h2 := hCb T
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) (symmS (I := I) (M := M) g₀ T)‖
      ≤ Ca * ∑ j ∈ Finset.range (n + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 j (symmS (I := I) (M := M) g₀ T)‖ := h1
    _ ≤ Ca * ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ :=
        mul_le_mul_of_nonneg_left hterm hCa_nn
    _ ≤ Ca * (Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖) :=
        mul_le_mul_of_nonneg_left h2 hCa_nn
    _ = Ca * Cb * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by ring

theorem symmS_eq_self_of_ccTensorBilin_symm (g₀ : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2)
    (hsymm : ∀ (x : M) (u w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ S x u w = ccTensorBilin (I := I) g₀ S x w u) :
    symmS (I := I) (M := M) g₀ S = S := by
  have hswap : domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1) S = S := by
    refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀ (fun x => ?_)
    rw [domDomCongrSection_unitModel]
    refine ContinuousMultilinearMap.ext (fun v => ?_)
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : ∀ u w : TangentSpace I x,
        unitModel (I := I) (M := M) g₀ 2 S x ![u, w] =
          unitModel (I := I) (M := M) g₀ 2 S x ![w, u] := by
      intro u w
      rw [unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x u w,
        unitModel_eq_ccTensorBilin_local (I := I) (M := M) g₀ S x w u]
      exact hsymm x u w
    have hveta : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext i
      fin_cases i <;> rfl
    have hveta' : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hveta]
    conv_rhs => rw [hveta']
    exact hv (v 1) (v 0)
  have htwo : S + S = (2 : ℝ) • S := (two_smul ℝ S).symm
  rw [symmS, hswap, htwo, smul_smul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]

open Classical in

def deTurckSobolevNHa2Symm (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ) :
    tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
  fun v =>
    if h : ∃ p : ℝ × ℝ, 0 < p.1 ∧ p.2 ≤ deTurckArmContractionThreshold'' (Module.finrank ℝ E) ∧
        ∀ (T : SmoothCcTensor g₀ 0 2),
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ p.1 →
          gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) p.2 then
      Dense.extend (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2))
        (fun x =>
          deTurckSmoothN (I := I) (M := M) g₀ g_bg a
            (radialScaleSmooth (I := I) (M := M) g₀ a (Classical.choose h).1
              (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
            (lt_of_le_of_lt (Classical.choose_spec h).2.1
              (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
            ((Classical.choose_spec h).2.2 _
              (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
                g₀ a (Classical.choose_spec h).1.le
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))))
        v
    else 0

theorem deTurckSmoothN_symm_embedding_wellDefined (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T')) δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a (symmS (I := I) (M := M) g₀ T) hδ_lt hδ =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a (symmS (I := I) (M := M) g₀ T') hδ'_lt hδ' := by
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (symmS (I := I) (M := M) g₀ T) (symmS (I := I) (M := M) g₀ T') hδ_lt hδ hδ'_lt hδ' ?_
  obtain ⟨Csym, hCsym_nn, hCsym⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 2)
  have hcast : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  have hkey := hCsym (T - T')
  rw [hcast] at hkey
  have hzero_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ (T - T'))‖ ≤ 0 := by
    calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ (T - T'))‖
        ≤ Csym * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ := hkey
      _ = Csym * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T'‖ := by
          rw [smoothCcToTensorHs_sub]
      _ = 0 := by rw [hTT', sub_self, norm_zero, mul_zero]
  have hzero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ (T - T')) = 0 := by
    have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ (T - T'))‖ = 0 :=
      le_antisymm hzero_le (norm_nonneg _)
    rwa [norm_eq_zero] at h0
  have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ T) -
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ T') = 0 := by
    rw [← smoothCcToTensorHs_sub, ← symmS_sub]
    exact hzero
  exact sub_eq_zero.mp hsub

set_option maxHeartbeats 800000 in
theorem deTurckSobolevNHa2Symm_lipschitzWith (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ K : ℝ≥0, LipschitzWith K (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hembed_rs : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) =
          ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) := by
    intro x
    rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
  have hF_lip : ∀ x y : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      ‖F x - F y‖ ≤ (K : ℝ) *
        ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) - (y : _)‖ := by
    intro x y
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [hembed_rs x, hembed_rs y]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀
                (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hlipF : LipschitzWith K F := by
    refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    exact hF_lip x y
  have hF_cont : Continuous F := hlipF.continuous
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  have hext_eq : ∀ x : Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)),
      Dense.extend hdense F (x : _) = F x := fun x => hdense.extend_eq hF_cont x
  have hext_cont : Continuous (Dense.extend hdense F) :=
    (hdense.uniformContinuous_extend hlipF.uniformContinuous).continuous
  have hext_lip_s : LipschitzOnWith K (Dense.extend hdense F)
      (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) := by
    refine lipschitzOnWith_iff_dist_le_mul.mpr (fun p hp q hq => ?_)
    obtain ⟨xp, hxp⟩ := hp
    obtain ⟨xq, hxq⟩ := hq
    have hep : Dense.extend hdense F p = F ⟨p, ⟨xp, hxp⟩⟩ := by
      have := hext_eq ⟨p, ⟨xp, hxp⟩⟩; simpa using this
    have heq : Dense.extend hdense F q = F ⟨q, ⟨xq, hxq⟩⟩ := by
      have := hext_eq ⟨q, ⟨xq, hxq⟩⟩; simpa using this
    rw [dist_eq_norm, hep, heq, dist_eq_norm]
    exact hF_lip ⟨p, ⟨xp, hxp⟩⟩ ⟨q, ⟨xq, hxq⟩⟩
  have hext_lip : LipschitzWith K (Dense.extend hdense F) := by
    have hcl : LipschitzOnWith K (Dense.extend hdense F)
        (closure (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)))) :=
      hext_lip_s.closure (hext_cont.continuousOn)
    rw [hdense.closure_range] at hcl
    rwa [lipschitzOnWith_univ] at hcl
  refine ⟨K, ?_⟩
  have heq_fun : deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a =
      Dense.extend hdense F := by
    funext v
    show (dite _ _ _) = _
    rw [dif_pos h]
  rw [heq_fun]
  exact hext_lip

theorem deTurckSobolevNHa2Symm_eq_smoothN (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ (symmS (I := I) (M := M) g₀ T)) δ)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (symmS (I := I) (M := M) g₀ T) hδ_lt hδ := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
              smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀
                  (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    show (dite _ _ _) = _
    rw [dif_pos h]
  rw [hunfold, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  change deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem))) _ _ =
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a (symmS (I := I) (M := M) g₀ T) hδ_lt hδ
  have hchoose : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (Classical.choose hmem) = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
    Classical.choose_spec hmem
  have hsymm_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ (Classical.choose hmem)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ T) := by
    have hdiff_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (Classical.choose hmem - T) = 0 := by
      rw [smoothCcToTensorHs_sub, hchoose, sub_self]
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ ≤ 0 := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖
          ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose hmem - T)‖ :=
            norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _
        _ = 0 := by rw [hdiff_zero, norm_zero]
    have hsymm_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T)) = 0 := by
      have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ = 0 :=
        le_antisymm hnorm_le (norm_nonneg _)
      rwa [norm_eq_zero] at h0
    have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ (Classical.choose hmem)) -
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T) = 0 := by
      rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      exact hsymm_zero
    exact sub_eq_zero.mp hsub
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (symmS (I := I) (M := M) g₀ (Classical.choose hmem)))
    (symmS (I := I) (M := M) g₀ T) _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, hsymm_eq]
  refine ballRetraction_eq_self_of_mem ?_
  calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ T)‖
      ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ :=
        norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) T
    _ ≤ R₀ := hball

theorem deTurckSobolevNHa2Symm_smoothEmbed_eq (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2) :
    deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a
          (Classical.choose (deTurckSobolevNHa2_exists_of_super
            (I := I) (M := M) g₀ a ha_super)).1
          (symmS (I := I) (M := M) g₀ T))
        (lt_of_le_of_lt (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.1
          (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)))
        ((Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
          (I := I) (M := M) g₀ a ha_super)).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a
            (Classical.choose_spec (deTurckSobolevNHa2_exists_of_super
              (I := I) (M := M) g₀ a ha_super)).1.le
            (symmS (I := I) (M := M) g₀ T))) := by
  classical
  have h := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super
  set R₀ := (Classical.choose h).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec h).1
  have hδ₀_lt : (Classical.choose h).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec h).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2 (I := I) (M := M) g₀ g_bg a ha_super hR₀ hδ₀_lt
  set hdense := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
    with hdense_def
  set F : (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2))) →
      tensorHs (I := I) (M := M) g₀ 0 2 (a : ℝ) :=
    fun x =>
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a
        (radialScaleSmooth (I := I) (M := M) g₀ a R₀
          (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
        hδ₀_lt
        ((Classical.choose_spec h).2.2 _
          (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M)
            g₀ a hR₀.le
            (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))) with hF_def
  have hF_cont : Continuous F := by
    refine (LipschitzWith.of_dist_le_mul (K := K) (fun x y => ?_)).continuous
    rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
    have hbound := hK
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (le_refl _)
      ((Classical.choose_spec h).2.2 _
        (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _))
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
      (norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le _)
    calc ‖F x - F y‖ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (radialScaleSmooth (I := I) (M := M) g₀ a R₀
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := hbound
      _ = (K : ℝ) *
            ‖ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose x.2))) -
              ballRetraction R₀
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))‖ := by
            rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
              smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2))‖ := by
            have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
              g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose x.2)))
              (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (Classical.choose y.2)))
            rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
            exact mul_le_mul_of_nonneg_left hlip K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀
                  (Classical.choose x.2 - Classical.choose y.2))‖ := by
            rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      _ ≤ (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2 - Classical.choose y.2)‖ :=
            mul_le_mul_of_nonneg_left
              (norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _)
              K.coe_nonneg
      _ = (K : ℝ) *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose x.2) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (Classical.choose y.2)‖ := by
            rw [smoothCcToTensorHs_sub]
      _ = (K : ℝ) *
            ‖(x : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) -
              (y : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2))‖ := by
            rw [Classical.choose_spec x.2, Classical.choose_spec y.2]
  have hmem : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T ∈
      Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) := ⟨T, rfl⟩
  have hunfold : deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
      (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      Dense.extend hdense F
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) := by
    show (dite _ _ _) = _
    rw [dif_pos h]
  rw [hunfold, hdense.extend_eq hF_cont ⟨_, hmem⟩]
  change deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem))) _ _ =
    deTurckSmoothN (I := I) (M := M) g₀ g_bg a
      (radialScaleSmooth (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ T)) _ _
  have hchoose : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (Classical.choose hmem) = smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T :=
    Classical.choose_spec hmem
  have hsymm_eq : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ (Classical.choose hmem)) =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
      (symmS (I := I) (M := M) g₀ T) := by
    have hdiff_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (Classical.choose hmem - T) = 0 := by
      rw [smoothCcToTensorHs_sub, hchoose, sub_self]
    have hnorm_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ ≤ 0 := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖
          ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (Classical.choose hmem - T)‖ :=
            norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ ((a : ℝ) + 2) _
        _ = 0 := by rw [hdiff_zero, norm_zero]
    have hsymm_zero : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T)) = 0 := by
      have h0 : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ (Classical.choose hmem - T))‖ = 0 :=
        le_antisymm hnorm_le (norm_nonneg _)
      rwa [norm_eq_zero] at h0
    have hsub : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ (Classical.choose hmem)) -
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T) = 0 := by
      rw [← smoothCcToTensorHs_sub, ← symmS_sub]
      exact hsymm_zero
    exact sub_eq_zero.mp hsub
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (symmS (I := I) (M := M) g₀ (Classical.choose hmem)))
    (radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (symmS (I := I) (M := M) g₀ T)) _ _ _ _ ?_
  rw [smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction,
    smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction, hsymm_eq]

theorem deTurckSobolevNHa2Symm_eq_smoothN_of_symm (g₀ g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a)
    (T : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hTsymm : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g₀ T x v w = ccTensorBilin (I := I) g₀ T x w v)
    (hball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤
      (Classical.choose (deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super)).1) :
    deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T) =
      deTurckSmoothN (I := I) (M := M) g₀ g_bg a T hδ_lt hδ := by
  have hEq : symmS (I := I) (M := M) g₀ T = T :=
    symmS_eq_self_of_ccTensorBilin_symm (I := I) (M := M) g₀ T hTsymm
  have h1 := deTurckSobolevNHa2Symm_eq_smoothN (I := I) (M := M) g₀ g_bg a ha_super T hδ_lt
    (gFibreOpBound_symmS (I := I) (M := M) g₀ T hδ) hball
  rw [h1]
  refine deTurckSmoothN_embedding_wellDefined (I := I) (M := M) g₀ g_bg a ha_super
    (symmS (I := I) (M := M) g₀ T) T hδ_lt (gFibreOpBound_symmS (I := I) (M := M) g₀ T hδ)
    hδ_lt hδ ?_
  rw [hEq]

theorem deTurckSobolevNHa2Symm_mixed_lipschitz_pointwise_aux
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) :
    ∃ C₁ C₂ : ℝ≥0, ∀ (u u' : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
      ‖deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a u -
          deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a u'‖ ≤
        (C₁ : ℝ) * max ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u‖
                       ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                          (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) u'‖
          * ‖u - u'‖ +
        (C₂ : ℝ) * ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                      (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith) (u - u')‖ := by
  classical
  set hex := deTurckSobolevNHa2_exists_of_super (I := I) (M := M) g₀ a ha_super with hhex
  set R₀ := (Classical.choose hex).1 with hR₀_def
  have hR₀ : 0 < R₀ := (Classical.choose_spec hex).1
  have hδ₀_lt : (Classical.choose hex).2 < 1 :=
    lt_of_le_of_lt (Classical.choose_spec hex).2.1
      (deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E))
  set hτσ : (a : ℝ) + 1 ≤ (a : ℝ) + 2 := by linarith with hτσ_def
  set J := tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2) hτσ with hJ_def
  obtain ⟨Csym1, hCsym1_nn, hCsym1⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 1)
  obtain ⟨Csym2, hCsym2_nn, hCsym2⟩ :=
    exists_norm_smoothCcToTensorHs_symmS_le (I := I) (M := M) g₀ (a + 2)
  have hcast1 : ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by push_cast; ring
  have hcast2 : ((a + 2 : ℕ) : ℝ) = (a : ℝ) + 2 := by push_cast; ring
  have hCsym1' : ∀ W : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
          (symmS (I := I) (M := M) g₀ W)‖ ≤
        Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) W‖ := by
    intro W
    have hW := hCsym1 W
    rw [hcast1] at hW
    exact hW
  have hCsym2' : ∀ W : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ W)‖ ≤
        Csym2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W‖ := by
    intro W
    have hW := hCsym2 W
    rw [hcast2] at hW
    exact hW
  have hRbig : 0 < (Csym2 + 1) * R₀ := mul_pos (by linarith) hR₀
  obtain ⟨K, hK⟩ :=
    deTurckSmoothN_ballLipschitz_Ha2_dataWeighted_of_symm (I := I) (M := M) g₀ g_bg a ha_super
      hRbig hδ₀_lt
  have hRinv_nn : (0 : ℝ) ≤ 1 / R₀ := by positivity
  set C₂ : ℝ≥0 := K * Real.toNNReal Csym1 with hC₂_def
  set C₁ : ℝ≥0 := K * Real.toNNReal Csym1 * Real.toNNReal Csym2 +
    K * Real.toNNReal Csym1 * Real.toNNReal Csym2 * Real.toNNReal (1 / R₀) with hC₁_def
  have hC₂coe : (C₂ : ℝ) = (K : ℝ) * Csym1 := by
    rw [hC₂_def]
    push_cast
    rw [Real.coe_toNNReal _ hCsym1_nn]
  have hC₁coe : (C₁ : ℝ) =
      (K : ℝ) * Csym1 * Csym2 + (K : ℝ) * Csym1 * Csym2 * (1 / R₀) := by
    rw [hC₁_def]
    push_cast
    rw [Real.coe_toNNReal _ hCsym1_nn, Real.coe_toNNReal _ hCsym2_nn,
      Real.coe_toNNReal _ hRinv_nn]
  refine ⟨C₁, C₂, ?_⟩
  set D := Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)) with hD_def
  have hDdense : Dense D := smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ ((a : ℝ) + 2)
  set lhs : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) ×
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) → ℝ :=
    fun p => ‖deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a p.1 -
      deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a p.2‖ with hlhs_def
  set rhs : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) ×
      tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2) → ℝ :=
    fun p => (C₁ : ℝ) * max ‖J p.1‖ ‖J p.2‖ * ‖p.1 - p.2‖ +
      (C₂ : ℝ) * ‖J (p.1 - p.2)‖ with hrhs_def
  obtain ⟨KN, hKN⟩ := deTurckSobolevNHa2Symm_lipschitzWith (I := I) (M := M) g₀ g_bg a ha_super
  have hNcont : Continuous (deTurckSobolevNHa2Symm (I := I) (M := M) g₀ g_bg a) :=
    hKN.continuous
  have hlhs_cont : Continuous lhs := by
    rw [hlhs_def]
    exact ((hNcont.comp continuous_fst).sub (hNcont.comp continuous_snd)).norm
  have hrhs_cont : Continuous rhs := by
    rw [hrhs_def]
    refine Continuous.add ?_ ?_
    · refine (Continuous.mul ?_ ?_)
      · exact continuous_const.mul (((J.continuous.comp continuous_fst).norm).max
          ((J.continuous.comp continuous_snd).norm))
      · exact (continuous_fst.sub continuous_snd).norm
    · exact continuous_const.mul ((J.continuous.comp (continuous_fst.sub continuous_snd)).norm)
  have hclosed : IsClosed {p | lhs p ≤ rhs p} := isClosed_le hlhs_cont hrhs_cont
  have hsmooth : ∀ (T T' : SmoothCcTensor g₀ 0 2),
      lhs (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T,
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') ≤
      rhs (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T,
        smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') := by
    intro T T'
    have hccBilin_smul : ∀ (c : ℝ) (X : SmoothCcTensor g₀ 0 2)
        (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀ (c • X) x v w =
          c * ccTensorBilin (I := I) g₀ X x v w := by
      intros c X x v w
      rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    have hRSSsymm : ∀ (Y : SmoothCcTensor g₀ 0 2)
        (x : M) (v w : TangentSpace I x),
        ccTensorBilin (I := I) g₀
            (radialScaleSmooth (I := I) (M := M) g₀ a R₀
              (symmS (I := I) (M := M) g₀ Y)) x v w =
          ccTensorBilin (I := I) g₀
            (radialScaleSmooth (I := I) (M := M) g₀ a R₀
              (symmS (I := I) (M := M) g₀ Y)) x w v := by
      intros Y x v w
      show ccTensorBilin (I := I) g₀ (_ • symmS (I := I) (M := M) g₀ Y) x v w =
          ccTensorBilin (I := I) g₀ (_ • symmS (I := I) (M := M) g₀ Y) x w v
      rw [hccBilin_smul, hccBilin_smul,
        ccTensorBilin_symmS_symm' (I := I) (M := M) g₀ Y x v w]
    set S := radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (symmS (I := I) (M := M) g₀ T) with hS_def
    set S' := radialScaleSmooth (I := I) (M := M) g₀ a R₀
      (symmS (I := I) (M := M) g₀ T') with hS'_def
    have hSball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ :=
      norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le
        (symmS (I := I) (M := M) g₀ T)
    have hS'ball : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ R₀ :=
      norm_smoothCcToTensorHs_radialScaleSmooth_le (I := I) (M := M) g₀ a hR₀.le
        (symmS (I := I) (M := M) g₀ T')
    have hSfibre := (Classical.choose_spec hex).2.2 _ hSball
    have hS'fibre := (Classical.choose_spec hex).2.2 _ hS'ball
    have hSballBig : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤
        (Csym2 + 1) * R₀ := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S‖ ≤ R₀ := hSball
        _ ≤ (Csym2 + 1) * R₀ := by nlinarith [hCsym2_nn, hR₀.le]
    have hS'ballBig : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤
        (Csym2 + 1) * R₀ := by
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ R₀ := hS'ball
        _ ≤ (Csym2 + 1) * R₀ := by nlinarith [hCsym2_nn, hR₀.le]
    have hNT := deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super T
    have hNT' := deTurckSobolevNHa2Symm_smoothEmbed_eq (I := I) (M := M) g₀ g_bg a ha_super T'
    have hbase := hK S S' (le_refl _) hSfibre (le_refl _) hS'fibre
      (hRSSsymm T) (hRSSsymm T') hSballBig hS'ballBig
    have hSembed : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S =
        ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T)) :=
      smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ T)
    have hS'embed : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S' =
        ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T')) :=
      smoothCcToTensorHs_radialScaleSmooth_eq_ballRetraction (I := I) (M := M) g₀ a R₀
        (symmS (I := I) (M := M) g₀ T')
    simp only [hlhs_def, hrhs_def]
    rw [hNT, hNT']
    refine le_trans hbase ?_
    set p := smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T with hp_def
    set p' := smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T' with hp'_def
    have hJembed : ∀ W : SmoothCcTensor g₀ 0 2,
        J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) W) =
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) W := by
      intro W
      rw [hJ_def]
      exact tensorHsInclusion_smoothCcToTensorHs (I := I) (M := M) g₀ hτσ W
    have hJscale : ∀ (q : tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)),
        ‖J (ballRetraction R₀ q)‖ ≤ ‖J q‖ := by
      intro q
      rw [ballRetraction, map_smul, norm_smul, Real.norm_eq_abs]
      have hfac_nn : 0 ≤ min 1 (R₀ / ‖q‖) := le_min zero_le_one (by positivity)
      have hfac_le : min 1 (R₀ / ‖q‖) ≤ 1 := min_le_left _ _
      rw [abs_of_nonneg hfac_nn]
      calc min 1 (R₀ / ‖q‖) * ‖J q‖ ≤ 1 * ‖J q‖ :=
            mul_le_mul_of_nonneg_right hfac_le (norm_nonneg _)
        _ = ‖J q‖ := one_mul _
    have hJSymT : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ T))‖ ≤ Csym1 * ‖J p‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ T))‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
              (symmS (I := I) (M := M) g₀ T)‖ := by rw [hJembed]
        _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T‖ := hCsym1' T
        _ = Csym1 * ‖J p‖ := by rw [hJembed]
    have hJSymT' : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
        (symmS (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * ‖J p'‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ T'))‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
              (symmS (I := I) (M := M) g₀ T')‖ := by rw [hJembed]
        _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) T'‖ := hCsym1' T'
        _ = Csym1 * ‖J p'‖ := by rw [hJembed]
    have hmax1 : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖ ≤
        Csym1 * ‖J p‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T)))‖ := by rw [hSembed]
        _ ≤ ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T))‖ := hJscale _
        _ ≤ Csym1 * ‖J p‖ := hJSymT
    have hmax1' : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * ‖J p'‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T')))‖ := by rw [hS'embed]
        _ ≤ ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T'))‖ := hJscale _
        _ ≤ Csym1 * ‖J p'‖ := hJSymT'
    have hmaxle : max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
        ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * max ‖J p‖ ‖J p'‖ :=
      max_le
        (hmax1.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCsym1_nn))
        (hmax1'.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hCsym1_nn))
    have hdistSymT_le : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T) -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ T')‖ ≤ Csym2 * ‖p - p'‖ :=
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ T) -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T')‖
          = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ (T - T'))‖ := by
              rw [← smoothCcToTensorHs_sub, ← symmS_sub]
        _ ≤ Csym2 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T')‖ :=
              hCsym2' (T - T')
        _ = Csym2 * ‖p - p'‖ := by rw [smoothCcToTensorHs_sub]
    have hdistle : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ ≤ Csym2 * ‖p - p'‖ :=
      calc ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖
          = ‖ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T)) -
            ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T'))‖ := by rw [hSembed, hS'embed]
        _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T) -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T')‖ := by
              have hlip := (lipschitzWith_ballRetraction (X := tensorHs (I := I) (M := M)
                g₀ 0 2 ((a : ℝ) + 2)) hR₀.le).dist_le_mul
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ T))
                (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                  (symmS (I := I) (M := M) g₀ T'))
              rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hlip
              exact hlip
        _ ≤ Csym2 * ‖p - p'‖ := hdistSymT_le
    have hmaxSymT_le : max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T))‖
        ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * max ‖J p‖ ‖J p'‖ :=
      max_le
        (hJSymT.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hCsym1_nn))
        (hJSymT'.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hCsym1_nn))
    have hincl_diff_J : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T) -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
            (symmS (I := I) (M := M) g₀ T'))‖ ≤ Csym1 * ‖J (p - p')‖ :=
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T) -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ T'))‖
            = ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
                (symmS (I := I) (M := M) g₀ (T - T')))‖ := by
                rw [← smoothCcToTensorHs_sub, ← symmS_sub]
          _ = ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1)
                (symmS (I := I) (M := M) g₀ (T - T'))‖ := by rw [hJembed]
          _ ≤ Csym1 * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 1) (T - T')‖ :=
                hCsym1' (T - T')
          _ = Csym1 * ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) (T - T'))‖ := by
                rw [hJembed]
          _ = Csym1 * ‖J (p - p')‖ := by rw [smoothCcToTensorHs_sub]
    have hincl : ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
          smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        Csym1 * ‖J (p - p')‖ +
          Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ := by
      have hRinv_le : (0 : ℝ) ≤ 1 / R₀ := hRinv_nn
      have hCsym1max_nn : 0 ≤ Csym1 * max ‖J p‖ ‖J p'‖ :=
        mul_nonneg hCsym1_nn (le_trans (norm_nonneg _) (le_max_left _ _))
      have hbr_diff := norm_map_ballRetraction_sub_le
        (X := tensorHs (I := I) (M := M) g₀ 0 2 ((a : ℝ) + 2)) hR₀ J
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T))
        (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
          (symmS (I := I) (M := M) g₀ T'))
      calc ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖
          = ‖J (ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T)) -
            ballRetraction R₀ (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2)
              (symmS (I := I) (M := M) g₀ T')))‖ := by rw [hSembed, hS'embed]
        _ ≤ _ := hbr_diff
        _ ≤ Csym1 * ‖J (p - p')‖ +
              (1 / R₀) * (Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖) := by
              apply add_le_add hincl_diff_J
              apply mul_le_mul _ hdistSymT_le (norm_nonneg _)
                (mul_nonneg hRinv_le hCsym1max_nn)
              exact mul_le_mul_of_nonneg_left hmaxSymT_le hRinv_le
        _ = Csym1 * ‖J (p - p')‖ +
              Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ := by ring
    have hmaxP_nn : 0 ≤ max ‖J p‖ ‖J p'‖ := le_trans (norm_nonneg _) (le_max_left _ _)
    have hCM_nn : 0 ≤ Csym1 * max ‖J p‖ ‖J p'‖ := mul_nonneg hCsym1_nn hmaxP_nn
    have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.coe_nonneg
    have hstep1 : (K : ℝ) *
          (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
              ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖) ≤
        (K : ℝ) * ((Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hmaxle hdistle (norm_nonneg _) hCM_nn) hKnn
    have hstep2 : (K : ℝ) *
          ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
            smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ ≤
        (K : ℝ) * (Csym1 * ‖J (p - p')‖ +
          Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖) :=
      mul_le_mul_of_nonneg_left hincl hKnn
    calc (K : ℝ) *
          (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
              ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
            ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖ +
          ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖)
        = (K : ℝ) *
            (max ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S)‖
                ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ *
              ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
                smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S'‖) +
          (K : ℝ) * ‖J (smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S -
              smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) S')‖ := by ring
      _ ≤ (K : ℝ) * ((Csym1 * max ‖J p‖ ‖J p'‖) * (Csym2 * ‖p - p'‖)) +
          (K : ℝ) * (Csym1 * ‖J (p - p')‖ +
            Csym1 * Csym2 * (1 / R₀) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖) :=
            add_le_add hstep1 hstep2
      _ = ((K : ℝ) * Csym1 * Csym2 + (K : ℝ) * Csym1 * Csym2 * (1 / R₀)) *
            max ‖J p‖ ‖J p'‖ * ‖p - p'‖ + ((K : ℝ) * Csym1) * ‖J (p - p')‖ := by ring
      _ = (C₁ : ℝ) * max ‖J p‖ ‖J p'‖ * ‖p - p'‖ + (C₂ : ℝ) * ‖J (p - p')‖ := by
            rw [hC₁coe, hC₂coe]
  have hsub : (D ×ˢ D) ⊆ {p | lhs p ≤ rhs p} := by
    rintro ⟨p₁, p₂⟩ ⟨⟨T, hT⟩, ⟨T', hT'⟩⟩
    have := hsmooth T T'
    rw [hT, hT'] at this
    exact this
  have huniv : {p | lhs p ≤ rhs p} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (hDdense.prod hDdense).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  intro u u'
  have hmem : ((u, u') : _ × _) ∈ {p | lhs p ≤ rhs p} := by rw [huniv]; trivial
  have := hmem
  rw [Set.mem_setOf_eq, hlhs_def, hrhs_def] at this
  simpa only [hJ_def] using this

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
