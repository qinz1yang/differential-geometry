import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralMassUniformSup
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.MaxRegInteriorTimeSmoothing
import DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.SpectralSmoothRepresentativeRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.TensorHsRealize
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.EigenCombination
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RealizeMetricChartGramDifference
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RawComponentEuclideanBridge
import DifferentialGeometry.Analysis.Sobolev.Embedding.SobolevEmbeddingCmOrderDropping
import DifferentialGeometry.Analysis.Calculus.ContDiffOnTsum
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.CompactChartJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.EigensectionSobolevDecay
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Analysis.Elliptic.TensorRegularity.DirichletForm.RotatedTestSection
import DifferentialGeometry.Analysis.Spectral.Tensor.SmoothSection.SmoothTensorAllOrderCompleteness
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.Representation.TensorReprFromFrame
import DifferentialGeometry.Analysis.Calculus.AnisotropicJointContDiff

/-!
# Joint chart-Gram smoothness from a *time-smooth* spectral eigen-coordinate family

This file records the corrected spectral-regularity bedrock behind the joint
chart-Gram smoothness conjunct of the realized DeTurck–Ricci family.  It replaces
the false-as-stated `jointChartGramSmooth_of_spectralSmooth_timeContinuous`
(`SpectralPartialSumJointGram.lean`), whose hypothesis was only `L²`-time
*continuity* of the family — which does **not** give joint `C^∞` (counterexample
`T_rep t = |t| · S₀`: the realized chart-Gram entries are then merely `C⁰`, not
`C^∞`, in `t`).

The corrected statement takes a genuinely **time-smooth** eigen-coordinate family
`φ : TensorEigenIdx g 0 2 → ℝ → ℝ` together with a single, `t`-independent,
summable-across-modes majorant on every time-jet of the weighted coordinate
squares — exactly the consumer-facing conclusion shape produced by
`perModeConv_allOrder_timeDeriv_spectralMass_le`
(`MaxRegInteriorTimeSmoothing.lean`).  Under these hypotheses the chart-Gram
matrix entries of the realized metric family
`g_DT t = tensorSectionRealizeMetric g (T_rep t) hδ_lt (hδ t)` are jointly `C^∞`
up to `t = 0` (`JointChartGramSmooth`).

## The reasoning route

The realized chart-Gram entry is *affine* in the tensor `T_rep t`:
`chartGramMatrix (realize g (T_rep t)) α x i j
  = chartGramMatrix g α x i j + ccTensorBilinSymm g (T_rep t) x (vᵢ) (vⱼ)`
(`tensorSectionRealizeMetric_inner`, `chartGramMatrix_apply`), where
`vₖ = chartBasisVecFiber α k x`.  The first (background) term is time-independent
and smooth in `x` (`chartGramMatrix_entry_contMDiffOn`); the time-dependence enters
only through the increment, and through `T_rep t`'s eigen-series
`T_rep t = ∑ᵢ φᵢ(t) · bᵢ`.

This file proves the manifold-level joint smoothness *in full* — the affine
decomposition, the background smoothness, the manifold↔Euclidean chart pull/push,
and the composition with the smooth moving chart point — and reduces the genuine
analytic content to a **single** Euclidean prerequisite: that the realized
chart-Gram increment, pulled through the inverse chart to a scalar function on
`ℝ × E`, is jointly `C^∞` on the closed-time slab over the chart target.

That Euclidean increment is the series
`(t, y) ↦ ∑' i, φᵢ(t) · ccTensorBilinSymm g (bᵢ) ((extChartAt α).symm y) (vᵢ) (vⱼ)`
of jointly-`C^∞` per-mode terms (time-`C^∞` `φᵢ` by `hφ_smooth`; space-`C^∞`
eigensection chart-component by `eigenvectorSmooth_contMDiff`), and joint `C^∞`
is the closed-set `M`-test series lemma `contDiffOn_tsum` applied per convex
chart-ball: the spatial chart `Sobolev ↪ Cᵏ` embedding of the eigensections
contributes a `tensorSobolevWeight`-power factor per spatial order, which the
supplied time-jet mode-mass hypothesis `hmodemass` absorbs into a
summable-across-modes majorant.

## The chart-`C⁰` spectral convergence (proved in full)

The Euclidean increment smoothness `realizedChartGramIncrement_euclidean_contDiffOn`
is the eigen-series assembly: `contDiffOn_tsum` applied per convex chart-ball over the
open-ball cover of the chart-target interior (`contDiffOn_of_locally_contDiffOn`), with the
per-mode joint smoothness `eigenChartIncrementMode_contDiffOn` and the per-mode mixed-jet
chart `M`-test majorant `eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant`
(the latter via the compact-uniform reverse-Christoffel order-peeling and `C^m` Sobolev
embedding).  The pointwise eigen-series identity
`realizedChartGramIncrement_eigenSeries_eq` is assembled from public spectral API (all-order
`Hˢ` membership, the finite spectral partial-sum bilinear identity, the eigenIdxFinset
exhaustion, and `HasSum`).

Its genuine analytic core is the *chart-`C⁰` (pointwise)* convergence
`spectralPartialSum_ccTensorBilinSymm_tendsto` of the symmetrized extracted bilinear form of
the spectral partial sums to that of the smooth `L²` representative.  This is proved here in
full by a **scalar** argument that bypasses the disabled fibre-bundle topology: the chart-frame
fibre reconstruction `toSection_eq_sum_chartBasisFiberSection` expands the symmetrized form
(through the additive, homogeneous fibre functional `ccBilinSymmFibre`) into a finite sum of
real raw chart-frame components, and each raw component converges by dividing the POU-weighted
chart-component limit (`spectralChartComponent_tendsto` — the all-order uniform-Cauchy limit
of `SmoothTensorAllOrderCompleteness`, identified with the smooth representative via
`continuous_tensorL2ChartComponent` + an a.e. subsequence + `Measure.eqOn_of_ae_eq`) by the
positive partition-of-unity weight.

The apex `jointChartGramSmooth_of_spectralSmooth_timeSmooth` is sorry-free: `#print axioms`
is `[propext, Classical.choice, Quot.sound]`. -/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Topology
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Tensor
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Sobolev.Tensor
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Additivity of the symmetrized extracted bilinear form in the tensor argument.**
The companion to `ccTensorBilinSymm_smul`: `ccTensorBilinSymm` is additive in the
`(0,2)`-tensor section.  Both `ccTensorBilin` and the symmetrization are linear in the
section, which is additive (`SmoothCcTensor.toSection_add`). -/
theorem ccTensorBilinSymm_add (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S + T) x v w =
      ccTensorBilinSymm (I := I) g S x v w + ccTensorBilinSymm (I := I) g T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply, ccTensorBilinSymm_apply]
  have hbilin : ∀ (a b : TangentSpace I x),
      ccTensorBilin (I := I) g (S + T) x a b =
        ccTensorBilin (I := I) g S x a b + ccTensorBilin (I := I) g T x a b := by
    intro a b
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
    show ccTensorModel (I := I) g (S + T) x ![a, b] =
      ccTensorModel (I := I) g S x ![a, b] + ccTensorModel (I := I) g T x ![a, b]
    have hmodel : ccTensorModel (I := I) g (S + T) x =
        ccTensorModel (I := I) g S x + ccTensorModel (I := I) g T x := by
      rw [ccTensorModel, ccTensorModel, ccTensorModel]
      have hmul : (ccTensorMultilinear (I := I) g (S + T) x :
            Tensor0SBundle.Tensor0SSpace 2 I x) =
          (ccTensorMultilinear (I := I) g S x : Tensor0SBundle.Tensor0SSpace 2 I x) +
            (ccTensorMultilinear (I := I) g T x : Tensor0SBundle.Tensor0SSpace 2 I x) := by
        rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply, ccTensorMultilinear_apply,
          SmoothCcTensor.toSection_add]
        exact ContinuousLinearMap.add_apply _ _ _
      rw [hmul, Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [hmodel, ContinuousMultilinearMap.add_apply]
  rw [hbilin v w, hbilin w v]; ring

/-- The Euclidean *per-mode* increment scalar: for an eigen-index `i`, the chart-pulled
chart-Gram increment of the smooth eigensection `eigenvectorSmooth g 0 2 i`, weighted by the
smooth time coordinate `φ i`.  This is the summand of the eigen-series whose joint `C^∞`
smoothness (across the closed-time slab) assembles into the increment smoothness. -/
private def eigenChartIncrementMode
    (g : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ × E → ℝ :=
  fun q : ℝ × E =>
    φ i q.1 *
      ccTensorBilinSymm (I := I) g
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
          (I := I) (M := M) g 0 2 i)
        ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))

/-- **Per-mode joint smoothness (analytic prerequisite P0).**  Each eigen-series summand
`eigenChartIncrementMode` is jointly `C^∞` on the closed-time slab over the chart-target
interior.  In `t` it is the smooth coordinate `φ i` (`hφ_smooth`); in `y` it is the
chart-pulled chart-Gram increment of the *smooth* eigensection
`eigenvectorSmooth g 0 2 i` (a `C^∞` tensor section, whose chart component is `C^∞` in the
chart coordinate).  The product is jointly smooth.

The chart-pulled increment of a fixed smooth eigensection is `C^∞` in `y` through the same
manifold↔Euclidean chart transfer used by the sibling
`realizedChartGramIncrement_alongChart_contMDiffOn`, specialised to the time-constant
eigensection: the manifold scalar `x ↦ ccTensorBilinSymm g bᵢ x (vᵢ' x)(vⱼ' x)` is smooth on
the trivialization base set (the smooth Hom-section `ccTensorBilinSymm_contMDiff` evaluated on
the two smooth chart-basis sections, exactly as `chartGramMatrix_entry_contMDiffOn`), composed
with the smooth inverse chart `contMDiffOn_extChartAt_symm` and read as a Euclidean
`ContDiffOn` (`ContMDiffOn.contDiffOn`).  The product with the time-smooth coordinate is jointly
smooth. -/
private theorem eigenChartIncrementMode_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ}
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set S := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.eigenvectorSmooth
    (I := I) (M := M) g 0 2 i with hS_def

  have hB : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (ccTensorBilinSymm (I := I) g S b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    (MetricRealization.ccTensorBilinSymm_contMDiff (I := I) g S).contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i'
  have hw := chartBasisVec_contMDiffOn (I := I) α j'
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            ccTensorBilinSymm (I := I) g S m
              (chartBasisVecFiber (I := I) α i' m)
              (chartBasisVecFiber (I := I) α j' m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ) (b := id) hB hv hw
  have hScal : ContMDiffOn I 𝓘(ℝ) ∞
      (fun m : M => ccTensorBilinSymm (I := I) g S m
        (chartBasisVecFiber (I := I) α i' m)
        (chartBasisVecFiber (I := I) α j' m))
      (trivializationAt E (TangentSpace I) α).baseSet := by
    intro x hx
    have hpx := happ x hx
    rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
    exact hpx.2

  rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hScal
  have hsource_eq : (chartAt H α).source = (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]
  rw [hsource_eq] at hScal
  have hmapsTo : Set.MapsTo (extChartAt I α).symm (interior (extChartAt I α).target)
      (extChartAt I α).source := by
    intro y hy
    have hy' : y ∈ (extChartAt I α).target := interior_subset hy
    exact (extChartAt I α).map_target hy'
  have hsymm_cmdiff : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (interior (extChartAt I α).target) :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) α).mono interior_subset
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hScal.comp hsymm_cmdiff hmapsTo
  have hSpace : ContDiffOn ℝ ∞
      (fun y : E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm y)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y)))
      (interior (extChartAt I α).target) :=
    hcomp.contDiffOn

  have htime : ContDiffOn ℝ ∞ (fun q : ℝ × E => φ i q.1)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
  have hspaceComp : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ccTensorBilinSymm (I := I) g S ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    hSpace.comp contDiffOn_snd (Set.mapsTo_snd_prod)
  exact htime.mul hspaceComp

/-- **Eigenbasis-coordinate faithfulness of the `L²` spectral coordinates.**  Two
`L²` tensors with the same eigenbasis-coordinate family `tensorL2Coeff` are equal.
This is `HilbertBasis.repr`-injectivity applied to the chart-locality-free eigenbasis
`tensorResolventHilbertEigenbasisSigma`, of which `tensorL2Coeff` is the coordinate
readout (`tensorL2Coeff i = (b.repr ·) i` by definition). -/
private theorem tensorL2_ext_of_tensorL2Coeff'
    (g : SmoothRiemannianMetric I M)
    {S T : TensorL2 0 2 g}
    (h : ∀ i, tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) S i =
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) T i) :
    S = T := by
  classical
  set hc := tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2 with hhc
  set b := DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) hc with hb
  apply b.repr.injective
  ext i
  have hS : (b.repr S) i = tensorL2Coeff (I := I) (M := M) hc S i := rfl
  have hT : (b.repr T) i = tensorL2Coeff (I := I) (M := M) hc T i := rfl
  rw [hS, hT, h i]

/-- **All-order Sobolev membership of an `L²` tensor with summable weighted coordinate
squares.**  If for every `σ ≥ 0` the weighted eigenbasis-coordinate squares of `u` are
summable across modes, then `u` lies (via the chart-locality-free realization
`tensorHsToL2`) in `Hˢ` for every `σ ≥ 0`: the witness `v : Hˢ` is the coordinate family
of `u` itself, whose `tensorHsToL2` image has the same coordinates as `u` and hence equals
`u` by eigenbasis-coordinate faithfulness. -/
private theorem allHs_of_weighted_summable
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
  refine tensorL2_ext_of_tensorL2Coeff' (I := I) (M := M) g (fun i => ?_)
  rw [tensorHsToL2_tensorL2Coeff]

/-- **The `ccTensorBilinSymm` of a finite eigen-combination is the finite coefficient
sum of the per-mode `ccTensorBilinSymm`.**  Bilinear-form extraction is additive
(`ccTensorBilinSymm_add`) and `ℝ`-homogeneous (`ccTensorBilinSymm_smul`) in the tensor
argument, and `finiteEigenCombo F c = ∑_{i ∈ F} c i • eᵢ`, so the symmetrized extracted
form distributes over the finite sum. -/
private theorem ccTensorBilinSymm_finiteEigenCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (finiteEigenCombo (I := I) (M := M) g F c) x v w =
      ∑ i ∈ F, c i *
        ccTensorBilinSymm (I := I) g (eigenSmooth (I := I) (M := M) g i) x v w := by
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

/-- **Fibre-level symmetrized bilinear extraction.**  A real-valued functional of the raw
`(0,2)`-tensor fibre element `T` at `x`, additive and `ℝ`-homogeneous in `T`, recovering
`ccTensorBilinSymm` on the section value.  It evaluates `T` on the canonical empty-product
`(0,0)`-tensor, pushes the resulting `(0,2)` model value through `Tensor0SSpace.toModel`, and
symmetrizes its bilinear evaluation on `(v, w)`.  Working at the fibre level (rather than on
`SmoothCcTensor`) is what lets the chart-frame fibre reconstruction
`toSection_eq_sum_chartBasisFiberSection` distribute over the symmetrized form, reducing the
scalar spectral convergence to a finite sum of real chart-component limits — no fibre-bundle
topology required. -/
def ccBilinSymmFibre (x : M) (T : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) : ℝ :=
  (1 / 2 : ℝ) * (
    Tensor0SBundle.Tensor0SSpace.toModel
      (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![v, w]
    + Tensor0SBundle.Tensor0SSpace.toModel
      (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) ![w, v])

/-- `ccTensorBilinSymm g S x v w` is the fibre functional `ccBilinSymmFibre` applied to the
section value `S.toSection x`. -/
theorem ccTensorBilinSymm_eq_ccBilinSymmFibre (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g S x v w =
      ccBilinSymmFibre (I := I) x (S.toSection x) v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilin_apply, ccTensorBilin_apply]
  rfl

/-- `ccBilinSymmFibre` is additive in the fibre argument. -/
theorem ccBilinSymmFibre_add (x : M) (T₁ T₂ : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    ccBilinSymmFibre (I := I) x (T₁ + T₂) v w =
      ccBilinSymmFibre (I := I) x T₁ v w + ccBilinSymmFibre (I := I) x T₂ v w := by
  unfold ccBilinSymmFibre
  rw [show (T₁ + T₂) (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      = T₁ (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
        + T₂ (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ)) from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    ContinuousMultilinearMap.add_apply]
  ring

/-- `ccBilinSymmFibre` is `ℝ`-homogeneous in the fibre argument. -/
theorem ccBilinSymmFibre_smul (x : M) (a : ℝ) (T : Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    ccBilinSymmFibre (I := I) x (a • T) v w = a * ccBilinSymmFibre (I := I) x T v w := by
  unfold ccBilinSymmFibre
  rw [show (a • T) (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      = a • (T (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))) from rfl,
    Tensor0SBundle.Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

/-- `ccBilinSymmFibre` distributes over a finite scalar-weighted sum of fibre elements. -/
theorem ccBilinSymmFibre_sum {ι : Type*} (s : Finset ι) (x : M)
    (c : ι → ℝ) (T : ι → Tensor0SBundle.TensorRSSpace 0 2 I x)
    (v w : TangentSpace I x) :
    ccBilinSymmFibre (I := I) x (∑ i ∈ s, c i • T i) v w =
      ∑ i ∈ s, c i * ccBilinSymmFibre (I := I) x (T i) v w := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : Tensor0SBundle.TensorRSSpace 0 2 I x) =
          (0 : ℝ) • (0 : Tensor0SBundle.TensorRSSpace 0 2 I x) := by rw [zero_smul]
      rw [h0, ccBilinSymmFibre_smul, zero_mul]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ccBilinSymmFibre_add,
        ccBilinSymmFibre_smul, ih]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (tensorChartComponentRaw) in
/-- **The symmetrized extracted bilinear form as a finite chart-frame component sum.**
On the chart-`β` source, `ccTensorBilinSymm g S b v w` is the finite sum over component
multi-indices `Q` of the raw chart-`β`-frame component
`tensorChartComponentRaw g 0 2 S β Q.1 Q.2 b` weighted by a fixed (`S`-independent) real
scalar `ccBilinSymmFibre b (chartBasisFiberSection 0 2 β Q b) v w`.  This is the chart-frame
fibre reconstruction `toSection_eq_sum_chartBasisFiberSection` carried through the additive,
homogeneous fibre functional `ccBilinSymmFibre`. -/
theorem ccTensorBilinSymm_eq_sum_chartBasis (g : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g 0 2) (β : M) {b : M} (hb : b ∈ (chartAt H β).source)
    (v w : TangentSpace I b) :
    ccTensorBilinSymm (I := I) g S b v w =
      ∑ Q : CompIdx E 0 2,
        tensorChartComponentRaw (I := I) (M := M) g 0 2 S β Q.1 Q.2 b *
          ccBilinSymmFibre (I := I) b
            (chartBasisFiberSection (I := I) (M := M) 0 2 β Q b) v w := by
  rw [ccTensorBilinSymm_eq_ccBilinSymmFibre,
    toSection_eq_sum_chartBasisFiberSection (I := I) (M := M) g 0 2 S β hb,
    ccBilinSymmFibre_sum]

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
open DifferentialGeometry.Analysis.Sobolev.Chart in
/-- **Pointwise convergence of the POU-weighted chart-frame component of the spectral
partial sums to that of any smooth `L²` representative.**

If the spectral partial sums `F n = spectralPartialSum g u n` are Cauchy in every chart
`H^{2k}` (`hcauchy`) and converge to `u` in `L²` (`hF_L2`), and `Trep` is any smooth
representative of `u` (`hTrep`), then at every chart-target point `y` the canonical
POU-weighted Euclidean chart component `tensorChartComponent g 0 2 (F n) β P.1 P.2 y`
converges to `tensorChartComponent g 0 2 Trep β P.1 P.2 y`.

The Euclidean uniform-limit-of-derivatives machinery
(`exists_chartComponent_limit_smooth_compactSupport`) supplies a *pointwise everywhere*
continuous limit `uP`; the canonical chart component is continuous-linear in the `L²`
argument (`continuous_tensorL2ChartComponent`) and identifies, as an `Lp` class, with the
smooth chart component (`tensorL2ChartComponent_smoothToTensorL2_eq`), so the chart
components converge to `tensorChartComponent Trep` in `Lp(chartL2Measure)`; an a.e.-convergent
subsequence (`TendstoInMeasure.exists_seq_tendsto_ae`) then forces `uP = tensorChartComponent
Trep` a.e., hence everywhere on the open chart target (both continuous,
`Measure.eqOn_of_ae_eq` against the open-positive Lebesgue measure). -/
theorem spectralChartComponent_tendsto
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hcauchy : ∀ k : ℕ, CauchySeq (fun n =>
      SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k)
        (spectralPartialSum (I := I) (M := M) g u n)))
    (hF_L2 : Tendsto (fun n => (spectralPartialSum (I := I) (M := M) g u n : TensorL2 0 2 g))
      atTop (𝓝 u))
    (Trep : SmoothCcTensor g 0 2) (hTrep : (Trep : TensorL2 0 2 g) = u)
    (β : M) (P : TensorCompIdx (E := E) 0 2)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) β) :
    Tendsto (fun n => tensorChartComponent (I := I) (M := M) g 0 2
        (spectralPartialSum (I := I) (M := M) g u n) β P.1 P.2 y)
      atTop (𝓝 (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 y)) := by
  classical
  set F : ℕ → SmoothCcTensor g 0 2 :=
    fun n => spectralPartialSum (I := I) (M := M) g u n with hF_def
  set S : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) β with hS_def
  set μ : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartL2Measure (I := I) (M := M) β with hμ_def
  have hμ_eq : μ = (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))).restrict S := by
    rw [hμ_def, chartL2Measure, hS_def]
  have hS_open : IsOpen S := chartTargetEuclid_isOpen (I := I) (M := M) β
  obtain ⟨uP, huP_contDiff, _huP_supp, huP_tendsto⟩ :=
    exists_chartComponent_limit_smooth_compactSupport (I := I) (M := M) g 0 2 F hcauchy β
  have hmemFn : ∀ n,
      MemLp (tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2) 2 μ :=
    fun n => tensorChartComponent_memLp (I := I) (M := M) g 0 2 (F n) β P.1 P.2
  have hmemTrep : MemLp (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) 2 μ :=
    tensorChartComponent_memLp (I := I) (M := M) g 0 2 Trep β P.1 P.2
  have hL2cont : Tendsto (fun n => tensorL2ChartComponent (I := I) (M := M) g 0 2
        ((F n : TensorL2 0 2 g)) β P) atTop
        (𝓝 (tensorL2ChartComponent (I := I) (M := M) g 0 2 u β P)) :=
    ((continuous_tensorL2ChartComponent (I := I) (M := M) g 0 2 β P).tendsto u).comp hF_L2
  have hLp_Fn : ∀ n, tensorL2ChartComponent (I := I) (M := M) g 0 2
      ((F n : TensorL2 0 2 g)) β P = (hmemFn n).toLp _ :=
    fun n => tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g 0 2 (F n) β P
  have hLp_Trep : tensorL2ChartComponent (I := I) (M := M) g 0 2 u β P = hmemTrep.toLp _ := by
    rw [← hTrep]
    exact tensorL2ChartComponent_smoothToTensorL2_eq (I := I) (M := M) g 0 2 Trep β P
  rw [hLp_Trep] at hL2cont
  simp only [hLp_Fn] at hL2cont
  have heLp : Tendsto (fun n => eLpNorm
      (tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2 -
        tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) 2 μ) atTop (𝓝 0) := by
    have hed : Tendsto (fun n => edist ((hmemFn n).toLp _)
        (hmemTrep.toLp (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2)))
        atTop (𝓝 (edist (hmemTrep.toLp _) (hmemTrep.toLp _))) :=
      hL2cont.edist tendsto_const_nhds
    rw [edist_self] at hed
    refine hed.congr (fun n => ?_)
    exact Lp.edist_toLp_toLp _ _ (hmemFn n) hmemTrep
  have h_tim : TendstoInMeasure μ
      (fun n => tensorChartComponent (I := I) (M := M) g 0 2 (F n) β P.1 P.2)
      atTop (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (μ := μ) (p := 2) (by norm_num)
      (fun n => (hmemFn n).aestronglyMeasurable) hmemTrep.aestronglyMeasurable heLp
  obtain ⟨σ, hσ_mono, hσ_ae⟩ := h_tim.exists_seq_tendsto_ae
  have hae_eq : (uP P) =ᵐ[μ] tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 := by
    filter_upwards [hσ_ae] with z hz
    have hfull : Tendsto
        (fun n => tensorChartComponent (I := I) (M := M) g 0 2 (F (σ n)) β P.1 P.2 z)
        atTop (𝓝 (uP P z)) := (huP_tendsto P z).comp hσ_mono.tendsto_atTop
    exact tendsto_nhds_unique hfull hz
  have huP_contOn : ContinuousOn (uP P) S := (huP_contDiff P).continuousOn
  have hTrep_contOn :
      ContinuousOn (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) S :=
    (tensorChartComponent_contDiff' (I := I) (M := M) g 0 2 Trep β P.1 P.2).continuous.continuousOn
  have hEqOn :
      Set.EqOn (uP P) (tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2) S := by
    rw [hμ_eq] at hae_eq
    exact MeasureTheory.Measure.eqOn_of_ae_eq hae_eq huP_contOn hTrep_contOn
      (by rw [hS_open.interior_eq]; exact subset_closure)
  have hlimit_y :
      tensorChartComponent (I := I) (M := M) g 0 2 Trep β P.1 P.2 y = uP P y :=
    (hEqOn hy).symm
  rw [hlimit_y]
  exact huP_tendsto P y

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral in
open DifferentialGeometry.Analysis.Sobolev.Chart in
/-- **Pointwise chart-`C⁰` spectral convergence of the symmetrized bilinear form
(analytic prerequisite P1₀).**  For an `L²` tensor `u` lying in `Hˢ` for every `σ ≥ 0`
(`hu`) and a smooth representative `Trep` of `u` (`hTrep : (Trep : TensorL2) = u`), the
symmetrized extracted bilinear form of the spectral partial sums converges, at every
point `x` and pair of tangent vectors `(v, w)`, to that of `Trep`:
`ccTensorBilinSymm g (spectralPartialSum g u n) x v w → ccTensorBilinSymm g Trep x v w`.

The argument is purely scalar (`ℝ`-valued), bypassing the disabled fibre-bundle topology.
Choose any chart `β` whose partition-of-unity weight is positive at `x` (such a `β` exists
since `chartAtlasPOU` sums to `1`); then `x` lies in the chart-`β` source.  The chart-frame
fibre reconstruction `ccTensorBilinSymm_eq_sum_chartBasis` writes
`ccTensorBilinSymm g S x v w` as the finite sum over component multi-indices `Q` of the raw
chart-`β`-frame component `tensorChartComponentRaw g 0 2 S β Q.1 Q.2 x` weighted by a fixed
real scalar.  Each raw component of the spectral partial sums converges to that of `Trep`:
the POU-weighted chart component converges (`spectralChartComponent_tendsto`, the genuine
analytic content), and dividing by the positive POU weight `ρ` recovers the raw component
(`tensorChartComponent = ρ · raw` at the chart point).  `tendsto_finset_sum` over the finite
`CompIdx` then gives the result.

The hypotheses `hu`/`hTrep` constrain it to the genuine spectral expansion of `u`'s smooth
representative; it is not a free posit. -/
private theorem spectralPartialSum_ccTensorBilinSymm_tendsto
    (g : SmoothRiemannianMetric I M) (u : TensorL2 0 2 g)
    (hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ v = u)
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

/-- **Per-order summable mixed-jet majorant (analytic prerequisite P2).**  On a convex
subset `Icc 0 T ×ˢ B` of the slab over a **compact** chart-ball `B ⊆ interior target`, each
order-`k` within-iterated Fréchet derivative of the per-mode increment admits a single
summable-across-modes uniform majorant.  By the Leibniz product rule the mixed `(t, y)`-jet
is bounded by `∑_{a+b=k} |∂ₜ^a φ_i| · ‖∇^b(chart increment of eigensection)‖`; the spatial
factor is controlled, uniformly over the **compact** `B`, by the eigensection's chart
`H^{2k} ↪ C^b` Sobolev embedding — now reduced (away from the partition-of-unity kernel, near
the chart-target boundary) to the compact-uniform reverse-Christoffel order-peeling
`iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact` and order-`0` fibre bound
`exists_zeroContentR_le_fiberNorm_on_compact` (`CompactChartJetBound.lean`, both PROVEN),
composed with the global pointwise `C^m` embedding
`iteratedCovGrad_toSobolev_embedding_Cm_unconditional` — contributing a
`tensorSobolevWeight`-power factor, which the supplied summable time-jet mode-mass
(`hmodemass`) absorbs into a summable-across-modes bound.

**Domain correctness (the routing fix).**  The earlier free `{B} (hB : B ⊆ interior target)`
quantification was FALSE-as-posited: the chart-trivialisation operator norm blows up at the
chart-target boundary, so no `tensorSobolevWeight`-power majorant exists for an arbitrary
boundary-touching `B`.  Requiring `B` compact (e.g. a closed ball strictly inside the
interior) is exactly the domain on which the compact-uniform bounds hold; the consumer
`realizedChartGramIncrement_euclidean_contDiffOn` only ever needs a compact-in-interior ball
(it works locally per ball via `contDiffOn_of_locally_contDiffOn`), so the restriction does
not weaken the apex.

This is now proved in full.  The spatial factor of each per-mode increment is bounded,
uniformly over the compact `B`, by the **uniform-in-`i` eigensection chart `H^{2k} ↪ C^b`
Sobolev decay** (`eigenvectorSmooth_toHs_norm_le_lambda_pow`, the spectral norm of the
smooth eigensection equals its eigenvalue weight) composed with the compact-uniform
reverse-Christoffel order-peeling and `C^m` Sobolev embedding; the time factor of each
Leibniz summand is controlled, uniformly over `Icc 0 T`, by the supplied summable time-jet
mode-mass `hmodemass` (without which no uniform majorant exists).  The two factors are
combined across modes by the arithmetic–geometric-mean inequality against the Weyl
summability `tensorEigen_summable_negpow`. -/
private lemma norm_iteratedFDeriv_clm_le
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (i : ℕ) (hi : 1 ≤ i) (x : F) :
    ‖iteratedFDeriv ℝ i (fun p => L p) x‖ ≤ (‖L‖ + 1) ^ i := by
  have hD1 : (1 : ℝ) ≤ ‖L‖ + 1 := by have := norm_nonneg L; linarith
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · interval_cases i
    rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    simp only [pow_one]; linarith [norm_nonneg L]
  · obtain ⟨j, rfl⟩ : ∃ jj, i = (jj + 1) + 1 := ⟨i - 2, by omega⟩
    have hz : ‖iteratedFDeriv ℝ ((j + 1) + 1) (fun p => L p) x‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv]
      have hfd : fderiv ℝ (fun p => L p) = fun _ : F => (L : F →L[ℝ] G) := by
        funext y; exact ContinuousLinearMap.fderiv L
      rw [hfd, iteratedFDeriv_const_of_ne (by omega) (L : F →L[ℝ] G)]
      simp
    rw [hz]; positivity

private lemma norm_iteratedFDerivWithin_compFst_le
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) {a bb : ℝ} {B : Set E}
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B)) (hab : a < bb)
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => f p.1) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set t := Set.Icc a bb with ht_def
  set L : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E with hL_def
  have hUDt : UniqueDiffOn ℝ t := uniqueDiffOn_Icc hab
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.1) s t := fun p hp => hp.1
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := f)
    (f := fun p : ℝ × E => p.1) (n := n) (s := s) (t := t) (x := q) (N := ∞)
    hf.contDiffOn contDiffOn_fst (by exact_mod_cast le_top) hUDt hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => by
      have heq : iteratedFDerivWithin ℝ i f t q.1 = iteratedFDeriv ℝ i f q.1 :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUDt
          (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hmaps hq)
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.1) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (f ∘ (fun p : ℝ × E => p.1)) = (fun p : ℝ × E => f p.1) := rfl
  rw [hcomp] at hbound
  exact hbound

private lemma norm_iteratedFDerivWithin_compSnd_le
    (spatial : E → ℝ) {O : Set E} (hO_open : IsOpen O)
    (hspatial : ContDiffOn ℝ ∞ spatial O)
    {a bb : ℝ} {B : Set E} (hBO : B ⊆ O)
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B))
    (n : ℕ) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j spatial O q.2‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => spatial p.2) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set L : (ℝ × E) →L[ℝ] E := ContinuousLinearMap.snd ℝ ℝ E with hL_def
  have hUDO : UniqueDiffOn ℝ O := hO_open.uniqueDiffOn
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.2) s O := fun p hp => hBO hp.2
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := spatial)
    (f := fun p : ℝ × E => p.2) (n := n) (s := s) (t := O) (x := q) (N := ∞)
    hspatial contDiffOn_snd (by exact_mod_cast le_top) hUDO hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.2) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.2) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_snd (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (spatial ∘ (fun p : ℝ × E => p.2)) = (fun p : ℝ × E => spatial p.2) := rfl
  rw [hcomp] at hbound
  exact hbound

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma ccTensorBilinSymm_eq_half_rawComponent
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {p : M}
    (hp : p ∈ (chartAt H α).source) :
    ccTensorBilinSymm (I := I) g S p
        (chartBasisVecFiber (I := I) α a p) (chartBasisVecFiber (I := I) α b p) =
      (1 / 2 : ℝ) *
        (tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![a, b] p +
          tensorChartComponentRaw (I := I) (M := M) g 0 2 S α ![] ![b, a] p) := by
  classical
  rw [ccTensorBilinSymm_apply]
  have hrawAB := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![a, b] : Fin 2 → Fin (Module.finrank ℝ E))
  have hrawBA := tensorChartComponentRaw_eq_chartFrame (I := I) (M := M) g 0 2
    S α hp (![] : Fin 0 → Fin (Module.finrank ℝ E))
    (![b, a] : Fin 2 → Fin (Module.finrank ℝ E))
  have hframe : chartFrameBasisModel (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) =
      (ContinuousMultilinearMap.constOfIsEmpty ℝ
        (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) := by
    apply ContinuousMultilinearMap.ext
    intro v
    have h := chartFrameBasisModel_apply (I := I) (M := M) α p 0
      (![] : Fin 0 → Fin (Module.finrank ℝ E)) v
    rw [Fin.prod_univ_zero] at h
    rw [ContinuousMultilinearMap.constOfIsEmpty_apply]
    exact h
  rw [hframe] at hrawAB hrawBA
  have hbilin : ∀ (i j : Fin (Module.finrank ℝ E)),
      (S.toSection p
          (ContinuousMultilinearMap.constOfIsEmpty ℝ
            (fun _ : Fin 0 => TangentSpace I p) (1 : ℝ)) :
        ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I p) ℝ)
          (fun k : Fin 2 =>
            chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ccTensorBilin (I := I) g S p
            (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p) := by
    intro i j
    have hvecAB : (fun k : Fin 2 =>
        chartBasisVecFiber (I := I) α ((![i, j] : Fin 2 → _) k) p) =
        ![chartBasisVecFiber (I := I) α i p, chartBasisVecFiber (I := I) α j p] := by
      funext k; fin_cases k <;> rfl
    rw [hvecAB, ccTensorBilin_apply]
    rfl
  rw [hrawAB, hrawBA, hbilin a b, hbilin b a]

private lemma norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
        (interior (extChartAt I α).target) y‖ ≤
      ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m *
        ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
          (toEuclidean (E := E) y)‖ := by
  classical
  set e : E ≃L[ℝ] EuclN := toEuclidean (E := E) with he_def
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hO_open : IsOpen O := isOpen_interior
  have hcompose : rawCompOnE (I := I) (M := M) g S α Jdx =
      (rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) ∘ ⇑e := by
    have h := rawPullR_eq_rawCompOnE_comp (I := I) (M := M) g S α Jdx
    funext z
    have := congrFun h (e z)
    simp only [Function.comp_apply, he_def] at this ⊢
    rw [this, ContinuousLinearEquiv.symm_apply_apply]
  rw [hcompose]
  set Oe : Set EuclN := e '' O with hOe_def
  have hOe_open : IsOpen Oe := e.isOpenMap O hO_open
  have hUDe : UniqueDiffOn ℝ Oe := hOe_open.uniqueDiffOn
  have hpre : (⇑e) ⁻¹' Oe = O := by rw [hOe_def, Set.preimage_image_eq _ e.injective]
  have hey : e y ∈ Oe := ⟨y, hy, rfl⟩
  have hOe_sub : Oe ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hOe_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, he_def, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset hx
  have hcr := e.iteratedFDerivWithin_comp_right
    (f := rawPullR (I := I) (M := M) g 0 2 S α (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx)
    hUDe (x := y) hey m
  rw [hpre] at hcr
  rw [hcr]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) m hOe_open hey]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [mul_comm]

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
private lemma exists_rawCompOnE_jet_le_toHs_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m k : ℕ)
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m)
    {B : Set E} (hB_compact : IsCompact B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m (rawCompOnE (I := I) (M := M) g S α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          C * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  set K : Set EuclN := (toEuclidean (E := E)) '' B with hK_def
  have hK_compact : IsCompact K := hB_compact.image (toEuclidean (E := E)).continuous
  have hK_sub : K ⊆ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid (I := I) (M := M) α := by
    rw [hK_def]
    rintro z ⟨x, hx, rfl⟩
    rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_eq_preimage_symm (I := I) (M := M)]
    simp only [Set.mem_preimage, ContinuousLinearEquiv.symm_apply_apply]
    exact interior_subset (hB hx)
  set KM : Set M := (extChartAt I α).symm '' B with hKM_def
  have hKM_compact : IsCompact KM :=
    hB_compact.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) α).mono
        (fun x hx => interior_subset (hB hx)))
  have hKM_sub : KM ⊆ (chartAt H α).source := by
    rw [hKM_def]
    rintro b ⟨x, hx, rfl⟩
    have hx' : x ∈ (extChartAt I α).target := interior_subset (hB hx)
    have := (extChartAt I α).map_target hx'
    rwa [extChartAt_source (I := I)] at this
  obtain ⟨Cpeel, hCpeel_nn, hpeel⟩ :=
    iteratedFDeriv_rawPullR_le_zeroContent_sum_on_compact (I := I) (M := M) g 0 2 α m
      hK_compact hK_sub m (le_refl m)
  have hz_per : ∀ i : ℕ, ∃ Cz : ℝ, 0 ≤ Cz ∧ ∀ (S : SmoothCcTensor g 0 2) {b : M}, b ∈ KM →
      zeroContentR (I := I) (M := M) g 0 (2 + i)
          (iteratedCovGrad g 0 2 i S) α (toEuclidean (E := E) (extChartAt I α b)) ≤
        Cz * (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    intro i
    obtain ⟨Cz, hCz_nn, hCz⟩ :=
      exists_zeroContentR_le_fiberNorm_on_compact (I := I) (M := M) g 0 (2 + i) α
        hKM_compact hKM_sub
    exact ⟨Cz, hCz_nn, fun S b hb => hCz (iteratedCovGrad g 0 2 i S) hb⟩
  choose Czf hCzf_nn hCzf using hz_per
  set Czmax : ℝ := (Finset.range (m + 1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m)) Czf with hCzmax_def
  have hCzmax_nn : 0 ≤ Czmax := by
    rw [hCzmax_def]
    exact le_trans (hCzf_nn 0) (Finset.le_sup' Czf (Finset.mem_range.mpr (Nat.succ_pos m)))
  have hCz_le : ∀ i ∈ Finset.range (m + 1), Czf i ≤ Czmax :=
    fun i hi => Finset.le_sup' Czf hi
  obtain ⟨Cemb, hCemb_pos, hCemb⟩ :=
    iteratedCovGrad_toSobolev_embedding_Cm_unconditional (I := I) (M := M) g 0 2 k m h_super
  set Cnorm : ℝ := ‖(toEuclidean (E := E) : E →L[ℝ] EuclN)‖ ^ m with hCnorm_def
  have hCnorm_nn : 0 ≤ Cnorm := by rw [hCnorm_def]; positivity
  refine ⟨Cnorm * (Cpeel * (Czmax * Cemb)), by positivity, fun S y hy => ?_⟩
  set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * k) S‖ with hN_def
  have hN_nn : 0 ≤ N := norm_nonneg _
  set b : M := (extChartAt I α).symm y with hb_def
  have hyt : y ∈ (extChartAt I α).target := interior_subset (hB hy)
  have hb_mem : b ∈ KM := ⟨y, hy, rfl⟩
  have hyB : toEuclidean (E := E) y ∈ K := ⟨y, hy, rfl⟩
  have hy_eq : extChartAt I α b = y := by rw [hb_def]; exact (extChartAt I α).right_inv hyt
  have hrev := norm_iteratedFDerivWithin_rawCompOnE_le_rawPullR (I := I) (M := M) g S α Jdx m (hB hy)
  refine le_trans hrev ?_
  have hpeel_y := hpeel S m (le_refl m) 0 (by omega) (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx
    (toEuclidean (E := E) y) hyB
  rw [iteratedCovGrad_zero] at hpeel_y
  have hsum_fiber : ∑ i ∈ Finset.range (m + 1),
        zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
          (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
      Czmax * ∑ i ∈ Finset.range (m + 1),
        (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
        ‖(iteratedCovGrad g 0 2 i S).toSection b‖) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    rw [Nat.zero_add]
    have hzi := hCzf i S hb_mem
    rw [hy_eq] at hzi
    refine le_trans hzi ?_
    letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
    exact mul_le_mul_of_nonneg_right (hCz_le i hi) (norm_nonneg _)
  have hemb := hCemb S b
  have hpeel_y' : ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
        (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖ ≤
      Cpeel * (Czmax * (Cemb * N)) := by
    refine le_trans hpeel_y ?_
    have hstep1 : Cpeel * ∑ i ∈ Finset.range (m + 1),
          zeroContentR (I := I) (M := M) g 0 (2 + (0 + i))
            (iteratedCovGrad g 0 2 (0 + i) S) α (toEuclidean (E := E) y) ≤
        Cpeel * (Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖)) :=
      mul_le_mul_of_nonneg_left hsum_fiber hCpeel_nn
    refine le_trans hstep1 ?_
    have hfiber_le : ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Cemb * N := hemb
    have hthis : Czmax * ∑ i ∈ Finset.range (m + 1),
          (letI : Bundle.RiemannianBundle (fun bb : M => Tensor0SBundle.TensorRSSpace 0 (2 + i) I bb) :=
              Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 (2 + i)
          ‖(iteratedCovGrad g 0 2 i S).toSection b‖) ≤ Czmax * (Cemb * N) :=
      mul_le_mul_of_nonneg_left hfiber_le hCzmax_nn
    exact mul_le_mul_of_nonneg_left hthis hCpeel_nn
  calc Cnorm * ‖iteratedFDeriv ℝ m (rawPullR (I := I) (M := M) g 0 2 S α
          (![] : Fin 0 → Fin (Module.finrank ℝ E)) Jdx) (toEuclidean (E := E) y)‖
      ≤ Cnorm * (Cpeel * (Czmax * (Cemb * N))) :=
        mul_le_mul_of_nonneg_left hpeel_y' hCnorm_nn
    _ = Cnorm * (Cpeel * (Czmax * Cemb)) * N := by ring

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
/-- The spatial factor of the per-mode increment, as a function on `E` (the chart target):
`y ↦ ccTensorBilinSymm g (eᵢ) ((extChartAt α).symm y) (vᵢ')(vⱼ')`, equal on the chart-target
interior to `(1/2)(rawCompOnE ![i',j'] + rawCompOnE ![j',i'])`. -/
private def eigenSpatialFactor
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : E → ℝ :=
  fun y : E =>
    ccTensorBilinSymm (I := I) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i)
      ((extChartAt I α).symm y)
      (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm y))
      (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm y))

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma eigenSpatialFactor_eqOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    Set.EqOn (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (fun y : E => (1 / 2 : ℝ) *
        (rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y))
      (interior (extChartAt I α).target) := by
  intro y hy
  have hsrc : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have hyt : y ∈ (extChartAt I α).target := interior_subset hy
    have := (extChartAt I α).map_target hyt
    rwa [extChartAt_source (I := I)] at this
  rw [eigenSpatialFactor,
    ccTensorBilinSymm_eq_half_rawComponent (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α i' j' hsrc]
  rfl

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma eigenSpatialFactor_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ ∞ (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
      (interior (extChartAt I α).target) := by
  refine ContDiffOn.congr ?_ (eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i)
  have hadd : ContDiffOn ℝ ∞
      (fun y : E => rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j'] y +
          rawCompOnE (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'] y)
      (interior (extChartAt I α).target) :=
    (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![i', j']).add
      (rawCompOnE_contDiffOn (I := I) (M := M) g (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![j', i'])
  exact contDiffOn_const.mul hadd

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private lemma exists_eigenSpatialFactor_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M) (i' j' : Fin (Module.finrank ℝ E)) (m : ℕ)
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i)
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set O : Set E := interior (extChartAt I α).target with hO_def
  have hUDO : UniqueDiffOn ℝ O := isOpen_interior.uniqueDiffOn

  set kE : ℕ := Module.finrank ℝ E + 2 * m + 1 with hkE_def

  have hper : ∀ m' : ℕ, m' ≤ m → ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y‖ ≤
          Cm' * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
   intro m' hm'
   have h_super : 2 * kE > Module.finrank ℝ E + 2 * m' := by rw [hkE_def]; omega
   obtain ⟨Cab, hCab_nn, hCab⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![i', j'] m' kE h_super hB_compact hB
   obtain ⟨Cba, hCba_nn, hCba⟩ :=
     exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α ![j', i'] m' kE h_super hB_compact hB
   obtain ⟨Cdec, hCdec_nn, hCdec⟩ :=
     eigenvectorSmooth_toHs_norm_le_lambda_pow (I := I) (M := M) g kE
   refine ⟨(1 / 2 : ℝ) * (Cab + Cba) * Cdec, by positivity, fun i y hy => ?_⟩
   set S := eigenvectorSmooth (I := I) (M := M) g 0 2 i with hS_def

   have hcongr : iteratedFDerivWithin ℝ m' (eigenSpatialFactor (I := I) (M := M) g α i' j' i) O y =
       iteratedFDerivWithin ℝ m'
         ((1 / 2 : ℝ) • (rawCompOnE (I := I) (M := M) g S α ![i', j'] +
           rawCompOnE (I := I) (M := M) g S α ![j', i'])) O y := by
     refine iteratedFDerivWithin_congr ?_ (hB hy) m'
     intro z hz
     rw [eigenSpatialFactor_eqOn (I := I) (M := M) g α i' j' i hz]
     simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, hS_def]
   rw [hcongr]
   have hcd_ab : ContDiffWithinAt ℝ (m' : ℕ∞) (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![i', j']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   have hcd_ba : ContDiffWithinAt ℝ (m' : ℕ∞) (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y :=
     ((rawCompOnE_contDiffOn (I := I) (M := M) g S α ![j', i']).contDiffWithinAt (hB hy)).of_le
       (by exact_mod_cast le_top)
   rw [iteratedFDerivWithin_const_smul_apply (f := rawCompOnE (I := I) (M := M) g S α ![i', j'] +
         rawCompOnE (I := I) (M := M) g S α ![j', i']) (hcd_ab.add hcd_ba) hUDO (hB hy),
     iteratedFDerivWithin_add_apply hcd_ab hcd_ba hUDO (hB hy)]
   refine le_trans (norm_smul_le (1 / 2 : ℝ)
     (iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
       iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y)) ?_
   have htri : ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
         iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖ ≤
       Cab * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ +
         Cba * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ :=
     le_trans (norm_add_le _ _) (add_le_add (hCab S y hy) (hCba S y hy))
   set N : ℝ := ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE) S‖ with hN_def
   have hN_nn : 0 ≤ N := norm_nonneg _
   have hdec : N ≤ Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := hCdec i
   have hbase_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) :=
     pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _
   calc ‖(1 / 2 : ℝ)‖ * ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
           iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖
       ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * N) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         calc ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![i', j']) O y +
               iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g S α ![j', i']) O y‖
             ≤ Cab * N + Cba * N := htri
           _ = (Cab + Cba) * N := by ring
     _ ≤ ‖(1 / 2 : ℝ)‖ * ((Cab + Cba) * (Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE))) := by
         refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
         exact mul_le_mul_of_nonneg_left hdec (by positivity)
     _ = (1 / 2 : ℝ) * (Cab + Cba) * Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
         rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]; ring
  choose Cf hCf_nn hCf using hper
  set Cmax : ℝ := (Finset.range (m + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun b => if hb : b ≤ m then Cf b hb else 0) with hCmax_def
  have hCmax_ge : ∀ (m' : ℕ) (h : m' ≤ m), Cf m' h ≤ Cmax := by
    intro m' h
    rw [hCmax_def]
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun b => if hb : b ≤ m then Cf b hb else 0)
      (Finset.mem_range.mpr (by omega : m' < m + 1)))
    rw [dif_pos h]
  refine ⟨Cmax, 2 * kE, ?_, fun m' hm' i y hy => ?_⟩
  · exact le_trans (hCf_nn 0 (Nat.zero_le m)) (hCmax_ge 0 (Nat.zero_le m))
  · refine le_trans (hCf m' hm' i y hy) ?_
    refine mul_le_mul_of_nonneg_right (hCmax_ge m' hm') ?_
    exact pow_nonneg (by have := tensor_lambda_nonneg (I := I) (M := M) i; linarith) _

set_option maxHeartbeats 1600000 in
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth tensorChartComponentRaw) in
private theorem eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB_uniq : UniqueDiffOn ℝ B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ k : ℕ, ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro k
  set O : Set E := interior (extChartAt I α).target with hO_def
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq

  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ :=
    exists_eigenSpatialFactor_jet_le_lambda_pow (I := I) (M := M) g α i' j' k hB_compact hB

  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  set σ0 : ℝ := 2 * (pSp : ℝ) + 2 * (sW : ℝ) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity

  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cm ∧
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i :=
    fun a => hmodemass a σ0 hσ0_nn
  choose Cmf hCmf_summable hCmf using htime

  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ)))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * (sW : ℝ)) ?_
    rw [hsW_def]; push_cast; have := weylSobolevExp_gt_finrank (E := E); push_cast at this ⊢
    have h0 : (0:ℝ) ≤ (weylSobolevExp (E := E) : ℝ) := by positivity
    nlinarith [h0]

  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have htime_pt : ∀ (j : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2) (t : ℝ),
      t ∈ Set.Icc (0 : ℝ) T →
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) := by
    intro j i t ht
    have hmm := hCmf j i t ht

    have hw : tensorSobolevWeight (I := I) (M := M) i σ0 =
        ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ))) ^ 2 := by
      unfold tensorSobolevWeight
      rw [hσ0_def, show 2 * (pSp : ℝ) + 2 * (sW : ℝ) = ((pSp : ℝ) + (sW : ℝ)) * 2 by ring,
        Real.rpow_mul (hbase_pos i).le, Real.rpow_two]
    rw [hw] at hmm
    set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (((pSp : ℝ)) + (sW : ℝ)) with hW_def
    have hW_pos : 0 < W := Real.rpow_pos_of_pos (hbase_pos i) _

    have hCm_nn : 0 ≤ Cmf j i := le_trans (by positivity) hmm
    have habs : |iteratedDeriv j (φ i) t| ≤ Real.sqrt (Cmf j i) / W := by
      rw [le_div_iff₀ hW_pos]
      have h2 : (|iteratedDeriv j (φ i) t| * W) ^ 2 ≤ (Real.sqrt (Cmf j i)) ^ 2 := by
        rw [Real.sq_sqrt hCm_nn, mul_pow, sq_abs]
        nlinarith [hmm, hW_pos.le]
      have hlhs_nn : 0 ≤ |iteratedDeriv j (φ i) t| * W := by positivity
      nlinarith [Real.sqrt_nonneg (Cmf j i), h2, hlhs_nn, sq_nonneg (|iteratedDeriv j (φ i) t| * W - Real.sqrt (Cmf j i))]
    rw [Real.rpow_neg (hbase_pos i).le]
    rw [div_eq_mul_inv] at habs
    rwa [← hW_def]

  set Kconst : ℝ := (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hwfun_sq : ∀ i, wfun i ^ 2 = tensorSobolevWeight (I := I) (M := M) i (-(2 * (sW : ℝ))) := by
    intro i
    rw [hwfun_def]
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hCm_nn : ∀ (a : ℕ) (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a i
    have h := hCmf a i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) with htermf_def
  have hw2_summable : Summable (fun i => wfun i ^ 2) := by simp_rw [hwfun_sq]; exact hweyl
  have hsqrt_summable : ∀ j, Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j
    have hbound : ∀ i, Real.sqrt (Cmf j i) * wfun i ≤ (Cmf j i + wfun i ^ 2) / 2 := by
      intro i
      have h1 : Real.sqrt (Cmf j i) * wfun i ≤ (Real.sqrt (Cmf j i) ^ 2 + wfun i ^ 2) / 2 := by
        nlinarith [sq_nonneg (Real.sqrt (Cmf j i) - wfun i), Real.sq_sqrt (hCm_nn j i)]
      rwa [Real.sq_sqrt (hCm_nn j i)] at h1
    have hnn : ∀ i, 0 ≤ Real.sqrt (Cmf j i) * wfun i :=
      fun i => mul_nonneg (Real.sqrt_nonneg _) (hwfun_nn i)
    exact Summable.of_nonneg_of_le hnn hbound (((hCmf_summable j).add hw2_summable).div_const 2)
  have htermf_summable : ∀ a, Summable (termf a) := by
    intro a
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j _ => hsqrt_summable j)
  refine ⟨fun i => ∑ a ∈ Finset.range (k + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a _ => htermf_summable a)
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ ∞ (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ ∞ (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s := by
      refine (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i).comp contDiffOn_snd ?_
      intro p hp; exact hB hp.2
    have heqmode : eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i =
        (fun p : ℝ × E => φ i p.1) * (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) := by
      funext p; rw [eigenChartIncrementMode]; rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ) (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := k) (by exact_mod_cast le_top)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (k + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have hak : a ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)

    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le (φ i) (hφ_smooth i) hUD hT a q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (eigenSpatialFactor (I := I) (M := M) g α i' j' i) isOpen_interior
      (eigenSpatialFactor_contDiffOn (I := I) (M := M) g α i' j' i) hB hUD (k - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)

    have hfn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ := norm_nonneg _
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (k - a)
        (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (k.choose a : ℝ) := by positivity
    have hF1 := hfst_bnd
    have hG1 := hsnd_bnd

    have hsp_nn : 0 ≤ Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp :=
      mul_nonneg hCsp_nn (pow_nonneg hbase_nn _)
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (k - a)
            (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a)) := by
      refine mul_le_mul hF1 hG1 hgn_nn ?_
      positivity
    calc (k.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖
        = (k.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (k - a)
              (fun p : ℝ × E => eigenSpatialFactor (I := I) (M := M) g α i' j' i p.2) s q‖) := by ring
      _ ≤ (k.choose a : ℝ) * (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]

          have hcollapse : (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (k.choose a : ℝ) ≤ (2 : ℝ) ^ k := by
            calc (k.choose a : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.choose_le_two_pow k a
              _ = (2:ℝ) ^ k := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le hak
          have hfka : ((k-a).factorial : ℝ) ≤ (k.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) hak
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k :=
            pow_le_pow_right₀ (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)

          have hlhs_eq : (k.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((k - a).factorial : ℝ) * (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a))) =
              ((k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp) *
              (Ssqrt * ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-(((pSp : ℝ)) + (sW : ℝ))) *
                (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hcoef_nn : (0:ℝ) ≤ (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp := by positivity
            have hstep : (k.choose a : ℝ) * (a.factorial : ℝ) * ((k-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (k - a) * Csp ≤
                (2:ℝ) ^ k * (k.factorial : ℝ) * (k.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ k * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ k * Csp := by
              have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
              have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
              gcongr
            exact hstep
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

/-- **Pointwise eigen-series identity (analytic prerequisite P1).**  On the closed-time
slab over the chart-target interior, the Euclidean chart-Gram increment of `T_rep q.1`
equals the eigen-series of its per-mode increments.  This is the chart-level (pointwise)
convergence `T_rep t = ∑' i, φ i t • eigenvectorSmooth g 0 2 i` of the spectral partial
sums, paired with the additivity of `ccTensorBilinSymm` in its tensor argument.

This is now proved in full, assembled from public spectral API plus the single isolated
chart-`C⁰` convergence posit `spectralPartialSum_ccTensorBilinSymm_tendsto`:

* the `hmodemass` hypothesis (at time-jet order `0`) supplies, for each `σ ≥ 0`, the
  summable weighted coordinate squares of `(T_rep t).toL2`, hence the all-order `Hˢ`
  membership `hu` (`allHs_of_weighted_summable`), so the partial sums are all-order Cauchy;
* the spectral partial sum `spectralPartialSum g ((T_rep t).toL2) n = finiteEigenCombo` has
  symmetrized bilinear form equal to `∑_{i ∈ eigenIdxFinset n} φᵢ(t)·(per-mode increment)`
  (`ccTensorBilinSymm_finiteEigenCombo`, `hcoeff` identifying the coordinates as `φᵢ(t)`),
  i.e. the eigenIdxFinset partial sum of the eigen-series summands;
* the chart-`C⁰` convergence (`spectralPartialSum_ccTensorBilinSymm_tendsto`) gives the
  limit of these partial sums is the chart-Gram increment of `T_rep t`, while the per-mode
  summability (from the P2 compact-uniform majorant on a closed ball about `q.2`) gives
  `HasSum` of the eigen-series; composing the eigenIdxFinset exhaustion
  (`tendsto_eigenIdxFinset_atTop`) with `HasSum` and uniqueness of limits identifies the
  limit with the `∑'`. -/
private theorem realizedChartGramIncrement_eigenSeries_eq
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ∀ q ∈ Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target,
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2))
        = ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q := by
  classical
  rintro q ⟨hqt, hqy⟩
  set t : ℝ := q.1 with ht_def
  set x : M := (extChartAt I α).symm q.2 with hx_def
  set vv : TangentSpace I x := chartBasisVecFiber (I := I) α i' x with hvv
  set ww : TangentSpace I x := chartBasisVecFiber (I := I) α j' x with hww
  set u : TensorL2 0 2 g := SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t) with hu_def

  have hcoeff_t : ∀ i, tensorL2Coeff (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) u i = φ i t :=
    fun i => hcoeff t hqt i

  have hu : ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ vH : tensorHs (I := I) (M := M) g 0 2 σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := 0) (s := 2)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2) hσ vH = u := by
    refine allHs_of_weighted_summable (I := I) (M := M) g u (fun σ hσ => ?_)
    obtain ⟨Cmaj, hCmaj_sum, hCmaj⟩ := hmodemass 0 σ hσ
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hCmaj_sum
    · exact mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ) (sq_nonneg _)
    · have h := hCmaj i t hqt
      rw [iteratedDeriv_zero] at h
      rw [hcoeff_t i]
      exact h

  have hpartial : ∀ n,
      ccTensorBilinSymm (I := I) g (spectralPartialSum (I := I) (M := M) g u n) x vv ww =
        ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q := by
    intro n
    rw [spectralPartialSum, ccTensorBilinSymm_finiteEigenCombo]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcoeff_t i, eigenChartIncrementMode]

  have hTrep_u : (T_rep t : TensorL2 0 2 g) = u := by rw [hu_def, SmoothCcTensor.toL2_apply]
  have htend_lhs : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      Filter.atTop
      (𝓝 (ccTensorBilinSymm (I := I) g (T_rep t) x vv ww)) := by
    have h := spectralPartialSum_ccTensorBilinSymm_tendsto
      (I := I) (M := M) g u hu (T_rep t) hTrep_u x vv ww
    refine h.congr (fun n => (hpartial n))

  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open q.2 hqy
  set Bc : Set E := Metric.closedBall q.2 (r / 2) with hBc_def
  have hBc_sub : Bc ⊆ Ω := by
    intro z hz
    rw [hBc_def, Metric.mem_closedBall] at hz
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hBc_compact : IsCompact Bc := isCompact_closedBall q.2 (r / 2)
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall q.2 (by positivity : (r / 2) ≠ 0)]
    exact ⟨q.2, Metric.mem_ball_self (by positivity)⟩
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall q.2 (r / 2)) hBc_int_ne
  have hqBc : q.2 ∈ Bc := Metric.mem_closedBall_self (by positivity)
  have hqmemBc : q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc := ⟨hqt, hqBc⟩
  obtain ⟨v0, hv0_sum, hv0_bd⟩ :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g hT φ hφ_smooth hmodemass α i' j'
      hBc_compact huniqBc hBc_sub 0
  have hsummable : Summable (fun i =>
      eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q) := by
    refine Summable.of_norm_bounded hv0_sum (fun i => ?_)
    have hb := hv0_bd i q hqmemBc
    rwa [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
      (LinearIsometryEquiv.norm_map _ _)] at hb

  have hhasSum : HasSum
      (fun i => eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q) :=
    hsummable.hasSum
  have htend_tsum : Filter.Tendsto
      (fun n => ∑ i ∈ eigenIdxFinset (I := I) (M := M) g n,
          eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      Filter.atTop
      (𝓝 (∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)) :=
    hhasSum.comp (tendsto_eigenIdxFinset_atTop (I := I) (M := M) g)

  exact tendsto_nhds_unique htend_lhs htend_tsum

/-- **The realized chart-Gram increment is jointly `C^∞` in chart coordinates.**

For a smooth representative family `T_rep` whose `L²` eigen-coordinates at time `t`
are `φ i t` (`hcoeff`), with `φ` time-smooth (`hφ_smooth`) and equipped with summable
time-jet mode-mass (`hmodemass`), the chart-Gram *increment*
`ccTensorBilinSymm g (T_rep t) ((extChartAt α).symm y) (vᵢ') (vⱼ')`, pulled to a scalar
function of `(t, y) : ℝ × E`, is jointly `C^∞` on the closed-time slab
`Icc 0 T ×ˢ interior (extChartAt α).target`.

The increment is the eigen-series
`∑' i, φᵢ(t) · ccTensorBilinSymm g (bᵢ) ((extChartAt α).symm y) (vᵢ') (vⱼ')` of
jointly-`C^∞` per-mode terms (`eigenChartIncrementMode_contDiffOn`, equal to the increment
by `realizedChartGramIncrement_eigenSeries_eq`); joint `C^∞` is the closed-set `M`-test
series lemma `contDiffOn_tsum` applied per convex chart-ball
(`Icc 0 T ×ˢ B`, convex as a product), the `M`-test majorant supplied by
`eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant`, and glued over the open
ball cover of `interior (extChartAt α).target` by `contDiffOn_of_locally_contDiffOn`.

This assembles the spectral series joint smoothness; the genuine analytic content is the
chart-`C⁰` convergence `spectralPartialSum_ccTensorBilinSymm_tendsto` (proved in full via the
chart-frame fibre reconstruction and the POU-weighted chart-component limit identification);
the per-mode smoothness `eigenChartIncrementMode_contDiffOn`, the eigen-series identity
`realizedChartGramIncrement_eigenSeries_eq`, and the `M`-test majorant
`eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant` are all proved here in full.
The hypotheses `hφ_smooth`/`hcoeff`/`hmodemass` constrain it: a non-time-smooth `φ`, or one
without summable time-jet mode-mass, does not yield the joint `C^∞` increment. -/
theorem realizedChartGramIncrement_euclidean_contDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun q : ℝ × E =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
          (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
          (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)))
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  set Ω : Set E := interior (extChartAt I α).target with hΩ_def
  have hΩ_open : IsOpen Ω := isOpen_interior
  refine contDiffOn_of_locally_contDiffOn ?_
  rintro ⟨t₀, y₀⟩ hmem
  obtain ⟨_ht₀, hy₀⟩ := hmem
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hΩ_open y₀ hy₀

  refine ⟨Set.univ ×ˢ Metric.ball y₀ (r / 2), isOpen_univ.prod Metric.isOpen_ball,
    ⟨Set.mem_univ t₀, Metric.mem_ball_self (by positivity)⟩, ?_⟩
  set B : Set E := Metric.ball y₀ (r / 2) with hB_def
  set Bc : Set E := Metric.closedBall y₀ (r / 2) with hBc_def
  have hball_le : B ⊆ Bc := Metric.ball_subset_closedBall
  have hBc_sub : Bc ⊆ Ω := by
    intro x hx
    rw [hBc_def, Metric.mem_closedBall] at hx
    exact hball_sub (by rw [Metric.mem_ball]; linarith)
  have hB_sub : B ⊆ Ω := hball_le.trans hBc_sub
  have hBc_compact : IsCompact Bc := isCompact_closedBall y₀ (r / 2)
  have hslab_inter :
      (Set.Icc (0 : ℝ) T ×ˢ Ω) ∩ (Set.univ ×ˢ B) = Set.Icc (0 : ℝ) T ×ˢ B := by
    rw [Set.prod_inter_prod, Set.inter_univ, Set.inter_eq_right.mpr hB_sub]
  rw [hslab_inter]
  have hBc_int_ne : (interior Bc).Nonempty := by
    rw [hBc_def, interior_closedBall y₀ (by positivity : (r / 2) ≠ 0)]
    exact ⟨y₀, Metric.mem_ball_self (by positivity)⟩
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (convex_Icc (0 : ℝ) T).prod (convex_closedBall y₀ (r / 2))
  have huniqBc : UniqueDiffOn ℝ Bc :=
    uniqueDiffOn_convex (convex_closedBall y₀ (r / 2)) hBc_int_ne
  have huniq : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) T ×ˢ Bc) :=
    (uniqueDiffOn_Icc hT).prod huniqBc
  have hmajorant :=
    eigenChartIncrementMode_iteratedFDerivWithin_summable_majorant
      (I := I) (M := M) (T := T) g hT φ hφ_smooth hmodemass α i' j' hBc_compact huniqBc hBc_sub
  classical
  set v : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun k => Classical.choose (hmajorant k) with hv_def
  have hv_spec : ∀ k, Summable (v k) ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
        q ∈ Set.Icc (0 : ℝ) T ×ˢ Bc →
        ‖iteratedFDerivWithin ℝ k (eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i)
            (Set.Icc (0 : ℝ) T ×ˢ Bc) q‖ ≤ v k i :=
    fun k => Classical.choose_spec (hmajorant k)
  have htsum_Bc : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ Bc) := by
    refine DifferentialGeometry.Analysis.contDiffOn_tsum (v := v) (x₀ := (0, y₀))
      huniq hconv
      (fun i => (eigenChartIncrementMode_contDiffOn (I := I) (M := M) (T := T)
        g φ hφ_smooth α i' j' i).mono (Set.prod_mono (le_refl _) hBc_sub))
      (fun k _hk => (hv_spec k).1)
      (fun k i q hq _hk => (hv_spec k).2 i q hq)
      ⟨left_mem_Icc.mpr hT.le, Metric.mem_closedBall_self (by positivity)⟩
  have htsum : ContDiffOn ℝ ∞
      (fun q : ℝ × E => ∑' i, eigenChartIncrementMode (I := I) (M := M) g φ α i' j' i q)
      (Set.Icc (0 : ℝ) T ×ˢ B) :=
    htsum_Bc.mono (Set.prod_mono (le_refl _) hball_le)
  refine htsum.congr ?_
  intro q hq
  have hq' : q ∈ Set.Icc (0 : ℝ) T ×ˢ Ω := ⟨hq.1, hB_sub hq.2⟩
  exact realizedChartGramIncrement_eigenSeries_eq (I := I) (M := M) (T := T)
    g hT T_rep φ hφ_smooth hcoeff hmodemass α i' j' q hq'

/-- The realized chart-Gram increment, along the moving chart point, is jointly `C^∞` on
the closed-time slab over the trivialization base set: the Euclidean increment scalar (a
function on `ℝ × E`, supplied by `realizedChartGramIncrement_euclidean_contDiffOn`) is
composed with the smooth moving `(t, x) ↦ (t, extChartAt α x)`, carried pointwise through
the single normed-space model to avoid the product-model defeq blow-up. -/
private theorem realizedChartGramIncrement_alongChart_contMDiffOn
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (i' j' : Fin (Module.finrank ℝ E)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
  set G : ℝ × E → ℝ :=
    fun q : ℝ × E =>
      ccTensorBilinSymm (I := I) g (T_rep q.1) ((extChartAt I α).symm q.2)
        (chartBasisVecFiber (I := I) α i' ((extChartAt I α).symm q.2))
        (chartBasisVecFiber (I := I) α j' ((extChartAt I α).symm q.2)) with hG_def
  have hGEuclid : ContDiffOn ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    realizedChartGramIncrement_euclidean_contDiffOn
      (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i' j'
  set f : ℝ × M → ℝ × E := fun q : ℝ × M => (q.1, extChartAt I α q.2) with hf_def
  have hf_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞ f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    refine ContMDiffOn.prodMk_space contMDiffOn_fst ?_
    refine (contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)).comp contMDiffOn_snd ?_
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    exact hx
  have hmaps : Set.MapsTo f
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    refine ⟨ht, ?_⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    have hmem : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hx'
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  have heq : Set.EqOn
      (fun q : ℝ × M =>
        ccTensorBilinSymm (I := I) g (T_rep q.1) q.2
          (chartBasisVecFiber (I := I) α i' q.2)
          (chartBasisVecFiber (I := I) α j' q.2))
      (G ∘ f)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    rintro ⟨t, x⟩ ⟨_, hx⟩
    rw [Integral.Measure.trivializationAt_baseSet_eq_chartAt_source (I := I)] at hx
    have hx' : x ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hx
    simp only [Function.comp, hG_def, hf_def]
    rw [(extChartAt I α).left_inv hx']
  intro q hq
  refine (ContMDiffWithinAt.congr ?_ (fun y hy => heq hy) (heq hq))
  have hGf : ContDiffWithinAt ℝ ∞ G
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) (f q) :=
    hGEuclid.contDiffWithinAt (hmaps hq)
  exact hGf.comp_contMDiffWithinAt (hf_smooth q hq) hmaps

/-- **Joint chart-Gram smoothness of a realized time-smooth spectral family
(the corrected interior-smoothing regularity bedrock).**

Let `g` be a closed Riemannian metric, `T_rep : ℝ → SmoothCcTensor g 0 2` a family of
`C^∞` representatives, uniformly `g`-fibre small with a single constant `δ < 1`
(`hδ_lt`, `hδ`), and suppose

* `φ` is a genuinely **time-smooth** eigen-coordinate family (`hφ_smooth`) realizing the
  `L²` eigen-coordinates of `T_rep` (`hcoeff`); and
* `hmodemass`: every time-jet of the weighted coordinate squares admits a single,
  `t`-independent, summable-across-modes majorant on `[0,T]` — the consumer-facing
  conclusion shape produced by `perModeConv_allOrder_timeDeriv_spectralMass_le`.

Then the chart-Gram matrix entries of the realized metric family
`g_DT t = tensorSectionRealizeMetric g (T_rep t) hδ_lt (hδ t)` are jointly `C^∞` up to
`t = 0`: `JointChartGramSmooth T g_DT`.

This is the corrected form of `jointChartGramSmooth_of_spectralSmooth_timeContinuous`
(whose `L²`-time-*continuity* hypothesis is too weak — `T_rep t = |t| · S₀`
counterexample): time *smoothness* of the eigen-coordinates with summable time-jet
mode-mass is what makes the chart-Gram limit jointly `C^∞`.

The chart-Gram entry of the realized metric is affine in `T_rep t`; the time-constant
background part is smooth (`chartGramMatrix_entry_contMDiffOn`), and the increment is
jointly `C^∞` in chart coordinates (`realizedChartGramIncrement_euclidean_contDiffOn`,
the spectral series joint smoothness), pushed back through the smooth moving chart point.
This is proved in full: `#print axioms` is `[propext, Classical.choice, Quot.sound]`. -/
theorem jointChartGramSmooth_of_spectralSmooth_timeSmooth
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (T_rep : ℝ → SmoothCcTensor g 0 2) {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : ∀ t : ℝ, gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (T_rep t)) δ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcoeff : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
        tensorL2Coeff (I := I) (M := M)
            (tensorResolventL2_isCompactOperator (I := I) (M := M) g 0 2)
            (SmoothCcTensor.toL2 (g := g) (r := 0) (s := 2) (T_rep t)) i = φ i t)
    (hmodemass : ∀ (k : ℕ) (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv k (φ i) t) ^ 2 ≤ Cmaj i) :
    JointChartGramSmooth (I := I) T
      (fun t : ℝ => tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) := by
  intro α i j
  have hincrement := realizedChartGramIncrement_alongChart_contMDiffOn
    (I := I) (M := M) g hT T_rep φ hφ_smooth hcoeff hmodemass α i j
  have hbg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
      (fun p : ℝ × M =>
        Integral.Measure.chartGramMatrix (I := I) g α p.2 i j)
      (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) := by
    have hbase := chartGramMatrix_entry_contMDiffOn (I := I) g α i j
    have hsnd : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
      contMDiffOn_snd
    have hmaps : Set.MapsTo (fun p : ℝ × M => p.2)
        (Set.Icc (0 : ℝ) T ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)
        (trivializationAt E (TangentSpace I) α).baseSet :=
      fun p hp => hp.2
    exact hbase.comp hsnd hmaps
  refine (hbg.add hincrement).congr ?_
  rintro ⟨t, x⟩ _
  change Integral.Measure.chartGramMatrix (I := I)
      (tensorSectionRealizeMetric (I := I) g (T_rep t) hδ_lt (hδ t)) α x i j =
    Integral.Measure.chartGramMatrix (I := I) g α x i j +
      ccTensorBilinSymm (I := I) g (T_rep t) x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x)
  rw [chartGramMatrix_apply, chartGramMatrix_apply,
    tensorSectionRealizeMetric_inner]

section FiniteOrderEigenSeries

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral (eigenvectorSmooth
  tensorChartComponentRaw tensorChartComponentRaw_add tensorChartComponentRaw_smul
  tensorChartComponentProjection tensorChartBasisElement
  toEuclidean_extChartAt_mem_chartTargetEuclid)

private local instance tensorRSModel02NormedAddCommGroup_local :
    NormedAddCommGroup (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup 0 2

private local instance tensorRSModel02NormedSpace_local :
    NormedSpace ℝ (Tensor0SBundle.TensorRSModel 0 2 ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace 0 2

omit [BoundarylessManifold I M] in
private lemma weight_two_rpow_eq_sq (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) :
    tensorSobolevWeight (I := I) (M := M) i (2 * pp)
      = ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp) ^ 2 := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  unfold tensorSobolevWeight
  rw [show (2 : ℝ) * pp = pp * 2 by ring, Real.rpow_mul hbase_pos.le, Real.rpow_two]

omit [BoundarylessManifold I M] in
lemma abs_le_sqrt_of_weight_sq_le (g : SmoothRiemannianMetric I M)
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) (pp : ℝ) {v C : ℝ}
    (h : tensorSobolevWeight (I := I) (M := M) i (2 * pp) * v ^ 2 ≤ C) :
    |v| ≤ Real.sqrt C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-pp) := by
  have hbase_pos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hw := weight_two_rpow_eq_sq (I := I) (M := M) g i pp
  rw [hw] at h
  set W : ℝ := (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pp with hW_def
  have hW_pos : 0 < W := Real.rpow_pos_of_pos hbase_pos _
  have hC_nn : 0 ≤ C := le_trans (by positivity) h
  have habs : |v| ≤ Real.sqrt C / W := by
    rw [le_div_iff₀ hW_pos]
    have h2 : (|v| * W) ^ 2 ≤ (Real.sqrt C) ^ 2 := by
      rw [Real.sq_sqrt hC_nn, mul_pow, sq_abs]
      nlinarith [h, hW_pos.le]
    have hlhs_nn : 0 ≤ |v| * W := by positivity
    nlinarith [Real.sqrt_nonneg C, h2, hlhs_nn,
      sq_nonneg (|v| * W - Real.sqrt C)]
  rw [Real.rpow_neg hbase_pos.le]
  rw [div_eq_mul_inv] at habs
  rwa [← hW_def]

omit [BoundarylessManifold I M] in
lemma summable_sqrt_mul_weight_neg (g : SmoothRiemannianMetric I M)
    (Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (hCm : Summable Cm)
    (hCm_nn : ∀ i, 0 ≤ Cm i) {sW : ℝ} (hsW : ((weylSobolevExp (E := E) : ℕ) : ℝ) < sW) :
    Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)) := by
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hweyl : Summable (fun i : TensorEigenIdx (I := I) (M := M) g 0 2 =>
      tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) := by
    refine tensorEigen_summable_negpow (I := I) (M := M) g (2 * sW) ?_
    have h0 : (0 : ℝ) ≤ ((weylSobolevExp (E := E) : ℕ) : ℝ) := by positivity
    nlinarith [h0]
  have hw_sq : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2
        = tensorSobolevWeight (I := I) (M := M) i (-(2 * sW)) := by
    intro i
    unfold tensorSobolevWeight
    rw [← Real.rpow_natCast ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-sW)) 2,
      ← Real.rpow_mul (hbase_pos i).le]
    congr 1; push_cast; ring
  have hbound : ∀ i, Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
      ≤ (Cm i + tensorSobolevWeight (I := I) (M := M) i (-(2 * sW))) / 2 := by
    intro i
    have h1 : Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW)
        ≤ (Real.sqrt (Cm i) ^ 2 + tensorSobolevWeight (I := I) (M := M) i (-sW) ^ 2) / 2 := by
      nlinarith [sq_nonneg (Real.sqrt (Cm i) - tensorSobolevWeight (I := I) (M := M) i (-sW)),
        Real.sq_sqrt (hCm_nn i)]
    rw [Real.sq_sqrt (hCm_nn i), hw_sq i] at h1
    exact h1
  have hnn : ∀ i, 0 ≤ Real.sqrt (Cm i) * tensorSobolevWeight (I := I) (M := M) i (-sW) :=
    fun i => mul_nonneg (Real.sqrt_nonneg _)
      (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  exact Summable.of_nonneg_of_le hnn hbound ((hCm.add hweyl).div_const 2)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma norm_iteratedFDerivWithin_compFst_le_ofOrder
    (kk : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ (kk : ℕ) f) {a bb : ℝ} {B : Set E}
    (hUD : UniqueDiffOn ℝ (Set.Icc a bb ×ˢ B)) (hab : a < bb)
    (n : ℕ) (hn : n ≤ kk) (q : ℝ × E) (hq : q ∈ Set.Icc a bb ×ˢ B)
    (C : ℝ) (hC : ∀ j ≤ n, ‖iteratedDeriv j f q.1‖ ≤ C) :
    ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => f p.1) (Set.Icc a bb ×ˢ B) q‖ ≤
      (n.factorial : ℝ) * C * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n := by
  classical
  set s := Set.Icc a bb ×ˢ B with hs_def
  set t := Set.Icc a bb with ht_def
  set L : (ℝ × E) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E with hL_def
  have hUDt : UniqueDiffOn ℝ t := uniqueDiffOn_Icc hab
  have hmaps : Set.MapsTo (fun p : ℝ × E => p.1) s t := fun p hp => hp.1
  have hbound := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (g := f)
    (f := fun p : ℝ × E => p.1) (n := n) (s := s) (t := t) (x := q)
    (N := ((kk : ℕ) : WithTop ℕ∞))
    hf.contDiffOn contDiffOn_fst (by exact_mod_cast hn) hUDt hUD hmaps hq
    (C := C) (D := ‖L‖ + 1)
    (fun i hi => by
      have heq : iteratedFDerivWithin ℝ i f t q.1 = iteratedFDeriv ℝ i f q.1 :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUDt
          (hf.contDiffAt.of_le (by exact_mod_cast le_trans hi hn)) (hmaps hq)
      rw [heq, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC i hi)
    (fun i hi1 hin => by
      have hwithin : iteratedFDerivWithin ℝ i (fun p : ℝ × E => p.1) s q =
          iteratedFDeriv ℝ i (fun p : ℝ × E => p.1) q :=
        iteratedFDerivWithin_eq_iteratedFDeriv hUD
          ((contDiff_fst (𝕜 := ℝ)).contDiffAt.of_le (by exact_mod_cast le_top)) hq
      rw [hwithin]
      exact norm_iteratedFDeriv_clm_le L i hi1 q)
  have hcomp : (f ∘ (fun p : ℝ × E => p.1)) = (fun p : ℝ × E => f p.1) := rfl
  rw [hcomp] at hbound
  exact hbound

set_option maxHeartbeats 1600000 in
private lemma exists_rawCompOnE_eigen_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ)
    {B : Set E} (hB_compact : IsCompact B) (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  set kE : ℕ := Module.finrank ℝ E + 2 * m + 1 with hkE_def
  obtain ⟨Cdec, hCdec_nn, hCdec⟩ :=
    eigenvectorSmooth_toHs_norm_le_lambda_pow (I := I) (M := M) g kE
  have hper : ∀ m' : ℕ, m' ≤ m → ∃ Cm' : ℝ, 0 ≤ Cm' ∧
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖ ≤
          Cm' * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
    intro m' hm'
    have h_super : 2 * kE > Module.finrank ℝ E + 2 * m' := by rw [hkE_def]; omega
    obtain ⟨Cj, hCj_nn, hCj⟩ :=
      exists_rawCompOnE_jet_le_toHs_on_compact (I := I) (M := M) g α Jdx m' kE h_super
        hB_compact hB
    refine ⟨Cj * Cdec, by positivity, fun i y hy => ?_⟩
    have h1 := hCj (eigenvectorSmooth (I := I) (M := M) g 0 2 i) y hy
    have h2 := hCdec i
    have hbase_nn : (0 : ℝ) ≤ (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by
      have := tensor_lambda_nonneg (I := I) (M := M) i; positivity
    calc ‖iteratedFDerivWithin ℝ m' (rawCompOnE (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
            (interior (extChartAt I α).target) y‖
        ≤ Cj * ‖SmoothCcTensor.toHs (g := g) (r := 0) (s := 2) (2 * kE)
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i)‖ := h1
      _ ≤ Cj * (Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE)) :=
          mul_le_mul_of_nonneg_left h2 hCj_nn
      _ = Cj * Cdec * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (2 * kE) := by ring
  choose Cf hCf_nn hCf using hper
  set Cmax : ℝ := (Finset.range (m + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero m))
    (fun b => if hb : b ≤ m then Cf b hb else 0) with hCmax_def
  have hCmax_ge : ∀ (m' : ℕ) (h : m' ≤ m), Cf m' h ≤ Cmax := by
    intro m' h
    rw [hCmax_def]
    refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun b => if hb : b ≤ m then Cf b hb else 0)
      (Finset.mem_range.mpr (by omega : m' < m + 1)))
    rw [dif_pos h]
  refine ⟨Cmax, 2 * kE, ?_, fun m' hm' i y hy => ?_⟩
  · exact le_trans (hCf_nn 0 (Nat.zero_le m)) (hCmax_ge 0 (Nat.zero_le m))
  · refine le_trans (hCf m' hm' i y hy) ?_
    refine mul_le_mul_of_nonneg_right (hCmax_ge m' hm') ?_
    have := tensor_lambda_nonneg (I := I) (M := M) i; positivity

def eigenRawIncrementMode
    (g : SmoothRiemannianMetric I M)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) : ℝ × E → ℝ :=
  fun q : ℝ × E =>
    φ i q.1 * rawCompOnE (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx q.2

lemma eigenRawIncrementMode_contDiffOn_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
    ContDiffOn ℝ (kk : ℕ) (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) := by
  have htime : ContDiffOn ℝ (kk : ℕ) (fun q : ℝ × E => φ i q.1)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
  have hspace : ContDiffOn ℝ (kk : ℕ)
      (fun q : ℝ × E => rawCompOnE (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx q.2)
      (Set.Icc (0 : ℝ) T ×ˢ interior (extChartAt I α).target) :=
    ((rawCompOnE_contDiffOn (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx).of_le
      (by exact_mod_cast le_top)).comp contDiffOn_snd (Set.mapsTo_snd_prod)
  exact htime.mul hspace

set_option maxHeartbeats 1600000 in
theorem eigenRawIncrementMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ Cmaj i)
    (α : M) (Jdx : Fin 2 → Fin (Module.finrank ℝ E))
    {B : Set E} (hB_compact : IsCompact B) (hB_uniq : UniqueDiffOn ℝ B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∀ n : ℕ, n ≤ kk →
      ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
          q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
          ‖iteratedFDerivWithin ℝ n (eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i)
              (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro n hn
  set O : Set E := interior (extChartAt I α).target with hO_def
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq
  obtain ⟨Csp, pSp, hCsp_nn, hCsp⟩ :=
    exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M) g α Jdx n hB_compact hB
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  set σ0 : ℝ := 2 * ((pSp : ℝ) + (sW : ℝ)) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      a ≤ kk → Summable Cm ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i := by
    intro a
    by_cases ha : a ≤ kk
    · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
      exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose Cmf hCmf using htime
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hCm_nn : ∀ (a : ℕ), a ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a ha i
    have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  have htime_pt : ∀ (j : ℕ), j ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) := by
    intro j hj i t ht
    exact abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pSp : ℝ) + (sW : ℝ))
      (by rw [← hσ0_def]; exact (hCmf j hj).2 i t ht)
  set Kconst : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hsqrt_summable : ∀ j : ℕ, j ≤ kk →
      Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j hj
    exact summable_sqrt_mul_weight_neg (I := I) (M := M) g (Cmf j) (hCmf j hj).1
      (hCm_nn j hj) hsW_gt
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i)
    with htermf_def
  have htermf_summable : ∀ a : ℕ, a ≤ kk → Summable (termf a) := by
    intro a ha
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j hj => hsqrt_summable j
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ha))
  refine ⟨fun i => ∑ a ∈ Finset.range (n + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a ha => htermf_summable a
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hn))
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ (kk : ℕ)
        (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s := by
      refine (((rawCompOnE_contDiffOn (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx).of_le
        (by exact_mod_cast le_top)).comp contDiffOn_snd ?_)
      intro p hp; exact hB hp.2
    have heqmode : eigenRawIncrementMode (I := I) (M := M) g φ α Jdx i =
        (fun p : ℝ × E => φ i p.1) *
          (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) := by
      funext p; rw [eigenRawIncrementMode]; rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ)
      (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := n) (by exact_mod_cast hn)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (n + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hak : a ≤ kk := le_trans han hn
    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ)))
      with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le_ofOrder
      kk (φ i) (hφ_smooth i) hUD hT a hak q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj (le_trans hjj hak) i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (rawCompOnE (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) isOpen_interior
      (rawCompOnE_contDiffOn (I := I) (M := M) g
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) hB hUD (n - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (n - a)
        (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (n.choose a : ℝ) := by positivity
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (n - a)
            (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((n - a).factorial : ℝ) *
            (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a)) := by
      refine mul_le_mul hfst_bnd hsnd_bnd hgn_nn ?_
      positivity
    calc (n.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a)
              (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖
        = (n.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a)
              (fun p : ℝ × E => rawCompOnE (I := I) (M := M) g
                (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx p.2) s q‖) := by ring
      _ ≤ (n.choose a : ℝ) *
            (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((n - a).factorial : ℝ) *
              (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]
          have hcollapse :
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (n.choose a : ℝ) ≤ (2 : ℝ) ^ n := by
            calc (n.choose a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                  exact_mod_cast Nat.choose_le_two_pow n a
              _ = (2:ℝ) ^ n := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le han
          have hfka : ((n-a).factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) han
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)
          have hlhs_eq : (n.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((n - a).factorial : ℝ) *
                (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) =
              ((n.choose a : ℝ) * (a.factorial : ℝ) * ((n-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) * Csp) *
              (Ssqrt *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ))) *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
            have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
            gcongr
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

lemma exists_rawComponentRaw_eigen_pointwise_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
        |tensorChartComponentRaw (I := I) (M := M) g 0 2
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx x| ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  have hx' : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source (I := I)]; exact hx
  set y : E := extChartAt I α x with hy_def
  have hy_int : y ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source hx'
  obtain ⟨C, p, hC_nn, hC⟩ := exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M)
    g α Jdx 0 isCompact_singleton (Set.singleton_subset_iff.mpr hy_int)
  refine ⟨C, p, hC_nn, fun i => ?_⟩
  have h0 := hC 0 le_rfl i y (Set.mem_singleton y)
  rw [iteratedFDerivWithin_zero_eq_comp, Function.comp_apply,
    LinearIsometryEquiv.norm_map] at h0
  have heq : rawCompOnE (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx y =
      tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α ![] Jdx
        ((extChartAt I α).symm y) := rfl
  have hxy : (extChartAt I α).symm y = x := (extChartAt I α).left_inv hx'
  rw [heq, hxy, Real.norm_eq_abs] at h0
  exact h0

lemma tensorChartComponentRaw_finiteEigenCombo
    (g : SmoothRiemannianMetric I M)
    (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
    (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ) (α : M)
    (Idx : Fin 0 → Fin (Module.finrank ℝ E))
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (x : M) :
    tensorChartComponentRaw (I := I) (M := M) g 0 2
        (finiteEigenCombo (I := I) (M := M) g F c) α Idx Jdx x =
      ∑ i ∈ F, c i * tensorChartComponentRaw (I := I) (M := M) g 0 2
        (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Idx Jdx x := by
  classical
  rw [finiteEigenCombo_eq]
  induction F using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h0 : (0 : SmoothCcTensor g 0 2) = (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := by
        rw [zero_smul]
      rw [h0, tensorChartComponentRaw_smul (I := I) (M := M)]
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        tensorChartComponentRaw_add (I := I) (M := M),
        tensorChartComponentRaw_smul (I := I) (M := M), ih]
      simp [smul_eq_mul]

lemma pdIter_rawCompOnE_contDiffOn
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (L : List E) :
    ContDiffOn ℝ ∞
      (DifferentialGeometry.Analysis.pdIter L (rawCompOnE (I := I) (M := M) g S α Jdx))
      (interior (extChartAt I α).target) :=
  DifferentialGeometry.Analysis.pdIter_contDiffOn isOpen_interior
    (rawCompOnE_contDiffOn (I := I) (M := M) g S α Jdx) L

lemma exists_pdIter_rawCompOnE_eigen_jet_le_lambda_pow
    (g : SmoothRiemannianMetric I M) (α : M)
    (Jdx : Fin 2 → Fin (Module.finrank ℝ E)) (m : ℕ) (L : List E)
    {B : Set E} (hB_compact : IsCompact B)
    (hB : B ⊆ interior (extChartAt I α).target) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧
      ∀ (m' : ℕ), m' ≤ m → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ y ∈ B,
        ‖iteratedFDerivWithin ℝ m'
            (DifferentialGeometry.Analysis.pdIter L (rawCompOnE (I := I) (M := M) g
              (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx))
            (interior (extChartAt I α).target) y‖ ≤
          C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by
  classical
  obtain ⟨C, p, hC_nn, hC⟩ := exists_rawCompOnE_eigen_jet_le_lambda_pow (I := I) (M := M)
    g α Jdx (m + L.length) hB_compact hB
  set Cnorm : ℝ := (L.map (fun v => ‖v‖)).prod with hCnorm_def
  have hCnorm_nn : 0 ≤ Cnorm := List.prod_nonneg (by
    intro a ha
    simp only [List.mem_map] at ha
    obtain ⟨w, _, hw⟩ := ha
    rw [← hw]; exact norm_nonneg w)
  refine ⟨Cnorm * C, p, by positivity, fun m' hm' i y hy => ?_⟩
  have h1 := DifferentialGeometry.Analysis.norm_iteratedFDerivWithin_pdIter_le
    isOpen_interior (rawCompOnE_contDiffOn (I := I) (M := M) g
      (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx) L (hB hy) m'
  have h2 := hC (m' + L.length) (by omega) i y hy
  calc ‖iteratedFDerivWithin ℝ m'
        (DifferentialGeometry.Analysis.pdIter L (rawCompOnE (I := I) (M := M) g
          (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx))
        (interior (extChartAt I α).target) y‖
      ≤ Cnorm * ‖iteratedFDerivWithin ℝ (m' + L.length)
          (rawCompOnE (I := I) (M := M) g
            (eigenvectorSmooth (I := I) (M := M) g 0 2 i) α Jdx)
          (interior (extChartAt I α).target) y‖ := h1
    _ ≤ Cnorm * (C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p) :=
        mul_le_mul_of_nonneg_left h2 hCnorm_nn
    _ = Cnorm * C * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ p := by ring

set_option maxHeartbeats 1600000 in
theorem eigenTimeSpatialProductMode_iteratedFDerivWithin_summable_majorant_ofOrder
    (g : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T) (kk : ℕ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hφ_smooth : ∀ i, ContDiff ℝ (kk : ℕ) (φ i))
    (hmodemass : ∀ (j : ℕ), j ≤ kk → ∀ (σ : ℝ), 0 ≤ σ →
      ∃ Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable Cmaj ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ *
              (iteratedDeriv j (φ i) t) ^ 2 ≤ Cmaj i)
    (ψ : TensorEigenIdx (I := I) (M := M) g 0 2 → E → ℝ)
    {O : Set E} (hO_open : IsOpen O)
    (hψ_smooth : ∀ i, ContDiffOn ℝ ∞ (ψ i) O)
    {B : Set E} (hB_uniq : UniqueDiffOn ℝ B) (hBO : B ⊆ O)
    (Csp : ℝ) (pSp : ℕ) (hCsp_nn : 0 ≤ Csp)
    (hCsp : ∀ (n : ℕ), n ≤ kk → ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2),
      ∀ y ∈ B, ‖iteratedFDerivWithin ℝ n (ψ i) O y‖ ≤
        Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) :
    ∀ n : ℕ, n ≤ kk →
      ∃ v : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ, Summable v ∧
        ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2) (q : ℝ × E),
          q ∈ Set.Icc (0 : ℝ) T ×ˢ B →
          ‖iteratedFDerivWithin ℝ n (fun p : ℝ × E => φ i p.1 * ψ i p.2)
              (Set.Icc (0 : ℝ) T ×ˢ B) q‖ ≤ v i := by
  classical
  intro n hn
  set s : Set (ℝ × E) := Set.Icc (0 : ℝ) T ×ˢ B with hs_def
  have hUD : UniqueDiffOn ℝ s := (uniqueDiffOn_Icc hT).prod hB_uniq
  set sW : ℕ := weylSobolevExp (E := E) + 1 with hsW_def
  have hsW_gt : ((weylSobolevExp (E := E) : ℕ) : ℝ) < (sW : ℝ) := by
    rw [hsW_def]; push_cast; linarith
  set σ0 : ℝ := 2 * ((pSp : ℝ) + (sW : ℝ)) with hσ0_def
  have hσ0_nn : (0 : ℝ) ≤ σ0 := by rw [hσ0_def]; positivity
  have htime : ∀ a : ℕ, ∃ Cm : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ,
      a ≤ kk → Summable Cm ∧
        ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
          tensorSobolevWeight (I := I) (M := M) i σ0 * (iteratedDeriv a (φ i) t) ^ 2 ≤ Cm i := by
    intro a
    by_cases ha : a ≤ kk
    · obtain ⟨Cm, h1, h2⟩ := hmodemass a ha σ0 hσ0_nn
      exact ⟨Cm, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h ha⟩
  choose Cmf hCmf using htime
  have hbase_pos : ∀ i : TensorEigenIdx (I := I) (M := M) g 0 2,
      (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i := fun i => by
    have := tensor_lambda_nonneg (I := I) (M := M) i; linarith
  have hCm_nn : ∀ (a : ℕ), a ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), 0 ≤ Cmf a i := by
    intro a ha i
    have h := (hCmf a ha).2 i 0 (Set.left_mem_Icc.mpr hT.le)
    have hw := tensorSobolevWeight_pos (I := I) (M := M) i σ0
    nlinarith [sq_nonneg (iteratedDeriv a (φ i) 0), hw.le, h]
  have htime_pt : ∀ (j : ℕ), j ≤ kk →
      ∀ (i : TensorEigenIdx (I := I) (M := M) g 0 2), ∀ t ∈ Set.Icc (0 : ℝ) T,
      |iteratedDeriv j (φ i) t| ≤
        Real.sqrt (Cmf j i) *
          (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) := by
    intro j hj i t ht
    exact abs_le_sqrt_of_weight_sq_le (I := I) (M := M) g i ((pSp : ℝ) + (sW : ℝ))
      (by rw [← hσ0_def]; exact (hCmf j hj).2 i t ht)
  set Kconst : ℝ := (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
    (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n * (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n *
    Csp with hKconst_def
  have hKconst_nn : 0 ≤ Kconst := by rw [hKconst_def]; positivity
  set wfun : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) with hwfun_def
  have hwfun_nn : ∀ i, 0 ≤ wfun i := fun i => by
    rw [hwfun_def]; exact (tensorSobolevWeight_nonneg (I := I) (M := M) i _)
  have hsqrt_summable : ∀ j : ℕ, j ≤ kk →
      Summable (fun i => Real.sqrt (Cmf j i) * wfun i) := by
    intro j hj
    exact summable_sqrt_mul_weight_neg (I := I) (M := M) g (Cmf j) (hCmf j hj).1
      (hCm_nn j hj) hsW_gt
  set termf : ℕ → TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun a i => Kconst * ((∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i)
    with htermf_def
  have htermf_summable : ∀ a : ℕ, a ≤ kk → Summable (termf a) := by
    intro a ha
    refine Summable.mul_left Kconst ?_
    have heq : (fun i => (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) * wfun i) =
        (fun i => ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) * wfun i) := by
      funext i; rw [Finset.sum_mul]
    rw [heq]
    exact summable_sum (fun j hj => hsqrt_summable j
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) ha))
  refine ⟨fun i => ∑ a ∈ Finset.range (n + 1), termf a i, ?_, ?_⟩
  · exact summable_sum (fun a ha => htermf_summable a
      (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)) hn))
  · intro i q hq
    have hqt : q.1 ∈ Set.Icc (0 : ℝ) T := hq.1
    have hqB : q.2 ∈ B := hq.2
    have hbase_nn : (0 : ℝ) ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
      (hbase_pos i).le
    have hcd_fst : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => φ i p.1) s :=
      ((hφ_smooth i).contDiffOn).comp contDiffOn_fst (Set.mapsTo_fst_prod)
    have hcd_snd : ContDiffOn ℝ (kk : ℕ) (fun p : ℝ × E => ψ i p.2) s := by
      refine ((hψ_smooth i).of_le (by exact_mod_cast le_top)).comp contDiffOn_snd ?_
      intro p hp; exact hBO hp.2
    have heqmode : (fun p : ℝ × E => φ i p.1 * ψ i p.2) =
        (fun p : ℝ × E => φ i p.1) * (fun p : ℝ × E => ψ i p.2) := rfl
    rw [heqmode]
    have hleib := norm_iteratedFDerivWithin_mul_le (𝕜 := ℝ)
      (f := fun p : ℝ × E => φ i p.1)
      (g := fun p : ℝ × E => ψ i p.2)
      hcd_fst hcd_snd hUD (x := q) hq (n := n) (by exact_mod_cast hn)
    refine le_trans hleib ?_
    change _ ≤ ∑ a ∈ Finset.range (n + 1), termf a i
    refine Finset.sum_le_sum (fun a ha => ?_)
    have han : a ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hak : a ≤ kk := le_trans han hn
    set Cφa : ℝ := (∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i)) *
      (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ)))
      with hCφa_def
    have hCφa_nn : 0 ≤ Cφa := by
      rw [hCφa_def]
      exact mul_nonneg (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
        (Real.rpow_nonneg hbase_nn _)
    have hfst_bnd := norm_iteratedFDerivWithin_compFst_le_ofOrder
      kk (φ i) (hφ_smooth i) hUD hT a hak q hq Cφa
      (fun jj hjj => by
        rw [Real.norm_eq_abs]
        refine le_trans (htime_pt jj (le_trans hjj hak) i q.1 hqt) ?_
        rw [hCφa_def]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hbase_nn _)
        refine Finset.single_le_sum (f := fun j => Real.sqrt (Cmf j i))
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (by omega)))
    have hsnd_bnd := norm_iteratedFDerivWithin_compSnd_le
      (ψ i) hO_open (hψ_smooth i) hBO hUD (n - a) q hq
      (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)
      (fun jj hjj => hCsp jj (by omega) i q.2 hqB)
    have hgn_nn : (0:ℝ) ≤ ‖iteratedFDerivWithin ℝ (n - a)
        (fun p : ℝ × E => ψ i p.2) s q‖ := norm_nonneg _
    have hchoose_nn : (0:ℝ) ≤ (n.choose a : ℝ) := by positivity
    have hprod : ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
          ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖ ≤
        ((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
          (((n - a).factorial : ℝ) *
            (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
            (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a)) := by
      refine mul_le_mul hfst_bnd hsnd_bnd hgn_nn ?_
      positivity
    calc (n.choose a : ℝ) * ‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖
        = (n.choose a : ℝ) * (‖iteratedFDerivWithin ℝ a (fun p : ℝ × E => φ i p.1) s q‖ *
            ‖iteratedFDerivWithin ℝ (n - a) (fun p : ℝ × E => ψ i p.2) s q‖) := by ring
      _ ≤ (n.choose a : ℝ) *
            (((a.factorial : ℝ) * Cφa * (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
            (((n - a).factorial : ℝ) *
              (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) :=
          mul_le_mul_of_nonneg_left hprod hchoose_nn
      _ ≤ termf a i := by
          simp only [htermf_def, hCφa_def, hKconst_def, hwfun_def]
          have hcollapse :
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ (-((pSp : ℝ) + (sW : ℝ))) *
              (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp =
              tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ)) := by
            unfold tensorSobolevWeight
            rw [← Real.rpow_natCast (1 + TensorEigenIdx.lambda (I := I) (M := M) i) pSp,
              ← Real.rpow_add (hbase_pos i)]
            congr 1; ring
          set Ssqrt : ℝ := ∑ j ∈ Finset.range (a + 1), Real.sqrt (Cmf j i) with hSs_def
          have hSs_nn : 0 ≤ Ssqrt := Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _)
          have hbinom : (n.choose a : ℝ) ≤ (2 : ℝ) ^ n := by
            calc (n.choose a : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
                  exact_mod_cast Nat.choose_le_two_pow n a
              _ = (2:ℝ) ^ n := by push_cast; ring
          have hfa : (a.factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le han
          have hfka : ((n-a).factorial : ℝ) ≤ (n.factorial : ℝ) := by
            exact_mod_cast Nat.factorial_le (by omega)
          have hfst_pow : (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a ≤
              (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.fst ℝ ℝ E)]) han
          have hsnd_pow : (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) ≤
              (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n :=
            pow_le_pow_right₀
              (by linarith [norm_nonneg (ContinuousLinearMap.snd ℝ ℝ E)]) (by omega)
          have hlhs_eq : (n.choose a : ℝ) * (((a.factorial : ℝ) *
                (Ssqrt *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ)))) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a) *
              (((n - a).factorial : ℝ) *
                (Csp * (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp) *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a))) =
              ((n.choose a : ℝ) * (a.factorial : ℝ) * ((n-a).factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ a *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ (n - a) * Csp) *
              (Ssqrt *
                ((1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^
                    (-((pSp : ℝ) + (sW : ℝ))) *
                  (1 + TensorEigenIdx.lambda (I := I) (M := M) i) ^ pSp)) := by ring
          rw [hlhs_eq, hcollapse]
          have hrhs_eq : (2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) =
              ((2 : ℝ) ^ n * (n.factorial : ℝ) * (n.factorial : ℝ) *
                (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) ^ n *
                (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) ^ n * Csp) *
              (Ssqrt * tensorSobolevWeight (I := I) (M := M) i (-(sW : ℝ))) := by ring
          rw [hrhs_eq]
          refine mul_le_mul ?_ (le_refl _) ?_ (by positivity)
          · have hfst_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.fst ℝ ℝ E‖ + 1) := by positivity
            have hsnd_nn : (0:ℝ) ≤ (‖ContinuousLinearMap.snd ℝ ℝ E‖ + 1) := by positivity
            gcongr
          · exact mul_nonneg hSs_nn (tensorSobolevWeight_nonneg (I := I) (M := M) i _)

lemma chartGramOnE_realize_eq_add_half_rawCompOnE
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g S) δ)
    (α : M) (a b : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ interior (extChartAt I α).target) :
    Integral.DivergenceTheorem.chartGramOnE (I := I)
        (tensorSectionRealizeMetric (I := I) g S hδ_lt hδ) α a b y =
      Integral.DivergenceTheorem.chartGramOnE (I := I) g α a b y +
        (1 / 2 : ℝ) * (rawCompOnE (I := I) (M := M) g S α ![a, b] y +
          rawCompOnE (I := I) (M := M) g S α ![b, a] y) := by
  classical
  have hy_t : y ∈ (extChartAt I α).target := interior_subset hy
  have hp_src : (extChartAt I α).symm y ∈ (chartAt H α).source := by
    have := (extChartAt I α).map_target hy_t
    rwa [extChartAt_source] at this
  rw [Integral.DivergenceTheorem.chartGramOnE_def, Integral.DivergenceTheorem.chartGramOnE_def,
    chartGramMatrix_apply, chartGramMatrix_apply, tensorSectionRealizeMetric_inner]
  have hhalf := ccTensorBilinSymm_eq_half_rawComponent (I := I) (M := M) g S α a b hp_src
  rw [hhalf]
  rfl

end FiniteOrderEigenSeries

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
