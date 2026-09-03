import DifferentialGeometry.Analysis.Calculus.BallRetraction
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.DenseMixedBound
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.LowScaleCutoff
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.TameForcingFixedPoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowerScaleActionSobolevExtensions
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.Remainder.ZeroState
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.SmoothEmbedInj
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

noncomputable section

open Bundle Manifold MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private abbrev metricH2 (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem ccBilin_smul
    (g : SmoothRiemannianMetric I M) (c : ℝ)
    (T : SmoothCcTensor g 0 2) (x : M)
    (u v : TangentSpace I x) :
    ccTensorBilin (I := I) g (c • T) x u v =
      c * ccTensorBilin (I := I) g T x u v := by
  rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul]

private theorem ccToHs_neg
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ (-T) =
      -ccTensorToHs (I := I) (M := M) g 2 σ T := by
  rw [show -T = (-1 : ℝ) • T by simp, ccTensorToHs_smul]
  simp

private theorem ccToHs_sub
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T U : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ (T - U) =
      ccTensorToHs (I := I) (M := M) g 2 σ T -
        ccTensorToHs (I := I) (M := M) g 2 σ U := by
  rw [sub_eq_add_neg, ccTensorToHs_add, ccToHs_neg, sub_eq_add_neg]

private abbrev symmCore
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :=
  Set.range (ccToHsLin (I := I) (M := M) g 2 σ)

private noncomputable def symmRep
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (x : symmCore (I := I) (M := M) g σ) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem symmRep_spec
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (x : symmCore (I := I) (M := M) g σ) :
    ccToHsLin (I := I) (M := M) g 2 σ
        (symmRep (I := I) (M := M) g σ x) =
      (x : TensorHs (I := I) (M := M) g 0 2 σ) :=
  Classical.choose_spec x.property

private noncomputable def symmCoreMap
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    symmCore (I := I) (M := M) g σ →
      TensorHs (I := I) (M := M) g 0 2 σ :=
  fun x =>
    ccToHsLin (I := I) (M := M) g 2 σ
      (symmS (I := I) (M := M) g
        (symmRep (I := I) (M := M) g σ x))

private theorem symmCore_lip
    (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    LipschitzWith 1 (symmCoreMap (I := I) (M := M) g σ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  have hx :
      ccTensorToHs (I := I) (M := M) g 2 σ
          (symmRep (I := I) (M := M) g σ x) =
        (x : TensorHs (I := I) (M := M) g 0 2 σ) := by
    simpa only [ccToHsLin_apply] using
      symmRep_spec (I := I) (M := M) g σ x
  have hy :
      ccTensorToHs (I := I) (M := M) g 2 σ
          (symmRep (I := I) (M := M) g σ y) =
        (y : TensorHs (I := I) (M := M) g 0 2 σ) := by
    simpa only [ccToHsLin_apply] using
      symmRep_spec (I := I) (M := M) g σ y
  change
    ‖ccTensorToHs (I := I) (M := M) g 2 σ
          (symmS (I := I) (M := M) g
            (symmRep (I := I) (M := M) g σ x)) -
        ccTensorToHs (I := I) (M := M) g 2 σ
          (symmS (I := I) (M := M) g
            (symmRep (I := I) (M := M) g σ y))‖ ≤
      ‖(x : TensorHs (I := I) (M := M) g 0 2 σ) -
        (y : TensorHs (I := I) (M := M) g 0 2 σ)‖
  rw [← ccToHs_sub, ← symmS_sub, ← hx, ← hy, ← ccToHs_sub]
  exact norm_smoothCcToTensorHs_symmS_le
    (I := I) (M := M) g σ
      (symmRep (I := I) (M := M) g σ x -
        symmRep (I := I) (M := M) g σ y)

private noncomputable def symmFun
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ) :
    TensorHs (I := I) (M := M) g 0 2 σ →
      TensorHs (I := I) (M := M) g 0 2 σ :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 hσ)
    (symmCoreMap (I := I) (M := M) g σ)

private theorem symmFun_lip
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ) :
    LipschitzWith 1 (symmFun (I := I) (M := M) g hσ) := by
  exact dense_lipschitz
    (ccToHsLin_dense (I := I) (M := M) g 2 hσ)
    (symmCoreMap (I := I) (M := M) g σ)
    (symmCore_lip (I := I) (M := M) g σ)

private theorem symmFun_core
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (T : SmoothCcTensor g 0 2) :
    symmFun (I := I) (M := M) g hσ
        (ccToHsLin (I := I) (M := M) g 2 σ T) =
      ccToHsLin (I := I) (M := M) g 2 σ
        (ccTensor02Symm (I := I) (M := M) g T) := by
  let x : symmCore (I := I) (M := M) g σ :=
    ⟨ccToHsLin (I := I) (M := M) g 2 σ T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 hσ).extend_eq
      (symmCore_lip (I := I) (M := M) g σ).continuous x
  have hrep :
      symmRep (I := I) (M := M) g σ x = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 σ
    simpa only [ccToHsLin_apply, x] using
      symmRep_spec (I := I) (M := M) g σ x
  simpa only [symmFun, symmCoreMap, x, hrep] using hext

private theorem symmFun_zero
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ) :
    symmFun (I := I) (M := M) g hσ 0 = 0 := by
  have hsymm :
      ccTensor02Symm (I := I) (M := M) g (0 : SmoothCcTensor g 0 2) = 0 := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      symmS_smul]
    simp
  simpa only [map_zero, hsymm] using
    symmFun_core (I := I) (M := M) g hσ
      (0 : SmoothCcTensor g 0 2)

private theorem symmFun_add
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (u v : TensorHs (I := I) (M := M) g 0 2 σ) :
    symmFun (I := I) (M := M) g hσ (u + v) =
      symmFun (I := I) (M := M) g hσ u +
        symmFun (I := I) (M := M) g hσ v := by
  let D : Set (TensorHs (I := I) (M := M) g 0 2 σ) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 σ)
  let C : Set
      (TensorHs (I := I) (M := M) g 0 2 σ ×
        TensorHs (I := I) (M := M) g 0 2 σ) :=
    {p | symmFun (I := I) (M := M) g hσ (p.1 + p.2) =
      symmFun (I := I) (M := M) g hσ p.1 +
        symmFun (I := I) (M := M) g hσ p.2}
  have hf : Continuous (symmFun (I := I) (M := M) g hσ) :=
    (symmFun_lip (I := I) (M := M) g hσ).continuous
  have hclosed : IsClosed C := by
    exact isClosed_eq
      (hf.comp (continuous_fst.add continuous_snd))
      ((hf.comp continuous_fst).add (hf.comp continuous_snd))
  have hsub : D ×ˢ D ⊆ C := by
    rintro ⟨p, q⟩ ⟨⟨T, rfl⟩, ⟨U, rfl⟩⟩
    change symmFun (I := I) (M := M) g hσ
        (ccToHsLin (I := I) (M := M) g 2 σ T +
          ccToHsLin (I := I) (M := M) g 2 σ U) =
      symmFun (I := I) (M := M) g hσ
          (ccToHsLin (I := I) (M := M) g 2 σ T) +
        symmFun (I := I) (M := M) g hσ
          (ccToHsLin (I := I) (M := M) g 2 σ U)
    rw [← map_add,
      symmFun_core (I := I) (M := M) g hσ,
      symmFun_core (I := I) (M := M) g hσ,
      symmFun_core (I := I) (M := M) g hσ,
      symmS_add, map_add]
  have hD : Dense D :=
    ccToHsLin_dense (I := I) (M := M) g 2 hσ
  have hC : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (hD.prod hD).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have huv : (u, v) ∈ C := by
    rw [hC]
    trivial
  exact huv

private theorem symmFun_smul
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (c : ℝ) (u : TensorHs (I := I) (M := M) g 0 2 σ) :
    symmFun (I := I) (M := M) g hσ (c • u) =
      c • symmFun (I := I) (M := M) g hσ u := by
  let D : Set (TensorHs (I := I) (M := M) g 0 2 σ) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 σ)
  let C : Set (TensorHs (I := I) (M := M) g 0 2 σ) :=
    {v | symmFun (I := I) (M := M) g hσ (c • v) =
      c • symmFun (I := I) (M := M) g hσ v}
  have hf : Continuous (symmFun (I := I) (M := M) g hσ) :=
    (symmFun_lip (I := I) (M := M) g hσ).continuous
  have hclosed : IsClosed C := by
    exact isClosed_eq
      (hf.comp (continuous_const_smul c))
      (continuous_const_smul c |>.comp hf)
  have hsub : D ⊆ C := by
    rintro v ⟨T, rfl⟩
    change symmFun (I := I) (M := M) g hσ
        (c • ccToHsLin (I := I) (M := M) g 2 σ T) =
      c • symmFun (I := I) (M := M) g hσ
        (ccToHsLin (I := I) (M := M) g 2 σ T)
    rw [← map_smul,
      symmFun_core (I := I) (M := M) g hσ,
      symmFun_core (I := I) (M := M) g hσ,
      symmS_smul, map_smul]
  have hD : Dense D :=
    ccToHsLin_dense (I := I) (M := M) g 2 hσ
  have hC : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hD.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hu : u ∈ C := by
    rw [hC]
    trivial
  exact hu

noncomputable def symmHs
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ) :
    TensorHs (I := I) (M := M) g 0 2 σ →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 σ :=
  let L : TensorHs (I := I) (M := M) g 0 2 σ →ₗ[ℝ]
      TensorHs (I := I) (M := M) g 0 2 σ :=
    { toFun := symmFun (I := I) (M := M) g hσ
      map_add' := symmFun_add (I := I) (M := M) g hσ
      map_smul' := symmFun_smul (I := I) (M := M) g hσ }
  LinearMap.mkContinuous L
    1
    (fun u => by
      have h := (symmFun_lip (I := I) (M := M) g hσ).dist_le_mul u 0
      rw [NNReal.coe_one, one_mul, symmFun_zero (I := I) (M := M) g hσ,
        dist_zero_right, dist_zero_right] at h
      change ‖L u‖ ≤ 1 * ‖u‖
      rw [show L u = symmFun (I := I) (M := M) g hσ u by rfl, one_mul]
      exact h)

theorem symmHs_core
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (T : SmoothCcTensor g 0 2) :
    symmHs (I := I) (M := M) g hσ
        (ccToHsLin (I := I) (M := M) g 2 σ T) =
      ccToHsLin (I := I) (M := M) g 2 σ
        (symmS (I := I) (M := M) g T) :=
  symmFun_core (I := I) (M := M) g hσ T

theorem symmHs_le
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (u : TensorHs (I := I) (M := M) g 0 2 σ) :
    ‖symmHs (I := I) (M := M) g hσ u‖ ≤ ‖u‖ := by
  have h := (symmFun_lip (I := I) (M := M) g hσ).dist_le_mul u 0
  rw [NNReal.coe_one, one_mul, symmFun_zero (I := I) (M := M) g hσ,
    dist_zero_right, dist_zero_right] at h
  exact h

private theorem hsIncl_core
    (g : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτσ : τ ≤ σ) (T : SmoothCcTensor g 0 2) :
    tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) hτσ
        (ccToHsLin (I := I) (M := M) g 2 σ T) =
      ccToHsLin (I := I) (M := M) g 2 τ T := by
  apply TensorHs.ext
  funext i
  simp only [tensorHsInclusion_coeff_apply, ccToHsLin_apply,
    ccTensorToHs_coeff]

theorem symmHs_incl
    (g : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hτσ : τ ≤ σ) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) hτσ).comp
        (symmHs (I := I) (M := M) g hσ) =
      (symmHs (I := I) (M := M) g hτ).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) hτσ) := by
  apply ContinuousLinearMap.ext
  intro u
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 σ) :=
    ccToHsLin_dense (I := I) (M := M) g 2 hσ
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact (tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) hτσ).continuous.comp
        (symmHs (I := I) (M := M) g hσ).continuous
  · exact (symmHs (I := I) (M := M) g hτ).continuous.comp
      (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) hτσ).continuous
  · intro T
    simp only [ContinuousLinearMap.comp_apply]
    rw [symmHs_core (I := I) (M := M) g hσ,
      hsIncl_core (I := I) (M := M) g hτσ,
      hsIncl_core (I := I) (M := M) g hτσ,
      symmHs_core (I := I) (M := M) g hτ]

noncomputable def radialScale
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) : ℝ :=
  min 1
    (ρ / ‖symmHs (I := I) (M := M) g (by norm_num) v‖)

private theorem radialScale_nonneg
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :
    0 ≤ radialScale (I := I) (M := M) g ρ v := by
  unfold radialScale
  exact le_min zero_le_one (div_nonneg hρ (norm_nonneg _))

private theorem radialScale_le
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :
    radialScale (I := I) (M := M) g ρ v ≤ 1 := by
  exact min_le_left _ _

noncomputable def radialCLM
    (g : SmoothRiemannianMetric I M) {σ : ℝ} (hσ : 0 ≤ σ)
    (ρ : ℝ) (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :
    TensorHs (I := I) (M := M) g 0 2 σ →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 σ :=
  radialScale (I := I) (M := M) g ρ v •
    symmHs (I := I) (M := M) g hσ

theorem radialCLM_le
    (g : SmoothRiemannianMetric I M) {σ ρ : ℝ}
    (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
    (u : TensorHs (I := I) (M := M) g 0 2 σ) :
    ‖radialCLM (I := I) (M := M) g hσ ρ v u‖ ≤ ‖u‖ := by
  rw [radialCLM, smul_apply, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg
      (radialScale_nonneg (I := I) (M := M) g hρ v)]
  calc
    radialScale (I := I) (M := M) g ρ v *
        ‖symmHs (I := I) (M := M) g hσ u‖ ≤
      1 * ‖symmHs (I := I) (M := M) g hσ u‖ :=
        mul_le_mul_of_nonneg_right
          (radialScale_le (I := I) (M := M) g ρ v)
          (norm_nonneg _)
    _ = ‖symmHs (I := I) (M := M) g hσ u‖ := one_mul _
    _ ≤ ‖u‖ := symmHs_le (I := I) (M := M) g hσ u

theorem radialCLM_norm
    (g : SmoothRiemannianMetric I M) {σ ρ : ℝ}
    (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ)
    (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :
    ‖radialCLM (I := I) (M := M) g hσ ρ v‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => ?_)
  simpa only [one_mul] using
    radialCLM_le (I := I) (M := M) g hσ hρ v u

theorem radialCLM_aemeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : SmoothRiemannianMetric I M) {σ ρ : ℝ} (hσ : 0 ≤ σ)
    {v : Ω → TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)}
    (hv : AEStronglyMeasurable v μ) :
    AEStronglyMeasurable
      (fun x => radialCLM (I := I) (M := M) g hσ ρ (v x)) μ := by
  have hs :
      AEStronglyMeasurable
        (fun x =>
          symmHs (I := I) (M := M) g (show (0 : ℝ) ≤ 2 by norm_num)
            (v x)) μ :=
    (symmHs (I := I) (M := M) g
      (show (0 : ℝ) ≤ 2 by norm_num)).continuous.comp_aestronglyMeasurable hv
  have hscale :
      AEStronglyMeasurable
        (fun x => min 1
          (ρ / ‖symmHs (I := I) (M := M) g
            (show (0 : ℝ) ≤ 2 by norm_num) (v x)‖)) μ :=
    (aemeasurable_const.min
      (aemeasurable_const.div hs.norm.aemeasurable)).aestronglyMeasurable
  have hconst :
      AEStronglyMeasurable
        (fun _ : Ω => symmHs (I := I) (M := M) g hσ) μ :=
    aestronglyMeasurable_const
  refine (hscale.smul hconst).congr ?_
  exact Filter.Eventually.of_forall fun x => by
    simp only [radialCLM, radialScale]
    congr 3

theorem radialCLM_incl
    (g : SmoothRiemannianMetric I M) {τ σ : ℝ}
    (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (hτσ : τ ≤ σ)
    (ρ : ℝ) (v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) hτσ).comp
        (radialCLM (I := I) (M := M) g hσ ρ v) =
      (radialCLM (I := I) (M := M) g hτ ρ v).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) hτσ) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, radialCLM,
    smul_apply, map_smul]
  have h := DFunLike.congr_fun
    (symmHs_incl (I := I) (M := M) g hτ hσ hτσ) u
  simp only [ContinuousLinearMap.comp_apply] at h
  exact congrArg
    (fun z => radialScale (I := I) (M := M) g ρ v • z) h

noncomputable def lowRadial
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (T : SmoothCcTensor g 0 2) : SmoothCcTensor g 0 2 :=
  (min 1
      (ρ /
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g T)‖)) •
    symmS (I := I) (M := M) g T

@[simp] theorem lowRadial_zero
    (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    lowRadial (I := I) (M := M) g ρ
        (0 : SmoothCcTensor g 0 2) = 0 := by
  have hs :
      symmS (I := I) (M := M) g (0 : SmoothCcTensor g 0 2) = 0 := by
    simpa only [zero_smul] using
      symmS_smul (I := I) (M := M) g (0 : ℝ)
        (0 : SmoothCcTensor g 0 2)
  rw [lowRadial, hs, smul_zero]

theorem lowRadial_embed
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (lowRadial (I := I) (M := M) g ρ T) =
      ballRetraction ρ
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g T)) := by
  rw [lowRadial, ccTensorToHs_smul, ballRetraction]

theorem lowRadial_norm
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (T : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (lowRadial (I := I) (M := M) g ρ T)‖ ≤ ρ := by
  rw [lowRadial_embed (I := I) (M := M)]
  exact ballRetraction_mem_closedBall hρ _

theorem lowRadial_eq_self
    (g : SmoothRiemannianMetric I M) {ρ : ℝ}
    (T : SmoothCcTensor g 0 2)
    (hT : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
      (symmS (I := I) (M := M) g T)‖ ≤ ρ) :
    lowRadial (I := I) (M := M) g ρ T = symmS (I := I) (M := M) g T := by
  rcases eq_or_lt_of_le (norm_nonneg
      (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (symmS (I := I) (M := M) g T))) with hz | hz
  · have hzero : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2) = 0 := by
      simpa only [ccToHsLin_apply] using
        map_zero (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
    have hS : symmS (I := I) (M := M) g T = (0 : SmoothCcTensor g 0 2) :=
      ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
        ((norm_eq_zero.mp hz.symm).trans hzero.symm)
    rw [lowRadial, hS, smul_zero]
  · rw [lowRadial, min_eq_left ((one_le_div hz).mpr hT), one_smul]

theorem lowRadial_symm
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (T : SmoothCcTensor g 0 2)
    (x : M) (u v : TangentSpace I x) :
    ccTensorBilin (I := I) g
        (lowRadial (I := I) (M := M) g ρ T) x u v =
      ccTensorBilin (I := I) g
        (lowRadial (I := I) (M := M) g ρ T) x v u := by
  rw [lowRadial, ccBilin_smul, ccBilin_smul,
    ccTensorBilin_symmS, ccTensorBilin_symmS,
    ccTensorBilinSymm_symm (I := I) g T x u v]

theorem lowRadial_lip
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (T U : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (lowRadial (I := I) (M := M) g ρ T) -
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (lowRadial (I := I) (M := M) g ρ U)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  rw [lowRadial_embed (I := I) (M := M),
    lowRadial_embed (I := I) (M := M)]
  have hretract :=
    (lipschitzWith_one_ballRetraction
      (X := metricH2 (I := I) (M := M) g) hρ).dist_le_mul
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g T))
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g U))
  rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm] at hretract
  calc
    ‖ballRetraction ρ
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (symmS (I := I) (M := M) g T)) -
        ballRetraction ρ
          (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (symmS (I := I) (M := M) g U))‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (symmS (I := I) (M := M) g T) -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (symmS (I := I) (M := M) g U)‖ := hretract
    _ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g (T - U))‖ := by
      simp only [symmS]
      rw [symmS_sub, ccToHs_sub]
    _ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ := by
      exact norm_smoothCcToTensorHs_symmS_le
        (I := I) (M := M) g (2 : ℝ) (T - U)
    _ =
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
      rw [ccToHs_sub]

private abbrev metricThirdOrderSobolev (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ)

private abbrev incl32 (g : SmoothRiemannianMetric I M) :
    metricThirdOrderSobolev (I := I) (M := M) g →L[ℝ]
      metricH2 (I := I) (M := M) g :=
  tensorHsInclusion (I := I) (M := M) (g := g)
    (r := 0) (s := 2) (by norm_num)

private theorem incl32_ccToHs
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    incl32 (I := I) (M := M) g
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T := by
  refine TensorHs.ext ?_
  funext i
  simp only [incl32, tensorHsInclusion_coeff_apply, ccTensorToHs_coeff]

theorem lowRadial_h3_eq
    (g : SmoothRiemannianMetric I M) (ρ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
        (lowRadial (I := I) (M := M) g ρ T) =
      lowScaleCutoff (incl32 (I := I) (M := M) g) ρ
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (symmS (I := I) (M := M) g T)) := by
  rw [lowRadial, lowScaleCutoff, ccTensorToHs_smul,
    incl32_ccToHs (I := I) (M := M)]

theorem lowRadial_h3_sub
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (T U : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (lowRadial (I := I) (M := M) g ρ T) -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (lowRadial (I := I) (M := M) g ρ U)‖ ≤
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ +
      (1 / ρ) *
        max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
  let T3 :=
    ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
      (symmS (I := I) (M := M) g T)
  let U3 :=
    ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
      (symmS (I := I) (M := M) g U)
  have hcut :=
    lowScaleCutoff_sub_le (incl32 (I := I) (M := M) g)
      (tensorHsInclusion_injective (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (by norm_num))
      hρ T3 U3
  have h3diff :
      ‖T3 - U3‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
    rw [show T3 - U3 =
        ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (symmS (I := I) (M := M) g (T - U)) by
      simp only [T3, U3, symmS_sub, ccToHs_sub]]
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (symmS (I := I) (M := M) g (T - U))‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) (T - U)‖ :=
        norm_smoothCcToTensorHs_symmS_le
          (I := I) (M := M) g (3 : ℝ) (T - U)
      _ = ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ := by
        rw [ccToHs_sub]
  have hT3 :
      ‖T3‖ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
    norm_smoothCcToTensorHs_symmS_le
      (I := I) (M := M) g (3 : ℝ) T
  have hU3 :
      ‖U3‖ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
    norm_smoothCcToTensorHs_symmS_le
      (I := I) (M := M) g (3 : ℝ) U
  have h2diff :
      ‖incl32 (I := I) (M := M) g T3 -
          incl32 (I := I) (M := M) g U3‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
    rw [show incl32 (I := I) (M := M) g T3 -
        incl32 (I := I) (M := M) g U3 =
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (symmS (I := I) (M := M) g (T - U)) by
      simp only [T3, U3, incl32_ccToHs, symmS_sub, ccToHs_sub]]
    calc
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (symmS (I := I) (M := M) g (T - U))‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
        norm_smoothCcToTensorHs_symmS_le
          (I := I) (M := M) g (2 : ℝ) (T - U)
      _ = ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ := by
        rw [ccToHs_sub]
  have hmax :
      max ‖T3‖ ‖U3‖ ≤
        max
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
    max_le_max hT3 hU3
  have hfac :
      (1 / ρ) * max ‖T3‖ ‖U3‖ ≤
        (1 / ρ) *
          max
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  have hprod :
      (1 / ρ) * max ‖T3‖ ‖U3‖ *
          ‖incl32 (I := I) (M := M) g T3 -
            incl32 (I := I) (M := M) g U3‖ ≤
        (1 / ρ) *
          max
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
            ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) U‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ :=
    mul_le_mul hfac h2diff (norm_nonneg _)
      (mul_nonneg (by positivity)
        (le_trans
          (norm_nonneg
            (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T))
          (le_max_left _ _)))
  rw [lowRadial_h3_eq (I := I) (M := M),
    lowRadial_h3_eq (I := I) (M := M)]
  exact hcut.trans (add_le_add h3diff hprod)

private abbrev highCore (g : SmoothRiemannianMetric I M) :=
  Set.range (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))

private noncomputable def highRep
    (g : SmoothRiemannianMetric I M) (x : highCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem highRep_spec
    (g : SmoothRiemannianMetric I M) (x : highCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
        (highRep (I := I) (M := M) g x) =
      (x : metricThirdOrderSobolev (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def radialHighCore
    (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    highCore (I := I) (M := M) g → metricThirdOrderSobolev (I := I) (M := M) g :=
  fun x =>
    ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
      (lowRadial (I := I) (M := M) g ρ
        (highRep (I := I) (M := M) g x))

private theorem radialHigh_balls
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ R : ℝ, ∃ K : NNReal,
      LipschitzOnWith K (radialHighCore (I := I) (M := M) g ρ)
        {x : highCore (I := I) (M := M) g |
          dist (x : metricThirdOrderSobolev (I := I) (M := M) g) 0 ≤ R} := by
  intro R
  let q : ℝ := max R 0
  let K0 : ℝ := 1 + (1 / ρ) * q
  have hq : 0 ≤ q := by
    exact le_max_right _ _
  have hK0 : 0 ≤ K0 := by
    dsimp only [K0]
    positivity
  refine ⟨Real.toNNReal K0, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hx3 :
      ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (highRep (I := I) (M := M) g x) =
        (x : metricThirdOrderSobolev (I := I) (M := M) g) := by
    simpa only [ccToHsLin_apply] using
      highRep_spec (I := I) (M := M) g x
  have hy3 :
      ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
          (highRep (I := I) (M := M) g y) =
        (y : metricThirdOrderSobolev (I := I) (M := M) g) := by
    simpa only [ccToHsLin_apply] using
      highRep_spec (I := I) (M := M) g y
  have hx2 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (highRep (I := I) (M := M) g x) =
        incl32 (I := I) (M := M) g
          (x : metricThirdOrderSobolev (I := I) (M := M) g) := by
    rw [← incl32_ccToHs (I := I) (M := M), hx3]
  have hy2 :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (highRep (I := I) (M := M) g y) =
        incl32 (I := I) (M := M) g
          (y : metricThirdOrderSobolev (I := I) (M := M) g) := by
    rw [← incl32_ccToHs (I := I) (M := M), hy3]
  have hmix := lowRadial_h3_sub (I := I) (M := M) g hρ
    (highRep (I := I) (M := M) g x)
    (highRep (I := I) (M := M) g y)
  rw [hx3, hy3, hx2, hy2] at hmix
  have hxq :
      ‖(x : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤ q := by
    change dist
      (x : metricThirdOrderSobolev (I := I) (M := M) g) 0 ≤ R at hx
    rw [dist_zero_right] at hx
    exact hx.trans (le_max_left _ _)
  have hyq :
      ‖(y : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤ q := by
    change dist
      (y : metricThirdOrderSobolev (I := I) (M := M) g) 0 ≤ R at hy
    rw [dist_zero_right] at hy
    exact hy.trans (le_max_left _ _)
  have hmax :
      max
          ‖(x : metricThirdOrderSobolev (I := I) (M := M) g)‖
          ‖(y : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤ q :=
    max_le hxq hyq
  have hincl :
      ‖incl32 (I := I) (M := M) g
            (x : metricThirdOrderSobolev (I := I) (M := M) g) -
          incl32 (I := I) (M := M) g
            (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤
        ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
          (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ := by
    rw [← map_sub]
    exact tensorHsInclusion_norm_le (I := I) (M := M)
      (g := g) (r := 0) (s := 2) (by norm_num) _
  have hfac :
      (1 / ρ) *
          max
            ‖(x : metricThirdOrderSobolev (I := I) (M := M) g)‖
            ‖(y : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤
        (1 / ρ) * q :=
    mul_le_mul_of_nonneg_left hmax (by positivity)
  have hprod :
      (1 / ρ) *
          max
            ‖(x : metricThirdOrderSobolev (I := I) (M := M) g)‖
            ‖(y : metricThirdOrderSobolev (I := I) (M := M) g)‖ *
          ‖incl32 (I := I) (M := M) g
              (x : metricThirdOrderSobolev (I := I) (M := M) g) -
            incl32 (I := I) (M := M) g
              (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ ≤
        (1 / ρ) * q *
          ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
            (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ :=
    mul_le_mul hfac hincl (norm_nonneg _)
      (mul_nonneg (by positivity) hq)
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  calc
    ‖radialHighCore (I := I) (M := M) g ρ x -
        radialHighCore (I := I) (M := M) g ρ y‖ ≤
        ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
          (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ +
        (1 / ρ) *
          max
            ‖(x : metricThirdOrderSobolev (I := I) (M := M) g)‖
            ‖(y : metricThirdOrderSobolev (I := I) (M := M) g)‖ *
          ‖incl32 (I := I) (M := M) g
              (x : metricThirdOrderSobolev (I := I) (M := M) g) -
            incl32 (I := I) (M := M) g
              (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ := by
      simpa only [radialHighCore, ccToHsLin_apply] using hmix
    _ ≤ ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
          (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ +
        (1 / ρ) * q *
          ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
            (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ :=
      add_le_add le_rfl hprod
    _ = K0 * ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
          (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ := by
      simp only [K0]
      ring
    _ = (Real.toNNReal K0 : ℝ) *
        ‖(x : metricThirdOrderSobolev (I := I) (M := M) g) -
          (y : metricThirdOrderSobolev (I := I) (M := M) g)‖ := by
      rw [Real.coe_toNNReal _ hK0]

private theorem radialHigh_cont
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (radialHighCore (I := I) (M := M) g ρ) := by
  rw [continuous_iff_continuousAt]
  intro x
  let R : ℝ :=
    dist (x : metricThirdOrderSobolev (I := I) (M := M) g) 0 + 1
  obtain ⟨K, hK⟩ :=
    radialHigh_balls (I := I) (M := M) g hρ R
  have hxball :
      (x : metricThirdOrderSobolev (I := I) (M := M) g) ∈
        Metric.ball (0 : metricThirdOrderSobolev (I := I) (M := M) g) R := by
    rw [Metric.mem_ball]
    dsimp only [R]
    linarith
  have hxclosed :
      x ∈ {y : highCore (I := I) (M := M) g |
        dist (y : metricThirdOrderSobolev (I := I) (M := M) g) 0 ≤ R} := by
    change dist (x : metricThirdOrderSobolev (I := I) (M := M) g) 0 ≤ R
    dsimp only [R]
    linarith
  have hclosed :
      Metric.closedBall
          (0 : metricThirdOrderSobolev (I := I) (M := M) g) R ∈
        𝓝 (x : metricThirdOrderSobolev (I := I) (M := M) g) :=
    Metric.closedBall_mem_nhds_of_mem hxball
  have hpre :
      ((↑) : highCore (I := I) (M := M) g →
          metricThirdOrderSobolev (I := I) (M := M) g) ⁻¹'
          Metric.closedBall
            (0 : metricThirdOrderSobolev (I := I) (M := M) g) R ∈ 𝓝 x :=
    continuousAt_subtype_val.preimage_mem_nhds hclosed
  apply (hK.continuousOn x hxclosed).continuousAt
  change ((↑) : highCore (I := I) (M := M) g →
      metricThirdOrderSobolev (I := I) (M := M) g) ⁻¹'
      Metric.closedBall
        (0 : metricThirdOrderSobolev (I := I) (M := M) g) R ∈ 𝓝 x
  exact hpre

noncomputable def lowRadialH3
    (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    metricThirdOrderSobolev (I := I) (M := M) g → metricThirdOrderSobolev (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (radialHighCore (I := I) (M := M) g ρ)

theorem lowRadialH3_cont
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (lowRadialH3 (I := I) (M := M) g ρ) := by
  exact dense_cont_on_balls
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (radialHighCore (I := I) (M := M) g ρ) 0
    (radialHigh_balls (I := I) (M := M) g hρ)

theorem lowRadialH3_core
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (T : SmoothCcTensor g 0 2) :
    lowRadialH3 (I := I) (M := M) g ρ
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T) =
      ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)
        (lowRadial (I := I) (M := M) g ρ T) := by
  let x : highCore (I := I) (M := M) g :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      (radialHigh_cont (I := I) (M := M) g hρ) x
  have hrep : highRep (I := I) (M := M) g x = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (3 : ℝ)
    simpa only [ccToHsLin_apply, x] using
      highRep_spec (I := I) (M := M) g x
  simpa only [lowRadialH3, radialHighCore, x, hrep] using hext

@[simp] theorem lowRadialH3_zero
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ) :
    lowRadialH3 (I := I) (M := M) g ρ 0 = 0 := by
  simpa only [map_zero, lowRadial_zero] using
    lowRadialH3_core (I := I) (M := M) g hρ
      (0 : SmoothCcTensor g 0 2)

theorem lowRadialH3_le
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    ‖lowRadialH3 (I := I) (M := M) g ρ u‖ ≤ ‖u‖ := by
  let D : Set (metricThirdOrderSobolev (I := I) (M := M) g) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
  let C : Set (metricThirdOrderSobolev (I := I) (M := M) g) :=
    {v | ‖lowRadialH3 (I := I) (M := M) g ρ v‖ ≤ ‖v‖}
  have hclosed : IsClosed C := by
    exact isClosed_le
      (lowRadialH3_cont (I := I) (M := M) g hρ).norm continuous_norm
  have hsub : D ⊆ C := by
    rintro v ⟨T, rfl⟩
    change
      ‖lowRadialH3 (I := I) (M := M) g ρ
          (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T)‖ ≤
        ‖ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T‖
    rw [lowRadialH3_core (I := I) (M := M) g hρ]
    simp only [ccToHsLin_apply]
    rw [lowRadial_h3_eq (I := I) (M := M), lowScaleCutoff, norm_smul]
    let q : ℝ :=
      ρ /
        ‖incl32 (I := I) (M := M) g
          (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
            (symmS (I := I) (M := M) g T))‖
    have hq : 0 ≤ q := by
      exact div_nonneg hρ.le (norm_nonneg _)
    have hmin0 : 0 ≤ min 1 q := le_min zero_le_one hq
    have hmin1 : min 1 q ≤ 1 := min_le_left _ _
    change
      ‖min 1 q‖ *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
            (symmS (I := I) (M := M) g T)‖ ≤
        ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
    rw [Real.norm_eq_abs, abs_of_nonneg hmin0]
    calc
      min 1 q *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
            (symmS (I := I) (M := M) g T)‖ ≤
        1 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
            (symmS (I := I) (M := M) g T)‖ :=
        mul_le_mul_of_nonneg_right hmin1 (norm_nonneg _)
      _ =
          ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ)
            (symmS (I := I) (M := M) g T)‖ := one_mul _
      _ ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ :=
        norm_smoothCcToTensorHs_symmS_le
          (I := I) (M := M) g (3 : ℝ) T
  have hD : Dense D :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hC : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hD.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hu : u ∈ C := by
    rw [hC]
    trivial
  exact hu

theorem lowRadialH3_sub
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u v : metricThirdOrderSobolev (I := I) (M := M) g) :
    ‖lowRadialH3 (I := I) (M := M) g ρ u -
        lowRadialH3 (I := I) (M := M) g ρ v‖ ≤
      ‖u - v‖ +
        (1 / ρ) * max ‖u‖ ‖v‖ *
          ‖incl32 (I := I) (M := M) g u -
            incl32 (I := I) (M := M) g v‖ := by
  let D : Set (metricThirdOrderSobolev (I := I) (M := M) g) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ))
  let lhs :
      metricThirdOrderSobolev (I := I) (M := M) g ×
        metricThirdOrderSobolev (I := I) (M := M) g → ℝ :=
    fun p => ‖lowRadialH3 (I := I) (M := M) g ρ p.1 -
      lowRadialH3 (I := I) (M := M) g ρ p.2‖
  let rhs :
      metricThirdOrderSobolev (I := I) (M := M) g ×
        metricThirdOrderSobolev (I := I) (M := M) g → ℝ :=
    fun p => ‖p.1 - p.2‖ +
      (1 / ρ) * max ‖p.1‖ ‖p.2‖ *
        ‖incl32 (I := I) (M := M) g p.1 -
          incl32 (I := I) (M := M) g p.2‖
  have hrad := lowRadialH3_cont (I := I) (M := M) g hρ
  have hlhs : Continuous lhs := by
    dsimp only [lhs]
    exact ((hrad.comp continuous_fst).sub
      (hrad.comp continuous_snd)).norm
  have hincl : Continuous
      (fun p :
          metricThirdOrderSobolev (I := I) (M := M) g ×
            metricThirdOrderSobolev (I := I) (M := M) g =>
        incl32 (I := I) (M := M) g p.1 -
          incl32 (I := I) (M := M) g p.2) :=
    ((incl32 (I := I) (M := M) g).continuous.comp continuous_fst).sub
      ((incl32 (I := I) (M := M) g).continuous.comp continuous_snd)
  have hrhs : Continuous rhs := by
    dsimp only [rhs]
    exact (continuous_fst.sub continuous_snd).norm.add
      ((continuous_const.mul
        (continuous_fst.norm.max continuous_snd.norm)).mul hincl.norm)
  have hclosed : IsClosed {p | lhs p ≤ rhs p} :=
    isClosed_le hlhs hrhs
  have hsub : D ×ˢ D ⊆ {p | lhs p ≤ rhs p} := by
    rintro ⟨x, y⟩ ⟨⟨T, rfl⟩, ⟨U, rfl⟩⟩
    change lhs
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T,
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U) ≤
      rhs
        (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T,
          ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) U)
    dsimp only [lhs, rhs]
    rw [lowRadialH3_core (I := I) (M := M) g hρ,
      lowRadialH3_core (I := I) (M := M) g hρ]
    simpa only [ccToHsLin_apply, incl32_ccToHs] using
      lowRadial_h3_sub (I := I) (M := M) g hρ T U
  have hD : Dense D :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have huniv : {p | lhs p ≤ rhs p} = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← (hD.prod hD).closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have huv : (u, v) ∈ {p | lhs p ≤ rhs p} := by
    rw [huniv]
    trivial
  simpa only [Set.mem_ofPred_eq, lhs, rhs] using huv

private abbrev lowCore (g : SmoothRiemannianMetric I M) :=
  Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))

private noncomputable def lowRep
    (g : SmoothRiemannianMetric I M) (x : lowCore (I := I) (M := M) g) :
    SmoothCcTensor g 0 2 :=
  Classical.choose x.property

private theorem lowRep_spec
    (g : SmoothRiemannianMetric I M) (x : lowCore (I := I) (M := M) g) :
    ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)
        (lowRep (I := I) (M := M) g x) =
      (x : metricH2 (I := I) (M := M) g) :=
  Classical.choose_spec x.property

private noncomputable def radialCore
    (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    lowCore (I := I) (M := M) g → metricH2 (I := I) (M := M) g :=
  fun x =>
    ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)
      (lowRadial (I := I) (M := M) g ρ
        (lowRep (I := I) (M := M) g x))

private theorem radialCore_lip
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    LipschitzWith 1 (radialCore (I := I) (M := M) g ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one, one_mul, dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  have hx :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (lowRep (I := I) (M := M) g x) =
        (x : metricH2 (I := I) (M := M) g) := by
    simpa only [ccToHsLin_apply] using
      lowRep_spec (I := I) (M := M) g x
  have hy :
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
          (lowRep (I := I) (M := M) g y) =
        (y : metricH2 (I := I) (M := M) g) := by
    simpa only [ccToHsLin_apply] using
      lowRep_spec (I := I) (M := M) g y
  have h := lowRadial_lip (I := I) (M := M) g hρ
    (lowRep (I := I) (M := M) g x)
    (lowRep (I := I) (M := M) g y)
  rw [hx, hy] at h
  simpa only [radialCore, ccToHsLin_apply] using h

private theorem dense_ext_lip
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [T2Space Y] [CompleteSpace Y] {D : Set X} (hD : Dense D)
    {K : NNReal} (F : D → Y)
    (hF : ∀ x y : D,
      dist (F x) (F y) ≤ (K : ℝ) * dist (x : X) (y : X)) :
    LipschitzWith K (Dense.extend hD F) := by
  exact dense_lipschitz hD F <|
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [Subtype.dist_eq] using hF x y

noncomputable def lowRadialHs
    (g : SmoothRiemannianMetric I M) (ρ : ℝ) :
    metricH2 (I := I) (M := M) g → metricH2 (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (radialCore (I := I) (M := M) g ρ)

theorem lowRadialHs_lip
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    LipschitzWith 1 (lowRadialHs (I := I) (M := M) g ρ) := by
  apply dense_ext_lip
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (radialCore (I := I) (M := M) g ρ)
  intro x y
  simpa only [Subtype.dist_eq] using
    (radialCore_lip (I := I) (M := M) g hρ).dist_le_mul x y

theorem lowRadialHs_cont
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Continuous (lowRadialHs (I := I) (M := M) g ρ) :=
  (lowRadialHs_lip (I := I) (M := M) g hρ).continuous

theorem lowRadialHs_aemeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {u : Ω → metricH2 (I := I) (M := M) g}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowRadialHs (I := I) (M := M) g ρ (u t)) μ :=
  (lowRadialHs_cont (I := I) (M := M) g hρ).comp_aestronglyMeasurable hu

theorem lowRadialHs_core
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (T : SmoothCcTensor g 0 2) :
    lowRadialHs (I := I) (M := M) g ρ
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)
        (lowRadial (I := I) (M := M) g ρ T) := by
  let x : lowCore (I := I) (M := M) g :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      (radialCore_lip (I := I) (M := M) g hρ).continuous x
  have hrep : lowRep (I := I) (M := M) g x = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
    simpa only [ccToHsLin_apply, x] using
      lowRep_spec (I := I) (M := M) g x
  simpa only [lowRadialHs, radialCore, x, hrep] using hext

@[simp] theorem lowRadialHs_zero
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    lowRadialHs (I := I) (M := M) g ρ 0 = 0 := by
  simpa only [map_zero, lowRadial_zero] using
    lowRadialHs_core (I := I) (M := M) g hρ
      (0 : SmoothCcTensor g 0 2)

theorem lowRadialH3_incl
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    incl32 (I := I) (M := M) g
        (lowRadialH3 (I := I) (M := M) g ρ u) =
      lowRadialHs (I := I) (M := M) g ρ
        (incl32 (I := I) (M := M) g u) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact (incl32 (I := I) (M := M) g).continuous.comp
      (lowRadialH3_cont (I := I) (M := M) g hρ)
  · exact (lowRadialHs_cont (I := I) (M := M) g hρ.le).comp
      (incl32 (I := I) (M := M) g).continuous
  · intro T
    rw [lowRadialH3_core (I := I) (M := M) g hρ]
    simp only [ccToHsLin_apply, incl32_ccToHs]
    simpa only [ccToHsLin_apply] using
      (lowRadialHs_core (I := I) (M := M) g hρ.le T).symm

theorem lowRadialH3_eq
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    lowRadialH3 (I := I) (M := M) g ρ u =
      lowScaleCutoff (incl32 (I := I) (M := M) g) ρ
        (symmHs (I := I) (M := M) g (by norm_num) u) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on u (isClosed_eq ?_ ?_) ?_
  · exact lowRadialH3_cont (I := I) (M := M) g hρ
  · exact
      (lowScaleCutoff_cont (incl32 (I := I) (M := M) g)
        (tensorHsInclusion_injective (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (by norm_num)) hρ).comp
        (symmHs (I := I) (M := M) g (by norm_num)).continuous
  · intro T
    rw [lowRadialH3_core (I := I) (M := M) g hρ]
    simp only [ccToHsLin_apply]
    rw [lowRadial_h3_eq (I := I) (M := M)]
    have hs := symmHs_core (I := I) (M := M)
      (σ := (3 : ℝ)) g (by norm_num) T
    simp only [ccToHsLin_apply] at hs
    rw [hs]

theorem radialCLM_h3
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    radialCLM (I := I) (M := M) g (by norm_num) ρ
        (incl32 (I := I) (M := M) g u) u =
      lowRadialH3 (I := I) (M := M) g ρ u := by
  rw [lowRadialH3_eq (I := I) (M := M) g hρ]
  unfold radialCLM radialScale lowScaleCutoff
  simp only [smul_apply]
  have h := DFunLike.congr_fun
    (symmHs_incl (I := I) (M := M) g
      (τ := (2 : ℝ)) (σ := (3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)) u
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]

theorem lowRadialHs_eq
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : metricH2 (I := I) (M := M) g) :
    lowRadialHs (I := I) (M := M) g ρ v =
      ballRetraction ρ
        (symmHs (I := I) (M := M) g (by norm_num) v) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq ?_ ?_) ?_
  · exact lowRadialHs_cont (I := I) (M := M) g hρ
  · exact (lipschitzWith_one_ballRetraction hρ).continuous.comp
      (symmHs (I := I) (M := M) g (by norm_num)).continuous
  · intro T
    rw [lowRadialHs_core (I := I) (M := M) g hρ,
      symmHs_core (I := I) (M := M)]
    simp only [ccToHsLin_apply, lowRadial, ballRetraction,
      ccTensorToHs_smul]

theorem radialCLM_h2
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : metricH2 (I := I) (M := M) g) :
    radialCLM (I := I) (M := M) g (by norm_num) ρ v v =
      lowRadialHs (I := I) (M := M) g ρ v := by
  rw [lowRadialHs_eq (I := I) (M := M) g hρ]
  rfl

theorem lowRadialH3_aemeas
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    {u : Ω → metricThirdOrderSobolev (I := I) (M := M) g}
    (hu : AEStronglyMeasurable u μ) :
    AEStronglyMeasurable
      (fun t => lowRadialH3 (I := I) (M := M) g ρ (u t)) μ :=
  (lowRadialH3_cont (I := I) (M := M) g hρ).comp_aestronglyMeasurable hu

theorem lowRadialHs_norm
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (u : metricH2 (I := I) (M := M) g) :
    ‖lowRadialHs (I := I) (M := M) g ρ u‖ ≤ ρ := by
  let D : Set (metricH2 (I := I) (M := M) g) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
  let C : Set (metricH2 (I := I) (M := M) g) :=
    {v | ‖lowRadialHs (I := I) (M := M) g ρ v‖ ≤ ρ}
  have hcont : Continuous (lowRadialHs (I := I) (M := M) g ρ) :=
    (lowRadialHs_lip (I := I) (M := M) g hρ).continuous
  have hclosed : IsClosed C := by
    exact isClosed_le hcont.norm continuous_const
  have hsub : D ⊆ C := by
    rintro v ⟨T, rfl⟩
    change ‖lowRadialHs (I := I) (M := M) g ρ
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T)‖ ≤ ρ
    rw [lowRadialHs_core (I := I) (M := M) g hρ]
    simpa only [ccToHsLin_apply] using
      lowRadial_norm (I := I) (M := M) g hρ T
  have hD : Dense D :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  have hC : C = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← hD.closure_eq]
    exact hclosed.closure_subset_iff.mpr hsub
  have hu : u ∈ C := by
    rw [hC]
    trivial
  exact hu

theorem lowRadialH3_norm
    (g : SmoothRiemannianMetric I M) {ρ : ℝ} (hρ : 0 < ρ)
    (u : metricThirdOrderSobolev (I := I) (M := M) g) :
    ‖incl32 (I := I) (M := M) g
        (lowRadialH3 (I := I) (M := M) g ρ u)‖ ≤ ρ := by
  rw [lowRadialH3_incl (I := I) (M := M) g hρ]
  exact lowRadialHs_norm (I := I) (M := M) g hρ.le _

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem zeroBound
    (g : SmoothRiemannianMetric I M) {δ : ℝ} (hδ : 0 ≤ δ) :
    gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ := by
  intro x u v
  refine
    (gFibreOpBound_ccTensorBilinSymm_zero
      (I := I) (M := M) g x u v).trans ?_
  simp only [zero_mul]
  exact mul_nonneg
    (mul_nonneg hδ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem exists_lowRadius
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ 0 ≤ δ ∧ δ ≤ 1 / 3 ∧
      ∀ S : SmoothCcTensor g 0 2,
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g S) δ := by
  obtain ⟨C, hC, hbound⟩ := hs2_op_bound (I := I) (M := M) hDim g
  let δ : ℝ := 1 / 3
  let ρ : ℝ := δ / C
  have hδ : 0 < δ := by
    norm_num [δ]
  have hρ : 0 < ρ := div_pos hδ hC
  refine ⟨ρ, δ, hρ, hδ.le, by simp only [δ]; exact le_rfl, ?_⟩
  intro S hS
  have hscale :
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ δ := by
    calc
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖
          ≤ C * ρ := mul_le_mul_of_nonneg_left hS hC.le
      _ = δ := by
        simp only [ρ]
        field_simp
  intro x u v
  refine (hbound S x u v).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hscale (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

noncomputable def lowCoreActionCoefficients
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) : LowerScaleActionCoefficients g :=
  lowerScaleActionCoefficients (I := I) (M := M) g g
    (lowRadial (I := I) (M := M) g ρ T)
    (lt_of_le_of_lt hδ_le (by norm_num))
    (hreal _ (lowRadial_norm (I := I) (M := M) g hρ T))
    (zeroBound (I := I) (M := M) g hδ0)

abbrev lowerScaleSecondOrderActionFourthToSecondOrderSpace (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
    TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev lowerScaleSecondOrderActionThirdToFirstOrderSpace (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable def lowerScaleSecondOrderActionFourthToSecondOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    lowCore (I := I) (M := M) g → lowerScaleSecondOrderActionFourthToSecondOrderSpace (I := I) (M := M) g :=
  fun x =>
    (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (lowRep (I := I) (M := M) g x)).secondOrderActionFourthToSecondOrder (I := I) (M := M)

private noncomputable def lowerScaleSecondOrderActionThirdToFirstOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    lowCore (I := I) (M := M) g → lowerScaleSecondOrderActionThirdToFirstOrderSpace (I := I) (M := M) g :=
  fun x =>
    (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (lowRep (I := I) (M := M) g x)).secondOrderActionThirdToFirstOrder (I := I) (M := M)

private theorem lowerScaleSecondOrderActionFourthToSecondOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleSecondOrderActionFourthToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder
        (I := I) (M := M) := by
  have hrep :
      lowRep (I := I) (M := M) g
          ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
    simpa only [ccToHsLin_apply] using
      lowRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowerScaleSecondOrderActionFourthToSecondOrderCore, hrep]

private theorem lowerScaleSecondOrderActionThirdToFirstOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleSecondOrderActionThirdToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder
        (I := I) (M := M) := by
  have hrep :
      lowRep (I := I) (M := M) g
          ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (2 : ℝ)
    simpa only [ccToHsLin_apply] using
      lowRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowerScaleSecondOrderActionThirdToFirstOrderCore, hrep]

namespace LowerScaleTimeInternal

abbrev LowCore (g : SmoothRiemannianMetric I M) :=
  lowCore (I := I) (M := M) g

abbrev SecondOrderActionFourthToSecondOrderSpace (g : SmoothRiemannianMetric I M) :=
  lowerScaleSecondOrderActionFourthToSecondOrderSpace (I := I) (M := M) g

abbrev SecondOrderActionThirdToFirstOrderSpace (g : SmoothRiemannianMetric I M) :=
  lowerScaleSecondOrderActionThirdToFirstOrderSpace (I := I) (M := M) g

noncomputable def secondOrderActionFourthToSecondOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    LowCore (I := I) (M := M) g → SecondOrderActionFourthToSecondOrderSpace (I := I) (M := M) g :=
  lowerScaleSecondOrderActionFourthToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal

noncomputable def secondOrderActionThirdToFirstOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    LowCore (I := I) (M := M) g → SecondOrderActionThirdToFirstOrderSpace (I := I) (M := M) g :=
  lowerScaleSecondOrderActionThirdToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal

theorem secondOrderActionFourthToSecondOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    secondOrderActionFourthToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder
        (I := I) (M := M) :=
  lowerScaleSecondOrderActionFourthToSecondOrderCore_value (I := I) (M := M) g hρ hδ0 hδ_le hreal T

theorem secondOrderActionThirdToFirstOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    secondOrderActionThirdToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder
        (I := I) (M := M) :=
  lowerScaleSecondOrderActionThirdToFirstOrderCore_value (I := I) (M := M) g hρ hδ0 hδ_le hreal T

end LowerScaleTimeInternal

noncomputable def lowerScaleSecondOrderActionFourthToSecondOrder
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowerScaleSecondOrderActionFourthToSecondOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowerScaleSecondOrderActionFourthToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)

noncomputable def lowerScaleSecondOrderActionThirdToFirstOrder
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricH2 (I := I) (M := M) g → lowerScaleSecondOrderActionThirdToFirstOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowerScaleSecondOrderActionThirdToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)

abbrev lowerScaleFirstOrderActionThirdToSecondOrderSpace (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
    TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)

private abbrev lowerScaleFirstOrderActionSecondToFirstOrderSpace (g : SmoothRiemannianMetric I M) :=
  TensorHs (I := I) (M := M) g 0 2 (2 : ℝ) →L[ℝ]
    TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)

private noncomputable def lowerScaleFirstOrderActionThirdToSecondOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    highCore (I := I) (M := M) g → lowerScaleFirstOrderActionThirdToSecondOrderSpace (I := I) (M := M) g :=
  fun x =>
    (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (highRep (I := I) (M := M) g x)).firstOrderActionThirdToSecondOrder (I := I) (M := M)

private noncomputable def lowerScaleFirstOrderActionSecondToFirstOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    highCore (I := I) (M := M) g → lowerScaleFirstOrderActionSecondToFirstOrderSpace (I := I) (M := M) g :=
  fun x =>
    (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal
      (highRep (I := I) (M := M) g x)).firstOrderActionSecondToFirstOrder (I := I) (M := M)

private theorem lowerScaleFirstOrderActionThirdToSecondOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleFirstOrderActionThirdToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
        (I := I) (M := M) := by
  have hrep :
      highRep (I := I) (M := M) g
          ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (3 : ℝ)
    simpa only [ccToHsLin_apply] using
      highRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowerScaleFirstOrderActionThirdToSecondOrderCore, hrep]

private theorem lowerScaleFirstOrderActionSecondToFirstOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleFirstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
        (I := I) (M := M) := by
  have hrep :
      highRep (I := I) (M := M) g
          ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ = T := by
    apply ccToHs_injective (I := I) (M := M) g 2 (3 : ℝ)
    simpa only [ccToHsLin_apply] using
      highRep_spec (I := I) (M := M) g
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩
  simp only [lowerScaleFirstOrderActionSecondToFirstOrderCore, hrep]

namespace LowerScaleTimeInternal

abbrev HighCore (g : SmoothRiemannianMetric I M) :=
  highCore (I := I) (M := M) g

abbrev FirstOrderActionThirdToSecondOrderSpace (g : SmoothRiemannianMetric I M) :=
  lowerScaleFirstOrderActionThirdToSecondOrderSpace (I := I) (M := M) g

abbrev FirstOrderActionSecondToFirstOrderSpace (g : SmoothRiemannianMetric I M) :=
  lowerScaleFirstOrderActionSecondToFirstOrderSpace (I := I) (M := M) g

noncomputable def firstOrderActionThirdToSecondOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    HighCore (I := I) (M := M) g → FirstOrderActionThirdToSecondOrderSpace (I := I) (M := M) g :=
  lowerScaleFirstOrderActionThirdToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal

noncomputable def firstOrderActionSecondToFirstOrderCore
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    HighCore (I := I) (M := M) g → FirstOrderActionSecondToFirstOrderSpace (I := I) (M := M) g :=
  lowerScaleFirstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal

theorem firstOrderActionThirdToSecondOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    firstOrderActionThirdToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).firstOrderActionThirdToSecondOrder
        (I := I) (M := M) :=
  lowerScaleFirstOrderActionThirdToSecondOrderCore_value (I := I) (M := M) g hρ hδ0 hδ_le hreal T

theorem firstOrderActionSecondToFirstOrderCore_value
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    firstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal
        ⟨ccToHsLin (I := I) (M := M) g 2 (3 : ℝ) T, ⟨T, rfl⟩⟩ =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).firstOrderActionSecondToFirstOrder
        (I := I) (M := M) :=
  lowerScaleFirstOrderActionSecondToFirstOrderCore_value (I := I) (M := M) g hρ hδ0 hδ_le hreal T

end LowerScaleTimeInternal

noncomputable def lowerScaleFirstOrderActionThirdToSecondOrder
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricThirdOrderSobolev (I := I) (M := M) g → lowerScaleFirstOrderActionThirdToSecondOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowerScaleFirstOrderActionThirdToSecondOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)

noncomputable def lowerScaleFirstOrderActionSecondToFirstOrder
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    metricThirdOrderSobolev (I := I) (M := M) g → lowerScaleFirstOrderActionSecondToFirstOrderSpace (I := I) (M := M) g :=
  Dense.extend
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
    (lowerScaleFirstOrderActionSecondToFirstOrderCore (I := I) (M := M) g hρ hδ0 hδ_le hreal)

theorem lowCore_split
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (T : SmoothCcTensor g 0 2) :
    let S := lowRadial (I := I) (M := M) g ρ T
    let A := lowCoreActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T
    deTurckSmoothRemainder (I := I) g g S
          (lt_of_le_of_lt hδ_le (by norm_num))
          (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
        deTurckSmoothRemainder (I := I) g g
          (0 : SmoothCcTensor g 0 2)
          (lt_of_le_of_lt hδ_le (by norm_num))
          (zeroBound (I := I) (M := M) g hδ0) =
      A.secondOrderAction (I := I) (M := M) S + A.firstOrderAction (I := I) (M := M) S := by
  obtain ⟨κ, D, hκ, hD, hdiag⟩ :=
    exists_ricciDeTurckRemainder_diagonal_secondOrder_bound (I := I) (M := M) hDim g
  let S := lowRadial (I := I) (M := M) g ρ T
  let R := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 S)
  let B := Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 S)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hR2 :
      covariantJetNormSq (I := I) (M := M) g 2 S ≤ R ^ 2 := by
    rw [show R ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 S by
      exact Real.sq_sqrt
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hB2 :
      covariantJetNormSq (I := I) (M := M) g 3 S ≤ B ^ 2 := by
    rw [show B ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 S by
      exact Real.sq_sqrt
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hs := hdiag S
    (lowRadial_symm (I := I) (M := M) g ρ T)
    hδ_le hδ0
    (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
    (zeroBound (I := I) (M := M) g hδ0)
    R B hR hB hR2 hB2
  change deTurckSmoothRemainder (I := I) (M := M) g g S
        (lt_of_le_of_lt hδ_le (by norm_num))
        (hreal S (lowRadial_norm (I := I) (M := M) g hρ T)) -
      deTurckSmoothRemainder (I := I) (M := M) g g
        (0 : SmoothCcTensor g 0 2)
        (lt_of_le_of_lt hδ_le (by norm_num))
        (zeroBound (I := I) (M := M) g hδ0) =
      (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).secondOrderAction
          (I := I) (M := M) S +
        (lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T).firstOrderAction
          (I := I) (M := M) S
  rw [show lowCoreActionCoefficients (I := I) (M := M) g hρ hδ0 hδ_le hreal T =
      lowerScaleActionCoefficients (I := I) (M := M) g g S
        (lt_of_le_of_lt hδ_le (by norm_num))
        (hreal S (lowRadial_norm (I := I) (M := M) g hρ T))
        (zeroBound (I := I) (M := M) g hδ0) by rfl]
  exact hs.1

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
