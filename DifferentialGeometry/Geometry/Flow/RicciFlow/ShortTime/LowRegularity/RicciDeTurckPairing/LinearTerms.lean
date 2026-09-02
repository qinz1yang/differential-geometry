import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lipschitz
import DifferentialGeometry.Analysis.Estimates.QuarticInterpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Interpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.JetDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.JetProduct
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.LieCorrection.ZeroOrder.ReindexedPureTraceCovariantJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds

section

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (quartic_product_sum_le_interpolation_square
  sq_add_sq_le_sq_add_of_nonneg three_term_sq_le_weighted_product)
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private lemma unit_interval_sq_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    s ^ 2 ≤ 1 := by
  nlinarith

private lemma one_le_one_add_sq {A : ℝ} (hA : 0 ≤ A) :
    1 ≤ (1 + A) ^ 2 := by
  nlinarith

private lemma sq_le_one_add_sq {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ (1 + A) ^ 2 := by
  nlinarith

private local instance instCompleteSpaceE_linearTerms : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricLoweredConnectionDifference_self
    (g : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g g g = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  apply ContinuousMultilinearMap.ext
  intro m
  have hm : m = fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m i)) := by
    funext i
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hm, metricLoweredConnectionDifference_unitModel_apply]
  simp only [PDE.DeTurck.connectionDifference_self, Pi.zero_apply,
    zero_apply, map_zero]
  rfl
theorem exists_metricLoweredConnectionDifference_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hw⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  let B : ℝ → ℝ := fun R => B0 0 + B1 0 + B1 0 * R
  refine ⟨B, ?_, ?_⟩
  · intro R hR
    exact add_nonneg
      (add_nonneg (hB0 0 (by norm_num)) (hB1 0 (by norm_num)))
      (mul_nonneg (hB1 0 (by norm_num)) hR)
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ
    R A hR hA hT2 hT3
  let J2 : ℝ := covariantJetNormSq (I := I) (M := M) g 2 T
  let D2 : ℝ := Real.sqrt J2
  have hJ2 : 0 ≤ J2 :=
    covariantJetNormSq_nonneg (I := I) (M := M) g T
  have hD2 : 0 ≤ D2 := Real.sqrt_nonneg _
  have hD2sq : D2 ^ 2 = J2 := by
    simpa only [D2] using Real.sq_sqrt hJ2
  have hJ23 : J2 ≤ covariantJetNormSq (I := I) (M := M) g 3 T := by
    simpa only [J2] using
      covariantJetNormSq_mono (I := I) (M := M) g (by omega : 2 ≤ 3) T
  have hD2A : D2 ≤ A := by
    nlinarith
  have hD2R : D2 ≤ R := by
    have : J2 ≤ R ^ 2 := by simpa only [J2] using hT2
    nlinarith
  have hZsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x u v =
        ccTensorBilin (I := I) g
          (0 : SmoothCcTensor g 0 2) x v u := by
    intro x u v
    rw [ccTensorBilin_zero, ccTensorBilin_zero]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero,
      ccTensorBilin_zero]
    ring_nf
  have hraw := hw gT g g T (0 : SmoothCcTensor g 0 2)
    hT hZsymm hTtie hZtie
    hδ_le hδ0 hδT hδ_le hδ0 hδZ
    0 A D2 A (by norm_num) hA hD2 hA
    (by
      rw [covariantJetNormSq_zero]
      norm_num)
    hT3
    (by
      rw [sub_zero]
      change J2 ≤ D2 ^ 2
      rw [hD2sq])
    (by simpa only [sub_zero] using hT3)
  have hraw' :
      covariantJetNormSq (I := I) (M := M) g 2
          (metricLoweredConnectionDifference (I := I) (M := M) g gT g) ≤
        (B0 0 * A + B1 0 * D2 + B1 0 * A * D2) ^ 2 := by
    simpa only [metricLoweredConnectionDifference_self, sub_zero] using hraw
  have hB00 : 0 ≤ B0 0 := hB0 0 (by norm_num)
  have hB10 : 0 ≤ B1 0 := hB1 0 (by norm_num)
  have hmid : B1 0 * D2 ≤ B1 0 * A :=
    mul_le_mul_of_nonneg_left hD2A hB10
  have hlast : B1 0 * A * D2 ≤ B1 0 * A * R :=
    mul_le_mul_of_nonneg_left hD2R (mul_nonneg hB10 hA)
  have hlin :
      B0 0 * A + B1 0 * D2 + B1 0 * A * D2 ≤ B R * A := by
    simp only [B]
    nlinarith
  have hlin0 :
      0 ≤ B0 0 * A + B1 0 * D2 + B1 0 * A * D2 :=
    add_nonneg
      (add_nonneg (mul_nonneg hB00 hA) (mul_nonneg hB10 hD2))
      (mul_nonneg (mul_nonneg hB10 hA) hD2)
  exact hraw'.trans (pow_le_pow_left₀ hlin0 hlin 2)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
  [SigmaCompactSpace M] in
private lemma rankZeroTensor_eq_smul_unit (x : M) (c : Tensor0SSpace 0 I x) :
    c = Tensor0SSpace.toModel c (fun i : Fin 0 => i.elim0) •
      unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  beta_reduce
  rw [Tensor0SSpace.toModel_smul, smul_apply,
    smul_eq_mul]
  have h1 : Tensor0SSpace.toModel
      (unitTensor (I := I) (M := M) x) v = (1 : ℝ) := rfl
  rw [h1, mul_one]
  congr 1
  funext i
  exact i.elim0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma metricConnectionDifferenceLoweredCoefficient_unitModel
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 3 → TangentSpace I x) :
    unitModel (I := I) (M := M) g₀ 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun i => tangentSpaceModelContinuousLinearEquiv (I := I) x (m i)) =
      g₁.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x (m 0) (m 1)) (m 2) := by
  rw [unitModel]
  rw [show (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x
      (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E)
          (E := (TangentSpace I : M → Type _)) x).smulRight
        (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x)
        (ContinuousMultilinearMap.constOfIsEmpty ℝ
          (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  exact metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x m

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma metricLoweredConnectionDifferenceTensorProduct_eq_slotExtension
    (g₀ g₁ : SmoothRiemannianMetric I M) (x : M)
    (B : Tensor0SSpace 1 I x) :
    Tensor0SSpace.toModel
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) x
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ x) B) =
      Tensor0SSpace.toModel
        (DifferentialGeometry.Integral.Connection.slotExtendFib
          (I := I) (M := M) 0 3 x
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
          B) := by
  classical
  apply ContinuousMultilinearMap.ext
  intro u
  rw [show (u : Fin 4 → E) = Fin.cons (u 0) (Fin.tail u) from
    (Fin.cons_self_tail u).symm]
  rw [tensor0SProdKappaFib_apply, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  rw [DifferentialGeometry.Integral.Connection.slotExtendFib_apply_eval
    (I := I) (M := M) 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
    B (u 0) (Fin.tail u)]
  have hc : tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) •
        unitTensor (I := I) (M := M) x := by
    have h2 := rankZeroTensor_eq_smul_unit (I := I) (M := M) x
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x B
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (u 0)))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M)
      (T := B) (v0 := u 0) (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  have hm : (fun j => Fin.tail u j) =
      fun j => tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (Fin.tail u j)) := by
    funext j
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [hm, metricConnectionDifferenceLoweredCoefficient_unitModel (I := I) (M := M) g₀ g₁ x
    (fun j => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (Fin.tail u j))]
  have hcast : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.castAdd 3) = (fun _ : Fin 1 => u 0) := by
    funext i
    fin_cases i
    rfl
  have hnat : ((Fin.cons (u 0) (Fin.tail u) : Fin 4 → E) ∘
      Fin.natAdd 1) = Fin.tail u := by
    funext j
    have hj : Fin.natAdd 1 j = Fin.succ j := by
      apply Fin.ext
      simp [Fin.natAdd, Fin.succ, Nat.add_comm]
    change Fin.cons (u 0) (Fin.tail u) (Fin.natAdd 1 j) = Fin.tail u j
    rw [hj, Fin.cons_succ]
  rw [hcast, hnat]
  rw [metricConnectionDifferenceLoweredFib_toModel (I := I) g₁ g₁ g₀ x
    (fun j => Fin.tail u j)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_toModel_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ∀ (y : M) (d : Tensor0SSpace 1 I y),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
            (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
        ContinuousMultilinearMap.domDomCongr LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
              (slotExtend (I := I) (M := M) g₀ 0 3
                (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀)).toSection
                  y) d)) := by
  intro y d
  rw [show ((show Tensor0SSpace 1 I y →L[ℝ] Tensor0SSpace 4 I y from
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g₀ g₁).toSection y) d) =
      domDomCongrFibRank (I := I) 4 LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation y
        (tensor0SProdKappaFib (I := I) (p := 1) (q := 3) y
          (metricConnectionDifferenceLoweredFib (I := I) g₁ g₁ g₀ y) d) from rfl]
  rw [domDomCongrFibRank_apply, Tensor0SSpace.toModel_ofModel]
  exact congrArg
    (ContinuousMultilinearMap.domDomCongr LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation)
    (metricLoweredConnectionDifferenceTensorProduct_eq_slotExtension
      (I := I) (M := M) g₀ g₁ y d)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
theorem lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_eq_rsDomDomCongrSection_slotExtend
    (g gm : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm =
      rsDomDomCongrSection (I := I) (M := M) g 1 4
        LieCorrectionZeroCore.lieCorrectionZeroVectorBundleTracePermutation
        (slotExtend (I := I) (M := M) g 0 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  beta_reduce
  rw [rsDomDomCongrSection_toSection, toModel_rsDomDomCongr_apply]
  exact lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_toModel_eq
    (I := I) (M := M) g gm x d

theorem covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le
    (g gm : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2 (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) := by
  rw [lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_eq_rsDomDomCongrSection_slotExtend, covariantJetNormSq_rsDomDomCongrSection]
  exact covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _

theorem covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sub_le
    (g gT gU : SmoothRiemannianMetric I M) :
    covariantJetNormSq (I := I) (M := M) g 2
        (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gT -
          lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gU) ≤
      (Module.finrank ℝ E : ℝ) *
        covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gU g) := by
  rw [lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_eq_rsDomDomCongrSection_slotExtend, lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_eq_rsDomDomCongrSection_slotExtend, ← rsDomDomCongrSection_sub, ← slotExtend_sub, covariantJetNormSq_rsDomDomCongrSection]
  exact covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 3 _

theorem exists_lieCorrectionZeroVectorBundle_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) -
            lieCorrectionZeroVectorBundle (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Cout, hCout, happOut⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 4 2
  obtain ⟨Cin, hCin, happIn⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 1 4
  obtain ⟨Cipp, hCipp, happIp⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 3 1
  obtain ⟨Cw, hCw, happW⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 1
  obtain ⟨ρt1, Ct1, hρt1, hCt1, htp1⟩ :=
    RicciDeTurckLowOrder.trace1_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb1, Bt1, hρb1, hBt1, htb1⟩ :=
    RicciDeTurckLowOrder.trace_one_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨ρt2, Ct2, hρt2, hCt2, htp2⟩ :=
    RicciDeTurckLowOrder.trace2_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb2, Bt2, hρb2, hBt2, htb2⟩ :=
    RicciDeTurckLowOrder.trace_two_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨B0m, B1m, hB0m, hB1m, hmcdp⟩ :=
    RicciDeTurckLowOrder.mcd_pair_h2 (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bm, hBm, hmcdb⟩ :=
    RicciDeTurckLowOrder.metric_connection_difference_coefficient_sobolev_two_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨W0, W1, hW0, hW1, hwxip⟩ :=
    exists_metricLoweredConnectionDifference_covariantJetNormSq_two_sub_tame_bound (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  obtain ⟨Bs, hBs, hwxib⟩ := exists_metricLoweredConnectionDifference_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cip, hCip, hinterp⟩ := covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  have hfr2 : (0 : ℝ) ≤ fr ^ 2 := sq_nonneg _
  set Jp : ℝ := covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g)
    with hJpdef
  have hJp : 0 ≤ Jp := covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _
  set ρ : ℝ := min (min ρt1 ρb1) (min ρt2 ρb2) with hρdef
  have hρ0 : 0 < ρ :=
    lt_min (lt_min hρt1 hρb1) (lt_min hρt2 hρb2)
  let Cs : ℝ → ℝ := fun R => (Bs R) ^ 2
  let M5 : ℝ → ℝ := fun R => 2 * (B0m R + B1m R) ^ 2 + 2 * (B1m R) ^ 2
  let M5w : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Wb : ℝ → ℝ := fun R => Cw * Bt1 ^ 2 * Cs R
  let Wm : ℝ → ℝ := fun R =>
    2 * (Cw * Ct1 ^ 2 * Cs R + Cw * Bt1 ^ 2 * M5w R)
  let Ib : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wb R
  let Im : ℝ → ℝ := fun R => Cipp * Jp * fr ^ 2 * Wm R
  let Vb : ℝ → ℝ := fun R => fr * (Bm R) ^ 2
  let Vd : ℝ → ℝ := fun R => fr * M5 R
  let Sin : ℝ → ℝ := fun R => Cin * Vb R * Ib R
  let Kv : ℝ → ℝ := fun R => Cin * Vd R * Ib R
  let Ki : ℝ → ℝ := fun R => Cin * Vb R * Im R
  let K1 : ℝ → ℝ := fun R => Cout * Ct2 ^ 2 * Sin R
  let K2 : ℝ → ℝ := fun R => Cout * Bt2 ^ 2 * (2 * (Kv R + Ki R))
  let Bh : ℝ → ℝ := fun R => 4 * (2 * (K1 R + K2 R))
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hCs : ∀ R : ℝ, 0 ≤ R → 0 ≤ Cs R := fun R hR => sq_nonneg _
  have hM5 : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5 R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (B0m R + B1m R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (B1m R) ^ 2 := by positivity
    simpa only [M5] using add_nonneg h1 h2
  have hM5w : ∀ R : ℝ, 0 ≤ R → 0 ≤ M5w R := fun R hR => by
    have h1 : (0 : ℝ) ≤ 2 * (W0 R + W1 R) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ 2 * (W1 R) ^ 2 := by positivity
    simpa only [M5w] using add_nonneg h1 h2
  have hWb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wb R := fun R hR =>
    mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
  have hWm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Wm R := fun R hR => by
    have h1 : (0 : ℝ) ≤ Cw * Ct1 ^ 2 * Cs R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hCs R hR)
    have h2 : (0 : ℝ) ≤ Cw * Bt1 ^ 2 * M5w R :=
      mul_nonneg (mul_nonneg hCw (sq_nonneg _)) (hM5w R hR)
    simpa only [Wm] using
      mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (add_nonneg h1 h2)
  have hIb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ib R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWb R hR)
  have hIm : ∀ R : ℝ, 0 ≤ R → 0 ≤ Im R := fun R hR =>
    mul_nonneg (mul_nonneg (mul_nonneg hCipp hJp) hfr2) (hWm R hR)
  have hVb : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vb R := fun R hR =>
    mul_nonneg hfr (sq_nonneg _)
  have hVd : ∀ R : ℝ, 0 ≤ R → 0 ≤ Vd R := fun R hR =>
    mul_nonneg hfr (hM5 R hR)
  have hSin : ∀ R : ℝ, 0 ≤ R → 0 ≤ Sin R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIb R hR)
  have hKv : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kv R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVd R hR)) (hIb R hR)
  have hKi : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ki R := fun R hR =>
    mul_nonneg (mul_nonneg hCin (hVb R hR)) (hIm R hR)
  have hK1 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K1 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _)) (hSin R hR)
  have hK2 : ∀ R : ℝ, 0 ≤ R → 0 ≤ K2 R := fun R hR =>
    mul_nonneg (mul_nonneg hCout (sq_nonneg _))
      (mul_nonneg (by norm_num) (add_nonneg (hKv R hR) (hKi R hR)))
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := fun R hR => by
    simp only [Bh]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by norm_num) (add_nonneg (hK1 R hR) (hK2 R hR)))
  refine ⟨ρ, B0, B1, hρ0,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hs2 : s ^ 2 ≤ (1 : ℝ) := unit_interval_sq_le_one hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem
        (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw :=
      convexPerturbation_gFibreOpBound_abs
        (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP4 : covariantJetNormSq (I := I) (M := M) g 4 P ≤ A4 ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g T) hs2).trans hT4
  have hQ4 : covariantJetNormSq (I := I) (M := M) g 4 Q ≤ A4 ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 4) g U) hs2).trans hU4
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hball : ∀ ρ' : ℝ, ρ ≤ ρ' →
      (‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρ' ∧
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρ') := by
    intro ρ' hρ'
    constructor
    · rw [hcP, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hTn.trans hρ'))
    · rw [hcQ, ccTensorToHs_smul, norm_smul]
      exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
        (by simpa using (hUn.trans hρ'))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by
      rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hP3i : covariantJetNormSq (I := I) (M := M) g 3 P ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp P R A4 hR hA4 hP2 hP4
  have hQ3i : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp Q R A4 hR hA4 hQ2 hQ4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    exact one_le_one_add_sq ha0
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : a ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_sq ha0
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact add_nonneg (sq_nonneg D3) (sq_nonneg N)
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_right (sq_nonneg N)
  have hD3u : D3 ^ 2 ≤ pl2 * u := by
    calc D3 ^ 2 ≤ u := hD3le
      _ = 1 * u := (one_mul u).symm
      _ ≤ pl2 * u := mul_le_mul_of_nonneg_right hpl21 hu0
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    exact le_add_of_nonneg_left (sq_nonneg D3)
  have hpl2u : 0 ≤ pl2 * u := mul_nonneg hpl20 hu0
  set mcdT : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g with hmT
  set mcdU : SmoothCcTensor g 0 3 :=
    metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g with hmU
  set cdT : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmT with hcdT
  set cdU : SmoothCcTensor g 0 3 :=
    metricLoweredConnectionDifferenceCoefficient (I := I) g gmU with hcdU
  set Tr1T : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmT 1 (Equiv.refl (Fin 3)) with hTr1T
  set Tr1U : SmoothCcTensor g 3 1 :=
    reindexedPureTrace (I := I) (M := M) g gmU 1 (Equiv.refl (Fin 3)) with hTr1U
  set WT : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmT g with hWTdef
  set WU : SmoothCcTensor g 0 1 :=
    deTurckVectorFieldCovector (I := I) (M := M) g gmU g with hWUdef
  set IpT : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WT with hIpT
  set IpU : SmoothCcTensor g 2 1 := ipLowCc (I := I) (M := M) g WU with hIpU
  set VmT : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmT with hVmT
  set VmU : SmoothCcTensor g 1 4 := lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gmU with hVmU
  set LvT : SmoothCcTensor g 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g gmT with hLvT
  set LvU : SmoothCcTensor g 4 2 :=
    reindexedCometricDoubleTrace (I := I) (M := M) g gmU with hLvU
  set InT : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmT IpT with hInT
  set InU : SmoothCcTensor g 2 4 :=
    ccOperatorFieldComp (I := I) (M := M) g 2 1 4 VmU IpU with hInU
  have hρc : ρ ≤ ρt1 ∧ ρ ≤ ρb1 ∧ ρ ≤ ρt2 ∧ ρ ≤ ρb2 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · rw [hρdef]
        first
        | exact le_trans (min_le_left _ _) (min_le_left _ _)
        | exact le_trans (min_le_left _ _) (min_le_right _ _)
        | exact le_trans (min_le_right _ _) (min_le_left _ _)
        | exact le_trans (min_le_right _ _) (min_le_right _ _)
  have htrp : ∀ (p : ℕ) (Cp : ℝ) (ρp' : ℝ),
      (∀ (T' U' : SmoothCcTensor g 0 2)
        (gT' gU' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        (∀ (y : M) (v w : TangentSpace I y),
          gU'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g U' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p -
              pureTrace (I := I) (M := M) g gU' p) ≤
          (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
            (T' - U')‖) ^ 2) →
      0 ≤ Cp → ρ ≤ ρp' →
      covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p -
            pureTrace (I := I) (M := M) g gmU p) ≤
        Cp ^ 2 * u := by
    intro p Cp ρp' hpair hCp hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    have h := hpair P Q gmT gmU hPtie hQtie hPn hQn
    refine h.trans ?_
    have h1 : Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖ ≤ Cp * N :=
      mul_le_mul_of_nonneg_left hPQn hCp
    have h2 : (Cp * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (P - Q)‖) ^ 2 ≤ (Cp * N) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _)) h1 2
    refine h2.trans ?_
    have he : (Cp * N) ^ 2 = Cp ^ 2 * N ^ 2 := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hNu (sq_nonneg Cp)
  have htrb : ∀ (p : ℕ) (Bp : ℝ) (ρp' : ℝ),
      (∀ (T' : SmoothCcTensor g 0 2)
        (gT' : SmoothRiemannianMetric I M),
        (∀ (y : M) (v w : TangentSpace I y),
          gT'.inner y v w =
            g.inner y v w + ccTensorBilinSymm (I := I) g T' y v w) →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ ρp' →
        covariantJetNormSq (I := I) (M := M) g 2
            (pureTrace (I := I) (M := M) g gT' p) ≤ Bp ^ 2) →
      ρ ≤ ρp' →
      (covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmT p) ≤ Bp ^ 2 ∧
        covariantJetNormSq (I := I) (M := M) g 2
          (pureTrace (I := I) (M := M) g gmU p) ≤ Bp ^ 2) := by
    intro p Bp ρp' hbdd hρp'
    obtain ⟨hPn, hQn⟩ := hball ρp' hρp'
    exact ⟨hbdd P gmT hPtie hPn, hbdd Q gmU hQtie hQn⟩
  have htp1' := htrp 1 Ct1 ρt1 htp1 hCt1 hρc.1
  have htb1' := htrb 1 Bt1 ρb1 htb1 hρc.2.1
  have htp2' := htrp 2 Ct2 ρt2 htp2 hCt2 hρc.2.2.1
  have htb2' := htrb 2 Bt2 ρb2 htb2 hρc.2.2.2
  have hmbT : covariantJetNormSq (I := I) (M := M) g 2 mcdT ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmT P hPsymm hPtie hδ_le hδ0 hδP R a hR ha0 hP2 hP3i
    rw [hmT]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring_nf
  have hmbU : covariantJetNormSq (I := I) (M := M) g 2 mcdU ≤ (Bm R) ^ 2 * pl2 := by
    have h := hmcdb gmU Q hQsymm hQtie hδ_le hδ0 hδQ R a hR ha0 hQ2 hQ3i
    rw [hmU]
    refine h.trans (le_of_eq ?_)
    rw [hpl2]
    ring_nf
  have hmpd : covariantJetNormSq (I := I) (M := M) g 2 (mcdT - mcdU) ≤
      M5 R * (pl2 * u) := by
    have h := hmcdp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3 hQ2 hP3i hPQ2 hPQ3
    rw [hmT, hmU]
    refine h.trans ?_
    refine (three_term_sq_le_weighted_product (b0 := B0m R) (b1 := B1m R)
      (a := a) (p := pl2) (u := u) (d := D3)
      hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5]
  have hcdT2 : covariantJetNormSq (I := I) (M := M) g 2 cdT ≤ Cs R * pl2 := by
    rw [hcdT, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT]
    refine (hwxib gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R a hR ha0
      hP2 hP3i).trans ?_
    have he : (Bs R * a) ^ 2 = (Bs R) ^ 2 * a ^ 2 := by ring
    rw [he]
    refine (mul_le_mul_of_nonneg_left hplA2 (sq_nonneg (Bs R))).trans
      (le_of_eq ?_)
    simp only [Cs]
  have hcdd2 : covariantJetNormSq (I := I) (M := M) g 2 (cdT - cdU) ≤
      M5w R * (pl2 * u) := by
    rw [hcdT, hcdU, ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmT,
      ← metricLoweredConnectionDifference_eq_connectionDifferenceLoweredCc (I := I) (M := M) g gmU]
    refine (hwxip gmT gmU g P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδ_le hδ0 hδQ R a D3 D3 hR ha0 hD3 hD3
      hQ2 hP3i hPQ2 hPQ3).trans ?_
    refine (three_term_sq_le_weighted_product (b0 := W0 R) (b1 := W1 R)
      (a := a) (p := pl2) (u := u) (d := D3)
      hpl21 hplA2 hu0 hD3le).trans (le_of_eq ?_)
    simp only [M5w]
  have hTr1T2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1T ≤ Bt1 ^ 2 := by
    rw [hTr1T, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.1
  have hTr1U2 : covariantJetNormSq (I := I) (M := M) g 2 Tr1U ≤ Bt1 ^ 2 := by
    rw [hTr1U, covariantJetNormSq_reindexedPureTrace]
    exact htb1'.2
  have hTr1d2 : covariantJetNormSq (I := I) (M := M) g 2 (Tr1T - Tr1U) ≤
      Ct1 ^ 2 * u := by
    rw [hTr1T, hTr1U, reindexedPureTrace_sub, covariantJetNormSq_reindexCoeffGen]
    exact htp1'
  have hWTform : WT = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1T cdT := by
    rw [hWTdef, hTr1T, hcdT, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWUform : WU = ccOperatorFieldComp (I := I) (M := M) g 0 3 1 Tr1U cdU := by
    rw [hWUdef, hTr1U, hcdU, deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp]
  have hWT2 : covariantJetNormSq (I := I) (M := M) g 2 WT ≤ Wb R * pl2 := by
    rw [hWTform]
    refine (happW Tr1T cdT).trans ?_
    calc
      Cw * covariantJetNormSq (I := I) (M := M) g 2 Tr1T *
          covariantJetNormSq (I := I) (M := M) g 2 cdT ≤
          Cw * Bt1 ^ 2 * (Cs R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hTr1T2 hCw) hcdT2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g cdT)
          (mul_nonneg hCw (sq_nonneg _))
      _ = Wb R * pl2 := by
        simp only [Wb]
        ring
  have hWd2 : covariantJetNormSq (I := I) (M := M) g 2 (WT - WU) ≤ Wm R * (pl2 * u) := by
    rw [hWTform, hWUform]
    refine (covariantJetNormSq_operatorFieldComposition_sub_le
      (I := I) (M := M) g 2 0 3 1
      Cw (Ct1 ^ 2 * u) (Cs R * pl2) (Bt1 ^ 2)
        (M5w R * (pl2 * u)) hCw
      Tr1T Tr1U cdT cdU happW hTr1d2 hcdT2 hTr1U2 hcdd2).trans ?_
    simp only [Wm]
    ring_nf
    exact le_rfl
  have hIpT2 : covariantJetNormSq (I := I) (M := M) g 2 IpT ≤ Ib R * pl2 := by
    rw [hIpT, ipLowCc_eq_ccOperatorFieldComp]
    refine (happIp (ipLowCoeff (I := I) (M := M) g) _).trans ?_
    have hslot : covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 WT) :=
      le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 WT)) ≤
          Cipp * Jp * (fr * (fr * (Wb R * pl2))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWT2 hfr) hfr))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Ib R * pl2 := by
        simp only [Ib]
        ring
  have hIpd2 : covariantJetNormSq (I := I) (M := M) g 2 (IpT - IpU) ≤
      Im R * (pl2 * u) := by
    rw [hIpT, hIpU, ← ipLowCc_sub, ipLowCc_eq_ccOperatorFieldComp]
    refine (happIp (ipLowCoeff (I := I) (M := M) g) _).trans ?_
    have hslot : covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 2
          (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
        fr * (fr * covariantJetNormSq (I := I) (M := M) g 2 (WT - WU)) :=
      le_trans (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 2 _)
        (mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 1 _) hfr)
    calc
      Cipp * covariantJetNormSq (I := I) (M := M) g 2 (ipLowCoeff (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2
            (slotExtend (I := I) (M := M) g 1 2
              (slotExtend (I := I) (M := M) g 0 1 (WT - WU))) ≤
          Cipp * Jp * (fr * (fr * (Wm R * (pl2 * u)))) := by
        refine mul_le_mul (le_of_eq (by rw [hJpdef]))
          (le_trans hslot
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hWd2 hfr) hfr))
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
          (mul_nonneg hCipp hJp)
      _ = Im R * (pl2 * u) := by
        simp only [Im]
        ring
  have hVmT2 : covariantJetNormSq (I := I) (M := M) g 2 VmT ≤ Vb R * pl2 := by
    rw [hVmT]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gmT).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbT
        rw [hmT] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmU2 : covariantJetNormSq (I := I) (M := M) g 2 VmU ≤ Vb R * pl2 := by
    rw [hVmU]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_le (I := I) (M := M) g gmU).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
          fr * ((Bm R) ^ 2 * pl2) := by
        have h := hmbU
        rw [hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vb R * pl2 := by
        simp only [Vb]
        ring
  have hVmd2 : covariantJetNormSq (I := I) (M := M) g 2 (VmT - VmU) ≤
      Vd R * (pl2 * u) := by
    rw [hVmT, hVmU]
    refine (covariantJetNormSq_lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm_sub_le (I := I) (M := M) g gmT gmU).trans ?_
    calc
      fr * covariantJetNormSq (I := I) (M := M) g 2
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmT g -
            metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gmU g) ≤
          fr * (M5 R * (pl2 * u)) := by
        have h := hmpd
        rw [hmT, hmU] at h
        exact mul_le_mul_of_nonneg_left h hfr
      _ = Vd R * (pl2 * u) := by
        simp only [Vd]
        ring
  have hInT2 : covariantJetNormSq (I := I) (M := M) g 2 InT ≤ Sin R * (pl2 * pl2) := by
    rw [hInT]
    refine (happIn VmT IpT).trans ?_
    calc
      Cin * covariantJetNormSq (I := I) (M := M) g 2 VmT *
          covariantJetNormSq (I := I) (M := M) g 2 IpT ≤
          Cin * (Vb R * pl2) * (Ib R * pl2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hVmT2 hCin) hIpT2
          (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g IpT)
          (mul_nonneg hCin (mul_nonneg (hVb R hR) hpl20))
      _ = Sin R * (pl2 * pl2) := by
        simp only [Sin]
        ring
  have hInd2 : covariantJetNormSq (I := I) (M := M) g 2 (InT - InU) ≤
      2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u)) := by
    rw [hInT, hInU]
    refine (covariantJetNormSq_operatorFieldComposition_sub_le
      (I := I) (M := M) g 2 2 1 4
      Cin (Vd R * (pl2 * u)) (Ib R * pl2) (Vb R * pl2)
        (Im R * (pl2 * u)) hCin
      VmT VmU IpT IpU happIn hVmd2 hIpT2 hVmU2 hIpd2).trans ?_
    simp only [Kv, Ki]
    ring_nf
    exact le_rfl
  have hLvd2 : covariantJetNormSq (I := I) (M := M) g 2 (LvT - LvU) ≤ Ct2 ^ 2 * u := by
    rw [hLvT, hLvU, reindexedCometricDoubleTrace_eq_pureTrace, reindexedCometricDoubleTrace_eq_pureTrace]
    exact htp2'
  have hLvU2 : covariantJetNormSq (I := I) (M := M) g 2 LvU ≤ Bt2 ^ 2 := by
    rw [hLvU, reindexedCometricDoubleTrace_eq_pureTrace]
    exact htb2'.2
  have hFormT : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT := by
    rw [hLvT, hInT, hVmT, hIpT, hWTdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  have hFormU : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU =
      (2 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU := by
    rw [hLvU, hInU, hVmU, hIpU, hWUdef, lieCorrectionZeroVectorBundle_eq_expansion, lieCorrectionZeroVectorBundleExpansion]
  have hAppD : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT -
        ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU) ≤
      2 * (Cout * (Ct2 ^ 2 * u) * (Sin R * (pl2 * pl2)) +
        Cout * (Bt2 ^ 2) *
          (2 * (Kv R * ((pl2 * pl2) * u) +
            Ki R * ((pl2 * pl2) * u)))) :=
    covariantJetNormSq_operatorFieldComposition_sub_le
      (I := I) (M := M) g 2 2 4 2
      Cout (Ct2 ^ 2 * u) (Sin R * (pl2 * pl2)) (Bt2 ^ 2)
        (2 * (Kv R * ((pl2 * pl2) * u) + Ki R * ((pl2 * pl2) * u))) hCout
      LvT LvU InT InU happOut hLvd2 hInT2 hLvU2 hInd2
  have hdel1 : lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT -
      lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU =
      (2 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvT InT -
        ccOperatorFieldComp (I := I) (M := M) g 2 4 2 LvU InU) := by
    rw [hFormT, hFormU, smul_sub]
  have hwhole : covariantJetNormSq (I := I) (M := M) g 2
      (lieCorrectionZeroVectorBundle (I := I) (M := M) g gmT - lieCorrectionZeroVectorBundle (I := I) (M := M) g gmU) ≤
      Bh R * ((pl2 * pl2) * u) := by
    rw [hdel1, covariantJetNormSq_smul]
    refine (mul_le_mul_of_nonneg_left hAppD (sq_nonneg (2 : ℝ))).trans ?_
    simp only [Bh, K1, K2]
    ring_nf
    exact le_rfl
  refine hwhole.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact quartic_product_sum_le_interpolation_square (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
end

section

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis (quartic_product_sum_le_interpolation_square
  one_le_one_add_pow_four pow_four_le_one_add_pow_four sq_le_one_add_pow_four
  three_term_sq_le_weighted_product)
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance instCompleteSpaceE_covariantTerm : CompleteSpace E :=
  FiniteDimensional.complete ℝ E

private local instance (x : M) :
    ContinuousAdd (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ContinuousLinearMap.topologicalAddGroup.toContinuousAdd

private lemma half_sq_le_one {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    (s / 2) ^ 2 ≤ 1 := by
  nlinarith

private lemma unit_interval_sq_le_one_covariantTerm {s : ℝ}
    (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    s ^ 2 ≤ 1 := by
  nlinarith

private lemma one_le_one_add_sq_covariantTerm {A : ℝ} (hA : 0 ≤ A) :
    1 ≤ (1 + A) ^ 2 := by
  nlinarith

private lemma sq_le_one_add_sq_covariantTerm {A : ℝ} (hA : 0 ≤ A) :
    A ^ 2 ≤ (1 + A) ^ 2 := by
  nlinarith

theorem exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) ≤
        (B R * A) ^ 2 := by
  obtain ⟨B, hB, hbdd⟩ := lie_omega_sobolev_two_bound (I := I) (M := M) hDim g
  exact ⟨B, hB, fun gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 =>
    hbdd gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3⟩

theorem exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) ≤
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ := lieOmega_pair_h2 (I := I) (M := M) hDim g
  exact ⟨B0, B1, hB0, hB1,
    fun gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU hδZ
      R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3 =>
      hpair gT gU T U hT hU hTtie hUtie hδ_le hδ0 hδT hδU hδZ
        R A D2 D3 hR hA hD2 hD3 hT2 hU2 hT3 hTU2 hTU3⟩


theorem exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B R) ∧
      ∀ (gT : SmoothRiemannianMetric I M)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
        ((Module.finrank ℝ E : ℝ) * B R * A) ^ 2 := by
  obtain ⟨Bs, hBs, hwSelf⟩ := exists_metricLoweredConnectionDifference_covariantJetNormSq_bound (I := I) (M := M) hDim g
  refine ⟨Bs, hBs, ?_⟩
  intro gT T hT hTtie δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  have hbase : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) =
      connectionDifferenceSection (I := I) gT g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gT).symm
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
        (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Bs R * A) ^ 2 := by
    rw [hbase, connSec_self_h2 (I := I) (M := M) g gT]
    exact hwSelf gT T hT hTtie hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT)) :=
      covariantJetNormSq_bilinearSlotInsertionCoefficient_two_le (I := I) (M := M) g (connectionDifferenceEndomorphism (I := I) (M := M) g gT)
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 * (Bs R * A) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * Bs R * A) ^ 2 := by ring

theorem exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (gT gU : SmoothRiemannianMetric I M)
        (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        (_hTtie : ∀ (x : M) (u v : TangentSpace I x),
          gT.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g T x u v)
        (_hUtie : ∀ (x : M) (u v : TangentSpace I x),
          gU.inner x u v =
            g.inner x u v + ccTensorBilinSymm (I := I) g U x u v)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (_hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (_hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (R A D2 D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D2 → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
      covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) ≤
        ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
          (Module.finrank ℝ E : ℝ) * B1 R * D2 +
          (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, hpair⟩ :=
    connSec_sub_tame (I := I) (M := M) hDim g
      (δ₀ := (1 : ℝ) / 3) (by norm_num) (by norm_num)
  refine ⟨B0, B1, hB0, hB1, ?_⟩
  intro gT gU T U hT hU hTtie hUtie δ hδ_le hδ0 hδT hδU
    R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  have hbT : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) =
      connectionDifferenceSection (I := I) gT g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gT).symm
  have hbU : bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
      (connectionDifferenceEndomorphism (I := I) (M := M) g gU) =
      connectionDifferenceSection (I := I) gU g :=
    (connectionDifferenceSection_eq_bilinearSlotInsertionCoefficient_zero
      (I := I) (M := M) g gU).symm
  have h0 : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) ≤
      (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 := by
    rw [hbT, hbU]
    exact hpair gT gU T U hT hU hTtie hUtie
      hδ_le hδ0 hδT hδ_le hδ0 hδU
      R A D2 D3 hR hA hD2 hD3 hU2 hT3 hTU2 hTU3
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) =
      covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
            connectionDifferenceEndomorphism (I := I) (M := M) g gU)) := by
      rw [DifferentialGeometry.Analysis.Sobolev.armSlotEndoCc_sub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
            (connectionDifferenceEndomorphism (I := I) (M := M) g gT -
              connectionDifferenceEndomorphism (I := I) (M := M) g gU)) :=
      covariantJetNormSq_bilinearSlotInsertionCoefficient_two_le (I := I) (M := M) g _
    _ = (Module.finrank ℝ E : ℝ) ^ 2 *
        covariantJetNormSq (I := I) (M := M) g 2
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 0
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) := by
      rw [DifferentialGeometry.Analysis.Sobolev.armSlotEndoCc_sub]
    _ ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
        (B0 R * D3 + B1 R * D2 + B1 R * A * D2) ^ 2 :=
      mul_le_mul_of_nonneg_left h0 (pow_nonneg (Nat.cast_nonneg _) 2)
    _ = ((Module.finrank ℝ E : ℝ) * B0 R * D3 +
        (Module.finrank ℝ E : ℝ) * B1 R * D2 +
        (Module.finrank ℝ E : ℝ) * B1 R * A * D2) ^ 2 := by ring

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem riemannCurvatureCoefficientField_sub
    (g : SmoothRiemannianMetric I M) (T U : SmoothCcTensor g 0 2) :
    riemannCurvatureCoefficientField (I := I) (M := M) g T - riemannCurvatureCoefficientField (I := I) (M := M) g U =
      riemannCurvatureCoefficientField (I := I) (M := M) g (T - U) := by
  simp only [riemannCurvatureCoefficientField, riemannCurvatureCoefficientField]
  rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_right]
  module

theorem exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2),
        covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
          C * covariantJetNormSq (I := I) (M := M) g 2 T := by
  obtain ⟨C₀, hC₀, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 2 4
  refine ⟨2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionA (I := I) (M := M) g) +
      C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionB (I := I) (M := M) g)), ?_, ?_⟩
  · have h1 : 0 ≤ C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionA (I := I) (M := M) g) :=
      mul_nonneg hC₀ (covariantJetNormSq_nonneg (I := I) (M := M) g _)
    have h2 : 0 ≤ C₀ * covariantJetNormSq (I := I) (M := M) g 2
        (riemannLoweredContractionB (I := I) (M := M) g) :=
      mul_nonneg hC₀ (covariantJetNormSq_nonneg (I := I) (M := M) g _)
    linarith
  intro T
  rw [riemannCurvatureCoefficientField]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) T +
          ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) T) ≤
      2 * (covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionA (I := I) (M := M) g) T) +
        covariantJetNormSq (I := I) (M := M) g 2
          (ccOperatorFieldComp (I := I) (M := M) g 0 2 4
            (riemannLoweredContractionB (I := I) (M := M) g) T)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ ≤ 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
            (riemannLoweredContractionA (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2 T +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2
            (riemannLoweredContractionB (I := I) (M := M) g) *
          covariantJetNormSq (I := I) (M := M) g 2 T) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (happ _ T) (happ _ T)) (by norm_num)
    _ = 2 * (C₀ * covariantJetNormSq (I := I) (M := M) g 2
          (riemannLoweredContractionA (I := I) (M := M) g) +
        C₀ * covariantJetNormSq (I := I) (M := M) g 2
          (riemannLoweredContractionB (I := I) (M := M) g)) *
        covariantJetNormSq (I := I) (M := M) g 2 T := by ring

omit [NeZero (Module.finrank ℝ E)] in
private theorem covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le
    (g : SmoothRiemannianMetric I M)
    (X Y : SmoothCcTensor g 0 4) {K : ℝ}
    (hX : covariantJetNormSq (I := I) (M := M) g 2 X ≤ K)
    (hY : covariantJetNormSq (I := I) (M := M) g 2 Y ≤ K) :
    covariantJetNormSq (I := I) (M := M) g 2
        (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1) X + X +
          domDomCongrSection (I := I) g lrPermA Y +
          domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2) Y +
          domDomCongrSection (I := I) g lrPermB Y +
          domDomCongrSection (I := I) g lrPermC Y) ≤ 94 * K :=
  covariantJetNormSq_sum_six_le (I := I) (M := M) g 2 _ _ _ _ _ _
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hX) hX
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hY) (by rw [covariantJetNormSq_domDomCongrSection]; exact hY)
    (by rw [covariantJetNormSq_domDomCongrSection]; exact hY) (by rw [covariantJetNormSq_domDomCongrSection]; exact hY)

theorem exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gm : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
                (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
              covariantJetNormSq (I := I) (M := M) g 2
                (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  refine ⟨94 * Ca, by positivity, ?_⟩
  intro gm
  have hQB : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gm) ≤
      Ca * (covariantJetNormSq (I := I) (M := M) g 2
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
    rw [connectionDifferenceQuadraticPairedTensor]
    refine (happ _ _).trans (le_of_eq ?_)
    ring
  have hQA : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gm) ≤
      Ca * (covariantJetNormSq (I := I) (M := M) g 2
            (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) *
          covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm)) := by
    rw [connectionDifferenceQuadraticComposedTensor]
    refine (happ _ _).trans (le_of_eq ?_)
    rw [covariantJetNormSq_domDomCongrSection]
    ring
  rw [connectionDifferenceQuadraticCurvatureTerm]
  refine (covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le (I := I) (M := M) g _ _ hQB hQA).trans (le_of_eq ?_)
  ring

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceQuadraticPairedTensor_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT) := by
  simp only [connectionDifferenceQuadraticPairedTensor,
    connectionDifferenceEndomorphism, connectionDifferenceMetricLoweredTensor]
  rw [operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceQuadraticComposedTensor_sub
    (g gT gU : SmoothRiemannianMetric I M) :
    connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU =
      ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
              connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU)) +
        ccOperatorFieldComp (I := I) (M := M) g 0 3 4
          (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
            bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
              (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
          (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
            (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  simp only [connectionDifferenceQuadraticComposedTensor,
    connectionDifferenceEndomorphism, connectionDifferenceMetricLoweredTensor]
  rw [domDomCongrSection_sub, operatorFieldComposition_sub_right, operatorFieldComposition_sub_left]
  module

theorem exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gT gU : SmoothRiemannianMetric I M),
        covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
              connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU) ≤
          C * (covariantJetNormSq (I := I) (M := M) g 2
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                    (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                    connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
              covariantJetNormSq (I := I) (M := M) g 2
                  (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                    bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                      (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
                covariantJetNormSq (I := I) (M := M) g 2
                  (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 0 3 4
  refine ⟨188 * Ca, by positivity, ?_⟩
  intro gT gU
  have hQBd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) ≤
      2 * Ca * (covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
    rw [connectionDifferenceQuadraticPairedTensor_sub]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
        connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU)
    have e2 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)
    linarith
  have hQAd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) ≤
      2 * Ca * (covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
                connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU) +
          covariantJetNormSq (I := I) (M := M) g 2
              (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
                bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
                  (connectionDifferenceEndomorphism (I := I) (M := M) g gU)) *
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT)) := by
    rw [connectionDifferenceQuadraticComposedTensor_sub]
    refine (covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _).trans ?_
    have e1 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT -
          connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gU))
    have e2 := happ
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gU))
      (domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 3) 1)
        (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gT))
    rw [covariantJetNormSq_domDomCongrSection] at e1
    rw [covariantJetNormSq_domDomCongrSection] at e2
    linarith
  have hsplit : connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gT -
      connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gU =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 1)
          (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) +
        (connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticPairedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermA
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 4) 2)
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermB
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) +
        domDomCongrSection (I := I) g lrPermC
          (connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gT - connectionDifferenceQuadraticComposedTensor (I := I) (M := M) g gU) := by
    simp only [connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticCurvatureTerm, connectionDifferenceQuadraticPairedTensor,
      connectionDifferenceQuadraticPairedTensor, connectionDifferenceQuadraticComposedTensor, connectionDifferenceQuadraticComposedTensor, domDomCongrSection_sub]
    abel_nf
  rw [hsplit]
  refine (covariantJetNormSq_connectionDifferenceQuadraticCurvatureTerm_decomposition_le (I := I) (M := M) g _ _ hQBd hQAd).trans (le_of_eq ?_)
  ring


theorem exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Cc, hCc, hcurv⟩ := exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquad⟩ := exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  let D : ℝ → ℝ := fun R =>
    2 * Cc + 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2)
  refine ⟨D, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ 2 * Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2) :=
      mul_nonneg (by linarith) (by positivity)
    simp only [D]
    linarith
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gm : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgm
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := unit_interval_sq_le_one hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgm, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hCF : covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * A ^ 2 :=
    (hcurv T).trans (mul_le_mul_of_nonneg_left
      ((covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) T).trans hT3)
      hCc)
  have harm : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gm)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhat : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gm) ≤ (Bt R * A) ^ 2 :=
    hhatb gm P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hQF : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) :=
    (hquad gm).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul harm hhat (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (sq_nonneg _)) hCq)
  have hdecomp : deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s =
      (-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
        (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm := by
    rw [hgm, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := half_sq_le_one hs.1 hs.2
  have hu0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T) := covariantJetNormSq_nonneg (I := I) (M := M) g _
  have hfin : 2 * (Cc * A ^ 2 +
      Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) ≤ D R * (1 + A) ^ 4 := by
    have e1 : Cc * A ^ 2 ≤ Cc * (1 + A) ^ 4 :=
      mul_le_mul_of_nonneg_left (sq_le_one_add_pow_four hA) hCc
    have e2 : Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) ≤
        Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4) := by
      refine mul_le_mul_of_nonneg_left ?_ hCq
      have hre : (fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2 =
          (fr * Bs R) ^ 2 * (Bt R) ^ 2 * A ^ 4 := by ring
      rw [hre]
      exact mul_le_mul_of_nonneg_left (pow_four_le_one_add_pow_four hA)
        (by positivity)
    have heq : D R * (1 + A) ^ 4 =
        2 * (Cc * (1 + A) ^ 4) +
          2 * (Cq * ((fr * Bs R) ^ 2 * (Bt R) ^ 2 * (1 + A) ^ 4)) := by
      simp only [D]
      ring
    rw [heq]
    linarith
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T +
          (-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • riemannCurvatureCoefficientField (I := I) (M := M) g T) +
        covariantJetNormSq (I := I) (M := M) g 2
          ((-1 : ℝ) • connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) +
        (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) := by
      rw [covariantJetNormSq_smul, covariantJetNormSq_smul]
    _ ≤ 2 * (Cc * A ^ 2 +
        Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤ Cc * A ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T) ≤
            1 * covariantJetNormSq (I := I) (M := M) g 2
              (riemannCurvatureCoefficientField (I := I) (M := M) g T) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hu0
        rw [one_mul] at hle
        exact hle.trans hCF
      have h2 : (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) ≤
          Cq * ((fr * Bs R * A) ^ 2 * (Bt R * A) ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm)) =
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gm) := by ring
        rw [hvv]
        exact hQF
      linarith
    _ ≤ D R * (1 + A) ^ 4 := hfin

theorem exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cc, hCc, hcurv⟩ := exists_riemannCurvatureCoefficientField_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cq, hCq, hquadp⟩ := exists_connectionDifferenceQuadraticCurvatureTerm_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Bs, hBs, harmb⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Bt, hBt, hhatb⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨A0, A1, hA0, hA1, harmp⟩ := exists_bilinearSlotInsertionCoefficient_connectionDifferenceEndomorphism_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨W0, W1, hW0, hW1, hhatp⟩ := exists_connectionDifferenceMetricLoweredTensor_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  let Mh : ℝ → ℝ := fun R => 2 * (W0 R + W1 R) ^ 2 + 2 * (W1 R) ^ 2
  let Ma : ℝ → ℝ := fun R =>
    2 * (fr * A0 R + fr * A1 R) ^ 2 + 2 * (fr * A1 R) ^ 2
  let Kq : ℝ → ℝ := fun R =>
    (fr * Bs R) ^ 2 * Mh R + Ma R * (Bt R) ^ 2
  let C : ℝ → ℝ := fun R => 2 * Cc + 2 * (Cq * Kq R)
  have hMh : ∀ R : ℝ, 0 ≤ R → 0 ≤ Mh R := fun R hR => by
    simp only [Mh]
    positivity
  have hMa : ∀ R : ℝ, 0 ≤ R → 0 ≤ Ma R := fun R hR => by
    simp only [Ma]
    positivity
  have hKq : ∀ R : ℝ, 0 ≤ R → 0 ≤ Kq R := fun R hR => by
    have h1 : (0 : ℝ) ≤ (fr * Bs R) ^ 2 * Mh R :=
      mul_nonneg (sq_nonneg _) (hMh R hR)
    have h2 : (0 : ℝ) ≤ Ma R * (Bt R) ^ 2 :=
      mul_nonneg (hMa R hR) (sq_nonneg _)
    simp only [Kq]
    linarith
  refine ⟨C, ?_, ?_⟩
  · intro R hR
    have h1 : (0 : ℝ) ≤ Cq * Kq R := mul_nonneg hCq (hKq R hR)
    simp only [C]
    linarith
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hs2 : s ^ 2 ≤ (1 : ℝ) := unit_interval_sq_le_one hs.1 hs.2
  have hPsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u := by
    intro x u v
    simp only [hcP, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hU x u v
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hδP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g T 0 hδT hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcP, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hδQ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g Q) δ := by
    intro x u v
    have hraw := convexPerturbation_gFibreOpBound_abs
      (I := I) g U 0 hδU hδZ s x u v
    have heq : |1 - s| * δ + |s| * δ = δ := by
      rw [abs_of_nonneg (by linarith [hs.2] : (0 : ℝ) ≤ 1 - s),
        abs_of_nonneg hs.1]
      ring
    simpa only [hcQ, convexPerturbation, smul_zero, zero_add, heq] using hraw
  have hP2 : covariantJetNormSq (I := I) (M := M) g 2 P ≤ R ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g T) hs2).trans hT2
  have hQ2 : covariantJetNormSq (I := I) (M := M) g 2 Q ≤ R ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g U) hs2).trans hU2
  have hP3 : covariantJetNormSq (I := I) (M := M) g 3 P ≤ A ^ 2 := by
    rw [hcP, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g T) hs2).trans hT3
  have hQ3 : covariantJetNormSq (I := I) (M := M) g 3 Q ≤ A ^ 2 := by
    rw [hcQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g U) hs2).trans hU3
  have hPQ3 : covariantJetNormSq (I := I) (M := M) g 3 (P - Q) ≤ D3 ^ 2 := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, covariantJetNormSq_smul]
    exact (mul_le_of_le_one_left
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 3) g (T - U)) hs2).trans hTU3
  have hPQ2 : covariantJetNormSq (I := I) (M := M) g 2 (P - Q) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (P - Q)).trans hPQ3
  have hTU2 : covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D3 ^ 2 :=
    (covariantJetNormSq_mono (I := I) (M := M) g (by norm_num : (2 : ℕ) ≤ 3) (T - U)).trans hTU3
  set pl2 : ℝ := (1 + A) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    exact one_le_one_add_sq hA
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hplA2 : A ^ 2 ≤ pl2 := by
    rw [hpl2]
    exact sq_le_one_add_sq hA
  have hd0 : (0 : ℝ) ≤ D3 ^ 2 := sq_nonneg _
  have hquart : pl2 * (pl2 * D3 ^ 2) = (1 + A) ^ 4 * D3 ^ 2 := by
    rw [hpl2]
    ring
  have hCFd : covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T -
        riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
    rw [riemannCurvatureCoefficientField_sub]
    exact (hcurv (T - U)).trans (mul_le_mul_of_nonneg_left hTU2 hCc)
  have harmU : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
        (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤ (fr * Bs R * A) ^ 2 :=
    harmb gmU Q hQsymm hQtie hδ_le hδ0 hδQ hδZ R A hR hA hQ2 hQ3
  have hhatT : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤ (Bt R * A) ^ 2 :=
    hhatb gmT P hPsymm hPtie hδ_le hδ0 hδP hδZ R A hR hA hP2 hP3
  have hhatD : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
        connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤ Mh R * (pl2 * D3 ^ 2) := by
    refine (hhatp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ hδZ R A D3 D3 hR hA hD3 hD3
      hP2 hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact three_term_sq_le_weighted_product hpl21 hplA2 hd0 le_rfl
  have harmD : covariantJetNormSq (I := I) (M := M) g 2
      (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
        bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) ≤
      Ma R * (pl2 * D3 ^ 2) := by
    refine (harmp gmT gmU P Q hPsymm hQsymm hPtie hQtie
      hδ_le hδ0 hδP hδQ R A D3 D3 hR hA hD3 hD3
      hQ2 hP3 hPQ2 hPQ3).trans ?_
    exact three_term_sq_le_weighted_product hpl21 hplA2 hd0 le_rfl
  have hQFd : covariantJetNormSq (I := I) (M := M) g 2
      (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
        connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) ≤
      Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
    refine (hquadp gmT gmU).trans ?_
    have e1 : covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
          (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT -
            connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmU) ≤
        (fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmU hhatD
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _) (sq_nonneg _)
      refine hstep.trans ?_
      have hre : (fr * Bs R * A) ^ 2 * (Mh R * (pl2 * D3 ^ 2)) =
          (fr * Bs R) ^ 2 * Mh R * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (sq_nonneg _) (hMh R hR))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have e2 : covariantJetNormSq (I := I) (M := M) g 2
        (bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmT) -
          bilinearSlotInsertionCoefficient (I := I) (M := M) g 2
            (connectionDifferenceEndomorphism (I := I) (M := M) g gmU)) *
        covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceMetricLoweredTensor (I := I) (M := M) g gmT) ≤
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2) := by
      have hstep := mul_le_mul harmD hhatT
        (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
        (mul_nonneg (hMa R hR) (mul_nonneg hpl20 hd0))
      refine hstep.trans ?_
      have hre : Ma R * (pl2 * D3 ^ 2) * (Bt R * A) ^ 2 =
          Ma R * (Bt R) ^ 2 * (A ^ 2 * (pl2 * D3 ^ 2)) := by ring
      rw [hre]
      refine mul_le_mul_of_nonneg_left ?_
        (mul_nonneg (hMa R hR) (sq_nonneg _))
      rw [← hquart]
      exact mul_le_mul_of_nonneg_right hplA2
        (mul_nonneg hpl20 hd0)
    have hsum : Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
        Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) =
        Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
      simp only [Kq]
      ring
    calc
      Cq * (_ + _) ≤ Cq * ((fr * Bs R) ^ 2 * Mh R * ((1 + A) ^ 4 * D3 ^ 2) +
          Ma R * (Bt R) ^ 2 * ((1 + A) ^ 4 * D3 ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add e1 e2) hCq
      _ = Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := hsum
  have hdecomp : deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
      deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s =
      (-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
          riemannCurvatureCoefficientField (I := I) (M := M) g U) +
        (-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
          connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) := by
    rw [hgmT, hgmU, deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g T hδT hδZ s,
      deTurckLieCovariantDerivativeRemainderTensor_eq (I := I) (M := M) g U hδU hδZ s]
    module
  have hs22 : (s / 2) ^ 2 ≤ 1 := half_sq_le_one hs.1 hs.2
  have hcf0 : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2
      (riemannCurvatureCoefficientField (I := I) (M := M) g T -
        riemannCurvatureCoefficientField (I := I) (M := M) g U) := covariantJetNormSq_nonneg (I := I) (M := M) g _
  have hDenv : D3 ^ 2 ≤ (1 + A) ^ 4 * D3 ^ 2 := by
    calc D3 ^ 2 = 1 * D3 ^ 2 := (one_mul _).symm
      _ ≤ (1 + A) ^ 4 * D3 ^ 2 :=
        mul_le_mul_of_nonneg_right (one_le_one_add_pow_four hA) hd0
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s) =
      covariantJetNormSq (I := I) (M := M) g 2
        ((-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) +
          (-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) := by
      rw [hdecomp]
    _ ≤ 2 * (covariantJetNormSq (I := I) (M := M) g 2
          ((-(s / 2) : ℝ) • (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U)) +
        covariantJetNormSq (I := I) (M := M) g 2
          ((-1 : ℝ) • (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU))) :=
      covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
    _ = 2 * ((-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) +
        (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) := by
      rw [covariantJetNormSq_smul, covariantJetNormSq_smul]
    _ ≤ 2 * (Cc * D3 ^ 2 + Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
      have h1 : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (riemannCurvatureCoefficientField (I := I) (M := M) g T -
            riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤ Cc * D3 ^ 2 := by
        have hle : (-(s / 2)) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (riemannCurvatureCoefficientField (I := I) (M := M) g T -
              riemannCurvatureCoefficientField (I := I) (M := M) g U) ≤
            1 * covariantJetNormSq (I := I) (M := M) g 2
              (riemannCurvatureCoefficientField (I := I) (M := M) g T -
                riemannCurvatureCoefficientField (I := I) (M := M) g U) := by
          have hss : (-(s / 2)) ^ 2 = (s / 2) ^ 2 := by ring
          rw [hss]
          exact mul_le_mul_of_nonneg_right hs22 hcf0
        rw [one_mul] at hle
        exact hle.trans hCFd
      have h2 : (-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
          (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
            connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) ≤
          Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2) := by
        have hvv : ((-1 : ℝ) ^ 2 * covariantJetNormSq (I := I) (M := M) g 2
            (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
              connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU)) =
            covariantJetNormSq (I := I) (M := M) g 2
              (connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmT -
                connectionDifferenceQuadraticCurvatureTerm (I := I) (M := M) g gmU) := by ring
        rw [hvv]
        exact hQFd
      linarith
    _ ≤ C R * ((1 + A) ^ 4 * D3 ^ 2) := by
      have e1 : Cc * D3 ^ 2 ≤ Cc * ((1 + A) ^ 4 * D3 ^ 2) :=
        mul_le_mul_of_nonneg_left hDenv hCc
      have heq : C R * ((1 + A) ^ 4 * D3 ^ 2) =
          2 * (Cc * ((1 + A) ^ 4 * D3 ^ 2)) +
            2 * (Cq * Kq R * ((1 + A) ^ 4 * D3 ^ 2)) := by
        simp only [C]
        ring
      rw [heq]
      linarith

noncomputable def deTurckLieCovariantDerivativeRemainderPairTrace
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {δ : ℝ}
    (hδT : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 2 6 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
    (slotExtendIter (I := I) (M := M) g 0 4 2
      (deTurckLieCovariantDerivativeRemainderTensor
        (I := I) (M := M) g T hδT hδZ s))

theorem exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ D : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ D R) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderPairTrace
            (I := I) (M := M) g T hδT hδZ s) ≤
        D R * (1 + A) ^ 4 := by
  obtain ⟨Dr, hDr, hr4⟩ := exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Dr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hDr R hR), ?_⟩
  intro T hT δ hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 s hs
  unfold deTurckLieCovariantDerivativeRemainderPairTrace
  have hIter : slotExtendIter (I := I) (M := M) g 0 4 2
      (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s) =
      slotExtend (I := I) (M := M) g 1 5
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) := rfl
  have hbase := hr4 T hT hδ_le hδ0 hδT hδZ R A hR hA hT2 hT3 hs
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) =
      covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
      rw [hIter, covariantJetNormSq_rsDomDomCongrSection]
    _ ≤ fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) :=
      mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Dr R * (1 + A) ^ 4)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Dr R * (1 + A) ^ 4 := by ring

theorem exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ C R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A D3 : ℝ), 0 ≤ R → 0 ≤ A → 0 ≤ D3 →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          (deTurckLieCovariantDerivativeRemainderPairTrace
              (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderPairTrace
              (I := I) (M := M) g U hδU hδZ s) ≤
        C R * ((1 + A) ^ 4 * D3 ^ 2) := by
  obtain ⟨Cr, hCr, hr4p⟩ := exists_deTurckLieCovariantDerivativeRemainderTensor_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  set fr : ℝ := (Module.finrank ℝ E : ℝ) with hfrdef
  have hfr : 0 ≤ fr := Nat.cast_nonneg _
  refine ⟨fun R => fr ^ 2 * Cr R, fun R hR => mul_nonneg (sq_nonneg _)
    (hCr R hR), ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 s hs
  unfold deTurckLieCovariantDerivativeRemainderPairTrace
  have hXsub :
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) =
      rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [← rsDomDomCongrSection_sub, slotExtend_sub, slotExtend_sub]
    rfl
  have hbase := hr4p T U hT hU hδ_le hδ0 hδT hδU hδZ R A D3 hR hA hD3
    hT2 hU2 hT3 hU3 hTU3 hs
  rw [hXsub, covariantJetNormSq_rsDomDomCongrSection]
  calc
    covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 1 5
          (slotExtend (I := I) (M := M) g 0 4
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
              deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      fr * covariantJetNormSq (I := I) (M := M) g 2
        (slotExtend (I := I) (M := M) g 0 4
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
            deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
      covariantJetNormSq_slotExtend_le (I := I) (M := M) g 1 5 _
    _ ≤ fr * (fr * covariantJetNormSq (I := I) (M := M) g 2
        (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s -
          deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)) :=
      mul_le_mul_of_nonneg_left (covariantJetNormSq_slotExtend_le (I := I) (M := M) g 0 4 _) hfr
    _ ≤ fr * (fr * (Cr R * ((1 + A) ^ 4 * D3 ^ 2))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hbase hfr) hfr
    _ = fr ^ 2 * Cr R * ((1 + A) ^ 4 * D3 ^ 2) := by ring

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) :
    deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
        lieDecompositionQ lieDecompositionEps s =
      deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
        g T hδ hδZ
          ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
            Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
              Equiv.swap (0 : Fin 4) 1,
            Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
          ![(-1 : ℝ), -1, 1] s := rfl

theorem exists_deTurckLieCovariantDerivativeRemainder_covariantJetNormSq_difference_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ ρ : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (T U : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (_hU : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g U x u v =
            ccTensorBilin (I := I) g U x v u)
        {δ : ℝ} (_hδ_le : δ ≤ 1 / 3) (_hδ0 : 0 ≤ δ)
        (hδT : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδU : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g U) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (R A A4 D2 D3 D4 N : ℝ),
        0 ≤ R → 0 ≤ A → 0 ≤ A4 → 0 ≤ D2 → 0 ≤ D3 → 0 ≤ D4 → 0 ≤ N →
        covariantJetNormSq (I := I) (M := M) g 2 T ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 U ≤ R ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 T ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 U ≤ A ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 T ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 U ≤ A4 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 2 (T - U) ≤ D2 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 3 (T - U) ≤ D3 ^ 2 →
        covariantJetNormSq (I := I) (M := M) g 4 (T - U) ≤ D4 ^ 2 →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U‖ ≤ ρ →
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ ≤ N →
        ∀ {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
      covariantJetNormSq (I := I) (M := M) g 2
          ((deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g T 0 hδT hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδT hδZ
              lieDecompositionQ lieDecompositionEps s) -
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g
              (metricPerturbationPath (I := I) g U 0 hδU hδZ s) g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g U hδU hδZ
              lieDecompositionQ lieDecompositionEps s)) ≤
        (B0 R * (1 + A) * (D4 + D3 + D2 + N) +
          B1 R * A4 * (D3 + N)) ^ 2 := by
  obtain ⟨Ca, hCa, happ⟩ := exists_covariantJetNormSq_two_operatorFieldComposition_le (I := I) (M := M) hDim g 2 6 2
  obtain ⟨ρp, Cp, hρp, hCp, hlcvp⟩ :=
    RicciDeTurckLowOrder.pairTrace_pair_h2 (I := I) (M := M) hDim g
  obtain ⟨ρb, Bp, hρb, hBp, hlcvb⟩ :=
    RicciDeTurckLowOrder.pair_trace_sobolev_two_bound (I := I) (M := M) hDim g
  obtain ⟨Dx, hDx, hcovb⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_bound (I := I) (M := M) hDim g
  obtain ⟨Cx, hCx, hcovp⟩ := exists_deTurckLieCovariantDerivativeRemainderPairTrace_covariantJetNormSq_difference_bound (I := I) (M := M) hDim g
  obtain ⟨Cip, hCip, hinterp⟩ := covariantJetNormSq_three_interpolation (I := I) (M := M) g 2
  let Bh : ℝ → ℝ := fun R => 2 * (Ca * Cp ^ 2 * Dx R + Ca * Bp ^ 2 * Cx R)
  let B0 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R)
  let B1 : ℝ → ℝ := fun R => Real.sqrt (8 * Bh R) * Cip * R
  have hBhnn : ∀ R : ℝ, 0 ≤ R → 0 ≤ Bh R := by
    intro R hR
    have h1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
    have h2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
      mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
    simp only [Bh]
    linarith
  refine ⟨min ρp ρb, B0, B1, lt_min hρp hρb,
    fun R hR => by
      simp only [B0]
      exact Real.sqrt_nonneg _,
    fun R hR => by
      simp only [B1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hCip) hR, ?_⟩
  intro T U hT hU δ hδ_le hδ0 hδT hδU hδZ
    R A A4 D2 D3 D4 N hR hA hA4 hD2 hD3 hD4 hN
    hT2 hU2 hT3 hU3 hT4 hU4 hTU2 hTU3 hTU4 hTn hUn hTUn s hs
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  set gmT : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g T 0 hδT hδZ s with hgmT
  set gmU : SmoothRiemannianMetric I M :=
    metricPerturbationPath (I := I) g U 0 hδU hδZ s with hgmU
  set P : SmoothCcTensor g 0 2 := s • T with hcP
  set Q : SmoothCcTensor g 0 2 := s • U with hcQ
  have hs_mem : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have hsabs : ‖s‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact hs.2
  have hPtie : ∀ (x : M) (u v : TangentSpace I x),
      gmT.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v := by
    intro x u v
    simpa only [hgmT, hcP, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g T 0 hδT hδZ hs_mem x u v
  have hQtie : ∀ (x : M) (u v : TangentSpace I x),
      gmU.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g Q x u v := by
    intro x u v
    simpa only [hgmU, hcQ, convexPerturbation, smul_zero, zero_add] using
      metricPerturbationPath_inner_of_mem (I := I) g U 0 hδU hδZ hs_mem x u v
  have hPn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) P‖ ≤ ρp := by
    rw [hcP, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTn.trans (min_le_left _ _))
  have hQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρp := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_left _ _))
  have hQnb : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) Q‖ ≤ ρb := by
    rw [hcQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hUn.trans (min_le_right _ _))
  have hPQn : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (P - Q)‖ ≤ N := by
    have hPQ : P - Q = s • (T - U) := by rw [hcP, hcQ, smul_sub]
    rw [hPQ, ccTensorToHs_smul, norm_smul]
    exact (mul_le_mul_of_nonneg_right hsabs (norm_nonneg _)).trans
      (by simpa using hTUn)
  set a : ℝ := Real.sqrt (Cip * (R * A4)) with hadef
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hasq : a ^ 2 = Cip * (R * A4) :=
    Real.sq_sqrt (mul_nonneg hCip (mul_nonneg hR hA4))
  have hT3i : covariantJetNormSq (I := I) (M := M) g 3 T ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp T R A4 hR hA4 hT2 hT4
  have hU3i : covariantJetNormSq (I := I) (M := M) g 3 U ≤ a ^ 2 := by
    rw [hasq]
    exact hinterp U R A4 hR hA4 hU2 hU4
  set pl2 : ℝ := (1 + a) ^ 2 with hpl2
  have hpl21 : (1 : ℝ) ≤ pl2 := by
    rw [hpl2]
    nlinarith [ha0]
  have hpl20 : 0 ≤ pl2 := le_trans zero_le_one hpl21
  have hpl4 : (0 : ℝ) ≤ pl2 * pl2 := mul_nonneg hpl20 hpl20
  set u : ℝ := D3 ^ 2 + N ^ 2 with hu
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hD3le : D3 ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg N]
  have hNu : N ^ 2 ≤ u := by
    rw [hu]
    linarith [sq_nonneg D3]
  have hUT :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gmT g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g T hδT hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) := by
    rw [hgmT]
    exact lieCov_residual (I := I) (M := M) g T hδ_lt hδT hδZ hT hs
  have hUU :
      deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gmU g -
        deTurckLieCovariantDerivativeDecompositionPairTraceFamily (I := I) (M := M)
          g U hδU hδZ
            ![Equiv.swap (0 : Fin 4) 1 * Equiv.swap (0 : Fin 4) 2,
              Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2 *
                Equiv.swap (0 : Fin 4) 1,
              Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3]
            ![(-1 : ℝ), -1, 1] s =
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) := by
    rw [hgmU]
    exact lieCov_residual (I := I) (M := M) g U hδ_lt hδU hδZ hU hs
  rw [deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g T hδT hδZ s,
    deTurckLieEdgePairingFamily_eq_deTurckLieCovariantDerivativeExpansionPairTraceFamily (I := I) (M := M) g U hδU hδZ s, hUT, hUU]
  have htel :
      (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) -
        (-1 : ℝ) • ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) =
      (-1 : ℝ) • (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) := by
    rw [operatorFieldComposition_sub_left, operatorFieldComposition_sub_right]
    module
  rw [htel, covariantJetNormSq_smul, neg_one_sq, one_mul]
  have hPairD : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
        cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ (Cp * N) ^ 2 := by
    refine (hlcvp P Q gmT gmU hPtie hQtie hPn hQn).trans ?_
    exact pow_le_pow_left₀ (mul_nonneg hCp (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hPQn hCp) 2
  have hPairU : covariantJetNormSq (I := I) (M := M) g 2
      (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU) ≤ Bp ^ 2 :=
    hlcvb Q gmU hQtie hQnb
  have hXT : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
        (slotExtendIter (I := I) (M := M) g 0 4 2
          (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) ≤
      Dx R * (pl2 * pl2) := by
    refine (hcovb T hT hδ_le hδ0 hδT hδZ R a hR ha0 hT2 hT3i hs).trans
      (le_of_eq ?_)
    rw [hpl2]
    ring
  have hXD : covariantJetNormSq (I := I) (M := M) g 2
      (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
        rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s))) ≤
      Cx R * ((pl2 * pl2) * D3 ^ 2) := by
    refine (hcovp T U hT hU hδ_le hδ0 hδT hδU hδZ R a D3 hR ha0 hD3
      hT2 hU2 hT3i hU3i hTU3 hs).trans (le_of_eq ?_)
    rw [hpl2]
    ring
  have hc1 : (0 : ℝ) ≤ Ca * Cp ^ 2 * Dx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hDx R hR)
  have hc2 : (0 : ℝ) ≤ Ca * Bp ^ 2 * Cx R :=
    mul_nonneg (mul_nonneg hCa (sq_nonneg _)) (hCx R hR)
  have hT1 : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
          cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
          (slotExtendIter (I := I) (M := M) g 0 4 2
            (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)))) ≤
      Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairD hCa) hXT
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * (Cp * N) ^ 2 * (Dx R * (pl2 * pl2)) =
        Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * N ^ 2) := by ring
      _ ≤ Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hNu hpl4) hc1
  have hT2b : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
        (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
        (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
          rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) := by
    refine (happ _ _).trans ?_
    have hstep := mul_le_mul (mul_le_mul_of_nonneg_left hPairU hCa) hXD
      (covariantJetNormSq_nonneg (I := I) (M := M) (m := 2) g _)
      (mul_nonneg hCa (sq_nonneg _))
    refine hstep.trans ?_
    calc Ca * Bp ^ 2 * (Cx R * ((pl2 * pl2) * D3 ^ 2)) =
        Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * D3 ^ 2) := by ring
      _ ≤ Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hD3le hpl4) hc2
  have hwhole : covariantJetNormSq (I := I) (M := M) g 2
      (ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmT -
            cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
            (slotExtendIter (I := I) (M := M) g 0 4 2
              (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s))) +
        ccOperatorFieldComp (I := I) (M := M) g 2 6 2
          (cometricDoublePairTraceCoefficient (I := I) (M := M) g gmU)
          (rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g T hδT hδZ s)) -
            rsDomDomCongrSection (I := I) (M := M) g 2 6 deTurckLieCovariantDerivativePairTracePermutation
              (slotExtendIter (I := I) (M := M) g 0 4 2
                (deTurckLieCovariantDerivativeRemainderTensor (I := I) (M := M) g U hδU hδZ s)))) ≤
      Bh R * ((pl2 * pl2) * u) := by
    calc
      covariantJetNormSq (I := I) (M := M) g 2 (_ + _) ≤
          2 * (covariantJetNormSq (I := I) (M := M) g 2 _ +
            covariantJetNormSq (I := I) (M := M) g 2 _) :=
        covariantJetNormSq_add_le (I := I) (M := M) g 2 _ _
      _ ≤ 2 * (Ca * Cp ^ 2 * Dx R * ((pl2 * pl2) * u) +
          Ca * Bp ^ 2 * Cx R * ((pl2 * pl2) * u)) := by
        linarith [hT1, hT2b]
      _ = Bh R * ((pl2 * pl2) * u) := by
        simp only [Bh]
        ring
  refine hwhole.trans ?_
  rw [hpl2, hu]
  simp only [B0, B1]
  exact quartic_product_sum_le_interpolation_square (hBhnn R hR) hCip hR hA hA4 hD2 hD3 hD4 hN hasq

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
end

section

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev
  (iteratedCovGrad iteratedCovGrad_succ iteratedCovGrad_zero metricConnectionDifferenceLoweredCoefficient
   rsDomDomCongrSection rsDomDomCongrSection_toSection)
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral
  (operatorFieldApply operatorFieldApplication_add_left operatorFieldApplication_add_right operatorFieldApplication_assoc operatorFieldApplication_smul_left operatorFieldApplication_smul_right operatorFieldApplication_sub_left operatorFieldApplication_toSection ccOperatorFieldComp
   operatorFieldComposition_toSection operatorFieldComposition_zero_eq_operatorFieldApply ccInputSlotSymm ccInputSlotSymm ccOperatorFieldComp
   ccSlotSwapField ccSlotSwapField_toSection deTurckLieTopOrderPairingFamily lieCorrectionZeroMixedConnection lieCorrectionZeroKappa lieCorrectionZeroRiemann lieCorrectionZeroVectorBundle
   lieCorrectionZeroField operatorFieldApply permCoeff ricciConnectionDifferenceQuadraticArm ricciConnectionDifferenceQuadraticKernel rsDomDomCongr slotExtend slotSwapFib slotSwapFib_apply
   slotExtendFib_apply slotExtend_toSection slotExtendIter symmS_eq_self_of_ccTensorBilin_symm
   tail_base_split toModel_rsDomDomCongr_apply)
open DifferentialGeometry.Geometry.Connection (slotInsertEndoCc slotInsertEndoCc_toSection)
open DifferentialGeometry.Geometry.Curvature (slotInsertEndoFib_apply_eval)
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

namespace LieCorrectionZeroCore

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne

private abbrev lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour :=
  DifferentialGeometry.Analysis.Spectral.LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour

end LieCorrectionZeroCore

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

namespace RicciDeTurckPairing

omit [SigmaCompactSpace M] in
omit [BoundarylessManifold I M] in
theorem ricciCovariantDerivativeConnectionDifference_self
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder (I := I) (M := M) g gm T) T =
      operatorFieldApply (I := I) (M := M) g 3 2
        (RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm T)
        (iteratedCovGrad (I := I) g 0 2 1 T) := by
  rw [iteratedCovGrad_succ, iteratedCovGrad_zero]
  exact RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder_apply (I := I) (M := M) g gm T T

omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem operatorFieldApplication_ipLowCc_eq_cometricRaiseSlot0Field
    (g : SmoothRiemannianMetric I M) (om : SmoothCcTensor g 0 1)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 1
        (ipLowCc (I := I) (M := M) g om) W =
      operatorFieldApply (I := I) (M := M) g 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W) om := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  let alpha : Tensor0SSpace 1 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 1 I x from om.toSection x)
      (unitTensor (I := I) (M := M) x)
  have hflat : ∀ z : TangentSpace I x,
      unitModel (I := I) (M := M) g 1 om x (fun _ : Fin 1 => z) =
        g.inner x (inverseMetricSharpFib (I := I) g x alpha) z := by
    intro z
    rw [inverseMetricSharpFib_inner]
    change Tensor0SSpace.toModel alpha (fun _ : Fin 1 => (z : E)) =
      cotangentToDualLinear (I := I) (x := x) alpha z
    rw [show cotangentToDualLinear (I := I) (x := x) alpha z =
      cotangentToDual (I := I) (x := x) alpha z from rfl]
    rw [cotangentToDual_apply]
    rfl
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [ipLowCc_toSec_ip (I := I) (M := M) g om x
    (inverseMetricSharpFib (I := I) g x alpha) hflat]
  rw [cometricRaiseSlot0Field_toSection,
    cometricRaiseSlot0Fib_clm_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitTensor_toModel_apply (x : M) (m : Fin 0 → E) :
    Tensor0SSpace.toModel (unitTensor (I := I) (M := M) x) m = 1 := by
  rw [unitTensor, Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem unitModel_add
    (g : SmoothRiemannianMetric I M)
    (A B : SmoothCcTensor g 0 2) (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 (A + B) x v =
      unitModel (I := I) (M := M) g 2 A x v +
        unitModel (I := I) (M := M) g 2 B x v := by
  simp only [unitModel]
  rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
    Pi.add_apply, add_apply,
    Tensor0SSpace.toModel_add, add_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma tensor0S_curry_zero_eq_smul_unitTensor
    (x : M) (D : Tensor0SSpace 1 I x) (v₀ : E) :
    tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v₀) =
      Tensor0SSpace.toModel D (fun _ : Fin 1 => v₀) •
        unitTensor (I := I) (M := M) x := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  have h₁ : Tensor0SSpace.toModel
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 0 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v₀)) m =
      Tensor0SSpace.toModel D (Fin.cons v₀ m) :=
    TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (n := 0)
      (T := D) (v0 := v₀) (vs := m)
  rw [h₁, Tensor0SSpace.toModel_smul,
    smul_apply, unitTensor_toModel_apply (I := I) (M := M) x m,
    smul_eq_mul, mul_one]
  congr 1
  funext k
  refine Fin.cases ?_ (fun j => j.elim0) k
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma continuousLinearMap_apply_smul_unitTensor (x : M) (s : ℕ)
    (A : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (c : ℝ) :
    A (c • unitTensor (I := I) (M := M) x) =
      c • A (unitTensor (I := I) (M := M) x) := A.map_smul c _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_two_zero_three_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 4 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 4 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 3 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 4 → E) =
        Fin.cons (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 3 x _ D₁
      (m 1) (fun j : Fin 3 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 3 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_two_zero_four_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 4) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 4) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 4 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 4 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 5 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 5 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 4 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 4 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 4 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 5 → E) =
        Fin.cons (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 4 x _ D₁
      (m 1) (fun j : Fin 4 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 4 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_two_zero_two_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 2 I x) :
    (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 2) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 2 j)) := by
    rw [show
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 1 3 x
            (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 1 3 x _ D
      (m 0) (Fin.tail m)]
    set D₁ : Tensor0SSpace 1 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₁
    rw [show
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 1 K).toSection x) D₁) =
          slotExtendFib (I := I) (M := M) 0 2 x
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
              K.toSection x) D₁ from rfl]
    rw [show (Fin.tail m : Fin 3 → E) =
        Fin.cons (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j)) from by
      funext k
      fin_cases k <;> rfl]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 0 2 x _ D₁
      (m 1) (fun j : Fin 2 => m (Fin.natAdd 2 j))]
    rw [tensor0S_curry_zero_eq_smul_unitTensor (I := I) (M := M) x D₁ (m 1)]
    rw [continuousLinearMap_apply_smul_unitTensor (I := I) (M := M) x 2 _ _]
    rw [← hkappa, Tensor0SSpace.toModel_smul,
      smul_apply, smul_eq_mul]
    have hD₁val : Tensor0SSpace.toModel D₁ (fun _ : Fin 1 => m 1) =
        Tensor0SSpace.toModel D ![m 0, m 1] := by
      rw [hD₁, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 1) (T := D) (v0 := m 0)
        (vs := fun _ : Fin 1 => m 1)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₁val]
    first
      | rfl
      | (congr 1; first | rfl | (congr 1; funext k; fin_cases k <;> rfl))
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private lemma slotExtendIter_three_zero_two_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 2) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
      (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 2) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 2 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
        (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 2 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 5 I x from
          (slotExtendIter (I := I) (M := M) g 0 2 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 2 4 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 4 I x from
              (slotExtendIter (I := I) (M := M) g 0 2 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 2 4 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₂
    rw [slotExtendIter_two_zero_two_apply (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 4 → E) ∘ Fin.castAdd 2)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma slotExtendIter_three_zero_three_apply (g : SmoothRiemannianMetric I M)
    (K : SmoothCcTensor g 0 3) (x : M) (D : Tensor0SSpace 3 I x) :
    (show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
      (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D =
    tensor0SProdKappaFib (I := I) (p := 3) (q := 3) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
        (unitTensor (I := I) (M := M) x)) D := by
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  beta_reduce
  set kappa : Tensor0SSpace 3 I x :=
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from K.toSection x)
      (unitTensor (I := I) (M := M) x) with hkappa
  have hLHS : Tensor0SSpace.toModel
      ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
        (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) m =
      Tensor0SSpace.toModel D ![m 0, m 1, m 2] *
        Tensor0SSpace.toModel kappa (fun j : Fin 3 => m (Fin.natAdd 3 j)) := by
    rw [show
        ((show Tensor0SSpace 3 I x →L[ℝ] Tensor0SSpace 6 I x from
          (slotExtendIter (I := I) (M := M) g 0 3 3 K).toSection x) D) =
          slotExtendFib (I := I) (M := M) 2 5 x
            (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 5 I x from
              (slotExtendIter (I := I) (M := M) g 0 3 2 K).toSection x) D
          from rfl]
    rw [show m = Fin.cons (m 0) (Fin.tail m) from (Fin.cons_self_tail m).symm]
    rw [slotExtendFib_apply_eval (I := I) (M := M) 2 5 x _ D
      (m 0) (Fin.tail m)]
    set D₂ : Tensor0SSpace 2 I x :=
      tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 2 x D
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) with hD₂
    rw [slotExtendIter_two_zero_three_apply (I := I) (M := M) g K x D₂, ← hkappa,
      tensor0SProdKappaFib_apply (I := I) x kappa D₂,
      Tensor0SSpace.toModel_ofModel,
      Bundle.continuousMultilinearMap.modelProduct_apply]
    have hD₂val : Tensor0SSpace.toModel D₂
        ((Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3) =
        Tensor0SSpace.toModel D ![m 0, m 1, m 2] := by
      rw [hD₂, TensorMultilinear.tensor0S_curry_toModel_apply
        (I := I) (M := M) (n := 2) (T := D) (v0 := m 0)
        (vs := (Fin.tail m : Fin 5 → E) ∘ Fin.castAdd 3)]
      congr 1
      funext k
      fin_cases k <;> rfl
    rw [hD₂val]
    first
      | rfl
      | (congr 2; funext j; fin_cases j <;> rfl)
  rw [hLHS, tensor0SProdKappaFib_apply (I := I) x kappa D,
    Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  congr 1
  all_goals
    first
      | rfl
      | (congr 1; funext k; fin_cases k <;> rfl)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_permutationCoefficient_apply
    (g : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g 0 d) :
    ccOperatorFieldComp (I := I) (M := M) g 0 d d
        (permCoeff (I := I) (M := M) g ρ) S =
      domDomCongrSection (I := I) g ρ S := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  rw [domDomCongrSection_unitModel]
  rw [unitModel, operatorFieldComposition_toSection, ContinuousLinearMap.comp_apply]
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) (unitTensor (I := I) (M := M) x))) = _
  rw [slotPermCLM_apply, Tensor0SSpace.toModel_ofModel]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_permutationCoefficient_apply_eq_rsDomDomCongrSection
    (g : SmoothRiemannianMetric I M) {a d : ℕ}
    (ρ : Equiv.Perm (Fin d)) (S : SmoothCcTensor g a d) :
    ccOperatorFieldComp (I := I) (M := M) g a d d
        (permCoeff (I := I) (M := M) g ρ) S =
      rsDomDomCongrSection (I := I) (M := M) g a d ρ S := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection, rsDomDomCongrSection_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      (slotPermCLM (I := I) ρ x
        ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
          S.toSection x) D)) =
    Tensor0SSpace.toModel
      ((show Tensor0SSpace a I x →L[ℝ] Tensor0SSpace d I x from
        rsDomDomCongr ρ (S.toSection x)) D)
  rw [toModel_rsDomDomCongr_apply, slotPermCLM_apply,
    Tensor0SSpace.toModel_ofModel]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_slotExtend_apply
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g (a + 1) (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A)
        (slotExtend (I := I) (M := M) g a b B) =
      slotExtend (I := I) (M := M) g a c
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [operatorFieldComposition_toSection, slotExtend_toSection, slotExtend_toSection,
    slotExtend_toSection, operatorFieldComposition_toSection]
  apply ContinuousLinearMap.ext
  intro D
  rw [ContinuousLinearMap.comp_apply]
  rw [DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply,
    DifferentialGeometry.Analysis.Spectral.slotExtendFib_apply]
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [ContinuousLinearMap.comp_assoc]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem operatorFieldComposition_slotExtendIter_two_apply
    (g : SmoothRiemannianMetric I M) (a b c : ℕ)
    (A : SmoothCcTensor g b c) (B : SmoothCcTensor g a b) :
    ccOperatorFieldComp (I := I) (M := M) g (a + 2) (b + 2) (c + 2)
        (slotExtendIter (I := I) (M := M) g b c 2 A)
        (slotExtendIter (I := I) (M := M) g a b 2 B) =
      slotExtendIter (I := I) (M := M) g a c 2
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B) := by
  change ccOperatorFieldComp (I := I) (M := M) g ((a + 1) + 1) ((b + 1) + 1) ((c + 1) + 1)
      (slotExtend (I := I) (M := M) g (b + 1) (c + 1)
        (slotExtend (I := I) (M := M) g b c A))
      (slotExtend (I := I) (M := M) g (a + 1) (b + 1)
        (slotExtend (I := I) (M := M) g a b B)) =
    slotExtend (I := I) (M := M) g (a + 1) (c + 1)
      (slotExtend (I := I) (M := M) g a c
        (ccOperatorFieldComp (I := I) (M := M) g a b c A B))
  rw [operatorFieldComposition_slotExtend_apply (I := I) (M := M) g (a + 1) (b + 1) (c + 1)]
  rw [operatorFieldComposition_slotExtend_apply (I := I) (M := M) g a b c]

noncomputable def koszulCovectorCoefficient
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  (1 / 2 : ℝ) •
    (permCoeff (I := I) (M := M) g (Equiv.swap (0 : Fin 3) 2) +
      permCoeff (I := I) (M := M) g (finRotate 3) -
      permCoeff (I := I) (M := M) g (Equiv.swap (1 : Fin 3) 2))

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem koszulCovectorCoefficient_apply
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (koszulCovectorCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      koszulCovecCc (I := I) g T := by
  have hs := symmS_eq_self_of_ccTensorBilin_symm
    (I := I) (M := M) g T hT
  have hp (ρ : Equiv.Perm (Fin 3)) :
      operatorFieldApply (I := I) (M := M) g 3 3
          (permCoeff (I := I) (M := M) g ρ)
          (covGrad (I := I) (M := M) g 0 2 T) =
        domDomCongrSection (I := I) g ρ
          (covGrad (I := I) (M := M) g 0 2 T) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g ρ
        (covGrad (I := I) (M := M) g 0 2 T)
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, koszulCovectorCoefficient, operatorFieldApplication_smul_left,
    operatorFieldApplication_sub_left, operatorFieldApplication_add_left, hp, hp, hp]
  rw [koszulCovecCc, symmSCovGrad3, hs]

noncomputable def metricConnectionDifferenceLoweringCoefficient
    (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (permCoeff (I := I) (M := M) g (finRotate 3).symm)
    (koszulCovectorCoefficient (I := I) (M := M) g)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricConnectionDifferenceLoweringCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g T x u v) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 3
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 T) =
      lieCorrectionZeroKappa (I := I) (M := M) g gm g := by
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, metricConnectionDifferenceLoweringCoefficient, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (koszulCovectorCoefficient (I := I) (M := M) g)
      (covGrad (I := I) (M := M) g 0 2 T) =
        koszulCovecCc (I := I) g T by
      simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
        koszulCovectorCoefficient_apply (I := I) (M := M) g T hT]
  have hp : operatorFieldApply (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3).symm)
      (koszulCovecCc (I := I) g T) =
        domDomCongrSection (I := I) g (finRotate 3).symm
          (koszulCovecCc (I := I) g T) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (finRotate 3).symm
        (koszulCovecCc (I := I) g T)
  rw [hp]
  exact (kappa_self (I := I) (M := M) g gm T htie).symm

def tensorThreeTwoBlockPermutation : Equiv.Perm (Fin 5) :=
  ⟨![2, 3, 4, 0, 1], ![3, 4, 0, 1, 2], by decide, by decide⟩

noncomputable def tensorThreeTwoProductCoefficient
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 5 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 5 5
    (permCoeff (I := I) (M := M) g tensorThreeTwoBlockPermutation)
    (slotExtendIter (I := I) (M := M) g 0 2 3 W)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem tensorThreeTwoProductCoefficient_apply
    (g : SmoothRiemannianMetric I M) (K : SmoothCcTensor g 0 3)
    (W : SmoothCcTensor g 0 2) :
    ccOperatorFieldComp (I := I) (M := M) g 0 3 5
        (tensorThreeTwoProductCoefficient (I := I) (M := M) g W) K =
      ccOperatorFieldComp (I := I) (M := M) g 0 2 5
        (slotExtendIter (I := I) (M := M) g 0 3 2 K) W := by
  have hp (ρ : Equiv.Perm (Fin 5)) (S : SmoothCcTensor g 0 5) :
      ccOperatorFieldComp (I := I) (M := M) g 0 5 5
          (permCoeff (I := I) (M := M) g ρ) S =
        domDomCongrSection (I := I) g ρ S := by
    simpa only [ccOperatorFieldComp] using operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g ρ S
  rw [operatorFieldComposition_zero_eq_operatorFieldApply, operatorFieldComposition_zero_eq_operatorFieldApply, tensorThreeTwoProductCoefficient,
    ← operatorFieldApplication_assoc, ← operatorFieldComposition_zero_eq_operatorFieldApply, hp]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro m
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [slotExtendIter_three_zero_two_apply (I := I) (M := M) g W x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        K.toSection x) (unitTensor (I := I) (M := M) x)),
    slotExtendIter_two_zero_three_apply (I := I) (M := M) g K x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        W.toSection x) (unitTensor (I := I) (M := M) x))]
  rw [tensor0SProdKappaFib_apply, tensor0SProdKappaFib_apply,
    Tensor0SSpace.toModel_ofModel, Tensor0SSpace.toModel_ofModel,
    Bundle.continuousMultilinearMap.modelProduct_apply,
    Bundle.continuousMultilinearMap.modelProduct_apply]
  have hK :
      ((fun i => m (tensorThreeTwoBlockPermutation i)) ∘ Fin.castAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := by
    funext j
    fin_cases j <;> rfl
  have hW :
      ((fun i => m (tensorThreeTwoBlockPermutation i)) ∘ Fin.natAdd 3) =
        (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  have hK₀ :
      (m ∘ Fin.natAdd 2) =
        (fun j : Fin 3 => m (Fin.natAdd 2 j)) := rfl
  have hW₀ :
      (m ∘ Fin.castAdd 3) = (![m 0, m 1] : Fin 2 → E) := by
    funext j
    fin_cases j <;> rfl
  rw [hK, hW, hK₀, hW₀]
  exact mul_comm _ _

noncomputable def lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (reindexedPureTrace (I := I) (M := M) g gm 2 σlast)
    (ccOperatorFieldComp (I := I) (M := M) g 3 6 4
      (reindexedPureTrace (I := I) (M := M) g gm 4
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoThreeOne)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 6
        (slotExtendIter (I := I) (M := M) g 0 3 3
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm gB))
        (ccOperatorFieldComp (I := I) (M := M) g 3 5 3
          (reindexedPureTrace (I := I) (M := M) g gm 3
            LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroOneFour)
          (ccOperatorFieldComp (I := I) (M := M) g 3 3 5
            (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
            (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)))))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (σlast : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroMixedConnectionHalfExpansion (I := I) (M := M) g gm gB σlast) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W σlast)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hprod :
      operatorFieldApply (I := I) (M := M) g 2 5
          (slotExtendIter (I := I) (M := M) g 0 3 2
            (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g)) W =
        operatorFieldApply (I := I) (M := M) g 3 5
          (tensorThreeTwoProductCoefficient (I := I) (M := M) g W)
          (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) := by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      (tensorThreeTwoProductCoefficient_apply (I := I) (M := M) g
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g) W).symm
  have hconn :
      operatorFieldApply (I := I) (M := M) g 3 3
          (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
          (covGrad (I := I) (M := M) g 0 2 P) =
        metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g gm g := by
    change operatorFieldApply (I := I) (M := M) g 3 3
        (metricConnectionDifferenceLoweringCoefficient (I := I) (M := M) g)
        (covGrad (I := I) (M := M) g 0 2 P) =
      lieCorrectionZeroKappa (I := I) (M := M) g gm g
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      metricConnectionDifferenceLoweringCoefficient_apply (I := I) (M := M) g gm P hP htie
  rw [lieCorrectionZeroMixedConnectionHalfExpansion]
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hprod, ← hconn]
  rw [lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc,
      ← operatorFieldApplication_assoc]

noncomputable def lieCorrectionZeroMixedConnectionDerivativeCoefficient
    (g gm gB : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) •
    (lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W
        LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne +
      lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient (I := I) (M := M) g gm gB W
        (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lieCorrectionZeroMixedConnectionDerivativeCoefficient_apply
    (g gm gB : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroMixedConnectionExpansion (I := I) (M := M) g gm gB) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroMixedConnectionDerivativeCoefficient (I := I) (M := M) g gm gB W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [lieCorrectionZeroMixedConnectionExpansion, operatorFieldApplication_smul_left, operatorFieldApplication_add_left]
  have hhalf := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply (I := I) (M := M) g gm gB P W
    LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne hP htie
  have hhalf' := lieCorrectionZeroMixedConnectionHalfDerivativeCoefficient_apply (I := I) (M := M) g gm gB P W
    (lieCorrectionZeroMixedConnectionTraceOutputSwapPermutation * LieCorrectionZeroCore.lieCorrectionZeroMixedConnectionPermutationCycleZeroTwoOne) hP htie
  rw [hhalf, hhalf']
  rw [lieCorrectionZeroMixedConnectionDerivativeCoefficient, operatorFieldApplication_smul_left, operatorFieldApplication_add_left]

noncomputable def lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (reindexedCometricDoubleTrace (I := I) (M := M) g gm)
    (ccOperatorFieldComp (I := I) (M := M) g 3 1 4
      (lieCorrectionZeroVectorBundleMetricConnectionDifferenceTerm (I := I) (M := M) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 1 1
        (cometricRaiseSlot0Field (I := I) (M := M) g 0 W)
        (ccOperatorFieldComp (I := I) (M := M) g 3 3 1
          (reindexedPureTrace (I := I) (M := M) g gm 1 (Equiv.refl _))
          (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm))))

noncomputable def lieCorrectionZeroVectorBundleDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  (2 : ℝ) • lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient (I := I) (M := M) g gm W

omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroVectorBundleDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (lieCorrectionZeroVectorBundleExpansion (I := I) (M := M) g gm) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (lieCorrectionZeroVectorBundleDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hip := operatorFieldApplication_ipLowCc_eq_cometricRaiseSlot0Field (I := I) (M := M) g (deTurckVectorFieldCovector (I := I) (M := M) g gm g) W
  have hw := deTurckVectorFieldCovector_eq_reindexedPureTrace_ccOperatorFieldComp (I := I) (M := M) g gm
  have hconn := RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_apply (I := I) (M := M) g gm P hP htie
  rw [lieCorrectionZeroVectorBundleExpansion, operatorFieldApplication_smul_left]
  rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hip]
  rw [hw, operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [← hconn]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply]
  rw [lieCorrectionZeroVectorBundleDerivativeCoefficient, lieCorrectionZeroVectorBundleUnscaledDerivativeCoefficient, operatorFieldApplication_smul_left]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

noncomputable def connectionDifferenceInsertionInnerDerivativeCoefficient
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (slotInsertEndoCc (I := I) (M := M) g 2
      (symmRaiseEndo (I := I) (M := M) g W))
    (permCoeff (I := I) (M := M) g (finRotate 3))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private lemma unitModel_eq_ccTensorBilin_toModel
    (g : SmoothRiemannianMetric I M) (S : SmoothCcTensor g 0 2)
    (x : M) (v : Fin 2 → E) :
    unitModel (I := I) (M := M) g 2 S x v =
      ccTensorBilin (I := I) g S x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)) := by
  have h := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g S x
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
  change unitModel (I := I) (M := M) g 2 S x
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)),
        tangentSpaceModelContinuousLinearEquiv (I := I) x
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))] = _ at h
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  conv_lhs => rw [hv]
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma connContr11_insert_toModel
    (g₁ g₀ : SmoothRiemannianMetric I M) (x : M)
    (D : Tensor0SSpace 2 I x) (v : Fin 3 → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
          (connectionDifferenceContrInsertionInnerField (I := I) g₀ g₁).toSection x) D) v =
      Tensor0SSpace.toModel D
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            (PDE.DeTurck.connectionDifference (I := I) g₁ g₀ x
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
              ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2))),
          v 0] := by
  rw [connectionDifferenceContrInsertionInnerField_toSection, connContr11_insert]
  congr 1

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma metricLoweredConnectionDifferenceCoefficient_unitModel_toModel
    (g g₁ : SmoothRiemannianMetric I M) (x : M) (v : Fin 3 → E) :
    unitModel (I := I) (M := M) g 3
        (metricLoweredConnectionDifferenceCoefficient (I := I) g g₁) x v =
      g.inner x (PDE.DeTurck.connectionDifference (I := I) g₁ g x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 2)) := by
  have h := connectionDifferenceLoweredCc_unitModel_apply' (I := I) (M := M) g g₁ x
    (fun i => (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v i))
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using h

omit [NeZero (Module.finrank ℝ E)] in
omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem connectionDifferenceInsertionInnerDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 3
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 3
        (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) := by
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient, ← operatorFieldApplication_assoc]
  rw [show operatorFieldApply (I := I) (M := M) g 3 3
      (permCoeff (I := I) (M := M) g (finRotate 3))
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) =
        domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm) by
    simpa only [operatorFieldComposition_zero_eq_operatorFieldApply] using
      operatorFieldComposition_permutationCoefficient_apply (I := I) (M := M) g (finRotate 3)
        (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [connContr11_insert_toModel]
  change unitModel (I := I) (M := M) g 2 (symmS (I := I) (M := M) g W) x _ = _
  rw [unitModel_eq_ccTensorBilin_toModel]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [ccTensorBilin_symmS]
  change _ = Tensor0SSpace.toModel
    (DifferentialGeometry.Geometry.Curvature.slotInsertEndoFib (I := I) (M := M) 3 0 x
      (symmRaiseEndo (I := I) (M := M) g W x)
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (domDomCongrSection (I := I) g (finRotate 3)
          (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)).toSection x)
        (unitTensor (I := I) (M := M) x))) m
  rw [slotInsertEndoFib_apply_eval]
  change _ = unitModel (I := I) (M := M) g 3
    (domDomCongrSection (I := I) g (finRotate 3)
      (metricLoweredConnectionDifferenceCoefficient (I := I) g gm)) x
    (Function.update m 0
      (tangentLinearMapToModel (symmRaiseEndo (I := I) (M := M) g W x) (m 0)))
  rw [domDomCongrSection_unitModel, ContinuousMultilinearMap.domDomCongr_apply]
  rw [show (fun i =>
      Function.update m 0
        (tangentLinearMapToModel (symmRaiseEndo (I := I) (M := M) g W x) (m 0))
          ((finRotate 3) i)) =
        ![m 1, m 2,
          tangentLinearMapToModel (symmRaiseEndo (I := I) (M := M) g W x) (m 0)] by
    funext j
    fin_cases j <;> rfl]
  rw [metricLoweredConnectionDifferenceCoefficient_unitModel_toModel]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, tangentLinearMapToModel_apply,
    ContinuousLinearEquiv.symm_apply_apply]
  rw [g.symm, symmRaiseEndo_apply, inner_symmRaiseEndo]
  exact ccTensorBilinSymm_symm (I := I) g W x _ _

noncomputable def connectionDifferenceInsertionInnerActionCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 3 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 3 3
    (connectionDifferenceInsertionInnerDerivativeCoefficient (I := I) (M := M) g W)
    (RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator (I := I) (M := M) g gm)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connectionDifferenceInsertionInnerActionCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 3
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 3
        (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [connectionDifferenceInsertionInnerDerivativeCoefficient_apply (I := I) (M := M) g gm W]
  rw [← RicciDeTurckLowOrder.connectionDifferenceLowOrderOperator_apply (I := I) (M := M) g gm P hP htie]
  rw [connectionDifferenceInsertionInnerActionCoefficient, ← operatorFieldApplication_assoc]
  rw [operatorFieldComposition_zero_eq_operatorFieldApply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_reindexCoeffGen_symmetrized_input
    (g : SmoothRiemannianMetric I M) {s : ℕ}
    (R : SmoothCcTensor g 2 s) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 s
        (reindexCoeffGen (I := I) (M := M) g 2 s R innerCoreInPerm10)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 2 s R
        (symmS (I := I) (M := M) g W) := by
  have hperm : innerCoreInPerm10 = Equiv.swap (0 : Fin 2) 1 := by
    ext j
    fin_cases j <;> rfl
  rw [hperm]
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [unitModel, unitModel, operatorFieldApplication_toSection, operatorFieldApplication_toSection,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  rw [reindexCoeffGen_toSection, reindexCoeffFibGen_apply]
  have hu : Tensor0SSpace.ofModel
      (ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x)))) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (symmS (I := I) (M := M) g W).toSection x)
        (unitTensor (I := I) (M := M) x) := by
    apply Tensor0SSpace.toModel_injective
    change ContinuousMultilinearMap.domDomCongr (Equiv.swap (0 : Fin 2) 1)
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
            (symmS (I := I) (M := M) g W).toSection x)
            (unitTensor (I := I) (M := M) x))) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (symmS (I := I) (M := M) g W).toSection x)
          (unitTensor (I := I) (M := M) x))
    apply ContinuousMultilinearMap.ext
    intro v
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    have hv : (fun i => v ((Equiv.swap (0 : Fin 2) 1) i)) = ![v 1, v 0] := by
      funext j
      fin_cases j <;> rfl
    have hv' : v = ![v 0, v 1] := by
      funext j
      fin_cases j <;> rfl
    rw [hv]
    conv_rhs => rw [hv']
    change unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 1, v 0] =
      unitModel (I := I) (M := M) g 2
        (symmS (I := I) (M := M) g W) x ![v 0, v 1]
    have hleft := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
      (symmS (I := I) (M := M) g W) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
    have hright := unitModel_eq_ccTensorBilin_local (I := I) (M := M) g
      (symmS (I := I) (M := M) g W) x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
    change unitModel (I := I) (M := M) g 2 (symmS (I := I) (M := M) g W) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1)),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))] = _ at hleft
    change unitModel (I := I) (M := M) g 2 (symmS (I := I) (M := M) g W) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0)),
          tangentSpaceModelContinuousLinearEquiv (I := I) x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))] = _ at hright
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hleft hright
    rw [hleft, hright, ccTensorBilin_symmS, ccTensorBilin_symmS]
    exact ccTensorBilinSymm_symm (I := I) g W x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 1))
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (v 0))
  rw [hu]

def ricciQuadraticPermutationCycleZeroThreeOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 2, 0, 1], ![2, 3, 1, 0], by decide, by decide⟩

def ricciQuadraticPermutationSwapBlocks : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

def ricciQuadraticPermutationCycleZeroThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![3, 1, 0, 2], ![2, 1, 3, 0], by decide, by decide⟩

def ricciQuadraticPermutationCycleZeroOneThreeTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

def ricciQuadraticPermutationCycleZeroOneTwo : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

def ricciQuadraticPermutationSwapZeroTwo : Equiv.Perm (Fin 4) :=
  ⟨![2, 1, 0, 3], ![2, 1, 0, 3], by decide, by decide⟩

def ricciQuadraticPermutationSwapZeroOne : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

def ricciQuadraticPermutationRotateInputs : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private noncomputable def nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

noncomputable def ricciQuadraticKernelDerivativeNestedTerm
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4)) :
    SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 3 3 3
        (permCoeff (I := I) (M := M) g mid)
        (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W)))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeNestedTerm_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (mid : Equiv.Perm (Fin 3)) (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gm)
            (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
              (permCoeff (I := I) (M := M) g mid)
              (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W mid out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_apply (I := I) (M := M) g gm P W hP htie
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hinner]
  rw [ricciQuadraticKernelDerivativeNestedTerm]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo hP htie

private noncomputable def reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapBlocks)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroOne)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

private noncomputable def nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroThreeTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
        (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))

private noncomputable def reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneThreeTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (connectionDifferenceContrInsertionInnerField (I := I) g gm)))
    innerCoreInPerm10

private noncomputable def bareConnectionDifferenceKernelTerm_cycleZeroOneTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationCycleZeroOneTwo)
    (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (connectionDifferenceContrInsertionInnerField (I := I) g gm))

private noncomputable def reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo
    (g gm : SmoothRiemannianMetric I M) : SmoothCcTensor g 2 4 :=
  reindexCoeffGen (I := I) (M := M) g 2 4
    (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
      (permCoeff (I := I) (M := M) g ricciQuadraticPermutationSwapZeroTwo)
      (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
        (connectionDifferenceContravariantInsertionField (I := I) g gm)
        (ccOperatorFieldComp (I := I) (M := M) g 2 3 3
          (permCoeff (I := I) (M := M) g ricciQuadraticPermutationRotateInputs)
          (connectionDifferenceContrInsertionInnerField (I := I) g gm))))
    innerCoreInPerm10

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private noncomputable def ricciConnectionDifferenceQuadraticKernelSum
    (g gm : SmoothRiemannianMetric I M) :
    SmoothCcTensor g 2 4 :=
      nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo (I := I) (M := M) g gm +
      reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g gm +
      nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g gm +
      reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g gm +
      bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g gm +
      reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g gm

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem ricciConnectionDifferenceQuadraticKernel_eq_sum
    (g gm : SmoothRiemannianMetric I M) :
    ricciConnectionDifferenceQuadraticKernel (I := I) (M := M) g gm =
      ricciConnectionDifferenceQuadraticKernelSum (I := I) (M := M) g gm := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  unfold ricciConnectionDifferenceQuadraticKernel ricciConnectionDifferenceQuadraticKernelSum
  rfl

noncomputable def ricciQuadraticKernelDerivativeBareTerm
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4)) : SmoothCcTensor g 3 4 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 4
      (permCoeff (I := I) (M := M) g out)
    (ccOperatorFieldComp (I := I) (M := M) g 3 3 4
      (connectionDifferenceContravariantInsertionField (I := I) g gm)
      (connectionDifferenceInsertionInnerActionCoefficient (I := I) (M := M) g gm W))

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciQuadraticKernelDerivativeBareTerm_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (out : Equiv.Perm (Fin 4))
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4
        (ccOperatorFieldComp (I := I) (M := M) g 2 4 4
          (permCoeff (I := I) (M := M) g out)
          (ccOperatorFieldComp (I := I) (M := M) g 2 3 4
            (connectionDifferenceContravariantInsertionField (I := I) g gm)
            (connectionDifferenceContrInsertionInnerField (I := I) g gm)))
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W out)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hinner := connectionDifferenceInsertionInnerActionCoefficient_apply (I := I) (M := M) g gm P W hP htie
  conv_lhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]
  rw [hinner]
  rw [ricciQuadraticKernelDerivativeBareTerm]
  conv_rhs =>
    rw [← operatorFieldApplication_assoc, ← operatorFieldApplication_assoc]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks hP htie

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo hP htie

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutationCycleZeroOneThreeTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeBareTerm_apply (I := I) (M := M) g gm P W ricciQuadraticPermutationCycleZeroOneThreeTwo hP htie

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem bareConnectionDifferenceKernelTerm_cycleZeroOneTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (bareConnectionDifferenceKernelTerm_cycleZeroOneTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutationCycleZeroOneTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [bareConnectionDifferenceKernelTerm_cycleZeroOneTwo]
  exact ricciQuadraticKernelDerivativeBareTerm_apply (I := I) (M := M) g gm P W ricciQuadraticPermutationCycleZeroOneTwo hP htie

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 4 (reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 4
        (ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo, operatorFieldApplication_reindexCoeffGen_symmetrized_input]
  exact ricciQuadraticKernelDerivativeNestedTerm_apply (I := I) (M := M) g gm P W
    ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo hP htie

noncomputable def ricciQuadraticKernelDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 4 :=
  ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationCycleZeroThreeOneTwo +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationSwapZeroOne ricciQuadraticPermutationSwapBlocks +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationCycleZeroThreeTwo +
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutationCycleZeroOneThreeTwo +
    ricciQuadraticKernelDerivativeBareTerm (I := I) (M := M) g gm W ricciQuadraticPermutationCycleZeroOneTwo +
    ricciQuadraticKernelDerivativeNestedTerm (I := I) (M := M) g gm W ricciQuadraticPermutationRotateInputs ricciQuadraticPermutationSwapZeroTwo

noncomputable def ricciConnectionDifferenceQuadraticDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ccOperatorFieldComp (I := I) (M := M) g 3 4 2
    (ricciCometricFourTraceCastG0 (I := I) g gm)
    (ricciQuadraticKernelDerivativeCoefficient (I := I) (M := M) g gm W)

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricciConnectionDifferenceQuadraticDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ricciConnectionDifferenceQuadraticArm (I := I) (M := M) g gm)
        (symmS (I := I) (M := M) g W) =
      operatorFieldApply (I := I) (M := M) g 3 2
        (ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  rw [ricciConnectionDifferenceQuadraticArm, ← operatorFieldApplication_assoc, ricciConnectionDifferenceQuadraticKernel_eq_sum]
  unfold ricciConnectionDifferenceQuadraticKernelSum
  simp only [operatorFieldApplication_add_left]
  have h0 := nestedConnectionDifferenceKernelTerm_swapZeroOne_cycleZeroThreeOneTwo_apply (I := I) (M := M) g gm P W hP htie
  have h1 := reindexedNestedConnectionDifferenceKernelTerm_swapZeroOne_swapBlocks_apply (I := I) (M := M) g gm P W hP htie
  have h2 := nestedConnectionDifferenceKernelTerm_rotateInputs_cycleZeroThreeTwo_apply (I := I) (M := M) g gm P W hP htie
  have h3 := reindexedBareConnectionDifferenceKernelTerm_cycleZeroOneThreeTwo_apply (I := I) (M := M) g gm P W hP htie
  have h4 := bareConnectionDifferenceKernelTerm_cycleZeroOneTwo_apply (I := I) (M := M) g gm P W hP htie
  have h5 := reindexedNestedConnectionDifferenceKernelTerm_rotateInputs_swapZeroTwo_apply (I := I) (M := M) g gm P W hP htie
  rw [h0, h1, h2, h3, h4, h5]
  rw [ricciConnectionDifferenceQuadraticDerivativeCoefficient, ← operatorFieldApplication_assoc, ricciQuadraticKernelDerivativeCoefficient]
  simp only [operatorFieldApplication_add_left]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_ccSlotSwapField_apply
    (g : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccSlotSwapField (I := I) (M := M) g) W =
      domDomCongrSection (I := I) g (Equiv.swap (0 : Fin 2) 1) W := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [unitModel, operatorFieldApplication_toSection, ContinuousLinearMap.comp_apply,
    ccSlotSwapField_toSection]
  change Tensor0SSpace.toModel
      (slotSwapFib (I := I) (M := M) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          W.toSection x) (unitTensor (I := I) (M := M) x))) v =
    (ContinuousMultilinearMap.domDomCongr
      (Equiv.swap (0 : Fin 2) 1)
      (unitModel (I := I) (M := M) g 2 W x)) v
  rw [slotSwapFib_apply, Tensor0SSpace.toModel_ofModel,
    ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem operatorFieldApplication_ccInputSlotSymm_apply
    (g : SmoothRiemannianMetric I M) (C : SmoothCcTensor g 2 2)
    (W : SmoothCcTensor g 0 2) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (ccInputSlotSymm (I := I) (M := M) g C) W =
      operatorFieldApply (I := I) (M := M) g 2 2 C
        (symmS (I := I) (M := M) g W) := by
  simp only [ccInputSlotSymm, ccInputSlotSymm]
  have hswap := operatorFieldApplication_ccSlotSwapField_apply (I := I) (M := M) g W
  rw [operatorFieldApplication_smul_left, operatorFieldApplication_add_left, ← operatorFieldApplication_assoc,
    hswap]
  simp only [symmS, ccTensor02Symm]
  rw [operatorFieldApplication_smul_right, operatorFieldApplication_add_right]

noncomputable def ricciConnectionDifferenceDerivativeCoefficient
    (g gm : SmoothRiemannianMetric I M) (W : SmoothCcTensor g 0 2) :
    SmoothCcTensor g 3 2 :=
  ricciConnectionDifferenceQuadraticDerivativeCoefficient (I := I) (M := M) g gm W +
    RicciDeTurckLowOrder.ricciConnectionDerivativeTransposedCoefficient (I := I) (M := M) g gm
      (symmS (I := I) (M := M) g W)

omit [SigmaCompactSpace M] in
theorem ricciConnectionDifferenceDerivativeCoefficient_apply
    (g gm : SmoothRiemannianMetric I M) (P W : SmoothCcTensor g 0 2)
    (hP : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g P x u v =
        ccTensorBilin (I := I) g P x v u)
    (htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v) :
    operatorFieldApply (I := I) (M := M) g 2 2
        (RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W =
      operatorFieldApply (I := I) (M := M) g 3 2
        (ricciConnectionDifferenceDerivativeCoefficient (I := I) (M := M) g gm W)
        (covGrad (I := I) (M := M) g 0 2 P) := by
  have hsymmInput := operatorFieldApplication_ccInputSlotSymm_apply (I := I) (M := M) g
    (RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm P) W
  have haa := ricciConnectionDifferenceQuadraticDerivativeCoefficient_apply (I := I) (M := M) g gm P W hP htie
  have hda := RicciDeTurckLowOrder.ricciCovariantDerivativeConnectionDifferenceLowOrder_apply (I := I) (M := M) g gm P
    (symmS (I := I) (M := M) g W)
  rw [RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient, hsymmInput,
    RicciDeTurckLowOrder.ricciConnectionDifferenceLowOrderCoefficient, operatorFieldApplication_add_left]
  rw [haa, hda]
  rw [ricciConnectionDifferenceDerivativeCoefficient, operatorFieldApplication_add_left]

omit [SigmaCompactSpace M] in
theorem lowerScalePathIntegrand_decomposition
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g
        (0 : SmoothCcTensor g 0 2)) δ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    RicciDeTurckLowOrder.pathIntegrand (I := I) (M := M) g g T hδ hδZ s =
      let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
      ((((-2 : ℝ) •
            RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
          (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g -
            deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
              lieDecompositionQ lieDecompositionEps s)) +
        lieCorrectionZeroVectorBundle (I := I) (M := M) g gm) +
        lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g) +
        lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
  rw [RicciDeTurckLowOrder.selfLow_good (I := I) (M := M)
    g g T hT hδ_lt hδ hδZ hs]
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let Q := deTurckLieTopOrderPairingFamily (I := I) (M := M) g T hδ hδZ
    lieDecompositionQ lieDecompositionEps s
  have hlie :
      deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q =
        (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g - Q) +
          lieCorrectionZeroVectorBundle (I := I) (M := M) g gm +
          lieCorrectionZeroMixedConnection (I := I) (M := M) g gm g +
          lieCorrectionZeroRiemann (I := I) (M := M) g gm := by
    calc
      _ = (deTurckLieCovariantDerivativeArmField (I := I) (M := M) g gm g - Q) +
          (lieCorrectionZeroField (I := I) (M := M) g gm g +
            deTurckLieEndoArmField (I := I) (M := M) g gm g) := by
        rw [deTurckLieCoeffField_eq_covDerivArm_add_endoArm]
        abel
      _ = _ := by
        rw [tail_base_split (I := I) (M := M) g gm g]
        simp only [sub_self, zero_add]
        abel
  calc
    _ = (-2 : ℝ) •
          RicciDeTurckLowOrder.symmetrizedRicciConnectionDifferenceLowOrderCoefficient (I := I) (M := M) g gm (s • T) +
        (deTurckLieCoeffField (I := I) (M := M) g gm g +
          lieCorrectionZeroField (I := I) (M := M) g gm g - Q) := by
      simp only [gm, Q]
      abel
    _ = _ := by
      rw [hlie]
      simp only [gm, Q]
      abel

end RicciDeTurckPairing
end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
end
end
