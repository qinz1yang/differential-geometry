import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Lipschitz
import DifferentialGeometry.Analysis.Estimates.QuarticInterpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetInterpolation
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJetNaturality
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorFieldJetDifference
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorFieldJetProduct
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ReindexedPureTraceCovariantJet

noncomputable section

set_option backward.isDefEq.respectTransparency false

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

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem metricLoweredConnectionDifference_self
    (g : SmoothRiemannianMetric I M) :
    metricLoweredConnectionDifference (I := I) (M := M) g g g = 0 := by
  refine smoothCcTensor_ext_of_unitModel (I := I) (M := M) g fun x => ?_
  apply ContinuousMultilinearMap.ext
  intro m
  rw [metricLoweredConnectionDifference_unitModel_apply]
  simp only [PDE.DeTurck.connectionDifference_self, Pi.zero_apply,
    ContinuousLinearMap.zero_apply, map_zero]
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
    rw [ccTensorBilin_zero_weight, ccTensorBilin_zero_weight]
  have hZtie : ∀ (x : M) (u v : TangentSpace I x),
      g.inner x u v =
        g.inner x u v +
          ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2) x u v := by
    intro x u v
    rw [ccTensorBilinSymm_apply, ccTensorBilin_zero_weight,
      ccTensorBilin_zero_weight]
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
  rw [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply,
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
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x m =
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
        (slotExtendFib (I := I) (M := M) 0 3 x
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
  rw [slotExtendFib_apply_eval (I := I) (M := M) 0 3 x
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
      (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
    B (u 0) (Fin.tail u)]
  have hc : tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0) =
      Tensor0SSpace.toModel B (fun _ : Fin 1 => u 0) •
        unitTensor (I := I) (M := M) x := by
    have h2 := rankZeroTensor_eq_smul_unit (I := I) (M := M) x
      (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) 0 x B (u 0))
    rw [h2]
    congr 1
    rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := B) (v0 := u 0) (vs := fun i : Fin 0 => i.elim0)]
    congr 1
    funext k
    fin_cases k
    rfl
  rw [hc, ContinuousLinearMap.map_smul, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  rw [show Tensor0SSpace.toModel
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 3 I x from
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀).toSection x)
        (unitTensor (I := I) (M := M) x)) (Fin.tail u) =
      unitModel (I := I) (M := M) g₀ 3
        (metricConnectionDifferenceLoweredCoefficient (I := I) (M := M) g₀ g₁ g₀) x
        (fun j => Fin.tail u j) from by rw [unitModel]]
  rw [metricConnectionDifferenceLoweredCoefficient_unitModel (I := I) (M := M) g₀ g₁ x (fun j => Fin.tail u j)]
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
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    apply congrArg (fun z : ℝ => s * z)
    simpa only [ccTensorBilin_apply] using hT x u v
  have hQsymm : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g Q x u v =
        ccTensorBilin (I := I) g Q x v u := by
    intro x u v
    simp only [hcQ, ccTensorBilin_apply, ccTensorModel_smul,
      ContinuousMultilinearMap.smul_apply, smul_eq_mul]
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
