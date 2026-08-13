import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.ConnDiffJetL2Summed
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle MeasureTheory
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
    DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private def kOutPerm0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def kOutPerm0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def kOutPerm2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def kOutPerm1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def kOutPerm1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def kInPerm102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def kInPerm120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [SigmaCompactSpace M] in
private theorem slotPermCcFib_contMDiff (_g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) ρ x)
  intro Y
  have h := slotPermCLM_field_contMDiff (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk' (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

private def slotPermCc (g₀ : SmoothRiemannianMetric I M) {d : ℕ} (ρ : Equiv.Perm (Fin d)) :
    SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from slotPermCLM (I := I) ρ x)
      contMDiff_toFun := slotPermCcFib_contMDiff (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem kernelField_eq_neg_arm_combination (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁ =
      -(reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I)
            (M := M) g₀ kOutPerm0312)
            (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I)
              (M := M) g₀ kOutPerm0213)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120
        + ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I)
          (M := M) g₀ kOutPerm2301)
            (connDiffContrInsertionField (I := I) g₀ g₁)
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I)
              (M := M) g₀ kOutPerm1302)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I)
              (M := M) g₀ kOutPerm1203)
              (connDiffContrInsertionField (I := I) g₀ g₁)) kInPerm120) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem armOuter_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  refine riemannianFiberNormSq_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g₀ 3 4 σ
    (connDiffContrInsertionField (I := I) g₀ g₁)
    (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁))
    (fun y d => ?_) q x
  have hy : (show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
      (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
        (connDiffContrInsertionField (I := I) g₀ g₁)).toSection y) d =
      slotPermCLM (I := I) σ y
        ((show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ] Tensor0SBundle.Tensor0SSpace 4 I y from
          (connDiffContrInsertionField (I := I) g₀ g₁).toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

private theorem armFull_rfns_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  rw [riemannianFiberNormSq_iteratedCovGrad_reindexCoeffGen_eq (I := I) (M := M) g₀ 3 4
    (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁)) ρ q x]
  exact armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x

private lemma c3_norm_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 = b ^ 2) : a = b := by
  have hs := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] at hs

private theorem armOuter_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armOuter_rfns_eq (I := I) (M := M) g₀ g₁ σ q x
  rw [hpt]

private theorem armFull_norm_eq (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine c3_norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs (I := I) (M := M) g₀ 3 (4 + q)
      (iteratedCovGrad (I := I) g₀ 3 4 q (connDiffContrInsertionField (I := I) g₀ g₁))]
  have hpt : (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (ccOperatorFieldComp (I := I) (M := M) g₀ 3 4 4 (slotPermCc (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x)) =
      (fun x => riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x)) :=
    funext fun x => armFull_rfns_eq (I := I) (M := M) g₀ g₁ σ ρ q x
  rw [hpt]

private lemma c3_norm_five_le {V : Type*} [SeminormedAddCommGroup V] {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n) (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have t1 := norm_add_le (a + b + c + d) e
  have t2 := norm_add_le (a + b + c) d
  have t3 := norm_add_le (a + b) c
  have t4 := norm_add_le a b
  linarith

private theorem lie_normSq_le_25 (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
      25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by
  have h5 : ‖iteratedCovGrad (I := I) g₀ 3 4 i
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ≤
      5 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
    rw [kernelField_eq_neg_arm_combination (I := I) g₀ g₁, iteratedCovGrad_neg, norm_neg,
      iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add, iteratedCovGrad_add]
    exact c3_norm_five_le
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0312 kInPerm102 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm0213 kInPerm120 i)
      (armOuter_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm2301 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1302 kInPerm102 i)
      (armFull_norm_eq (I := I) (M := M) g₀ g₁ kOutPerm1203 kInPerm120 i)
  have hsq := pow_le_pow_left₀ (norm_nonneg (iteratedCovGrad (I := I) g₀ 3 4 i
    (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁))) h5 2
  calc ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2
      ≤ (5 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖) ^ 2 := hsq
    _ = 25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by ring

theorem linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_perOrder_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ (i : ℕ), i ≤ a →
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
              (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
                (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hcd⟩ :=
    connDiffContrInsertionField_realizedFam_jetL2_perOrder_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨25 * Ktop, mul_nonneg (by norm_num) hKtop_nn,
    fun i => 25 * Kc i, fun i => mul_nonneg (by norm_num) (hKc_nn i), ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs i hi
  have hb := lie_normSq_le_25 (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) i
  have hc := hcd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs i hi
  have h25 := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 25 by norm_num)
  calc ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
      ≤ 25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := hb
    _ ≤ 25 * (Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
          Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) := h25
    _ = 25 * Ktop * (‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T‖ ^ 2 +
            ‖iteratedCovGrad (I := I) g₀ 0 2 (i + 1) T'‖ ^ 2) +
          25 * Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
            (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring

theorem linearizedRicciConnDiffOrder1KernelField_realizedFam_jetL2_summed_topSeparated
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha_super : 2 * Module.finrank ℝ E + 10 ≤ a) {R : ℝ} (hR : 0 ≤ R)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
      ∀ (T T' : SmoothCcTensor g₀ 0 2)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀)
        (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        {δ' : ℝ} (_hδ'_le : δ' ≤ δ₀)
        (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T') δ'),
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤ R) →
        (∀ j : ℕ, j ≤ a + 2 → ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ≤ R) →
        ∀ (s : ℝ), s ∈ Set.Icc (0 : ℝ) 1 →
          ∑ i ∈ Finset.range (a + 1),
              ‖iteratedCovGrad (I := I) g₀ 3 4 i
                (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
                  (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
            Ktop * (∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
                (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                  ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by
  obtain ⟨Ktop, hKtop_nn, Kc, hKc_nn, hcd⟩ :=
    connDiffContrInsertionField_realizedFam_jetL2_summed_topSeparated
      (I := I) (M := M) g₀ a ha_super hR hδ₀
  refine ⟨25 * Ktop, mul_nonneg (by norm_num) hKtop_nn,
    25 * Kc, mul_nonneg (by norm_num) hKc_nn, ?_⟩
  intro T T' δ hδ_le hδ δ' hδ'_le hδ' hTball hT'ball s hs
  have hcd' := hcd T T' hδ_le hδ hδ'_le hδ' hTball hT'ball s hs
  have hsum25 : ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 ≤
      25 * ∑ i ∈ Finset.range (a + 1),
        ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀
            (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ =>
      lie_normSq_le_25 (I := I) (M := M) g₀ (realizedFam (I := I) g₀ T T' hδ hδ' s) i)
  have h25 := mul_le_mul_of_nonneg_left hcd' (show (0 : ℝ) ≤ 25 by norm_num)
  calc ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
            (linearizedRicciConnDiffOrder1KernelField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2
      ≤ 25 * ∑ i ∈ Finset.range (a + 1),
          ‖iteratedCovGrad (I := I) g₀ 3 4 i
            (connDiffContrInsertionField (I := I) g₀
              (realizedFam (I := I) g₀ T T' hδ hδ' s))‖ ^ 2 := hsum25
    _ ≤ 25 * (Ktop * (∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
            Kc * (1 + ∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2))) := h25
    _ = 25 * Ktop * (∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) +
          25 * Kc * (1 + ∑ j ∈ Finset.range (a + 2),
              (‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ^ 2 +
                ‖iteratedCovGrad (I := I) g₀ 0 2 j T'‖ ^ 2)) := by ring

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
