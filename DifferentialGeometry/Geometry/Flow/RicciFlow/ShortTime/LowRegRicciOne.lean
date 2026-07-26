import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoeffJets

/-!
# Low-regularity order-one Ricci coefficient

This file proves the dimension-three `H2` jet estimate for the concrete
order-one connection-difference coefficient in the Ricci linearization.  The
proof uses only the metric perturbation jet through order three.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem iteratedCovGrad_smul_real
    (g : SmoothRiemannianMetric I M) (r s j : ℕ) (c : ℝ)
    (W : SmoothCcTensor g r s) :
    iteratedCovGrad (I := I) g r s j (c • W) =
      c • iteratedCovGrad (I := I) g r s j W := by
  induction j with
  | zero => simp only [iteratedCovGrad_zero]
  | succ j ih =>
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ, ih,
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.covGrad_smul]

private theorem pure_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁ =
      pureTrace (I := I) (M := M) g₀ g₁ 2 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem norm_eq_of_sq_eq {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) : a = b := by
  have hs := congrArg Real.sqrt h
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb] at hs

private theorem slotExtend_norm_le
    (g : SmoothRiemannianMetric I M) (r s i : ℕ)
    (Φ : SmoothCcTensor g r s) :
    ‖iteratedCovGrad (I := I) g (r + 1) (s + 1) i
        (slotExtend (I := I) (M := M) g r s Φ)‖ ≤
      Real.sqrt (Module.finrank ℝ E) *
        ‖iteratedCovGrad (I := I) g r s i Φ‖ := by
  classical
  let F : M → ℝ := fun x => (Module.finrank ℝ E : ℝ) *
    riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
      ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
  have hFint : Integrable F
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    dsimp only [F]
    exact (integrable_riemannianFiberNormSq_toSection
      (I := I) (M := M) g r (s + i)
      (iteratedCovGrad (I := I) g r s i Φ)).const_mul _
  have hsq := normSq_le_integral_of_pointwise_fiberNormSq_le_rs
    (I := I) (M := M) g (r + 1) ((s + 1) + i)
    (iteratedCovGrad (I := I) g (r + 1) (s + 1) i
      (slotExtend (I := I) (M := M) g r s Φ))
    F hFint (fun x => rfns_iteratedCovGrad_slotExtend_le
      (I := I) (M := M) g r s Φ i x)
  have hint : (∫ x,
      riemannianFiberNormSq (I := I) (M := M) g r (s + i) x
        ((iteratedCovGrad (I := I) g r s i Φ).toSection x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ‖iteratedCovGrad (I := I) g r s i Φ‖ ^ 2 := by
    rw [SmoothCcTensor.norm_def,
      tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
        (I := I) (M := M) g r (s + i)]
  dsimp only [F] at hsq
  rw [MeasureTheory.integral_const_mul, hint] at hsq
  refine le_of_sq_le_sq ?_
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [mul_pow, Real.sq_sqrt (by positivity :
    (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ))]
  exact hsq

private theorem conn_norm_eq
    (g₀ g₁ : SmoothRiemannianMetric I M) (i : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 1 2 i
        (connDiffSection (I := I) g₁ g₀)‖ =
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (connDiffLoweredCc (I := I) g₀ g₁)‖ := by
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 1 (2 + i),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 0 (3 + i)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      (connLow_rfns (I := I) (M := M) g₀ g₁ i x).symm)

private theorem core_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g₁ : SmoothRiemannianMetric I M) (A : ℝ)
    (hA : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 3 i
        (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2) ≤ A ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2) ≤
      (3 * A) ^ 2 := by
  classical
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ≤
        3 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (connDiffLoweredCc (I := I) g₀ g₁)‖ := by
    intro i
    rw [connDiffContrInsertionField_eq_reindex_slotExtend_two
      (I := I) (M := M) g₀ g₁,
      iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
      norm_reindexCoeffGen_eq (I := I) (M := M)]
    calc
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          ‖iteratedCovGrad (I := I) g₀ 2 3 i
            (slotExtend (I := I) (M := M) g₀ 1 2
              (connDiffSection (I := I) g₁ g₀))‖ :=
        slotExtend_norm_le (I := I) (M := M) g₀ 2 3 i _
      _ ≤ Real.sqrt (Module.finrank ℝ E) *
          (Real.sqrt (Module.finrank ℝ E) *
            ‖iteratedCovGrad (I := I) g₀ 1 2 i
              (connDiffSection (I := I) g₁ g₀)‖) :=
        mul_le_mul_of_nonneg_left
          (slotExtend_norm_le (I := I) (M := M) g₀ 1 2 i _)
          (Real.sqrt_nonneg _)
      _ = 3 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (connDiffLoweredCc (I := I) g₀ g₁)‖ := by
        rw [conn_norm_eq (I := I) (M := M) g₀ g₁ i, hDim]
        have hs : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
          Real.sq_sqrt (by norm_num)
        nlinarith
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 ≤
        9 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range 3,
        9 * ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 9 * (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 0 3 i
          (connDiffLoweredCc (I := I) g₀ g₁)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 9 * A ^ 2 := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = (3 * A) ^ 2 := by ring

private def ko0312 : Equiv.Perm (Fin 4) :=
  ⟨![0, 3, 1, 2], ![0, 2, 3, 1], by decide, by decide⟩

private def ko0213 : Equiv.Perm (Fin 4) :=
  ⟨![0, 2, 1, 3], ![0, 2, 1, 3], by decide, by decide⟩

private def ko2301 : Equiv.Perm (Fin 4) :=
  ⟨![2, 3, 0, 1], ![2, 3, 0, 1], by decide, by decide⟩

private def ko1302 : Equiv.Perm (Fin 4) :=
  ⟨![1, 3, 0, 2], ![2, 0, 3, 1], by decide, by decide⟩

private def ko1203 : Equiv.Perm (Fin 4) :=
  ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

private def ki102 : Equiv.Perm (Fin 3) :=
  ⟨![1, 0, 2], ![1, 0, 2], by decide, by decide⟩

private def ki120 : Equiv.Perm (Fin 3) :=
  ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩

private theorem slotPerm_smooth
    (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SBundle.TensorRSModel d d ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SBundle.TensorRSModel d d ℝ E)
        (E := fun z : M => Tensor0SBundle.TensorRSSpace d d I z) x
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) ρ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₁ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (F₂ := Tensor0SBundle.Tensor0SModel d ℝ E)
    (V₂ := fun z : M => Tensor0SBundle.Tensor0SSpace d I z)
    (φ := fun x : M => slotPermCLM (I := I) ρ x)
  intro Y
  have h := slotPermCLM_field_contMDiff
    (I := I) ρ (fun x => Y x) Y.contMDiff
  refine h.congr (fun x => ?_)
  exact congrArg (fun t => TotalSpace.mk'
    (Tensor0SBundle.Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SBundle.Tensor0SSpace d I z) x t) rfl

private def slotPerm1
    (g₀ : SmoothRiemannianMetric I M) {d : ℕ}
    (ρ : Equiv.Perm (Fin d)) : SmoothCcTensor g₀ d d where
  toSection :=
    { toFun := fun x : M =>
        (show Tensor0SBundle.TensorRSSpace d d I x from
          slotPermCLM (I := I) ρ x)
      contMDiff_toFun := slotPerm_smooth (I := I) (M := M) g₀ ρ }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

private theorem kernel_split
    (g₀ g₁ : SmoothRiemannianMetric I M) :
    linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁ =
      -(reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4
            (slotPerm1 (I := I) (M := M) g₀ ko0312)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ki102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4
              (slotPerm1 (I := I) (M := M) g₀ ko0213)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ki120
        + appCcRS (I := I) (M := M) g₀ 3 4 4
            (slotPerm1 (I := I) (M := M) g₀ ko2301)
            (connDiffContrInsertionField (I := I) g₀ g₁)
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4
              (slotPerm1 (I := I) (M := M) g₀ ko1302)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ki102
        + reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4
              (slotPerm1 (I := I) (M := M) g₀ ko1203)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ki120) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rfl

private theorem arm_rfns
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (appCcRS (I := I) (M := M) g₀ 3 4 4
            (slotPerm1 (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁))).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  refine rfns_iteratedCovGrad_rs_eq_of_section_domDomCongr
    (I := I) (M := M) g₀ 3 4 σ
    (connDiffContrInsertionField (I := I) g₀ g₁)
    (appCcRS (I := I) (M := M) g₀ 3 4 4
      (slotPerm1 (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁))
    (fun y d => ?_) q x
  have hy :
      (show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ]
          Tensor0SBundle.Tensor0SSpace 4 I y from
        (appCcRS (I := I) (M := M) g₀ 3 4 4
          (slotPerm1 (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection y) d =
        slotPermCLM (I := I) σ y
          ((show Tensor0SBundle.Tensor0SSpace 3 I y →L[ℝ]
              Tensor0SBundle.Tensor0SSpace 4 I y from
            (connDiffContrInsertionField (I := I) g₀ g₁).toSection y) d) := rfl
  rw [hy, slotPermCLM_apply, Tensor0SBundle.Tensor0SSpace.toModel_ofModel]

private theorem fullArm_rfns
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3))
    (q : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (reindexCoeffGen (I := I) (M := M) g₀ 3 4
            (appCcRS (I := I) (M := M) g₀ 3 4 4
              (slotPerm1 (I := I) (M := M) g₀ σ)
              (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 3 (4 + q) x
        ((iteratedCovGrad (I := I) g₀ 3 4 q
          (connDiffContrInsertionField (I := I) g₀ g₁)).toSection x) := by
  rw [rfns_iteratedCovGrad_reindexCoeffGen_eq
    (I := I) (M := M) g₀ 3 4
    (appCcRS (I := I) (M := M) g₀ 3 4 4
      (slotPerm1 (I := I) (M := M) g₀ σ)
      (connDiffContrInsertionField (I := I) g₀ g₁)) ρ q x]
  exact arm_rfns (I := I) (M := M) g₀ g₁ σ q x

private theorem arm_norm
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (appCcRS (I := I) (M := M) g₀ 3 4 4
          (slotPerm1 (I := I) (M := M) g₀ σ)
          (connDiffContrInsertionField (I := I) g₀ g₁))‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 3 (4 + q),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 3 (4 + q)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      arm_rfns (I := I) (M := M) g₀ g₁ σ q x)

private theorem fullArm_norm
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (σ : Equiv.Perm (Fin 4)) (ρ : Equiv.Perm (Fin 3)) (q : ℕ) :
    ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (reindexCoeffGen (I := I) (M := M) g₀ 3 4
          (appCcRS (I := I) (M := M) g₀ 3 4 4
            (slotPerm1 (I := I) (M := M) g₀ σ)
            (connDiffContrInsertionField (I := I) g₀ g₁)) ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 3 4 q
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
  refine norm_eq_of_sq_eq (norm_nonneg _) (norm_nonneg _) ?_
  rw [SmoothCcTensor.norm_def, SmoothCcTensor.norm_def,
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 3 (4 + q),
    tensorL2Norm_sq_toFun_eq_integral_riemannianFiberNormSq_rs
      (I := I) (M := M) g₀ 3 (4 + q)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x =>
      fullArm_rfns (I := I) (M := M) g₀ g₁ σ ρ q x)

private theorem norm_five_le
    {V : Type*} [SeminormedAddCommGroup V]
    {a b c d e : V} {n : ℝ}
    (ha : ‖a‖ = n) (hb : ‖b‖ = n) (hc : ‖c‖ = n)
    (hd : ‖d‖ = n) (he : ‖e‖ = n) :
    ‖a + b + c + d + e‖ ≤ 5 * n := by
  have h1 := norm_add_le (a + b + c + d) e
  have h2 := norm_add_le (a + b + c) d
  have h3 := norm_add_le (a + b) c
  have h4 := norm_add_le a b
  linarith

private theorem kernel_h2
    (g₀ g₁ : SmoothRiemannianMetric I M) (A : ℝ)
    (hA : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2) ≤ A ^ 2) :
    (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2) ≤
      (5 * A) ^ 2 := by
  classical
  have hsplit := kernel_split (I := I) (M := M) g₀ g₁
  have hper : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ≤
      5 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ := by
    intro i
    rw [hsplit, iteratedCovGrad_neg, norm_neg,
      iteratedCovGrad_add, iteratedCovGrad_add,
      iteratedCovGrad_add, iteratedCovGrad_add]
    exact norm_five_le
      (fullArm_norm (I := I) (M := M) g₀ g₁ ko0312 ki102 i)
      (fullArm_norm (I := I) (M := M) g₀ g₁ ko0213 ki120 i)
      (arm_norm (I := I) (M := M) g₀ g₁ ko2301 i)
      (fullArm_norm (I := I) (M := M) g₀ g₁ ko1302 ki102 i)
      (fullArm_norm (I := I) (M := M) g₀ g₁ ko1203 ki120 i)
  have hsq : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)‖ ^ 2 ≤
      25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 := by
    intro i
    have h := pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
    nlinarith
  calc
    _ ≤ ∑ i ∈ Finset.range 3,
        25 * ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hsq i
    _ = 25 * (∑ i ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g₀ 3 4 i
          (connDiffContrInsertionField (I := I) g₀ g₁)‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ 25 * A ^ 2 := mul_le_mul_of_nonneg_left hA (by norm_num)
    _ = (5 * A) ^ 2 := by ring

/-- On a closed three-manifold, the concrete order-one Ricci
connection-difference coefficient has a tame intrinsic `H2` bound.  The
moving-trace factor depends only on the lower metric `H2` radius, while the
third metric derivative enters through one affine top-order arm. -/
theorem ricci1_h2_tame
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B0 B1 : ℝ → ℝ,
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (R A : ℝ), 0 ≤ R → 0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (linearizedRicciConnDiffOrder1CoeffField
              (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤
          (B0 R + B1 R * A) ^ 2 := by
  classical
  obtain ⟨Capp, hCapp, happ⟩ :=
    appRS_h2_h2_h2 (I := I) (M := M) hDim g₀ 3 4 2
  obtain ⟨Bt, hBt, htrace⟩ :=
    trace2_h2 (I := I) (M := M) hDim g₀ hδ₀
  obtain ⟨Bc0, Bc1, hBc0, hBc1, hconn⟩ :=
    connLow_tame (I := I) (M := M) hDim g₀ hδ₀
  let B0 : ℝ → ℝ := fun R => Capp * (2 * Bt R) * (15 * Bc0 R)
  let B1 : ℝ → ℝ := fun R => Capp * (2 * Bt R) * (15 * Bc1 R)
  refine ⟨B0, B1, fun R hR => by
    exact mul_nonneg
      (mul_nonneg hCapp (mul_nonneg (by norm_num) (hBt R hR)))
      (mul_nonneg (by norm_num) (hBc0 R hR)), fun R hR => by
    exact mul_nonneg
      (mul_nonneg hCapp (mul_nonneg (by norm_num) (hBt R hR)))
      (mul_nonneg (by norm_num) (hBc1 R hR)), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound R A hR hA hP2 hP3
  let pureF : SmoothCcTensor g₀ 4 2 :=
    ricciArmPrincipalCoeffPure (I := I) (M := M) g₀ g₁
  let R1 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0231
  let R2 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm0321
  let R3 : SmoothCcTensor g₀ 4 2 :=
    reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF fourTraceArgPerm2301
  have hcomb : ricciCometricFourTraceCastG0 (I := I) g₀ g₁ =
      ((1 : ℝ) / 2) • (R1 + R2 - pureF - R3) := by
    simpa only [pureF, R1, R2, R3] using
      ricciCometricFourTraceCastG0_eq_reindex_combination
        (I := I) (M := M) g₀ g₁
  have hreindex : ∀ (ρ : Equiv.Perm (Fin 4)) (i : ℕ),
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (reindexCoeffGen (I := I) (M := M) g₀ 4 2 pureF ρ)‖ =
      ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ := by
    intro ρ i
    rw [iteratedCovGrad_reindexCoeffGen (I := I) (M := M),
      norm_reindexCoeffGen_eq (I := I) (M := M)]
  have hpure : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2) ≤
      (Bt R) ^ 2 := by
    have ht := htrace g₁ P htie hδ_le hδ_nonneg hbound
      (Equiv.refl (Fin 4)) R hR hP2
    calc
      _ = ∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i
            (lc0Trace (I := I) (M := M) g₀ g₁ 2
              (Equiv.refl (Fin 4)))‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [lc0Trace, iteratedCovGrad_reindexCoeffGen
          (I := I) (M := M),
          norm_reindexCoeffGen_eq (I := I) (M := M),
          pureF, pure_eq (I := I) (M := M) g₀ g₁]
      _ ≤ (Bt R) ^ 2 := ht
  have hcastNorm : ∀ i : ℕ,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ≤
      2 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ := by
    intro i
    rw [hcomb, iteratedCovGrad_smul_real,
      iteratedCovGrad_sub, iteratedCovGrad_sub, iteratedCovGrad_add,
      norm_smul, Real.norm_eq_abs,
      show |(1 : ℝ) / 2| = 1 / 2 by norm_num]
    have h1 := norm_add_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1)
      (iteratedCovGrad (I := I) g₀ 4 2 i R2)
    have h2 := norm_sub_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1 +
        iteratedCovGrad (I := I) g₀ 4 2 i R2)
      (iteratedCovGrad (I := I) g₀ 4 2 i pureF)
    have h3 := norm_sub_le
      (iteratedCovGrad (I := I) g₀ 4 2 i R1 +
        iteratedCovGrad (I := I) g₀ 4 2 i R2 -
        iteratedCovGrad (I := I) g₀ 4 2 i pureF)
      (iteratedCovGrad (I := I) g₀ 4 2 i R3)
    rw [show ‖iteratedCovGrad (I := I) g₀ 4 2 i R1‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm0231 i,
      show ‖iteratedCovGrad (I := I) g₀ 4 2 i R2‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm0321 i] at h1
    rw [show ‖iteratedCovGrad (I := I) g₀ 4 2 i R3‖ =
        ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ by
          exact hreindex fourTraceArgPerm2301 i] at h3
    linarith [norm_nonneg
      (iteratedCovGrad (I := I) g₀ 4 2 i pureF)]
  have hcast : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 4 2 i
        (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2) ≤
      (2 * Bt R) ^ 2 := by
    have hsq : ∀ i : ℕ,
        ‖iteratedCovGrad (I := I) g₀ 4 2 i
          (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)‖ ^ 2 ≤
        4 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2 := by
      intro i
      have h := pow_le_pow_left₀ (norm_nonneg _) (hcastNorm i) 2
      nlinarith
    calc
      _ ≤ ∑ i ∈ Finset.range 3,
          4 * ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hsq i
      _ = 4 * (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 4 2 i pureF‖ ^ 2) := by
        rw [Finset.mul_sum]
      _ ≤ 4 * (Bt R) ^ 2 :=
        mul_le_mul_of_nonneg_left hpure (by norm_num)
      _ = (2 * Bt R) ^ 2 := by ring
  have hconnLow := hconn g₁ P htie hδ_le hδ_nonneg hbound
    R A hR hA hP2 hP3
  have hcore := core_h2 (I := I) (M := M) hDim g₀ g₁
    (Bc0 R + Bc1 R * A) hconnLow
  have hkernel := kernel_h2 (I := I) (M := M) g₀ g₁
    (3 * (Bc0 R + Bc1 R * A)) hcore
  have hkernel' : (∑ i ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 3 4 i
        (linearizedRicciConnDiffOrder1KernelField
          (I := I) g₀ g₁)‖ ^ 2) ≤
      (15 * (Bc0 R + Bc1 R * A)) ^ 2 := by
    convert hkernel using 1 <;> ring
  rw [linearizedRicciConnDiffOrder1CoeffField_eq_appCcRS
    (I := I) (M := M) g₀ g₁]
  have hout := happ
      (ricciCometricFourTraceCastG0 (I := I) g₀ g₁)
      (linearizedRicciConnDiffOrder1KernelField (I := I) g₀ g₁)
      (2 * Bt R) (15 * (Bc0 R + Bc1 R * A))
      (mul_nonneg (by norm_num) (hBt R hR))
      (mul_nonneg (by norm_num)
        (add_nonneg (hBc0 R hR) (mul_nonneg (hBc1 R hR) hA)))
      hcast hkernel'
  have hfactor :
      Capp * (2 * Bt R) * (15 * (Bc0 R + Bc1 R * A)) =
        B0 R + B1 R * A := by
    simp only [B0, B1]
    ring
  rw [← hfactor]
  exact hout

/-- One-parameter compatibility wrapper around `ricci1_h2_tame`. -/
theorem ricci1_h2
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ B : ℝ → ℝ,
      (∀ A : ℝ, 0 ≤ A → 0 ≤ B A) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (P : SmoothCcTensor g₀ 0 2)
        (htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w +
            ccTensorBilinSymm (I := I) g₀ P y v w)
        {δ : ℝ} (hδ_le : δ ≤ δ₀) (hδ_nonneg : 0 ≤ δ)
        (hbound : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ P) δ)
        (A : ℝ), 0 ≤ A →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 →
        (∑ i ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g₀ 3 2 i
            (linearizedRicciConnDiffOrder1CoeffField
              (I := I) (M := M) g₀ g₁)‖ ^ 2) ≤ (B A) ^ 2 := by
  obtain ⟨B0, B1, hB0, hB1, htame⟩ :=
    ricci1_h2_tame (I := I) (M := M) hDim g₀ hδ₀
  let B : ℝ → ℝ := fun A => B0 A + B1 A * A
  refine ⟨B, fun A hA =>
    add_nonneg (hB0 A hA) (mul_nonneg (hB1 A hA) hA), ?_⟩
  intro g₁ P htie δ hδ_le hδ_nonneg hbound A hA hP3
  have hP2 : (∑ j ∈ Finset.range 3,
      ‖iteratedCovGrad (I := I) g₀ 0 2 j P‖ ^ 2) ≤ A ^ 2 := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (by omega))
      (fun j _ _ => sq_nonneg _)).trans hP3
  simpa only [B] using htame g₁ P htie hδ_le hδ_nonneg hbound
    A A hA hA hP2 hP3

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
