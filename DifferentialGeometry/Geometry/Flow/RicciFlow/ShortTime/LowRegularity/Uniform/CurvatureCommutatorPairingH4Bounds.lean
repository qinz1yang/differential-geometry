import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.GreenIdentityAndIBP.AllOrderGardingConstant
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.RicciTopOrderCoefficientBounds
import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.SecondDerivativePairing.ZeroOrderCoefficient
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.ConvexJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Bundle Manifold Set Filter Topology DifferentialGeometry.Tensor0SBundle ContinuousLinearMap
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem curvature_commutator_pairing_h4_uniform_bound
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∀ {η : ℝ}, 0 < η →
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∃ Gc : ℝ, 0 ≤ Gc ∧
          ∀ (T : SmoothCcTensor g 0 2)
            (_hT : ∀ (x : M) (u v : TangentSpace I x),
              ccTensorBilin (I := I) g T x u v =
                ccTensorBilin (I := I) g T x v u)
            {δ : ℝ}, δ ≤ 1 / 3 → 0 ≤ δ →
            ∀ (hδ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ)
              (hδZ : gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g
                  (0 : SmoothCcTensor g 0 2)) δ)
              {s : ℝ}, s ∈ Set.Icc (0 : ℝ) 1 →
            let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
            let Cφ :=
              deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
                deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g
            let B :=
              lieDecomposition2 (I := I) (M := M) g T hδ hδZ s + Cφ +
                (-2 * s : ℝ) •
                  RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
            let GT :=
              covGrad (I := I) (M := M) g 0 3
                  (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
                pointwiseTensorCurv (I := I) (M := M) g 3
                  (covGrad (I := I) (M := M) g 0 2 T)
            let LT := oneMinusConnLapSmooth (I := I) g 0 2 T
            2 * |tensorL2Inner (I := I) (M := M) g 0 2
                (oneMinusConnLapSmooth (I := I) g 0 2 LT).toFun
                (operatorFieldApply (I := I) (M := M) g 4 2 B GT).toFun| ≤
              η * ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖ ^ 2 +
                Gc * ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ^ 2 := by
  obtain ⟨Ktop, hKtop0, htop⟩ :=
    RicciDeTurckLowOrder.exists_topOrderKernel_path_riemannianFiberNormSq_le (I := I) (M := M)
  obtain ⟨Kcurv, hKcurv⟩ :=
    exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  intro η hη g hEq hjet
  obtain ⟨Kφ, hKφ0, hφ⟩ := metricPrincipalDefect_cap (I := I) (M := M) g gBase
  obtain ⟨Kcomm, hKcomm0, hcomm⟩ :=
    exists_iteratedRoughLapGrad_commutator_l2Norm_le
      (I := I) (M := M) g 2 2
  let KB2 : ℝ := 2 * Ktop ^ 2 + 2 * Kφ ^ 2
  have hKB2 : 0 ≤ KB2 := by positivity
  let KB : ℝ := Real.sqrt KB2
  let D : ℝ := KB * Kcomm * h2CovsumC Kcurv.rankTwo
  have hD0 : 0 ≤ D := mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) hKcomm0)
    (h2CovsumC_nonneg Kcurv.rankTwo)
  let Gc : ℝ := η⁻¹ * D ^ 2
  have hGc0 : 0 ≤ Gc :=
    mul_nonneg (inv_nonneg.mpr hη.le) (sq_nonneg D)
  refine ⟨Gc, hGc0, ?_⟩
  intro T hT δ hδ_le hδ0 hδ hδZ s hs
  dsimp only
  let gm := metricPerturbationPath (I := I) g T 0 hδ hδZ s
  let P := convexPerturbation (I := I) g T 0 s
  let Cφ : SmoothCcTensor g 4 2 :=
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase gm -
      deTurckMetricPrincipalDefectTotal (I := I) (M := M) g gBase g
  let Dtop : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let B : SmoothCcTensor g 4 2 :=
    lieDecomposition2 (I := I) (M := M) g T hδ hδZ s + Cφ +
      (-2 * s : ℝ) •
        RicciDeTurckLowOrder.ricciConnectionDifferenceTopOrderCoefficient (I := I) (M := M) g gm T
  let GT : SmoothCcTensor g 0 4 :=
    covGrad (I := I) (M := M) g 0 3
        (pointwiseTensorCurv (I := I) (M := M) g 2 T) +
      pointwiseTensorCurv (I := I) (M := M) g 3
        (covGrad (I := I) (M := M) g 0 2 T)
  let LT : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 T
  let V : SmoothCcTensor g 0 2 :=
    oneMinusConnLapSmooth (I := I) g 0 2 LT
  let Y : SmoothCcTensor g 0 2 :=
    operatorFieldApply (I := I) (M := M) g 4 2 B GT
  let y2 : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
  let y3 : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖
  let z : ℝ := ‖ccTensorToHs (I := I) (M := M) g 2 (4 : ℝ) T‖
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsmall : s ∈ metricPerturbationPathDomain (δ := δ) (δ' := δ) :=
    Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt hs
  have htie : ∀ (x : M) (u v : TangentSpace I x),
      gm.inner x u v =
        g.inner x u v + ccTensorBilinSymm (I := I) g P x u v :=
    fun x u v => metricPerturbationPath_inner_of_mem
      (I := I) g T 0 hδ hδZ hsmall x u v
  have hP : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g P) δ := by
    convert convexPerturbation_gFibreOpBound
      (I := I) (M := M) g T 0 hδ hδZ hs.1 hs.2 using 1
    all_goals ring
  let r1 : ℝ := δ / (1 - δ)
  let r2 : ℝ := δ / (1 - δ) ^ 2
  have hbase : 0 < 1 - δ := by linarith
  have hr1_0 : 0 ≤ r1 := div_nonneg hδ0 hbase.le
  have hr2_0 : 0 ≤ r2 := div_nonneg hδ0 (sq_nonneg _)
  have hr1 : r1 ≤ 1 := by
    dsimp only [r1]
    rw [div_le_iff₀ hbase]
    linarith
  have hr2 : r2 ≤ 1 := by
    dsimp only [r2]
    rw [div_le_iff₀ (sq_pos_of_pos hbase)]
    nlinarith [sq_nonneg δ]
  have hDtop : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Dtop.toSection x) ≤ Ktop ^ 2 := by
    intro x
    have hraw := htop g T hT hδ_le hδ0 hδ hδZ hs x
    have hscaled := pow_le_pow_left₀
      (mul_nonneg hKtop0 hr2_0)
      (mul_le_mul_of_nonneg_left hr2 hKtop0) 2
    simpa only [Dtop, r2, mul_one] using hraw.trans hscaled
  have hCφ : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (Cφ.toSection x) ≤ Kφ ^ 2 := by
    intro x
    have hraw := hφ gm P hδ_lt hδ0 htie hP x
    have hscaled := pow_le_pow_left₀
      (mul_nonneg hKφ0 hr1_0)
      (mul_le_mul_of_nonneg_left hr1 hKφ0) 2
    simpa only [Cφ, gm, r1, mul_one] using hraw.trans hscaled
  have hBdc : B = Dtop + Cφ := by
    dsimp only [B, Dtop]
    module
  have hB : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 4 2 x
          (B.toSection x) ≤ KB ^ 2 := by
    intro x
    have hsum := riemannianFiberNormSq_add_le
      (I := I) (M := M) g 4 2 x (Dtop.toSection x) (Cφ.toSection x)
    rw [hBdc, SmoothCcTensor.toSection_add, ContMDiffSection.coe_add,
      Pi.add_apply]
    calc
      _ ≤ 2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (Dtop.toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g 4 2 x
            (Cφ.toSection x) := hsum
      _ ≤ KB2 := by
        dsimp only [KB2]
        nlinarith [hDtop x, hCφ x]
      _ = KB ^ 2 := by
        dsimp only [KB]
        rw [Real.sq_sqrt hKB2]
  have hcommT := hcomm T
  have hcomm_eq :
      rawTensorConnLapSmooth (I := I) g 0 4
          (iteratedCovGrad (I := I) g 0 2 2 T) -
        iteratedCovGrad (I := I) g 0 2 2
          (rawTensorConnLapSmooth (I := I) g 0 2 T) = GT := by
    rw [rawConnLap_iteratedCovGrad_two_comm (I := I) (M := M) g 2 T]
    dsimp only [GT]
    module
  rw [hcomm_eq] at hcommT
  have hact : IsCurvAction0 (I := I) (M := M) g 2 Kcurv.rankTwo :=
    (hKcurv.bounds g hEq hjet).1
  have hcov :
      ∑ a ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 a T‖ ≤
        h2CovsumC Kcurv.rankTwo * y2 := by
    simpa only [y2] using covsum_hs_two
      (I := I) (M := M) g 2 hact T
  have hGT : ‖GT‖ ≤ Kcomm * (h2CovsumC Kcurv.rankTwo * y2) :=
    hcommT.trans (mul_le_mul_of_nonneg_left hcov hKcomm0)
  have hY : ‖Y‖ ≤ D * y2 := by
    have happ := operatorFieldApply_l2_le_of_pointwise_fiberNormSq_bound_left
      (I := I) (M := M) g 4 2 B GT KB (Real.sqrt_nonneg _) hB
    calc
      ‖Y‖ ≤ KB * ‖GT‖ := by simpa only [Y] using happ
      _ ≤ KB * (Kcomm * (h2CovsumC Kcurv.rankTwo * y2)) :=
        mul_le_mul_of_nonneg_left hGT (Real.sqrt_nonneg _)
      _ = D * y2 := by
        dsimp only [D]
        ring
  have hVnorm : ‖V‖ = z := by
    have heven := smoothCcToTensorHs_even_norm_eq_toL2_iter
      (I := I) (M := M) g 2 T
    change ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ =
      ‖SmoothCcTensor.toL2 V‖ at heven
    rw [SmoothCcTensor.norm_toL2] at heven
    simpa only [z, norm_ccHs_eq_smoothHs] using heven.symm
  have hy23 : y2 ≤ y3 := by
    simpa only [y2, y3] using
      ccToHs_norm_mono (I := I) (M := M) g 2 (by norm_num) T
  have hpair :
      |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Y.toFun| ≤
        z * (D * y3) := by
    calc
      _ ≤ ‖V‖ * ‖Y‖ := by
        rw [← SmoothCcTensor.inner_def (I := I) (M := M) V Y]
        exact abs_real_inner_le_norm V Y
      _ ≤ z * (D * y2) := by
        rw [hVnorm]
        exact mul_le_mul_of_nonneg_left hY (norm_nonneg _)
      _ ≤ z * (D * y3) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left hy23 hD0
  have hyoung :
      2 * z * (D * y3) ≤ η * z ^ 2 + η⁻¹ * (D * y3) ^ 2 := by
    have hinv : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
    have hsquare := mul_nonneg hinv (sq_nonneg (η * z - D * y3))
    have hexpand :
        η⁻¹ * (η * z - D * y3) ^ 2 =
          η * z ^ 2 - 2 * z * (D * y3) + η⁻¹ * (D * y3) ^ 2 := by
      field_simp [ne_of_gt hη]
      ring
    rw [hexpand] at hsquare
    linarith
  change
    2 * |tensorL2Inner (I := I) (M := M) g 0 2 V.toFun Y.toFun| ≤
      η * z ^ 2 + Gc * y3 ^ 2
  calc
    _ ≤ 2 * (z * (D * y3)) :=
      mul_le_mul_of_nonneg_left hpair (by norm_num)
    _ = 2 * z * (D * y3) := by ring
    _ ≤ η * z ^ 2 + η⁻¹ * (D * y3) ^ 2 := hyoung
    _ = η * z ^ 2 + Gc * y3 ^ 2 := by
      dsimp only [Gc]
      ring

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
