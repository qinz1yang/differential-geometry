import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientJetBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.LowOrderCoefficientJetBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.DeTurckRemainderPrincipalArm.TameBounds

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
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
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.DeTurck
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem operatorFieldApplication_cap_hs_affine_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : max 2 (Module.finrank ℝ E / 2 * 2 + 1) ≤ a)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ {R₀ : ℝ}, 0 ≤ R₀ → ∀
        (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m * (1 + R₀) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hCl_nn, hfam⟩ :=
    exists_coeffContraction_secondCovGrad_smallFibreCoeff_Hs_family_affine_le
      (I := I) (M := M) g₀ a ha εC hεC_nn Kc hKc_nn
  refine ⟨Clower, hCl_nn, ?_⟩
  intro R₀ hR₀ C₂ T₀ hball hsup hjets m
  have h := hfam hR₀ C₂ T₀ hball hsup hjets m T₀ ⟨0, rfl⟩
  have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (by push_cast; ring) T₀
  rw [hshift] at h
  have hmul : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    mul_le_mul_of_nonneg_left
      (smoothCcToTensorHs_rawTensorConnLapSmooth_le
        (I := I) (M := M) g₀ (m : ℝ) T₀) hεC_nn
  exact le_trans h (add_le_add hmul (le_refl _))

theorem operatorFieldApplication_cap_hs_le
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : max 2 (Module.finrank ℝ E / 2 * 2 + 1) ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (εC : ℝ) (hεC_nn : 0 ≤ εC) (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Cop : ℕ → ℝ, (∀ m, 0 ≤ Cop m) ∧
      ∀ (C₂ : SmoothCcTensor g₀ (2 + 2) 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ (2 + 2) 2 x
            (C₂.toSection x) ≤ εC ^ 2) →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ (2 + 2) 2 i C₂‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (operatorFieldApply (I := I) (M := M) g₀ (2 + 2) 2 C₂
                (iteratedCovGrad (I := I) g₀ 0 2 2 T₀))‖ ≤
            εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ +
              Cop m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ := by
  classical
  obtain ⟨Clower, hCl_nn, hfam⟩ :=
    exists_coeffContraction_secondCovGrad_smallFibreCoeff_Hs_family_le
      (I := I) (M := M) g₀ a ha hR₀ εC hεC_nn Kc hKc_nn
  refine ⟨Clower, hCl_nn, ?_⟩
  intro C₂ T₀ hball hsup hjets m
  have h := hfam C₂ T₀ hball hsup hjets m T₀ ⟨0, rfl⟩
  have hshift : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m + 1 : ℕ) : ℝ) T₀‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T₀‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
      (by push_cast; ring) T₀
  rw [hshift] at h
  have hmul : εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 T₀)‖ ≤
      εC * ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T₀‖ :=
    mul_le_mul_of_nonneg_left
      (smoothCcToTensorHs_rawTensorConnLapSmooth_le
        (I := I) (M := M) g₀ (m : ℝ) T₀) hεC_nn
  exact le_trans h (by linarith only [hmul])

private lemma hsMono (g₀ : SmoothRiemannianMetric I M)
    {σ τ : ℝ} (hστ : σ ≤ τ) (w : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ w‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ τ w‖ := by
  have hbσ : smoothCcToTensorHs (I := I) (M := M) g₀ σ w =
      ccSpectralEmbed (I := I) (M := M) g₀ σ w :=
    Analysis.Parabolic.TensorHeatEquation.tensorHs.ext (funext fun i => rfl)
  have hbτ : smoothCcToTensorHs (I := I) (M := M) g₀ τ w =
      ccSpectralEmbed (I := I) (M := M) g₀ τ w :=
    Analysis.Parabolic.TensorHeatEquation.tensorHs.ext (funext fun i => rfl)
  rw [hbσ, hbτ]
  exact ccSpectralEmbed_norm_mono (I := I) (M := M) g₀ hστ w

theorem secondOrderCoefficient_jet_tower_sharp
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  classical
  obtain ⟨Kk, hKk_nn, hker⟩ := topKerJetSharp (I := I) (M := M) g
  refine ⟨Kk, hKk_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  have hδ_lt : δ < 1 := lt_of_le_of_lt hδ_le (by norm_num)
  have hsum : (0 : ℝ) ≤ ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hΛ : 0 ≤ Kk i * (1 + ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    mul_nonneg (hKk_nn i) (by linarith only [hsum])
  have hSI : Set.uIcc (0 : ℝ) 1 ⊆ metricPerturbationPathDomain (δ := δ) (δ' := δ) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Icc_subset_metricPerturbationPathDomain hδ_lt hδ_lt
  obtain ⟨X, hXdef, hXjet⟩ :
      ∃ X : SmoothCcTensor g 4 2,
        (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient = X ∧
          covariantJetNormSq (I := I) (M := M) g i X ≤
            Kk i * (1 + ∑ j ∈ Finset.range (i + 1),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :=
    ⟨rhsDecompositionTopInt (I := I) (M := M) g T hδ_lt hδg hδZ +
        RicciDeTurckLowOrder.selfTopInt (I := I) (M := M) g T hδ_lt hδg hδZ -
        deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g, rfl,
      path_add_sub_jet (I := I) (M := M) g 4 i hSI
        (rhsDecompositionTop (I := I) (M := M) g T hδg hδZ)
        (RicciDeTurckLowOrder.ricciDeTurckSelfTopOrderCoefficient (I := I) (M := M) g T hδg hδZ)
        (deTurckMetricPrincipalDefectTotal (I := I) (M := M) g g)
        (rhsDecompositionTop_joint (I := I) (M := M) g T hδ_lt hδg hδZ)
        (RicciDeTurckLowOrder.selfTop_joint (I := I) (M := M) g T hδg hδZ)
        hΛ (hker T hT hδ0 hδ_le hδg hδZ i)⟩
  rw [hXdef]
  clear hXdef
  refine le_trans ?_ hXjet
  unfold covariantJetNormSq
  exact Finset.single_le_sum
    (fun q _ => sq_nonneg ‖iteratedCovGrad (I := I) g 4 2 q X‖)
    (Finset.mem_range.mpr (Nat.lt_succ_self i))

theorem secondOrderCoefficient_jet_tower_quadratic
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (i : ℕ),
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kc, hKc_nn, htower⟩ := secondOrderCoefficient_jet_tower_sharp (I := I) (M := M) g g_bg
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ i
  refine (htower T hT hδ0 hδ_le hδg hδZ i).trans ?_
  have hsub : Finset.range (i + 1) ⊆ Finset.range (i + 2) := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  have hmono : ∑ j ∈ Finset.range (i + 1),
      ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
      ∑ j ∈ Finset.range (i + 2),
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left (by linarith only [hmono]) (hKc_nn i)

theorem secondOrderCoefficient_jet_tower
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ) {R₀ : ℝ} :
    ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g 4 2 i
              (lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderCoefficient‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) := by
  obtain ⟨Kc, hKc_nn, h⟩ := secondOrderCoefficient_jet_tower_quadratic (I := I) (M := M) g g_bg
  refine ⟨Kc, hKc_nn, ?_⟩
  intro T hT δ hδ0 hδ_le hδg hδZ _ i
  exact h T hT hδ0 hδ_le hδg hδZ i

theorem secondOrderAction_ladder_quadratic_background_affine
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower m *
                (1 + ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  obtain ⟨Kc, hKc_nn, htower⟩ := secondOrderCoefficient_jet_tower_quadratic (I := I) (M := M) g g_bg
  refine ⟨K, hK, ?_⟩
  intro δ hδ0 hδ_le
  have hεC_nn : (0 : ℝ) ≤ K * (δ / (1 - δ) ^ 2) :=
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _))
  obtain ⟨Cop, hCop_nn, hop⟩ :=
    operatorFieldApplication_cap_hs_affine_le (I := I) (M := M) g 3 (by omega)
      (K * (δ / (1 - δ) ^ 2)) hεC_nn Kc hKc_nn
  refine ⟨Cop, hCop_nn, ?_⟩
  intro T hT hδg hδZ m
  have hball : ‖smoothCcToTensorHs (I := I) (M := M) g (((3 : ℕ) : ℝ) + 2) T‖ ≤
      ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ := by
    exact le_of_eq (smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; norm_num) T)
  obtain ⟨A, hAdef, hc2pt, hc2jet⟩ :
      ∃ A : LowerScaleActionCoefficients g,
        lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤ (K * (δ / (1 - δ) ^ 2)) ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 4 2 i A.secondOrderCoefficient‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) :=
    ⟨lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      (hsplit T hT hδ_le hδ0 hδg hδZ).2,
      htower T hT hδ0 hδ_le hδg hδZ⟩
  rw [hAdef]
  clear hAdef
  have hshape : A.secondOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g (2 + 2) 2 A.secondOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  rw [hshape]
  exact le_trans (hop (norm_nonneg _) A.secondOrderCoefficient T hball hc2pt hc2jet m) (le_of_eq (by ring))

theorem secondOrderAction_ladder_quadratic_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨K, hK, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  obtain ⟨Kc, hKc_nn, htower⟩ := secondOrderCoefficient_jet_tower_quadratic (I := I) (M := M) g g_bg
  refine ⟨K, hK, ?_⟩
  intro δ hδ0 hδ_le
  have hεC_nn : (0 : ℝ) ≤ K * (δ / (1 - δ) ^ 2) :=
    mul_nonneg hK (div_nonneg hδ0 (sq_nonneg _))
  choose Cop hCop_nn hop using fun R : ℝ =>
    operatorFieldApplication_cap_hs_le (I := I) (M := M) g 3 (by omega) (abs_nonneg R)
      (K * (δ / (1 - δ) ^ 2)) hεC_nn Kc hKc_nn
  refine ⟨Cop, hCop_nn, ?_⟩
  intro T hT hδg hδZ R hR m
  have hball : ‖smoothCcToTensorHs (I := I) (M := M) g (((3 : ℕ) : ℝ) + 2) T‖ ≤ |R| := by
    refine le_trans (le_of_eq ?_) (le_trans hR (le_abs_self R))
    exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; norm_num) T
  obtain ⟨A, hAdef, hc2pt, hc2jet⟩ :
      ∃ A : LowerScaleActionCoefficients g,
        lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g 4 2 x
              (A.secondOrderCoefficient.toSection x) ≤ (K * (δ / (1 - δ) ^ 2)) ^ 2) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 4 2 i A.secondOrderCoefficient‖ ^ 2 ≤
              Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) :=
    ⟨lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      (hsplit T hT hδ_le hδ0 hδg hδZ).2,
      htower T hT hδ0 hδ_le hδg hδZ⟩
  rw [hAdef]
  clear hAdef
  have hshape : A.secondOrderAction (I := I) (M := M) T =
      operatorFieldApply (I := I) (M := M) g (2 + 2) 2 A.secondOrderCoefficient
        (iteratedCovGrad (I := I) g 0 2 2 T) := rfl
  rw [hshape]
  exact le_trans (hop R A.secondOrderCoefficient T hball hc2pt hc2jet m) (le_of_eq (by ring))

theorem secondOrderAction_ladder_quadratic
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  secondOrderAction_ladder_quadratic_background (I := I) (M := M) hDim g g

theorem secondOrderAction_ladder
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 3 ≤ a) {R₀ : ℝ} :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g₀ g₀ T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).secondOrderAction
                  (I := I) (M := M) T)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T‖ +
              Clower m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, hQ⟩ := secondOrderAction_ladder_quadratic (I := I) (M := M) hDim g₀
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C, hC_nn, hC⟩ := hQ hδ0 hδ_le
  refine ⟨fun m => C R₀ m, fun m => hC_nn R₀ m, ?_⟩
  intro T hT hδg hδZ hball m
  refine hC T hT hδg hδZ ?_ m
  refine le_trans (hsMono (I := I) (M := M) g₀ ?_ T) hball
  have h3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  linarith

private theorem coeffCap
    (g₀ : SmoothRiemannianMetric I M) (b a : ℕ)
    (ha : Module.finrank ℝ E / 2 ≤ a) {R₀ : ℝ}
    (Kc : ℕ → ℝ) (hKc_nn : ∀ i, 0 ≤ Kc i) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ (C : SmoothCcTensor g₀ b 2) (T₀ : SmoothCcTensor g₀ 0 2),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ ≤ R₀ →
        (∀ i : ℕ,
          ‖iteratedCovGrad (I := I) g₀ b 2 i C‖ ^ 2 ≤
            Kc i * (1 + ∑ j ∈ Finset.range (i + 2),
              ‖iteratedCovGrad (I := I) g₀ 0 2 j T₀‖ ^ 2)) →
        ∀ x : M,
          riemannianFiberNormSq (I := I) (M := M) g₀ b 2 x (C.toSection x) ≤
            Λ ^ 2 := by
  classical
  obtain ⟨Csh, hCsh_nn, hCsh⟩ :=
    exists_riemannianFiberNorm_le_iteratedCovGrad_l2_jetSum_supercritical
      (I := I) (M := M) g₀ b 2
  obtain ⟨C2, hC2_nn, hC2⟩ :=
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general
      (I := I) (M := M) g₀ (a + 2)
  have hW_nn : (0 : ℝ) ≤ Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
      Kc j * (1 + (C2 * R₀) ^ 2) := by
    refine mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => ?_))
    exact mul_nonneg (hKc_nn j) (by positivity)
  refine ⟨Real.sqrt (Csh ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
      Kc j * (1 + (C2 * R₀) ^ 2)), Real.sqrt_nonneg _, ?_⟩
  intro C T₀ hball henv x
  rw [Real.sq_sqrt hW_nn]
  refine le_trans (hCsh C x) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j hj => ?_)) (sq_nonneg _)
  have hjw : j < Module.finrank ℝ E / 2 + 2 := Finset.mem_range.mp hj
  refine le_trans (henv j) ?_
  refine mul_le_mul_of_nonneg_left ?_ (hKc_nn j)
  have hwin : ∑ l ∈ Finset.range (j + 2),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
      ∑ l ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun l hl => Finset.mem_range.mpr
        (by have := Finset.mem_range.mp hl; omega))
      (fun l _ _ => sq_nonneg _)
  have hball_sq : ∑ l ∈ Finset.range (a + 2 + 1),
      ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤ (C2 * R₀) ^ 2 := by
    have hnn : ∀ l ∈ Finset.range (a + 2 + 1),
        (0 : ℝ) ≤ ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ := fun l _ => norm_nonneg _
    have hsq_le : ∑ l ∈ Finset.range (a + 2 + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
        (∑ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖) ^ 2 := by
      have hstep : ∀ l ∈ Finset.range (a + 2 + 1),
          ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ ^ 2 ≤
            ‖iteratedCovGrad (I := I) g₀ 0 2 l T₀‖ *
              ∑ i ∈ Finset.range (a + 2 + 1),
                ‖iteratedCovGrad (I := I) g₀ 0 2 i T₀‖ := by
        intro l hl
        rw [sq]
        exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hnn hl) (norm_nonneg _)
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.sum_mul, sq]
    refine le_trans hsq_le ?_
    have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a + 2 : ℕ) : ℝ) T₀‖ =
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T₀‖ :=
      smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g₀
        (by push_cast; ring) T₀
    have hjets := hC2 T₀
    rw [hcast] at hjets
    exact pow_le_pow_left₀ (Finset.sum_nonneg hnn)
      (le_trans hjets (mul_le_mul_of_nonneg_left hball hC2_nn)) 2
  linarith only [hwin, hball_sq]

theorem firstOrderAction_ladder_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                  (I := I) (M := M) T)‖ ≤
            Clower m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨Kc0, hKc0_nn, htow0⟩ :=
    zeroOrderCoefficient_jet_tower_background (I := I) (M := M) hDim g g_bg a (by omega) hR₀
  obtain ⟨Kc1, hKc1_nn, htow1⟩ :=
    firstOrderCoefficient_jet_tower_background (I := I) (M := M) g g_bg a
  obtain ⟨Λ0, hΛ0_nn, hcap0⟩ :=
    coeffCap (I := I) (M := M) g 2 a (by omega) (R₀ := R₀) Kc0 hKc0_nn
  obtain ⟨Λ1, hΛ1_nn, hcap1⟩ :=
    coeffCap (I := I) (M := M) g 3 a (by omega) (R₀ := R₀) Kc1 hKc1_nn
  obtain ⟨Cm0, hCm0_nn, heng0⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g a (by omega) hR₀ Kc0 hKc0_nn Λ0 hΛ0_nn
  obtain ⟨Cm1, hCm1_nn, heng1⟩ :=
    exists_coeffAction_iteratedCovGrad_l2_coeffJetEnvelope_dataJetWindow_le
      (I := I) (M := M) g a (by omega) hR₀ Kc1 hKc1_nn Λ1 hΛ1_nn
  choose Chs hChs_nn hhs using fun n : ℕ =>
    exists_smoothCcToTensorHs_le_iteratedCovGrad_sum_general (I := I) (M := M) g n
  choose Cjet hCjet_nn hjet using fun n : ℕ =>
    exists_iteratedCovGrad_sum_le_smoothCcToTensorHs_general (I := I) (M := M) g n
  refine ⟨fun m => Chs m * (∑ q ∈ Finset.range (m + 1), (Cm0 q + Cm1 q)) *
      Cjet (m + 1),
    fun m => mul_nonneg (mul_nonneg (hChs_nn m)
      (Finset.sum_nonneg (fun q _ => add_nonneg (hCm0_nn q) (hCm1_nn q))))
      (hCjet_nn _), ?_⟩
  intro δ hδ0 hδ_le T hT hδg hδZ hball m
  obtain ⟨A, hAdef, hc0jet, hc1jet⟩ :
      ∃ A : LowerScaleActionCoefficients g,
        lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
            (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ = A ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 2 2 i A.zeroOrderCoefficient‖ ^ 2 ≤
              Kc0 i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) ∧
          (∀ i : ℕ,
            ‖iteratedCovGrad (I := I) g 3 2 i A.firstOrderCoefficient‖ ^ 2 ≤
              Kc1 i * (1 + ∑ j ∈ Finset.range (i + 2),
                ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)) :=
    ⟨lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
        (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ, rfl,
      htow0 T hT hδ0 hδ_le hδg hδZ hball,
      htow1 T hT hδ0 hδ_le hδg hδZ hball⟩
  rw [hAdef]
  clear hAdef
  have hq : ∀ q : ℕ,
      ‖iteratedCovGrad (I := I) g 0 2 q (A.firstOrderAction (I := I) (M := M) T)‖ ≤
        (Cm0 q + Cm1 q) * Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 2 i T‖ ^ 2) := by
    intro q
    have h0 := heng0 0 (by norm_num) A.zeroOrderCoefficient T hball
      (hcap0 A.zeroOrderCoefficient T hball hc0jet) hc0jet q
    have h1 := heng1 1 (by norm_num) A.firstOrderCoefficient T hball
      (hcap1 A.firstOrderCoefficient T hball hc1jet) hc1jet q
    have hsplitArm : A.firstOrderAction (I := I) (M := M) T =
        operatorFieldApply (I := I) (M := M) g 2 2 A.zeroOrderCoefficient T +
          operatorFieldApply (I := I) (M := M) g 3 2 A.firstOrderCoefficient
            (iteratedCovGrad (I := I) g 0 2 1 T) := rfl
    rw [hsplitArm, iteratedCovGrad_add, add_mul]
    exact le_trans (norm_add_le _ _) (add_le_add h0 h1)
  have hwin : ∀ q ∈ Finset.range (m + 1),
      Real.sqrt (∑ i ∈ Finset.range (q + 1 + 1),
          ‖iteratedCovGrad (I := I) g 0 2 i T‖ ^ 2) ≤
        Cjet (m + 1) * ‖smoothCcToTensorHs (I := I) (M := M) g
          ((m + 1 : ℕ) : ℝ) T‖ := by
    intro q hq'
    have hqm : q ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq')
    refine le_trans (sqrt_finset_sum_sq_le_sum _ _ (fun i _ => norm_nonneg _)) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr
        (by have := Finset.mem_range.mp hi; omega))
      (fun i _ _ => norm_nonneg _)) (hjet (m + 1) T)
  refine le_trans (hhs m (A.firstOrderAction (I := I) (M := M) T)) ?_
  have hsum : ∑ q ∈ Finset.range (m + 1),
      ‖iteratedCovGrad (I := I) g 0 2 q (A.firstOrderAction (I := I) (M := M) T)‖ ≤
      (∑ q ∈ Finset.range (m + 1), (Cm0 q + Cm1 q)) *
        (Cjet (m + 1) * ‖smoothCcToTensorHs (I := I) (M := M) g
          ((m + 1 : ℕ) : ℝ) T‖) := by
    refine le_trans (Finset.sum_le_sum (fun q hq' =>
      le_trans (hq q) (mul_le_mul_of_nonneg_left (hwin q hq')
        (add_nonneg (hCm0_nn q) (hCm1_nn q))))) (le_of_eq ?_)
    rw [Finset.sum_mul]
  have hcast : ‖smoothCcToTensorHs (I := I) (M := M) g ((m + 1 : ℕ) : ℝ) T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
    smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
      (by push_cast; ring) T
  rw [← hcast]
  refine le_trans (mul_le_mul_of_nonneg_left hsum (hChs_nn m)) (le_of_eq (by ring))

theorem firstOrderAction_ladder
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 2 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                  (I := I) (M := M) T)‖ ≤
            Clower m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  firstOrderAction_ladder_background (I := I) (M := M) hDim g g a ha hR₀

theorem firstOrderAction_ladder_quadratic_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (_hR : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g_bg T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                  (I := I) (M := M) T)‖ ≤
            Clower R m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  choose C hC_nn hC using fun R : ℝ =>
    firstOrderAction_ladder_background (I := I) (M := M) hDim g g_bg 2 le_rfl
      (R₀ := |R|) (abs_nonneg R)
  refine ⟨C, hC_nn, ?_⟩
  intro δ hδ0 hδ_le T hT hδg hδZ R hR m
  refine hC R hδ0 hδ_le T hT hδg hδZ ?_ m
  refine le_trans (le_of_eq ?_) (le_trans hR (le_abs_self R))
  exact smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g
    (by push_cast; norm_num) T

theorem firstOrderAction_ladder_quadratic
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
        (T : SmoothCcTensor g 0 2)
        (_hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (_hR : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              ((lowerScaleActionCoefficients (I := I) (M := M) g g T
                (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ).firstOrderAction
                  (I := I) (M := M) T)‖ ≤
            Clower R m *
              ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  firstOrderAction_ladder_quadratic_background (I := I) (M := M) hDim g g

theorem n_diff_hm_rung
    (hDim : Module.finrank ℝ E = 3)
    (g₀ : SmoothRiemannianMetric I M) (a : ℕ)
    (ha : 3 ≤ a) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℕ → ℝ, (∀ m, 0 ≤ Clower m) ∧
      ∀ (T : SmoothCcTensor g₀ 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g₀ T x u v =
            ccTensorBilin (I := I) g₀ T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀
            (0 : SmoothCcTensor g₀ 0 2)) δ),
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T‖ ≤ R₀ →
        ∀ m : ℕ,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (m : ℝ)
              (deTurckSmoothRemainder (I := I) g₀ g₀ T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g₀ g₀
                  (0 : SmoothCcTensor g₀ 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 2) T‖ +
              Clower m *
                ‖smoothCcToTensorHs (I := I) (M := M) g₀ ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, h2⟩ := secondOrderAction_ladder (I := I) (M := M) hDim g₀ a ha
  obtain ⟨C1low, hC1low_nn, h1⟩ :=
    firstOrderAction_ladder (I := I) (M := M) hDim g₀ a (by omega) hR₀
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g₀ g₀
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C2low, hC2low_nn, h2δ⟩ := h2 hδ0 hδ_le
  refine ⟨fun m => C2low m + C1low m,
    fun m => add_nonneg (hC2low_nn m) (hC1low_nn m), ?_⟩
  intro T hT hδg hδZ hball m
  rw [(hsplit T hT hδ_le hδ0 hδg hδZ).1, smoothCcToTensorHs_add]
  refine le_trans (norm_add_le _ _) ?_
  exact le_trans
    (add_le_add (h2δ T hT hδg hδZ hball m)
      (h1 hδ0 hδ_le T hT hδg hδZ hball m))
    (le_of_eq (by ring))

theorem exists_deTurckRemainder_allOrder_ladder_bound_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g_bg
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ := by
  classical
  obtain ⟨κ, hκ, h2⟩ := secondOrderAction_ladder_quadratic_background (I := I) (M := M) hDim g g_bg
  obtain ⟨C1low, hC1low_nn, h1⟩ := firstOrderAction_ladder_quadratic_background (I := I) (M := M) hDim g g_bg
  obtain ⟨_, _, hsplit⟩ := lowData_split (I := I) (M := M) g g_bg
  refine ⟨κ, hκ, ?_⟩
  intro δ hδ0 hδ_le
  obtain ⟨C2low, hC2low_nn, h2δ⟩ := h2 hδ0 hδ_le
  refine ⟨fun R m => C2low R m + C1low R m,
    fun R m => add_nonneg (hC2low_nn R m) (hC1low_nn R m), ?_⟩
  intro T hT hδg hδZ R hR m
  have hR4 : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R :=
    le_trans (hsMono (I := I) (M := M) g (by norm_num) T) hR
  rw [(hsplit T hT hδ_le hδ0 hδg hδZ).1, smoothCcToTensorHs_add]
  refine le_trans (norm_add_le _ _) ?_
  exact le_trans
    (add_le_add (h2δ T hT hδg hδZ hR m)
      (h1 hδ0 hδ_le T hT hδg hδZ hR4 m))
    (le_of_eq (by ring))

theorem exists_deTurckRemainder_allOrder_ladder_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, 0 ≤ κ ∧
      ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g ((m : ℝ) + 1) T‖ :=
  exists_deTurckRemainder_allOrder_ladder_bound_background (I := I) (M := M) hDim g g

def HasDeTurckRemainderAllOrderLadderBoundBackground (g g_bg : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  0 ≤ κ ∧
    ∀ {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3),
      ∃ Clower : ℝ → ℕ → ℝ, (∀ R m, 0 ≤ Clower R m) ∧
      ∀ (T : SmoothCcTensor g 0 2)
        (hT : ∀ (x : M) (u v : TangentSpace I x),
          ccTensorBilin (I := I) g T x u v =
            ccTensorBilin (I := I) g T x v u)
        (hδg : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g T) δ)
        (hδZ : gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g
            (0 : SmoothCcTensor g 0 2)) δ)
        {R : ℝ}
        (hR : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤ R)
        (m : ℕ),
          ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
              (deTurckSmoothRemainder (I := I) g g_bg T
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδg -
                deTurckSmoothRemainder (I := I) g g_bg
                  (0 : SmoothCcTensor g 0 2)
                  (lt_of_le_of_lt hδ_le (by norm_num)) hδZ)‖ ≤
            κ * (δ / (1 - δ) ^ 2) *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  ((m : ℝ) + 2) T‖ +
              Clower R m *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  ((m : ℝ) + 1) T‖

def HasDeTurckRemainderAllOrderLadderBound (g : SmoothRiemannianMetric I M) (κ : ℝ) : Prop :=
  HasDeTurckRemainderAllOrderLadderBoundBackground (I := I) (M := M) g g κ

theorem exists_deTurck_remainder_all_order_ladder_bound_parameters_background
    (hDim : Module.finrank ℝ E = 3)
    (g g_bg : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, HasDeTurckRemainderAllOrderLadderBoundBackground (I := I) (M := M) g g_bg κ := by
  obtain ⟨κ, hκ, hord⟩ := exists_deTurckRemainder_allOrder_ladder_bound_background (I := I) (M := M) hDim g g_bg
  exact ⟨κ, hκ, hord⟩

theorem exists_deTurck_remainder_all_order_ladder_bound_parameters
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ κ : ℝ, HasDeTurckRemainderAllOrderLadderBound (I := I) (M := M) g κ := by
  simpa only [HasDeTurckRemainderAllOrderLadderBound] using
    (exists_deTurck_remainder_all_order_ladder_bound_parameters_background (I := I) (M := M) hDim g g)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
