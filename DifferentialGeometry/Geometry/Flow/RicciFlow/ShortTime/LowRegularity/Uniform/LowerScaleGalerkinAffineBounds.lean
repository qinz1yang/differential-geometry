import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Background.GalerkinForcingTerms
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.LowerScaleSecondOrderAffineBounds

set_option autoImplicit false

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
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral hiding TensorEigenIdx
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem exists_uniform_galerkin_action_all_order_affine_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      ∀ {δ : ℝ} (hδ_le : δ ≤ 1 / 3) (hδ0 : 0 ≤ δ)
        {R : ℝ} (hR0 : 0 ≤ R) (hRρ : R ≤ ρ)
        (g : SmoothRiemannianMetric I M)
        (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ)
        (hjet : ∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ)
        (hreal : ∀ T : SmoothCcTensor g 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g T) δ),
        ∃ Ca2 : ℕ → ℝ, ∃ Ca1 : ℝ → ℕ → ℝ,
          (∀ m, 0 ≤ Ca2 m) ∧ (∀ R4 m, 0 ≤ Ca1 R4 m) ∧
          ∀ (F : Finset (TensorEigenIdx (I := I) (M := M) g 0 2))
            (c : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ)
            {R4 : ℝ},
            Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i 4 * (c i) ^ 2) ≤ R4 →
            ∀ m : ℕ,
              Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
                  ((galerkinActionVectorBackground (I := I) (M := M) g gBase hR0
                    (lt_of_le_of_lt hδ_le (by norm_num))
                    hreal F c).coeff i) ^ 2) ≤
                K * (δ / (1 - δ) ^ 2 + R) *
                    Real.sqrt (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 2) *
                        (c i) ^ 2) +
                  (Ca1 R4 m + Ca2 m *
                      (1 + Real.sqrt (∑ i ∈ F,
                        tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2))) *
                    Real.sqrt (∑ i ∈ F,
                      tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                        (c i) ^ 2) := by
  classical
  obtain ⟨ρ, K, hρ, hK, ha2⟩ :=
    secondOrderAction_ladder_affine_uniform (I := I) (M := M) hDim gBase hΛ
  refine ⟨ρ, K, hρ, hK, ?_⟩
  intro δ hδ_le hδ0 R hR0 hRρ g hEq hjet hreal
  obtain ⟨Ca2, hCa2, ha2g⟩ := ha2 hδ_le hδ0 hR0 hRρ g hEq hjet
  obtain ⟨Ca1, hCa1, ha1g⟩ := firstOrderAction_ladder_quadratic_background (I := I) (M := M) hDim g gBase
  refine ⟨Ca2, Ca1, hCa2, hCa1, ?_⟩
  intro F c R4 hE4 m
  let T : SmoothCcTensor g 0 2 :=
    symmS (I := I) (M := M) g (galCoreRep (I := I) (M := M) g R F c)
  have hT : ∀ (x : M) (u v : TangentSpace I x),
      ccTensorBilin (I := I) g T x u v =
        ccTensorBilin (I := I) g T x v u := by
    dsimp only [T]
    exact ccTensorBilin_symmS_symm (I := I) (M := M) g _
  have hδg : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ := by
    dsimp only [T]
    exact galRepFib (I := I) (M := M) g hR0 hreal F c
  have hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ :=
    zeroMetricPerturbation_fibre_bound (I := I) (M := M) g hR0 hreal
  have hT2 : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R := by
    rw [norm_ccHs_eq_smoothHs]
    calc
      ‖smoothCcToTensorHs (I := I) (M := M) g 2 T‖ =
          ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ :=
        smoothCcToTensorHs_norm_order_congr (I := I) (M := M) g (by norm_num) T
      _ ≤ R := by
        simpa only [T] using symm_h2_of_state (I := I) (M := M) g
          (galCoreRep (I := I) (M := M) g R F c)
          (galCoreRep_ball (I := I) (M := M) g hR0 F c)
  have hT4 : ‖smoothCcToTensorHs (I := I) (M := M) g (4 : ℝ) T‖ ≤ R4 := by
    exact (galRepHs_le (I := I) (M := M) g 4 hR0 F c).trans hE4
  have hT5 : ‖smoothCcToTensorHs (I := I) (M := M) g (5 : ℝ) T‖ ≤
      Real.sqrt (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2) :=
    galRepHs_le (I := I) (M := M) g 5 hR0 F c
  have h2 := ha2g T hT hδg hδZ hT2 m
  have h1 := ha1g hδ0 hδ_le T hT hδg hδZ hT4 m
  have htop := galRepHs_le (I := I) (M := M) g ((m : ℝ) + 2) hR0 F c
  have hmid := galRepHs_le (I := I) (M := M) g ((m : ℝ) + 1) hR0 F c
  let A := lowerScaleActionCoefficients (I := I) (M := M) g gBase T
    (lt_of_le_of_lt hδ_le (by norm_num)) hδg hδZ
  have harms : ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
      (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T)‖ ≤
      K * (δ / (1 - δ) ^ 2 + R) *
          Real.sqrt (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 2) * (c i) ^ 2) +
        (Ca1 R4 m + Ca2 m *
            (1 + Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2))) *
          Real.sqrt (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
              (c i) ^ 2) := by
    have htri := norm_add_le
      (smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
        (A.secondOrderAction (I := I) (M := M) T))
      (smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
        (A.firstOrderAction (I := I) (M := M) T))
    rw [← smoothCcToTensorHs_add] at htri
    dsimp only [A] at htri h2 h1
    have h2' := h2.trans (add_le_add
      (mul_le_mul_of_nonneg_left htop
        (mul_nonneg hK (add_nonneg (div_nonneg hδ0 (sq_nonneg _)) hR0)))
      (mul_le_mul_of_nonneg_left hmid
        (mul_nonneg (hCa2 m) (by positivity))))
    have h1' := h1.trans (mul_le_mul_of_nonneg_left hmid (hCa1 R4 m))
    have h5mul : Ca2 m * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g 5 T‖) ≤
        Ca2 m * (1 + Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hT5) (hCa2 m)
    have h5mid := mul_le_mul_of_nonneg_right h5mul
      (Real.sqrt_nonneg (∑ i ∈ F,
        tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) * (c i) ^ 2))
    have hlower :
        Ca2 m * (1 + ‖smoothCcToTensorHs (I := I) (M := M) g 5 T‖) *
            Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) * (c i) ^ 2) +
          Ca1 R4 m * Real.sqrt (∑ i ∈ F,
            tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) * (c i) ^ 2) ≤
        (Ca1 R4 m + Ca2 m * (1 + Real.sqrt (∑ i ∈ F,
          tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2))) *
            Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                (c i) ^ 2) := by
      calc
        _ ≤ Ca2 m * (1 + Real.sqrt (∑ i ∈ F,
              tensorSobolevWeight (I := I) (M := M) i 5 * (c i) ^ 2)) *
                Real.sqrt (∑ i ∈ F,
                  tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                    (c i) ^ 2) +
              Ca1 R4 m * Real.sqrt (∑ i ∈ F,
                tensorSobolevWeight (I := I) (M := M) i ((m : ℝ) + 1) *
                  (c i) ^ 2) := add_le_add h5mid le_rfl
        _ = _ := by ring
    linarith [htri, h2', h1', hlower]
  have hmass := cc_partial_le_norm (I := I) (M := M) g 2 (m : ℝ)
    (A.secondOrderAction (I := I) (M := M) T + A.firstOrderAction (I := I) (M := M) T) F
  have hpartial :
      Real.sqrt (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i (m : ℝ) *
          ((smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
            (A.secondOrderAction (I := I) (M := M) T +
              A.firstOrderAction (I := I) (M := M) T)).coeff i) ^ 2) ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T)‖ := by
    exact (Real.sqrt_le_sqrt hmass).trans
      (le_of_eq (Real.sqrt_sq (norm_nonneg _)))
  have hgal (i : TensorEigenIdx (I := I) (M := M) g 0 2) :
      (galerkinActionVectorBackground (I := I) (M := M) g gBase hR0
          (lt_of_le_of_lt hδ_le (by norm_num)) hreal F c).coeff i =
        (smoothCcToTensorHs (I := I) (M := M) g (m : ℝ)
          (A.secondOrderAction (I := I) (M := M) T +
            A.firstOrderAction (I := I) (M := M) T)).coeff i := by
    simp only [galerkinActionVectorBackground, smoothCcToTensorHs_coeff, A, T]
  simp_rw [hgal]
  exact hpartial.trans harms

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
