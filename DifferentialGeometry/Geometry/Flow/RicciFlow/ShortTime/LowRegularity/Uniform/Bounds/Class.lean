import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Solution.Dense

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Spectral

def lowRegularityOuterRadius (Ctop ρ P : ℝ) : ℝ :=
  min (ρ / 2) (min (P / 2) (1 / (32 * (Ctop + 1))))

def lowRegularityStateRadius (Ctop B1 ρ P : ℝ) : ℝ :=
  min (lowRegularityOuterRadius Ctop ρ P / 2) (1 / (32 * (B1 + 1)))

def lowRegularityTimeHorizon (Ctop B0 B1 D ρ P : ℝ) : ℝ :=
  min 1 (min (1 / (64 * (B0 + 1) ^ 2))
    ((lowRegularityStateRadius Ctop B1 ρ P / 4 / (2 * (D + 1))) ^ 2))

theorem lowRegularityOuterRadius_le_rho {Ctop ρ P : ℝ} :
    lowRegularityOuterRadius Ctop ρ P ≤ ρ / 2 :=
  min_le_left _ _

theorem lowRegularityOuterRadius_le_P {Ctop ρ P : ℝ} :
    lowRegularityOuterRadius Ctop ρ P ≤ P / 2 :=
  le_trans (min_le_right _ _) (min_le_left _ _)

theorem lowRegularityOuterRadius_le_cap {Ctop ρ P : ℝ} :
    lowRegularityOuterRadius Ctop ρ P ≤ 1 / (32 * (Ctop + 1)) :=
  le_trans (min_le_right _ _) (min_le_right _ _)

theorem lowRegularityOuterRadius_pos {Ctop ρ P : ℝ} (hCtop : 0 ≤ Ctop) (hρ : 0 < ρ)
    (hP : 0 < P) : 0 < lowRegularityOuterRadius Ctop ρ P := by
  refine lt_min (by linarith) (lt_min (by linarith) ?_)
  exact one_div_pos.mpr (by linarith)

theorem lowRegularityOuterRadius_small {Ctop ρ P : ℝ} (hCtop : 0 ≤ Ctop) :
    Ctop * lowRegularityOuterRadius Ctop ρ P ≤ 1 / 16 := by
  have hCtop1 : (0 : ℝ) < Ctop + 1 := by linarith
  calc
    Ctop * lowRegularityOuterRadius Ctop ρ P ≤ Ctop * (1 / (32 * (Ctop + 1))) :=
      mul_le_mul_of_nonneg_left lowRegularityOuterRadius_le_cap hCtop
    _ ≤ (Ctop + 1) * (1 / (32 * (Ctop + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 32 := by field_simp
    _ ≤ 1 / 16 := by norm_num

theorem lowRegularityStateRadius_le_Q {Ctop B1 ρ P : ℝ} :
    lowRegularityStateRadius Ctop B1 ρ P ≤ lowRegularityOuterRadius Ctop ρ P / 2 :=
  min_le_left _ _

theorem lowRegularityStateRadius_le_cap {Ctop B1 ρ P : ℝ} :
    lowRegularityStateRadius Ctop B1 ρ P ≤ 1 / (32 * (B1 + 1)) :=
  min_le_right _ _

theorem lowRegularityStateRadius_pos {Ctop B1 ρ P : ℝ} (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1)
    (hρ : 0 < ρ) (hP : 0 < P) : 0 < lowRegularityStateRadius Ctop B1 ρ P := by
  have hQ : 0 < lowRegularityOuterRadius Ctop ρ P := lowRegularityOuterRadius_pos hCtop hρ hP
  refine lt_min (by linarith) ?_
  exact one_div_pos.mpr (by linarith)

theorem lowRegularityStateRadius_le_P {Ctop B1 ρ P : ℝ} (hP : 0 ≤ P) :
    lowRegularityStateRadius Ctop B1 ρ P ≤ P := by
  have h1 : lowRegularityStateRadius Ctop B1 ρ P ≤ lowRegularityOuterRadius Ctop ρ P / 2 :=
    lowRegularityStateRadius_le_Q
  have h2 : lowRegularityOuterRadius Ctop ρ P ≤ P / 2 := lowRegularityOuterRadius_le_P
  linarith

theorem lowRegularityStateRadius_le_quarter_realization_radius {Ctop B1 ρ P : ℝ} :
    lowRegularityStateRadius Ctop B1 ρ P ≤ P / 4 := by
  have h1 : lowRegularityStateRadius Ctop B1 ρ P ≤ lowRegularityOuterRadius Ctop ρ P / 2 :=
    lowRegularityStateRadius_le_Q
  have h2 : lowRegularityOuterRadius Ctop ρ P ≤ P / 2 := lowRegularityOuterRadius_le_P
  linarith

theorem lowRegularityStateRadius_small {Ctop B1 ρ P : ℝ} (hB1 : 0 ≤ B1) :
    B1 * lowRegularityStateRadius Ctop B1 ρ P ≤ 1 / 16 := by
  have hB11 : (0 : ℝ) < B1 + 1 := by linarith
  calc
    B1 * lowRegularityStateRadius Ctop B1 ρ P ≤ B1 * (1 / (32 * (B1 + 1))) :=
      mul_le_mul_of_nonneg_left lowRegularityStateRadius_le_cap hB1
    _ ≤ (B1 + 1) * (1 / (32 * (B1 + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 1 / 32 := by field_simp
    _ ≤ 1 / 16 := by norm_num

theorem lowRegularityTimeHorizon_le_one {Ctop B0 B1 D ρ P : ℝ} :
    lowRegularityTimeHorizon Ctop B0 B1 D ρ P ≤ 1 :=
  min_le_left _ _

theorem lowRegularityTimeHorizon_pos {Ctop B0 B1 D ρ P : ℝ} (hCtop : 0 ≤ Ctop)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D) (hρ : 0 < ρ) (hP : 0 < P) :
    0 < lowRegularityTimeHorizon Ctop B0 B1 D ρ P := by
  have hB01 : (0 : ℝ) < B0 + 1 := by linarith
  have hR : 0 < lowRegularityStateRadius Ctop B1 ρ P := lowRegularityStateRadius_pos hCtop hB1 hρ hP
  refine lt_min one_pos (lt_min ?_ ?_)
  · exact one_div_pos.mpr (mul_pos (by norm_num) (pow_pos hB01 2))
  · exact pow_pos (div_pos (by linarith) (by linarith)) 2

theorem lowRegularityOuterRadius_mono {Ctop Ctop' ρ ρ' P P' : ℝ} (hCtop : 0 ≤ Ctop)
    (hC : Ctop ≤ Ctop') (hρ : ρ' ≤ ρ) (hP : P' ≤ P) :
    lowRegularityOuterRadius Ctop' ρ' P' ≤ lowRegularityOuterRadius Ctop ρ P := by
  refine min_le_min (by linarith) (min_le_min (by linarith) ?_)
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem lowRegularityStateRadius_mono {Ctop Ctop' B1 B1' ρ ρ' P P' : ℝ} (hCtop : 0 ≤ Ctop)
    (hB1 : 0 ≤ B1) (hC : Ctop ≤ Ctop') (hB : B1 ≤ B1') (hρ : ρ' ≤ ρ)
    (hP : P' ≤ P) :
    lowRegularityStateRadius Ctop' B1' ρ' P' ≤ lowRegularityStateRadius Ctop B1 ρ P := by
  have hQ := lowRegularityOuterRadius_mono hCtop hC hρ hP
  refine min_le_min (by linarith) ?_
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem lowRegularityTimeHorizon_mono {Ctop Ctop' B0 B0' B1 B1' D D' ρ ρ' P P' : ℝ}
    (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hD : 0 ≤ D)
    (hRnn : 0 ≤ lowRegularityStateRadius Ctop' B1' ρ' P')
    (hC : Ctop ≤ Ctop') (hB0' : B0 ≤ B0') (hB1' : B1 ≤ B1') (hD' : D ≤ D')
    (hρ : ρ' ≤ ρ) (hP : P' ≤ P) :
    lowRegularityTimeHorizon Ctop' B0' B1' D' ρ' P' ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P := by
  have hR := lowRegularityStateRadius_mono hCtop hB1 hC hB1' hρ hP
  refine min_le_min le_rfl (min_le_min ?_ ?_)
  · refine one_div_le_one_div_of_le ?_ ?_
    · nlinarith [sq_nonneg B0]
    · nlinarith [sq_nonneg B0, sq_nonneg B0']
  · have hq : lowRegularityStateRadius Ctop' B1' ρ' P' / 4 / (2 * (D' + 1)) ≤
        lowRegularityStateRadius Ctop B1 ρ P / 4 / (2 * (D + 1)) := by
      rw [div_eq_mul_one_div (lowRegularityStateRadius Ctop' B1' ρ' P' / 4),
        div_eq_mul_one_div (lowRegularityStateRadius Ctop B1 ρ P / 4)]
      refine mul_le_mul (by linarith)
        (one_div_le_one_div_of_le (by linarith) (by linarith)) ?_ (by linarith)
      exact (one_div_pos.mpr (by linarith)).le
    have hnn : 0 ≤ lowRegularityStateRadius Ctop' B1' ρ' P' / 4 / (2 * (D' + 1)) :=
      div_nonneg (by linarith) (by linarith)
    rw [pow_two, pow_two]
    exact mul_le_mul hq hq hnn (by linarith)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

theorem lowRegularityMetricRealization (g₀ : SmoothRiemannianMetric I M) {δ Ctop B1 ρ P : ℝ}
    (hP : 0 ≤ P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤
          lowRegularityStateRadius Ctop B1 ρ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ :=
  realizeOfLE (I := I) (M := M) g₀ (lowRegularityStateRadius_le_P hP) hreal

theorem realize_h2_bound (g₀ : SmoothRiemannianMetric I M) {δ P : ℝ}
    (hP : 0 < P) (hδ : δ ≤ 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ C : ℝ, 0 < C ∧
      (∀ T : SmoothCcTensor g₀ 0 2,
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T)
          (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀
            (((1 : ℕ) : ℝ) + 1) T‖)) ∧
      P / 4 ≤ 1 / (2 * C) := by
  let C : ℝ := 1 / P
  refine ⟨C, one_div_pos.mpr hP, ?_, ?_⟩
  · intro T
    let n : ℝ := ‖smoothCcToTensorHs (I := I) (M := M) g₀
      (((1 : ℕ) : ℝ) + 1) T‖
    by_cases hn : n = 0
    · have hTemb : smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 1) T = 0 := norm_eq_zero.mp hn
      have hzero : smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 1) (0 : SmoothCcTensor g₀ 0 2) = 0 := by
        simpa only [zero_smul] using
          (smoothCcToTensorHs_smul (I := I) (M := M) g₀
            (((1 : ℕ) : ℝ) + 1) (0 : ℝ) (0 : SmoothCcTensor g₀ 0 2))
      have hT0 : T = 0 :=
        smoothHs_inj (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
          (hTemb.trans hzero.symm)
      subst T
      simpa only [C, hzero, norm_zero, mul_zero] using
        gFibreOpBound_ccTensorBilinSymm_zero (I := I) (M := M) g₀
    · have hnpos : 0 < n := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
      let T₀ : SmoothCcTensor g₀ 0 2 := (P / n) • T
      have hT₀norm : ‖smoothCcToTensorHs (I := I) (M := M) g₀
          (((1 : ℕ) : ℝ) + 1) T₀‖ = P := by
        dsimp only [T₀]
        rw [smoothCcToTensorHs_smul, tensorHs_norm_smul,
          abs_of_pos (div_pos hP hnpos)]
        exact div_mul_cancel₀ P hn
      have hb₀ := hreal T₀ hT₀norm.le
      have hb := gFibreOpBound_ccTensorBilinSymm_smul
        (I := I) (M := M) g₀ (n / P) T₀ hb₀
      have hback : (n / P) • T₀ = T := by
        dsimp only [T₀]
        rw [smul_smul]
        have hscalar : n / P * (P / n) = 1 := by
          field_simp [ne_of_gt hP, ne_of_gt hnpos]
        rw [hscalar, one_smul]
      rw [hback] at hb
      have hquot : 0 ≤ n / P := (div_pos hnpos hP).le
      have hcoeff : |n / P| * δ ≤ C * n := by
        rw [abs_of_pos (div_pos hnpos hP)]
        calc
          n / P * δ ≤ n / P * 1 := mul_le_mul_of_nonneg_left hδ hquot
          _ = C * n := by simp only [C]; ring
      intro x v w
      refine le_trans (hb x v w) ?_
      have hnn : 0 ≤ Real.sqrt (g₀.inner x v v) *
          Real.sqrt (g₀.inner x w w) :=
        mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc
        (|n / P| * δ) * Real.sqrt (g₀.inner x v v) *
            Real.sqrt (g₀.inner x w w) =
            (|n / P| * δ) * (Real.sqrt (g₀.inner x v v) *
              Real.sqrt (g₀.inner x w w)) := by ring
        _ ≤ (C * n) * (Real.sqrt (g₀.inner x v v) *
              Real.sqrt (g₀.inner x w w)) :=
          mul_le_mul_of_nonneg_right hcoeff hnn
        _ = (C * ‖smoothCcToTensorHs (I := I) (M := M) g₀
              (((1 : ℕ) : ℝ) + 1) T‖) *
              Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
          simp only [n]
          ring
  · have hrecip : 1 / (2 * (1 / P)) = P / 2 := by
      field_simp [ne_of_gt hP]
    simp only [C, hrecip]
    linarith

def boundedDeTurckRemainderOnLowerState (g₀ g_bg : SmoothRiemannianMetric I M) {δ Ctop B1 ρ P : ℝ}
    (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    lowerState (I := I) (M := M) g₀ 1 (lowRegularityStateRadius Ctop B1 ρ P) →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  deTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg (lowRegularityStateRadius_pos hCtop hB1 hρ hP) hδ
    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      hP.le hreal)

theorem exists_lowRegularity_solution_of_remainder_bounds (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ)
    (hcont : Continuous
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hzero : ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ D) :
    ∀ {T : ℝ} (hT : 0 < T)
      (_hTτ : T ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
        (gforce : timeL2
          (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
        let field := maximalRegularityDuhamelSolutionField (I := I) (M := M)
          ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce
        u = maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce ∧
          (∀ᵐ t ∂(timeMeasure T),
            field t ∈ lowerState (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius Ctop B1 ρ P)) ∧
          gforce =ᵐ[timeMeasure T]
            (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP
              hreal (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
                (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le) field t)) ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ) field + gforce ∧
          ‖gforce‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 := by
  intro T hT hTτ
  have hRpos : 0 < lowRegularityStateRadius Ctop B1 ρ P :=
    lowRegularityStateRadius_pos hCtop hB1 hρ hP
  have hQnn : 0 ≤ lowRegularityOuterRadius Ctop ρ P :=
    (lowRegularityOuterRadius_pos hCtop hρ hP).le
  let A : ℝ≥0 :=
    Real.toNNReal (Ctop * lowRegularityOuterRadius Ctop ρ P / lowRegularityStateRadius Ctop B1 ρ P)
  let B : ℝ≥0 := Real.toNNReal B0
  let C : ℝ≥0 := Real.toNNReal B1
  have hAarg : 0 ≤
      Ctop * lowRegularityOuterRadius Ctop ρ P / lowRegularityStateRadius Ctop B1 ρ P :=
    div_nonneg (mul_nonneg hCtop hQnn) hRpos.le
  have hAcoe : (A : ℝ) =
      Ctop * lowRegularityOuterRadius Ctop ρ P / lowRegularityStateRadius Ctop B1 ρ P :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = B0 := Real.coe_toNNReal _ hB0
  have hCcoe : (C : ℝ) = B1 := Real.coe_toNNReal _ hB1
  have hAR : (A : ℝ) * lowRegularityStateRadius Ctop B1 ρ P =
      Ctop * lowRegularityOuterRadius Ctop ρ P := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hRpos.ne'
  have hsmallA : (A : ℝ) * lowRegularityStateRadius Ctop B1 ρ P ≤ 1 / 16 := by
    rw [hAR]
    exact lowRegularityOuterRadius_small hCtop
  have hsmallC : (C : ℝ) * lowRegularityStateRadius Ctop B1 ρ P ≤ 1 / 16 := by
    rw [hCcoe]
    exact lowRegularityStateRadius_small hB1
  have hsingle : ∀ u v : lowerState (I := I) (M := M) g₀ 1
      (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
        (A : ℝ) * lowRegularityStateRadius Ctop B1 ρ P *
            ‖(u : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - (v : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (v : _))‖ +
          (C : ℝ) *
              (‖(u : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u : _) - (v : _))‖ := by
    intro u v
    rw [hAR, hBcoe, hCcoe]
    exact htame u v
  have hDnn : 0 ≤ D := le_trans (norm_nonneg _) hzero
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    partial_solution_tame (I := I) (M := M) g₀ 1 hRpos
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal) hcont
      A B C D hDnn hzero hsmallA hsmallC hsingle
  have hτ : lowRegularityTimeHorizon Ctop B0 B1 D ρ P = T₀ := by
    rw [hT₀eq, hBcoe]
    rfl
  have hTT₀ : T ≤ T₀ := hTτ.trans hτ.le
  simpa only [Nat.cast_one] using hsol hT hTT₀

structure IsLowRegularitySolutionAt (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (Rcap : ℝ) : Prop where
  threshold_lt_one : δ < 1
  top_nonneg : 0 ≤ Ctop
  slope_nonneg : 0 ≤ B1
  outer_pos : 0 < ρ
  realize_pos : 0 < P
  metric_realization : ∀ S : SmoothCcTensor g₀ 0 2,
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ S) δ
  threshold_nonneg : 0 ≤ δ
  threshold_le_third : δ ≤ 1 / 3
  smoothCore_continuous : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ threshold_lt_one
    (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
      realize_pos.le metric_realization))
  base_nonneg : 0 ≤ B0
  remainder_continuous : Continuous
    (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ threshold_lt_one top_nonneg slope_nonneg outer_pos realize_pos metric_realization)
  remainder_lipschitz : ∀ u v : lowerState (I := I) (M := M) g₀ 1
      (lowRegularityStateRadius Ctop B1 ρ P),
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ threshold_lt_one top_nonneg slope_nonneg outer_pos realize_pos metric_realization u -
        boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ threshold_lt_one top_nonneg slope_nonneg outer_pos realize_pos metric_realization v‖ ≤
      Ctop * lowRegularityOuterRadius Ctop ρ P *
          ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
        B0 *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
        B1 *
            (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖
  remainder_zero_bound : ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ threshold_lt_one top_nonneg slope_nonneg outer_pos realize_pos metric_realization
      ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos top_nonneg slope_nonneg outer_pos realize_pos).le⟩‖ ≤ D
  time_le_horizon : T ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P
  forcing_norm_le_quarter_radius : ‖fLo‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4
  forcing_ae_eq_remainder : fLo =ᵐ[timeMeasure T]
    (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ threshold_lt_one top_nonneg slope_nonneg outer_pos realize_pos metric_realization
      (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos top_nonneg slope_nonneg outer_pos realize_pos).le)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
          fLo) t))
  stateRadius_le : lowRegularityStateRadius Ctop B1 ρ P ≤ Rcap

def IsLowRegularitySolution (g₀ : SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T) : Prop :=
  ∃ (δ Ctop B0 B1 D ρ P : ℝ) (hδ : δ < 1)
    (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ),
    0 ≤ δ ∧ δ ≤ 1 / 3 ∧
      Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
        (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
          hP.le hreal)) ∧
      0 ≤ B0 ∧
      Continuous
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal) ∧
      (∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius Ctop B1 ρ P),
        ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
            boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowRegularityOuterRadius Ctop ρ P *
              ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖) ∧
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ D ∧
      T ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P ∧
      ‖fLo‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4 ∧
      fLo =ᵐ[timeMeasure T]
        (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
          (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
              (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
            (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
              (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
              fLo) t))

theorem isLowRegularitySolution_of_remainder_bounds (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (hcont : Continuous
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hzero : ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ D)
    {T : ℝ} (hT : 0 < T) (hTτ : T ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ‖fLo‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4)
    (hforce : fLo =ᵐ[timeMeasure T]
      (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t))) :
    IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo :=
  ⟨δ, Ctop, B0, B1, D, ρ, P, hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore,
    hB0, hcont, htame, hzero, hTτ, hball, hforce⟩

theorem isLowRegularitySolutionAt_of_remainder_bounds (g₀ : SmoothRiemannianMetric I M)
    {δ Ctop B0 B1 D ρ P : ℝ} (hδ : δ < 1) (hCtop : 0 ≤ Ctop) (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hρ : 0 < ρ) (hP : 0 < P)
    (hreal : ∀ S : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ S) δ)
    (hδ0 : 0 ≤ δ) (hδ3 : δ ≤ 1 / 3)
    (hcore : Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g₀ hδ
      (lowRegularityMetricRealization (I := I) (M := M) g₀ (Ctop := Ctop) (B1 := B1) (ρ := ρ)
        hP.le hreal)))
    (hcont : Continuous
      (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal))
    (htame : ∀ u v : lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius Ctop B1 ρ P),
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal u -
          boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal v‖ ≤
        Ctop * lowRegularityOuterRadius Ctop ρ P *
            ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
          B0 *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
          B1 *
              (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
                ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1)‖)
    (hzero : ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ D)
    {T : ℝ} (hT : 0 < T) (hTτ : T ≤ lowRegularityTimeHorizon Ctop B0 B1 D ρ P)
    (hT1 : T ≤ 1)
    (fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T)
    (hball : ‖fLo‖ ≤ lowRegularityStateRadius Ctop B1 ρ P / 4)
    (hforce : fLo =ᵐ[timeMeasure T]
      (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g₀ hδ hCtop hB1 hρ hP hreal
        (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
            (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le)
          (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
            (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
            fLo) t)))
    {Rcap : ℝ} (hcap : lowRegularityStateRadius Ctop B1 ρ P ≤ Rcap) :
    IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop) (B0 := B0)
      (B1 := B1) (D := D) (ρ := ρ) (P := P) g₀ hT hT1 fLo Rcap :=
  ⟨hδ, hCtop, hB1, hρ, hP, hreal, hδ0, hδ3, hcore, hB0, hcont, htame,
    hzero, hTτ, hball, hforce, hcap⟩

theorem IsLowRegularitySolutionAt.toIsLowRegularitySolution {g₀ : SmoothRiemannianMetric I M}
    {δ Ctop B0 B1 D ρ P T Rcap : ℝ} {hT : 0 < T} {hT1 : T ≤ 1}
    {fLo : timeL2 (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T}
    (h : IsLowRegularitySolutionAt (I := I) (M := M) (δ := δ) (Ctop := Ctop) (B0 := B0)
      (B1 := B1) (D := D) (ρ := ρ) (P := P) g₀ hT hT1 fLo Rcap) :
    IsLowRegularitySolution (I := I) (M := M) g₀ hT fLo :=
  isLowRegularitySolution_of_remainder_bounds (I := I) (M := M) g₀ h.threshold_lt_one h.top_nonneg h.base_nonneg h.slope_nonneg h.outer_pos h.realize_pos
    h.metric_realization h.threshold_nonneg h.threshold_le_third h.smoothCore_continuous h.remainder_continuous h.remainder_lipschitz h.remainder_zero_bound hT h.time_le_horizon fLo
    h.forcing_norm_le_quarter_radius h.forcing_ae_eq_remainder

theorem exists_lowRegularity_remainder_bounds (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) {δ P : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < 1)
    (hP : 0 < P)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∃ (Ctop B0 B1 D ρ : ℝ) (hCtop : 0 ≤ Ctop) (hB1 : 0 ≤ B1) (hρ : 0 < ρ),
      0 ≤ B0 ∧
      Continuous
        (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal) ∧
      (∀ u v : lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius Ctop B1 ρ P),
        ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal u -
            boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal v‖ ≤
          Ctop * lowRegularityOuterRadius Ctop ρ P *
              ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
            B0 *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
            B1 *
                (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2))‖ +
                  ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                    (((1 : ℕ) : ℝ) + 2))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
                  (((1 : ℕ) : ℝ) + 2)) - v.1)‖) ∧
      ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1 hρ hP hreal
        ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
          (lowRegularityStateRadius_pos hCtop hB1 hρ hP).le⟩‖ ≤ D := by
  obtain ⟨ρ, Ctop, B0f, B1f, hρ, hCtop, hB0f, hB1f, houter⟩ :=
    deTurckRemainderOnLowerState_outer_bound (I := I) (M := M) hDim g₀ g_bg hδ0 hδ
  have hQpos : 0 < lowRegularityOuterRadius Ctop ρ P := lowRegularityOuterRadius_pos hCtop hρ hP
  have hB1Q : 0 ≤ B1f (lowRegularityOuterRadius Ctop ρ P) := hB1f _ hQpos.le
  have hRpos : 0 < lowRegularityStateRadius Ctop (B1f (lowRegularityOuterRadius Ctop ρ P)) ρ P :=
    lowRegularityStateRadius_pos hCtop hB1Q hρ hP
  have hQρ : lowRegularityOuterRadius Ctop ρ P ≤ ρ := by
    have := lowRegularityOuterRadius_le_rho (Ctop := Ctop) (ρ := ρ) (P := P)
    linarith
  have hRQ : lowRegularityStateRadius Ctop (B1f (lowRegularityOuterRadius Ctop ρ P)) ρ P ≤
      lowRegularityOuterRadius Ctop ρ P := by
    have := lowRegularityStateRadius_le_Q (Ctop := Ctop)
      (B1 := B1f (lowRegularityOuterRadius Ctop ρ P)) (ρ := ρ) (P := P)
    linarith
  have hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤
          lowRegularityOuterRadius Ctop ρ P →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ := by
    refine realizeOfLE (I := I) (M := M) g₀ ?_ hreal
    have := lowRegularityOuterRadius_le_P (Ctop := Ctop) (ρ := ρ) (P := P)
    linarith
  obtain ⟨hcont0, _hcorecont0, hbound0⟩ :=
    houter hQpos.le hQρ hRpos hRQ hrealQ
  exact ⟨Ctop, B0f (lowRegularityOuterRadius Ctop ρ P),
    B1f (lowRegularityOuterRadius Ctop ρ P),
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg hδ hCtop hB1Q hρ hP hreal
      ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hRpos.le⟩‖,
    ρ, hCtop, hB1Q, hρ, hB0f _ hQpos.le, hcont0, hbound0, le_rfl⟩

structure LowRegularityBoundParameters where
  threshold : ℝ
  top : ℝ
  base : ℝ
  slope : ℝ
  zeroBd : ℝ
  outer : ℝ
  realize : ℝ
  threshold_lt : threshold < 1
  top_nonneg : 0 ≤ top
  base_nonneg : 0 ≤ base
  slope_nonneg : 0 ≤ slope
  zero_nonneg : 0 ≤ zeroBd
  outer_pos : 0 < outer
  realize_pos : 0 < realize

structure LowRegularityHorizonParameters where
  top : ℝ
  base : ℝ
  slope : ℝ
  zeroBd : ℝ
  outer : ℝ
  realize : ℝ
  top_nonneg : 0 ≤ top
  base_nonneg : 0 ≤ base
  slope_nonneg : 0 ≤ slope
  zero_nonneg : 0 ≤ zeroBd
  outer_pos : 0 < outer
  realize_pos : 0 < realize

def LowRegularityBoundParameters.toHorizon (K : LowRegularityBoundParameters) : LowRegularityHorizonParameters where
  top := K.top
  base := K.base
  slope := K.slope
  zeroBd := K.zeroBd
  outer := K.outer
  realize := K.realize
  top_nonneg := K.top_nonneg
  base_nonneg := K.base_nonneg
  slope_nonneg := K.slope_nonneg
  zero_nonneg := K.zero_nonneg
  outer_pos := K.outer_pos
  realize_pos := K.realize_pos

structure IsLowRegularityBoundCap (K : LowRegularityBoundParameters) (U : LowRegularityHorizonParameters) : Prop where
  top_le : K.top ≤ U.top
  base_le : K.base ≤ U.base
  slope_le : K.slope ≤ U.slope
  zero_le : K.zeroBd ≤ U.zeroBd
  outer_le : U.outer ≤ K.outer
  realize_le : U.realize ≤ K.realize

theorem boundCap_refl (K : LowRegularityBoundParameters) :
    IsLowRegularityBoundCap K K.toHorizon :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

theorem horizon_le_of_cap {K : LowRegularityBoundParameters} {U : LowRegularityHorizonParameters}
    (h : IsLowRegularityBoundCap K U) :
    lowRegularityTimeHorizon U.top U.base U.slope U.zeroBd U.outer U.realize ≤
      lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize := by
  exact lowRegularityTimeHorizon_mono K.top_nonneg K.base_nonneg K.slope_nonneg
    K.zero_nonneg
    (lowRegularityStateRadius_pos U.top_nonneg U.slope_nonneg U.outer_pos U.realize_pos).le
    h.top_le h.base_le h.slope_le h.zero_le h.outer_le h.realize_le

structure HasLowRegularityBoundsAt (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) : Prop where
  threshold_nonneg : 0 ≤ K.threshold
  threshold_le_third : K.threshold ≤ 1 / 3
  metric_realization : ∀ S : SmoothCcTensor g₀ 0 2,
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) S‖ ≤ K.realize →
      gFibreOpBound (I := I) (M := M) g₀
        (ccTensorBilinSymm (I := I) g₀ S) K.threshold
  remainder_continuous : Continuous
    (boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
      K.slope_nonneg K.outer_pos K.realize_pos metric_realization)
  remainder_lipschitz : ∀ u v : lowerState (I := I) (M := M) g₀ 1
      (lowRegularityStateRadius K.top K.slope K.outer K.realize),
    ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos metric_realization u -
        boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
          K.slope_nonneg K.outer_pos K.realize_pos metric_realization v‖ ≤
      K.top * lowRegularityOuterRadius K.top K.outer K.realize *
          ‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
            (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
        K.base *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
        K.slope *
            (‖(u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(v.1 : TensorHs (I := I) (M := M) g₀ 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
          ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
            (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
            ((u.1 : TensorHs (I := I) (M := M) g₀ 0 2
              (((1 : ℕ) : ℝ) + 2)) - v.1)‖
  remainder_zero_bound : ‖boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
      K.slope_nonneg K.outer_pos K.realize_pos metric_realization
      ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
          K.realize_pos).le⟩‖ ≤ K.zeroBd
  smoothCore_continuous : Continuous
    (deTurckRemainderOnSmoothCore (I := I) (M := M) g₀ g_bg K.threshold_lt
      (lowRegularityMetricRealization (I := I) (M := M) g₀
        (Ctop := K.top) (B1 := K.slope) (ρ := K.outer)
        K.realize_pos.le metric_realization))

structure IsBackgroundLowRegularitySolution (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) (hK : HasLowRegularityBoundsAt (I := I) (M := M) g₀ g_bg K)
    {T : ℝ} (hT : 0 < T) (hT1 : T ≤ 1)
    (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
    (gforce : timeL2
      (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T) : Prop where
  map_eq : u = maximalRegularityDuhamelMap (I := I) (M := M) ((1 : ℕ) : ℝ) hT
    (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce
  field_mem : ∀ᵐ t ∂(timeMeasure T),
    maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) gforce t ∈
      lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius K.top K.slope K.outer K.realize)
  force_eq : gforce =ᵐ[timeMeasure T]
    (fun t => boundedDeTurckRemainderOnLowerState (I := I) (M := M) g₀ g_bg K.threshold_lt K.top_nonneg
      K.slope_nonneg K.outer_pos K.realize_pos hK.metric_realization
      (aeSetLift (zero_mem_lowerState (I := I) (M := M) g₀ 1
        (lowRegularityStateRadius_pos K.top_nonneg K.slope_nonneg K.outer_pos
          K.realize_pos).le)
        (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
          (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
          gforce) t))
  trace_zero : timeH1.trace0 _ T u = 0
  pde : timeH1.timeDeriv _ T u =
    timeScaleLaplacian (I := I) (M := M) ((1 : ℕ) : ℝ)
      (maximalRegularityDuhamelSolutionField (I := I) (M := M) ((1 : ℕ) : ℝ) hT
        (0 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2))
        gforce) + gforce
  force_bound : ‖gforce‖ ≤
    lowRegularityStateRadius K.top K.slope K.outer K.realize / 4

theorem exists_background_lowRegularity_solution (g₀ g_bg : SmoothRiemannianMetric I M)
    (K : LowRegularityBoundParameters) (hK : HasLowRegularityBoundsAt (I := I) (M := M) g₀ g_bg K) :
    ∀ {T : ℝ} (hT : 0 < T)
      (_ : T ≤ lowRegularityTimeHorizon K.top K.base K.slope K.zeroBd K.outer K.realize)
      (hT1 : T ≤ 1),
      ∃ (u : MaximalRegularitySolutionSpace (I := I) (M := M) ((1 : ℕ) : ℝ) T)
        (gforce : timeL2
          (TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ)) T),
        IsBackgroundLowRegularitySolution (I := I) (M := M) g₀ g_bg K hK hT hT1 u gforce := by
  intro T hT hTτ hT1
  obtain ⟨u, gforce, hmap, hmem, hforce, htrace, hpde, hbound⟩ :=
    exists_lowRegularity_solution_of_remainder_bounds (I := I) (M := M) g₀ g_bg K.threshold_lt
      K.top_nonneg K.base_nonneg K.slope_nonneg K.outer_pos K.realize_pos
      hK.metric_realization hK.remainder_continuous hK.remainder_lipschitz hK.remainder_zero_bound hT hTτ
  exact ⟨u, gforce, hmap, hmem, hforce, htrace, hpde, hbound⟩

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
