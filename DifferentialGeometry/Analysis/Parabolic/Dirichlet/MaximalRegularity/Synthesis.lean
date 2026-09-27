import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.Plancherel
import DifferentialGeometry.Analysis.Sobolev.DirichletHs.FiniteSupport

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace Dirichlet
namespace MaximalRegularity

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs

variable {g : SmoothRiemannianMetric (I_half n) M}

private theorem norm_dirichletHsBasisVec {σ : ℝ}
    (i : DirichletLaplacianEigenIndex g) :
    ‖DirichletHs.basisVec g σ i‖ =
      Real.sqrt (dirichletSobolevWeight i σ) := by
  classical
  rw [DirichletHs.norm_eq_sqrt_tsum]
  congr 1
  have hfun : (fun j => dirichletSobolevWeight j σ *
        ((DirichletHs.basisVec g σ i).coeff j) ^ 2)
      = fun j => if j = i then dirichletSobolevWeight j σ else 0 := by
    funext j
    rw [DirichletHs.basisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, one_pow, mul_one]
    · rw [if_neg hj, if_neg hj, zero_pow (by norm_num), mul_zero]
  rw [hfun, tsum_ite_eq i (fun j => dirichletSobolevWeight j σ)]

private def singleModeCLM {σ : ℝ}
    (i : DirichletLaplacianEigenIndex g) :
    ℝ →L[ℝ] DirichletHs g σ :=
  LinearMap.mkContinuous
    { toFun := fun c => c • DirichletHs.basisVec g σ i
      map_add' := fun c d => by rw [add_smul]
      map_smul' := fun a c => by rw [smul_smul]; rfl }
    (Real.sqrt (dirichletSobolevWeight i σ))
    (fun c => by
      change ‖c • DirichletHs.basisVec g σ i‖ ≤ _
      rw [norm_smul, norm_dirichletHsBasisVec i, Real.norm_eq_abs]
      exact le_of_eq (mul_comm _ _))

@[simp] private theorem singleModeCLM_apply {σ : ℝ}
    (i : DirichletLaplacianEigenIndex g) (c : ℝ) :
    singleModeCLM (g := g) (σ := σ) i c =
      c • DirichletHs.basisVec g σ i := rfl

open scoped Classical in
private theorem singleModeCLM_coeff {σ : ℝ}
    (i j : DirichletLaplacianEigenIndex g) (c : ℝ) :
    (singleModeCLM (g := g) (σ := σ) i c).coeff j =
      (if j = i then c else 0) := by
  classical
  rw [singleModeCLM_apply]
  simp only [DirichletHs.smul_coeff, DirichletHs.basisVec_coeff]
  by_cases hj : j = i
  · rw [if_pos hj, if_pos hj, mul_one]
  · rw [if_neg hj, if_neg hj, mul_zero]

variable {σ : ℝ} {T : ℝ}

private def singleModeTimeL2 {σ : ℝ}
    {T : ℝ} (i : DirichletLaplacianEigenIndex g) :
    timeL2 ℝ T →L[ℝ] timeL2 (DirichletHs g σ) T :=
  (singleModeCLM (g := g) (σ := σ) i).compLpL 2 (timeMeasure T)

private theorem singleModeTimeL2_coeFn (i : DirichletLaplacianEigenIndex g)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (g := g) (σ := σ) i gf =ᵐ[timeMeasure T]
      fun t => (gf t) • DirichletHs.basisVec g σ i := by
  have h := (singleModeCLM (g := g) (σ := σ) i).coeFn_compLpL
    (p := 2) (μ := timeMeasure T) gf
  exact h.trans (Eventually.of_forall fun t => singleModeCLM_apply i (gf t))

open scoped Classical in
private theorem timeModeCoeff_singleModeTimeL2
    (i j : DirichletLaplacianEigenIndex g) (gf : timeL2 ℝ T) :
    timeModeCoeff
        (singleModeTimeL2 (σ := σ) i gf) j =
      (if j = i then gf else 0) := by
  classical
  refine Lp.ext ?_
  have hlhs := timeModeCoeff_coeFn
    (singleModeTimeL2 (σ := σ) i gf) j
  have hsm := singleModeTimeL2_coeFn
    (σ := σ) i gf
  have hcoord : ∀ t,
      (((gf t) • DirichletHs.basisVec g σ i).coeff j)
        = (if j = i then gf t else 0) := by
    intro t
    simp only [DirichletHs.smul_coeff, DirichletHs.basisVec_coeff]
    by_cases hj : j = i
    · rw [if_pos hj, if_pos hj, mul_one]
    · rw [if_neg hj, if_neg hj, mul_zero]
  by_cases hj : j = i
  · filter_upwards [hlhs, hsm] with t ht hsmt
    rw [ht, hsmt, hcoord t, if_pos hj, if_pos hj]
  · have hzero := Lp.coeFn_zero (E := ℝ) (p := 2) (μ := timeMeasure T)
    filter_upwards [hlhs, hsm, hzero] with t ht hsmt hzt
    rw [ht, hsmt, hcoord t, if_neg hj, if_neg hj, hzt]
    rfl

private theorem norm_singleModeTimeL2_sq (i : DirichletLaplacianEigenIndex g)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (σ := σ) i gf‖ ^ 2 =
      dirichletSobolevWeight i σ * ‖gf‖ ^ 2 := by
  rw [TimeSobolev.norm_sq_eq_integral, TimeSobolev.norm_sq_eq_integral,
    ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn
    (σ := σ) i gf] with t ht
  rw [ht, norm_smul, mul_pow, norm_dirichletHsBasisVec i,
    Real.sq_sqrt (dirichletSobolevWeight_nonneg i σ),
    Real.norm_eq_abs, sq_abs, mul_comm]

private theorem norm_singleModeTimeL2 (i : DirichletLaplacianEigenIndex g)
    (gf : timeL2 ℝ T) :
    ‖singleModeTimeL2 (σ := σ) i gf‖ =
      Real.sqrt (dirichletSobolevWeight i σ) * ‖gf‖ := by
  have hsq := norm_singleModeTimeL2_sq
    (σ := σ) i gf
  have hrhs_nonneg : 0 ≤ Real.sqrt (dirichletSobolevWeight i σ) * ‖gf‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have h := Real.sqrt_le_sqrt (le_of_eq hsq)
  have h' := Real.sqrt_le_sqrt (le_of_eq hsq.symm)
  have hsqrt : ‖singleModeTimeL2 (σ := σ) i gf‖ =
      Real.sqrt (dirichletSobolevWeight i σ * ‖gf‖ ^ 2) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hsqrt, Real.sqrt_mul (dirichletSobolevWeight_nonneg i σ),
    Real.sqrt_sq (norm_nonneg _)]

private theorem inner_dirichletHsBasisVec_eq_zero
    {i j : DirichletLaplacianEigenIndex g}
    (hij : i ≠ j) :
    (inner ℝ (DirichletHs.basisVec g σ i)
      (DirichletHs.basisVec g σ j) : ℝ) = 0 := by
  classical
  rw [DirichletHs.inner_def]
  have hterm : (fun k => dirichletSobolevWeight k σ *
        ((DirichletHs.basisVec g σ i).coeff k *
          (DirichletHs.basisVec g σ j).coeff k))
      = fun _ => (0 : ℝ) := by
    funext k
    rw [DirichletHs.basisVec_coeff, DirichletHs.basisVec_coeff]
    by_cases hki : k = i
    · rw [if_pos hki, if_neg (by rw [hki]; exact hij), mul_zero, mul_zero]
    · rw [if_neg hki, zero_mul, mul_zero]
  rw [hterm, tsum_zero]

private theorem inner_singleModeTimeL2_eq_zero
    {i j : DirichletLaplacianEigenIndex g} (hij : i ≠ j)
    (gf hf : timeL2 ℝ T) :
    (inner ℝ (singleModeTimeL2 (σ := σ) i gf)
      (singleModeTimeL2 (σ := σ) j hf) : ℝ) = 0 := by
  rw [TimeSobolev.inner_def]
  rw [show (∫ t in Set.Icc (0 : ℝ) T,
        inner ℝ (singleModeTimeL2 (σ := σ) i gf t)
          (singleModeTimeL2 (σ := σ) j hf t))
      = ∫ t in Set.Icc (0 : ℝ) T, (0 : ℝ) from ?_, integral_zero]
  refine integral_congr_ae ?_
  filter_upwards [singleModeTimeL2_coeFn
      (σ := σ) i gf,
    singleModeTimeL2_coeFn
      (σ := σ) j hf] with t hit hjt
  rw [hit, hjt, inner_smul_left, inner_smul_right,
    inner_dirichletHsBasisVec_eq_zero hij, mul_zero, mul_zero]

private def singleModeScaledCLM {σ : ℝ}
    {T : ℝ} (i : DirichletLaplacianEigenIndex g) :
    timeL2 ℝ T →L[ℝ]
      timeL2 (DirichletHs g σ) T :=
  (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ •
    singleModeTimeL2 (σ := σ) (T := T) i

@[simp] private theorem singleModeScaledCLM_apply
    (i : DirichletLaplacianEigenIndex g) (gf : timeL2 ℝ T) :
    singleModeScaledCLM (g := g) (σ := σ) i gf =
      (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ •
        singleModeTimeL2 (σ := σ) i gf := by
  rw [singleModeScaledCLM, smul_apply]

private def singleModeIsometry {σ : ℝ}
    {T : ℝ} (i : DirichletLaplacianEigenIndex g) :
    timeL2 ℝ T →ₗᵢ[ℝ]
      timeL2 (DirichletHs g σ) T :=
  { (singleModeScaledCLM (g := g) (σ := σ) i).toLinearMap with
    norm_map' := fun gf => by
      have hsqrt_pos : 0 < Real.sqrt (dirichletSobolevWeight i σ) :=
        Real.sqrt_pos.mpr (dirichletSobolevWeight_pos i σ)
      have hval : ((singleModeScaledCLM (g := g)
            (σ := σ) i).toLinearMap gf) =
            (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ •
              singleModeTimeL2 (σ := σ) i gf :=
        singleModeScaledCLM_apply i gf
      rw [hval, norm_smul, norm_singleModeTimeL2 i, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hsqrt_pos), ← mul_assoc,
        inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_mul] }

@[simp] private theorem singleModeIsometry_apply
    (i : DirichletLaplacianEigenIndex g) (gf : timeL2 ℝ T) :
    singleModeIsometry (g := g) (σ := σ) i gf =
      (Real.sqrt (dirichletSobolevWeight i σ))⁻¹ •
        singleModeTimeL2 (σ := σ) i gf :=
  singleModeScaledCLM_apply i gf

private theorem orthogonalFamily_singleModeIsometry {σ : ℝ} {T : ℝ} :
    OrthogonalFamily ℝ (fun _ : DirichletLaplacianEigenIndex g => timeL2 ℝ T)
      (fun i => singleModeIsometry (g := g)
        (σ := σ) (T := T) i) := by
  intro i j hij gf hf
  rw [singleModeIsometry_apply, singleModeIsometry_apply, inner_smul_left,
    inner_smul_right, inner_singleModeTimeL2_eq_zero hij,
    mul_zero, mul_zero]

private theorem singleModeTimeL2_eq_isometry
    (i : DirichletLaplacianEigenIndex g)
    (gf : timeL2 ℝ T) :
    singleModeTimeL2 (σ := σ) i gf =
      singleModeIsometry (g := g) (σ := σ) i
        ((Real.sqrt (dirichletSobolevWeight i σ)) • gf) := by
  have hsqrt_pos : 0 < Real.sqrt (dirichletSobolevWeight i σ) :=
    Real.sqrt_pos.mpr (dirichletSobolevWeight_pos i σ)
  rw [singleModeIsometry_apply, map_smul, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_smul]

private theorem summable_singleModeTimeL2
    (gFam : DirichletLaplacianEigenIndex g → timeL2 ℝ T)
    (hsum : Summable (fun i => dirichletSobolevWeight i σ *
      ‖gFam i‖ ^ 2)) :
    Summable (fun i => singleModeTimeL2 (σ := σ) i
      (gFam i)) := by
  have hrw : (fun i => singleModeTimeL2 (σ := σ) i
        (gFam i))
      = fun i => singleModeIsometry (g := g)
          (σ := σ) i
          ((Real.sqrt (dirichletSobolevWeight i σ)) • gFam i) := by
    funext i
    exact singleModeTimeL2_eq_isometry i (gFam i)
  rw [hrw]
  rw [(orthogonalFamily_singleModeIsometry
    (g := g) (σ := σ) (T := T)).summable_iff_norm_sq_summable]
  refine hsum.congr (fun i => ?_)
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (dirichletSobolevWeight_nonneg i σ)]

def timeL2OfModes
    (gFam : DirichletLaplacianEigenIndex g → timeL2 ℝ T) :
    timeL2 (DirichletHs g σ) T :=
  ∑' i, singleModeTimeL2 (σ := σ) i (gFam i)

theorem timeL2OfModes_timeModeCoeff
    (gFam : DirichletLaplacianEigenIndex g → timeL2 ℝ T)
    (hsum : Summable (fun i => dirichletSobolevWeight i σ *
      ‖gFam i‖ ^ 2))
    (j : DirichletLaplacianEigenIndex g) :
    timeModeCoeff
        (timeL2OfModes (σ := σ) gFam) j =
      gFam j := by
  classical
  have hsumm := summable_singleModeTimeL2 gFam hsum
  have hcomm : timeModeCoeff
        (timeL2OfModes (σ := σ) gFam) j =
      ∑' i, timeModeCoeff
        (singleModeTimeL2 (σ := σ) i (gFam i)) j := by
    rw [timeL2OfModes]
    exact ContinuousLinearMap.map_tsum
      ((dirichletHsCoeffL j).compLpL 2 (timeMeasure T))
      hsumm
  rw [hcomm]
  have hterm : (fun i => timeModeCoeff
        (singleModeTimeL2 (σ := σ) i (gFam i)) j)
      = fun i => if i = j then gFam i else 0 := by
    funext i
    rw [timeModeCoeff_singleModeTimeL2 i j (gFam i)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij h.symm)]
  rw [hterm, tsum_ite_eq j gFam]

end MaximalRegularity
end Dirichlet
end Parabolic
end Analysis
end DifferentialGeometry
