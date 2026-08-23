import DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.H2Pointwise
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.UnifBochnerGap
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SmoothPathHs

noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped ContDiff Manifold Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Laplacian

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Tensor0SBundle

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem norm_ccHs_eq_smoothHs (g₀ : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g₀ 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g₀ 2 σ T‖ =
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ σ T‖ := by
  rw [ccHs_eq_smoothHs]

theorem hsCovsum_smoothCc
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (n : ℕ) (T : SmoothCcTensor g₀ 0 2) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ ≤
      hsCovsumC Fc (Module.finrank ℝ E) n * ∑ j ∈ Finset.range (n + 1),
        ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact hsCovsum_unif_const (I := I) (M := M) g₀ Fc hFc hcurv 2 n T

theorem covsumHs_smoothCc
    (g₀ : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g₀ 0 r),
        ‖iteratedCovGrad (I := I) g₀ 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g₀ r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g₀ 0 r a S‖)
    (n : ℕ) (T : SmoothCcTensor g₀ 0 2) :
    ∑ j ∈ Finset.range (n + 1), ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
      covsumHsC Fc (Module.finrank ℝ E) n *
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (n : ℝ) T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact covsum_hs_unif_const (I := I) (M := M) g₀ Fc hFc hcurv 2 n T

theorem covsumHs2_smoothCc
    (g₀ : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g₀ 2 K)
    (T : SmoothCcTensor g₀ 0 2) :
    ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g₀ 0 2 j T‖ ≤
      h2CovsumC K * ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ := by
  rw [← norm_ccHs_eq_smoothHs]
  exact covsum_hs_two (I := I) (M := M) g₀ 2 hact T

def hs2FibreC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ := Cpt * covsumHsC Fc d 2

def hs2OpC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ := hs2FibreC Cpt Fc d + 1

theorem hs2FibreC_nonneg {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 ≤ hs2FibreC Cpt Fc d :=
  mul_nonneg hCpt (covsumHsC_nonneg (d := d) hFc 2)

theorem hs2OpC_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 < hs2OpC Cpt Fc d := by
  have h := hs2FibreC_nonneg hCpt hFc d
  unfold hs2OpC
  linarith

theorem hs2FibreC_le_opC (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) :
    hs2FibreC Cpt Fc d ≤ hs2OpC Cpt Fc d := by
  unfold hs2OpC
  linarith

def hs2FibreActionC (Cpt K : ℝ) : ℝ := Cpt * h2CovsumC K

def hs2OpActionC (Cpt K : ℝ) : ℝ := hs2FibreActionC Cpt K + 1

theorem hs2FibreAct_nonneg {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) :
    0 ≤ hs2FibreActionC Cpt K :=
  mul_nonneg hCpt (h2CovsumC_nonneg K)

theorem hs2OpActionC_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) :
    0 < hs2OpActionC Cpt K := by
  have h := hs2FibreAct_nonneg hCpt K
  unfold hs2OpActionC
  linarith

theorem hs2_fiber_sq_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ}
    (hmorrey : ∀ (T : SmoothCcTensor g 0 s) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2)
    (T : SmoothCcTensor g 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x) ≤
      hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
  classical
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt := hmorrey T x
  rw [hrange] at hpt
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖ ≤
        covsumHsC Fc (Module.finrank ℝ E) 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ := by
    simpa using covsum_hs_unif_const (I := I) (M := M) g Fc hFc hcurv s 2 T
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 s x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 s j T‖ ^ 2 := hpt
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 s j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (covsumHsC Fc (Module.finrank ℝ E) 2 *
            ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g s (2 : ℝ) T‖ ^ 2 := by
      unfold hs2FibreC
      ring

theorem hs2_fiber_sq_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ}
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
      hs2FibreActionC Cpt K ^ 2 *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
  classical
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hpt := hmorrey T x
  rw [hrange] at hpt
  have hsq :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 ≤
        (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
  have hsum :
      ∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤
        h2CovsumC K * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ := by
    have h := covsumHs2_smoothCc (I := I) (M := M) g hact T
    rw [← norm_ccHs_eq_smoothHs] at h
    exact h
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ Cpt ^ 2 * ∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2 := hpt
    _ ≤ Cpt ^ 2 *
          (∑ j ∈ Finset.range 3, ‖iteratedCovGrad (I := I) g 0 2 j T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg Cpt)
    _ ≤ Cpt ^ 2 *
          (h2CovsumC K * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀
          (Finset.sum_nonneg (fun j _ => norm_nonneg _)) hsum 2)
        (sq_nonneg Cpt)
    _ = hs2FibreActionC Cpt K ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      unfold hs2FibreActionC
      ring

omit [BoundarylessManifold I M] in
attribute [-instance] Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem gFibreOp_of_fiberSq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) {K : ℝ}
    (hK : 0 ≤ K)
    (hpt : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤ K ^ 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T) K := by
  intro x v w
  letI instTens : Bundle.RiemannianBundle
      (fun b : M => Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 2
  letI instNormed : ∀ b : M,
      NormedAddCommGroup (Tensor0SBundle.TensorRSSpace 0 2 I b) :=
    fun b =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := fun y : M => Tensor0SBundle.TensorRSSpace 0 2 I y) b
  have hnorm : ‖(T.toSection x : Tensor0SBundle.TensorRSSpace 0 2 I x)‖ ≤ K := by
    rw [norm_eq_sqrt_tensorInnerPointwise (I := I) (M := M) g 0 2 x (T.toSection x),
      ← riemannianFiberNormSq_eq_tensorInnerPointwise
        (I := I) (M := M) g 0 2 x (T.toSection x)]
    calc
      Real.sqrt (riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x))
          ≤ Real.sqrt (K ^ 2) := Real.sqrt_le_sqrt (hpt x)
      _ = K := Real.sqrt_sq hK
  have hcs := ccTensorBilin_abs_le_fibreNorm_mul_sqrt (I := I) (M := M) g T x
  have hsv : 0 ≤ Real.sqrt (g.inner x v v) := Real.sqrt_nonneg _
  have hsw : 0 ≤ Real.sqrt (g.inner x w w) := Real.sqrt_nonneg _
  have hvw : |ccTensorBilin (I := I) g T x v w| ≤
      K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) :=
    (hcs v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hsv) hsw)
  have hwv : |ccTensorBilin (I := I) g T x w v| ≤
      K * Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v) :=
    (hcs w v).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hsw) hsv)
  rw [ccTensorBilinSymm_apply]
  calc
    |(1 / 2 : ℝ) *
        (ccTensorBilin (I := I) g T x v w + ccTensorBilin (I := I) g T x w v)|
        ≤ (1 / 2 : ℝ) *
          (|ccTensorBilin (I := I) g T x v w| +
            |ccTensorBilin (I := I) g T x w v|) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
          (K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) +
            K * Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x v v)) :=
      mul_le_mul_of_nonneg_left (add_le_add hvw hwv) (by norm_num)
    _ = K * Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x w w) := by ring

theorem hs2_op_bound_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpC Cpt Fc (Module.finrank ℝ E) *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  have hN : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hFib : 0 ≤ hs2FibreC Cpt Fc (Module.finrank ℝ E) :=
    hs2FibreC_nonneg hCpt hFc _
  have hOp : 0 < hs2OpC Cpt Fc (Module.finrank ℝ E) := hs2OpC_pos hCpt hFc _
  refine gFibreOp_of_fiberSq (I := I) (M := M) g T (mul_nonneg hOp.le hN) ?_
  intro x
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ hs2FibreC Cpt Fc (Module.finrank ℝ E) ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 :=
      hs2_fiber_sq_unif (I := I) (M := M) hDim g 2 Fc hFc hcurv hmorrey T x
    _ ≤ hs2OpC Cpt Fc (Module.finrank ℝ E) ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      unfold hs2OpC
      nlinarith [hFib]
    _ = (hs2OpC Cpt Fc (Module.finrank ℝ E) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by ring

theorem hs2_op_bound_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpActionC Cpt K *
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) := by
  have hN : (0 : ℝ) ≤ ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ :=
    norm_nonneg _
  have hFib : 0 ≤ hs2FibreActionC Cpt K := hs2FibreAct_nonneg hCpt K
  have hOp : 0 < hs2OpActionC Cpt K := hs2OpActionC_pos hCpt K
  refine gFibreOp_of_fiberSq (I := I) (M := M) g T (mul_nonneg hOp.le hN) ?_
  intro x
  calc
    riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x)
        ≤ hs2FibreActionC Cpt K ^ 2 *
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 :=
      hs2_fiber_sq_action (I := I) (M := M) hDim g hact hmorrey T x
    _ ≤ hs2OpActionC Cpt K ^ 2 *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      unfold hs2OpActionC
      nlinarith [hFib]
    _ = (hs2OpActionC Cpt K *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖) ^ 2 := by ring

theorem hs2_op_smoothCc_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2)
    (T : SmoothCcTensor g 0 2) :
    gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
      (hs2OpC Cpt Fc (Module.finrank ℝ E) *
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖) := by
  rw [← norm_ccHs_eq_smoothHs]
  exact hs2_op_bound_unif (I := I) (M := M) hDim g Fc hFc hcurv hCpt hmorrey T

def unifRealizeRad (Cpt : ℝ) (Fc : ℕ → ℝ) (d : ℕ) : ℝ :=
  deTurckRemainderContractionThreshold d / hs2OpC Cpt Fc d

theorem unifRealizeRad_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) {Fc : ℕ → ℝ}
    (hFc : ∀ p, 0 ≤ Fc p) (d : ℕ) : 0 < unifRealizeRad Cpt Fc d :=
  div_pos (de_turck_remainder_contraction_threshold_pos d) (hs2OpC_pos hCpt hFc d)

def actionRealizeRad (Cpt K : ℝ) (d : ℕ) : ℝ :=
  deTurckRemainderContractionThreshold d / hs2OpActionC Cpt K

theorem actionRealizeRad_pos {Cpt : ℝ} (hCpt : 0 ≤ Cpt) (K : ℝ) (d : ℕ) :
    0 < actionRealizeRad Cpt K d :=
  div_pos (de_turck_remainder_contraction_threshold_pos d) (hs2OpActionC_pos hCpt K)

theorem realize_at_action
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) {K : ℝ}
    (hact : IsCurvAction0 (I := I) (M := M) g 2 K)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤
          actionRealizeRad Cpt K (Module.finrank ℝ E) →
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (deTurckRemainderContractionThreshold (Module.finrank ℝ E)) := by
  intro T hT
  have hOp : 0 < hs2OpActionC Cpt K := hs2OpActionC_pos hCpt K
  have hTtwo : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤
      actionRealizeRad Cpt K (Module.finrank ℝ E) := by
    rw [Nat.cast_one] at hT
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at hT
    exact hT
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
      actionRealizeRad Cpt K (Module.finrank ℝ E) := by
    rw [norm_ccHs_eq_smoothHs]
    exact hTtwo
  have hdelta : hs2OpActionC Cpt K *
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
        deTurckRemainderContractionThreshold (Module.finrank ℝ E) := by
    calc
      hs2OpActionC Cpt K *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ hs2OpActionC Cpt K *
              actionRealizeRad Cpt K (Module.finrank ℝ E) :=
        mul_le_mul_of_nonneg_left hT' hOp.le
      _ = deTurckRemainderContractionThreshold (Module.finrank ℝ E) := by
        unfold actionRealizeRad
        field_simp
  have hsmall := hs2_op_bound_action (I := I) (M := M) hDim g hact hCpt hmorrey T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem realize_at_unif
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    (Fc : ℕ → ℝ) (hFc : ∀ p, 0 ≤ Fc p)
    (hcurv : ∀ (r p : ℕ) (S : SmoothCcTensor g 0 r),
        ‖iteratedCovGrad (I := I) g 0 (r + 1) p
            (pointwiseTensorCurv (I := I) (M := M) g r S)‖ ≤
          Fc p * ∑ a ∈ Finset.range (p + 2),
            ‖iteratedCovGrad (I := I) g 0 r a S‖)
    {Cpt : ℝ} (hCpt : 0 ≤ Cpt)
    (hmorrey : ∀ (T : SmoothCcTensor g 0 2) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 2 x (T.toSection x) ≤
          Cpt ^ 2 * ∑ j ∈ Finset.range (Module.finrank ℝ E / 2 + 2),
            ‖iteratedCovGrad (I := I) g 0 2 j T‖ ^ 2) :
    ∀ T : SmoothCcTensor g 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) T‖ ≤
          unifRealizeRad Cpt Fc (Module.finrank ℝ E) →
        gFibreOpBound (I := I) (M := M) g (ccTensorBilinSymm (I := I) g T)
          (deTurckRemainderContractionThreshold (Module.finrank ℝ E)) := by
  intro T hT
  have hOp : 0 < hs2OpC Cpt Fc (Module.finrank ℝ E) := hs2OpC_pos hCpt hFc _
  have hTtwo : ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤
      unifRealizeRad Cpt Fc (Module.finrank ℝ E) := by
    rw [Nat.cast_one] at hT
    rw [show (1 : ℝ) + 1 = 2 by norm_num] at hT
    exact hT
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
      unifRealizeRad Cpt Fc (Module.finrank ℝ E) := by
    rw [norm_ccHs_eq_smoothHs]
    exact hTtwo
  have hdelta : hs2OpC Cpt Fc (Module.finrank ℝ E) *
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤
        deTurckRemainderContractionThreshold (Module.finrank ℝ E) := by
    calc
      hs2OpC Cpt Fc (Module.finrank ℝ E) *
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ hs2OpC Cpt Fc (Module.finrank ℝ E) *
              unifRealizeRad Cpt Fc (Module.finrank ℝ E) :=
        mul_le_mul_of_nonneg_left hT' hOp.le
      _ = deTurckRemainderContractionThreshold (Module.finrank ℝ E) := by
        unfold unifRealizeRad
        field_simp
  have hsmall := hs2_op_bound_unif (I := I) (M := M) hDim g Fc hFc hcurv hCpt hmorrey T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end DifferentialGeometry.Analysis.Spectral

end
