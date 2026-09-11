import DifferentialGeometry.Analysis.Heat.Kernel.Basic
import DifferentialGeometry.Analysis.Heat.Smoothing.Scalar.HeatFlow

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.HeatEquation

open MeasureTheory
open Spectral
open Parabolic.TensorHeatEquation
open Parabolic.TensorSpectral (eigenvectorSmooth)
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2 (TensorL2)
open DifferentialGeometry.Analysis.Laplacian (smoothToLp smoothToLp_apply)
open scoped Manifold ContDiff InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_heatKernel_mul_eq_scalarHeatFlow (g : SmoothRiemannianMetric I M)
    (u₀ : Lp Real 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : Real} (ht : 0 < t) (x : M) :
    (∫ y, heatKernel g t x y * u₀ y ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      scalarHeatFlow g u₀ t x := by
  let : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hu₀ : Integrable u₀ (riemannianVolumeMeasure (I := I) (M := M) g) :=
    (Lp.memLp u₀).integrable (by norm_num)
  have hcoeff (i : TensorEigenIdx00 g) :
      tensorL2Coeff (tensorResolventL2_isCompactOperator g 0 0)
        ((tensor00ScalarL2Equiv g).symm u₀) i =
        ∫ y, (scalarEigenFunction g i).toFun y * u₀ y
          ∂riemannianVolumeMeasure (I := I) (M := M) g := by
    calc
      _ = ⟪(eigenvectorSmooth g 0 0 i : TensorL2 0 0 g),
          (tensor00ScalarL2Equiv g).symm u₀⟫_ℝ := by
        rw [tensorL2Coeff_eq_inner, ← eigenvectorSmooth00_eq_basis]
      _ = ⟪scalarEigenFunctionLp g i, u₀⟫_ℝ := by
        rw [scalarEigenFunctionLp_eq_tensorBasis]
        simpa using ((tensor00ScalarL2Equiv g).toLinearIsometry.inner_map_map
          (eigenvectorSmooth g 0 0 i : TensorL2 0 0 g)
          ((tensor00ScalarL2Equiv g).symm u₀)).symm
      _ = _ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp (scalarEigenFunction g i).memLp_two] with y hy
        change ⟪smoothToLp g (scalarEigenFunction g i) y, u₀ y⟫_ℝ = _
        rw [smoothToLp_apply, hy]
        change u₀ y * (scalarEigenFunction g i).toFun y =
          (scalarEigenFunction g i).toFun y * u₀ y
        exact mul_comm _ _
  rw [integral_heatKernel_mul g ht hu₀ x]
  unfold scalarHeatFlow scalarHeatFlowTensor scalarSpecSum scalarHeatCoeff
  apply tsum_congr
  intro i
  dsimp only
  rw [hcoeff]
  change Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x *
      (∫ y, (scalarEigenFunction g i).toFun y * u₀ y
        ∂riemannianVolumeMeasure (I := I) (M := M) g) =
    Real.exp (-TensorEigenIdx.lambda i * t) *
      (∫ y, (scalarEigenFunction g i).toFun y * u₀ y
        ∂riemannianVolumeMeasure (I := I) (M := M) g) * (scalarEigenFunction g i).toFun x
  ring

theorem integral_heatKernel_mul_ae_eq_heatSemigroup (g : SmoothRiemannianMetric I M)
    (u₀ : Lp Real 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {t : Real} (ht : 0 < t) :
    (fun x => ∫ y, heatKernel g t x y * u₀ y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g] (heatSemigroup g t u₀ : M → Real) := by
  have hab : t / 2 < t + 1 := by linarith
  have ha : 0 < t / 2 := half_pos ht
  have ht' : t ∈ Set.Icc (t / 2) (t + 1) := by
    constructor
    · exact (half_lt_self ht).le
    · linarith
  have heq := scalarHeatFlowSlice_toL2_eq_heatSemigroup g u₀ hab ha ht'
  have hae := MemLp.coeFn_toLp (scalarHeatFlowSlice g u₀ hab ha ht').memLp_two
  filter_upwards [hae] with x hx
  calc
    _ = scalarHeatFlow g u₀ t x := integral_heatKernel_mul_eq_scalarHeatFlow g u₀ ht x
    _ = (scalarHeatFlowSlice g u₀ hab ha ht').toFun x := rfl
    _ = smoothToLp g (scalarHeatFlowSlice g u₀ hab ha ht') x := by
      rw [smoothToLp_apply]
      exact hx.symm
    _ = heatSemigroup g t u₀ x := by rw [heq]

theorem integral_heatKernel_mul_scalarEigenFunction (g : SmoothRiemannianMetric I M)
    {t : Real} (ht : 0 < t) (x : M) (i : TensorEigenIdx00 g) :
    (∫ y, heatKernel g t x y * (scalarEigenFunction g i).toFun y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      Real.exp (-TensorEigenIdx.lambda i * t) * (scalarEigenFunction g i).toFun x := by
  classical
  have hi := DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    (scalarEigenFunction g i).smooth.continuous
    (HasCompactSupport.of_compactSpace (scalarEigenFunction g i).toFun)
  have hinner (j : TensorEigenIdx00 g) :
      (∫ y, (scalarEigenFunction g j).toFun y * (scalarEigenFunction g i).toFun y
        ∂riemannianVolumeMeasure (I := I) (M := M) g) = if j = i then 1 else 0 := by
    rw [← smoothToLp_inner_eq_integral_mul]
    change ⟪scalarEigenFunctionLp g j, scalarEigenFunctionLp g i⟫_ℝ = _
    rw [scalarEigenFunctionLp_eq_tensorBasis, scalarEigenFunctionLp_eq_tensorBasis,
      (tensor00ScalarL2Equiv g).inner_map_map]
    rw [eigenvectorSmooth00_eq_basis, ← tensorL2Coeff_eq_inner]
    exact tensorL2Coeff_eigenvectorSmooth00 g j i
  rw [integral_heatKernel_mul g ht hi x]
  simp_rw [hinner]
  simp

theorem heatKernel_convolution (g : SmoothRiemannianMetric I M)
    {s t : Real} (hs : 0 < s) (ht : 0 < t) (x y : M) :
    (∫ z, heatKernel g t x z * heatKernel g s z y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = heatKernel g (t + s) x y := by
  have hcont : Continuous (fun z : M => heatKernel g s z y) := by
    exact (continuousOn_heatKernel g).comp_continuous
      (continuous_const.prodMk (continuous_id.prodMk continuous_const))
      (fun z => ⟨hs, Set.mem_univ _⟩)
  have hi := DifferentialGeometry.Integral.DivergenceTheorem.Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g
    hcont (HasCompactSupport.of_compactSpace _)
  rw [integral_heatKernel_mul g ht hi x]
  change _ = ∑' i : TensorEigenIdx00 g,
    Real.exp (-TensorEigenIdx.lambda i * (t + s)) * (scalarEigenFunction g i).toFun x *
      (scalarEigenFunction g i).toFun y
  apply tsum_congr
  intro i
  have h := integral_heatKernel_mul_scalarEigenFunction g hs y i
  have heq : (∫ z, (scalarEigenFunction g i).toFun z * heatKernel g s z y
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      Real.exp (-TensorEigenIdx.lambda i * s) * (scalarEigenFunction g i).toFun y := by
    convert h using 1
    apply integral_congr_ae
    filter_upwards with z
    rw [heatKernel_symm g s z y]
    ring
  rw [heq, mul_add, Real.exp_add]
  ring
end DifferentialGeometry.Analysis.HeatEquation
