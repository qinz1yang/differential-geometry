import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleParabolicTraceEnergy
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Regularity.DominatedConvergence

open DifferentialGeometry.Geometry.Curvature
open Manifold MeasureTheory Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
variable {g : SmoothRiemannianMetric I M} {r s : ℕ} {a T : ℝ}
variable (u : CrossScaleField (I := I) (M := M) g r s a T)

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private theorem coeffFun_sq_le_initial_add_integral_norm (hT : 0 < T)
    (i : TensorEigenIdx (I := I) (M := M) g r s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i t) ^ 2 ≤
      tensorSobolevWeight (I := I) (M := M) i (a + 1) * (u.coeffFun i 0) ^ 2 +
        ∫ τ in Ioc 0 T, ‖u.energyIntegrand i τ‖ := by
  rw [u.perMode_energyIdentity i ht]
  gcongr
  calc
    ∫ s in (0 : ℝ)..t, u.energyIntegrand i s ≤ ‖∫ s in (0 : ℝ)..t, u.energyIntegrand i s‖ := Real.le_norm_self _
    _ ≤ ∫ s in Ioc (0 : ℝ) T, ‖u.energyIntegrand i s‖ :=
      u.norm_intervalIntegral_energyIntegrand_le hT i ht

theorem continuousOn_repr : ContinuousOn u.repr (Icc 0 T) := by
  rcases lt_or_ge 0 T with hT | hT
  swap
  · exact (subsingleton_Icc_of_ge hT).continuousOn _
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  refine TensorHs.continuousOn_of_coeff_of_summable_bound
    (f := u.repr) (σ := a + 1) (K := Icc (0 : ℝ) T)
    (B := fun i => tensorSobolevWeight (I := I) (M := M) i (a + 1) *
      (u.coeffFun i 0) ^ 2 + ∫ τ in Ioc 0 T, ‖u.energyIntegrand i τ‖) ?_ ?_ ?_
  · intro i
    refine (u.continuousOn_coeffFun i).congr ?_
    intro t ht
    exact u.repr_coeff hT ht i
  · exact (u.summable_coeffFun_sq hT hzero).add
      (u.summable_integral_norm_energyIntegrand ⟨hT.le, le_rfl⟩)
  · intro t ht i
    rw [u.repr_coeff hT ht i]
    exact u.coeffFun_sq_le_initial_add_integral_norm hT i ht

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear.CrossScaleField
