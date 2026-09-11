import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold
variable {E F H H' M N : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable [TopologicalSpace H] [TopologicalSpace H']
variable (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
variable [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H' N]

theorem isImmersionAtOfComplement_unit_of_equalDimension (f : M → N) (x : M)
    (h : IsImmersionAt I J ∞ f x) (hdim : Module.finrank ℝ E = Module.finrank ℝ F) :
    IsImmersionAtOfComplement Unit I J ∞ f x := by
  let C := h.complement
  let L : C →ₗ[ℝ] F := h.equiv.toLinearMap.comp (LinearMap.inr ℝ E C)
  have hL : Injective L := by
    intro c d he
    exact congrArg (fun p : E × C => p.2) (h.equiv.injective he)
  let : FiniteDimensional ℝ C := FiniteDimensional.of_injective L hL
  have heq := h.equiv.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at heq
  change Module.finrank ℝ E + Module.finrank ℝ C = Module.finrank ℝ F at heq
  have hzero : Module.finrank ℝ C = 0 := by omega
  let e : C ≃L[ℝ] Unit :=
    (LinearEquiv.ofFinrankEq (R := ℝ) C Unit (by rw [hzero]; exact (Module.finrank_zero_of_subsingleton (R := ℝ) (M := Unit)).symm)).toContinuousLinearEquiv
  exact h.isImmersionAtOfComplement_complement.trans_F e
end DifferentialGeometry.Topology.Manifold
