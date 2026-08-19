import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorLeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.HamiltonIveyRegion
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciControlsRm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.RicciPreservation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ScalarLowerBound
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open Bundle Tensor0SBundle
open Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

private theorem scalar_eq_neg_two_mul_sum_sectional
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis) :
    metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) =
      2 * ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
  have htrace := traceData_metricTrace (I := I) (M := M) S horth
  have hscalar := htrace.scalar_trace
  have hscalar' : metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) =
      -stdScalar3 (standardRmCompAt (I := I) basis (S.base.rm04 t x)) := by
    linarith
  rw [hscalar']
  have hcurv := htrace.curvature_symmetries
  have h01 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 0 1 0 1 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 0) (basis 1) (basis 1) (basis 0) := by
    have h' : -(S.base.rm04 t x) (vec4 (basis 0) (basis 1) (basis 0) (basis 1)) =
        (S.base.rm04 t x) (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) := by
      simpa using (hcurv.anti_last 0 1 0 1).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg h'
  have h02 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 0 2 0 2 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 0) (basis 2) (basis 2) (basis 0) := by
    have h' : -(S.base.rm04 t x) (vec4 (basis 0) (basis 2) (basis 0) (basis 2)) =
        (S.base.rm04 t x) (vec4 (basis 0) (basis 2) (basis 2) (basis 0)) := by
      simpa using (hcurv.anti_last 0 2 0 2).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg h'
  have h12 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 1 2 1 2 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 1) (basis 2) (basis 2) (basis 1) := by
    have h' : -(S.base.rm04 t x) (vec4 (basis 1) (basis 2) (basis 1) (basis 2)) =
        (S.base.rm04 t x) (vec4 (basis 1) (basis 2) (basis 2) (basis 1)) := by
      simpa using (hcurv.anti_last 1 2 1 2).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg h'
  have h10' : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 1 0 1 0 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 0) (basis 1) (basis 1) (basis 0) := by
    have hlast : -(S.base.rm04 t x) (vec4 (basis 1) (basis 0) (basis 1) (basis 0)) =
        (S.base.rm04 t x) (vec4 (basis 1) (basis 0) (basis 0) (basis 1)) := by
      simpa using (hcurv.anti_last 1 0 1 0).symm
    have hswap : (S.base.rm04 t x) (vec4 (basis 1) (basis 0) (basis 0) (basis 1)) =
        (S.base.rm04 t x) (vec4 (basis 0) (basis 1) (basis 1) (basis 0)) := by
      simpa using (hcurv.block_symm 1 0 0 1).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg (hlast.trans hswap)
  have h20' : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 2 0 2 0 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 0) (basis 2) (basis 2) (basis 0) := by
    have hlast : -(S.base.rm04 t x) (vec4 (basis 2) (basis 0) (basis 2) (basis 0)) =
        (S.base.rm04 t x) (vec4 (basis 2) (basis 0) (basis 0) (basis 2)) := by
      simpa using (hcurv.anti_last 2 0 2 0).symm
    have hswap : (S.base.rm04 t x) (vec4 (basis 2) (basis 0) (basis 0) (basis 2)) =
        (S.base.rm04 t x) (vec4 (basis 0) (basis 2) (basis 2) (basis 0)) := by
      simpa using (hcurv.block_symm 2 0 0 2).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg (hlast.trans hswap)
  have h21' : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 2 1 2 1 a)) =
      -tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis 1) (basis 2) (basis 2) (basis 1) := by
    have hlast : -(S.base.rm04 t x) (vec4 (basis 2) (basis 1) (basis 2) (basis 1)) =
        (S.base.rm04 t x) (vec4 (basis 2) (basis 1) (basis 1) (basis 2)) := by
      simpa using (hcurv.anti_last 2 1 2 1).symm
    have hswap : (S.base.rm04 t x) (vec4 (basis 2) (basis 1) (basis 1) (basis 2)) =
        (S.base.rm04 t x) (vec4 (basis 1) (basis 2) (basis 2) (basis 1)) := by
      simpa using (hcurv.block_symm 2 1 1 2).symm
    simpa [vec4, tensor04StdAt] using congrArg Neg.neg (hlast.trans hswap)
  have hdiag0 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 0 0 0 0 a)) = 0 := by
    have h : standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 0 0 0 =
        -standardRmCompAt (I := I) basis (S.base.rm04 t x) 0 0 0 0 :=
      hcurv.anti_first 0 0 0 0
    unfold standardRmCompAt rm04CompAt component0S at h
    nlinarith
  have hdiag1 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 1 1 1 1 a)) = 0 := by
    have h : standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 1 1 1 =
        -standardRmCompAt (I := I) basis (S.base.rm04 t x) 1 1 1 1 :=
      hcurv.anti_first 1 1 1 1
    unfold standardRmCompAt rm04CompAt component0S at h
    nlinarith
  have hdiag2 : (S.base.rm04 t x) (fun a : Fin 4 => basis (slots4 2 2 2 2 a)) = 0 := by
    have h : standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 2 2 2 =
        -standardRmCompAt (I := I) basis (S.base.rm04 t x) 2 2 2 2 :=
      hcurv.anti_first 2 2 2 2
    unfold standardRmCompAt rm04CompAt component0S at h
    nlinarith
  unfold stdScalar3 stdRicci3
  simp only [Fin.sum_univ_three, standardRmCompAt, rm04CompAt, component0S,
    bivectorIndex3, Fin.reduceEq, ↓reduceIte]
  rw [h01, h02, h12, h10', h20', h21', hdiag0, hdiag1, hdiag2]
  ring_nf

theorem scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis) :
    S.scalar t x =
      2 * ∑ i : Fin 3,
        orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ i := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hscalar : metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) =
      2 * ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) :=
    scalar_eq_neg_two_mul_sum_sectional (I := I) (M := M) S basis horth
  have htrace :
      ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i =
        ∑ i : Fin 3,
          tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
            (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
            (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
    have hperm :
        ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i =
          ∑ i : Fin 3,
            (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues i := by
      unfold orderedSectionalCurvaturesAt Matrix.IsHermitian.eigenvalues
      let e : Fin 3 ≃ Fin 3 := Fintype.equivOfCardEq (Fintype.card_fin 3)
      have hsum := Fintype.sum_equiv e.symm
        (f := fun i => (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀
          (e.symm i))
        (g := fun i => (curvatureOperatorMatrixAt_isHermitian (I := I) x basis A).eigenvalues₀ i)
        (by intro i; rfl)
      simpa [e, Matrix.IsHermitian.eigenvalues] using hsum.symm
    rw [hperm]
    simpa [A, orderedSectionalCurvaturesAt] using
      (curvatureOperatorMatrixAt_eigenvalues_trace_eq_sectionalSum
        (I := I) x basis A)
  calc
    S.scalar t x =
        metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
          simp [SolutionOn.scalar_eq_metricTrace]
    _ = 2 * ∑ i : Fin 3,
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := hscalar
    _ = 2 * ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i := by
          rw [htrace]

theorem sum_orderedSectionalCurvaturesAt_basisIndependent
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (basis₁ basis₂ : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth₁ : OrthonormalBasisAt (I := I) (S.base.metric t) x basis₁)
    (horth₂ : OrthonormalBasisAt (I := I) (S.base.metric t) x basis₂) :
    (∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis₁
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ i) =
      ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis₂
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ i := by
  have h₁ := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis₁ horth₁
  have h₂ := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis₂ horth₂
  nlinarith

omit [SigmaCompactSpace M] in
theorem curvatureOperatorMatrixAt_initial_mem_hamiltonIveyConvexMatrixRegion
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K : Real} (hK : 0 < K)
    {x : M} (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t0) x basis)
    (hinit : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K) :
    curvatureOperatorMatrixAt (I := I) x basis
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩ ∈
      hamiltonIveyConvexMatrixRegion K 0 := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t0) x⟩
  let M : Matrix (Fin 3) (Fin 3) Real := curvatureOperatorMatrixAt (I := I) x basis A
  have hM : M.IsHermitian := by
    dsimp [M]
    exact curvatureOperatorMatrixAt_isHermitian (I := I) x basis A
  have hmin : -K ≤ orderedSectionalCurvaturesAt (I := I) x basis A 2 := by
    have hiff := (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le
      (I := I) (S.base.metric t0) x basis horth A K).mp hinit
    linarith
  have h21 := orderedSectionalCurvaturesAt_one_le_zero (I := I) x basis A
  have h32 := orderedSectionalCurvaturesAt_two_le_one (I := I) x basis A
  have hbar := hamiltonIveyConvexBarrier_initial_le_sectionalSum_of_ordered
    (l1 := orderedSectionalCurvaturesAt (I := I) x basis A 0)
    (l2 := orderedSectionalCurvaturesAt (I := I) x basis A 1)
    (l3 := orderedSectionalCurvaturesAt (I := I) x basis A 2)
    h21 h32 hmin hK
  have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
    (I := I) x basis A
  refine ⟨hM, ?_, ?_⟩
  · dsimp [M, orderedSectionalCurvaturesAt]
    exact le_max_right _ _
  · dsimp [M]
    rw [htrace]
    simpa [A, M, orderedSectionalCurvaturesAt, pinchHeight3, sectionalSum3,
      Fin.sum_univ_three] using hbar

theorem scalar_ge_two_mul_negative_sectional_barrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t t0 K : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (hν : orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ 2 < 0)
    (hbarrier : hamiltonIveyBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ 2)) ≤ S.scalar t x / 2) :
    S.scalar t x ≥
      2 * (-orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ 2) *
        (Real.log ((-orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ 2) / K) +
          Real.log (1 + 2 * K * (t - t0)) - 3) := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hνA : orderedSectionalCurvaturesAt (I := I) x basis A 2 < 0 := by
    simpa [A] using hν
  have hpinch : pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2) =
      -orderedSectionalCurvaturesAt (I := I) x basis A 2 := by
    unfold pinchHeight3
    rw [max_eq_left (neg_nonneg.mpr hνA.le)]
  have hbar : hamiltonIveyBarrier K (t - t0)
      (-orderedSectionalCurvaturesAt (I := I) x basis A 2) ≤ S.scalar t x / 2 := by
    simpa [A, hpinch] using hbarrier
  have hscalar := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis horth
  unfold hamiltonIveyBarrier at hbar
  nlinarith

theorem scalar_ge_two_mul_negative_sectional_of_convexBarrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t t0 K : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis)
    (hν : orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ 2 < 0)
    (hconv : hamiltonIveyConvexBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ 2)) ≤ S.scalar t x / 2) :
    S.scalar t x ≥
      2 * (-orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ 2) *
        (Real.log ((-orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ 2) / K) +
          Real.log (1 + 2 * K * (t - t0)) - 3) := by
  exact scalar_ge_two_mul_negative_sectional_barrier (I := I) (M := M) S
    basis horth hν (by
      have hle := hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ 2))
      exact hle.trans hconv)

omit [SigmaCompactSpace M] [T2Space M] in
theorem sectionalCurvature_asymptotic_pinching_of_barrier
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t t0 K δ : Real} {ν : Real} {x : M}
    (hK : 0 < K) (hδ : 0 < δ) (hτ : 0 ≤ t - t0)
    (hbarrier : hamiltonIveyBarrier K (t - t0) (pinchHeight3 ν) ≤ S.scalar t x / 2) :
    pinchHeight3 ν ≤
      δ * S.scalar t x +
        2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * (t - t0)) := by
  have hmain := pinchHeight_le_linear_sectionalSum_of_barrier
    (K := K) (τ := t - t0) (X := pinchHeight3 ν) (S := S.scalar t x / 2)
    (δ := δ) hK hδ hτ (le_max_right _ _) hbarrier
  nlinarith

private theorem scalar_ge_two_mul_three_mul_min
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M}
    (basis : Module.Basis (Fin 3) Real (TangentSpace I x))
    (horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis) :
    2 * 3 * orderedSectionalCurvaturesAt (I := I) x basis
        ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t) x⟩ 2 ≤
      metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hscalar := scalar_eq_neg_two_mul_sum_sectional (I := I) (M := M) S basis horth
  rw [hscalar]
  have hray : ∀ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A 2 ≤
      tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
    intro i
    have h := algebraicCurvatureOperatorQuadraticEval_rayleighLower
      (I := I) (S.base.metric t) x basis horth A
      (c := fun _ : Fin 1 => (1 : Real))
      (v := fun _ : Fin 1 => basis (bivectorIndex3 i).1)
      (w := fun _ : Fin 1 => basis (bivectorIndex3 i).2)
    have hid : algebraicCurvatureIdentityQuadraticEval (I := I) (S.base.metric t)
        (fun _ : Fin 1 => (1 : Real))
        (fun _ : Fin 1 => basis (bivectorIndex3 i).1)
        (fun _ : Fin 1 => basis (bivectorIndex3 i).2) = 1 := by
      unfold algebraicCurvatureIdentityQuadraticEval
      simp only [Fin.sum_univ_one]
      have hpair := bivectorBasisPairing_eq_delta (I := I) (S.base.metric t) x basis horth i i
      simp [hpair]
    have hquad : algebraicCurvatureOperatorQuadraticEval (I := I) (M := M) A
        (fun _ : Fin 1 => (1 : Real))
        (fun _ : Fin 1 => basis (bivectorIndex3 i).1)
        (fun _ : Fin 1 => basis (bivectorIndex3 i).2) =
        tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
          (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
          (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
      dsimp [A]
      unfold algebraicCurvatureOperatorQuadraticEval
      simp only [Fin.sum_univ_one, tensor04StdAt, one_mul]
    rw [hquad, hid, mul_one] at h
    exact h
  have hsum : 3 * orderedSectionalCurvaturesAt (I := I) x basis A 2 ≤
      ∑ i : Fin 3, tensor04StdAt (I := I) (M := M) (S.base.rm04 t x)
        (basis (bivectorIndex3 i).1) (basis (bivectorIndex3 i).2)
        (basis (bivectorIndex3 i).2) (basis (bivectorIndex3 i).1) := by
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hray i)
    simpa [Fin.sum_univ_three, mul_comm, mul_left_comm, mul_assoc] using hle
  nlinarith

private theorem scalar_initial_lower
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t : Real} {x : M} {K : Real}
    (hdim : Module.finrank Real (TangentSpace I x) = 3)
    (hA : CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t) x
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ K) :
    -6 * K ≤ metricTracePair0SAt (I := I) (S.base.metric t) (S.ricci t x) := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t) x hdim
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  have hmin :
      -orderedSectionalCurvaturesAt (I := I) x basis A 2 ≤ K :=
    (curvatureOperatorLowerBoundAt_iff_neg_sectionalMin_le
      (I := I) (S.base.metric t) x basis horth A K).mp hA
  have hmin' : -K ≤ orderedSectionalCurvaturesAt (I := I) x basis A 2 := by
    linarith
  have hscalar := scalar_ge_two_mul_three_mul_min (I := I) (M := M) S basis horth
  have hmin'' : -K ≤ orderedSectionalCurvaturesAt (I := I) x basis
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩ 2 := by
    simpa [A] using hmin'
  nlinarith [hmin'', hscalar]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem canonicalScalarRegularOn_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hreg : CanonicalScalarRegularOn (I := I) (M := M) S) (t0 : Real) :
    CanonicalScalarRegularOn (I := I) (M := M) (S.timeShift t0) where
  scalar_continuousOn := by
    have hmaps : MapsTo (fun q : Real × M => (q.1 + t0, q.2))
        ((D.timeShift t0).carrier ×ˢ (Set.univ : Set M))
        (D.carrier ×ˢ (Set.univ : Set M)) := by
      intro q hq
      exact ⟨by simpa [RealTimeInterval.timeShift_carrier] using hq.1, trivial⟩
    have hcont : ContinuousOn (fun q : Real × M => (q.1 + t0, q.2))
        ((D.timeShift t0).carrier ×ˢ (Set.univ : Set M)) := by
      fun_prop
    have hcomp := hreg.scalar_continuousOn.comp hcont hmaps
    simpa [SolutionOn.timeShift_scalar] using hcomp
  scalar_time_within := by
    intro K t ht hsub x
    have htcar : t + t0 ∈ D.carrier := by
      have ht' : t ∈ (D.timeShift t0).carrier := hsub ht
      simpa [RealTimeInterval.timeShift_carrier] using ht'
    have hf : HasDerivWithinAt (fun r : Real => S.scalar r x)
        (derivWithin (fun r : Real => S.scalar r x) D.carrier (t + t0)) D.carrier (t + t0) := by
      exact (hreg.scalar_time_within (K := D.carrier) (t := t + t0) htcar
        (by intro r hr; exact hr) x).hasDerivWithinAt
    have hg : HasDerivWithinAt (fun s : Real => s + t0) 1 K t := by
      exact ((hasDerivAt_id (t : Real)).add_const t0).hasDerivWithinAt
    have hmaps : MapsTo (fun s : Real => s + t0) K D.carrier := by
      intro s hs
      have hs' : s ∈ (D.timeShift t0).carrier := hsub hs
      simpa [RealTimeInterval.timeShift_carrier] using hs'
    have hcomp := HasDerivWithinAt.comp (h₂ := fun r : Real => S.scalar r x)
      (h := fun s : Real => s + t0) (x := t) hf hg hmaps
    simpa [SolutionOn.timeShift_scalar, Function.comp_apply] using hcomp.differentiableWithinAt
  scalar_space := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_scalar] using hreg.scalar_space (t + t0) ht' x
  scalar_grad := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad (t + t0) ht' x
  scalar_mul_grad := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_mul_grad (t + t0) ht' x
  scalar_sq_space := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_scalar] using hreg.scalar_sq_space (t + t0) ht' x
  scalar_sq_grad := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_sq_grad (t + t0) ht' x
  scalar_sq_div_space := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_scalar] using hreg.scalar_sq_div_space (t + t0) ht' x
  scalar_sq_div_grad := by
    intro t ht x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_sq_div_grad (t + t0) ht' x
  scalar_grad_sub_const := by
    intro t ht c x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad_sub_const (t + t0) ht' c x
  scalar_grad_const_mul_sub_const := by
    intro t ht a c x
    have ht' : t + t0 ∈ D.carrier := by
      simpa [RealTimeInterval.timeShift_carrier] using ht
    simpa [SolutionOn.timeShift_family_metric, SolutionOn.timeShift_scalar] using
      hreg.scalar_grad_const_mul_sub_const (t + t0) ht' a c x

private theorem scalarEvolutionEquationOn_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S) (t0 : Real) :
    ScalarEvolutionEquationOn (D := D.timeShift t0)
      (S.timeShift t0).scalar
      (fun t x => DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I)
        (flowG (I := I) (S.timeShift t0)) t ((S.timeShift t0).scalar t) x)
      (fun t x => normSq0S (I := I) ((S.timeShift t0).family.metric t) x 2
        ((S.timeShift t0).ricci t x)) := by
  intro t x
  have htreg : (t : Real) + t0 ∈ D.regular := by
    have ht' : (t : Real) ∈ (D.timeShift t0).regular := t.property
    simpa only [RealTimeInterval.timeShift_regular, Set.mem_setOf_eq] using ht'
  have hevol := hS.scalarEvolution (flowG (I := I) S) (by intro u; rfl) (by intro u; rfl)
    ⟨(t : Real) + t0, htreg⟩ x
  have hg : HasDerivWithinAt (fun s : Real => s + t0) 1 (D.timeShift t0).carrier (t : Real) := by
    exact ((hasDerivAt_id (t : Real)).add_const t0).hasDerivWithinAt
  have hmaps : MapsTo (fun s : Real => s + t0) (D.timeShift t0).carrier D.carrier := by
    intro s hs
    simpa [RealTimeInterval.timeShift_carrier] using hs
  have hcomp := HasDerivWithinAt.comp (h₂ := fun r : Real => S.scalar r x)
    (h := fun s : Real => s + t0) (x := (t : Real)) hevol hg hmaps
  simp only [mul_one] at hcomp
  have hlap_eq :
      DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) (flowG (I := I) S)
          ((t : Real) + t0) (S.scalar ((t : Real) + t0)) x =
        DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I)
          (flowG (I := I) (S.timeShift t0)) (t : Real) ((S.timeShift t0).scalar (t : Real)) x := by
    unfold DifferentialGeometry.Geometry.Curvature.laplacianAt flowG
      SolutionOn.timeShift SolutionFamily.timeShift SolutionOn.scalar SolutionFamily.scalar
      SolutionFamily.connection
    rfl
  have hnorm_eq :
      normSq0S (I := I) (S.family.metric ((t : Real) + t0)) x 2 (S.ricci ((t : Real) + t0) x) =
        normSq0S (I := I) ((S.timeShift t0).family.metric (t : Real)) x 2
          ((S.timeShift t0).ricci (t : Real) x) := by
    unfold SolutionOn.timeShift SolutionFamily.timeShift SolutionOn.ricci SolutionFamily.ricci
      SolutionOn.family
    rfl
  rw [hlap_eq, hnorm_eq] at hcomp
  simpa [SolutionOn.timeShift_scalar, Function.comp_apply] using hcomp

private theorem scalarLowerBoundWMPRegularity_timeShift
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    (t0 T n c0 : Real) (K : NNReal)
    (hsubset : ∀ t : Real, t ∈ Set.Icc 0 T -> t ∈ (D.timeShift t0).carrier)
    (hden : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / n) * c0 * t ≠ 0) :
    ScalarLowerBoundWMPRegularity (I := I)
      (flowG (I := I) (S.timeShift t0)) T n c0 (S.timeShift t0).scalar K := by
  classical
  let hreg := canonicalScalarRegularOn_timeShift (I := I) (M := M) S hS.scalarRegular t0
  have hmetric : ∀ t : Real, t ∈ Set.Icc 0 T ->
      (flowG (I := I) (S.timeShift t0)).metric t = (S.timeShift t0).family.metric t := by
    intro t _ht
    rfl
  have hscalar_cont : ContinuousOn
      (fun p : Real × M => (S.timeShift t0).scalar p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    refine hreg.scalar_continuousOn.mono ?_
    intro p hp
    exact ⟨hsubset p.1 hp.1, trivial⟩
  have hbar_cont : ContinuousOn
      (fun p : Real × M => scalarLowerBarrier n c0 p.1)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    have hden_ne : ∀ p : Real × M, p ∈ DifferentialGeometry.Analysis.Parabolic.spacetimeSlab
      (M := M) T ->
        1 - (2 / n) * c0 * p.1 ≠ 0 := by
      intro p hp
      exact hden p.1 hp.1
    have hden_cont : ContinuousOn
        (fun p : Real × M => 1 - (2 / n) * c0 * p.1)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
      have hlin : Continuous
          (fun p : Real × M => ((2 / n) * c0) * p.1) :=
        continuous_const.mul continuous_fst
      have hcont : Continuous
          (fun p : Real × M => 1 - ((2 / n) * c0) * p.1) :=
        continuous_const.sub hlin
      simpa [mul_assoc] using hcont.continuousOn
    have hconst : ContinuousOn
        (fun _p : Real × M => c0)
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
      exact continuous_const.continuousOn
    simpa [scalarLowerBarrier] using hconst.div hden_cont hden_ne
  refine
    { weighted_cont := ?_
      weighted_mdiff := ?_
      weighted_grad := ?_
      scalar_time := ?_
      scalar_space := ?_
      diff_space := ?_
      diff_grad := ?_ }
  · have hexp_cont : ContinuousOn
        (fun p : Real × M => Real.exp (-(K : Real) * p.1))
        (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
      have hlin : Continuous
          (fun p : Real × M => -((K : Real) * p.1)) :=
        (continuous_const.mul continuous_fst).neg
      simpa using (Real.continuous_exp.comp hlin).continuousOn
    exact hexp_cont.mul (hscalar_cont.sub hbar_cont)
  · intro t ht x
    have hdiff :
        MDifferentiableAt I 𝓘(Real, Real)
          (fun y : M => (S.timeShift t0).scalar t y - scalarLowerBarrier n c0 t) x :=
      (hreg.scalar_space t (hsubset t ht) x).sub mdifferentiableAt_const
    simpa [smul_eq_mul] using
      (hdiff.const_smul (Real.exp (-(K : Real) * t)))
  · intro t ht x
    rw [hmetric t ht]
    exact hreg.scalar_grad_const_mul_sub_const t (hsubset t ht)
      (Real.exp (-(K : Real) * t)) (scalarLowerBarrier n c0 t) x
  · intro t ht x
    exact hreg.scalar_time_within ht hsubset x
  · intro t ht y
    exact hreg.scalar_space t (hsubset t ht) y
  · intro t ht y
    exact (hreg.scalar_space t (hsubset t ht) y).sub mdifferentiableAt_const
  · intro t ht x
    rw [hmetric t ht]
    exact hreg.scalar_grad_sub_const t (hsubset t ht)
      (scalarLowerBarrier n c0 t) x

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem scalarBarrierLowerBound_of_engineData
    [CompactSpace M] [I.Boundaryless]
    {D' : RealTimeInterval}
    (G' : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real)
    (T n c0 : Real) (hT : 0 < T) (hn : n ≠ 0)
    (scalar' scalarLap' ricciNormSq' : Real -> M -> Real) (K' : NNReal)
    (hslab' : Set.Icc 0 T ⊆ D'.carrier)
    (hregular' : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ D'.regular)
    (hden' : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < 1 - (2 / n) * c0 * t)
    (hreg' : ScalarLowerBoundWMPRegularity (I := I) G' T n c0 scalar' K')
    (hevol' : ScalarEvolutionEquationOn (D := D') scalar' scalarLap' ricciNormSq')
    (hlap' : ScalarLaplacianRealizesHeatOperatorOn (I := I) G' T scalar' scalarLap')
    (hricci' : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / n) * (scalar' t x) ^ 2 <= ricciNormSq' t x)
    (hinit' : InitialScalarLowerBound (M := M) scalar' c0)
    (hF_lip' : ∀ t : Real, t ∈ Set.Icc 0 T ->
      LipschitzOnWith K' (fun a : Real => scalarLowerReaction n a t)
        (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet
          (M := M) T scalar' (scalarLowerBarrier n c0))) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier n c0 t <= scalar' t x :=
  scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := I) (M := M) (D := D') G' T n c0 hT hn
    scalar' scalarLap' ricciNormSq' K'
    hslab' hregular' hden' hreg' hevol' hlap' hricci' hinit' hF_lip'

private theorem initialScalarLowerBound_shifted
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K : Real} (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    InitialScalarLowerBound (M := M) (fun t x => S.scalar (t + t0) x) (-6 * K) := by
  intro x
  have h := scalar_initial_lower (I := I) (M := M) S (by simpa using hdim)
    (by simpa [SolutionOn.family_metric] using hinit x)
  have hsc : -6 * K ≤ S.scalar t0 x := by
    simpa using h
  simpa [InitialScalarLowerBound] using hsc

private theorem scalarLowerBarrier_le_shifted_scalar
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T K : Real} (hK : 0 < K) (hT : 0 < T)
    (hdim : Module.finrank Real E = 3)
    (hslab : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t ∈ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    ∀ s : Real, s ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier 3 (-6 * K) s <= (S.timeShift t0).scalar s x := by
  let S' : SolutionOn (I := I) (M := M) (D.timeShift t0) := S.timeShift t0
  let G' : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamily (I := I) (M := M) Real :=
    flowG (I := I) S'
  let scalar' : Real -> M -> Real := S'.scalar
  let scalarLap' : Real -> M -> Real :=
    fun t x => DifferentialGeometry.Geometry.Curvature.laplacianAt (I := I) G' t (scalar' t) x
  let ricciNormSq' : Real -> M -> Real :=
    fun t x => normSq0S (I := I) (S'.family.metric t) x 2 (S'.ricci t x)
  have hslab_fn' : ∀ s : Real, s ∈ Set.Icc 0 T -> s ∈ (D.timeShift t0).carrier := by
    intro s hs
    have hmem := hslab (s + t0) ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa [RealTimeInterval.timeShift_carrier] using hmem
  have hslab' : Set.Icc 0 T ⊆ (D.timeShift t0).carrier := by
    intro s hs
    exact hslab_fn' s hs
  have hregular' : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t -> t ∈ (D.timeShift t0).regular := by
    intro s hs hspos
    have hmem := hregular (s + t0) ⟨by linarith [hs.1], by linarith [hs.2]⟩
      (by linarith [hspos])
    simpa [RealTimeInterval.timeShift_regular] using hmem
  have hden' : ∀ t : Real, t ∈ Set.Icc 0 T ->
      0 < 1 - (2 / 3 : Real) * (-6 * K) * t := by
    intro t ht
    have hpos : 0 ≤ K * t := mul_nonneg (le_of_lt hK) ht.1
    nlinarith
  have hden_ne' : ∀ t : Real, t ∈ Set.Icc 0 T ->
      1 - (2 / 3 : Real) * (-6 * K) * t ≠ 0 := by
    intro t ht
    exact ne_of_gt (hden' t ht)
  have hscalar_cont : ContinuousOn
      (fun p : Real × M => scalar' p.1 p.2)
      (DifferentialGeometry.Analysis.Parabolic.spacetimeSlab (M := M) T) := by
    have hcont :=
      (canonicalScalarRegularOn_timeShift (I := I) (M := M) S hS.scalarRegular t0).scalar_continuousOn
    refine hcont.mono ?_
    intro p hp
    exact ⟨hslab_fn' p.1 hp.1, trivial⟩
  have hbar_cont : ContinuousOn (scalarLowerBarrier 3 (-6 * K)) (Set.Icc 0 T) := by
    unfold scalarLowerBarrier
    have hden_cont : ContinuousOn (fun t : Real => 1 - (2 / 3 : Real) * (-6 * K) * t)
        (Set.Icc 0 T) := by
      fun_prop
    exact continuousOn_const.div hden_cont (fun t ht => ne_of_gt (hden' t ht))
  have hcompact :
      IsCompact (DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet
        (M := M) T scalar' (scalarLowerBarrier 3 (-6 * K))) :=
    DifferentialGeometry.Analysis.Parabolic.scalarWeakMaximumPrincipleValueSet_isCompact
      (M := M) T scalar' (scalarLowerBarrier 3 (-6 * K)) hscalar_cont hbar_cont
  obtain ⟨K', hK'⟩ :=
    exists_scalarLowerReaction_lipschitzOn_valueSet (M := M) 3 T scalar'
      (scalarLowerBarrier 3 (-6 * K)) hcompact
  have hreg' :
      ScalarLowerBoundWMPRegularity (I := I) G' T 3 (-6 * K) scalar' K' := by
    simpa [G', scalar', S'] using
      (scalarLowerBoundWMPRegularity_timeShift (I := I) (M := M) S hS t0 T 3 (-6 * K) K'
        hslab' hden_ne')
  have hevol' : ScalarEvolutionEquationOn (D := D.timeShift t0) scalar' scalarLap' ricciNormSq' := by
    simpa [scalar', scalarLap', ricciNormSq', G', S'] using
      scalarEvolutionEquationOn_timeShift (I := I) (M := M) S hS t0
  have hlap' : ScalarLaplacianRealizesHeatOperatorOn (I := I) G' T scalar' scalarLap' :=
    ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt
      (I := I) (G := G') (T := T) (scalar := scalar') (scalarLap := scalarLap')
      (by
        intro t _ht x
        rfl)
  have hricci' : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      (1 / 3 : Real) * (scalar' t x) ^ 2 <= ricciNormSq' t x := by
    intro t _ht x
    classical
    letI : Nonempty (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :=
      ⟨⟨0, by simp [hdim]⟩⟩
    let basis : Module.Basis (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E)
      Real
        (TangentSpace I x) :=
      DifferentialGeometry.Tensor.Coordinates.coordinateFrameAt_toBasis (I := I) x
    let gInv :
        DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E ->
          DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E -> Real :=
      fun k l =>
        DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_component
          (I := I) (S'.family.metric t) x k l (extChartAt I x x)
    have hinv :
        Tensor0SBundle.MetricInverseInBasis (I := I) (S'.family.metric t) x
          basis gInv := by
      simpa [basis, gInv] using
        Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
          (I := I) (S'.family.metric t) x
    have h :=
      DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_sq_div_rank_le_normSq0S
        (I := I) (g := S'.family.metric t) (basis := basis)
        (gInv := gInv) hinv (S'.ricciAt t x)
    have hcard :
        (1 / (Fintype.card (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := Real) E) :
          Real)) =
          (1 / 3 : Real) := by
      simp [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hdim]
    have hcoef : ((Module.finrank Real E : Real)⁻¹) = (3⁻¹ : Real) := by
      simp [hdim]
    simpa [scalar', ricciNormSq', S', SolutionOn.scalar_eq_metricTrace,
      DifferentialGeometry.Tensor.Coordinates.CoordinateIdx, hcard, hcoef]
      using h
  have hinit' : InitialScalarLowerBound (M := M) scalar' (-6 * K) := by
    simpa [scalar', S', SolutionOn.timeShift_scalar] using
      (initialScalarLowerBound_shifted (I := I) (M := M) S hdim hinit)
  have hmain : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      scalarLowerBarrier 3 (-6 * K) t <= scalar' t x :=
    scalarBarrierLowerBound_of_engineData (I := I) (M := M) (D' := D.timeShift t0)
      G' T 3 (-6 * K) hT (by norm_num : (3 : Real) ≠ 0)
      scalar' scalarLap' ricciNormSq' K'
      hslab' hregular' hden'
      hreg' hevol' hlap' hricci' hinit' hK'
  simpa [scalar', S'] using hmain

theorem scalarCurvature_lower_bound_of_curvatureOperator_lower_bound
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T K : Real} (hK : 0 < K) (hT : 0 < T)
    (hdim : Module.finrank Real E = 3)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x := by
  have hslab_fn : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t ∈ D.carrier := by
    intro t ht
    exact hslab ht
  intro t ht x
  have hs : t - t0 ∈ Set.Icc 0 T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hb : scalarLowerBarrier 3 (-6 * K) (t - t0) ≤ (S.timeShift t0).scalar (t - t0) x :=
    scalarLowerBarrier_le_shifted_scalar (I := I) (M := M) S hS hK hT hdim
      hslab_fn hregular hinit (t - t0) hs x
  have hbar_eq : scalarLowerBarrier 3 (-6 * K) (t - t0) = -6 * K / (1 + 4 * K * (t - t0)) := by
    unfold scalarLowerBarrier
    have hden' : 1 - (2 / 3 : Real) * (-6 * K) * (t - t0) = 1 + 4 * K * (t - t0) := by
      ring
    rw [hden']
  have hscalar : (S.timeShift t0).scalar (t - t0) x = S.scalar t x := by
    have harg : (t - t0) + t0 = t := by ring
    rw [SolutionOn.timeShift_scalar, harg]
  rw [← hbar_eq, ← hscalar]
  exact hb

theorem scalar_curvature_initial_lower_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K : Real} (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    ∀ x : M, -6 * K ≤ S.scalar t0 x := by
  intro x
  have h := scalar_initial_lower (I := I) (M := M) S (by simpa using hdim)
    (by simpa [SolutionOn.family_metric] using hinit x)
  simpa using h

theorem scalar_curvature_lower_bound
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T K : Real} (hK : 0 < K) (hT : 0 < T)
    (hdim : Module.finrank Real E = 3)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x :=
  scalarCurvature_lower_bound_of_curvatureOperator_lower_bound
    (I := I) (M := M) S hS hK hT hdim hslab hregular hinit

theorem scalar_curvature_lower_bound_compact_flow
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T K : Real} (hK : 0 < K) (hT : 0 ≤ T)
    (hdim : Module.finrank Real E = 3)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ K) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x := by
  intro t ht x
  by_cases hT0 : T = 0
  · subst hT0
    have ht_eq : t = t0 := by
      nlinarith [ht.1, ht.2]
    rw [ht_eq]
    have hinit_bound := scalar_curvature_initial_lower_bound
      (I := I) (M := M) S hdim hinit x
    have hden : 1 + 4 * K * (t0 - t0) = 1 := by
      rw [sub_self, mul_zero, add_zero]
    rw [hden, div_one]
    exact hinit_bound
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hT0)
    exact scalar_curvature_lower_bound (I := I) (M := M) S hS hK hTpos
      hdim hslab hregular hinit t ht x

theorem scalar_curvature_lower_bound_K_one
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T : Real} (hT : 0 < T)
    (hdim : Module.finrank Real E = 3)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ 1) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      -6 / (1 + 4 * (t - t0)) ≤ S.scalar t x := by
  intro t ht x
  have hmain := scalar_curvature_lower_bound (I := I) (M := M) S hS
    (by norm_num : 0 < (1 : Real)) hT hdim hslab hregular hinit t ht x
  norm_num at hmain ⊢
  simpa [one_mul] using hmain

theorem scalar_curvature_lower_bound_K_one_compact_flow
    [CompactSpace M] [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {t0 T : Real} (hT : 0 ≤ T)
    (hdim : Module.finrank Real E = 3)
    (hslab : Set.Icc t0 (t0 + T) ⊆ D.carrier)
    (hregular : ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> t0 < t -> t ∈ D.regular)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.family.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.family.metric t0) x⟩ 1) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) -> ∀ x : M,
      -6 / (1 + 4 * (t - t0)) ≤ S.scalar t x := by
  intro t ht x
  have hmain := scalar_curvature_lower_bound_compact_flow
    (I := I) (M := M) S hS (by norm_num : 0 < (1 : Real)) hT
    hdim hslab hregular hinit t ht x
  norm_num at hmain ⊢
  simpa [one_mul] using hmain

def CurvatureOperatorRegionPropagationOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (K t0 T : Real) : Prop :=
  ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
    ∃ basis : Module.Basis (Fin 3) Real (TangentSpace I x),
      ∃ _horth : OrthonormalBasisAt (I := I) (S.base.metric t) x basis,
        curvatureOperatorMatrixAt (I := I) x basis
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩ ∈
          hamiltonIveyConvexMatrixRegion K (t - t0)

omit [SigmaCompactSpace M] in
theorem curvatureOperatorRegionPropagationOn_initial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K : Real} (hK : 0 < K)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K) :
    CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 0 := by
  intro t ht x
  have ht_eq : t = t0 := by
    rw [Set.mem_Icc] at ht
    nlinarith [ht.1, ht.2]
  subst t
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    simpa using hdim
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) (S.base.metric t0) x hdimT
  refine ⟨basis, horth, ?_⟩
  simpa using curvatureOperatorMatrixAt_initial_mem_hamiltonIveyConvexMatrixRegion
    (I := I) (M := M) S hK basis horth (hinit x)

theorem scalar_curvature_lower_and_negative_barrier_of_regionPropagation
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real}
    (hprop : CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ < 0 →
        S.scalar t x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) *
            (Real.log ((-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) / K) +
              Real.log (1 + 2 * K * (t - t0)) - 3)) := by
  constructor
  · intro t ht x
    rcases hprop t ht x with ⟨basis, horth, hmem⟩
    let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩
    rcases hmem with ⟨_hM, _hX, hbar⟩
    have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
      (I := I) x basis A
    have hscalar := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
      (I := I) (M := M) S basis horth
    have hsum : S.scalar t x / 2 = ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i := by
      nlinarith
    have hscalar_min :
        scalarSectionalLowerBarrier3 K (t - t0) ≤ S.scalar t x / 2 := by
      have hbar_trace : hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
          (curvatureOperatorMatrixAt (I := I) x basis A).trace := by
        simpa [A, pinchHeight3] using hbar
      have hbar_sum : hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
          ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i := by
        simpa [htrace] using hbar_trace
      have hbar' : hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
          S.scalar t x / 2 := by
        nlinarith [hbar_sum, hsum]
      exact (scalarSectionalLowerBarrier3_le_hamiltonIveyConvexBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2))).trans hbar'
    unfold scalarSectionalLowerBarrier3 at hscalar_min
    have hmul := mul_le_mul_of_nonneg_left hscalar_min (by norm_num : 0 ≤ (2 : Real))
    have hcalc : 2 * (S.scalar t x / 2) = S.scalar t x := by ring
    have hcalc₂ : 2 * (-3 * K / (1 + 4 * K * (t - t0))) =
        -6 * K / (1 + 4 * K * (t - t0)) := by ring
    nlinarith [hmul, hcalc, hcalc₂]
  · intro t ht x hneg
    rcases hprop t ht x with ⟨basis, horth, hmem⟩
    let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
      ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t) x⟩
    rcases hmem with ⟨_hM, _hX, hbar⟩
    have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
      (I := I) x basis A
    have hscalar := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
      (I := I) (M := M) S basis horth
    have hbar' : hamiltonIveyConvexBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
        S.scalar t x / 2 := by
      have hbar_ordered : hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
          (curvatureOperatorMatrixAt (I := I) x basis A).trace := by
        simpa [A, pinchHeight3] using hbar
      have hbar_trace : hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
          ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i := by
        simpa [htrace] using hbar_ordered
      nlinarith [hbar_trace, hscalar]
    have hνeq :
        leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A =
          orderedSectionalCurvaturesAt (I := I) x basis A 2 :=
      leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
        (I := I) (S.base.metric t) x basis horth A
    have hsectionalNeg : orderedSectionalCurvaturesAt (I := I) x basis A 2 < 0 := by
      rw [← hνeq]
      simpa [A] using hneg
    have hmain := scalar_ge_two_mul_negative_sectional_of_convexBarrier
      (I := I) (M := M) S basis horth hsectionalNeg hbar'
    simpa [A, hνeq] using hmain

theorem hamilton_ivey_pinching_of_curvatureOperatorRegionPropagation
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K : Real}
    (hprop : CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 * K / (1 + 4 * K * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ < 0 →
        S.scalar t x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) *
            (Real.log ((-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) / K) +
              Real.log (1 + 2 * K * (t - t0)) - 3)) :=
  scalar_curvature_lower_and_negative_barrier_of_regionPropagation
    (I := I) (M := M) S hprop

theorem hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagation
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T K δ : Real} (hK : 0 < K) (hδ : 0 < δ)
    (hprop : CurvatureOperatorRegionPropagationOn (I := I) (M := M) S K t0 T) :
    ∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩) ≤
        δ * S.scalar t x +
          2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) / (1 + 2 * K * (t - t0)) := by
  intro t ht x
  rcases hprop t ht x with ⟨basis, horth, hmem⟩
  let A : algebraicCurvatureTensorSubmodule (I := I) (M := M) x :=
    ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
      (I := I) (S.base.metric t) x⟩
  rcases hmem with ⟨_hM, _hX, hbar⟩
  have htrace := curvatureOperatorMatrixAt_trace_eq_sum_orderedSectionalCurvaturesAt
    (I := I) x basis A
  have hscalar := scalar_eq_two_mul_sum_orderedSectionalCurvaturesAt
    (I := I) (M := M) S basis horth
  have hbar_ordered : hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
      (curvatureOperatorMatrixAt (I := I) x basis A).trace := by
    simpa [A, pinchHeight3] using hbar
  have hbar_trace : hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
      ∑ i : Fin 3, orderedSectionalCurvaturesAt (I := I) x basis A i := by
    simpa [htrace] using hbar_ordered
  have hconv : hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
      S.scalar t x / 2 := by
    nlinarith [hbar_trace, hscalar]
  have hνeq :
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A =
        orderedSectionalCurvaturesAt (I := I) x basis A 2 :=
    leastCurvatureOperatorEigenvalueAt_eq_sectionalMin
      (I := I) (S.base.metric t) x basis horth A
  have hbarrier : hamiltonIveyBarrier K (t - t0)
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
        (S.base.metric t) x A)) ≤
      S.scalar t x / 2 := by
    have hle := hamiltonIveyBarrier_le_hamiltonIveyConvexBarrier K (t - t0)
      (pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I)
        (S.base.metric t) x A))
    have hle' : hamiltonIveyBarrier K (t - t0)
        (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) ≤
        hamiltonIveyConvexBarrier K (t - t0)
          (pinchHeight3 (orderedSectionalCurvaturesAt (I := I) x basis A 2)) := by
      simpa [hνeq] using hle
    simpa [hνeq] using hle'.trans hconv
  have hτ : 0 ≤ t - t0 := by linarith [ht.1]
  simpa [A] using sectionalCurvature_asymptotic_pinching_of_barrier
    (I := I) (M := M) S (K := K) (δ := δ) (ν :=
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x A)
      hK hδ hτ hbarrier

theorem hamilton_ivey_pinching_K_one_of_curvatureOperatorRegionPropagation
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 T : Real}
    (hprop : CurvatureOperatorRegionPropagationOn (I := I) (M := M) S 1 t0 T) :
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      -6 / (1 + 4 * (t - t0)) ≤ S.scalar t x) ∧
    (∀ t : Real, t ∈ Set.Icc t0 (t0 + T) → ∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
          ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t) x⟩ < 0 →
        S.scalar t x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
            ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t) x⟩) *
            (Real.log (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t) x
              ⟨S.base.rm04 t x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t) x⟩) +
              Real.log (1 + 2 * (t - t0)) - 3)) := by
  have hmain := hamilton_ivey_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S (K := 1) hprop
  constructor
  · intro t ht x
    have h := hmain.1 t ht x
    norm_num at h ⊢
    simpa [one_mul] using h
  · intro t ht x hneg
    have h := hmain.2 t ht x hneg
    norm_num at h ⊢
    simpa [one_mul] using h

theorem hamilton_ivey_pinching_initial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K : Real} (hK : 0 < K)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K) :
    (∀ x : M, -6 * K ≤ S.scalar t0 x) ∧
    (∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
          ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t0) x⟩ < 0 →
        S.scalar t0 x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
            ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t0) x⟩) *
            (Real.log ((-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
              ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t0) x⟩) / K) -
              3)) := by
  have hprop := curvatureOperatorRegionPropagationOn_initial
    (I := I) (M := M) S hK hdim hinit
  have hmain := hamilton_ivey_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S hprop
  constructor
  · intro x
    have h := hmain.1 t0 (by rw [Set.mem_Icc]; constructor <;> linarith) x
    have hτ : t0 - t0 = 0 := by ring
    rw [hτ] at h
    norm_num at h
    simpa [one_div] using h
  · intro x hneg
    have h := hmain.2 t0 (by rw [Set.mem_Icc]; constructor <;> linarith) x hneg
    have hτ : t0 - t0 = 0 := by ring
    rw [hτ] at h
    norm_num at h
    simpa [one_div] using h


theorem hamilton_ivey_pinching_initial_K_one
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 : Real}
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ 1) :
    (∀ x : M, -6 ≤ S.scalar t0 x) ∧
    (∀ x : M,
      leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
          ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t0) x⟩ < 0 →
        S.scalar t0 x ≥
          2 * (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
            ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (S.base.metric t0) x⟩) *
            (Real.log (-leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
              ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) (S.base.metric t0) x⟩) - 3)) := by
  have hmain := hamilton_ivey_pinching_initial
    (I := I) (M := M) S (by norm_num : 0 < (1 : Real)) hdim hinit
  constructor
  · intro x
    have h := hmain.1 x
    norm_num at h ⊢
    simpa [one_mul] using h
  · intro x hneg
    have h := hmain.2 x hneg
    norm_num at h ⊢
    simpa [one_mul] using h


theorem hamilton_ivey_asymptotic_pinching_initial
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {t0 K δ : Real} (hK : 0 < K) (hδ : 0 < δ)
    (hdim : Module.finrank Real E = 3)
    (hinit : ∀ x : M, CurvatureOperatorLowerBoundAt (I := I) (S.base.metric t0) x
      ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
        (I := I) (S.base.metric t0) x⟩ K) :
    ∀ x : M,
      pinchHeight3 (leastCurvatureOperatorEigenvalueAt (I := I) (S.base.metric t0) x
        ⟨S.base.rm04 t0 x, metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (S.base.metric t0) x⟩) ≤
        δ * S.scalar t0 x + 2 * δ * K * Real.exp (2 + (2 * δ)⁻¹) := by
  have hprop := curvatureOperatorRegionPropagationOn_initial
    (I := I) (M := M) S hK hdim hinit
  have hmain := hamilton_ivey_asymptotic_pinching_of_curvatureOperatorRegionPropagation
    (I := I) (M := M) S hK hδ hprop
  intro x
  simpa using hmain t0 (by rw [Set.mem_Icc]; constructor <;> linarith) x


end DifferentialGeometry.PDE.RicciFlow
