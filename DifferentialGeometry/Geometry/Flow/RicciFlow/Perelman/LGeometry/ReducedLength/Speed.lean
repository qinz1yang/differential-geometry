import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

section Attainment

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lSpeedSq_lExp_eq_of_lLength_eq_lCost
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hdom : (Z, tau) ∈ lExpPosDom (I := I) S T x)
    (hcost : lLength S T (fun r : Real => lExp S T x Z r) 0 tau =
      lCost S T x (lExp S T x Z tau) tau) :
    lSpeedSq S T (fun r : Real => lExp S T x Z r) tau =
      redLength S T x (lExp S T x Z tau) tau / tau -
        S.scalar (T - tau) (lExp S T x Z tau) -
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (tau * Real.sqrt tau) := by
  have htau : 0 < tau := ((mem_lExpPosDom S T x Z tau).1 hdom).1
  have hExpDom : tau ∈ lExpDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).2
  have hregDom : Real.sqrt tau ∈ lRegularizedDomain S T x Z := hExpDom.2
  have hs : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hlen :
      lLength S T (fun r : Real => lExp S T x Z r) 0 tau =
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) := by
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau = _
    exact lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau htau.le
  have hact :
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
        (2 * Real.sqrt tau) * redLength S T x (lExp S T x Z tau) tau := by
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : Real => lExp S T x Z r) 0 tau := hlen.symm
      _ = lCost S T x (lExp S T x Z tau) tau := hcost
      _ = (2 * Real.sqrt tau) * redLength S T x (lExp S T x Z tau) tau :=
        by
          dsimp only [redLength]
          field_simp [hs.ne']
  have hK := lK_ray_energy S hS T x Z hs hregDom
  rw [hact] at hK
  have hvel := lExp_velocity_sqrt (I := I) S T x Z htau
  have hmetric :
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          ((2 * Real.sqrt tau) •
            lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
          ((2 * Real.sqrt tau) •
            lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) =
        4 * tau *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) := by
    calc
      _ = (2 * Real.sqrt tau) * (2 * Real.sqrt tau) *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) :=
        metric_smul2 (I := I) (S.base.metric (T - tau))
          (2 * Real.sqrt tau)
          (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
      _ = 4 * (Real.sqrt tau) ^ 2 *
          (S.base.metric (T - tau)).inner (lExp S T x Z tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau)
            (lVelocity (I := I) (fun r : Real => lExp S T x Z r) tau) := by
        ring
      _ = _ := by rw [Real.sq_sqrt htau.le]
  have hlag :
      lRegularizedLagrangian S T (lRegularizedCurve S T x Z) (Real.sqrt tau) =
        2 * tau *
          (S.scalar (T - tau) (lExp S T x Z tau) +
            lSpeedSq S T (fun r : Real => lExp S T x Z r) tau) := by
    simp only [lRegularizedLagrangian]
    rw [show lRegularizedCurve S T x Z (Real.sqrt tau) = lExp S T x Z tau from rfl]
    rw [hvel, Real.sq_sqrt htau.le, hmetric]
    simp only [lSpeedSq]
    ring
  rw [hlag] at hK
  have hs0 : Real.sqrt tau ≠ 0 := hs.ne'
  field_simp [htau.ne', hs0]
  nlinarith [hK, Real.sq_sqrt htau.le]

end Attainment

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

theorem lSpeedSq_lExp_eq_of_mem_lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x) :
    lSpeedSq S T (fun r : Real => lExp S T x Z r) tau =
      redLength S T x (lExp S T x Z tau) tau / tau -
        S.scalar (T - tau) (lExp S T x Z tau) -
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (tau * Real.sqrt tau) :=
  lSpeedSq_lExp_eq_of_lLength_eq_lCost S hS T x
    ((mem_lMinDomain S T x Z tau).1 hmin).1
    ((mem_lMinDomain S T x Z tau).1 hmin).2

end DifferentialGeometry.PDE.RicciFlow.Perelman
