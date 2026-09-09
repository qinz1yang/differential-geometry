import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem redLength_lExp_le_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {s tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x) (hs : 0 < s) (hst : s ≤ tau)
    (hscalar : ∀ᵐ r ∂volume.restrict (Icc (Real.sqrt s) (Real.sqrt tau)),
      0 ≤ S.scalar (T - r ^ 2) (lRegularizedCurve S T x Z r)) :
    redLength S T x (lExp S T x Z s) s ≤
      (Real.sqrt tau / Real.sqrt s) *
        redLength S T x (lExp S T x Z tau) tau := by
  let alpha : Real → M := lRegularizedCurve S T x Z
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have htauSqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hsqrtLe : Real.sqrt s ≤ Real.sqrt tau := Real.sqrt_le_sqrt hst
  have hminS : (Z, s) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin hs hst
  have hdomTau : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hmin).1
  rcases (mem_lExpPosDom S T x Z tau).1 hdomTau with
    ⟨_htau, _htauNonneg, hdomTau⟩
  have hint : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume 0
      (Real.sqrt tau) := by
    exact intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 (Real.sqrt tau) htauSqrt.le alpha
      (lRegularizedCurve_c1On S hS T x Z hdomTau)
      (fun r hr => lExpPosDom_regularity S T x Z
        ((mem_lMinDomain S T x Z tau).1 hmin).1 hr)
  have hheadInt : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume 0
      (Real.sqrt s) :=
    hint.mono_set (by
      simpa only [uIcc_of_le hsqrt.le, uIcc_of_le htauSqrt.le] using
        (show Icc (0 : Real) (Real.sqrt s) ⊆ Icc (0 : Real) (Real.sqrt tau)
          from fun r hr ↦ ⟨hr.1, hr.2.trans hsqrtLe⟩))
  have htailInt : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume
      (Real.sqrt s) (Real.sqrt tau) :=
    hint.mono_set (by
      simpa only [uIcc_of_le hsqrtLe, uIcc_of_le htauSqrt.le] using
        (show Icc (Real.sqrt s) (Real.sqrt tau) ⊆
            Icc (0 : Real) (Real.sqrt tau)
          from fun r hr ↦ ⟨hsqrt.le.trans hr.1, hr.2⟩))
  have hlag : ∀ᵐ r ∂volume.restrict (Icc (Real.sqrt s) (Real.sqrt tau)),
      0 ≤ lRegularizedLagrangian S T alpha r := by
    filter_upwards [hscalar] with r hr
    have hspeed : 0 ≤ lRegularizedSpeedSq S T alpha r :=
      lRegularizedSpeedSq_nonneg S T alpha r
    have hpot : 0 ≤ S.scalar (T - r ^ 2) (alpha r) := by
      simpa only [alpha] using hr
    dsimp only [lRegularizedLagrangian]
    simpa only [lRegularizedSpeedSq] using
      add_nonneg (mul_nonneg (by norm_num) hspeed)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg r)) hpot)
  have htail : 0 ≤ lRegularizedAction S T alpha (Real.sqrt s) (Real.sqrt tau) := by
    unfold lRegularizedAction
    exact intervalIntegral.integral_nonneg_of_ae_restrict hsqrtLe hlag
  have hact : lRegularizedAction S T alpha 0 (Real.sqrt s) ≤
      lRegularizedAction S T alpha 0 (Real.sqrt tau) := by
    have hadd := lRegularizedAction_add S T alpha 0 (Real.sqrt s) (Real.sqrt tau)
      hheadInt htailInt
    linarith
  have hactS : lRegularizedAction S T alpha 0 (Real.sqrt s) =
      lCost S T x (lExp S T x Z s) s := by
    calc
      lRegularizedAction S T alpha 0 (Real.sqrt s) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 s := by
        change lRegularizedAction S T alpha 0 (Real.sqrt s) =
          lLength S T (squareRootReparametrization alpha) 0 s
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha s hs.le).symm
      _ = lCost S T x (lExp S T x Z s) s :=
        ((mem_lMinDomain S T x Z s).1 hminS).2
  have hactTau : lRegularizedAction S T alpha 0 (Real.sqrt tau) =
      lCost S T x (lExp S T x Z tau) tau := by
    calc
      lRegularizedAction S T alpha 0 (Real.sqrt tau) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := by
        change lRegularizedAction S T alpha 0 (Real.sqrt tau) =
          lLength S T (squareRootReparametrization alpha) 0 tau
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction S T alpha tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau :=
        ((mem_lMinDomain S T x Z tau).1 hmin).2
  have hcost : lCost S T x (lExp S T x Z s) s ≤
      lCost S T x (lExp S T x Z tau) tau := by
    calc
      lCost S T x (lExp S T x Z s) s =
          lRegularizedAction S T alpha 0 (Real.sqrt s) := hactS.symm
      _ ≤ lRegularizedAction S T alpha 0 (Real.sqrt tau) := hact
      _ = lCost S T x (lExp S T x Z tau) tau := hactTau
  calc
    redLength S T x (lExp S T x Z s) s =
        lCost S T x (lExp S T x Z s) s / (2 * Real.sqrt s) := rfl
    _ ≤ lCost S T x (lExp S T x Z tau) tau / (2 * Real.sqrt s) :=
      (div_le_div_iff_of_pos_right (mul_pos (by norm_num) hsqrt)).2 hcost
    _ = (Real.sqrt tau / Real.sqrt s) *
        redLength S T x (lExp S T x Z tau) tau := by
      dsimp only [redLength]
      field_simp [hsqrt.ne', htauSqrt.ne']

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
