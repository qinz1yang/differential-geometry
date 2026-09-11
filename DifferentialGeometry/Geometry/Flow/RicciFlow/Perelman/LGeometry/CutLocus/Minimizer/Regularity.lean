import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
theorem lMinimizingVector_regularity_min
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (delta : Real → M)
    (hdelta : ContMDiff (modelWithCornersSelf Real Real) I 1 delta)
    (hd0 : delta 0 = lRegularizedCurve S T x Z 0)
    (hdt : delta (Real.sqrt tau) =
      lRegularizedCurve S T x Z (Real.sqrt tau)) :
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) ≤
      lRegularizedAction S T delta 0 (Real.sqrt tau) := by
  have hvec := (mem_lMinDomain S T x Z tau).1 hmin
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lExpPosDom_regularity S T x Z hvec.1 hs
  have hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 hs.2
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have htime : Icc (T - tau) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hleTau : T - r ≤ tau := by linarith [hr.1]
    have hsqrtMem : Real.sqrt (T - r) ∈
        Icc (0 : Real) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hleTau⟩
    have hregR := lExpPosDom_regularity S T x Z hvec.1 hsqrtMem
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heq] using hregR)
  have hcost : lRegularizedAction S T (lRegularizedCurve S T x Z) 0
      (Real.sqrt tau) = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
        (lRegularizedCurve S T x Z (Real.sqrt tau)) := by
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := by
        change _ = lLength S T
          (fun r : Real ↦ lRegularizedCurve S T x Z (Real.sqrt r)) 0 tau
        rw [show (fun r : Real ↦ lRegularizedCurve S T x Z (Real.sqrt r)) =
          squareRootReparametrization (lRegularizedCurve S T x Z) by rfl]
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Z) tau
          htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := hvec.2
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
          (lExp S T x Z tau) :=
        lCost_eq_regularity (I := I) S T x (lExp S T x Z tau) tau htau.le
      _ = lRegularizedCostC1 S T 0 (Real.sqrt tau) x
          (lRegularizedCurve S T x Z (Real.sqrt tau)) := by rfl
  rw [hcost]
  exact lRegularizedCostC1_le (I := I) S hS T (T - tau) T 0
    (Real.sqrt tau) (Real.sqrt_pos.2 htau).le htime hback x
    (lRegularizedCurve S T x Z (Real.sqrt tau)) delta hdelta
    (hd0.trans (by simp only [lRegularizedCurve_zero])) hdt hreg

end DifferentialGeometry.PDE.RicciFlow.Perelman
