import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CostLocalBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import Mathlib.Analysis.Normed.Group.Bounded
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

theorem lMinVec_local_bdd_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (tau : ℝ) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K)
    (x y : M) :
    ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Z : TangentSpace I x,
          (Z, tau) ∈ lMinDomain S T x →
          lExp S T x Z tau ∈ U →
          ‖(Z : E)‖ ≤ C := by
  classical
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hb2] using hreg
  have hRmSq : ∀ t ∈ Icc (T - b ^ 2) T, ∀ q : M,
      normSq0S (I := I) (S.base.metric t) q 4
        (S.base.rm04 t q) ≤ K := by
    simpa only [hb2] using hRm
  obtain ⟨A, hA⟩ :=
    lCost_locally_bddAbove_of_rm (I := I) S hS K T tau htau
      hreg hRm x y
  obtain ⟨U, hUcost, hUopen, hyU⟩ := mem_nhds_iff.mp hA
  refine ⟨U, hUopen, hyU, ?_⟩
  by_contra hbound
  push Not at hbound
  choose Z hZmin hZend hZnorm using
    fun n : ℕ => hbound (n : ℝ) (Nat.cast_nonneg n)
  have hdom (n : ℕ) : b ∈ lRegularizedDomain S T x (Z n) := by
    have hn : (Z n, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x (Z n) tau).1 (hZmin n)).1
    exact ((mem_lExpPosDom S T x (Z n) tau).1 hn).2.2
  have hact (n : ℕ) :
      lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A := by
    have hn := ((mem_lMinDomain S T x (Z n) tau).1 (hZmin n)).2
    have heq :
        lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b =
          lCost S T x (lExp S T x (Z n) tau) tau := by
      calc
        lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b =
            lLength S T
              (squareRootReparametrization (lRegularizedCurve S T x (Z n))) 0 tau := by
          simpa only [b] using
            (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
              (lRegularizedCurve S T x (Z n)) tau htau.le).symm
        _ = lCost S T x (lExp S T x (Z n) tau) tau := by
          rw [show squareRootReparametrization (lRegularizedCurve S T x (Z n)) =
            (fun r => lRegularizedCurve S T x (Z n) (Real.sqrt r)) by rfl]
          simpa only [lExp] using hn
    rw [heq]
    exact (hUcost (hZend n)).le
  have hbounded : Bornology.IsBounded
      (range (fun n : ℕ => (Z n : E))) := by
    exact lRegInit_bound_of_rm (I := I) S hS K T hg x b A hb
      hregSq hRmSq Z hdom hact
  obtain ⟨C, hC⟩ := hbounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hnorm : ‖(Z n : E)‖ ≤ C :=
    hC (Z n : E) ⟨n, rfl⟩
  exact (not_lt_of_ge hnorm) (hn.trans (hZnorm n))

end DifferentialGeometry.PDE.RicciFlow

end
