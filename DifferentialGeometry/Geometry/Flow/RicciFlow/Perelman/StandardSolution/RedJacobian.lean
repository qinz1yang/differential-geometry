import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Monotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RedLengthRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ExpDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchTraceBound

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRedLog_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    HasDerivAt (lRedLog S T x Z)
      ((1 / 2 : ℝ) * Matrix.trace
          ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank ℝ E : ℝ) / (2 * tau)) tau := by
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    lExpPosDom_down S T x Z
      (((mem_lMinDomain S T x Z sigma).1 hmin).1)
      htau hlt.le
  have hnconj : ¬ IsLConjugate S T x Z tau :=
    lMinVec_nconj_lt_of_rm (I := I) S hS K T x hmin hlt hRm
  have hJ :=
    lExpJac_log_hasDeriv_of_nonconj
      (I := I) S hS T x Z tau hdom hnconj
  have hL :=
    redLength_ray_K_of_rm (I := I) S hS K T x hmin htau hlt hRm
  let n2 : ℝ := (Module.finrank ℝ E : ℝ) / 2
  have htlog :
      HasDerivAt (fun r : ℝ ↦ n2 * Real.log r)
        (n2 * tau⁻¹) tau :=
    (Real.hasDerivAt_log htau.ne').const_mul n2
  have hout :=
    ((hJ.sub hL).sub htlog).sub_const
      (n2 * Real.log (4 * Real.pi))
  change HasDerivAt (lRedLog S T x Z) _ tau at hout
  apply hout.congr_deriv
  dsimp only [n2]
  field_simp [htau.ne', (Real.sqrt_pos.2 htau).ne']
  ring

theorem lRedJac_hasDeriv_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    HasDerivAt (lReducedJacobian S T x Z)
      (lReducedJacobian S T x Z tau *
        ((1 / 2 : ℝ) * Matrix.trace
            ((lExpGram S T x Z tau)⁻¹ * lExpGramDeriv S T x Z tau) +
          lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau) -
          (Module.finrank ℝ E : ℝ) / (2 * tau))) tau := by
  exact (lRedLog_hasDeriv_of_rm
      (I := I) S hS K T x hmin htau hlt hRm).exp

variable [NeZero (Module.finrank ℝ E)]

theorem lRedLog_deriv_nonpos_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    deriv (lRedLog S T x Z) tau ≤ 0 := by
  rw [(lRedLog_hasDeriv_of_rm
    (I := I) S hS K T x hmin htau hlt hRm).deriv]
  obtain ⟨hdom, hnconj, hbound⟩ :=
    lActBranch_trace_le_of_rm (I := I) S hS K T x hmin htau hlt hRm
  have htrace :=
    lExpTrace_eq_branch (I := I) S hS T x Z tau hdom hnconj
  rw [htrace]
  let A : ℝ :=
    metricTracePair0SAt (I := I) (S.base.metric (T - tau))
      (hessTensorAt (I := I) (S.base.metric (T - tau))
        (lActBranch S hS T x Z tau hdom hnconj)
        (lExp S T x Z tau))
  change A / (2 * Real.sqrt tau) ≤
    (Module.finrank ℝ E : ℝ) / (2 * tau) -
      S.scalar (T - tau) (lExp S T x Z tau) -
      lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau) at hbound
  change (1 / (2 * Real.sqrt tau)) * A +
      S.scalar (T - tau) (lExp S T x Z tau) +
      lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau) -
      (Module.finrank ℝ E : ℝ) / (2 * tau) ≤ 0
  have hfrac :
      (1 / (2 * Real.sqrt tau)) * A =
        A / (2 * Real.sqrt tau) := by ring
  rw [hfrac]
  linarith only [hbound]

theorem lRedJac_deriv_nonpos_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    deriv (lReducedJacobian S T x Z) tau ≤ 0 := by
  have hlog :=
    lRedLog_deriv_nonpos_of_rm
      (I := I) S hS K T x hmin htau hlt hRm
  rw [(lRedLog_hasDeriv_of_rm
    (I := I) S hS K T x hmin htau hlt hRm).deriv] at hlog
  rw [(lRedJac_hasDeriv_of_rm
    (I := I) S hS K T x hmin htau hlt hRm).deriv]
  have hpos : 0 ≤ lReducedJacobian S T x Z tau := by
    exact (Real.exp_pos _).le
  exact mul_nonpos_of_nonneg_of_nonpos hpos hlog

theorem lRedJac_antitoneOn_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    AntitoneOn (lReducedJacobian S T x Z) (Ioo (0 : ℝ) sigma) := by
  have hdiff :
      DifferentiableOn ℝ (lReducedJacobian S T x Z) (Ioo (0 : ℝ) sigma) := by
    intro tau htau
    exact (lRedJac_hasDeriv_of_rm
      (I := I) S hS K T x hmin htau.1 htau.2 hRm).differentiableAt.differentiableWithinAt
  apply antitoneOn_of_deriv_nonpos
    (convex_Ioo (0 : ℝ) sigma) hdiff.continuousOn
  · exact hdiff.mono interior_subset
  · intro tau htau
    have htau' : tau ∈ Ioo (0 : ℝ) sigma := interior_subset htau
    exact lRedJac_deriv_nonpos_of_rm
      (I := I) S hS K T x hmin htau'.1 htau'.2 hRm

end DifferentialGeometry.PDE.RicciFlow
