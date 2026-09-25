import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.EndpointVariation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
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

theorem redLength_ray_K_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hsigma : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    HasDerivAt
      (fun r ↦ redLength S T x (lExp S T x Z r) r)
      (-lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau)) tau := by
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    lExpPosDom_down S T x Z
      (((mem_lMinDomain S T x Z sigma).1 hmin).1)
      htau hsigma.le
  let z : E := Z
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let b : ℝ := Real.sqrt tau
  let c : ℝ := lRegularizedLagrangian S T alpha b / (2 * b)
  have hact :
      HasDerivAt
        (fun r : ℝ ↦ lRegularizedAction S T alpha 0 (Real.sqrt r))
        c tau := by
    let Lz : E →L[ℝ] ℝ :=
      ((S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (lVelocity (I := I) alpha b)).comp
          (mfderiv 𝓘(ℝ, E) I (fun W : E ↦ lExp S T x W tau) z)
    have hJoint : HasFDerivAt
        (fun p : E × ℝ ↦ lRegularizedAction S T (lRegularizedCurve S T x p.1) 0 (Real.sqrt p.2))
        (Lz.comp (ContinuousLinearMap.fst ℝ E ℝ) +
          c • ContinuousLinearMap.snd ℝ E ℝ) (z, tau) := by
      exact hasFDerivAt_lRegularizedAction_lRegularizedCurve_sqrt (I := I) S hS T x Z hdom
    have htins : HasFDerivAt (fun r : ℝ ↦ (z, r))
        (ContinuousLinearMap.inr ℝ E ℝ) tau :=
      hasFDerivAt_prodMk_right z tau
    have hout := (hJoint.comp tau htins).hasDerivAt
    apply hout.congr_deriv
    simp
  have hEq :
      (fun r : ℝ ↦ lRegularizedAction S T alpha 0 (Real.sqrt r))
        =ᶠ[𝓝 tau]
      (fun r ↦ lCost S T x (lExp S T x Z r) r) := by
    filter_upwards
      [eventually_gt_nhds htau, eventually_lt_nhds hsigma]
      with r hrpos hrlt
    have hminr : (Z, r) ∈ lMinDomain S T x :=
      lMinDomain_down_of_bdd (I := I) S hS T x Z
        hmin hrpos hrlt.le (lRegularizedCosts_prefix_bdd_of_min S hS T x Z hmin hrpos hrlt.le hbddSigma)
        hbddSigma
    have hcost := ((mem_lMinDomain S T x Z r).1 hminr).2
    calc
      lRegularizedAction S T alpha 0 (Real.sqrt r) =
          lLength S T (fun q : ℝ ↦ lExp S T x Z q) 0 r := by
        change lRegularizedAction S T alpha 0 (Real.sqrt r) =
          lLength S T (squareRootReparametrization alpha) 0 r
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T alpha r hrpos.le).symm
      _ = lCost S T x (lExp S T x Z r) r := hcost
  have hcost := hact.congr_of_eventuallyEq hEq.symm
  have hbpos : 0 < b := Real.sqrt_pos.2 htau
  have hb0 : b ≠ 0 := hbpos.ne'
  have hbsq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hbdom : b ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  have hcostTau :
      lCost S T x (lExp S T x Z tau) tau =
        lRegularizedAction S T alpha 0 b := by
    simpa only [b] using hEq.self_of_nhds.symm
  have henergy :
      lK S T alpha b =
        (lRegularizedAction S T alpha 0 b -
          b * lRegularizedLagrangian S T alpha b) / 2 := by
    simpa only [alpha] using
      lK_ray_energy (I := I) S hS T x Z hbpos hbdom
  have hden0 : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hquot := hcost.div
    ((Real.hasDerivAt_sqrt htau.ne').const_mul 2) hden0
  have hderiv :
      (c * (2 * b) -
          lCost S T x (lExp S T x Z tau) tau *
            (2 * (1 / (2 * b)))) / (2 * b) ^ 2 =
        -lK S T alpha b / (2 * tau * b) := by
    rw [hcostTau, henergy]
    dsimp only [c]
    field_simp [hb0, htau.ne']
    rw [hbsq]
    ring
  have hquot' :
      HasDerivAt
        (fun r : ℝ ↦
          lCost S T x (lExp S T x Z r) r / (2 * Real.sqrt r))
        (-lK S T alpha b / (2 * tau * b)) tau := by
    apply hquot.congr_deriv
    simpa only [b] using hderiv
  simpa only [redLength, alpha, b] using hquot'

theorem redLength_ray_K_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hsigma : tau < sigma)
    (hRmSigma : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    HasDerivAt
      (fun r ↦ redLength S T x (lExp S T x Z r) r)
      (-lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau)) tau := by
  apply redLength_ray_K_of_bdd S hS T x hmin htau hsigma
  have hsigma : 0 < sigma := lMinDomain_pos S T x Z sigma hmin
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hreg : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith [ht.1]
    have hclock := lExpPosDom_regularity S T x Z hdom
      (show Real.sqrt (T - t) ∈ Icc (0 : ℝ) (Real.sqrt sigma) from
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩)
    rwa [Real.sq_sqrt hnonneg, sub_sub_cancel] at hclock
  exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt sigma)
    le_rfl (Real.sqrt_nonneg sigma)
    (by simpa only [Real.sq_sqrt hsigma.le] using hreg)
    (by simpa only [Real.sq_sqrt hsigma.le] using hRmSigma)
    x (lExp S T x Z sigma)

end DifferentialGeometry.PDE.RicciFlow
