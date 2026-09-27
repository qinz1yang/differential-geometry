import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.BranchHessian
import DifferentialGeometry.Geometry.Operator.OrthonormalTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.AdaptedFrame
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Integrability
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [I.Boundaryless] [T2Space M] in
private theorem branch_hess_trace_eq_sum
    (g : SmoothRiemannianMetric I M) (F : M → ℝ) (y : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I y)
    (hON : ∀ i j, g.inner y (e i) (e j) =
      if i = j then (1 : ℝ) else 0) :
    metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g F y) =
      ∑ i : Fin (Module.finrank ℝ E), hessFun (I := I) g F y (e i) (e i) := by
  classical
  have hLI : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h := congrArg (fun v : TangentSpace I y ↦ g.inner y (e i) v) hc
    simpa [map_sum, map_smul, smul_eq_mul, hON] using h
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
      Module.finrank ℝ (TangentSpace I y) := by
    rw [Fintype.card_fin]
    rfl
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I y) :=
    basisOfLinearIndependentOfCardEqFinrank' e hLI hcard
  have hB (i : Fin (Module.finrank ℝ E)) : B i = e i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' e hLI hcard) i
  have hBON : ∀ i j, g.inner y (B i) (B j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hB i, hB j]
    exact hON i j
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g B _
    (metricInverseInBasis_of_orthonormal (I := I) g B hBON)
    (hessTensorAt (I := I) g F y)]
  simp [identityInvMetric, diagonalInvMetric, hessTensorAt_apply, hB]

variable [NeZero (Module.finrank ℝ E)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lActBranch_trace_le_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hbddSigma : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    ∃ hdom : (Z, tau) ∈ lExpPosDom S T x,
      ∃ hconj : ¬ IsLConjugate S T x Z tau,
        metricTracePair0SAt (I := I) (S.base.metric (T - tau))
            (hessTensorAt (I := I) (S.base.metric (T - tau))
              (lActBranch S hS T x Z tau hdom hconj)
              (lExp S T x Z tau)) / (2 * Real.sqrt tau) ≤
          (Module.finrank ℝ E : ℝ) / (2 * tau) -
            S.scalar (T - tau) (lExp S T x Z tau) -
            lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
              (2 * tau * Real.sqrt tau) := by
  classical
  obtain ⟨hdom, hconj, hHess⟩ :=
    lActBranch_hess_le_of_bdd S hS T x hmin htau hlt
      (lRegularizedCosts_prefix_bdd_of_min S hS T x Z hmin htau hlt.le hbddSigma)
      hbddSigma
  refine ⟨hdom, hconj, ?_⟩
  let b : ℝ := Real.sqrt tau
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let y : M := lExp S T x Z tau
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  let F : M → ℝ := lActBranch S hS T x Z tau hdom hconj
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hbdom : b ∈ lRegularizedDomain S T x Z :=
    ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  obtain ⟨P, Ω, hΩ, hseg, hPsm, hDPΩ, hON⟩ :=
    exists_lRegularizedCurve_adaptedFrame (I := I) S hS T x hb hbdom
  let W : Fin (Module.finrank ℝ E) →
      ∀ s, TangentSpace I (alpha s) :=
    fun i s ↦ (s / b) • P i s
  have hPtwo (i : Fin (Module.finrank ℝ E)) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 2
        (fun s : ℝ ↦
          (TotalSpace.mk' E
            (E := (TangentSpace I : M → Type _))
            (alpha s) (P i s) : TangentBundle I M)) Ω :=
    (hPsm i).of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hWsm (i : Fin (Module.finrank ℝ E)) :
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent (8 : ℕ)
        (fun s : ℝ ↦
          (TotalSpace.mk' E
            (E := (TangentSpace I : M → Type _))
            (alpha s) (W i s) : TangentBundle I M)) Ω := by
    intro s hs
    apply ContMDiffAt.contMDiffWithinAt
    have hsec :=
      ((hPsm i s hs).contMDiffAt (hΩ.mem_nhds hs)).of_le
        (by decide :
          (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    have hc : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 8
        (fun r : ℝ ↦ r / b) s :=
      (contMDiff_id.div_const b).contMDiffAt
    rw [Bundle.contMDiffAt_totalSpace] at hsec ⊢
    refine ⟨hsec.1, ?_⟩
    let e := trivializationAt E (TangentSpace I) (alpha s)
    apply (hc.smul hsec.2).congr_of_eventuallyEq
    have he : ∀ᶠ r in 𝓝 s, alpha r ∈ e.baseSet := by
      apply hsec.1.continuousAt
      exact e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (alpha s))
    filter_upwards [he] with r hr
    change (e ⟨alpha r, (r / b) • P i r⟩).2 =
      (r / b) • (e ⟨alpha r, P i r⟩).2
    exact (e.linear ℝ hr).map_smul (r / b) (P i r)
  have hPdiff (i : Fin (Module.finrank ℝ E)) (s : ℝ)
      (hs : s ∈ Icc (0 : ℝ) b) :
      DifferentiableAt ℝ (chartRepAt (I := I) alpha (P i) s) s :=
    differentiableAt_chartRepAt_of_contMDiffAt_two (I := I)
      ((hPtwo i s (hseg hs)).contMDiffAt
        (hΩ.mem_nhds (hseg hs)))
  have halpha (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I alpha s := by
    have hsec := (hPtwo 0 s (hseg hs)).contMDiffAt
      (hΩ.mem_nhds (hseg hs))
    exact (Bundle.contMDiffAt_totalSpace.mp hsec).1.mdifferentiableAt
      (by norm_num)
  have hreg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ D.regular :=
    lRegularizedDomain_regularity S T x Z
      (lRegularizedDomain_segment S T x Z hbdom hs.1 hs.2)
  have hDP (i : Fin (Module.finrank ℝ E)) (s : ℝ)
      (hs : s ∈ Icc (0 : ℝ) b) :
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          alpha (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (alpha s) (P i s) :=
    hDPΩ i s (hseg hs)
  have huseg : uIcc (0 : ℝ) b ⊆ Ω := by
    simpa only [uIcc_of_le hb.le] using hseg
  have hIint (i : Fin (Module.finrank ℝ E)) :
      IntervalIntegrable
        (fun s : ℝ ↦ (s / b) ^ 2 *
          lRegularizedIndexIntegrand S T alpha (P i) (P i) s)
        MeasureTheory.volume 0 b := by
    have hi := intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn (I := I) S hS T 0 b alpha
      (P i) (P i) hΩ huseg (hPtwo i) (hPtwo i)
      (fun s hs ↦ hreg s (by
        simpa only [uIcc_of_le hb.le] using hs))
    exact hi.continuousOn_mul
      ((continuous_id.div_const b).pow 2).continuousOn
  have hRint (i : Fin (Module.finrank ℝ E)) :
      IntervalIntegrable
        (fun s : ℝ ↦ (2 * s ^ 2 / b ^ 2) *
          S.ricciAt (T - s ^ 2) (alpha s)
            (vec2 (P i s) (P i s)))
        MeasureTheory.volume 0 b := by
    let A : Set ℝ := Icc (0 : ℝ) b
    have hsec : Continuous (fun u : A ↦
        (TotalSpace.mk' E (alpha u) (P i u) : TangentBundle I M)) :=
      ((hPsm i).continuousOn.mono hseg).domRestrict
    have hbase : Continuous (fun u : A ↦ alpha u) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).comp hsec
    have htime : Continuous (fun u : A ↦ T - (u : ℝ) ^ 2) :=
      continuous_const.sub (continuous_subtype_val.pow 2)
    have heval := hS.ricciCont.eval_continuous
      (P := A) htime
      (fun u ↦ D.regular_subset (hreg u u.2)) hbase
      (v := fun k u ↦ vec2 (P i u) (P i u) k) (by
        intro k
        fin_cases k <;> exact hsec)
    have hric : ContinuousOn
        (fun s : ℝ ↦ S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (P i s) (P i s))) A := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact heval
    have hc : Continuous (fun s : ℝ ↦ 2 * s ^ 2 / b ^ 2) :=
      (continuous_const.mul (continuous_id.pow 2)).div_const _
    exact (hc.continuousOn.mul hric).intervalIntegrable_of_Icc hb.le
  have hONtau : ∀ i j,
      g.inner y (P i b) (P j b) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    have hout := hON i j
    rw [hb2] at hout
    change g.inner y (P i b) (P j b) =
      (if i = j then (1 : ℝ) else 0) at hout
    exact hout
  have hfield (i : Fin (Module.finrank ℝ E)) :
      hessFun (I := I) g F y (P i b) (P i b) ≤
        2 * lRegularizedIndex S T alpha (W i) (W i) 0 b := by
    have hW0 : W i 0 = 0 := by
      simp only [W, zero_div, zero_smul]
    have hWb : W i b = P i b := by
      simp only [W, div_self hb.ne', one_smul]
    exact hHess (P i b) (W i) hΩ hseg (hWsm i) hW0 hWb
  have hsum :
      metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g F y) ≤
        2 * ∑ i : Fin (Module.finrank ℝ E),
          lRegularizedIndex S T alpha (W i) (W i) 0 b := by
    rw [branch_hess_trace_eq_sum g F y (fun i ↦ P i b) hONtau]
    calc
      (∑ i : Fin (Module.finrank ℝ E),
          hessFun (I := I) g F y (P i b) (P i b)) ≤
          ∑ i : Fin (Module.finrank ℝ E),
            2 * lRegularizedIndex S T alpha (W i) (W i) 0 b :=
        Finset.sum_le_sum fun i _hi ↦ hfield i
      _ = 2 * ∑ i : Fin (Module.finrank ℝ E),
          lRegularizedIndex S T alpha (W i) (W i) 0 b := by
        rw [Finset.mul_sum]
  have hindex := lRegularizedIndex_trace_linear_cutoff_zero (I := I) S hS T alpha P b hb
    hreg halpha hPdiff hDP hON hIint hRint
  have htrace := lTraceInt_eq (I := I) S hS T x Z hb hbdom P
    hPdiff hDP hON hIint
  change
    metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g F y) /
        (2 * b) ≤
      (Module.finrank ℝ E : ℝ) / (2 * tau) -
        S.scalar (T - tau) y -
        lK S T alpha b / (2 * tau * b)
  calc
    metricTracePair0SAt (I := I) g (hessTensorAt (I := I) g F y) /
        (2 * b) ≤
        (2 * ∑ i : Fin (Module.finrank ℝ E),
          lRegularizedIndex S T alpha (W i) (W i) 0 b) / (2 * b) :=
      div_le_div_of_nonneg_right hsum (mul_pos (by norm_num) hb).le
    _ = (∑ i : Fin (Module.finrank ℝ E),
        lRegularizedIndex S T alpha (W i) (W i) 0 b) / b := by
      field_simp [hb.ne']
    _ = ((Module.finrank ℝ E : ℝ) / (2 * b) +
        (-b * S.scalar (T - b ^ 2) (alpha b) -
          lK S T alpha b / (2 * b ^ 2))) / b := by
      change
        (∑ i : Fin (Module.finrank ℝ E),
          lRegularizedIndex S T alpha
            (fun s ↦ (s / b) • P i s)
            (fun s ↦ (s / b) • P i s) 0 b) / b = _
      rw [hindex, htrace]
    _ = (Module.finrank ℝ E : ℝ) / (2 * tau) -
        S.scalar (T - tau) y -
        lK S T alpha b / (2 * tau * b) := by
      rw [show T - b ^ 2 = T - tau by rw [hb2],
        show alpha b = y by rfl]
      rw [← hb2]
      field_simp [hb.ne']
      ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lActBranch_trace_le_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (htau : 0 < tau) (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    ∃ hdom : (Z, tau) ∈ lExpPosDom S T x,
      ∃ hconj : ¬ IsLConjugate S T x Z tau,
        metricTracePair0SAt (I := I) (S.base.metric (T - tau))
            (hessTensorAt (I := I) (S.base.metric (T - tau))
              (lActBranch S hS T x Z tau hdom hconj)
              (lExp S T x Z tau)) / (2 * Real.sqrt tau) ≤
          (Module.finrank ℝ E : ℝ) / (2 * tau) -
            S.scalar (T - tau) (lExp S T x Z tau) -
            lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
              (2 * tau * Real.sqrt tau) := by
  apply lActBranch_trace_le_of_bdd S hS T x hmin htau hlt
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
    (by simpa only [Real.sq_sqrt hsigma.le] using hRm)
    x (lExp S T x Z sigma)

end DifferentialGeometry.PDE.RicciFlow
