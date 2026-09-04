import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Alternative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.BeforeCutTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bornology Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

def lInjDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set E :=
  {Z | ∃ sigma > tau, (Z, sigma) ∈ lMinDomain S T x}

theorem lInj_isOpen
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) :
    IsOpen (lInjDomain S T x tau) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  obtain ⟨sigma, hsigma, hZmin⟩ := hZ
  have hsigmaPos : 0 < sigma := lMinDomain_pos S T x Z sigma hZmin
  have hmaxS : max tau 0 < sigma := max_lt hsigma hsigmaPos
  let rho : Real := (max tau 0 + sigma) / 2
  have htRho : tau < rho := by
    dsimp only [rho]
    linarith [le_max_left tau 0, hmaxS]
  have hRhoS : rho < sigma := by
    dsimp only [rho]
    linarith [hmaxS]
  have hrho : 0 < rho := by
    dsimp only [rho]
    linarith [le_max_right tau 0, hmaxS]
  have hZrho : (Z, rho) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hZmin hrho hRhoS.le
  have hZdom : (Z, rho) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z rho).1 hZrho).1
  by_contra hnot
  have hcl : Z ∈ closure (lInjDomain S T x tau)ᶜ := by
    rw [mem_closure_iff_nhds]
    intro U hU
    by_contra hempty
    have hsub : U ⊆ lInjDomain S T x tau := by
      intro q hq
      by_contra hqnot
      exact hempty ⟨q, hq, hqnot⟩
    exact hnot (mem_of_superset hU hsub)
  choose Q hQnot hQdist using fun n : Nat ↦
    (Metric.mem_closure_iff.1 hcl (1 / ((n : Real) + 1)) (by positivity))
  have hQlim : Tendsto Q atTop (nhds Z) := by
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ dist_nonneg
    · exact Filter.Eventually.of_forall fun n ↦ by
        simpa only [dist_comm] using (hQdist n).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  let U : Set E := (fun W : E ↦ (W, rho)) ⁻¹' lExpPosDom S T x
  have hUopen : IsOpen U := by
    apply (lExpPosDom_open S hS T x).preimage
    exact continuous_id.prodMk continuous_const
  have hZU : Z ∈ U := by
    simpa only [U, mem_preimage] using hZdom
  have hQU : ∀ᶠ n in atTop, Q n ∈ U :=
    hQlim.eventually (hUopen.mem_nhds hZU)
  obtain ⟨N, hNU⟩ := eventually_atTop.1 hQU
  let V : Nat → E := fun n ↦ Q (n + N)
  have hVlim : Tendsto V atTop (nhds Z) := by
    simpa only [V, Function.comp_def] using
      hQlim.comp (tendsto_add_atTop_nat N)
  have hVnot (n : Nat) : V n ∉ lInjDomain S T x tau :=
    hQnot (n + N)
  have hVdom (n : Nat) : (V n, rho) ∈ lExpPosDom S T x := by
    have hmem := hNU (n + N) (by omega)
    simpa only [U, V, mem_preimage] using hmem
  have hminExists (n : Nat) :
      ∃ W : TangentSpace I x,
        (W, rho) ∈ lMinDomain S T x ∧
          lExp S T x W rho = lExp S T x (V n) rho :=
    exists_lMinimizingVector_ray S hS T x (V n) rho (hVdom n)
  let W : Nat → TangentSpace I x := fun n ↦ (hminExists n).choose
  have hWmin (n : Nat) : (W n, rho) ∈ lMinDomain S T x :=
    (hminExists n).choose_spec.1
  have hWend (n : Nat) :
      lExp S T x (W n) rho = lExp S T x (V n) rho :=
    (hminExists n).choose_spec.2
  let b : Real := Real.sqrt rho
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 hrho
  have hb2 : b ^ 2 = rho := by
    simpa only [b] using Real.sq_sqrt hrho.le
  have hslab : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ rho := by
      rw [hb2] at hr
      linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ Icc (0 : Real) (Real.sqrt rho) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    have hreg := lExpPosDom_regularity S T x Z hZdom hsqrt
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hreg
  have hWdom (n : Nat) : b ∈ lRegularizedDomain S T x (W n) := by
    have hdata := (mem_lExpPosDom S T x (W n) rho).1
      ((mem_lMinDomain S T x (W n) rho).1 (hWmin n)).1
    simpa only [b] using hdata.2.2
  have hVreg (n : Nat) : b ∈ lRegularizedDomain S T x (V n) := by
    have hdata := (mem_lExpPosDom S T x (V n) rho).1 (hVdom n)
    simpa only [b] using hdata.2.2
  let aV : Nat → Real := fun n ↦
    lRegularizedAction S T (lRegularizedCurve S T x (V n)) 0 b
  have haVlim : Tendsto aV atTop
      (nhds (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b)) := by
    have hcontinuous := continuousAt_lRegularizedAction_lRegularizedCurve (I := I) S hS T x hb
      (by simpa only [b] using ((mem_lExpPosDom S T x Z rho).1 hZdom).2.2)
    have hresult := hcontinuous.tendsto.comp
      (hVlim.prodMk_nhds
        (tendsto_const_nhds : Tendsto (fun _ : Nat ↦ b) atTop (nhds b)))
    change Tendsto
      (fun n ↦ lRegularizedAction S T (lRegularizedCurve S T x (V n)) 0 b)
      atTop (nhds (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b)) at hresult
    simpa only [aV] using hresult
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto aV haVlim).bddAbove
  have hWact (n : Nat) :
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b ≤ A := by
    have hminEq := ((mem_lMinDomain S T x (W n) rho).1 (hWmin n)).2
    have hcostEq :
        lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b =
          lCost S T x (lExp S T x (W n) rho) rho := by
      calc
        lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b =
            lLength S T (squareRootReparametrization (lRegularizedCurve S T x (W n))) 0 rho := by
          simpa only [b] using
            (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x (W n)) rho hrho.le).symm
        _ = lCost S T x (lExp S T x (W n) rho) rho := by
          change lLength S T (squareRootReparametrization (lRegularizedCurve S T x (W n))) 0 rho =
            lCost S T x (lRegularizedCurve S T x (W n) (Real.sqrt rho)) rho
          exact hminEq
    have hcostLe := lCost_le_ray (I := I) S hS T x (V n) b hb (hVreg n)
    have hcostLe' :
        lCost S T x (lExp S T x (V n) rho) rho ≤ aV n := by
      simpa only [lExp, b, aV, hb2] using hcostLe
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b =
          lCost S T x (lExp S T x (W n) rho) rho := hcostEq
      _ = lCost S T x (lExp S T x (V n) rho) rho := by rw [hWend n]
      _ ≤ aV n := hcostLe'
      _ ≤ A := hA (Set.mem_range_self n)
  have hWbounded : Bornology.IsBounded (Set.range W) :=
    isBounded_range_initialVector_of_lRegularizedAction_le (I := I) S hS T x W (fun _ : Nat ↦ b) b b A hb
      (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) hslab hWdom hWact
  let : ProperSpace (TangentSpace I x) := FiniteDimensional.proper Real _
  obtain ⟨W0, _hW0cl, phi, hphi, hWlim⟩ :=
    tendsto_subseq_of_bounded hWbounded (fun n ↦ Set.mem_range_self n)
  have hW0reg : b ∈ lRegularizedDomain S T x W0 :=
    mem_lRegularizedDomain_of_time_slab S hS T x W0 b hb.le hslab
  have hW0dom : (W0, rho) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x W0 rho).2 ⟨hrho, hrho.le, hW0reg⟩
  have hW0min : (W0, rho) ∈ lMinDomain S T x :=
    lMinimizingVector_lim S hS T x (fun n ↦ hWmin (phi n)) hWlim hW0dom
  have hVsub : Tendsto (fun n ↦ V (phi n)) atTop (nhds Z) :=
    hVlim.comp hphi.tendsto_atTop
  have hWpair : Tendsto (fun n ↦ (W (phi n), rho)) atTop
      (nhds (W0, rho)) := hWlim.prodMk_nhds tendsto_const_nhds
  have hVpair : Tendsto (fun n ↦ (V (phi n), rho)) atTop
      (nhds (Z, rho)) := hVsub.prodMk_nhds tendsto_const_nhds
  have hWExpAt : ContinuousAt
      (fun p : E × Real ↦ lExp S T x p.1 p.2) (W0, rho) :=
    ((lExp_smoothOn S hS T x) (W0, rho) hW0dom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hW0dom)
  have hVExpAt : ContinuousAt
      (fun p : E × Real ↦ lExp S T x p.1 p.2) (Z, rho) :=
    ((lExp_smoothOn S hS T x) (Z, rho) hZdom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hZdom)
  have hWExpLim : Tendsto (fun n ↦ lExp S T x (W (phi n)) rho) atTop
      (nhds (lExp S T x W0 rho)) := by
    change Tendsto
      ((fun p : E × Real ↦ lExp S T x p.1 p.2) ∘
        fun n ↦ (W (phi n), rho)) atTop (nhds (lExp S T x W0 rho))
    exact hWExpAt.tendsto.comp hWpair
  have hVExpLim : Tendsto (fun n ↦ lExp S T x (V (phi n)) rho) atTop
      (nhds (lExp S T x Z rho)) := by
    change Tendsto
      ((fun p : E × Real ↦ lExp S T x p.1 p.2) ∘
        fun n ↦ (V (phi n), rho)) atTop (nhds (lExp S T x Z rho))
    exact hVExpAt.tendsto.comp hVpair
  have hend0 : lExp S T x W0 rho = lExp S T x Z rho := by
    apply tendsto_nhds_unique hWExpLim
    exact hVExpLim.congr'
      (Filter.Eventually.of_forall fun n ↦ (hWend (phi n)).symm)
  have hW0eq : W0 = Z :=
    lMinimizingVector_unique_lt S hS T x (Z := Z) (W := W0)
      hZmin hrho hRhoS hW0min hend0
  have hlocal := lExp_localDiffeo S hS T x Z rho hZdom
    (lMinimizingVector_nconj_lt S hS T x hZmin hRhoS)
  obtain ⟨Phi, hPhiSource, hPhiEq⟩ := hlocal
  have hWsubZ : Tendsto (fun n ↦ W (phi n)) atTop (nhds Z) := by
    change Tendsto (W ∘ phi) atTop (nhds Z)
    rw [← hW0eq]
    exact hWlim
  have hWsrc : ∀ᶠ n in atTop, W (phi n) ∈ Phi.source :=
    hWsubZ.eventually (Phi.open_source.mem_nhds hPhiSource)
  have hVsrc : ∀ᶠ n in atTop, V (phi n) ∈ Phi.source :=
    hVsub.eventually (Phi.open_source.mem_nhds hPhiSource)
  obtain ⟨n, hnW, hnV⟩ := (hWsrc.and hVsrc).exists
  have hEq : W (phi n) = V (phi n) := by
    apply Phi.injOn hnW hnV
    rw [← hPhiEq hnW, ← hPhiEq hnV]
    exact hWend (phi n)
  apply hVnot (phi n)
  refine ⟨rho, htRho, ?_⟩
  have hm := hWmin (phi n)
  change (show E from W (phi n), rho) ∈ lMinDomain S T x at hm
  rw [hEq] at hm
  exact hm

omit [NeZero (Module.finrank ℝ E)] in
theorem lInj_local
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) {Z : E}
    (hZ : Z ∈ lInjDomain S T x tau) :
    IsLocalDiffeomorphAt 𝓘(Real, E) I ∞
      (fun W : E => lExp S T x W tau) Z := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hconj : ¬ IsLConjugate S T x Z tau :=
    lMinimizingVector_nconj_lt S hS T x hmin hsigma
  exact lExp_localDiffeo S hS T x Z tau hdom hconj

theorem lInj_inj
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    Set.InjOn (fun Z : E => lExp S T x Z tau) (lInjDomain S T x tau) := by
  intro Z hZ W hW hend
  obtain ⟨sigmaZ, hsigmaZ, hZmin⟩ := hZ
  obtain ⟨sigmaW, hsigmaW, hWmin⟩ := hW
  let sigma : Real := min sigmaZ sigmaW
  have htauSigma : tau < sigma := lt_min hsigmaZ hsigmaW
  have hZsigma : (Z, sigma) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hZmin (htau.trans htauSigma) (min_le_left _ _)
  have hWtau : (W, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x W hWmin htau (htauSigma.le.trans (min_le_right _ _))
  exact (lMinimizingVector_unique_lt S hS T x (Z := Z) (W := W)
    hZsigma htau htauSigma hWtau hend.symm).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
