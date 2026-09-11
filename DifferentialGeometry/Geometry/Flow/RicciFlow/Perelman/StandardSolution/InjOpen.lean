import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CutAlternativeComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RegDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinNonconjugacy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinUnique
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bornology Bundle Filter Function Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
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

theorem lInj_isOpen_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4
          (S.base.rm04 t z) ≤ K)
    (tau : ℝ) :
    IsOpen (lInjDomain S T x tau) := by
  classical
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  obtain ⟨sigma, hsigma, hZmin⟩ := hZ
  have hsigmaPos : 0 < sigma := lMinDomain_pos S T x Z sigma hZmin
  have hZsigmaDom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hZmin).1
  have hregSigma : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by linarith only [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈ Icc (0 : Real) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hZsigmaDom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  obtain ⟨K, hK⟩ := hRm sigma hsigmaPos hregSigma
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
    lMinDomain_down_of_rm S hS K T x Z hZmin hrho hRhoS.le hK
  have hZdom : (Z, rho) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z rho).1 hZrho).1
  have hsub : Icc (T - rho) T ⊆ Icc (T - sigma) T := by
    intro t ht
    exact ⟨(sub_le_sub_left hRhoS.le T).trans ht.1, ht.2⟩
  have hregRho : Icc (T - rho) T ⊆ D.regular :=
    fun _ ht ↦ hregSigma (hsub ht)
  have hKRho : ∀ t ∈ Icc (T - rho) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K :=
    fun t ht y ↦ hK t (hsub ht) y
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
    exists_lMinVec_ray_of_rm S hS K T hg x (V n) rho
      (hVdom n) hregRho hKRho
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
    simpa only [hb2] using hregRho
  have hKslab : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := by
    simpa only [hb2] using hKRho
  have hbdd (y : M) :
      BddBelow {r : Real | ∃ alpha : Real → M,
        ContMDiff 𝓘(Real, Real) I 1 alpha ∧
          alpha 0 = x ∧ alpha b = y ∧
          lRegularizedAction S T alpha 0 b = r} :=
    lRegularizedCosts_bdd_rm (I := I) S hS K T 0 b (by norm_num)
      hb.le hslab hKslab x y
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
    have hbDom : b ∈ lRegularizedDomain S T x Z := by
      simpa only [b] using ((mem_lExpPosDom S T x Z rho).1 hZdom).2.2
    have hpair : Tendsto (fun n ↦ (V n, b)) atTop (nhds (Z, b)) :=
      hVlim.prodMk_nhds tendsto_const_nhds
    change Tendsto
      ((fun p : E × ℝ ↦
        lRegularizedAction S T (lRegularizedCurve S T x p.1) 0 p.2) ∘
          fun n ↦ (V n, b)) atTop
        (nhds (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b))
    exact (continuousAt_lRegularizedAction_lRegularizedCurve
      (I := I) S hS T x hb hbDom).tendsto.comp hpair
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
    have hcostLe := lCost_le_ray_bdd (I := I) S hS T x (V n) b hb
      (hVreg n) (hbdd (lRegularizedCurve S T x (V n) b))
    have hcostLe' :
        lCost S T x (lExp S T x (V n) rho) rho ≤ aV n := by
      simpa only [lExp, b, aV, Real.sq_sqrt hrho.le] using hcostLe
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b =
          lCost S T x (lExp S T x (W n) rho) rho := hcostEq
      _ = lCost S T x (lExp S T x (V n) rho) rho := by rw [hWend n]
      _ ≤ aV n := hcostLe'
      _ ≤ A := hA (Set.mem_range_self n)
  have hWbounded : Bornology.IsBounded (Set.range W) :=
    lRegInit_bound_of_rm (I := I) S hS K T hg x b A hb
      hslab hKslab W hWdom hWact
  let : ProperSpace (TangentSpace I x) := FiniteDimensional.proper Real _
  obtain ⟨W0, _hW0cl, phi, hphi, hWlim⟩ :=
    tendsto_subseq_of_bounded hWbounded (fun n ↦ Set.mem_range_self n)
  have hW0reg : b ∈ lRegularizedDomain S T x W0 :=
    lRegDomain_lim_of_rm (I := I) S hS K T hg x b A hb
      hslab hKslab (fun n ↦ hWdom (phi n))
      (fun n ↦ hWact (phi n)) hWlim
  have hW0dom : (W0, rho) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x W0 rho).2 ⟨hrho, hrho.le, hW0reg⟩
  have hW0min : (W0, rho) ∈ lMinDomain S T x :=
    lMinVec_lim_of_bdd S hS T x (fun n ↦ hWmin (phi n)) hWlim hW0dom hbdd
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
    lMinVec_unique_lt_of_rm S hS K T x (Z := Z) (W := W0)
      hZmin hrho hRhoS hW0min hend0 hK
  have hlocal := lExp_localDiffeo S hS T x Z rho hZdom
    (lMinVec_nconj_lt_of_rm S hS K T x hZmin hRhoS hK)
  obtain ⟨Phi, hPhiSrc, hPhiEq⟩ := hlocal
  have hWsubZ : Tendsto (fun n ↦ W (phi n)) atTop (nhds Z) := by
    change Tendsto (W ∘ phi) atTop (nhds Z)
    rw [← hW0eq]
    exact hWlim
  have hWsrc : ∀ᶠ n in atTop, W (phi n) ∈ Phi.source :=
    hWsubZ.eventually (Phi.open_source.mem_nhds hPhiSrc)
  have hVsrc : ∀ᶠ n in atTop, V (phi n) ∈ Phi.source :=
    hVsub.eventually (Phi.open_source.mem_nhds hPhiSrc)
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

end DifferentialGeometry.PDE.RicciFlow

end
