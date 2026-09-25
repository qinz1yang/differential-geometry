import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Boundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedRepresentation
import DifferentialGeometry.Topology.Manifold.CurveIntervalExtension
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

set_option autoImplicit false
noncomputable section
open Set Filter Bornology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

private theorem exists_minimizing_vector_in_compact_of_ray_action_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {ρ A : ℝ} (hρ : 0 < ρ)
    (K : Set M) (hK : IsCompact K)
    (V : TangentSpace I x) (hV : (V, ρ) ∈ lExpPosDom S T x)
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      α (Real.sqrt ρ) = lExp S T x V ρ →
      lRegularizedAction S T α 0 (Real.sqrt ρ) ≤ A → MapsTo α (Icc 0 (Real.sqrt ρ)) K)
    (hact : lRegularizedAction S T (lRegularizedCurve S T x V) 0 (Real.sqrt ρ) < A) :
    ∃ W : TangentSpace I x, (W, ρ) ∈ lMinDomain S T x ∧
      lExp S T x W ρ = lExp S T x V ρ ∧
      MapsTo (lRegularizedCurve S T x W) (Icc 0 (Real.sqrt ρ)) K ∧
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 (Real.sqrt ρ) ≤
        lRegularizedAction S T (lRegularizedCurve S T x V) 0 (Real.sqrt ρ) := by
  have hb := Real.sqrt_pos.mpr hρ
  have hbdom := ((mem_lExpPosDom S T x V ρ).mp hV).2.2
  obtain ⟨α, hα, hαeq⟩ := DifferentialGeometry.Topology.exists_contMDiff_extension_Icc
    (lRegularizedCurve_c1On S hS T x V hbdom)
  have hα0 : α 0 = x := (hαeq ⟨le_rfl, hb.le⟩).trans (lRegularizedCurve_zero S T x V)
  have hαb : α (Real.sqrt ρ) = lExp S T x V ρ := hαeq ⟨hb.le, le_rfl⟩
  have hαact : lRegularizedAction S T α 0 (Real.sqrt ρ) =
      lRegularizedAction S T (lRegularizedCurve S T x V) 0 (Real.sqrt ρ) := by
    apply lRegularizedAction_congr
    intro t ht
    rw [uIoo_of_le hb.le] at ht
    exact hαeq (Ioo_subset_Icc_self ht)
  obtain ⟨η, hη, hη0, hηb, hηK, hmin⟩ := exists_lRegularizedMinC1_of_compact_action_sublevel
    S hS T hb (fun t ht => lExpPosDom_regularity S T x V hV ht) x (lExp S T x V ρ) α hα hα0 hαb K hK
    (fun β hβ hβ0 hβb hβact => hconf β hβ hβ0 hβb (hβact.trans (hαact.le.trans hact.le)))
  have hm : ∀ β : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 β → β 0 = η 0 → β (Real.sqrt ρ) = η (Real.sqrt ρ) →
      lRegularizedAction S T η 0 (Real.sqrt ρ) ≤ lRegularizedAction S T β 0 (Real.sqrt ρ) :=
    fun β hβ hβ0 hβb => hmin β hβ (hβ0.trans hη0) (hβb.trans hηb)
  cases hη0
  obtain ⟨W, hW, hWend, heq, heqact⟩ := exists_lMinimizingVector_of_minimal S hS T hb
    (fun t ht => lExpPosDom_regularity S T (η 0) V hV ht) η hη hm
  rw [Real.sq_sqrt hρ.le] at hW hWend
  refine ⟨W, hW, hWend.trans hηb, ?_, ?_⟩
  · intro t ht
    rw [heq ht]
    exact hηK ht
  · exact heqact.trans_le ((hmin α hα hα0 hαb).trans_eq hαact)

theorem eventually_mem_lMinDomain_of_unique_of_nonconj_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : E} {ρ A : ℝ} (hmin : (Z, ρ) ∈ lMinDomain S T x)
    (hunique : ∀ W : E, (W, ρ) ∈ lMinDomain S T x → lExp S T x W ρ = lExp S T x Z ρ → W = Z)
    (hnconj : ¬ IsLConjugate S T x Z ρ)
    (hbdd : ∀ y : M, BddBelow {c : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α 0 = x ∧ α (Real.sqrt ρ) = y ∧ lRegularizedAction S T α 0 (Real.sqrt ρ) = c})
    (K : Set M) (hK : IsCompact K) {U : Set M} (hU : U ∈ 𝓝 (lExp S T x Z ρ))
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      α (Real.sqrt ρ) ∈ U → lRegularizedAction S T α 0 (Real.sqrt ρ) ≤ A →
      MapsTo α (Icc 0 (Real.sqrt ρ)) K)
    (hA : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) < A) :
    ∀ᶠ W : E in 𝓝 Z, (W, ρ) ∈ lMinDomain S T x := by
  classical
  have hρ := lMinDomain_pos S T x Z ρ hmin
  have hZdom := ((mem_lMinDomain S T x Z ρ).mp hmin).1
  let b := Real.sqrt ρ
  have hb : 0 < b := Real.sqrt_pos.mpr hρ
  have hb2 : b ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hreg : Icc (T - b ^ 2) T ⊆ D.regular := by
    rw [hb2]
    intro t ht
    have hn : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hh : T - t ≤ ρ := by linarith [ht.1]
    have hc := lExpPosDom_regularity S T x Z hZdom ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hh⟩
    simpa only [Real.sq_sqrt hn, sub_sub_cancel] using hc
  have hnear : ∀ᶠ W : E in 𝓝 Z, (W, ρ) ∈ lExpPosDom S T x ∧
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 b < A ∧ lExp S T x W ρ ∈ U := by
    have hd : {W : E | (W, ρ) ∈ lExpPosDom S T x} ∈ 𝓝 Z :=
      ((lExpPosDom_open S hS T x).preimage (continuous_id.prodMk continuous_const)).mem_nhds hZdom
    have ha := (continuousAt_lRegularizedAction_lRegularizedCurve S hS T x hb
      (((mem_lExpPosDom S T x Z ρ).mp hZdom).2.2)).comp (f := fun W : E => (W, b))
      (continuousAt_id.prodMk continuousAt_const)
    have hend := ((lExp_smoothOn S hS T x) (Z, ρ) hZdom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hZdom)
    have hpoint : ContinuousAt (fun W : E => lExp S T x W ρ) Z :=
      hend.comp (f := fun W : E => (W, ρ)) (continuousAt_id.prodMk continuousAt_const)
    exact Filter.inter_mem hd ((ha.eventually (Iio_mem_nhds hA)).and (hpoint.eventually hU))
  by_contra hn
  have hcl : (Z : E) ∈ closure {W : E | (W, ρ) ∉ lMinDomain S T x} := by
    rw [mem_closure_iff_nhds]
    intro U hU
    by_contra he
    apply hn
    apply mem_of_superset hU
    intro W hW
    by_contra hnot
    exact he ⟨W, hW, hnot⟩
  obtain ⟨Q, hQnot, hQlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hQnear := hQlim.eventually hnear
  obtain ⟨N, hN⟩ := eventually_atTop.mp hQnear
  let V := fun n : ℕ => Q (n + N)
  have hVlim : Tendsto V atTop (𝓝 Z) := hQlim.comp (tendsto_add_atTop_nat N)
  have hVdom (n : ℕ) : (V n, ρ) ∈ lExpPosDom S T x := (hN (n + N) (by omega)).1
  have hVact (n : ℕ) : lRegularizedAction S T (lRegularizedCurve S T x (V n)) 0 b < A :=
    (hN (n + N) (by omega)).2.1
  have hVmem (n : ℕ) : lExp S T x (V n) ρ ∈ U := (hN (n + N) (by omega)).2.2
  have hVnot (n : ℕ) : (V n, ρ) ∉ lMinDomain S T x := hQnot (n + N)
  choose W hWmin hWend hWrange hWact using fun n =>
    exists_minimizing_vector_in_compact_of_ray_action_lt S hS T x hρ K hK (V n) (hVdom n)
      (fun α hα hα0 hαend hαact => hconf α hα hα0 (hαend.symm ▸ hVmem n) hαact) (hVact n)
  have hWdom (n : ℕ) : b ∈ lRegularizedDomain S T x (W n) :=
    ((mem_lExpPosDom S T x (W n) ρ).mp (((mem_lMinDomain S T x (W n) ρ).mp (hWmin n)).1)).2.2
  have hWbound : Bornology.IsBounded (range (fun n => (W n : E))) := lRegInit_bound_of_compact_range S hS T x b A hb hreg hK W
    hWdom (fun n => (hWact n).trans (hVact n).le) (fun n => image_subset_iff.mpr (hWrange n))
  let : ProperSpace E := FiniteDimensional.proper ℝ _
  obtain ⟨W₀, _, φ, hφ, hWlim⟩ := tendsto_subseq_of_bounded hWbound (fun n => mem_range_self n)
  have hW₀reg : b ∈ lRegularizedDomain S T x W₀ :=
    lRegDomain_lim_of_compact_range S hS T x b hb hreg K hK (fun n => hWrange (φ n)) hWlim
  have hW₀dom : (W₀, ρ) ∈ lExpPosDom S T x := (mem_lExpPosDom S T x W₀ ρ).mpr ⟨hρ, hρ.le, hW₀reg⟩
  have hW₀min := lMinVec_lim_of_bdd S hS T x (fun n => hWmin (φ n)) hWlim hW₀dom hbdd
  have hVsub := hVlim.comp hφ.tendsto_atTop
  have hWExp := ((lExp_smoothOn S hS T x) (W₀, ρ) hW₀dom).continuousWithinAt.continuousAt
    ((lExpPosDom_open S hS T x).mem_nhds hW₀dom)
  have hZExp := ((lExp_smoothOn S hS T x) (Z, ρ) hZdom).continuousWithinAt.continuousAt
    ((lExpPosDom_open S hS T x).mem_nhds hZdom)
  have heqend : lExp S T x W₀ ρ = lExp S T x Z ρ :=
    tendsto_nhds_unique (hWExp.tendsto.comp (hWlim.prodMk_nhds tendsto_const_nhds))
      ((hZExp.tendsto.comp (hVsub.prodMk_nhds tendsto_const_nhds)).congr'
        (Eventually.of_forall fun n => (hWend (φ n)).symm))
  have hW₀eq : W₀ = Z := hunique W₀ hW₀min heqend
  have hlocal := lExp_localDiffeo S hS T x Z ρ hZdom
    hnconj
  obtain ⟨Φ, hΦsrc, hΦeq⟩ := hlocal
  have hWsubZ : Tendsto (fun n => W (φ n)) atTop (𝓝 Z) := hW₀eq ▸ hWlim
  obtain ⟨n, hnW, hnV⟩ := ((hWsubZ.eventually (Φ.open_source.mem_nhds hΦsrc)).and
    (hVsub.eventually (Φ.open_source.mem_nhds hΦsrc))).exists
  have hWV : W (φ n) = V (φ n) := by
    apply Φ.injOn hnW hnV
    rw [← hΦeq hnW, ← hΦeq hnV]
    exact hWend (φ n)
  exact hVnot (φ n) (hWV ▸ hWmin (φ n))

theorem eventually_mem_lMinDomain_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : E} {σ ρ A B : ℝ} (hmin : (Z, σ) ∈ lMinDomain S T x)
    (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hscalar : ∀ t ∈ Icc (T - σ) T, ∀ y : M, -B ≤ S.scalar t y)
    (K : Set M) (hK : IsCompact K) {U : Set M} (hU : U ∈ 𝓝 (lExp S T x Z ρ))
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      α (Real.sqrt ρ) ∈ U → lRegularizedAction S T α 0 (Real.sqrt ρ) ≤ A →
      MapsTo α (Icc 0 (Real.sqrt ρ)) K)
    (hA : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) < A) :
    ∀ᶠ W : E in 𝓝 (Z : E), (W, ρ) ∈ lMinDomain S T x := by
  classical
  have hσ : 0 < σ := hρ.trans hρσ
  have hdomσ := ((mem_lMinDomain S T x Z σ).mp hmin).1
  have hregσ : Icc (T - σ) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hle : T - t ≤ σ := by linarith [ht.1]
    have hh := lExpPosDom_regularity S T x Z hdomσ ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hh
  have hbounded {r : ℝ} (hr : 0 < r) (hrσ : r ≤ σ) (y : M) :
      BddBelow {c : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧ α 0 = x ∧
        α (Real.sqrt r) = y ∧ lRegularizedAction S T α 0 (Real.sqrt r) = c} := by
    apply lRegularizedCosts_bdd_of_scalar_lower S hS T (Real.sqrt_nonneg r)
    · intro t ht
      exact D.regular_subset (lExpPosDom_regularity S T x Z hdomσ
        ⟨ht.1, ht.2.trans (Real.sqrt_le_sqrt hrσ)⟩)
    · intro t ht z
      have ht2 : t ^ 2 ≤ r := (Real.le_sqrt ht.1.le hr.le).mp ht.2.le
      exact hscalar (T - t ^ 2) ⟨by linarith, sub_le_self _ (sq_nonneg t)⟩ z
  have hZmin : (Z, ρ) ∈ lMinDomain S T x := lMinDomain_down_of_bdd S hS T x Z hmin hρ hρσ.le
    (hbounded hρ hρσ.le _) (hbounded hσ le_rfl _)
  exact eventually_mem_lMinDomain_of_unique_of_nonconj_of_compact_action_sublevel S hS T x hZmin
    (fun W hW heq => lMinVec_unique_lt_of_bdd S hS T x hmin hρσ hW heq (hbounded hσ le_rfl _))
    (lMinVec_nconj_lt_of_bdd S hS T x hmin hρσ (hbounded hσ le_rfl _))
    (hbounded hρ hρσ.le) K hK hU hconf hA

theorem exists_open_lMinDomain_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : E} {σ ρ A B : ℝ} (hmin : (Z, σ) ∈ lMinDomain S T x)
    (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hscalar : ∀ t ∈ Icc (T - σ) T, ∀ y : M, -B ≤ S.scalar t y)
    (K : Set M) (hK : IsCompact K) {U : Set M} (hU : U ∈ 𝓝 (lExp S T x Z ρ))
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      α (Real.sqrt ρ) ∈ U → lRegularizedAction S T α 0 (Real.sqrt ρ) ≤ A →
      MapsTo α (Icc 0 (Real.sqrt ρ)) K)
    (hA : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) < A) :
    ∃ V : Set E, IsOpen V ∧ Z ∈ V ∧ ∀ W ∈ V, (W, ρ) ∈ lMinDomain S T x := by
  obtain ⟨V, hVsub, hVopen, hZV⟩ := mem_nhds_iff.mp
    (eventually_mem_lMinDomain_of_compact_action_sublevel S hS T x hmin hρ hρσ hscalar K hK hU hconf hA)
  exact ⟨V, hVopen, hZV, hVsub⟩

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

theorem exists_open_lMinDomain_of_action_lt_frontier_barrier
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : E} {σ ρ μ B r : ℝ} (hmin : (Z, σ) ∈ lMinDomain S T x)
    (hρ : 0 < ρ) (hρσ : ρ < σ) (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hscalar : ∀ t ∈ Icc (T - σ) T, ∀ y : M, -B ≤ S.scalar t y)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (hxK : x ∈ interior K)
    (hmetric : ∀ t ∈ Ioo 0 (Real.sqrt ρ), ∀ y ∈ K, ∀ w : TangentSpace I y,
      μ * g.inner y w w ≤ (S.base.metric (T - t ^ 2)).inner y w w)
    (hfront : ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x y)
    (hact : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) <
      μ * r ^ 2 / (2 * Real.sqrt ρ) - 2 * B * (Real.sqrt ρ) ^ 3) :
    ∃ V : Set E, IsOpen V ∧ Z ∈ V ∧ ∀ W ∈ V, (W, ρ) ∈ lMinDomain S T x := by
  let threshold := μ * r ^ 2 / (2 * Real.sqrt ρ) - 2 * B * (Real.sqrt ρ) ^ 3
  let A := (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) + threshold) / 2
  have hlow : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) < A := by
    dsimp only [A, threshold]
    linarith
  have hA : A < threshold := by dsimp only [A, threshold]; linarith
  have hdom := ((mem_lMinDomain S T x Z σ).mp hmin).1
  have htime : ∀ t ∈ Icc 0 (Real.sqrt ρ), T - t ^ 2 ∈ D.carrier := by
    intro t ht
    exact D.regular_subset (lExpPosDom_regularity S T x Z hdom
      ⟨ht.1, ht.2.trans (Real.sqrt_le_sqrt hρσ.le)⟩)
  apply exists_open_lMinDomain_of_compact_action_sublevel S hS T x hmin hρ hρσ hscalar K hK
    (show (univ : Set M) ∈ 𝓝 (lExp S T x Z ρ) from Filter.univ_mem) _ hlow
  intro α hα hα0 _ hαact
  by_contra hescape
  have hint : IntervalIntegrable (lRegularizedLagrangian S T α) volume 0 (Real.sqrt ρ) := by
    have hc := lRegularizedLagrangian_continuousOn_carrier (I := I) S hS α hα
    have hm : ContinuousOn (fun t : ℝ => (T, t)) (Icc 0 (Real.sqrt ρ)) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hmap : MapsTo (fun t : ℝ => (T, t)) (Icc 0 (Real.sqrt ρ))
        {q : ℝ × ℝ | q.1 - q.2 ^ 2 ∈ D.carrier} := htime
    exact (hc.comp (f := fun t : ℝ => (T, t)) hm hmap).intervalIntegrable_of_Icc (Real.sqrt_nonneg ρ)
  have hgap := lRegularizedAction_ge_of_leaves_closed_set S T α le_rfl le_rfl hμ hB hr g hK.isClosed
    hα.contMDiffOn (hα0.symm ▸ hxK)
    (fun t ht hy => hmetric t ht (α t) hy (lVelocity α t))
    (fun t ht => hscalar (T - t ^ 2) ⟨by
      have ht2 : t ^ 2 ≤ ρ := (Real.le_sqrt ht.1.le hρ.le).mp ht.2.le
      linarith, sub_le_self _ (sq_nonneg t)⟩ (α t)) hint
    (by simpa only [hα0] using hfront) hescape
  have hthreshold : threshold ≤ lRegularizedAction S T α 0 (Real.sqrt ρ) := by
    simpa only [threshold, sub_zero, mul_assoc, pow_succ] using hgap
  exact (not_lt_of_ge hthreshold) (hαact.trans_lt hA)

end DifferentialGeometry.PDE.RicciFlow

end

noncomputable section
open Set Filter Bornology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}
theorem eventually_unique_lMinimizingVector_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : E} {ρ A : ℝ} (hmin : (Z, ρ) ∈ lMinDomain S T x)
    (hunique : ∀ W : E, (W, ρ) ∈ lMinDomain S T x → lExp S T x W ρ = lExp S T x Z ρ → W = Z)
    (hnconj : ¬ IsLConjugate S T x Z ρ)
    (hbdd : ∀ y : M, BddBelow {c : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α 0 = x ∧ α (Real.sqrt ρ) = y ∧ lRegularizedAction S T α 0 (Real.sqrt ρ) = c})
    (K : Set M) (hK : IsCompact K) {U : Set M} (hU : U ∈ 𝓝 (lExp S T x Z ρ))
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x →
      α (Real.sqrt ρ) ∈ U → lRegularizedAction S T α 0 (Real.sqrt ρ) ≤ A →
      MapsTo α (Icc 0 (Real.sqrt ρ)) K)
    (hA : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt ρ) < A) :
    ∀ᶠ V : E in 𝓝 Z, (V, ρ) ∈ lMinDomain S T x ∧
      ∀ W : E, (W, ρ) ∈ lMinDomain S T x → lExp S T x W ρ = lExp S T x V ρ → W = V := by
  classical
  have hρ := lMinDomain_pos S T x Z ρ hmin
  have hZdom := ((mem_lMinDomain S T x Z ρ).mp hmin).1
  let b := Real.sqrt ρ
  have hb : 0 < b := Real.sqrt_pos.mpr hρ
  have hb2 : b ^ 2 = ρ := Real.sq_sqrt hρ.le
  have hreg : Icc (T - b ^ 2) T ⊆ D.regular := by
    rw [hb2]
    intro t ht
    have hn : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hh : T - t ≤ ρ := by linarith [ht.1]
    have hc := lExpPosDom_regularity S T x Z hZdom ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hh⟩
    simpa only [Real.sq_sqrt hn, sub_sub_cancel] using hc
  have hnearmin := eventually_mem_lMinDomain_of_unique_of_nonconj_of_compact_action_sublevel
    S hS T x hmin hunique hnconj hbdd K hK hU hconf hA
  have ha := (continuousAt_lRegularizedAction_lRegularizedCurve S hS T x hb
    (((mem_lExpPosDom S T x Z ρ).mp hZdom).2.2)).comp (f := fun W : E => (W,b))
    (continuousAt_id.prodMk continuousAt_const)
  have hend := ((lExp_smoothOn S hS T x) (Z, ρ) hZdom).continuousWithinAt.continuousAt
    ((lExpPosDom_open S hS T x).mem_nhds hZdom)
  have hpoint : ContinuousAt (fun W : E => lExp S T x W ρ) Z :=
    hend.comp (f := fun W : E => (W,ρ)) (continuousAt_id.prodMk continuousAt_const)
  have hnear := hnearmin.and ((ha.eventually (Iio_mem_nhds hA)).and (hpoint.eventually hU))
  suffices hh : ∀ᶠ V : E in 𝓝 Z, ∀ W : E, (W,ρ) ∈ lMinDomain S T x →
      lExp S T x W ρ = lExp S T x V ρ → W = V from hnearmin.and hh
  by_contra hn
  have hcl : Z ∈ closure {V : E | ∃ W : E, (W,ρ) ∈ lMinDomain S T x ∧
      lExp S T x W ρ = lExp S T x V ρ ∧ W ≠ V} := by
    rw [mem_closure_iff_nhds]
    intro V hV
    by_contra he
    apply hn
    apply mem_of_superset hV
    intro q hq W hW hend
    by_contra hne
    exact he ⟨q, hq, W, hW, hend, hne⟩
  obtain ⟨Q,hQbad,hQlim⟩ := mem_closure_iff_seq_limit.mp hcl
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hQlim.eventually hnear)
  let V := fun n : ℕ => Q (n+N)
  have hVlim : Tendsto V atTop (𝓝 Z) := hQlim.comp (tendsto_add_atTop_nat N)
  have hVmin (n : ℕ) := (hN (n+N) (by omega)).1
  have hVact (n : ℕ) := (hN (n+N) (by omega)).2.1
  have hVU (n : ℕ) := (hN (n+N) (by omega)).2.2
  choose W hWmin hWend hWne using fun n => hQbad (n+N)
  have hWdom (n : ℕ) : b ∈ lRegularizedDomain S T x (W n) :=
    ((mem_lExpPosDom S T x (W n) ρ).mp (((mem_lMinDomain S T x (W n) ρ).mp (hWmin n)).1)).2.2
  have hWact (n : ℕ) : lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b < A := by
    have hw := ((mem_lMinDomain S T x (W n) ρ).mp (hWmin n)).2
    have hv := ((mem_lMinDomain S T x (V n) ρ).mp (hVmin n)).2
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x (W n))) 0 ρ = _ at hw
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x (V n))) 0 ρ = _ at hv
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ ρ hρ.le] at hw hv
    rw [hw, hWend n, ← hv]
    exact hVact n
  have hWrange (n : ℕ) : MapsTo (lRegularizedCurve S T x (W n)) (Icc 0 b) K := by
    obtain ⟨α,hα,heq⟩ := DifferentialGeometry.Topology.exists_contMDiff_extension_Icc
      (lRegularizedCurve_c1On S hS T x (W n) (hWdom n))
    have hα0 := (heq ⟨le_rfl,hb.le⟩).trans (lRegularizedCurve_zero S T x (W n))
    have hαb : α b = lExp S T x (W n) ρ := heq ⟨hb.le,le_rfl⟩
    have ha : lRegularizedAction S T α 0 b = lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 b := by
      apply lRegularizedAction_congr
      rw [uIoo_of_le hb.le]
      exact heq.mono Ioo_subset_Icc_self
    have hc := hconf α hα hα0 (hαb.symm ▸ (hWend n).symm ▸ hVU n) (ha.le.trans (hWact n).le)
    intro t ht
    rw [← heq ht]
    exact hc ht
  have hbnd := lRegInit_bound_of_compact_range S hS T x b A hb hreg hK W hWdom
    (fun n => (hWact n).le) (fun n => image_subset_iff.mpr (hWrange n))
  let _ : ProperSpace E := FiniteDimensional.proper ℝ _
  obtain ⟨W₀,_,φ,hφ,hWlim⟩ := tendsto_subseq_of_bounded hbnd (fun n => mem_range_self n)
  have hW₀reg := lRegDomain_lim_of_compact_range S hS T x b hb hreg K hK (fun n => hWrange (φ n)) hWlim
  have hW₀dom : (W₀,ρ) ∈ lExpPosDom S T x := (mem_lExpPosDom S T x W₀ ρ).mpr ⟨hρ,hρ.le,hW₀reg⟩
  have hW₀min := lMinVec_lim_of_bdd S hS T x (fun n => hWmin (φ n)) hWlim hW₀dom hbdd
  have hWExp := ((lExp_smoothOn S hS T x) (W₀,ρ) hW₀dom).continuousWithinAt.continuousAt
    ((lExpPosDom_open S hS T x).mem_nhds hW₀dom)
  have hVsub := hVlim.comp hφ.tendsto_atTop
  have heqend : lExp S T x W₀ ρ = lExp S T x Z ρ :=
    tendsto_nhds_unique (hWExp.tendsto.comp (hWlim.prodMk_nhds tendsto_const_nhds))
      ((hend.tendsto.comp (hVsub.prodMk_nhds tendsto_const_nhds)).congr'
        (Eventually.of_forall fun n => (hWend (φ n)).symm))
  have heq := hunique W₀ hW₀min heqend
  obtain ⟨Φ,hΦsrc,hΦeq⟩ := lExp_localDiffeo S hS T x Z ρ hZdom hnconj
  have hWZ : Tendsto (fun n => W (φ n)) atTop (𝓝 Z) := heq ▸ hWlim
  obtain ⟨n,hnW,hnV⟩ := ((hWZ.eventually (Φ.open_source.mem_nhds hΦsrc)).and
    (hVsub.eventually (Φ.open_source.mem_nhds hΦsrc))).exists
  apply hWne (φ n)
  apply Φ.injOn hnW hnV
  rw [← hΦeq hnW, ← hΦeq hnV]
  exact hWend (φ n)

end DifferentialGeometry.PDE.RicciFlow
end

noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
 [NeZero (Module.finrank ℝ E)] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] in
theorem eventually_not_isLConjugate
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    {Z : TangentSpace I x} {τ : ℝ} (hdom : (Z, τ) ∈ lExpPosDom S T x)
    (hnconj : ¬ IsLConjugate S T x Z τ) :
    ∀ᶠ W : E in 𝓝 Z, ¬ IsLConjugate S T x W τ := by
  obtain ⟨Φ, hZ, hEq⟩ := lExp_localDiffeo S hS T x Z τ hdom hnconj
  filter_upwards [Φ.open_source.mem_nhds hZ] with W hW
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (fun V : E => lExp S T x V τ) W :=
    ⟨Φ, hW, hEq⟩
  have hinj : Function.Injective (mfderiv 𝓘(ℝ, E) I (fun V : E => lExp S T x V τ) W) := by
    rw [← hloc.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
  exact fun hc => hc.2 hinj

theorem isOpen_setOf_unique_nonconjugate_minimizer_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M) {τ A : ℝ}
    (K : Set M) (hK : IsCompact K) (U : Set M) (hU : IsOpen U)
    (hbdd : ∀ y : M, BddBelow {a : ℝ | ∃ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α ∧
      α 0 = x ∧ α (Real.sqrt τ) = y ∧ lRegularizedAction S T α 0 (Real.sqrt τ) = a})
    (hconf : ∀ α : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 α → α 0 = x → α (Real.sqrt τ) ∈ U →
      lRegularizedAction S T α 0 (Real.sqrt τ) ≤ A → MapsTo α (Icc 0 (Real.sqrt τ)) K) :
    IsOpen {Z : E | (Z, τ) ∈ lMinDomain S T x ∧
      (∀ W : E, (W, τ) ∈ lMinDomain S T x → lExp S T x W τ = lExp S T x Z τ → W = Z) ∧
      ¬ IsLConjugate S T x Z τ ∧ lExp S T x Z τ ∈ U ∧
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt τ) < A} := by
  apply isOpen_iff_mem_nhds.mpr
  intro Z hZ
  have hd := ((mem_lMinDomain S T x Z τ).mp hZ.1).1
  have hτ := lMinDomain_pos S T x Z τ hZ.1
  have hb := Real.sqrt_pos.mpr hτ
  have hv := eventually_unique_lMinimizingVector_of_compact_action_sublevel S hS T x hZ.1 hZ.2.1 hZ.2.2.1
    hbdd K hK (hU.mem_nhds hZ.2.2.2.1) hconf hZ.2.2.2.2
  have hnc := eventually_not_isLConjugate S hS T x hd hZ.2.2.1
  have hact := (continuousAt_lRegularizedAction_lRegularizedCurve S hS T x hb
    ((mem_lExpPosDom S T x Z τ).mp hd).2.2).comp (f := fun W : E => (W, Real.sqrt τ))
      (continuousAt_id.prodMk continuousAt_const)
  have hend := ((lExp_smoothOn S hS T x) (Z, τ) hd).continuousWithinAt.continuousAt
    ((lExpPosDom_open S hS T x).mem_nhds hd)
  have hp := hend.comp (f := fun W : E => (W, τ)) (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hv, hnc, hp.eventually (hU.mem_nhds hZ.2.2.2.1),
    hact.eventually (Iio_mem_nhds hZ.2.2.2.2)] with W hW hWnc hWU hWA
  exact ⟨hW.1, hW.2, hWnc, hWU, hWA⟩

end DifferentialGeometry.PDE.RicciFlow
end
