import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.RegDomainLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVector
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bornology Bundle Filter Function MeasureTheory Set
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

theorem exists_lMinVec_ray_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (Z : TangentSpace I x) (tau : ℝ)
    (hdom : (Z, tau) ∈ lExpPosDom S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    ∃ W : TangentSpace I x,
      (W, tau) ∈ lMinDomain S T x ∧
        lExp S T x W tau = lExp S T x Z tau := by
  rcases (mem_lExpPosDom S T x Z tau).1 hdom with
    ⟨htau, _htau0, hbDom⟩
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  obtain ⟨c, hc, hcId, _hcDeriv, hcRange⟩ :=
    exists_lRegularizedDomain_smoothClamp S T x Z hb hbDom
  let z : E := Z
  let alpha : ℝ → M := fun s ↦ lRegularizedCurve S T x Z (c s)
  have hcM : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ c :=
    contMDiff_iff_contDiff.mpr hc
  have hpair : ContMDiff 𝓘(ℝ, ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) ∞
      (fun s : ℝ ↦ (z, c s)) :=
    contMDiff_const.prodMk hcM
  have halphaInf : ContMDiff 𝓘(ℝ, ℝ) I ∞ alpha := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      ((fun p : E × ℝ ↦ lRegularizedCurve S T x p.1 p.2) ∘
        fun s : ℝ ↦ (z, c s)) univ
    exact (lRegularizedCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change c s ∈ lRegularizedDomain S T x Z
        exact hcRange s)
  have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha :=
    halphaInf.of_le (by norm_num)
  have hc0 : c 0 = 0 := by
    simpa only [id_eq] using hcId ⟨le_rfl, hb.le⟩
  have hcb : c (Real.sqrt tau) = Real.sqrt tau := by
    simpa only [id_eq] using hcId ⟨hb.le, le_rfl⟩
  have hstart : alpha 0 = x := by
    simp only [alpha, hc0, lRegularizedCurve_zero]
  have hend : alpha (Real.sqrt tau) = lExp S T x Z tau := by
    change lRegularizedCurve S T x Z (c (Real.sqrt tau)) =
      lRegularizedCurve S T x Z (Real.sqrt tau)
    rw [hcb]
  exact exists_lMinimizingVector_rm (I := I) S hS K T hg tau htau
    hreg hRm x (lExp S T x Z tau) alpha halpha hstart hend

omit [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem original_ray_prefix_action_bound
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (x : M) (Z : TangentSpace I x) (b B R A : ℝ)
    (hb : 0 < b) (hbB : b ≤ B) (hBR : B ≤ R)
    (hreg : Icc (T - R ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - R ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    (hdom : B ∈ lRegularizedDomain S T x Z)
    (hact : lRegularizedAction S T (lRegularizedCurve S T x Z) 0 B ≤ A) :
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b ≤
      A - (-2 * R ^ 2 *
        ((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K)) * R := by
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  let Cp : ℝ := -2 * R ^ 2 * P
  have hP : 0 ≤ P := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg K)
  have hCp : Cp ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg R)) hP
  have hB : 0 ≤ B := hb.le.trans hbB
  have hR : 0 ≤ R := hB.trans hBR
  have hc1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc (0 : ℝ) B) :=
    lRegularizedCurve_c1On S hS T x Z hdom
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) B) :
      T - s ^ 2 ∈ D.regular := by
    apply hreg
    have hs2 : s ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ hs.1 hR).2 (hs.2.trans hBR)
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hprefixC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc (0 : ℝ) b) :=
    hc1.mono (fun _ hs ↦ ⟨hs.1, hs.2.trans hbB⟩)
  have htailC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc b B) :=
    hc1.mono (fun _ hs ↦ ⟨hb.le.trans hs.1, hs.2⟩)
  have hprefixLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume 0 b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le alpha hprefixC1
      (fun s hs ↦ hclock s ⟨hs.1, hs.2.trans hbB⟩)
  have htailLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume b B :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T b B hbB alpha htailC1
      (fun s hs ↦ hclock s ⟨hb.le.trans hs.1, hs.2⟩)
  have htailKin : IntervalIntegrable (lRegularizedSpeedSq S T alpha) volume b B :=
    intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T b B hbB alpha htailC1
      (fun s hs ↦ hclock s ⟨hb.le.trans hs.1, hs.2⟩)
  have hpot (s : ℝ) (hs : s ∈ Icc b B) :
      Cp ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) :=
    lRegularizedPot_lower_rm (I := I) S K T R hR hRm s
      ⟨hb.le.trans hs.1, hs.2.trans hBR⟩ (alpha s)
  have hkinLe := lRegularizedKinetic_le (I := I) S T alpha b B
    (lRegularizedAction S T alpha b B) Cp hbB hpot htailKin htailLag le_rfl
  have hkinNonneg : 0 ≤ ∫ s in b..B, lRegularizedSpeedSq S T alpha s := by
    apply intervalIntegral.integral_nonneg hbB
    intro s _hs
    exact lRegularizedSpeedSq_nonneg (I := I) S T alpha s
  have htailLower : Cp * (B - b) ≤ lRegularizedAction S T alpha b B := by
    linarith only [hkinLe, hkinNonneg]
  have htailUniform : Cp * R ≤ lRegularizedAction S T alpha b B := by
    have hlen : B - b ≤ R := by linarith only [hb, hBR]
    exact (mul_le_mul_of_nonpos_left hlen hCp).trans htailLower
  have hadd := lRegularizedAction_add S T alpha 0 b B hprefixLag htailLag
  change lRegularizedAction S T alpha 0 b ≤ A - Cp * R
  change lRegularizedAction S T alpha 0 B ≤ A at hact
  linarith only [hact, hadd, htailUniform]

theorem lCut_alt_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (Z : TangentSpace I x) (tau rho : ℝ)
    (hcut : IsGreatest
      {sigma : ℝ | ((Z : E), sigma) ∈ lMinDomain S T x} tau)
    (htr : tau < rho)
    (hreg : Icc (T - rho) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - rho) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    IsLConjugate S T x Z tau ∨
      ∃ W : TangentSpace I x, W ≠ Z ∧
        ((W : E), tau) ∈ lMinDomain S T x ∧
          lExp S T x W tau = lExp S T x Z tau := by
  classical
  by_cases hconj : IsLConjugate S T x Z tau
  · exact Or.inl hconj
  right
  have hZmin : (Z, tau) ∈ lMinDomain S T x := hcut.1
  have hZdom : ((Z : E), tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hZmin).1
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hZmin
  let z : E := Z
  let U : Set Real :=
    ((fun sigma : Real ↦ (z, sigma)) ⁻¹' lExpPosDom S T x) ∩ Iio rho
  have hUopen : IsOpen U := by
    apply IsOpen.inter _ isOpen_Iio
    apply (lExpPosDom_open S hS T x).preimage
    exact continuous_const.prodMk continuous_id
  have htauU : tau ∈ U := by
    change ((Z : E), tau) ∈ lExpPosDom S T x ∧ tau < rho
    exact ⟨hZdom, htr⟩
  obtain ⟨u, _huAnti, hutau, hulim⟩ :=
    exists_seq_strictAnti_tendsto tau
  have huU : ∀ᶠ n in atTop, u n ∈ U :=
    hulim.eventually (hUopen.mem_nhds htauU)
  obtain ⟨N, hNU⟩ := (eventually_atTop.1 huU)
  let sigma : Nat → Real := fun n ↦ u (n + N)
  have hsigmaGt (n : Nat) : tau < sigma n := hutau (n + N)
  have hsigmaPos (n : Nat) : 0 < sigma n := htau.trans (hsigmaGt n)
  have hsigmaLim : Tendsto sigma atTop (nhds tau) := by
    simpa only [sigma, Function.comp_def] using
      hulim.comp (tendsto_add_atTop_nat N)
  have hZdomN (n : Nat) : ((Z : E), sigma n) ∈ lExpPosDom S T x := by
    have hmem : u (n + N) ∈ U := hNU (n + N) (by omega)
    exact hmem.1
  have hsigmaRho (n : Nat) : sigma n < rho := by
    have hmem : u (n + N) ∈ U := hNU (n + N) (by omega)
    exact hmem.2
  have hregSub (s : Real) (hs : s ≤ rho) :
      Icc (T - s) T ⊆ D.regular := by
    intro t ht
    exact hreg ⟨(sub_le_sub_left hs T).trans ht.1, ht.2⟩
  have hRmSub (s : Real) (hs : s ≤ rho) :
      ∀ t ∈ Icc (T - s) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K := by
    intro t ht y
    exact hRm t ⟨(sub_le_sub_left hs T).trans ht.1, ht.2⟩ y
  have hZnotMin (n : Nat) : (Z, sigma n) ∉ lMinDomain S T x := by
    intro hmin
    exact (not_lt_of_ge (hcut.2 hmin)) (hsigmaGt n)
  have hminExists (n : Nat) :
      ∃ W : TangentSpace I x,
        (W, sigma n) ∈ lMinDomain S T x ∧
          lExp S T x W (sigma n) = lExp S T x Z (sigma n) :=
    exists_lMinVec_ray_of_rm S hS K T hg x Z (sigma n)
      (hZdomN n) (hregSub (sigma n) (hsigmaRho n).le)
      (hRmSub (sigma n) (hsigmaRho n).le)
  let W : Nat → TangentSpace I x := fun n ↦ (hminExists n).choose
  have hWmin (n : Nat) : (W n, sigma n) ∈ lMinDomain S T x :=
    (hminExists n).choose_spec.1
  have hWend (n : Nat) :
      lExp S T x (W n) (sigma n) = lExp S T x Z (sigma n) :=
    (hminExists n).choose_spec.2
  have hWne (n : Nat) : W n ≠ Z := by
    intro hEq
    apply hZnotMin n
    simpa only [hEq] using hWmin n
  let B : Nat → Real := fun n ↦ Real.sqrt (sigma n)
  let eps : Real := Real.sqrt tau
  let R : Real := Real.sqrt rho
  have heps : 0 < eps := by
    simpa only [eps] using Real.sqrt_pos.2 htau
  have hepsB (n : Nat) : eps ≤ B n := by
    simpa only [eps, B] using Real.sqrt_le_sqrt (hsigmaGt n).le
  have hBR (n : Nat) : B n ≤ R := by
    simpa only [B, R] using Real.sqrt_le_sqrt (hsigmaRho n).le
  have hR2 : R ^ 2 = rho := Real.sq_sqrt (htau.trans htr).le
  have heps2 : eps ^ 2 = tau := Real.sq_sqrt htau.le
  have hregR : Icc (T - R ^ 2) T ⊆ D.regular := by
    simpa only [hR2] using hreg
  have hRmR : ∀ t ∈ Icc (T - R ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := by
    simpa only [hR2] using hRm
  have hregEps : Icc (T - eps ^ 2) T ⊆ D.regular := by
    simpa only [heps2] using hregSub tau htr.le
  have hRmEps : ∀ t ∈ Icc (T - eps ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K := by
    simpa only [heps2] using hRmSub tau htr.le
  have hWdom (n : Nat) : B n ∈ lRegularizedDomain S T x (W n) := by
    have hdom := ((mem_lMinDomain S T x (W n) (sigma n)).1 (hWmin n)).1
    have hdata := (mem_lExpPosDom S T x (W n) (sigma n)).1 hdom
    simpa only [B] using hdata.2.2
  have hZreg (n : Nat) : B n ∈ lRegularizedDomain S T x Z := by
    have hdata := (mem_lExpPosDom S T x Z (sigma n)).1 (hZdomN n)
    simpa only [B] using hdata.2.2
  let aZ : Nat → Real := fun n ↦
    lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (B n)
  have hBLim : Tendsto B atTop (nhds eps) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsigmaLim
    change Tendsto (fun n ↦ Real.sqrt (sigma n)) atTop
      (nhds (Real.sqrt tau))
    convert h using 1 ; rfl
  have haZlim : Tendsto aZ atTop
      (nhds (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 eps)) := by
    have hepsDom : eps ∈ lRegularizedDomain S T x Z := by
      simpa only [eps] using ((mem_lExpPosDom S T x Z tau).1 hZdom).2.2
    have hpair : Tendsto (fun n ↦ (Z, B n)) atTop (nhds (Z, eps)) :=
      tendsto_const_nhds.prodMk_nhds hBLim
    change Tendsto
      ((fun p : E × ℝ ↦
        lRegularizedAction S T (lRegularizedCurve S T x p.1) 0 p.2) ∘
          fun n ↦ (Z, B n)) atTop
        (nhds (lRegularizedAction S T (lRegularizedCurve S T x Z) 0 eps))
    exact (continuousAt_lRegularizedAction_lRegularizedCurve
      (I := I) S hS T x heps hepsDom).tendsto.comp hpair
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto aZ haZlim).bddAbove
  have hWact (n : Nat) :
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 (B n) ≤ A := by
    have hminEq := ((mem_lMinDomain S T x (W n) (sigma n)).1 (hWmin n)).2
    have hcostEq :
        lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 (B n) =
          lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := by
      calc
        lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 (B n) =
            lLength S T (squareRootReparametrization (lRegularizedCurve S T x (W n))) 0
              (sigma n) := by
          simpa only [B] using
            (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x (W n))
              (sigma n) (hsigmaPos n).le).symm
        _ = lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := by
          rw [show squareRootReparametrization (lRegularizedCurve S T x (W n)) =
            (fun r ↦ lRegularizedCurve S T x (W n) (Real.sqrt r)) by rfl]
          simpa only [lExp] using hminEq
    have hB2 : (B n) ^ 2 = sigma n := Real.sq_sqrt (hsigmaPos n).le
    have hregB : Icc (T - (B n) ^ 2) T ⊆ D.regular := by
      simpa only [hB2] using hregSub (sigma n) (hsigmaRho n).le
    have hRmB : ∀ t ∈ Icc (T - (B n) ^ 2) T, ∀ y : M,
        normSq0S (I := I) (S.base.metric t) y 4
          (S.base.rm04 t y) ≤ K := by
      simpa only [hB2] using hRmSub (sigma n) (hsigmaRho n).le
    have hbdd := lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (B n)
      (by norm_num) (Real.sqrt_nonneg _) hregB hRmB x
      (lRegularizedCurve S T x Z (B n))
    have hcostLe := lCost_le_ray_bdd (I := I) S hS T x Z (B n)
      (by simpa only [B] using Real.sqrt_pos.2 (htau.trans (hsigmaGt n)))
      (hZreg n) hbdd
    have hcostLe' :
        lCost S T x (lExp S T x Z (sigma n)) (sigma n) ≤ aZ n := by
      simpa only [lExp, B, aZ, Real.sq_sqrt (hsigmaPos n).le] using hcostLe
    calc
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 (B n) =
          lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := hcostEq
      _ = lCost S T x (lExp S T x Z (sigma n)) (sigma n) := by
        rw [hWend n]
      _ ≤ aZ n := hcostLe'
      _ ≤ A := hA (Set.mem_range_self n)
  let Afix : Real := A - (-2 * R ^ 2 *
    ((Module.finrank Real E : Real) ^ 2 * Real.sqrt K)) * R
  have hWregEps (n : Nat) : eps ∈ lRegularizedDomain S T x (W n) :=
    lRegularizedDomain_segment S T x (W n) (hWdom n) heps.le (hepsB n)
  have hWactEps (n : Nat) :
      lRegularizedAction S T (lRegularizedCurve S T x (W n)) 0 eps ≤ Afix :=
    original_ray_prefix_action_bound S hS K T x (W n) eps (B n) R A
      heps (hepsB n) (hBR n) hregR hRmR (hWdom n) (hWact n)
  have hWbounded : Bornology.IsBounded (Set.range W) :=
    lRegInit_bound_of_rm (I := I) S hS K T hg x eps Afix heps
      hregEps hRmEps W hWregEps hWactEps
  let : ProperSpace (TangentSpace I x) := FiniteDimensional.proper Real _
  obtain ⟨W0, _hW0cl, phi, hphi, hWlim⟩ :=
    tendsto_subseq_of_bounded hWbounded (fun n ↦ Set.mem_range_self n)
  have hsigmaSub : Tendsto (fun n ↦ sigma (phi n)) atTop (nhds tau) :=
    hsigmaLim.comp hphi.tendsto_atTop
  have hWdown (n : Nat) : (W (phi n), tau) ∈ lMinDomain S T x :=
    lMinDomain_down_of_rm S hS K T x (W (phi n)) (hWmin (phi n))
      htau (hsigmaGt (phi n)).le
      (hRmSub (sigma (phi n)) (hsigmaRho (phi n)).le)
  have hW0reg : Real.sqrt tau ∈ lRegularizedDomain S T x W0 :=
    lRegDomain_lim_of_rm (I := I) S hS K T hg x eps Afix heps
      hregEps hRmEps (fun n ↦ hWregEps (phi n))
      (fun n ↦ hWactEps (phi n)) hWlim
  have hW0dom : (W0, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x W0 tau).2 ⟨htau, htau.le, hW0reg⟩
  have hbddTau (y : M) :
      BddBelow {r : Real | ∃ alpha : Real → M,
        ContMDiff 𝓘(Real, Real) I 1 alpha ∧
          alpha 0 = x ∧ alpha (Real.sqrt tau) = y ∧
          lRegularizedAction S T alpha 0 (Real.sqrt tau) = r} :=
    lRegularizedCosts_bdd_rm (I := I) S hS K T 0 eps (by norm_num)
      heps.le hregEps hRmEps x y
  have hW0min : (W0, tau) ∈ lMinDomain S T x :=
    lMinVec_lim_of_bdd S hS T x hWdown hWlim hW0dom hbddTau
  have hWpair : Tendsto (fun n ↦ (W (phi n), sigma (phi n))) atTop
      (nhds (W0, tau)) := hWlim.prodMk_nhds hsigmaSub
  have hZpair : Tendsto (fun n ↦ (Z, sigma (phi n))) atTop
      (nhds (Z, tau)) := tendsto_const_nhds.prodMk_nhds hsigmaSub
  have hWExpAt : ContinuousAt
      (fun p : E × Real ↦ lExp S T x p.1 p.2) (W0, tau) :=
    ((lExp_smoothOn S hS T x) (W0, tau) hW0dom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hW0dom)
  have hZExpAt : ContinuousAt
      (fun p : E × Real ↦ lExp S T x p.1 p.2) (Z, tau) :=
    ((lExp_smoothOn S hS T x) (Z, tau) hZdom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hZdom)
  have hWExpLim : Tendsto
      (fun n ↦ lExp S T x (W (phi n)) (sigma (phi n))) atTop
      (nhds (lExp S T x W0 tau)) := by
    have h := hWExpAt.tendsto.comp hWpair
    convert h using 1 ; rfl
  have hZExpLim : Tendsto
      (fun n ↦ lExp S T x Z (sigma (phi n))) atTop
      (nhds (lExp S T x Z tau)) := by
    have h := hZExpAt.tendsto.comp hZpair
    convert h using 1 ; rfl
  have hend0 : lExp S T x W0 tau = lExp S T x Z tau := by
    apply tendsto_nhds_unique hWExpLim
    exact hZExpLim.congr'
      (Filter.Eventually.of_forall fun n ↦ (hWend (phi n)).symm)
  by_cases hW0ne : W0 ≠ Z
  · exact ⟨W0, hW0ne, hW0min, hend0⟩
  have hW0eq : W0 = Z := not_ne_iff.mp hW0ne
  have hlocal := lExpTime_local (I := I) S hS T x Z tau hZdom hconj
  obtain ⟨Phi, hPhiSrc, hPhiEq⟩ := hlocal
  have hWpairZ : Tendsto (fun n ↦ (W (phi n), sigma (phi n))) atTop
      (nhds (Z, tau)) := by
    simpa only [hW0eq] using hWpair
  have hWsrc : ∀ᶠ n in atTop,
      (W (phi n), sigma (phi n)) ∈ Phi.source :=
    hWpairZ.eventually (Phi.open_source.mem_nhds hPhiSrc)
  have hZsrc : ∀ᶠ n in atTop,
      (Z, sigma (phi n)) ∈ Phi.source :=
    hZpair.eventually (Phi.open_source.mem_nhds hPhiSrc)
  obtain ⟨n, hnW, hnZ⟩ := (hWsrc.and hZsrc).exists
  have hpairEq : (W (phi n), sigma (phi n)) = (Z, sigma (phi n)) := by
    apply Phi.injOn hnW hnZ
    rw [← hPhiEq hnW, ← hPhiEq hnZ]
    exact Prod.ext (hWend (phi n)) rfl
  exact ((hWne (phi n)) (congrArg Prod.fst hpairEq)).elim

theorem lCut_split_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau rho : ℝ) (htr : tau < rho)
    (hreg : Icc (T - rho) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - rho) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K) :
    lCutImage S T x tau = lCutConj S T x tau ∪ lCutMulti S T x tau := by
  ext y
  constructor
  · rintro ⟨Z, hcut, rfl⟩
    rcases lCut_alt_of_rm S hS K T hg x Z tau rho hcut htr hreg hRm with
      hconj | ⟨W, hWne, hWmin, hend⟩
    · exact Or.inl ⟨Z, hcut, hconj, rfl⟩
    · exact Or.inr ⟨Z, hcut, W, hWne, hWmin, hend, rfl⟩
  · rintro (⟨Z, hcut, _hconj, rfl⟩ |
      ⟨Z, hcut, _W, _hWne, _hWmin, _hend, rfl⟩)
    · exact ⟨Z, hcut, rfl⟩
    · exact ⟨Z, hcut, rfl⟩

end DifferentialGeometry.PDE.RicciFlow

end
