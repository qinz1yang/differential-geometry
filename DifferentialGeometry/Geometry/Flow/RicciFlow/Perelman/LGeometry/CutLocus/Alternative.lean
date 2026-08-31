import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerClosedness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.LocalExponentialMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.InitialVector.VariableEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.DomainContinuation

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bornology Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem lCut_alt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (tau : Real)
    (hcut : IsGreatest
      {sigma : Real | ((Z : E), sigma) ∈ lMinDomain S T x} tau) :
    IsLConj S T x Z tau ∨
      ∃ W : TangentSpace I x, W ≠ Z ∧
        ((W : E), tau) ∈ lMinDomain S T x ∧
          lExp S T x W tau = lExp S T x Z tau := by
  classical
  by_cases hconj : IsLConj S T x Z tau
  · exact Or.inl hconj
  right
  have hZmin : (Z, tau) ∈ lMinDomain S T x := hcut.1
  have hZdom : ((Z : E), tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hZmin).1
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hZmin
  let z : E := Z
  let U : Set Real :=
    (fun sigma : Real ↦ (z, sigma)) ⁻¹' lExpPosDom S T x
  have hUopen : IsOpen U := by
    apply (lExpPosDom_open S hS T x).preimage
    exact continuous_const.prodMk continuous_id
  have htauU : tau ∈ U := by
    change ((Z : E), tau) ∈ lExpPosDom S T x
    exact hZdom
  obtain ⟨u, huAnti, hutau, hulim⟩ :=
    exists_seq_strictAnti_tendsto tau
  have huU : ∀ᶠ n in atTop, u n ∈ U :=
    hulim.eventually (hUopen.mem_nhds htauU)
  obtain ⟨N, hNU⟩ := (eventually_atTop.1 huU)
  let sigma : Nat → Real := fun n ↦ u (n + N)
  have hsigmaAnti : StrictAnti sigma := by
    intro a b hab
    exact huAnti (Nat.add_lt_add_right hab N)
  have hsigmaGt (n : Nat) : tau < sigma n := hutau (n + N)
  have hsigmaPos (n : Nat) : 0 < sigma n := htau.trans (hsigmaGt n)
  have hsigmaLim : Tendsto sigma atTop (nhds tau) := by
    simpa only [sigma, Function.comp_def] using
      hulim.comp (tendsto_add_atTop_nat N)
  have hZdomN (n : Nat) : ((Z : E), sigma n) ∈ lExpPosDom S T x := by
    have hmem : u (n + N) ∈ U := hNU (n + N) (by omega)
    change ((Z : E), u (n + N)) ∈ lExpPosDom S T x at hmem
    exact hmem
  have hZnotMin (n : Nat) : (Z, sigma n) ∉ lMinDomain S T x := by
    intro hmin
    exact (not_lt_of_ge (hcut.2 hmin)) (hsigmaGt n)
  have hminExists (n : Nat) :
      ∃ W : TangentSpace I x,
        (W, sigma n) ∈ lMinDomain S T x ∧
          lExp S T x W (sigma n) = lExp S T x Z (sigma n) :=
    exists_lMinVec_ray S hS T x Z (sigma n) (hZdomN n)
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
  let R : Real := Real.sqrt (sigma 0)
  have heps : 0 < eps := by
    simpa only [eps] using Real.sqrt_pos.2 htau
  have hepsB (n : Nat) : eps ≤ B n := by
    simpa only [eps, B] using Real.sqrt_le_sqrt (hsigmaGt n).le
  have hsigmaLe (n : Nat) : sigma n ≤ sigma 0 :=
    hsigmaAnti.antitone (Nat.zero_le n)
  have hBR (n : Nat) : B n ≤ R := by
    simpa only [B, R] using Real.sqrt_le_sqrt (hsigmaLe n)
  have hsig0 : 0 < sigma 0 := htau.trans (hsigmaGt 0)
  have hR2 : R ^ 2 = sigma 0 := by
    simpa only [R] using Real.sq_sqrt hsig0.le
  have hslab : Set.Icc (T - R ^ 2) T ⊆ D.regular := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hle : T - r ≤ sigma 0 := by
      rw [hR2] at hr
      linarith [hr.1]
    have hsqrtMem : Real.sqrt (T - r) ∈
        Set.Icc (0 : Real) (Real.sqrt (sigma 0)) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    have hreg := lExpPosDom_reg S T x Z (hZdomN 0) hsqrtMem
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hreg
  have hWdom (n : Nat) : B n ∈ lRegDomain S T x (W n) := by
    have hdom := ((mem_lMinDomain S T x (W n) (sigma n)).1 (hWmin n)).1
    have hdata := (mem_lExpPosDom S T x (W n) (sigma n)).1 hdom
    simpa only [B] using hdata.2.2
  have hZreg (n : Nat) : B n ∈ lRegDomain S T x Z := by
    have hdata := (mem_lExpPosDom S T x Z (sigma n)).1 (hZdomN n)
    simpa only [B] using hdata.2.2
  let aZ : Nat → Real := fun n ↦
    lRegAction S T (lRegCurve S T x Z) 0 (B n)
  have hBLim : Tendsto B atTop (nhds eps) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsigmaLim
    change Tendsto (fun n ↦ Real.sqrt (sigma n)) atTop
      (nhds (Real.sqrt tau))
    convert h using 1 ; rfl
  have haZlim : Tendsto aZ atTop
      (nhds (lRegAction S T (lRegCurve S T x Z) 0 eps)) := by
    simpa only [aZ] using lRayAct_tendsto (I := I) S hS T x heps
      (by simpa only [eps] using
        ((mem_lExpPosDom S T x Z tau).1 hZdom).2.2)
      (tendsto_const_nhds : Tendsto (fun _ : Nat ↦ Z) atTop (nhds Z)) hBLim
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto aZ haZlim).bddAbove
  have hWact (n : Nat) :
      lRegAction S T (lRegCurve S T x (W n)) 0 (B n) ≤ A := by
    have hminEq := ((mem_lMinDomain S T x (W n) (sigma n)).1 (hWmin n)).2
    have hcostEq :
        lRegAction S T (lRegCurve S T x (W n)) 0 (B n) =
          lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := by
      calc
        lRegAction S T (lRegCurve S T x (W n)) 0 (B n) =
            lLength S T (squareRootReparametrization (lRegCurve S T x (W n))) 0
              (sigma n) := by
          simpa only [B] using
            (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x (W n))
              (sigma n) (hsigmaPos n).le).symm
        _ = lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := by
          rw [show squareRootReparametrization (lRegCurve S T x (W n)) =
            (fun r ↦ lRegCurve S T x (W n) (Real.sqrt r)) by rfl]
          simpa only [lExp] using hminEq
    have hcostLe := lCost_le_ray (I := I) S hS T x Z (B n)
      (by simpa only [B] using Real.sqrt_pos.2 (htau.trans (hsigmaGt n)))
      (hZreg n)
    have hcostLe' :
        lCost S T x (lExp S T x Z (sigma n)) (sigma n) ≤ aZ n := by
      simpa only [lExp, B, aZ, Real.sq_sqrt (hsigmaPos n).le] using hcostLe
    calc
      lRegAction S T (lRegCurve S T x (W n)) 0 (B n) =
          lCost S T x (lExp S T x (W n) (sigma n)) (sigma n) := hcostEq
      _ = lCost S T x (lExp S T x Z (sigma n)) (sigma n) := by
        rw [hWend n]
      _ ≤ aZ n := hcostLe'
      _ ≤ A := hA (Set.mem_range_self n)
  have hWbounded : Bornology.IsBounded (Set.range W) :=
    lRegInit_var (I := I) S hS T x W B eps R A heps hepsB hBR
      hslab hWdom hWact
  let : ProperSpace (TangentSpace I x) := FiniteDimensional.proper Real _
  obtain ⟨W0, _hW0cl, phi, hphi, hWlim⟩ :=
    tendsto_subseq_of_bounded hWbounded (fun n ↦ Set.mem_range_self n)
  have hsigmaSub : Tendsto (fun n ↦ sigma (phi n)) atTop (nhds tau) :=
    hsigmaLim.comp hphi.tendsto_atTop
  have hWdown (n : Nat) : (W (phi n), tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x (W (phi n)) (hWmin (phi n)) htau
      (hsigmaGt (phi n)).le
  have hW0regR : R ∈ lRegDomain S T x W0 :=
    lRegDomain_of_slab S hS T x W0 R (Real.sqrt_nonneg _) hslab
  have hW0reg : Real.sqrt tau ∈ lRegDomain S T x W0 :=
    lRegDomain_seg S T x W0 hW0regR (Real.sqrt_nonneg tau)
      (by simpa only [R] using Real.sqrt_le_sqrt (hsigmaGt 0).le)
  have hW0dom : (W0, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x W0 tau).2 ⟨htau, htau.le, hW0reg⟩
  have hW0min : (W0, tau) ∈ lMinDomain S T x :=
    lMinVec_lim S hS T x hWdown hWlim hW0dom
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

end DifferentialGeometry.PDE.RicciFlow.Perelman
