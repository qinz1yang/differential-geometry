import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.RawMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.PrefixMinimum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Set
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

section Basic

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
def IsLMinVec
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Prop :=
  (Z, tau) ∈ lExpPosDom S T x ∧
    lLength S T (fun r : Real => lExp S T x Z r) 0 tau =
      lCost S T x (lExp S T x Z tau) tau

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
def lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    Set (E × Real) :=
  {p | IsLMinVec S T x p.1 p.2}

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem mem_lMinDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) :
    (Z, tau) ∈ lMinDomain S T x ↔ IsLMinVec S T x Z tau :=
  Iff.rfl

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem lMinDomain_pos
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real)
    (h : (Z, tau) ∈ lMinDomain S T x) : 0 < tau :=
  ((mem_lExpPosDom S T x Z tau).1
    ((mem_lMinDomain S T x Z tau).1 h).1).1

end Basic

section Compact

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem exists_lMinVec
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 tau : Real) (htau : 0 < tau)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular) :
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y := by
  obtain ⟨alpha, Z, _hcurve, hmax, hdom, hExp, _hend, hcost, _hmin⟩ :=
    exists_lMinimizer (I := I) S hS T t0 t1 tau htau htime hback
      x y alpha0 halpha0 h00 h0t hreg
  refine ⟨Z, (mem_lMinDomain S T x Z tau).2 ⟨hdom, ?_⟩, hExp⟩
  calc
    lLength S T (fun r : Real => lExp S T x Z r) 0 tau =
        lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) := by
      change lLength S T
          (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 tau = _
      rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
        sqrtReparam (lRegCurve S T x Z) by rfl]
      exact lLength_sqrt (I := I) S T (lRegCurve S T x Z) tau htau.le
    _ = lRegAction S T alpha 0 (Real.sqrt tau) := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) (Real.sqrt tau) := by
        simpa only [uIoo_of_le (Real.sqrt_nonneg tau)] using hs
      exact hmax ⟨hs'.1.le, hs'.2.le⟩
    _ = lLength S T (sqrtReparam alpha) 0 tau :=
      (lLength_sqrt (I := I) S T alpha tau htau.le).symm
    _ = lCost S T x y tau := hcost
    _ = lCost S T x (lExp S T x Z tau) tau := by rw [hExp]

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinDomain_down
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) {sigma tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hsigma : 0 < sigma) (hle : sigma ≤ tau) :
    (Z, sigma) ∈ lMinDomain S T x := by
  rcases lt_or_eq_of_le hle with hlt | rfl
  · have hvec := (mem_lMinDomain S T x Z tau).1 hmin
    have htauPos := hvec.1
    have hsigmaPos : (Z, sigma) ∈ lExpPosDom S T x :=
      lExpPosDom_down S T x Z htauPos hsigma hle
    apply (mem_lMinDomain S T x Z sigma).2
    refine ⟨hsigmaPos, ?_⟩
    rcases (mem_lExpPosDom S T x Z tau).1 htauPos with
      ⟨htau, _htau0, htauDom⟩
    rcases (mem_lExpPosDom S T x Z sigma).1 hsigmaPos with
      ⟨_hsigma, _hsigma0, hsigmaDom⟩
    let gamma : Real → M := lRegCurve S T x Z
    have hsqrtTau : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
    have hsqrtSigma : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hsigma
    have hsqrtLt : Real.sqrt sigma < Real.sqrt tau :=
      Real.sqrt_lt_sqrt hsigma.le hlt
    have hgammaC1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (0 : Real) (Real.sqrt tau)) := by
      simpa only [gamma] using lRegCurve_c1On S hS T x Z htauDom
    have hregTau : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
        T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact lExpPosDom_reg S T x Z htauPos hs
    have hbackTau : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
        T - s ^ 2 ∈ Icc (T - tau) T := by
      intro s hs
      have hsSq : s ^ 2 ≤ tau := by
        calc
          s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
            (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 hs.2
          _ = tau := Real.sq_sqrt htau.le
      exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have htimeTau : Icc (T - tau) T ⊆ D.carrier := by
      intro r hr
      have hnonneg : 0 ≤ T - r := by linarith [hr.2]
      have hleTau : T - r ≤ tau := by linarith [hr.1]
      have hsqrtMem : Real.sqrt (T - r) ∈
          Icc (0 : Real) (Real.sqrt tau) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hleTau⟩
      have hregR := lExpPosDom_reg S T x Z htauPos hsqrtMem
      have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
        rw [Real.sq_sqrt hnonneg]
        ring
      exact D.regular_subset (by simpa only [heq] using hregR)
    have hcostTau : lRegAction S T gamma 0 (Real.sqrt tau) =
        lRegCostC1 S T 0 (Real.sqrt tau) x (gamma (Real.sqrt tau)) := by
      calc
        lRegAction S T gamma 0 (Real.sqrt tau) =
            lLength S T (sqrtReparam gamma) 0 tau :=
          (lLength_sqrt (I := I) S T gamma tau htau.le).symm
        _ = lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := rfl
        _ = lCost S T x (lExp S T x Z tau) tau := hvec.2
        _ = lRegCostC1 S T 0 (Real.sqrt tau) x
            (lExp S T x Z tau) := lCost_eq_reg (I := I) S T x
              (lExp S T x Z tau) tau htau.le
        _ = lRegCostC1 S T 0 (Real.sqrt tau) x
            (gamma (Real.sqrt tau)) := by rfl
    have hminTau : ∀ delta : Real → M,
        ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
        delta 0 = gamma 0 →
        delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
        lRegAction S T gamma 0 (Real.sqrt tau) ≤
          lRegAction S T delta 0 (Real.sqrt tau) := by
      intro delta hdelta hd0 hdt
      rw [hcostTau]
      exact lRegCostC1_le (I := I) S hS T (T - tau) T 0
        (Real.sqrt tau) hsqrtTau.le htimeTau hbackTau x
        (gamma (Real.sqrt tau)) delta hdelta
        (hd0.trans (by simp only [gamma, lRegCurve_zero])) hdt hregTau
    have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
      hS.smoothMetric
    have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
    have hminSigma := lReg_prefix_min (I := I) S hMet hSc T 0
      (Real.sqrt sigma) (Real.sqrt tau) hsqrtSigma hsqrtLt gamma hgammaC1
      hregTau hminTau
    have hgammaSigma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
        (Icc (0 : Real) (Real.sqrt sigma)) := by
      simpa only [gamma] using lRegCurve_c1On S hS T x Z hsigmaDom
    have hregSigma : ∀ s ∈ Icc (0 : Real) (Real.sqrt sigma),
        T - s ^ 2 ∈ D.regular := by
      intro s hs
      exact lExpPosDom_reg S T x Z hsigmaPos hs
    have hbackSigma : ∀ s ∈ Icc (0 : Real) (Real.sqrt sigma),
        T - s ^ 2 ∈ Icc (T - sigma) T := by
      intro s hs
      have hsSq : s ^ 2 ≤ sigma := by
        calc
          s ^ 2 ≤ (Real.sqrt sigma) ^ 2 :=
            (sq_le_sq₀ hs.1 (Real.sqrt_nonneg sigma)).2 hs.2
          _ = sigma := Real.sq_sqrt hsigma.le
      exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
    have htimeSigma : Icc (T - sigma) T ⊆ D.carrier := by
      intro r hr
      have hnonneg : 0 ≤ T - r := by linarith [hr.2]
      have hleSigma : T - r ≤ sigma := by linarith [hr.1]
      have hsqrtMem : Real.sqrt (T - r) ∈
          Icc (0 : Real) (Real.sqrt sigma) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hleSigma⟩
      have hregR := lExpPosDom_reg S T x Z hsigmaPos hsqrtMem
      have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
        rw [Real.sq_sqrt hnonneg]
        ring
      exact D.regular_subset (by simpa only [heq] using hregR)
    have hcostSigma : lRegAction S T gamma 0 (Real.sqrt sigma) =
        lRegCostC1 S T 0 (Real.sqrt sigma) x
          (gamma (Real.sqrt sigma)) := by
      apply lRegCostC1_eq_on (I := I) S hS T (T - sigma) T 0
        (Real.sqrt sigma) hsqrtSigma htimeSigma hbackSigma x
        (gamma (Real.sqrt sigma)) gamma hgammaSigma
      · simp only [gamma, lRegCurve_zero]
      · rfl
      · exact hregSigma
      · intro delta hdelta hd0 hdt
        exact hminSigma delta hdelta.contMDiffOn
          (hd0.trans (by simp only [gamma, lRegCurve_zero])) hdt
    calc
      lLength S T (fun r : Real ↦ lExp S T x Z r) 0 sigma =
          lRegAction S T gamma 0 (Real.sqrt sigma) := by
        change lLength S T
            (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 sigma = _
        rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
          sqrtReparam gamma by rfl]
        exact lLength_sqrt (I := I) S T gamma sigma hsigma.le
      _ = lRegCostC1 S T 0 (Real.sqrt sigma) x
          (gamma (Real.sqrt sigma)) := hcostSigma
      _ = lCost S T x (gamma (Real.sqrt sigma)) sigma :=
        (lCost_eq_reg (I := I) S T x (gamma (Real.sqrt sigma)) sigma
          hsigma.le).symm
      _ = lCost S T x (lExp S T x Z sigma) sigma := by rfl
  · exact hmin

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinFiber_ord
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) :
    Set.OrdConnected {tau : Real | (Z, tau) ∈ lMinDomain S T x} := by
  rw [Set.ordConnected_iff]
  intro sigma hsigma tau htau _hle r hr
  have hsigmaPos : 0 < sigma := lMinDomain_pos S T x Z sigma hsigma
  exact lMinDomain_down S hS T x Z htau
    (lt_of_lt_of_le hsigmaPos hr.1) hr.2

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
