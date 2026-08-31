import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionContinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Set
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

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinVec_lim
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z : Nat → TangentSpace I x}
    {Z₀ : TangentSpace I x} {tau : Real}
    (hmin : ∀ n, (Z n, tau) ∈ lMinDomain S T x)
    (hZ : Tendsto Z atTop (nhds Z₀))
    (hdom : (Z₀, tau) ∈ lExpPosDom S T x) :
    (Z₀, tau) ∈ lMinDomain S T x := by
  have hdomData := (mem_lExpPosDom S T x Z₀ tau).1 hdom
  rcases hdomData with ⟨htau, _htau0, hbDom⟩
  let b : Real := Real.sqrt tau
  let gamma : Real → M := lRegCurve S T x Z₀
  let y : M := lExp S T x Z₀ tau
  let q : Nat → M := fun n ↦ lExp S T x (Z n) tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lExpPosDom_reg S T x Z₀ hdom (by simpa only [b] using hs)
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
          (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 (by simpa only [b] using hs.2)
        _ = tau := Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have htime : Icc (T - tau) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hleTau : T - r ≤ tau := by linarith [hr.1]
    have hsqrtMem : Real.sqrt (T - r) ∈ Icc (0 : Real) b :=
      ⟨Real.sqrt_nonneg _, by
        simpa only [b] using Real.sqrt_le_sqrt hleTau⟩
    have hregR := lExpPosDom_reg S T x Z₀ hdom hsqrtMem
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heq] using hregR)
  have hpair : Tendsto (fun n ↦ (Z n, tau)) atTop (nhds (Z₀, tau)) :=
    hZ.prodMk_nhds tendsto_const_nhds
  have hExpAt : ContinuousAt
      (fun p : E × Real ↦ lExp S T x p.1 p.2) (Z₀, tau) :=
    ((lExp_smoothOn S hS T x) (Z₀, tau) hdom).continuousWithinAt.continuousAt
      ((lExpPosDom_open S hS T x).mem_nhds hdom)
  have hq : Tendsto q atTop (nhds y) := by
    have h := hExpAt.tendsto.comp hpair
    change Tendsto (fun n ↦ lExp S T x (Z n) tau) atTop
      (nhds (lExp S T x Z₀ tau))
    convert h using 1 ; rfl
  have hactLim : Tendsto
      (fun n ↦ lRegAction S T (lRegCurve S T x (Z n)) 0 b)
      atTop (nhds (lRegAction S T gamma 0 b)) := by
    have hcontinuous := continuousAt_lRegAction_lRegCurve (I := I) S hS T x hb hbDom
    have hresult := hcontinuous.tendsto.comp
      (hZ.prodMk_nhds
        (tendsto_const_nhds : Tendsto (fun _ : Nat ↦ b) atTop (nhds b)))
    change Tendsto
      (fun n ↦ lRegAction S T (lRegCurve S T x (Z n)) 0 b)
      atTop (nhds (lRegAction S T (lRegCurve S T x Z₀) 0 b)) at hresult
    simpa only [gamma] using hresult
  have hactEq (n : Nat) :
      lRegAction S T (lRegCurve S T x (Z n)) 0 b =
        lCost S T x (q n) tau := by
    have hn := ((mem_lMinDomain S T x (Z n) tau).1 (hmin n)).2
    calc
      lRegAction S T (lRegCurve S T x (Z n)) 0 b =
          lLength S T (squareRootReparametrization (lRegCurve S T x (Z n))) 0 tau := by
        simpa only [b] using
          (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x (Z n)) tau htau.le).symm
      _ = lCost S T x (q n) tau := by
        rw [show squareRootReparametrization (lRegCurve S T x (Z n)) =
          (fun r ↦ lRegCurve S T x (Z n) (Real.sqrt r)) by rfl]
        simpa only [lExp, q] using hn
  have hgammaC1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) b) := by
    simpa only [gamma, b] using lRegCurve_c1On S hS T x Z₀ hbDom
  have hmin0 : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = x → delta b = y →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    by_contra hnot
    have hlt : lRegAction S T delta 0 b < lRegAction S T gamma 0 b :=
      lt_of_not_ge hnot
    let A : Real :=
      (lRegAction S T delta 0 b + lRegAction S T gamma 0 b) / 2
    have hdeltaA : lRegAction S T delta 0 b < A := by
      dsimp only [A]
      linarith
    have hcostEvent : ∀ᶠ n in atTop, lCost S T x (q n) tau < A :=
      lCost_lt_event (I := I) S hS T (T - tau) T tau htau htime
        (by simpa only [b] using hback) x y delta hdelta hd0 hdb
        (by simpa only [b] using hreg) A hdeltaA q hq
    have hactEvent : ∀ᶠ n in atTop,
        lRegAction S T (lRegCurve S T x (Z n)) 0 b ≤ A := by
      filter_upwards [hcostEvent] with n hn
      rw [hactEq n]
      exact hn.le
    have hle : lRegAction S T gamma 0 b ≤ A :=
      le_of_tendsto hactLim hactEvent
    dsimp only [A] at hle
    linarith
  have hcostEq : lRegAction S T gamma 0 b =
      lRegCostC1 S T 0 b x y :=
    lRegCostC1_eq_on (I := I) S hS T (T - tau) T 0 b hb htime
      hback x y gamma hgammaC1 (by simp only [gamma, lRegCurve_zero]) rfl
      hreg hmin0
  apply (mem_lMinDomain S T x Z₀ tau).2
  refine ⟨hdom, ?_⟩
  calc
    lLength S T (fun r : Real ↦ lExp S T x Z₀ r) 0 tau =
        lRegAction S T gamma 0 b := by
      change lLength S T
          (fun r : Real ↦ lRegCurve S T x Z₀ (Real.sqrt r)) 0 tau = _
      rw [show (fun r : Real ↦ lRegCurve S T x Z₀ (Real.sqrt r)) =
        squareRootReparametrization (lRegCurve S T x Z₀) by rfl]
      exact lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x Z₀) tau htau.le
    _ = lRegCostC1 S T 0 b x y := hcostEq
    _ = lCost S T x (lExp S T x Z₀ tau) tau := by
      simpa only [b, y] using
        (lCost_eq_reg (I := I) S T x (lExp S T x Z₀ tau) tau htau.le).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman
