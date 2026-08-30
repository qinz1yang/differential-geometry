import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortMinimizing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmallEndpoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.SmallTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bornology Bundle Filter Set Topology
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem lInj_eventually
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    (Z : TangentSpace I x) (hT : T ∈ D.regular) :
    ∀ᶠ tau in 𝓝[>] (0 : Real), Z ∈ lInjDomain (E := E) S T x tau := by
  let P : Set Real := {tau | Z ∈ lInjDomain (E := E) S T x tau}
  change P ∈ 𝓝[>] (0 : Real)
  by_contra hP
  have hbad : ∀ n : Nat, ∃ tau : Real,
      tau ∈ Metric.ball 0 (1 / ((n : Real) + 1)) ∧ tau ∈ Ioi 0 ∧ tau ∉ P := by
    intro n
    have hr : 0 < (1 / ((n : Real) + 1) : Real) := by positivity
    by_contra hnone
    push Not at hnone
    apply hP
    filter_upwards
      [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds 0 hr),
        self_mem_nhdsWithin] with tau htau htau0
    exact hnone tau htau htau0
  choose tau htauBall htauPos htauBad using hbad
  have htauLim : Tendsto tau atTop (𝓝 (0 : Real)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun n ↦ dist_nonneg
    · exact Filter.Eventually.of_forall fun n ↦ (htauBall n).le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  let sigma : Nat → Real := fun n ↦ 2 * tau n
  let B : Nat → Real := fun n ↦ Real.sqrt (sigma n)
  have hsigmaPos (n : Nat) : 0 < sigma n := by
    dsimp only [sigma]
    have ht := htauPos n
    change 0 < tau n at ht
    linarith
  have hBPos (n : Nat) : 0 < B n := by
    exact Real.sqrt_pos.2 (hsigmaPos n)
  have hBsq (n : Nat) : (B n) ^ 2 = sigma n := by
    exact Real.sq_sqrt (hsigmaPos n).le
  have hsigmaLim : Tendsto sigma atTop (𝓝 (0 : Real)) := by
    simpa only [sigma, mul_zero] using
      (tendsto_const_nhds.mul htauLim :
        Tendsto (fun n : Nat ↦ (2 : Real) * tau n) atTop (𝓝 ((2 : Real) * 0)))
  have hBLim : Tendsto B atTop (𝓝 (0 : Real)) := by
    change Tendsto (Real.sqrt ∘ sigma) atTop (𝓝 (0 : Real))
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsigmaLim
  have hBLimGT : Tendsto B atTop (𝓝[>] (0 : Real)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hBLim, ?_⟩
    exact Filter.Eventually.of_forall hBPos
  let qact : Nat → Real := fun n ↦
    lRegAction S T (lRegCurve S T x Z) 0 (B n) / (2 * B n)
  have hqactLim : Tendsto qact atTop
      (𝓝 ((S.base.metric T).inner x Z Z)) := by
    simpa only [qact, Function.comp_def] using
      (lRayAct_zero_lim S hS T x Z hT).comp hBLimGT
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto qact hqactLim).bddAbove
  let A0 : Real := 2 * A
  have hZact (n : Nat) :
      lRegAction S T (lRegCurve S T x Z) 0 (B n) ≤ A0 * B n := by
    have hq := hA (Set.mem_range_self n)
    rw [div_le_iff₀ (mul_pos (by norm_num) (hBPos n))] at hq
    dsimp only [A0]
    nlinarith
  obtain ⟨r, hr, hrreg⟩ := Metric.isOpen_iff.mp D.regular_isOpen T hT
  let R : Real := Real.sqrt (r / 2)
  have hR : 0 < R := Real.sqrt_pos.2 (div_pos hr (by norm_num))
  have hRsq : R ^ 2 = r / 2 := by
    exact Real.sq_sqrt (div_nonneg hr.le (by norm_num))
  have hslab : Icc (T - R ^ 2) T ⊆ D.regular := by
    intro t ht
    apply hrreg
    rw [Metric.mem_ball, Real.dist_eq]
    have hsub : 0 ≤ T - t := sub_nonneg.mpr ht.2
    rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]
    have hle : T - t ≤ R ^ 2 := by linarith [ht.1]
    rw [hRsq] at hle
    linarith
  have hBR : ∀ᶠ n in atTop, B n ≤ R :=
    (tendsto_order.1 hBLim).2 R hR |>.mono fun _ h ↦ h.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hBR
  let Bt : Nat → Real := fun n ↦ B (n + N)
  let taut : Nat → Real := fun n ↦ tau (n + N)
  let sigmat : Nat → Real := fun n ↦ sigma (n + N)
  have hBtPos (n : Nat) : 0 < Bt n := hBPos (n + N)
  have hBtR (n : Nat) : Bt n ≤ R := hN (n + N) (by omega)
  have hsigmatPos (n : Nat) : 0 < sigmat n := hsigmaPos (n + N)
  have hBtSq (n : Nat) : (Bt n) ^ 2 = sigmat n := hBsq (n + N)
  have hslabBt (n : Nat) : Icc (T - (Bt n) ^ 2) T ⊆ D.regular := by
    intro t ht
    apply hslab
    have hsq : (Bt n) ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (hBtPos n).le hR.le).2 (hBtR n)
    exact ⟨by linarith [ht.1], ht.2⟩
  have hZdom (n : Nat) : Bt n ∈ lRegDomain S T x Z :=
    lRegDomain_of_slab S hS T x Z (Bt n) (hBtPos n).le (hslabBt n)
  have hZexp (n : Nat) : (Z, sigmat n) ∈ lExpPosDom S T x := by
    apply (mem_lExpPosDom S T x Z (sigmat n)).2
    refine ⟨hsigmatPos n, (hsigmatPos n).le, ?_⟩
    simpa only [Bt, sigmat, B, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hsigmatPos n).le] using hZdom n
  have hWexists (n : Nat) : ∃ W : TangentSpace I x,
      (W, sigmat n) ∈ lMinDomain S T x ∧
        lExp S T x W (sigmat n) = lExp S T x Z (sigmat n) :=
    exists_lMinVec_ray S hS T x Z (sigmat n) (hZexp n)
  let W : Nat → TangentSpace I x := fun n ↦ (hWexists n).choose
  have hWmin (n : Nat) : (W n, sigmat n) ∈ lMinDomain S T x :=
    (hWexists n).choose_spec.1
  have hWend (n : Nat) :
      lExp S T x (W n) (sigmat n) = lExp S T x Z (sigmat n) :=
    (hWexists n).choose_spec.2
  have hWdom (n : Nat) : Bt n ∈ lRegDomain S T x (W n) := by
    have hdata := (mem_lExpPosDom S T x (W n) (sigmat n)).1
      ((mem_lMinDomain S T x (W n) (sigmat n)).1 (hWmin n)).1
    simpa only [Bt, sigmat, B, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (hsigmatPos n).le] using hdata.2.2
  have hWact (n : Nat) :
      lRegAction S T (lRegCurve S T x (W n)) 0 (Bt n) ≤ A0 * Bt n := by
    have hminEq := ((mem_lMinDomain S T x (W n) (sigmat n)).1 (hWmin n)).2
    have hcostEq :
        lRegAction S T (lRegCurve S T x (W n)) 0 (Bt n) =
          lCost S T x (lExp S T x (W n) (sigmat n)) (sigmat n) := by
      calc
        lRegAction S T (lRegCurve S T x (W n)) 0 (Bt n) =
            lLength S T (sqrtReparam (lRegCurve S T x (W n))) 0 (sigmat n) := by
          rw [← hBtSq n]
          simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (hBtPos n).le] using
            (lLength_sqrt (I := I) S T (lRegCurve S T x (W n))
              ((Bt n) ^ 2) (sq_nonneg (Bt n))).symm
        _ = lCost S T x (lExp S T x (W n) (sigmat n)) (sigmat n) := by
          change lLength S T
            (fun r : Real ↦ lRegCurve S T x (W n) (Real.sqrt r))
              0 (sigmat n) =
            lCost S T x (lRegCurve S T x (W n) (Real.sqrt (sigmat n)))
              (sigmat n)
          exact hminEq
    have hcostLe := lCost_le_ray (I := I) S hS T x Z (Bt n)
      (hBtPos n) (hZdom n)
    have hcostLe' :
        lCost S T x (lExp S T x Z (sigmat n)) (sigmat n) ≤
          lRegAction S T (lRegCurve S T x Z) 0 (Bt n) := by
      rw [← hBtSq n]
      simpa only [lExp, Real.sqrt_sq_eq_abs, abs_of_nonneg (hBtPos n).le] using hcostLe
    calc
      lRegAction S T (lRegCurve S T x (W n)) 0 (Bt n) =
          lCost S T x (lExp S T x (W n) (sigmat n)) (sigmat n) := hcostEq
      _ = lCost S T x (lExp S T x Z (sigmat n)) (sigmat n) := by rw [hWend n]
      _ ≤ lRegAction S T (lRegCurve S T x Z) 0 (Bt n) := hcostLe'
      _ ≤ A0 * Bt n := hZact (n + N)
  have hWbounded : Bornology.IsBounded (Set.range W) :=
    lRegInit_shrink (I := I) S hS T x W Bt R A0 hBtPos hBtR hslab hWdom hWact
  obtain ⟨L, hWL⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : TangentSpace I x)).1 hWbounded
  let C : Real := max L (dist Z (0 : TangentSpace I x))
  have hWC (n : Nat) : W n ∈ Metric.closedBall (0 : TangentSpace I x) C := by
    exact Metric.mem_closedBall.mpr ((hWL (Set.mem_range_self n)).trans (le_max_left _ _))
  have hZC : Z ∈ Metric.closedBall (0 : TangentSpace I x) C := by
    exact Metric.mem_closedBall.mpr (le_max_right _ _)
  obtain ⟨epsC, hepsC, hCinj⟩ := lEnd_inj_small S hS T x C hT
  have hBC : ∀ᶠ n in atTop, Bt n < epsC := by
    have hBtLim : Tendsto Bt atTop (𝓝 (0 : Real)) := by
      simpa only [Bt, Function.comp_def] using hBLim.comp (tendsto_add_atTop_nat N)
    exact (tendsto_order.1 hBtLim).2 epsC hepsC
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hBC
  let n : Nat := N2
  have hEq : W n = Z := by
    apply hCinj (Bt n) (hBtPos n) (hN2 n le_rfl) (hWC n) hZC
    have hend := hWend n
    rw [← hBtSq n] at hend
    simpa only [lExp, Real.sqrt_sq_eq_abs, abs_of_nonneg (hBtPos n).le] using hend
  have hZmin : (Z, sigmat n) ∈ lMinDomain S T x := by
    simpa only [hEq] using hWmin n
  have hmem : Z ∈ lInjDomain (E := E) S T x (taut n) := by
    refine ⟨sigmat n, ?_, hZmin⟩
    dsimp only [sigmat, sigma, taut]
    have ht := htauPos (n + N)
    change 0 < tau (n + N) at ht
    linarith
  exact htauBad (n + N) hmem

end DifferentialGeometry.PDE.RicciFlow.Perelman
