import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactChartAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardSolutionRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem ramp_action_eq_of_length {D : RealTimeInterval}
    (Q : SolutionOn (I := 𝓡 3) (M := E3) D) (hQ : IsSolutionOn Q)
    (T a b L : ℝ) (y z : E3) (hL : 0 < L) (hlen : b - a = L)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    lRegularizedAction Q T
      (fun s => (extChartAt (𝓡 3) (0 : E3)).symm
        ((lChartRamp y z hL.le).toFun (s - a))) a b =
      lChartAction Q T a (0 : E3) (lChartRamp y z hL.le) := by
  subst L
  have hab : a < b := sub_pos.mp hL
  exact lRampAct_eq (I := 𝓡 3) Q hQ T a b (0 : E3) hab
    (by intro r _hr
        simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_target, mem_univ]) hreg

theorem standard_minimizer_action_bounds
    (S : StandardSolution) (T : ℝ)
    (hT : T ∈ S.val.domain) (hTpos : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ z : E3,
        normSq0S (I := 𝓡 3)
          (S.val.toSolutionOn.base.metric t) z 4
          (S.val.toSolutionOn.base.rm04 t z) ≤ K ^ 2) ∧
      ∀ x : E3, ∀ tau : ℝ, 0 < tau → tau < T →
        ∀ R : ℝ, 0 < R →
          Icc (T - tau) T ⊆
            (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular ∧
          ∃ A : ℝ, 0 ≤ A ∧
            (∀ z ∈ Metric.closedBall x R,
              lRegularizedAction S.val.toSolutionOn T
                (fun s : ℝ ↦ x + (s / Real.sqrt tau) • (z - x))
                0 (Real.sqrt tau) ≤ A) ∧
            (∀ W : TangentSpace (𝓡 3) x,
              (W, tau) ∈ lMinDomain S.val.toSolutionOn T x →
              lExp S.val.toSolutionOn T x W tau ∈
                Metric.closedBall x R →
              lRegularizedAction S.val.toSolutionOn T
                (lRegularizedCurve S.val.toSolutionOn T x W)
                0 (Real.sqrt tau) ≤ A) := by
  classical
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hTlife : ENNReal.ofReal T < S.val.lifetime :=
    ((mem_lifetimeInterval_carrier
      S.val.lifetime S.val.lifetime_pos T).mp hT).2
  obtain ⟨K, hK, hbound⟩ :=
    S.val.curvature_bound T hTpos.le hTlife
  have hRmClosed : ∀ t ∈ Icc (0 : ℝ) T, ∀ z : E3,
      normSq0S (I := 𝓡 3)
        (S.val.toSolutionOn.base.metric t) z 4
        (S.val.toSolutionOn.base.rm04 t z) ≤ K ^ 2 := by
    intro t ht z
    change normSq0S (S.val.metric t) z 4
      (metricRm04 (S.val.metric t) z) ≤ K ^ 2
    exact (Real.sqrt_le_iff.mp (hbound t ht z)).2
  refine ⟨K, hK, hRmClosed, ?_⟩
  intro x tau htau hlt R hR
  let b : ℝ := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hleft : 0 < T - tau := sub_pos.mpr hlt
  have hreg : Icc (T - tau) T ⊆
      (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular
      S.val.lifetime S.val.lifetime_pos t).mpr
        ⟨hleft.trans_le ht.1,
          (ENNReal.ofReal_le_ofReal ht.2).trans_lt hTlife⟩
  have hRmSlab : ∀ t ∈ Icc (T - tau) T, ∀ z : E3,
      normSq0S (I := 𝓡 3)
        (S.val.toSolutionOn.base.metric t) z 4
        (S.val.toSolutionOn.base.rm04 t z) ≤ K ^ 2 := by
    intro t ht z
    exact hRmClosed t ⟨(hleft.trans_le ht.1).le, ht.2⟩ z
  have hregSq : Icc (T - b ^ 2) T ⊆
      (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular := by
    simpa only [hb2] using hreg
  have hRmSq : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : E3,
      normSq0S (I := 𝓡 3)
        (S.val.toSolutionOn.base.metric t) z 4
        (S.val.toSolutionOn.base.rm04 t z) ≤ K ^ 2 := by
    simpa only [hb2] using hRmSlab
  have hclock : ∀ s ∈ Icc (0 : ℝ) b,
      T - s ^ 2 ∈
        (lifetimeInterval S.val.lifetime S.val.lifetime_pos).regular := by
    intro s hs
    have hs2 : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
        _ = tau := hb2
    exact hreg ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hcompact : IsCompact (Metric.closedBall x R) :=
    isCompact_closedBall x R
  have htarget : Metric.closedBall x R ⊆
      interior (extChartAt (𝓡 3) (0 : E3)).target := by
    intro z _hz
    simp only [extChartAt_model_space_eq_id,
      PartialEquiv.refl_target, interior_univ, mem_univ]
  have hchart (v : E3) :
      (extChartAt (𝓡 3) (0 : E3)).symm v = v := by
    rw [extChartAt_model_space_eq_id]
    rfl
  have hx : x ∈ Metric.closedBall x R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  obtain ⟨Cg, Cs, hCg, hCs, hrampBound⟩ :=
    lRampAct_slab_of_compact_chart
      S.val.toSolutionOn S.val.isSolutionOn T (0 : E3)
      (A := 0) (B := b) hclock hcompact htarget
  let alpha : E3 → ℝ → E3 :=
    fun z s ↦ x + (s / b) • (z - x)
  have halpha (z : E3) :
      ContMDiff (modelWithCornersSelf ℝ ℝ) (𝓡 3) 1 (alpha z) := by
    have haff : ContDiff ℝ 1 (alpha z) :=
      contDiff_const.add
        ((contDiff_id.div_const b).smul contDiff_const)
    exact haff.contMDiff
  have hstart (z : E3) : alpha z 0 = x := by
    simp only [alpha, zero_div, zero_smul, add_zero]
  have hend (z : E3) : alpha z (Real.sqrt tau) = z := by
    change x + (b / b) • (z - x) = z
    rw [div_self hb.ne', one_smul]
    abel
  have hactRamp (z : E3) :
      lRegularizedAction S.val.toSolutionOn T (alpha z) 0 b =
        lChartAction S.val.toSolutionOn T 0 (0 : E3)
          (lChartRamp x z hb.le) := by
    have hramp :
        lRegularizedAction S.val.toSolutionOn T
          (fun s : ℝ ↦ (extChartAt (𝓡 3) (0 : E3)).symm
            ((lChartRamp x z hb.le).toFun s)) 0 b =
          lChartAction S.val.toSolutionOn T 0 (0 : E3)
            (lChartRamp x z hb.le) := by
      simpa only [sub_zero] using
        ramp_action_eq_of_length S.val.toSolutionOn S.val.isSolutionOn
          T 0 b b x z hb (sub_zero b) hclock
    calc
      lRegularizedAction S.val.toSolutionOn T (alpha z) 0 b =
          lRegularizedAction S.val.toSolutionOn T
            (fun s : ℝ ↦ (extChartAt (𝓡 3) (0 : E3)).symm
              ((lChartRamp x z hb.le).toFun s)) 0 b := by
        apply lRegularizedAction_congr
        intro s hs
        have hs' : s ∈ Ioo (0 : ℝ) b := by
          simpa only [uIoo_of_le hb.le] using hs
        change alpha z s = (extChartAt (𝓡 3) (0 : E3)).symm
          ((lChartRamp x z hb.le).toFun s)
        rw [hchart, lRamp_apply x z hb.le ⟨hs'.1.le, hs'.2.le⟩]
      _ = _ := hramp
  let A : ℝ := (Cg / 2) * (R ^ 2 / b) + Cs * b
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hA (z : E3) (hz : z ∈ Metric.closedBall x R) :
      lRegularizedAction S.val.toSolutionOn T (alpha z) 0 b ≤ A := by
    have hn : ‖z - x‖ ≤ R := by
      simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
    have hn2 : ‖z - x‖ ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hn
    calc
      lRegularizedAction S.val.toSolutionOn T (alpha z) 0 b =
          lChartAction S.val.toSolutionOn T 0 (0 : E3)
            (lChartRamp x z hb.le) := hactRamp z
      _ ≤ (Cg / 2) * (‖z - x‖ ^ 2 / b) + Cs * b :=
        hrampBound (a := 0) (L := b) (y := x) (z := z) hb
          (by intro r hr; simpa only [zero_add] using hr)
          (lRamp_mapsTo (convex_closedBall x R) hb.le hx hz)
      _ ≤ A := by
        change (Cg / 2) * (‖z - x‖ ^ 2 / b) + Cs * b ≤
          (Cg / 2) * (R ^ 2 / b) + Cs * b
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hn2 hb.le)
            (div_nonneg hCg (by norm_num : (0 : ℝ) ≤ 2))) le_rfl
  have hbdd (z : E3) :=
    lRegularizedCosts_bdd_rm S.val.toSolutionOn S.val.isSolutionOn
      (K ^ 2) T 0 b le_rfl hb.le hregSq hRmSq x z
  have hAnyAct (W : TangentSpace (𝓡 3) x)
      (hWmin : (W, tau) ∈ lMinDomain S.val.toSolutionOn T x)
      (hEndBall : lExp S.val.toSolutionOn T x W tau ∈
        Metric.closedBall x R) :
      lRegularizedAction S.val.toSolutionOn T
        (lRegularizedCurve S.val.toSolutionOn T x W) 0 b ≤ A := by
    let z : E3 := lExp S.val.toSolutionOn T x W tau
    calc
      lRegularizedAction S.val.toSolutionOn T
          (lRegularizedCurve S.val.toSolutionOn T x W) 0 b =
          lLength S.val.toSolutionOn T
            (fun r : ℝ ↦ lExp S.val.toSolutionOn T x W r) 0 tau := by
        change lRegularizedAction S.val.toSolutionOn T
            (lRegularizedCurve S.val.toSolutionOn T x W) 0 (Real.sqrt tau) =
          lLength S.val.toSolutionOn T
            (squareRootReparametrization (lRegularizedCurve S.val.toSolutionOn T x W)) 0 tau
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := 𝓡 3) S.val.toSolutionOn T
          (lRegularizedCurve S.val.toSolutionOn T x W) tau htau.le).symm
      _ = lCost S.val.toSolutionOn T x z tau :=
        ((mem_lMinDomain S.val.toSolutionOn T x W tau).mp hWmin).2
      _ = lRegularizedCostC1 S.val.toSolutionOn T 0 b x z :=
        lCost_eq_regularity (I := 𝓡 3) S.val.toSolutionOn T x z tau htau.le
      _ ≤ lRegularizedAction S.val.toSolutionOn T (alpha z) 0 b :=
        lRegularizedCostC1_le_bdd S.val.toSolutionOn T 0 b x z
          (hbdd z) (alpha z) (halpha z) (hstart z) (hend z)
      _ ≤ A := hA z hEndBall
  exact ⟨hreg, A, hA0, hA, hAnyAct⟩

end DifferentialGeometry.PDE.RicciFlow

end
