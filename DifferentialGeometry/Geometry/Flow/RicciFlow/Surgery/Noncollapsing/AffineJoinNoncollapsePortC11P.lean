import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.History.AffineHistoryParabolicBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryNoncollapsePrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialLayerBallVolume

/-!
S-CH11-FIX6 port（astra `Noncollapsing/AffineJoinNoncollapse` 的 elaboration 修补；陈述 / 定义 /
证明思路逐字不变）：`exists_noncollapsed_affine_join` 里 `have hT := T.property.2` 后补一行
`change (T : ℝ) ≤ J.horizon at hT`（`J.toHistory.horizon` 与 `J.horizon` head 不同，`rw [hhor]` 不匹配）。
-/

set_option autoImplicit false
noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace GC.GeneralFlow

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem exists_stage_cast_preimage {P Q : OrientedThreeStage.{u}}
    (h : P = Q) (x : P.Carrier) : ∃ y : Q.Carrier, (h.symm ▸ y) = x := by
  cases h
  exact ⟨x, rfl⟩

/-- Join the old and local tail noncollapse bounds on the actual concatenated
history. The coefficient is chosen before the histories, from the fixed tail
initial metric and the two positive coefficients and radius ceilings. -/
theorem exists_noncollapsed_affine_join
    (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
    {ρglobal ρtail κH κT : ℝ}
    (hρglobal : 0 < ρglobal) (hρtail : 0 < ρtail)
    (hκH : 0 < κH) (hκT : 0 < κT) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (H K J : RetainedCoreHistory.{u})
        (I : InitialIdentification P₀ g₀ K.toHistory)
        (c : ℝ) (offset : ℕ)
        (A : AffineEventPrefix K J c offset (Fin.last K.eventCount)),
        (∀ i : Fin K.eventCount, (K.toHistory.event i).incoming.SingularEndpoint) →
        H.toHistory.IsPrefixOf J.toHistory → c ≤ H.horizon →
        J.horizon = K.horizon + c →
        (∀ t : ℝ,
          HEq (J.toHistory.stageMetric (Fin.last J.eventCount) (t + c))
            (K.toHistory.stageMetric (Fin.last K.eventCount) t)) →
        H.NoncollapsedBefore κH ρglobal H.horizon →
        K.NoncollapsedBefore κT ρtail K.horizon →
        J.NoncollapsedBefore κ ρglobal J.horizon := by
  obtain ⟨κI, η, hκI, hη, hI⟩ :=
    exists_initial_layer_all_ball_volume_lower_bound P₀ g₀ hρglobal
  let a : ℝ := min 1 (min (Real.sqrt η / ρglobal) (ρtail / ρglobal))
  have ha : 0 < a := lt_min one_pos
    (lt_min (div_pos (Real.sqrt_pos.2 hη) hρglobal) (div_pos hρtail hρglobal))
  have ha1 : a ≤ 1 := min_le_left _ _
  have har : ∀ r : ℝ, 0 < r → r ≤ ρglobal →
      a * r ≤ r ∧ a * r ≤ ρtail ∧ (a * r) ^ 2 ≤ η := by
    intro r hr hrmax
    have harglobal : a * r ≤ a * ρglobal := mul_le_mul_of_nonneg_left hrmax ha.le
    have hasqrt : a * ρglobal ≤ Real.sqrt η :=
      (le_div_iff₀ hρglobal).mp ((min_le_right _ _).trans (min_le_left _ _))
    have hat : a * ρglobal ≤ ρtail :=
      (le_div_iff₀ hρglobal).mp ((min_le_right _ _).trans (min_le_right _ _))
    exact ⟨mul_le_of_le_one_left hr.le ha1, harglobal.trans hat,
      (pow_le_pow_left₀ (mul_nonneg ha.le hr.le) (harglobal.trans hasqrt) 2).trans_eq
        (Real.sq_sqrt hη.le)⟩
  let κ : ℝ := min κH (min κI (κT * a ^ 3))
  have hκ : 0 < κ := lt_min hκH (lt_min hκI (mul_pos hκT (pow_pos ha 3)))
  have hκold : κ ≤ κH := min_le_left _ _
  have hκinitial : κ ≤ κI := (min_le_right _ _).trans (min_le_left _ _)
  have hκtail : κ ≤ κT * a ^ 3 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨κ, hκ, ?_⟩
  intro H K J I c offset A hsing hp hc hhor hfinal hncH hncT
  have hncOld : J.NoncollapsedBefore κH ρglobal H.horizon :=
    RetainedCoreHistory.noncollapsedBefore_of_isPrefixOf hp le_rfl hncH
  intro T
  by_cases hTold : (T : ℝ) ≤ H.horizon
  · intro x r _ hr hball
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hκold) (le_refl _)).trans
      (hncOld T x r hTold hr hball)
  · obtain ⟨t, htpos, rfl⟩ :
        ∃ t : Icc (0 : ℝ) K.horizon, 0 < (t : ℝ) ∧ A.shiftTime hhor t = T := by
      have ht : 0 < (T : ℝ) - c := by
        have hT := lt_of_not_ge hTold
        linarith
      have htle : (T : ℝ) - c ≤ K.horizon := by
        have hT := T.property.2
        change (T : ℝ) ≤ J.horizon at hT
        rw [hhor] at hT
        linarith
      refine ⟨⟨(T : ℝ) - c, ht.le, htle⟩, ht, ?_⟩
      apply Subtype.ext
      change (T : ℝ) - c + c = (T : ℝ)
      ring
    intro x r _ hrglobal hball
    obtain ⟨p, rfl⟩ := exists_stage_cast_preimage (A.stageAt_shift_eq hhor t) x
    have hr : 0 < r := hball.1
    have hvolume := A.ball_volume_shift_eq hhor hfinal t p r
    by_cases htη : (t : ℝ) ≤ η
    · have hv := hI K I hsing t htpos htη p r hr hrglobal
      rw [hvolume]
      exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hκinitial) (le_refl _)).trans hv
    · have hrange := har r hr hrglobal
      have hsmall := hball.mono_radius J.toHistory (mul_pos ha hr) hrange.1
      have htime : (a * r) ^ 2 ≤ (t : ℝ) := hrange.2.2.trans (lt_of_not_ge htη).le
      have hsmallK :=
        (A.isParabolicallyRmControlledBall_shift_iff hhor hfinal t p (a * r) htime).mp hsmall
      have hv := hncT t p (a * r) t.property.2 hrange.2.1 hsmallK
      rw [hvolume]
      calc ENNReal.ofReal κ * ENNReal.ofReal r ^ 3
          ≤ ENNReal.ofReal (κT * a ^ 3) * ENNReal.ofReal r ^ 3 :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hκtail) (le_refl _)
        _ = ENNReal.ofReal κT * ENNReal.ofReal (a * r) ^ 3 := by
            rw [ENNReal.ofReal_mul hκT.le, ENNReal.ofReal_mul ha.le,
              ENNReal.ofReal_pow ha.le, mul_pow, mul_assoc]
        _ ≤ _ := hv
        _ ≤ _ := MeasureTheory.measure_mono (riemannianBallOf_mono _ _ hrange.1)

end GC.GeneralFlow
