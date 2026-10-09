import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompactSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedRepresentation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Topology.Manifold.CurveIntervalExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartLipschitz
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactChartAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MinVectorCompactComplete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

set_option autoImplicit false

noncomputable section

open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology Interval NNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private theorem lCost_ramp_le_of_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x p : M) {b c : Real} (hc : 0 < c) (hcb : c < b)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (W : TangentSpace I x) (hbdom : b ∈ lRegularizedDomain S T x W)
    (hrayc : lRegularizedCurve S T x W c ∈ (chartAt H p).source)
    (z : E)
    (hbdd : BddBelow {r : Real | ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = (extChartAt I p).symm z ∧
        lRegularizedAction S T gamma 0 b = r})
    (htar : MapsTo
      (lChartRamp ((extChartAt I p) (lRegularizedCurve S T x W c)) z
        (sub_nonneg.mpr hcb.le)).toFun (Icc (0 : Real) (b - c))
      (extChartAt I p).target) :
    lCost S T x ((extChartAt I p).symm z) (b ^ 2) ≤
      lRegularizedAction S T (lRegularizedCurve S T x W) 0 c +
        lChartAction S T c p
          (lChartRamp ((extChartAt I p) (lRegularizedCurve S T x W c)) z
            (sub_nonneg.mpr hcb.le)) := by
  let y : E := (extChartAt I p) (lRegularizedCurve S T x W c)
  let u : timeH1 E (b - c) := lChartRamp y z (sub_nonneg.mpr hcb.le)
  let beta : Real → M := fun s ↦
    (extChartAt I p).symm (u.toFun (s - c))
  have hcdom : c ∈ lRegularizedDomain S T x W :=
    lRegularizedDomain_segment S T x W hbdom hc.le hcb.le
  have halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (lRegularizedCurve S T x W) (Icc (0 : Real) c) :=
    lRegularizedCurve_c1On S hS T x W hcdom
  let v : Real → E := fun s ↦ y + ((s - c) / (b - c)) • (z - y)
  have hv : ContDiffOn Real 1 v (Icc c b) := by
    exact (contDiff_const.add
      (((contDiff_id.sub contDiff_const).div_const (b - c)).smul
        contDiff_const)).contDiffOn
  have hvmap : MapsTo v (Icc c b) (extChartAt I p).target := by
    intro s hs
    have hr : s - c ∈ Icc (0 : Real) (b - c) := by
      constructor <;> linarith [hs.1, hs.2]
    have hu := htar hr
    rw [show v s = y + ((s - c) / (b - c)) • (z - y) by rfl,
      ← lRamp_apply (y := y) (z := z) (sub_nonneg.mpr hcb.le) hr]
    exact hu
  have hbeta0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (fun s ↦ (extChartAt I p).symm (v s)) (Icc c b) := by
    apply (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp
    · exact contMDiffOn_iff_contDiffOn.mpr hv
    · exact hvmap
  have hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b) := by
    apply hbeta0.congr
    intro s hs
    have hr : s - c ∈ Icc (0 : Real) (b - c) := by
      constructor <;> linarith [hs.1, hs.2]
    exact congrArg (extChartAt I p).symm
      (lRamp_apply (y := y) (z := z) (sub_nonneg.mpr hcb.le) hr)
  have hnode : lRegularizedCurve S T x W c = beta c := by
    change lRegularizedCurve S T x W c =
      (extChartAt I p).symm (u.toFun (c - c))
    rw [sub_self, show u.toFun 0 = y by
      exact lRamp_start (y := y) (z := z) (sub_nonneg.mpr hcb.le)]
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hrayc)).symm
  have hend : beta b = (extChartAt I p).symm z := by
    simp only [beta, u, lRamp_end (sub_pos.mpr hcb)]
  have hle := lCost_le_join_bdd (I := I) S hS T b (lt_trans hc hcb) x
    ((extChartAt I p).symm z) hc hcb hbdd hreg
    (lRegularizedCurve S T x W) beta halpha hbeta hnode
    (lRegularizedCurve_zero S T x W) hend
  have hact := lRampAct_eq (I := I) S hS T c b p hcb htar
    (fun s hs ↦ hreg s ⟨hc.le.trans hs.1, hs.2⟩)
  rw [hact] at hle
  simpa only [y, u] using hle

omit [NeZero (Module.finrank ℝ E)] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem lCost_chart_locallyLipschitzOn_of_compact_minimizers
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) (U : Set M) (hU : IsOpen U)
    (hCosts : ∀ y : M, BddBelow {r : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧
      γ 0 = x ∧ γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = r})
    (hmins : ∀ y ∈ U, ∃ W : TangentSpace I x, (W, tau) ∈ lMinDomain S T x ∧ lExp S T x W tau = y)
    (hcompact : ∀ Y : Set M, IsCompact Y → Y ⊆ U →
      IsCompact {Z : TangentSpace I x | (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau ∈ Y})
    (p : M) :
    LocallyLipschitzOn ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U)
      ((fun y : M => lCost S T x y tau) ∘ (extChartAt I p).symm) := by
  classical
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hreg : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs2 : s ^ 2 ≤ tau := by
      have hh := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
      simpa only [hb2] using hh
    exact hslab ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩
  intro q0 hq0
  obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp
    ((continuousOn_extChartAt_symm (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_target (I := I) p) hU) q0 hq0
  have hRtar : Metric.ball q0 R ⊆ (extChartAt I p).target := fun z hz => (hRsub hz).1
  have hRU : ∀ z ∈ Metric.ball q0 R, (extChartAt I p).symm z ∈ U := fun z hz => (hRsub hz).2
  let ρ : Real := R / 8
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  let Q : Set E := Metric.closedBall q0 ρ
  have hQtar : Q ⊆ (extChartAt I p).target := by
    intro q hq
    apply hRtar
    have hρR : ρ < R := by dsimp only [ρ]; linarith
    exact lt_of_le_of_lt hq hρR
  have hQcpt : IsCompact Q := isCompact_closedBall q0 ρ
  let Y : Set M := (extChartAt I p).symm '' Q
  have hYcpt : IsCompact Y :=
    hQcpt.image_of_continuousOn
      ((continuousOn_extChartAt_symm (I := I) p).mono hQtar)
  have hYU : Y ⊆ U := by
    rintro y ⟨q, hq, rfl⟩
    exact hRU q (by
      have hqr : dist q q0 ≤ ρ := hq
      have hρR : ρ < R := by dsimp [ρ]; linarith
      exact hqr.trans_lt hρR)
  let F : Set E := {W : E | (W, tau) ∈ lMinDomain S T x ∧ lExp S T x W tau ∈ Y}
  have hFcpt : IsCompact F := hcompact Y hYcpt hYU
  have hbdomF (W : E) (hW : W ∈ F) :
      b ∈ lRegularizedDomain S T x W := by
    have hpos : (W, tau) ∈ lExpPosDom S T x :=
      ((mem_lMinDomain S T x W tau).1 hW.1).1
    exact ((mem_lExpPosDom S T x W tau).1 hpos).2.2
  have hbchart : ∀ W ∈ F,
      lRegularizedCurve S T x W b ∈ (chartAt H p).source := by
    intro W hW
    obtain ⟨q, hqQ, hqend⟩ := hW.2
    change lExp S T x W tau ∈ (chartAt H p).source
    rw [← hqend]
    simpa only [extChartAt_source] using
      (extChartAt I p).map_target (hQtar hqQ)
  obtain ⟨δ, hδ, hδb, htube⟩ := lRayChart_tube (I := I)
    S hS T x p hb hFcpt hbdomF hbchart
  have hdomTail : F ×ˢ Icc (b - δ) b ⊆ lRegularizedJointDom S T x := by
    intro q hq
    change q.2 ∈ lRegularizedDomain S T x q.1
    exact (htube q.1 hq.1 q.2 hq.2).1
  have hsrcTail : MapsTo
      (fun q : E × Real ↦ lRegularizedCurve S T x q.1 q.2)
      (F ×ˢ Icc (b - δ) b) (extChartAt I p).source := by
    intro q hq
    simpa only [extChartAt_source] using (htube q.1 hq.1 q.2 hq.2).2
  obtain ⟨V, hV, hchart⟩ := lRayChart_bound (I := I) S hS T x p
    hFcpt hdomTail hsrcTail
  obtain ⟨Cr, hCr, htail⟩ := lRayTail_bound (I := I) S hS T x
    hFcpt hdomTail
  let Qbig : Set E := Metric.closedBall q0 (R / 2)
  have hQbigCpt : IsCompact Qbig := isCompact_closedBall q0 (R / 2)
  have hQbigTar : Qbig ⊆ interior (extChartAt I p).target := by
    rw [interior_eq_iff_isOpen.mpr (isOpen_extChartAt_target (I := I) p)]
    intro q hq
    apply hRtar
    exact lt_of_le_of_lt hq (half_lt_self hR)
  obtain ⟨Cg, Cs, hCg, hCs, hramp⟩ := lRampAct_slab_of_compact_chart (I := I)
    S hS T p (A := b - δ) (B := b) (fun s hs ↦ hreg s ⟨by
      linarith [hs.1, hδb], hs.2⟩) hQbigCpt hQbigTar
  let ε : Real := min (ρ / 2)
    (min (δ / 4) (min (b / 4) (R / (16 * (V + 1)))))
  have hV1 : 0 < V + 1 := by linarith
  have hε : 0 < ε := by
    exact lt_min (half_pos hρ) (lt_min (by positivity)
      (lt_min (by positivity) (div_pos hR (by positivity))))
  let Aconst : Real := Cr + Cg / 2 * (V + 1) ^ 2 + Cs
  have hAconst : 0 ≤ Aconst := by positivity
  let Lip : NNReal := ⟨Aconst, hAconst⟩
  refine ⟨Lip, Metric.ball q0 ε,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds q0 hε), ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro q hq r hr
  have hqρ : q ∈ Metric.ball q0 ρ :=
    hq.trans_le ((min_le_left (ρ / 2) _).trans (half_le_self hρ.le))
  have hrρ : r ∈ Metric.ball q0 ρ :=
    hr.trans_le ((min_le_left (ρ / 2) _).trans (half_le_self hρ.le))
  have hqtar := hQtar (Metric.ball_subset_closedBall hqρ)
  have hrtar := hQtar (Metric.ball_subset_closedBall hrρ)
  have hρR : ρ < R := by dsimp [ρ]; linarith
  obtain ⟨Wq, hWqminTau, hWqendTau⟩ := hmins ((extChartAt I p).symm q) (hRU q (hqρ.trans hρR))
  obtain ⟨Wr, hWrminTau, hWrendTau⟩ := hmins ((extChartAt I p).symm r) (hRU r (hrρ.trans hρR))
  have hWqmin : (Wq, b ^ 2) ∈ lMinDomain S T x := by
    simpa only [hb2] using hWqminTau
  have hWrmin : (Wr, b ^ 2) ∈ lMinDomain S T x := by
    simpa only [hb2] using hWrminTau
  have hWqend : lExp S T x Wq (b ^ 2) = (extChartAt I p).symm q := by
    simpa only [hb2] using hWqendTau
  have hWrend : lExp S T x Wr (b ^ 2) = (extChartAt I p).symm r := by
    simpa only [hb2] using hWrendTau
  have hWqF : (Wq : E) ∈ F :=
    ⟨hWqminTau, ⟨q, Metric.ball_subset_closedBall hqρ, hWqendTau.symm⟩⟩
  have hWrF : (Wr : E) ∈ F :=
    ⟨hWrminTau, ⟨r, Metric.ball_subset_closedBall hrρ, hWrendTau.symm⟩⟩
  have oneSide : ∀ (u v : E) (Wu : TangentSpace I x),
      u ∈ Metric.ball q0 ε → v ∈ Metric.ball q0 ε →
      u ∈ (extChartAt I p).target → v ∈ (extChartAt I p).target →
      (Wu, b ^ 2) ∈ lMinDomain S T x →
      lExp S T x Wu (b ^ 2) = (extChartAt I p).symm u →
      (Wu : E) ∈ F →
      lCost S T x ((extChartAt I p).symm v) (b ^ 2) -
        lCost S T x ((extChartAt I p).symm u) (b ^ 2) ≤
          Aconst * ‖v - u‖ := by
    intro u v Wu hu hv hutar _hvtar hWmin hWend hWF
    by_cases huv : u = v
    · subst v
      simp only [sub_self, norm_zero, mul_zero, le_refl]
    let d : Real := ‖v - u‖
    have hd : 0 < d := (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv)))
    have hdist : d < 2 * ε := by
      calc
        d = dist v u := by rw [dist_eq_norm]
        _ ≤ dist v q0 + dist u q0 := by
          simpa only [dist_comm q0 u] using dist_triangle v q0 u
        _ < ε + ε := add_lt_add hv hu
        _ = 2 * ε := by ring
    have hdδ : d < δ := by
      have hεδ : ε ≤ δ / 4 :=
        (min_le_right (ρ / 2) _).trans (min_le_left _ _)
      linarith
    have hdb : d < b := by
      have hεb : ε ≤ b / 4 :=
        (min_le_right (ρ / 2) _).trans
          ((min_le_right (δ / 4) _).trans (min_le_left _ _))
      linarith
    let c : Real := b - d
    have hc : 0 < c := sub_pos.mpr hdb
    have hcb : c < b := sub_lt_self b hd
    have hcI : c ∈ Icc (b - δ) b := ⟨by dsimp only [c]; linarith, hcb.le⟩
    have hWuEnd : lRegularizedCurve S T x Wu b = (extChartAt I p).symm u := by
      simpa only [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb] using hWend
    have hchartEnd : (extChartAt I p) (lRegularizedCurve S T x Wu b) = u := by
      rw [hWuEnd]
      exact (extChartAt I p).right_inv hutar
    let y : E := (extChartAt I p) (lRegularizedCurve S T x Wu c)
    have hyu : ‖y - u‖ ≤ V * d := by
      have hh := hchart (Wu : E) hWF c hcI
      rw [hchartEnd] at hh
      simpa only [y, c, sub_sub_cancel, norm_sub_rev] using hh
    have hyv : ‖v - y‖ ≤ (V + 1) * d := by
      calc
        ‖v - y‖ = ‖(v - u) + (u - y)‖ := by congr 1; abel
        _ ≤ ‖v - u‖ + ‖u - y‖ := norm_add_le _ _
        _ = d + ‖y - u‖ := by
          rw [show ‖v - u‖ = d by rfl, norm_sub_rev u y]
        _ ≤ d + V * d := add_le_add (le_refl d) hyu
        _ = (V + 1) * d := by ring
    have hεR : ε ≤ R / (16 * (V + 1)) :=
      (min_le_right (ρ / 2) _).trans
        ((min_le_right (δ / 4) _).trans (min_le_right _ _))
    have hepsR : ε ≤ R / 16 := by
      calc
        ε ≤ R / (16 * (V + 1)) := hεR
        _ ≤ R / 16 := by
          apply (div_le_div_iff_of_pos_left hR (by positivity)
            (by positivity)).2
          nlinarith [hV]
    have hdR : V * d + ε ≤ R / 2 := by
      have hd' : d ≤ R / (8 * (V + 1)) := by
        calc d ≤ 2 * ε := hdist.le
          _ ≤ 2 * (R / (16 * (V + 1))) := by gcongr
          _ = R / (8 * (V + 1)) := by field_simp; ring
      have hVR : V * d ≤ R / 8 := by
        calc
          V * d ≤ (V + 1) * (R / (8 * (V + 1))) := by
            exact mul_le_mul (by linarith) hd' hd.le hV1.le
          _ = R / 8 := by field_simp [hV1.ne']
      calc
        V * d + ε ≤ R / 8 + R / 16 := add_le_add hVR hepsR
        _ ≤ R / 2 := by linarith [hR]
    have hyQ : y ∈ Qbig := by
      change dist y q0 ≤ R / 2
      calc
        dist y q0 ≤ dist y u + dist u q0 := dist_triangle _ _ _
        _ = ‖y - u‖ + dist u q0 := by rw [dist_eq_norm]
        _ ≤ V * d + ε := add_le_add hyu hu.le
        _ ≤ R / 2 := hdR
    have hvQ : v ∈ Qbig := by
      change dist v q0 ≤ R / 2
      exact hv.le.trans (hεR.trans (by
        apply (div_le_div_iff_of_pos_left hR (by positivity)
          (by positivity)).2
        nlinarith [hV]))
    have hmap := lRamp_mapsTo (convex_closedBall q0 (R / 2))
      (sub_nonneg.mpr hcb.le) hyQ hvQ
    have htimeRamp : ∀ r ∈ Icc (0 : Real) (b - c),
        c + r ∈ Icc (b - δ) b := by
      intro r hr
      exact ⟨by linarith [hcI.1, hr.1], by linarith [hr.2]⟩
    have hrampLe := hramp (sub_pos.mpr hcb) htimeRamp hmap
    have hrampLin : lChartAction S T c p
        (lChartRamp y v (sub_nonneg.mpr hcb.le)) ≤
          (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
      calc
        lChartAction S T c p (lChartRamp y v (sub_nonneg.mpr hcb.le)) ≤
            Cg / 2 * (‖v - y‖ ^ 2 / (b - c)) + Cs * (b - c) :=
          by simpa only [y] using hrampLe
        _ ≤ (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
          have hbcEq : b - c = d := by simp only [c, sub_sub_cancel]
          rw [hbcEq]
          have hd0 := hd.le
          have hsq : ‖v - y‖ ^ 2 ≤ ((V + 1) * d) ^ 2 :=
            sq_le_sq₀ (norm_nonneg _) (mul_nonneg hV1.le hd0) |>.2 hyv
          calc
            Cg / 2 * (‖v - y‖ ^ 2 / d) + Cs * d ≤
                Cg / 2 * (((V + 1) * d) ^ 2 / d) + Cs * d := by
                  gcongr
            _ = (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
                  field_simp
    have hrayc := (htube (Wu : E) hWF c hcI).2
    have hcostLe := lCost_ramp_le_of_bdd (I := I) S hS T x p hc hcb
      hreg Wu (hbdomF (Wu : E) hWF) hrayc v
      (hCosts ((extChartAt I p).symm v)) (by
        intro z hz
        exact interior_subset (hQbigTar (by
          simpa only [y, c, sub_sub_cancel] using hmap hz)))
    have hheadInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T 0 c hc.le (lRegularizedCurve S T x Wu)
      (lRegularizedCurve_c1On S hS T x Wu
        (lRegularizedDomain_segment S T x Wu (hbdomF (Wu : E) hWF) hc.le hcb.le))
      (fun s hs ↦ hreg s ⟨hs.1, hs.2.trans hcb.le⟩)
    have htailInt := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
      ⟨hS.scalarCont⟩ T c b hcb.le (lRegularizedCurve S T x Wu)
      ((lRegularizedCurve_c1On S hS T x Wu (hbdomF (Wu : E) hWF)).mono
        (fun s hs ↦ ⟨hc.le.trans hs.1, hs.2⟩))
      (fun s hs ↦ hreg s ⟨hc.le.trans hs.1, hs.2⟩)
    have hadd := lRegularizedAction_add (I := I) S T (lRegularizedCurve S T x Wu)
      0 c b hheadInt htailInt
    have hminEq := ((mem_lMinDomain S T x Wu (b ^ 2)).1 hWmin).2
    have hfull : lRegularizedAction S T (lRegularizedCurve S T x Wu) 0 b =
        lCost S T x ((extChartAt I p).symm u) (b ^ 2) := by
      calc
        lRegularizedAction S T (lRegularizedCurve S T x Wu) 0 b =
            lLength S T (squareRootReparametrization (lRegularizedCurve S T x Wu)) 0 (b ^ 2) := by
              simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using
                (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T (lRegularizedCurve S T x Wu)
                  (b ^ 2) (sq_nonneg b)).symm
        _ = lCost S T x (lExp S T x Wu (b ^ 2)) (b ^ 2) := by
              change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Wu)) 0
                (b ^ 2) = lCost S T x
                  (lRegularizedCurve S T x Wu (Real.sqrt (b ^ 2))) (b ^ 2)
              exact hminEq
        _ = lCost S T x ((extChartAt I p).symm u) (b ^ 2) := by rw [hWend]
    have htailLe := htail (Wu : E) hWF c hcI
    rw [← hfull, ← hadd]
    have hcalc := hcostLe
    dsimp only [y] at hrampLin hcalc
    have hnegTail : -lRegularizedAction S T (lRegularizedCurve S T x Wu) c b ≤ Cr * d := by
      calc
        -lRegularizedAction S T (lRegularizedCurve S T x Wu) c b ≤
            |lRegularizedAction S T (lRegularizedCurve S T x Wu) c b| := by
              simpa only [abs_neg] using
                le_abs_self (-lRegularizedAction S T (lRegularizedCurve S T x Wu) c b)
        _ ≤ Cr * (b - c) := htailLe
        _ = Cr * d := by simp only [c, sub_sub_cancel]
    dsimp only [Aconst]
    linarith [hcalc, hrampLin, hnegTail]
  have hqr := oneSide q r Wq hq hr hqtar hrtar hWqmin hWqend hWqF
  have hrq := oneSide r q Wr hr hq hrtar hqtar hWrmin hWrend hWrF
  change dist (lCost S T x ((extChartAt I p).symm q) tau)
    (lCost S T x ((extChartAt I p).symm r) tau) ≤
      (Lip : Real) * dist q r
  rw [Real.dist_eq, dist_eq_norm]
  rw [hb2] at hqr hrq
  change |lCost S T x ((extChartAt I p).symm q) tau -
    lCost S T x ((extChartAt I p).symm r) tau| ≤ Aconst * ‖q - r‖
  rw [abs_le]
  constructor
  · have := hqr
    rw [norm_sub_rev] at this
    linarith
  · simpa only [norm_sub_rev] using hrq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem lCost_chart_locallyLipschitzOn_of_compact_action_sublevel
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau A : ℝ} (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (K : Set M) (hK : IsCompact K) (U : Set M) (hU : IsOpen U)
    (hbdd : ∀ y : M, BddBelow {r : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧
      γ 0 = x ∧ γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = r})
    (hseed : ∀ y ∈ U, ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) ≤ A)
    (hconf : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ → γ 0 = x → γ (Real.sqrt tau) ∈ U →
      lRegularizedAction S T γ 0 (Real.sqrt tau) ≤ A → MapsTo γ (Icc 0 (Real.sqrt tau)) K)
    (p : M) :
    LocallyLipschitzOn ((extChartAt I p).target ∩ (extChartAt I p).symm ⁻¹' U)
      ((fun y : M => lCost S T x y tau) ∘ (extChartAt I p).symm) := by
  let b := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hreg : ∀ s ∈ Icc (0 : ℝ) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    have hs2 : s ^ 2 ≤ tau := by
      have hh := (sq_le_sq₀ hs.1 hb.le).mpr hs.2
      simpa only [hb2] using hh
    exact hslab ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩
  have hmins (y : M) (hy : y ∈ U) : ∃ W : TangentSpace I x,
      (W, tau) ∈ lMinDomain S T x ∧ lExp S T x W tau = y := by
    obtain ⟨γ, hγ, hγ0, hγb, hγact⟩ := hseed y hy
    obtain ⟨η, hη, hη0, hηb, _, hmin⟩ := exists_lRegularizedMinC1_of_compact_action_sublevel
      S hS T hb hreg x y γ hγ hγ0 hγb K hK
      (fun δ hδ hδ0 hδb hδact => hconf δ hδ hδ0 (hδb.symm ▸ hy) (hδact.trans hγact))
    have hm : ∀ δ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 δ → δ 0 = η 0 → δ b = η b →
        lRegularizedAction S T η 0 b ≤ lRegularizedAction S T δ 0 b :=
      fun δ hδ hδ0 hδb => hmin δ hδ (hδ0.trans hη0) (hδb.trans hηb)
    cases hη0
    obtain ⟨W, hW, hWend, _, _⟩ := exists_lMinimizingVector_of_minimal S hS T hb hreg η hη hm
    rw [hb2] at hW hWend
    exact ⟨W, hW, hWend.trans hηb⟩
  have hacts (Z : TangentSpace I x) (hZ : (Z, tau) ∈ lMinDomain S T x)
      (hy : lExp S T x Z tau ∈ U) :
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b ≤ A := by
    obtain ⟨γ, hγ, hγ0, hγb, hγact⟩ := hseed _ hy
    have hcost := ((mem_lMinDomain S T x Z tau).mp hZ).2
    change lLength S T (squareRootReparametrization (lRegularizedCurve S T x Z)) 0 tau = _ at hcost
    rw [lLength_squareRootReparametrization_eq_lRegularizedAction S T _ tau htau.le] at hcost
    rw [hcost, lCost_eq_regularity S T x _ tau htau.le]
    exact (lRegularizedCostC1_le_bdd S T 0 b x _ (hbdd _) γ hγ hγ0 hγb).trans hγact
  have hranges (Z : TangentSpace I x) (hZ : (Z, tau) ∈ lMinDomain S T x)
      (hy : lExp S T x Z tau ∈ U) : MapsTo (lRegularizedCurve S T x Z) (Icc 0 b) K := by
    have hdom := ((mem_lExpPosDom S T x Z tau).mp (((mem_lMinDomain S T x Z tau).mp hZ).1)).2.2
    obtain ⟨α, hα, heq⟩ := DifferentialGeometry.Topology.exists_contMDiff_extension_Icc
      (lRegularizedCurve_c1On S hS T x Z hdom)
    have hα0 : α 0 = x := (heq ⟨le_rfl, hb.le⟩).trans (lRegularizedCurve_zero S T x Z)
    have hαb : α b = lExp S T x Z tau := heq ⟨hb.le, le_rfl⟩
    have hact : lRegularizedAction S T α 0 b = lRegularizedAction S T (lRegularizedCurve S T x Z) 0 b := by
      apply lRegularizedAction_congr
      rw [uIoo_of_le hb.le]
      exact heq.mono Ioo_subset_Icc_self
    have hc := hconf α hα hα0 (hαb.symm ▸ hy) (hact.le.trans (hacts Z hZ hy))
    intro z hz
    rw [← heq hz]
    exact hc hz
  apply lCost_chart_locallyLipschitzOn_of_compact_minimizers S hS T x htau hslab U hU hbdd hmins ?_ p
  intro Y hY hYU
  exact isCompact_lMinVec_over_of_compact_range S hS T x htau hslab K hK hY.isClosed A hbdd
    (fun Z hZ hy => hacts Z hZ (hYU hy)) (fun Z hZ hy => hranges Z hZ (hYU hy))

theorem lCost_chart_lip_of_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - tau) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4 (S.base.rm04 t y) ≤ K)
    (p : M) :
    LocallyLipschitzOn (extChartAt I p).target
      ((fun y : M ↦ lCost S T x y tau) ∘ (extChartAt I p).symm) := by
  have hb : 0 < Real.sqrt tau := Real.sqrt_pos.mpr htau
  have hclock : ∀ r ∈ Icc (0 : ℝ) (Real.sqrt tau), T - r ^ 2 ∈ D.regular := by
    intro r hr
    have hsq : r ^ 2 ≤ tau := by
      have hh := (sq_le_sq₀ hr.1 hb.le).mpr hr.2
      rwa [Real.sq_sqrt htau.le] at hh
    exact hslab ⟨by linarith, sub_le_self _ (sq_nonneg r)⟩
  have hbdd (y : M) : BddBelow {r : ℝ | ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧
      γ 0 = x ∧ γ (Real.sqrt tau) = y ∧ lRegularizedAction S T γ 0 (Real.sqrt tau) = r} :=
    lRegularizedCosts_bdd_rm S hS K T 0 (Real.sqrt tau) le_rfl hb.le
      (by simpa only [Real.sq_sqrt htau.le] using hslab)
      (by simpa only [Real.sq_sqrt htau.le] using hRm) x y
  intro q hq
  by_cases hreach : ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 γ ∧ γ 0 = x ∧
      γ (Real.sqrt tau) = (extChartAt I p).symm q
  · obtain ⟨γ, hγ, hγ0, hγend⟩ := hreach
    obtain ⟨U, hU, hγU, α, hα, hα0, hαb, _, _⟩ :=
      exists_open_endpoint_family_of_lRegularizedAction_lt S hS T hb
        (fun r hr => D.regular_subset (hclock r hr)) γ hγ (lt_add_one _)
    have hmins (y : M) (hy : y ∈ U) : ∃ W : TangentSpace I x,
        (W, tau) ∈ lMinDomain S T x ∧ lExp S T x W tau = y :=
      exists_lMinimizingVector_rm S hS K T hg tau htau hslab hRm x y (α y) (hα y hy)
        ((hα0 y hy).trans hγ0) (hαb y hy)
    have hcompact (Y : Set M) (hY : IsCompact Y) (_ : Y ⊆ U) :
        IsCompact {W : TangentSpace I x | (W, tau) ∈ lMinDomain S T x ∧ lExp S T x W tau ∈ Y} := by
      obtain ⟨_, _, _, _, hc⟩ := lMinVec_compact_over_of_rm S hS K T hg x tau htau hslab hRm hY
      exact hc
    have hqU : (extChartAt I p).symm q ∈ U := hγend ▸ hγU
    obtain ⟨C, V, hV, hLip⟩ :=
      lCost_chart_locallyLipschitzOn_of_compact_minimizers S hS T x htau hslab U hU hbdd hmins hcompact p ⟨hq, hqU⟩
    have hn : (extChartAt I p).symm ⁻¹' U ∈ 𝓝[(extChartAt I p).target] q :=
      (continuousOn_extChartAt_symm (I := I) p q hq).preimage_mem_nhdsWithin (hU.mem_nhds hqU)
    rw [nhdsWithin_inter_of_mem' hn] at hV
    exact ⟨C, V, hV, hLip⟩
  · obtain ⟨ε, hε, hlip⟩ := lCost_zero_lip S hS T x (Real.sqrt tau) hb hclock p hq hreach
    refine ⟨0, Metric.ball q ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds q hε), ?_⟩
    simpa only [Real.sq_sqrt htau.le, Function.comp_def] using hlip

end DifferentialGeometry.PDE.RicciFlow

end
