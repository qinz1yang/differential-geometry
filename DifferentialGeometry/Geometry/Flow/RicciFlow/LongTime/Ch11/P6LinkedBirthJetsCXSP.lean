import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.LinkedWindowsWireC11SL
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.A12OfNarrowTupleC11A
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InitialWindowBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCurvatureJets

set_option autoImplicit false

/-!
# Actual linked birth-window jets / 同一插帽的任意固定阶出生 jets

S10 的 linked datum 保留实际 insertion formula 和增长的 neck order。
固定 collar length、model radius D 和阶数 j 后，将证书提升为 j+2 阶、误差 1/2。
新 witness 的 window metric 与 domain 完全相同，不改变 surgery metric 或任何 κ-window。

Sources: ModelWindow.exists_normalizedDatum_modelWindow_error_lt;
StaticWitness.StaticInsertionProperties.outMetric_eq/windowMap_eq;
InitialWindowBounds.exists_uniform_window_curvature_derivative_bounds;
StaticCapCurvatureJets.curvDerivNormSq_output_window.

chain consumer 从同一 narrow tuple 保留 linked；每固定 j 先选 T_j，
再量化全部 observation/event/cap/point。此处仅证明 birth jets，
还需后续接入正年龄 smoothing 与 whole-ball compactness。
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open GC.GeneralFlow
open scoped Manifold ContDiff Topology ENNReal

namespace GC.LongTime.Ch11

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩

/-- 保持固定 domain，以 linked precision 实付实际 output window 的任意固定阶数。 -/
theorem exists_linked_window_birth_jets_CXSP
    (fixed : StaticCapScaffold) (D : ℝ) (hD : 0 < D) (j : ℕ) :
    ∃ C δstar : ℝ, 0 < C ∧ 0 < δstar ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
        {m : ℕ} {ε : ℝ} {b : E.RetainedBoundaryIndex}
        (S : E.PresentedStaticCap fixed D m ε b),
        S.hasLinkedCanonicalWindow_C12X → S.delta ≤ δstar →
        ∀ x : standardCapWindow D, ‖x.val‖ < D →
          curvDerivNormSq j E.outputMetric (S.window x) ≤
            C ^ 2 * S.neck.scale ^ (j + 2) := by
  obtain ⟨C, hC, hbound⟩ := StandardCap.exists_uniform_window_curvature_derivative_bounds j
  obtain ⟨δw, hδw, _hhalf, hwindow⟩ :=
    StandardCap.exists_normalizedDatum_modelWindow_error_lt
      fixed.collarLength fixed.collar_pos D hD (j + 2) (1 / 2) (by norm_num)
  let δstar : ℝ := min δw ((j : ℝ) + 3)⁻¹
  have hδstar : 0 < δstar := lt_min hδw (inv_pos.mpr (by positivity))
  refine ⟨C, δstar, hC, hδstar, ?_⟩
  intro P Q a s E m ε b S hlinked hsmall x hx
  obtain ⟨x₀, δ, k, d, w, _hscale, hactual, _hcap, hδS, horder⟩ := hlinked
  have hδw' : δ ≤ δw := (hδS.trans hsmall).trans (min_le_left _ _)
  have hδj : δ ≤ ((j : ℝ) + 3)⁻¹ :=
    (hδS.trans hsmall).trans (min_le_right _ _)
  have hinv : (j : ℝ) + 3 ≤ δ⁻¹ := by
    have h := (inv_le_inv₀ (inv_pos.mpr (by positivity : 0 < (j : ℝ) + 3))
      d.precision_pos).mpr hδj
    rwa [inv_inv] at h
  have hjfloor : j + 2 ≤ ⌊δ⁻¹⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hjk : j + 2 ≤ k := by omega
  obtain ⟨hAB, hfit, hclose⟩ := hwindow δ d.precision_pos hδw'
  have htip : StandardCap.collapseTip fixed.collarLength ∈
      Ioo (-δ⁻¹) (-2 * fixed.collarLength - StandardCap.transitionEnd) :=
    w.properties.profileTip_eq ▸ w.properties.profileTip_location
  let w' := StandardCap.canonicalStaticInsertionWitness d
    fixed.collarLength fixed.collar_pos D hD (j + 2) (1 / 2) hAB hfit htip
      (hclose k hjk E.terminal.metric x₀ d.oriented)
  have hout : w'.data.outMetric = w.data.outMetric :=
    w'.properties.outMetric_eq.trans w.properties.outMetric_eq.symm
  have hmap : w'.window = w.window := by
    ext z
    change w'.data.windowMap z = w.data.windowMap z
    rw [w'.properties.windowMap_eq, w.properties.windowMap_eq]
  have hmetric : w'.windowMetric = w.windowMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v v'
    rw [w'.window_inner, w.window_inner, hout, hmap]
  have hactualMetric : w.windowMetric = S.witness.windowMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v v'
    exact (hactual z v v').trans (S.window_inner z v v').symm
  have hsqrt : Real.sqrt (curvDerivNormSq j w'.windowMetric x) ≤ C := by
    simpa only [curvDerivNormSq, curvCovDeriv_normSq_eq] using
      hbound w' (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2) (le_refl (j + 2)) x hx
  have hnonneg : 0 ≤ curvDerivNormSq j w'.windowMetric x := by
    unfold curvDerivNormSq
    exact normSq0S_nonneg _ _ _ _
  have hsquare : curvDerivNormSq j w'.windowMetric x ≤ C ^ 2 := by
    nlinarith [Real.sq_sqrt hnonneg,
      Real.sqrt_nonneg (curvDerivNormSq j w'.windowMetric x)]
  rw [S.curvDerivNormSq_output_window j x, ← hactualMetric, ← hmetric]
  exact (mul_le_mul_of_nonneg_left hsquare
    (pow_nonneg S.neck.scale_pos.le _)).trans_eq (mul_comm _ _)

/-- 同 prepared chain、同 F、同实际 records；固定 model window 覆盖所有 born cap。
每阶 late threshold 对所有 history indices 统一，linked/δ-smallness 在证明内支付。 -/
theorem exists_prepared_linked_birth_jets_CXSP
    {P : OrientedThreeStage.{u}} {g : P.Metric}
    {pBase : CutoffParameters} {Γ : ClosedBirthConstants}
    (S : PreparedSpatialChain pBase Γ P g) (F : GC.Interface.RawSurgery P g)
    (hTower : F.tower = S.tower) (q : CutoffParameters)
    (hdiag : ∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
      q.neckRadius t = (chainDiagonal_C11A S).neckRadius t)
    (hD : capWindowRadius_C11E + 1 ≤ pBase.modelRadius) :
    ∃ (params : CutoffParameters)
      (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
        GeometricCutoffRecord (F.tower.history n).toHistory e params),
      (params.fixed = pBase.fixed ∧ params.modelRadius = pBase.modelRadius ∧
        params.modelOrder = pBase.modelOrder ∧ params.modelAccuracy = pBase.modelAccuracy ∧
        params.recenterConstant = pBase.recenterConstant) ∧
      (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
        params.neckRadius t = q.neckRadius t) ∧
      (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) ∧
      Tendsto params.delta atTop (𝓝 0) ∧
      ∀ j : ℕ, ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
          T ≤ (F.tower.history n).time e.succ →
          ∀ b : ((F.tower.history n).toHistory.event e).RetainedBoundaryIndex,
            let cap := (records n e).static b
            (∀ x : standardCapWindow params.modelRadius, ‖x.val‖ < params.modelRadius →
              curvDerivNormSq j ((F.tower.history n).toHistory.event e).outputMetric
                (cap.window x) ≤ C ^ 2 * cap.neck.scale ^ (j + 2)) ∧
            (∀ z : ThreeBall,
              curvDerivNormSq j ((F.tower.history n).toHistory.event e).outputMetric
                (cap.inclusion (cap.witness.cap z)) ≤
                  C ^ 2 * cap.neck.scale ^ (j + 2)) := by
  obtain ⟨F₀, params, _κ, records, hTower₀, hstatic, _hκ, _hκanti, _hδanti, _hnranti,
    hpref, hbridge, _hcan, _hwin, _hnc, _hpast, hdecay, _hrecent⟩ :=
    S.exists_surgery_with_spatial_control_and_decay
  have hF : F₀ = F := by
    have hT := hTower₀.trans hTower.symm
    cases F₀
    cases F
    congr 1
  subst F₀
  have hlinked := hlink_of_narrowTuple_C11SL S F params records hTower hstatic hbridge
  have hparams : ∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
      params.neckRadius t = q.neckRadius t := by
    intro t ht
    have hp := hpref (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩
    have hδ : params.delta t = (chainDiagonal_C11A S).delta t := hp.1
    have hnr : params.neckRadius t = (chainDiagonal_C11A S).neckRadius t := hp.2.1
    exact ⟨hδ.trans (hdiag t ht).1.symm, hnr.trans (hdiag t ht).2.symm⟩
  have hcore : StandardCap.transitionEnd < params.modelRadius := by
    rw [hstatic.2.1]
    have ht := StandardCap.transitionEnd_pos
    unfold capWindowRadius_C11E at hD
    linarith
  have hDpos : 0 < params.modelRadius := StandardCap.transitionEnd_pos.trans hcore
  have hrec : 0 < params.recenterConstant := by linarith [params.recenterConstant_ge_four]
  refine ⟨params, records, hstatic, hparams, hlinked, hdecay, ?_⟩
  intro j
  obtain ⟨C, δstar, hC, hδstar, hjets⟩ :=
    exists_linked_window_birth_jets_CXSP params.fixed params.modelRadius hDpos j
  have hevent : ∀ᶠ t in atTop, params.delta t < δstar / params.recenterConstant :=
    hdecay.eventually (Iio_mem_nhds (div_pos hδstar hrec))
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hevent
  refine ⟨C, max T₀ 1, hC, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro n e hT b
  let cap := (records n e).static b
  have hδ : params.delta ((F.tower.history n).time e.succ) <
      δstar / params.recenterConstant :=
    hT₀ _ ((le_max_left _ _).trans hT)
  have hmul : params.recenterConstant *
      params.delta ((F.tower.history n).time e.succ) ≤ δstar := by
    have h := (lt_div_iff₀ hrec).mp hδ
    nlinarith
  have hsmall : cap.delta ≤ δstar := calc
    cap.delta = params.recenterConstant * (records n e).delta b.1.1 :=
      (records n e).recenter_delta b
    _ ≤ params.recenterConstant * params.delta ((F.tower.history n).time e.succ) :=
      mul_le_mul_of_nonneg_left ((records n e).delta_le b.1.1) hrec.le
    _ ≤ δstar := hmul
  have hfull : ∀ x : standardCapWindow params.modelRadius, ‖x.val‖ < params.modelRadius →
      curvDerivNormSq j ((F.tower.history n).toHistory.event e).outputMetric
        (cap.window x) ≤ C ^ 2 * cap.neck.scale ^ (j + 2) :=
    hjets cap (hlinked n e b) hsmall
  refine ⟨hfull, ?_⟩
  intro z
  obtain ⟨_x₀, _δ, _k, _d, _w, _hscale, _hmetric, hcap, _hδcap, _hk⟩ := hlinked n e b
  obtain ⟨x, hx, hpoint⟩ := hcap z
  have h := hfull x (hx.trans_lt hcore)
  rwa [hpoint] at h

end GC.LongTime.Ch11

end
