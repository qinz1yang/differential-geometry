import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SurvInduction_S146
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TubeConv_S146
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocationFinal_S146
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSAssembly_S113
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HTSBarrierEvent_S113

/-!
# CH12-S146, group 2d: `hsurv_core_S146` -- survival of a cap-window point to the slice (tube-aware hsurv)

The conclusion is the `hsurvT` of S137 (`hbirth_of_hsurvT_S137` hypothesis, `[FROZEN] CH12-S137 tube`) with two changes
(findings F-S146-1/2, see `[FROZEN] CH12-S146 G1/G2`): the tube has radius `60 * (θ' * ρ)` (not `20 *`) and the `τ`-clause
reads `9 K τ ≤ 1 → 9 K τ ≤ c₀ θ →`, where `(ε₀', c₀, hscaleR)` is the body of `hscale_of_record_S105`.
Proof: downward induction `surv_induction_S146` (hslab := `slab_forward_ball_S147`, tube := `tube_slab_S146`, last stage :=
`final_location_S146`, barrier step := `barrier_event_S113` + `hbirth_pt_S146` + `hno.restrictFirst`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {δ : ℝ → ℝ}

theorem hsurv_core_S146 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (Ctime : ℝ≥0) (hP2 : P2_O2 Hp Ctime)
    (hFront : ∀ (θ Dcap : ℝ), StandardCap.transitionEnd + 3 < Dcap → ∃ (Tf εFr : ℝ), 0 < εFr ∧
      ∀ s : RegularSlice F.observation, Tf ≤ s.time → ∀ T₀ : ℝ, Tf ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εFr → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
        (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ),
        ∀ y ∈ frontier (range ((sliceHistoryR_O3 F s).toHistory.event j).oldOutput),
          ∃ (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            ((records j hj).static b).window x = y ∧ ‖x.val‖ < Dcap - 1 + 1)
    {ε₀' c₀ : ℝ} (hε₀' : 0 < ε₀') (hc₀ : 0 < c₀)
    (hscaleR : ∀ {H : ObservedHistory.{u}} {pp : CutoffParameters} {i : Fin H.eventCount},
      pp.modelAccuracy ≤ ε₀' → 4 ≤ pp.modelOrder → ∀ (R : GeometricCutoffRecord H i pp)
      (b : (H.event i).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < pp.modelRadius → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event i).outputMetric ((R.static b).window x)) :
    ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ (θ Dcap C0 : ℝ), 0 < θ → 0 < C0 →
      StandardCap.transitionEnd + 3 < Dcap → ∀ K : ℝ, 0 < K →
      ∃ (bH TH θH εH : ℝ), 0 < bH ∧ 0 < θH ∧ 0 < εH ∧
      ∀ s : RegularSlice F.observation, TH ≤ s.time → ∀ T₀ : ℝ, TH ≤ T₀ → T₀ ≤ s.time →
      ∀ (pp : CutoffParameters)
        (records : ∀ i : Fin (sliceHistoryR_O3 F s).eventCount,
          T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ →
          GeometricCutoffRecord (sliceHistoryR_O3 F s).toHistory i pp),
        pp.delta = Hp.parameters.delta → pp.neckRadius = Hp.parameters.neckRadius →
        pp.fixed = Hp.parameters.fixed → pp.recenterConstant = Hp.parameters.recenterConstant →
        32 * (Dcap + 1) + 2 ≤ pp.modelRadius →
        pp.modelAccuracy ≤ εH → 4 ≤ pp.modelOrder →
        (∀ i hi b, linkedCanonicalWindow_O2 ((records i hi).static b)) →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ bH * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        (∀ x ∈ riemannianBallOf s.metric p (2 * ρ), metricScalarAt s.metric x ≤ C0 / ρ ^ 2) →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          ¬ (∃ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (hl : j.succ ≤ Fin.last (sliceHistoryR_O3 F s).eventCount)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) hl q)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius),
            B.point j.succ le_rfl hl = ((records j hj).static b).window x ∧
              ‖x.val‖ < Dcap + 1 ∧
              s.time - (sliceHistoryR_O3 F s).time j.succ ≤
                θ * (((records j hj).static b).neck.scale)⁻¹) →
          ∀ θ' : ℝ, 0 < θ' → θ' ≤ θH → ∀ τ : ℝ, 0 < τ → 9 * K * τ ≤ 1 → 9 * K * τ ≤ c₀ * θ →
          ∀ (j : Fin (sliceHistoryR_O3 F s).eventCount)
            (hj : T₀ - θ ≤ (sliceHistoryR_O3 F s).time j.succ)
            (B : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
              (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) q)
            (_ : ∀ (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
              (hav : towerIdx_S137 s j.succ ≤ (sliceTowerHistory_CX2 s).activeStage v)
              (hvt : (sliceTowerHistory_CX2 s).activeStage v ≤
                towerIdx_S137 s (Fin.last (sliceHistoryR_O3 F s).eventCount)),
              v.val ≤ s.time →
              ∀ q ∈ riemannianBallOf
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v)
                ((towerTrace_S137 s B).point ((sliceTowerHistory_CX2 s).activeStage v) hav hvt) (60 * (θ' * ρ)),
              Real.sqrt (normSq0S
                ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
                (metricRm04At
                  ((sliceTowerHistory_CX2 s).stageMetric ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ K / (θ' * ρ) ^ 2)
            (b : ((sliceHistoryR_O3 F s).toHistory.event j).RetainedBoundaryIndex)
            (x : standardCapWindow pp.modelRadius), ‖x.val‖ < Dcap - 1 + 1 →
            ((records j hj).static b).window x ∈
              riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
                (B.point j.succ le_rfl (Fin.le_last _)) (20 * (θ' * ρ)) →
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
              (((records j hj).static b).window x) ≤ 9 * K / (θ' * ρ) ^ 2 →
            s.time - (sliceHistoryR_O3 F s).time j.succ < τ * (θ' * ρ) ^ 2 →
            ∃ yf ∈ riemannianBallOf s.metric p (2 * ρ),
              ∃ A : BackwardPointTrace (sliceHistoryR_O3 F s).toHistory j.succ
                (Fin.last (sliceHistoryR_O3 F s).eventCount) (Fin.le_last _) yf,
                A.point j.succ le_rfl (Fin.le_last _) = ((records j hj).static b).window x := by
  intro w hw Λ hΛ θ Dcap C0 hθ hC0 hD K hK
  obtain ⟨Tf, εFr, hεFr, hFr⟩ := hFront θ Dcap hD
  obtain ⟨T₁, hT₁, hmic⟩ := micro_scale_le_neckRadius_O13 Hp Λ 1 (by linarith) one_pos
  have hm : 0 < max C0 1 := lt_max_of_lt_right one_pos
  have hCb : 0 < (1 + (Ctime : ℝ)) * max C0 1 / c₀ := by positivity
  set Cb : ℝ := (1 + (Ctime : ℝ)) * max C0 1 / c₀ with hCbdef
  have hsq : 0 < 120 * Real.sqrt Cb + 1 := by positivity
  refine ⟨1, max Tf T₁, min (1 / (120 * Real.sqrt Cb + 1)) (1 / 60),
    min εFr (min ε₀' (3 / 4)), one_pos, lt_min (by positivity) (by norm_num),
    lt_min hεFr (lt_min hε₀' (by norm_num)), ?_⟩
  intro s hs T₀ hT₀ hT₀s pp records e1 e2 e3 e4 hmr hacc hord hlink p ρ hρ hρb h2 h3 h4 h5 h6 q hq hno
    θ' hθ' hθ'H τ hτ hτK hτθ j hj B htube b x hx hmem hsc hage
  obtain ⟨hsTf, hsT₁⟩ := max_le_iff.mp hs
  obtain ⟨hTf₀, -⟩ := max_le_iff.mp hT₀
  have hθ1 : θ' ≤ 1 / (120 * Real.sqrt Cb + 1) := hθ'H.trans (min_le_left _ _)
  have hθ60 : θ' ≤ 1 / 60 := hθ'H.trans (min_le_right _ _)
  have haccFr : pp.modelAccuracy ≤ εFr := hacc.trans (min_le_left _ _)
  have hacc0 : pp.modelAccuracy ≤ ε₀' := hacc.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hacc34 : pp.modelAccuracy ≤ 3 / 4 := hacc.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hρN : ρ ≤ Hp.parameters.neckRadius s.time := by simpa using hmic s hsT₁ ρ h2
  have hr₀ : 0 < θ' * ρ := mul_pos hθ' hρ
  have hr₀2 : 0 < (θ' * ρ) ^ 2 := by positivity
  have hr0' : θ' * ρ ≠ 0 := hr₀.ne'
  have hKb : 0 ≤ K / (θ' * ρ) ^ 2 := by positivity
  have hAρ : 60 * (θ' * ρ) ≤ ρ := by
    have := mul_le_mul_of_nonneg_right hθ60 hρ.le
    linarith only [this]
  have hte := StandardCap.transitionEnd_pos
  have hDnn : 0 ≤ Dcap := by linarith only [hD, hte]
  have hlast_le : (sliceHistoryR_O3 F s).time (Fin.last (sliceHistoryR_O3 F s).eventCount) ≤ s.time :=
    (sliceSlabR_O3 F s).lt.le
  have key := surv_induction_S146 (Kb := K / (θ' * ρ) ^ 2) (Abar := 60 * (θ' * ρ)) (T := s.time)
    B (fun y => y ∈ riemannianBallOf s.metric p (2 * ρ)) hKb hlast_le slab_forward_ball_S147
    (tube_slab_S146 s B htube)
    (fun a ha hae y hy => final_location_S146 s hKb ha hae hAρ hq (tube_final_S146 s B htube) y hy)
    (by
      intro i hi hS a ha hae
      have hi1 : j.succ ≤ i.succ := hi.trans i.castSucc_lt_succ.le
      have hmono := (sliceHistoryR_O3 F s).time_strictMono.monotone hi1
      have hts_i : (sliceHistoryR_O3 F s).time i.succ ≤ s.time :=
        ((sliceHistoryR_O3 F s).time_strictMono.monotone (Fin.le_last _)).trans hlast_le
      have hji : T₀ - θ ≤ (sliceHistoryR_O3 F s).time i.succ := hj.trans hmono
      have hE1 : 1 ≤ Real.exp (9 * (K / (θ' * ρ) ^ 2) * (s.time - (sliceHistoryR_O3 F s).time i.succ)) :=
        Real.one_le_exp (by have := sub_nonneg.2 hts_i; positivity)
      have haA : a < 60 * (θ' * ρ) := lt_of_le_of_lt (le_mul_of_one_le_right ha.le hE1) hae
      have hage_i : s.time - (sliceHistoryR_O3 F s).time i.succ < τ * (θ' * ρ) ^ 2 :=
        lt_of_le_of_lt (by linarith only [hmono]) hage
      have ha0 : a ≠ 0 := ha.ne'
      have hrb : 0 < a / 20 := by positivity
      have hKbar : 9 * (K * (a / 20) ^ 2 / (θ' * ρ) ^ 2) / (a / 20) ^ 2 = 9 * K / (θ' * ρ) ^ 2 := by
        field_simp
      have hτb : 0 < τ * (θ' * ρ) ^ 2 / (a / 20) ^ 2 := by positivity
      have hKτ : 9 * (K * (a / 20) ^ 2 / (θ' * ρ) ^ 2) * (τ * (θ' * ρ) ^ 2 / (a / 20) ^ 2) =
          9 * K * τ := by field_simp
      have hagej : s.time - (sliceHistoryR_O3 F s).time i.succ <
          (τ * (θ' * ρ) ^ 2 / (a / 20) ^ 2) * (a / 20) ^ 2 := by
        rw [div_mul_cancel₀ _ (by positivity)]; exact hage_i
      have hFi := hFr s hsTf T₀ hTf₀ hT₀s pp records e1 e2 e3 e4 hmr haccFr hord hlink i hji
      have hscale : ∀ (b' : ((sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
          (x' : standardCapWindow pp.modelRadius), ‖x'.val‖ < Dcap - 1 + 1 →
          c₀ * ((records i hji).static b').neck.scale ≤
            metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
              (((records i hji).static b').window x') :=
        fun b' x' hx' => hscaleR hacc0 hord (records i hji) b' x'
          (lt_of_lt_of_le hx' (by linarith only [hmr, hDnn]))
      have hout : ∀ z, metricScalarAt ((sliceHistoryR_O3 F s).initialMetric i.succ) z =
          metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric z := by
        intro z; rw [(sliceHistoryR_O3 F s).toHistory.event_output i]
      have hshift : ∀ (b' : ((sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
          (x' : standardCapWindow pp.modelRadius), ‖x'.val‖ < Dcap - 1 + 1 →
          ((records i hji).static b').window x' ∈
            riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
              (B.point i.succ hi1 (Fin.le_last _)) (20 * (a / 20)) →
          metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
            (((records i hji).static b').window x') ≤
              9 * (K * (a / 20) ^ 2 / (θ' * ρ) ^ 2) / (a / 20) ^ 2 →
          40 * (a / 20) * Real.sqrt ((records i hji).static b').neck.scale ≤ 1 := by
        intro b' x' hx' hmem' hsc'
        have h20 : 20 * (a / 20) = a := by ring
        rw [h20] at hmem'
        have hmem'' : riemannianEDistOf ((sliceHistoryR_O3 F s).initialMetric i.succ)
            (B.point i.succ hi1 (Fin.le_last _)) (((records i hji).static b').window x') <
            ENNReal.ofReal a := by
          have this : riemannianEDistOf ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
              (B.point i.succ hi1 (Fin.le_last _)) (((records i hji).static b').window x') <
              ENNReal.ofReal a := hmem'
          rw [(sliceHistoryR_O3 F s).toHistory.event_output i] at this
          exact this
        obtain ⟨yf, hTgt, A, hA⟩ := hS a ha hae _ hmem''
        have hqpos : 0 < ((records i hji).static b').neck.scale :=
          ((records i hji).static b').neck.scale_pos
        have hlow : c₀ * ((records i hji).static b').neck.scale ≤
            metricScalarAt ((sliceHistoryR_O3 F s).initialMetric i.succ)
              (A.point i.succ le_rfl (Fin.le_last _)) := by
          rw [hA, hout]; exact hscale b' x' hx'
        have hsc_le : metricScalarAt ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
            (((records i hji).static b').window x') ≤ 9 * K / (θ' * ρ) ^ 2 := by
          rw [← hKbar]; exact hsc'
        have hage0 : 0 ≤ s.time - (sliceHistoryR_O3 F s).time i.succ := sub_nonneg.2 hts_i
        have haT : metricScalarAt ((sliceHistoryR_O3 F s).initialMetric i.succ)
            (A.point i.succ le_rfl (Fin.le_last _)) *
            (s.time - (sliceHistoryR_O3 F s).time i.succ) ≤ 1 := by
          rw [hA, hout]
          calc _ ≤ 9 * K / (θ' * ρ) ^ 2 * (τ * (θ' * ρ) ^ 2) :=
                mul_le_mul hsc_le hage_i.le hage0 (by positivity)
            _ = 9 * K * τ := by field_simp
            _ ≤ 1 := hτK
        have hbirth := hbirth_pt_S146 Hp s Ctime hP2 hρ hc₀ hqpos hρN i.succ (Fin.le_last _) yf
          (h6 yf hTgt) A hlow haT
        have hs16 : Real.sqrt (Cb / 16) = Real.sqrt Cb / 4 := by
          rw [Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 16)]
          congr 1
          rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        have hh1 : θ' * (120 * Real.sqrt Cb + 1) ≤ 1 := by
          rw [le_div_iff₀ hsq] at hθ1; exact hθ1
        have hh2 : a / 20 / ρ ≤ 3 * θ' := by
          rw [div_le_iff₀ hρ]; nlinarith only [haA]
        have hsC : 0 ≤ Real.sqrt Cb := Real.sqrt_nonneg _
        refine shift_le_of_birth_S105 (a := a / 20 / ρ) (C₀ := Cb / 16) hρ (by positivity)
          (by positivity) ?_ (by field_simp) ?_
        · rw [show 16 * (Cb / 16) = Cb by ring]; exact hbirth
        · calc a / 20 / ρ * (160 * Real.sqrt (Cb / 16)) = a / 20 / ρ * (40 * Real.sqrt Cb) := by
                rw [hs16]; ring
            _ ≤ 3 * θ' * (40 * Real.sqrt Cb) := mul_le_mul_of_nonneg_right hh2 (by positivity)
            _ = 120 * θ' * Real.sqrt Cb := by ring
            _ ≤ 1 := by nlinarith only [hh1, hθ']
      have hnoCap : ¬ ∃ (b' : ((sliceHistoryR_O3 F s).toHistory.event i).RetainedBoundaryIndex)
          (x' : standardCapWindow pp.modelRadius), ‖x'.val‖ < Dcap - 1 + 2 ∧
          ((records i hji).static b').window x' = B.point i.succ hi1 (Fin.le_last _) ∧
          s.time - (sliceHistoryR_O3 F s).time i.succ ≤ θ * (((records i hji).static b').neck.scale)⁻¹ := by
        rintro ⟨b', x', hx', hwc, hag⟩
        exact hno ⟨i, hji, Fin.le_last _, B.restrictFirst hi1 (Fin.le_last _), b', x', hwc.symm,
          by linarith only [hx'], hag⟩
      have hcross0 := B.crossing i hi (Fin.le_last _)
      obtain ⟨z, -, hzp, -⟩ := hcross0
      have hcross : ((sliceHistoryR_O3 F s).toHistory.event i).RegularCrossing
          (((sliceHistoryR_O3 F s).toHistory.event i).oldTerminal z).val
          (B.point i.succ hi1 (Fin.le_last _)) := by
        have := B.crossing i hi (Fin.le_last _)
        rwa [((sliceHistoryR_O3 F s).toHistory.event i).oldTerminal_eq z |>.trans hzp |>.symm.symm]
      refine barrier_event_S113 (records i hji) (Dc := Dcap - 1) (r := a / 20)
        (K := K * (a / 20) ^ 2 / (θ' * ρ) ^ 2) (τ := τ * (θ' * ρ) ^ 2 / (a / 20) ^ 2) (c₀ := c₀) (θ := θ)
        (age := s.time - (sliceHistoryR_O3 F s).time i.succ) hFi hrb hτb hc₀
        (by rw [hKτ]; exact hτθ) (by linarith only [hmr, hDnn]) hacc34 hscale hshift hagej hnoCap
        (U := riemannianBallOf ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
          (B.point i.succ hi1 (Fin.le_last _)) a)
        (fun y hy => by rw [show 20 * (a / 20) = a by ring]; exact hy)
        (isPathConnected_riemannianBallOf _ _ ha).isConnected.isPreconnected ?_ ?_ hcross
      · intro y hy
        rw [hKbar]
        have hyb : y ∈ riemannianBallOf ((sliceHistoryR_O3 F s).initialMetric i.succ)
            (B.point i.succ hi1 (Fin.le_last _)) (60 * (θ' * ρ)) := by
          have this : riemannianEDistOf ((sliceHistoryR_O3 F s).toHistory.event i).outputMetric
              (B.point i.succ hi1 (Fin.le_last _)) y < ENNReal.ofReal a := hy
          rw [(sliceHistoryR_O3 F s).toHistory.event_output i] at this
          change riemannianEDistOf _ _ _ < _
          exact this.trans ((ENNReal.ofReal_lt_ofReal_iff (by linarith only [haA, ha])).2 haA)
        have h1 := tube_out_S146 s B htube i hi y hyb
        have h2' := scalar_le_nine_rm_bound_CX2 _ ((sliceHistoryR_O3 F s).initialMetric i.succ) y h1
        rw [← hout y]
        exact h2'
      · change riemannianEDistOf _ _ _ < _
        rw [riemannianEDistOf_self]
        exact ENNReal.ofReal_pos.2 ha)
  have hage1 : 9 * (K / (θ' * ρ) ^ 2) * (s.time - (sliceHistoryR_O3 F s).time j.succ) < 1 := by
    have h1 : K / (θ' * ρ) ^ 2 * (s.time - (sliceHistoryR_O3 F s).time j.succ) <
        K / (θ' * ρ) ^ 2 * (τ * (θ' * ρ) ^ 2) := mul_lt_mul_of_pos_left hage (by positivity)
    have h2' : K / (θ' * ρ) ^ 2 * (τ * (θ' * ρ) ^ 2) = K * τ := by field_simp
    nlinarith only [h1, h2', hτK]
  have hae0 : 20 * (θ' * ρ) * Real.exp (9 * (K / (θ' * ρ) ^ 2) *
      (s.time - (sliceHistoryR_O3 F s).time j.succ)) < 60 * (θ' * ρ) := by
    have he : Real.exp (9 * (K / (θ' * ρ) ^ 2) * (s.time - (sliceHistoryR_O3 F s).time j.succ)) < 3 :=
      lt_of_lt_of_le (Real.exp_lt_exp.2 hage1) ((Real.exp_one_lt_d9.le).trans (by norm_num))
    nlinarith only [he, hr₀]
  have hmem' : riemannianEDistOf ((sliceHistoryR_O3 F s).initialMetric j.succ)
      (B.point j.succ le_rfl (Fin.le_last _)) (((records j hj).static b).window x) <
      ENNReal.ofReal (20 * (θ' * ρ)) := by
    have this : riemannianEDistOf ((sliceHistoryR_O3 F s).toHistory.event j).outputMetric
        (B.point j.succ le_rfl (Fin.le_last _)) (((records j hj).static b).window x) <
        ENNReal.ofReal (20 * (θ' * ρ)) := hmem
    rw [(sliceHistoryR_O3 F s).toHistory.event_output j] at this
    exact this
  exact key j.succ le_rfl (20 * (θ' * ρ)) (by positivity) hae0 _ hmem'

end GC.LongTime.Ch12
