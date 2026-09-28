import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

set_option autoImplicit false

noncomputable section

open Set Function Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp⟩
private local instance : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp⟩
private local instance (D : ℝ) : SigmaCompactSpace (standardCapWindow D) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      (standardCapWindow D).isOpen)

theorem exists_presented_cap_window_scalar_lower_bound (Dcap Dstar : ℝ)
    (hD : Dcap + 1 < Dstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
        {fixed : StaticCapScaffold} {D : ℝ} {m : ℕ} {ε : ℝ}, Dstar ≤ D → ε ≤ ε₀ → 2 ≤ m →
        ∀ {b : E.RetainedBoundaryIndex}
          (S : E.PresentedStaticCap fixed D m ε b), S.hasCanonicalWindow →
          ∀ x : standardCapWindow D, ‖x.val‖ < Dcap + 1 →
            S.neck.scale / 2 ≤ metricScalarAt E.outputMetric (S.window x) := by
  obtain ⟨ε₀, C, hε₀, _, hbound⟩ :=
    StandardCap.exists_uniform_window_scalar_bounds_of_metric_close Dstar (Dcap + 1)
      (hD.trans (lt_add_one Dstar))
  refine ⟨ε₀, hε₀, ?_⟩
  intro P Q a s E fixed D m ε hDD hε hm b S hcanonical x hxn
  obtain ⟨x₀, δ, k, d, w, _, hinner, -⟩ := hcanonical
  have hDpos : 0 < Dstar := by
    have := norm_nonneg x.val
    linarith
  let ws := w.restrictWindow hDpos hDD
  have hs : standardCapWindow Dstar ≤ standardCapWindow D := fun _ hy =>
    hy.trans_le (add_le_add hDD le_rfl)
  let inc := TopologicalSpace.Opens.inclusion hs
  let x' : standardCapWindow Dstar := ⟨x.val, show ‖x.val‖ < Dstar + 1 by linarith⟩
  have hsmall := ws.properties.window_close
  change metricDerivENormSupOn
    {y : standardCapWindow Dstar |
      (riemannianEDistOf StandardCap.metric 0 y.val).toReal < Dstar} m
    ws.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
      (StandardCap.metric.restrictOpen (standardCapWindow Dstar)) < ENNReal.ofReal ε at hsmall
  simp only [StandardCap.distance_zero] at hsmall
  have hrestrict := metricDerivENormSupOn_mono
    (show {y : standardCapWindow Dstar | ‖y.val‖ ≤ Dcap + 1} ⊆
      {y : standardCapWindow Dstar | ‖y.val‖ < Dstar} from fun y hy => hy.trans_lt hD)
    hm ws.windowMetric (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
      (StandardCap.metric.restrictOpen (standardCapWindow Dstar))
  have hscalar := (hbound ws.windowMetric
    (hrestrict.trans_lt (hsmall.trans_le (ENNReal.ofReal_le_ofReal hε))) x' hxn.le).1
  have hinc : ContMDiff ThreeModel ThreeModel ∞ inc := contMDiff_inclusion hs
  have hJ : ContMDiff ThreeModel ThreeModel ∞ (S.window ∘ inc) :=
    S.window_smooth.contMDiff.comp hinc
  have hlocal : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (S.window ∘ inc) :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv
      (S.window ∘ inc) hJ
      (fun p => by
        have hd := mfderiv_comp p (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
          (hinc.mdifferentiableAt (by simp))
        simp only [inc, mfderiv_opens_incl] at hd
        dsimp only [TangentSpace] at hd ⊢
        rw [hd]
        exact (S.window_smooth.isImmersion.isImmersionAt (inc p)).injective_mfderiv (by simp))
      rfl
  have hinj : Function.Injective (S.window ∘ inc) := fun p q h => by
    have h' := S.window_smooth.isEmbedding.injective h
    exact Subtype.ext (congrArg (fun y : standardCapWindow D => y.val) h')
  have heq := (curvature_of_injective_local_isometry ws.windowMetric
    (scaleMetric S.neck.scale S.neck.scale_pos E.outputMetric) (S.window ∘ inc) hlocal hinj
    (fun y v v' => by
      rw [scaleMetric_inner,
        StandardCap.CanonicalStaticInsertionWitness.restrictWindow_windowMetric]
      change w.windowMetric.inner (inc y) v v' = _
      have hd := mfderiv_comp y (S.window_smooth.contMDiff.mdifferentiableAt (by simp))
        (hinc.mdifferentiableAt (by simp))
      simp only [inc, mfderiv_opens_incl] at hd
      dsimp only [TangentSpace] at hd ⊢
      rw [hd]
      exact hinner (inc y) v v') x').1
  rw [metricScalarAt_scaleMetric] at heq
  have hx'eq : (S.window ∘ inc) x' = S.window x := rfl
  have hnormalized : S.neck.scale * metricScalarAt ws.windowMetric x' =
      metricScalarAt E.outputMetric (S.window x) := by
    rw [heq, hx'eq, ← mul_assoc, mul_inv_cancel₀ S.neck.scale_pos.ne', one_mul]
  have hlower := mul_le_mul_of_nonneg_left hscalar.le S.neck.scale_pos.le
  rw [hnormalized] at hlower
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using hlower

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem exists_window_scalar_lower_bound (Dcap Dstar : ℝ) (hD : Dcap + 1 < Dstar) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
        (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p),
        (∀ i b, ((records i).static b).hasCanonicalWindow) →
        Dstar ≤ p.modelRadius → p.modelAccuracy ≤ ε₀ → 2 ≤ p.modelOrder →
        ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
          (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
          ((records j).static b).neck.scale / 2 ≤
            metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x) := by
  obtain ⟨ε₀, hε₀, hbound⟩ := exists_presented_cap_window_scalar_lower_bound.{u} Dcap Dstar hD
  refine ⟨ε₀, hε₀, ?_⟩
  intro H p records hcan hDp hacc hm j b x hx
  change _ ≤ metricScalarAt (H.toHistory.initialMetric j.succ) _
  rw [← H.toHistory.event_output j]
  exact hbound (H.toHistory.event j) hDp hacc hm ((records j).static b) (hcan j b) x hx

private theorem time_lt_succ_of_activeStage_eq_castSucc (t : Icc (0 : ℝ) H.toHistory.horizon)
    (i : Fin H.eventCount) (hi : H.toHistory.activeStage t = i.castSucc) :
    (t : ℝ) < H.time i.succ := by
  have hval : (H.toHistory.activeStage t).val < H.toHistory.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.toHistory.activeStage_before_next t hval
  have he : (⟨(H.toHistory.activeStage t).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.toHistory.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

private theorem false_of_capWindowPoint_of_scalar_le {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {Ctime : ℝ≥0} {qcan M Cw Dcap θcap : ℝ} (hqM : qcan ≤ M) (hCw : 1 ≤ Cw)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / Cw ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (Cw + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (t : Icc (0 : ℝ) H.toHistory.horizon)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hnext : ∀ i : Fin H.eventCount, H.toHistory.activeStage t = i.castSucc →
      (t : ℝ) < H.time i.succ)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ i : Fin H.eventCount, i.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hcw : H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap) : False := by
  obtain ⟨j, hl, A, b, x, hAx, hxn, hage⟩ := hcw
  set S := ((records j).static b).neck.scale with hSdef
  have hSpos : 0 < S := ((records j).static b).neck.scale_pos
  have hC : (0 : ℝ) ≤ Ctime := Ctime.coe_nonneg
  have hjt : H.time j.succ ≤ t :=
    (H.time_strictMono.monotone hl).trans (H.toHistory.activeStage_time_le t)
  have hθ : 0 ≤ θcap := by
    have h0 : 0 ≤ θcap * S⁻¹ := (sub_nonneg.mpr hjt).trans hage
    exact nonneg_of_mul_nonneg_left h0 (inv_pos.mpr hSpos)
  set K := Cw + Ctime * θcap with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ (Ctime : ℝ) * θcap := mul_nonneg hC hθ
    linarith
  set q := max M (S / (2 * K)) with hqdef
  have hq : 0 < q := lt_of_lt_of_le (by positivity) (le_max_right M (S / (2 * K)))
  have hKq : K * q < S := by
    rcases le_total M (S / (2 * K)) with h | h
    · rw [hqdef, max_eq_right h, mul_div_assoc']
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    · rw [hqdef, max_eq_left h]
      exact hbig j b
  have hrec := A.inv_max_stageMetric_scalar_sub_le_of_derivativeBoundBefore hq
    (hqM.trans (le_max_left M _)) (H.toHistory.activeStage_time_le t) hnext t.2.2 hslabs
    hcurrent hfinal j.succ le_rfl hl le_rfl
    (fun i hi => hi ▸ H.time_strictMono (Fin.castSucc_lt_succ (i := i))) hjt
  rw [max_eq_left (hyM.trans (le_max_left M _)), H.toHistory.stageMetric_initial, hAx] at hrec
  set Rj := metricScalarAt (H.toHistory.initialMetric j.succ)
    (((records j).static b).window x) with hRj
  have hlow : S / Cw ≤ Rj := hwinScale j b x hxn
  have hCwpos : 0 < Cw := lt_of_lt_of_le one_pos hCw
  have hRjpos : 0 < Rj := lt_of_lt_of_le (div_pos hSpos hCwpos) hlow
  have hinvRj : (max q Rj)⁻¹ ≤ Cw / S := by
    calc (max q Rj)⁻¹ ≤ Rj⁻¹ := inv_anti₀ hRjpos (le_max_right q Rj)
      _ ≤ (S / Cw)⁻¹ := inv_anti₀ (div_pos hSpos hCwpos) hlow
      _ = Cw / S := inv_div S Cw
  have hgap : q⁻¹ - (max q Rj)⁻¹ ≤ Ctime * ((t : ℝ) - H.time j.succ) := by
    have := (abs_le.mp hrec).1
    linarith
  have hage' : (Ctime : ℝ) * ((t : ℝ) - H.time j.succ) ≤ Ctime * θcap / S := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (by rwa [div_eq_mul_inv]) hC
  have hqinv : q⁻¹ ≤ K / S := by
    rw [hKdef, add_div]
    linarith
  rw [inv_le_iff_one_le_mul₀ hq, div_mul_eq_mul_div, one_le_div hSpos] at hqinv
  linarith

theorem not_capWindowPoint_of_scalar_le {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {Ctime : ℝ≥0} {qcan M Cw Dcap θcap : ℝ} (hqM : qcan ≤ M) (hCw : 1 ≤ Cw)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / Cw ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (Cw + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (i : Fin H.eventCount)
    (hi : H.toHistory.activeStage t = i.castSucc)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : (H.toHistory.event i).incoming.DerivativeBoundBefore Ctime qcan t) :
    ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := fun hcw =>
  H.false_of_capWindowPoint_of_scalar_le records hqM hCw hwinScale hbig t y hyM
    (fun j hj => H.time_lt_succ_of_activeStage_eq_castSucc t j hj) hslabs
    (fun j hj => by
      have : j = i := Fin.castSucc_injective _ (hj.trans hi)
      subst this
      exact hcurrent)
    (fun _ h => absurd (hi.symm.trans h) (Fin.castSucc_ne_last i)) hcw

theorem not_capWindowPoint_of_scalar_le_of_activeStage_eq_last {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {Ctime : ℝ≥0} {qcan M Cw Dcap θcap : ℝ} (hqM : qcan ≤ M) (hCw : 1 ≤ Cw)
    (hwinScale : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex)
      (x : standardCapWindow p.modelRadius), ‖x.val‖ < Dcap + 1 →
      ((records j).static b).neck.scale / Cw ≤
        metricScalarAt (H.initialMetric j.succ) (((records j).static b).window x))
    (hbig : ∀ (j : Fin H.eventCount) (b : (H.toHistory.event j).RetainedBoundaryIndex),
      (Cw + Ctime * θcap) * M < ((records j).static b).neck.scale)
    (t : Icc (0 : ℝ) H.toHistory.horizon) (h : H.time (Fin.last H.eventCount) < H.horizon)
    (hlastA : H.toHistory.activeStage t = Fin.last H.eventCount)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hyM : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) y ≤ M)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hfinal : ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime
      qcan t) :
    ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t Dcap θcap := fun hcw =>
  H.false_of_capWindowPoint_of_scalar_le records hqM hCw hwinScale hbig t y hyM
    (fun j hj => absurd (hj.symm.trans hlastA) (Fin.castSucc_ne_last j)) hslabs
    (fun j hj => absurd (hj.trans hlastA) (Fin.castSucc_ne_last j))
    (fun h' _ => by
      have : h' = h := rfl
      subst this
      exact hfinal) hcw

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
