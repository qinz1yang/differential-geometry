import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

def eventPrefix (j : Fin H.eventCount) (T : ℝ) (hjT : H.time j.castSucc < T)
    (hTj : T < H.time j.succ) : RetainedCoreHistory.{u} :=
  (H.prefixAt j.castSucc).extendHorizon T hjT.le
    ((H.toHistory.event j).incoming.closedPrefix T hjT hTj) (H.event_initial j)

theorem eventPrefix_activeStage_val (j : Fin H.eventCount) {T : ℝ}
    (hjT : H.time j.castSucc < T) (hTj : T < H.time j.succ)
    (τ : Icc (0 : ℝ) (H.eventPrefix j T hjT hTj).toHistory.horizon)
    (τ' : Icc (0 : ℝ) H.toHistory.horizon) (hττ : (τ : ℝ) = τ') :
    ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ).val =
      (H.toHistory.activeStage τ').val := by
  have hk := (H.eventPrefix j T hjT hTj).toHistory.activeStage_time_le τ
  have h1 : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ) ≤ H.toHistory.activeStage τ' :=
    H.toHistory.le_activeStage τ' _ (by rw [← hττ]; exact hk)
  have hk'τ := H.toHistory.activeStage_time_le τ'
  have hτT : (τ : ℝ) ≤ T := τ.2.2
  have hk'j : H.toHistory.activeStage τ' < j.succ := by
    refine H.time_strictMono.lt_iff_lt.mp ?_
    change H.time (H.toHistory.activeStage τ') < H.time j.succ
    have : (τ' : ℝ) ≤ T := hττ ▸ hτT
    linarith
  have hk'v : (H.toHistory.activeStage τ').val ≤ j.val := by
    have := Fin.lt_def.mp hk'j
    simp only [Fin.val_succ] at this
    omega
  have h2 : (⟨(H.toHistory.activeStage τ').val, by
      change (H.toHistory.activeStage τ').val < j.val + 1
      omega⟩ : Fin ((H.eventPrefix j T hjT hTj).toHistory.eventCount + 1)) ≤
      (H.eventPrefix j T hjT hTj).toHistory.activeStage τ :=
    (H.eventPrefix j T hjT hTj).toHistory.le_activeStage τ _ (by
      change H.time (H.toHistory.activeStage τ') ≤ (τ : ℝ)
      rw [hττ]
      exact hk'τ)
  have h1v := Fin.le_def.mp h1
  have h2v := Fin.le_def.mp h2
  exact le_antisymm h1v h2v

theorem eventPrefix_stageMetric (j : Fin H.eventCount) {T : ℝ}
    (hjT : H.time j.castSucc < T) (hTj : T < H.time j.succ)
    (m : Fin ((H.eventPrefix j T hjT hTj).toHistory.eventCount + 1)) (v : ℝ) :
    (H.eventPrefix j T hjT hTj).toHistory.stageMetric m v =
      H.toHistory.stageMetric
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt)) m) v := by
  cases m using Fin.lastCases with
  | last =>
    rw [ObservedHistory.stageMetric_last_of_lt (h := hjT)]
    change (H.toHistory.event j).incoming.flow.base.metric v =
      H.toHistory.stageMetric j.castSucc v
    rw [ObservedHistory.stageMetric_castSucc_apply]
  | cast i =>
    rw [ObservedHistory.stageMetric_castSucc_apply]
    change _ = H.toHistory.stageMetric (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i).castSucc v
    rw [ObservedHistory.stageMetric_castSucc_apply]
    rfl

private theorem rm_bound_of_stage_eq {K : ObservedHistory.{u}}
    {first last : Fin (K.eventCount + 1)} {hle : first ≤ last} {x : (K.stage last).Carrier}
    (B : BackwardPointTrace K first last hle x) {m m' : Fin (K.eventCount + 1)} (hm : m' = m)
    (h1 : first ≤ m) (h2 : m ≤ last) (h1' : first ≤ m') (h2' : m' ≤ last) (v r : ℝ)
    (h : r ^ 4 * normSq0S (K.stageMetric m' v) (B.point m' h1' h2') 4
      (metricRm04At (K.stageMetric m' v) (B.point m' h1' h2')) ≤ 1) :
    r ^ 4 * normSq0S (K.stageMetric m v) (B.point m h1 h2) 4
      (metricRm04At (K.stageMetric m v) (B.point m h1 h2)) ≤ 1 := by
  subst hm
  exact h

private theorem volume_lower_bound_of_stage_index {κ ρ t₀ : ℝ} (hH : H.NoncollapsedBefore κ ρ t₀)
    (τ : Icc (0 : ℝ) H.toHistory.horizon) (hτ : (τ : ℝ) ≤ t₀)
    (last : Fin (H.eventCount + 1)) (hlast : H.toHistory.activeStage τ = last)
    (p : (H.stage last).Carrier) {r : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ)
    (a : Icc (0 : ℝ) H.toHistory.horizon) (hat : a ≤ τ) (ha : (a : ℝ) = (τ : ℝ) - r ^ 2)
    (first : Fin (H.eventCount + 1)) (hfirst : first ≤ H.toHistory.activeStage a)
    (hf : first ≤ last)
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric last τ) p r,
      ∃ B : BackwardPointTrace H.toHistory first last hf x,
        (∀ (v : Icc (0 : ℝ) H.toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ τ),
          r ^ 4 * normSq0S (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
            (B.point (H.toHistory.activeStage v) (hfirst.trans (H.toHistory.activeStage_mono hav))
              ((H.toHistory.activeStage_mono hvt).trans hlast.le)) 4
            (metricRm04At (H.toHistory.stageMetric (H.toHistory.activeStage v) v)
              (B.point (H.toHistory.activeStage v)
                (hfirst.trans (H.toHistory.activeStage_mono hav))
                ((H.toHistory.activeStage_mono hvt).trans hlast.le))) ≤ 1) ∧
        ∀ (i : Fin H.eventCount) (hi : H.toHistory.activeStage a ≤ i.castSucc)
          (hil : i.succ ≤ last),
          let y : (H.toHistory.event i).incoming.terminalRegularOpen :=
            ⟨B.point i.castSucc (hfirst.trans hi) (i.castSucc_lt_succ.le.trans hil),
              (B.crossing i (hfirst.trans hi) hil).mem_terminalRegularRegion
                (H.toHistory.event i)⟩;
          r ^ 4 * normSq0S (H.toHistory.event i).terminal.metric y 4
            (metricRm04At (H.toHistory.event i).terminal.metric y) ≤ 1) :
    ENNReal.ofReal κ * ENNReal.ofReal r ^ 3 ≤
      riemannianVolumeMeasure ThreeModel (H.stage last).Carrier
        (H.toHistory.stageMetric last τ)
        (riemannianBallOf (H.toHistory.stageMetric last τ) p r) := by
  subst hlast
  refine hH τ p r hτ hrρ ⟨hr, a, hat, ha, fun x hx => ?_⟩
  obtain ⟨B, hobs, hseam⟩ := htrace x hx
  exact ⟨B.restrictFirst hfirst (H.toHistory.activeStage_mono hat), hobs,
    fun i hi hil => hseam i hi hil⟩

theorem noncollapsedBefore_eventPrefix (j : Fin H.eventCount) {T : ℝ}
    (hjT : H.time j.castSucc < T) (hTj : T < H.time j.succ) {κ ρ t₀ : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t₀) (hT : T ≤ t₀) :
    (H.eventPrefix j T hjT hTj).NoncollapsedBefore κ ρ T := by
  have hTH : T ≤ H.horizon := hTj.le.trans (H.toHistory.time_le_horizon_at j.succ)
  intro τ p r hτ hr hball
  obtain ⟨hr0, a, hat, ha, htr⟩ := hball
  let τ' : Icc (0 : ℝ) H.toHistory.horizon := ⟨τ, τ.2.1, τ.2.2.trans hTH⟩
  let a' : Icc (0 : ℝ) H.toHistory.horizon := ⟨a, a.2.1, a.2.2.trans hTH⟩
  have hAτ := H.eventPrefix_activeStage_val j hjT hTj τ τ' rfl
  have hAa := H.eventPrefix_activeStage_val j hjT hTj a a' rfl
  have hka := (H.eventPrefix j T hjT hTj).toHistory.activeStage_mono hat
  rw [H.eventPrefix_stageMetric j hjT hTj]
  refine H.volume_lower_bound_of_stage_index hH τ' (hτ.trans hT)
    (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ)) (Fin.ext hAτ.symm) p hr0 hr a'
    hat ha (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
      ((H.eventPrefix j T hjT hTj).toHistory.activeStage a))
    (Fin.le_def.mpr (le_of_eq hAa)) (Fin.le_def.mpr (Fin.le_def.mp hka)) ?_
  intro x hx
  have hx' : x ∈ riemannianBallOf ((H.eventPrefix j T hjT hTj).toHistory.stageMetric
      ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ) τ) p r := by
    rw [H.eventPrefix_stageMetric j hjT hTj]
    exact hx
  obtain ⟨A, hA1, hA2⟩ := htr x hx'
  refine ⟨H.backwardPointTraceOfPrefix j.castSucc ⟨A.point, A.endpoint_eq, A.crossing⟩, ?_, ?_⟩
  · intro v hav hvt
    have hvT : (v : ℝ) ≤ T := (show (v : ℝ) ≤ τ from hvt).trans τ.2.2
    let vK : Icc (0 : ℝ) (H.eventPrefix j T hjT hTj).toHistory.horizon := ⟨v, v.2.1, hvT⟩
    have hAv := H.eventPrefix_activeStage_val j hjT hTj vK v rfl
    have hav' : a ≤ vK := show (a : ℝ) ≤ v from hav
    have hvt' : vK ≤ τ := show (v : ℝ) ≤ τ from hvt
    have h := hA1 vK hav' hvt'
    rw [H.eventPrefix_stageMetric j hjT hTj] at h
    refine rm_bound_of_stage_eq _ (m' := Fin.castLE
      (Nat.succ_le_succ (Nat.le_of_lt_succ j.castSucc.isLt))
        ((H.eventPrefix j T hjT hTj).toHistory.activeStage vK))
      (m := H.toHistory.activeStage v) (Fin.ext hAv) _ _
      (Fin.le_def.mpr (Fin.le_def.mp
        ((H.eventPrefix j T hjT hTj).toHistory.activeStage_mono hav')))
      (Fin.le_def.mpr (Fin.le_def.mp
        ((H.eventPrefix j T hjT hTj).toHistory.activeStage_mono hvt'))) v r ?_
    exact h
  · intro i hi hil
    have hil' : i.val + 1 ≤ ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ).val :=
      Fin.le_def.mp hil
    have hkj : ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ).val < j.val + 1 :=
      ((H.eventPrefix j T hjT hTj).toHistory.activeStage τ).isLt
    have hi' : ((H.eventPrefix j T hjT hTj).toHistory.activeStage a).val ≤ i.val := by
      rw [hAa]
      exact Fin.le_def.mp hi
    exact hA2 ⟨i.val, by
        change i.val < j.val
        omega⟩ (Fin.le_def.mpr hi') (Fin.le_def.mpr hil')

theorem terminalNoncollapsedBefore_prefixAt (j : Fin H.eventCount) {κ ρ t : ℝ}
    (hH : H.NoncollapsedBefore κ ρ t) :
    (H.prefixAt j.castSucc).TerminalNoncollapsedBefore rfl (H.toHistory.event j).incoming
      (H.event_initial j) κ ρ t :=
  fun _ hT hTs hTt => H.noncollapsedBefore_eventPrefix j hT hTs hH hTt

def prefixRecords (k : Fin (H.eventCount + 1)) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) :
    ∀ i : Fin (H.prefixAt k).eventCount, GeometricCutoffRecord (H.prefixAt k).toHistory i p :=
  fun i => H.geometricCutoffRecordOfPrefix k (records (Fin.castLE (Nat.le_of_lt_succ k.isLt) i))

theorem capWindowPoint_of_prefixAt (j : Fin H.eventCount) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    {y : (H.stage j.castSucc).Carrier} {t D θ : ℝ}
    (h : (H.prefixAt j.castSucc).CapWindowPoint (H.prefixRecords j.castSucc records)
      (Fin.last _) y t D θ) :
    H.CapWindowPoint records j.castSucc y t D θ := by
  obtain ⟨i, hl, A, b, x, h1, h2, h3⟩ := h
  exact ⟨Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) i, Fin.le_def.mpr (Fin.le_def.mp hl),
    H.backwardPointTraceOfPrefix j.castSucc A, b, x, h1, h2, h3⟩

theorem isCanonicalCutoffRecordFamily_prefixAt (k : Fin (H.eventCount + 1))
    {p₀ p : CutoffParameters} {δ₀ ρ₀ : ℝ}
    {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
    (hrec : H.IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ records) :
    (H.prefixAt k).IsCanonicalCutoffRecordFamily p₀ δ₀ ρ₀ (H.prefixRecords k records) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hrec
  exact ⟨h1, h2, h3, h4, h5, fun i b => h6 _ b,
    fun i => h7 (Fin.castLE (Nat.le_of_lt_succ k.isLt) i),
    fun i => h8 (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)⟩

theorem eventSlabsDerivative_prefixAt (k : Fin (H.eventCount + 1)) {Ctime : NNReal} {q : ℝ}
    (h : H.EventSlabsDerivative Ctime q k) :
    (H.prefixAt k).EventSlabsDerivative Ctime q (Fin.last _) :=
  fun i _ => h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) (Fin.lt_def.mpr i.isLt)

theorem eventSlabsPinched_prefixAt (k : Fin (H.eventCount + 1)) {phi : ℝ → ℝ}
    (h : H.EventSlabsPinched phi) : (H.prefixAt k).EventSlabsPinched phi :=
  fun i => h (Fin.castLE (Nat.le_of_lt_succ k.isLt) i)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
