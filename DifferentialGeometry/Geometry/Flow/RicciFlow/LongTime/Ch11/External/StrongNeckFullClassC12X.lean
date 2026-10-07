import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullLeafC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullCanonicalC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StrongNecksOfCutoffClass

/-!
# Strong necks of the cutoff class without truncation (C12X, S16 G2g)

`strong_necks_full_of_cutoff_class_C12X P₀ g₀ : StrongNecksFullOfCutoffClass_C12X P₀ g₀` is
`strong_necks_of_cutoff_class` (`Surgery/Neck/Cutoff`) re-threaded through the full branches:
old points (G2c, slab `CanonicalBefore`), cap-window points (G2c, non-neck witness) and young
crossing points (G2f).  Same hypotheses as the tree statement; the only change in the constants is
the diagonal choice `ε₁ := ε`, admissible under the new explicit constraint `ε ≤ εStrong_C12X`.
The conclusion carries `HistoryStrongNeckFull_C12X` (depth-one `StrongNeck` on the survivor flow,
accuracy `ε`).  `strongNecksOfCutoffClass_of_full_C12X` re-derives the tree theorem from it.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- `StrongNecksOfCutoffClass` on the diagonal `ε₁ := ε` with full history necks; the accuracy
constraint is the explicit binder `ε ≤ εStrong_C12X` (other binders and hypotheses verbatim). -/
def StrongNecksFullOfCutoffClass_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) : Prop :=
  ∀ (B ε : ℝ), 0 < B → 0 < ε → ε ≤ εStrong_C12X.{u} →
  ∀ (C1 C2 C1s C2s qcan τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ) (phi : ℝ → ℝ),
    1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < κ →
    Perelman.AdmissiblePinchingFunction phi →
  ∃ (C1h C2h qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
    1 ≤ C1h ∧ 1 ≤ C2h ∧ qcan ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
  ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
    p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
    δbound ≤ δmax → ρbound ≤ ρmax →
  ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound),
    H.EventSlabsPinched phi →
    H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
    H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
    H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
    H.EventSlabsSpatiallyCanonical ε C1s C2s qcan (Fin.last H.eventCount) →
    H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
    H.EventSlabsStronglyCanonicalFull_C12X ε ε C1h C2h qh (Fin.last H.eventCount) ∧
    ∀ (s : ℝ)
      (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
      (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
      Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
      G.CanonicalBefore ε C1 C2 qcan τmin s → G.DerivativeBoundBefore Ctime qcan s →
      G.GradientBoundBefore Cgrad qcan s → G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
      (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
        H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀) →
      H.StronglyCanonicalBeforeFull_C12X (Fin.last H.eventCount) G ε ε C1h C2h qh s

/-- **S16 main theorem (G2)**: `strong_necks_of_cutoff_class` without truncation, on the
diagonal `ε₁ := ε`, under the constant constraint `ε ≤ εStrong_C12X`. -/
theorem strong_necks_full_of_cutoff_class_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksFullOfCutoffClass_C12X P₀ g₀ := by
  intro B ε hB hε hεb
  have hε' : ε < 1 / 11 := (hεb.trans_lt εStrong_C12X_lt).trans (by norm_num)
  obtain ⟨Cx, hCx, hXB⟩ := strongSpatialCrossingContinuationFull_holds_C12X P₀ g₀ ε hε hεb
  intro C1 C2 C1s C2s qcan τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s hqcan hτ hκ hphi
  obtain ⟨Dcap, θcap, q₀, mcap, hDcap, hθcap, -, hXq⟩ :=
    hXB B hB C1 C2 τmin Ctime Cgrad hC1 hC2 hτ C1s C2s 1 hC1s hC2s le_rfl κ phi τmin hκ hphi hτ
  obtain ⟨Cs, Rcap, mw, hCs, hRcap, hW⟩ :=
    RetainedCoreHistory.exists_capWindow_stronglyCanonicalWhereFull_C12X P₀ g₀ hε hε' Ctime Cgrad
      Dcap θcap hDcap hθcap
  set qh := max qcan q₀ with hqhdef
  have hqh : qcan ≤ qh := le_max_left _ _
  obtain ⟨δX, ρX, εX, hδX, hρX, hεX, hXp⟩ := hXq qh (le_max_right _ _)
  obtain ⟨δW, ρW, εW, hδW, hρW, hεW, hWp⟩ := hW qh (hqcan.trans_le hqh)
  set C1h := max C1 (max Cs Cx) with hC1hdef
  set C2h := max C2 (max (max Cs (Cgrad : ℝ)) Cx) with hC2hdef
  refine ⟨C1h, C2h, qh, min δX δW, min ρX ρW, min εX εW, Rcap, max mcap mw,
    le_max_of_le_left hC1, le_max_of_le_left hC2, hqh, lt_min hδX hδW, lt_min hρX hρW,
    lt_min hεX hεW, by linarith, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hH hpinch hcan hder hgrad hspat hnon
  obtain ⟨p, records, hrec⟩ :=
    (H.hasCanonicalCutoffRecords_iff_exists_isCanonicalCutoffRecordFamily p₀ δbound ρbound).mp
      hH.2.2.2.1
  have hcanq : ∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.CanonicalBefore ε C1 C2 qh τmin (H.time j.succ) :=
    fun j y t ht hR hτ' => hcan j (Fin.castSucc_lt_last j) y t ht (hqh.trans_lt hR) hτ'
  have hderq : ∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qh (H.time j.succ) :=
    fun j y t ht hR => hder j (Fin.castSucc_lt_last j) y t ht (hqh.trans_lt hR)
  have hgradq : ∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.GradientBoundBefore Cgrad qh (H.time j.succ) :=
    fun j y t ht hR => hgrad j (Fin.castSucc_lt_last j) y t ht (hqh.trans_lt hR)
  have hspatq : ∀ j : Fin H.eventCount,
      (H.toHistory.event j).incoming.SpatiallyCanonicalBefore ε C1s C2s qh (H.time j.succ) :=
    fun j y t ht hR => hspat j (Fin.castSucc_lt_last j) y t ht (hqh.trans_lt hR)
  obtain ⟨hXev, hXterm⟩ := hXp qh le_rfl (one_mul qh).ge p₀ δbound ρbound
    (hacc.trans (min_le_left _ _)) ((show Dcap ≤ Rcap by linarith).trans hrad)
    ((le_max_left _ _).trans hord) (hδb.trans (min_le_left _ _)) (hρb.trans (min_le_left _ _))
    H hH p records hrec hpinch
  have hWH := hWp p₀ δbound ρbound (hacc.trans (min_le_right _ _)) hrad
    ((le_max_right _ _).trans hord) (hδb.trans (min_le_right _ _)) (hρb.trans (min_le_right _ _))
    H hH.1 hH.2.2.2.2 p records hrec
  have key : ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (G : (H.stage k).IncomingSlab (H.time k) s),
      G.flow.base.metric (H.time k) = H.initialMetric k →
      G.CanonicalBefore ε C1 C2 qh τmin s → G.DerivativeBoundBefore Ctime qh s →
      G.GradientBoundBefore Cgrad qh s →
      H.StronglyCanonicalWhereFull_C12X k G ε ε Cx Cx qh
        (fun y t => G.flow.scalar t y * (t - H.time k) < τmin ∧
          ¬ H.CapWindowPoint records k y t Dcap θcap) →
      H.StronglyCanonicalBeforeFull_C12X k G ε ε C1h C2h qh s := by
    intro k s G hinit hcanG hderG hgradG hyoung
    have h₁ := (RetainedCoreHistory.stronglyCanonicalWhereFull_of_canonicalBefore_C12X (H := H) k G
      le_rfl hε' hcanG).mono_constants
      (le_max_left C1 (max Cs Cx)) (le_max_left C2 (max (max Cs (Cgrad : ℝ)) Cx))
    have h₂ := (hWH k s G hinit (fun j _ => hderq j) hderG hgradG ε).mono_constants
      ((le_max_left Cs Cx).trans (le_max_right C1 _))
      ((le_max_left (max Cs (Cgrad : ℝ)) Cx).trans (le_max_right C2 _))
    have h₃ := hyoung.mono_constants ((le_max_right Cs Cx).trans (le_max_right C1 _))
      ((le_max_right (max Cs (Cgrad : ℝ)) Cx).trans (le_max_right C2 _))
    refine RetainedCoreHistory.stronglyCanonicalBeforeFull_of_where_cover_C12X h₁ h₂ h₃
      fun y t => ?_
    rcases le_or_gt τmin (G.flow.scalar t y * (t - H.time k)) with hold | hyng
    · exact Or.inl hold
    · by_cases hcw : H.CapWindowPoint records k y t Dcap θcap
      · exact Or.inr (Or.inl hcw)
      · exact Or.inr (Or.inr ⟨hyng, hcw⟩)
  refine ⟨fun j _ => ?_, fun s G hG hphiG hcanG hderG hgradG hspatG hnonG => ?_⟩
  · refine key j.castSucc (H.time j.succ) (H.toHistory.event j).incoming (H.event_initial j)
      (hcanq j) (hderq j) (hgradq j) ?_
    rintro y t ht hR ⟨hyng, hcw⟩
    have hjl : H.time j.succ ≤ H.time (Fin.last H.eventCount) :=
      H.time_strictMono.monotone (Fin.le_last _)
    obtain ⟨η, hη, -, -, hwin⟩ := hXev j (fun i _ => hcanq i) (fun i _ => hderq i)
      (fun i _ => hgradq i) (fun i _ => hspatq i) t ⟨ht.1.le, ht.2⟩
      ((H.toHistory.event j).incoming.canonicalBefore_mono ht.2.le (hcanq j))
      ((H.toHistory.event j).incoming.derivativeBoundBefore_mono ht.2.le (hderq j))
      ((H.toHistory.event j).incoming.gradientBoundBefore_mono ht.2.le (hgradq j))
      ((H.toHistory.event j).incoming.spatiallyCanonicalBefore_mono ht.2.le (hspatq j))
      (H.noncollapsedBefore_mono (ht.2.le.trans hjl) hnon) (H.time j.succ - t)
      (sub_pos.mpr ht.2)
      (fun y' t' ha _ _ hts hR' => hderq j y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' => hgradq j y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' hτ' => hcanq j y' t' ⟨ha, hts⟩ hR' hτ')
    exact hwin y t ht.1 le_rfl (by linarith) ht.2 hR hyng hcw
  · have hcanG' : G.CanonicalBefore ε C1 C2 qh τmin s :=
      fun y t ht hR hτ' => hcanG y t ht (hqh.trans_lt hR) hτ'
    have hderG' : G.DerivativeBoundBefore Ctime qh s :=
      fun y t ht hR => hderG y t ht (hqh.trans_lt hR)
    have hgradG' : G.GradientBoundBefore Cgrad qh s :=
      fun y t ht hR => hgradG y t ht (hqh.trans_lt hR)
    have hspatG' : G.SpatiallyCanonicalBefore ε C1s C2s qh s :=
      fun y t ht hR => hspatG y t ht (hqh.trans_lt hR)
    refine key (Fin.last H.eventCount) s G hG.2 hcanG' hderG' hgradG' ?_
    rintro y t ht hR ⟨hyng, hcw⟩
    obtain ⟨η, hη, -, -, hwin⟩ := hXterm s G hG hphiG (fun i _ => hcanq i) (fun i _ => hderq i)
      (fun i _ => hgradq i) (fun i _ => hspatq i) hnon t ⟨ht.1.le, ht.2⟩
      (G.canonicalBefore_mono ht.2.le hcanG') (G.derivativeBoundBefore_mono ht.2.le hderG')
      (G.gradientBoundBefore_mono ht.2.le hgradG') (G.spatiallyCanonicalBefore_mono ht.2.le hspatG')
      (hnonG t ht) (s - t) (sub_pos.mpr ht.2)
      (fun y' t' ha _ _ hts hR' => hderG' y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' => hgradG' y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' hτ' => hcanG' y' t' ⟨ha, hts⟩ hR' hτ')
    exact hwin y t ht.1 le_rfl (by linarith) ht.2 hR hyng hcw

/-- Projection check: the tree theorem `strong_necks_of_cutoff_class` re-derived from the full
diagonal one (`εbar := min ε₁ εStrong_C12X`, then `mono_eps` and truncation to depth `1 / 5`). -/
theorem strongNecksOfCutoffClass_of_full_C12X (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) :
    StrongNecksOfCutoffClass P₀ g₀ := by
  intro ε₁ hε₁ hε₁'
  refine ⟨min ε₁ εStrong_C12X.{u}, lt_min hε₁ εStrong_C12X_pos, min_le_left _ _,
    fun B ε hB hε hεb => ?_⟩
  have hεε₁ : ε ≤ ε₁ := hεb.trans (min_le_left _ _)
  intro C1 C2 C1s C2s qcan τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s hqcan hτ hκ hphi
  obtain ⟨C1h, C2h, qh, δmax, ρmax, εcap, Dcap, mcap, h₁, h₂, h₃, h₄, h₅, h₆, h₇, hrest⟩ :=
    strong_necks_full_of_cutoff_class_C12X P₀ g₀ B ε hB hε (hεb.trans (min_le_right _ _)) C1 C2
      C1s C2s qcan τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s hqcan hτ hκ hphi
  refine ⟨C1h, C2h, qh, δmax, ρmax, εcap, Dcap, mcap, h₁, h₂, h₃, h₄, h₅, h₆, h₇,
    fun p₀ δbound ρbound a₁ a₂ a₃ a₄ a₅ H hH b₁ b₂ b₃ b₄ b₅ b₆ => ?_⟩
  obtain ⟨hev, hterm⟩ := hrest p₀ δbound ρbound a₁ a₂ a₃ a₄ a₅ H hH b₁ b₂ b₃ b₄ b₅ b₆
  exact ⟨(hev.mono_eps hεε₁ hε₁').toEventSlabsStronglyCanonical,
    fun s G hG c₁ c₂ c₃ c₄ c₅ c₆ =>
      ((hterm s G hG c₁ c₂ c₃ c₄ c₅ c₆).mono_eps hεε₁ hε₁').toStronglyCanonicalBefore⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
