import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformClassYoungC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowAssemblyDeepC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.RecordHypFarC12X

/-!
# Uniform Full producer with the record hypothesis threaded (C12X, S16 round 3, O-C12X-S16K G1b)

Lead ruling (S16 round 3): `Deep` is a construction-time property of the record family, so the
global form `hwinYoung_of_deep_C12X` (Deep for every record family) is no interface.  Instead the
uniform producer of S16F G6 is restated for the S16G v2 window input
`HwinYoungDeep_C12X Deep`, with the class conclusion for an explicit canonical record family that
satisfies `Deep` (the record family is no longer extracted from `InCutoffClass`).

* `strong_necks_full_uniform_of_youngWindowDeep_C12X`: the v2 uniform producer (same constants
  `C1* = max C1 (max Ccore Cu)`, `C2* = max C2 (max (max Ccore Cu) Cgrad)`).
* `HwinYoungDeep_C12X.mono_C12X`: a stronger record hypothesis weakens the window input; e.g. the
  window input for `DeepBackwardNecks_C12X θ` (S16G G5) ⇒ for `RecordHypFar_C12X θ`
  (Deep ∧ Radial, the class antecedent).

Conditional on the window input: not counted as S16 supplied.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- A stronger record hypothesis weakens the v2 window input. -/
theorem HwinYoungDeep_C12X.mono_C12X {Deep Deep' : RecordHyp_C12X.{u}}
    (hD : ∀ (H : RetainedCoreHistory.{u}) (p : CutoffParameters)
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p), Deep' H records → Deep H records)
    {ε D₀ θ₀ Cu : ℝ} (h : HwinYoungDeep_C12X Deep ε D₀ θ₀ Cu) :
    HwinYoungDeep_C12X Deep' ε D₀ θ₀ Cu := by
  intro P₀ g₀ Ctime Cgrad Dw θw τw hDw hθw
  obtain ⟨Rw, mw, hRw, h⟩ := h P₀ g₀ Ctime Cgrad Dw θw τw hDw hθw
  refine ⟨Rw, mw, hRw, fun qcan hqcan => ?_⟩
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hε, h⟩ := h qcan hqcan
  refine ⟨δmax, ρmax, εcap, hδ, hρ, hε, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec hdeep
  exact h p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec
    (hD H p records hdeep)

/-- `RecordHypFar_C12X θ` contains `DeepBackwardNecks_C12X θ` (definitionally its first part). -/
theorem deepBackwardNecks_of_recordHypFar_C12X {θ : ℝ} (H : RetainedCoreHistory.{u})
    (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
    (h : RecordHypFar_C12X θ H records) : DeepBackwardNecks_C12X θ H records :=
  h.1

/-- The S16G G5 window input (record hypothesis `DeepBackwardNecks_C12X θ`) gives the window input
for the class antecedent `RecordHypFar_C12X θ`. -/
theorem HwinYoungDeep_C12X.toRecordHypFar_C12X {θ ε D₀ θ₀ Cu : ℝ}
    (h : HwinYoungDeep_C12X (DeepBackwardNecks_C12X.{u} θ) ε D₀ θ₀ Cu) :
    HwinYoungDeep_C12X (fun H _ records => RecordHypFar_C12X.{u} θ H records) ε D₀ θ₀ Cu :=
  h.mono_C12X fun H p records hR => deepBackwardNecks_of_recordHypFar_C12X H p records hR

/-- **Uniform witness constants, record-hypothesis form (v2).**  As
`strong_necks_full_uniform_of_youngWindow_C12X`, with the window input in the S16G v2 form
`HwinYoungDeep_C12X Deep` and the class conclusion stated for an explicit canonical record family
satisfying `Deep`. -/
theorem strong_necks_full_uniform_of_youngWindowDeep_C12X (Deep : RecordHyp_C12X.{u})
    (ε : ℝ) (hε : 0 < ε)
    (hεS : ε ≤ εStrong_C12X.{u}) (D₀ θ₀ : ℝ) (hD₀ : 0 < D₀) (hθ₀ : θ₀ < 1) :
    ∃ Ccore : ℝ, 1 ≤ Ccore ∧ ∀ Cu : ℝ,
    HwinYoungDeep_C12X Deep ε D₀ θ₀ Cu →
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ), 0 < B →
    ∀ (C1 C2 C1s C2s qcan τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ) (phi : ℝ → ℝ),
      1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < κ →
      Perelman.AdmissiblePinchingFunction phi →
    ∃ (qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      qcan ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ (H : RetainedCoreHistory.{u}) (hH : H.InCutoffClass (P₀ := P₀) g₀ B p₀ δbound ρbound)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records → Deep H records →
      H.EventSlabsPinched phi →
      H.EventSlabsCanonical ε C1 C2 qcan τmin (Fin.last H.eventCount) →
      H.EventSlabsDerivative Ctime qcan (Fin.last H.eventCount) →
      H.EventSlabsGradient Cgrad qcan (Fin.last H.eventCount) →
      H.EventSlabsSpatiallyCanonical ε C1s C2s qcan (Fin.last H.eventCount) →
      H.NoncollapsedBefore κ ε (H.time (Fin.last H.eventCount)) →
      H.EventSlabsStronglyCanonicalFull_C12X ε ε (max C1 (max Ccore Cu))
        (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh (Fin.last H.eventCount) ∧
      ∀ (s : ℝ)
        (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
        (hG : H.IsContinuationSlab B (Fin.last H.eventCount) G),
        Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi →
        G.CanonicalBefore ε C1 C2 qcan τmin s → G.DerivativeBoundBefore Ctime qcan s →
        G.GradientBoundBefore Cgrad qcan s → G.SpatiallyCanonicalBefore ε C1s C2s qcan s →
        (∀ t₀ ∈ Ioo (H.time (Fin.last H.eventCount)) s,
          H.TerminalNoncollapsedBefore hH.2.1 G hG.2 κ ε t₀) →
        H.StronglyCanonicalBeforeFull_C12X (Fin.last H.eventCount) G ε ε
          (max C1 (max Ccore Cu)) (max C2 (max (max Ccore Cu) (Cgrad : ℝ))) qh s := by
  have hε' : ε < 1 / 11 := (hεS.trans_lt εStrong_C12X_lt).trans (by norm_num)
  obtain ⟨Cx, hCx, hXU⟩ := exists_uniform_crossingFull_C12X.{u} ε hε hεS
  obtain ⟨Cs₀, hCs₀, hcore⟩ :=
    RetainedCoreHistory.exists_capWindowCore_stronglyCanonicalWhereFull_uniform_C12X.{u} hε hε'
      D₀ θ₀ hD₀ hθ₀
  refine ⟨max Cs₀ Cx, le_max_of_le_left hCs₀, fun Cu hwin => ?_⟩
  intro P₀ g₀ B hB C1 C2 C1s C2s qcan τmin Ctime Cgrad κ phi hC1 hC2 hC1s hC2s hqcan hτ hκ hphi
  obtain ⟨Dcap, θcap, q₀, mcap, hDcap, hθcap, -, hXq⟩ :=
    hXU P₀ g₀ B hB C1 C2 τmin Ctime Cgrad hC1 hC2 hτ C1s C2s 1 hC1s hC2s le_rfl κ phi τmin hκ
      hphi hτ
  obtain ⟨R0, m0, hR0, hC⟩ := hcore P₀ g₀ Ctime Cgrad
  obtain ⟨Rw, mw, hRw, hWw⟩ := hwin P₀ g₀ Ctime Cgrad Dcap θcap τmin hDcap hθcap
  set qh := max qcan q₀ with hqhdef
  have hqh : qcan ≤ qh := le_max_left _ _
  obtain ⟨δX, ρX, εX, hδX, hρX, hεX, hXp⟩ := hXq qh (le_max_right _ _)
  obtain ⟨δ0, ρ0, ε0, hδ0, hρ0, hε0, h0p⟩ := hC qh (hqcan.trans_le hqh)
  obtain ⟨δW, ρW, εW, hδW, hρW, hεW, hWp⟩ := hWw qh (hqcan.trans_le hqh)
  refine ⟨qh, min δX (min δ0 δW), min ρX (min ρ0 ρW), min εX (min ε0 εW), max Rw R0,
    max mcap (max m0 mw), hqh, lt_min hδX (lt_min hδ0 hδW), lt_min hρX (lt_min hρ0 hρW),
    lt_min hεX (lt_min hε0 hεW), lt_max_of_lt_left (by linarith), ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hH p records hrec hdeep hpinch hcan hder hgrad
    hspat hnon
  have hRw' : Rw ≤ p₀.modelRadius := (le_max_left _ _).trans hrad
  have hR0' : R0 ≤ p₀.modelRadius := (le_max_right _ _).trans hrad
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
    (hacc.trans (min_le_left _ _)) ((show Dcap ≤ Rw by linarith).trans hRw')
    ((le_max_left _ _).trans hord) (hδb.trans (min_le_left _ _)) (hρb.trans (min_le_left _ _))
    H hH p records hrec hpinch
  have h0H := h0p p₀ δbound ρbound (hacc.trans ((min_le_right _ _).trans (min_le_left _ _))) hR0'
    (((le_max_left _ _).trans (le_max_right _ _)).trans hord)
    (hδb.trans ((min_le_right _ _).trans (min_le_left _ _)))
    (hρb.trans ((min_le_right _ _).trans (min_le_left _ _))) H hH.1 hH.2.2.2.2 p records hrec
  have hWH := hWp p₀ δbound ρbound (hacc.trans ((min_le_right _ _).trans (min_le_right _ _))) hRw'
    (((le_max_right _ _).trans (le_max_right _ _)).trans hord)
    (hδb.trans ((min_le_right _ _).trans (min_le_right _ _)))
    (hρb.trans ((min_le_right _ _).trans (min_le_right _ _))) H hH.1 hH.2.2.2.2 p records hrec
    hdeep
  have hA1 : max Cs₀ Cx ≤ max C1 (max (max Cs₀ Cx) Cu) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hA2 : max (max Cs₀ Cx) Cu ≤ max C2 (max (max (max Cs₀ Cx) Cu) (Cgrad : ℝ)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hG2 : (Cgrad : ℝ) ≤ max C2 (max (max (max Cs₀ Cx) Cu) (Cgrad : ℝ)) :=
    (le_max_right _ _).trans (le_max_right _ _)
  have key : ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (G : (H.stage k).IncomingSlab (H.time k) s),
      G.flow.base.metric (H.time k) = H.initialMetric k →
      G.CanonicalBefore ε C1 C2 qh τmin s → G.DerivativeBoundBefore Ctime qh s →
      G.GradientBoundBefore Cgrad qh s →
      H.StronglyCanonicalWhereFull_C12X k G ε ε Cx Cx qh
        (fun y t => G.flow.scalar t y * (t - H.time k) < τmin ∧
          ¬ H.CapWindowPoint records k y t Dcap θcap) →
      H.StronglyCanonicalBeforeFull_C12X k G ε ε (max C1 (max (max Cs₀ Cx) Cu))
        (max C2 (max (max (max Cs₀ Cx) Cu) (Cgrad : ℝ))) qh s := by
    intro k s G hinit hcanG hderG hgradG hyoung
    have h₁ := (RetainedCoreHistory.stronglyCanonicalWhereFull_of_canonicalBefore_C12X (H := H) k G
      le_rfl hε' hcanG).mono_constants (le_max_left C1 (max (max Cs₀ Cx) Cu))
      (le_max_left C2 (max (max (max Cs₀ Cx) Cu) (Cgrad : ℝ)))
    have h₂ := (h0H k s G hinit (fun j _ => hderq j) hderG hgradG ε).mono_constants
      ((le_max_left Cs₀ Cx).trans hA1)
      (max_le ((le_max_left Cs₀ Cx).trans ((le_max_left _ Cu).trans hA2)) hG2)
    have h₂' := (hWH k s G hinit (fun j _ => hderq j) hderG hgradG).mono_constants
      ((le_max_right (max Cs₀ Cx) Cu).trans (le_max_right C1 _))
      (max_le ((le_max_right (max Cs₀ Cx) Cu).trans hA2) hG2)
    have h₃ := hyoung.mono_constants ((le_max_right Cs₀ Cx).trans hA1)
      ((le_max_right Cs₀ Cx).trans ((le_max_left _ Cu).trans hA2))
    have hwinW : H.StronglyCanonicalWhereFull_C12X k G ε ε (max C1 (max (max Cs₀ Cx) Cu))
        (max C2 (max (max (max Cs₀ Cx) Cu) (Cgrad : ℝ))) qh
        (fun y t => G.flow.scalar t y * (t - H.time k) < τmin ∧
          H.CapWindowPoint records k y t Dcap θcap) := by
      intro y t ht hR ⟨hyng, hcw⟩
      by_cases hc : H.CapWindowPoint records k y t D₀ θ₀
      · exact h₂ y t ht hR hc
      · exact h₂' y t ht hR ⟨hcw, hc, hyng⟩
    refine RetainedCoreHistory.stronglyCanonicalBeforeFull_of_where_cover_C12X h₁ hwinW h₃
      fun y t => ?_
    rcases le_or_gt τmin (G.flow.scalar t y * (t - H.time k)) with hold | hyng
    · exact Or.inl hold
    · by_cases hcw : H.CapWindowPoint records k y t Dcap θcap
      · exact Or.inr (Or.inl ⟨hyng, hcw⟩)
      · exact Or.inr (Or.inr ⟨hyng, hcw⟩)
  refine ⟨fun j _ => ?_, fun s G hG hphiG hcanG hderG hgradG hspatG hnonG => ?_⟩
  · refine key j.castSucc (H.time j.succ) (H.toHistory.event j).incoming (H.event_initial j)
      (hcanq j) (hderq j) (hgradq j) ?_
    rintro y t ht hR ⟨hyng, hcw⟩
    have hjl : H.time j.succ ≤ H.time (Fin.last H.eventCount) :=
      H.time_strictMono.monotone (Fin.le_last _)
    obtain ⟨η, hη, -, -, hwin'⟩ := hXev j (fun i _ => hcanq i) (fun i _ => hderq i)
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
    exact hwin' y t ht.1 le_rfl (by linarith) ht.2 hR hyng hcw
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
    obtain ⟨η, hη, -, -, hwin'⟩ := hXterm s G hG hphiG (fun i _ => hcanq i)
      (fun i _ => hderq i) (fun i _ => hgradq i) (fun i _ => hspatq i) hnon t ⟨ht.1.le, ht.2⟩
      (G.canonicalBefore_mono ht.2.le hcanG') (G.derivativeBoundBefore_mono ht.2.le hderG')
      (G.gradientBoundBefore_mono ht.2.le hgradG')
      (G.spatiallyCanonicalBefore_mono ht.2.le hspatG')
      (hnonG t ht) (s - t) (sub_pos.mpr ht.2)
      (fun y' t' ha _ _ hts hR' => hderG' y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' => hgradG' y' t' ⟨ha, hts⟩ hR')
      (fun y' t' ha _ _ hts hR' hτ' => hcanG' y' t' ⟨ha, hts⟩ hR' hτ')
    exact hwin' y t ht.1 le_rfl (by linarith) ht.2 hR hyng hcw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
