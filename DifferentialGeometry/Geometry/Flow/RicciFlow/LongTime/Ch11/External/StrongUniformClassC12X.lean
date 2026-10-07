import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformCoreC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformCrossingC12X

/-!
# Strong necks of the cutoff class with uniform witness constants (C12X, S16F G4)

R-S16 D-R-S16-1: `strong_necks_full_of_cutoff_class_C12X` (S16B) outputs `C1h = max C1 (max Cs Cx)`
with the cap-window constant `Cs` chosen after `Dcap θcap`, hence after `B κ phi` and the native
initial data; along a chain this only gives `∀ n ∃ C1h,n`.  Here the cover is split four ways
(design `out/CH12X-S16-uniform-design.md` §3):

* old points (`τmin ≤ R (t - time k)`): native `CanonicalBefore`, constants `C1 C2`;
* core `CapWindowPoint … D₀ θ₀`: non-neck witness, constant `Cs₀(ε, D₀, θ₀)` (G2);
* window minus core: explicit hypothesis `hwin` (uniform `Cu`, strong necks allowed);
* young points outside the window: crossing continuation with `Cx(ε)` before `P₀ g₀` (G3).

`strong_necks_full_uniform_of_window_C12X` therefore produces
`C1* = max C1 (max Ccore Cu)`, `C2* = max C2 (max (max Ccore Cu) Cgrad)` with `Ccore` depending on
`ε D₀ θ₀` only — the same pair for every `P₀ g₀ B κ phi qcan` (only `qh δmax ρmax εcap Dcap mcap`
vary).  `hwin` is the open geometric input (Perelman II §5.4 / KL 63.1, design §6); until it is
proved this theorem is conditional and does not count as S16 supplied.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **Uniform witness constants** for the full strong-neck class theorem, conditional on the
window-minus-core input `hwin` (stated inline, an explicit hypothesis). -/
theorem strong_necks_full_uniform_of_window_C12X (ε : ℝ) (hε : 0 < ε)
    (hεS : ε ≤ εStrong_C12X.{u}) (D₀ θ₀ : ℝ) (hD₀ : 0 < D₀) (hθ₀ : θ₀ < 1) :
    ∃ Ccore : ℝ, 1 ≤ Ccore ∧ ∀ Cu : ℝ,
    (∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime Cgrad : ℝ≥0) (Dw θw : ℝ),
      0 < Dw → θw < 1 →
      ∃ (Rw : ℝ) (mw : ℕ), Dw + 1 < Rw ∧
      ∀ qcan : ℝ, 0 < qcan →
      ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
      ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
        p₀.modelAccuracy ≤ εcap → Rw ≤ p₀.modelRadius → mw ≤ p₀.modelOrder →
        δbound ≤ δmax → ρbound ≤ ρmax →
      ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
        p₀.recenterConstant * δbound ≤ 1 / 2 →
      ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
        H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
        Gk.flow.base.metric (H.time k) = H.initialMetric k →
        H.EventSlabsDerivative Ctime qcan k →
        Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
        H.StronglyCanonicalWhereFull_C12X k Gk ε ε Cu (max Cu (Cgrad : ℝ)) qcan
          fun y t => H.CapWindowPoint records k y t Dw θw ∧
            ¬ H.CapWindowPoint records k y t D₀ θ₀) →
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (B : ℝ), 0 < B →
    ∀ (C1 C2 C1s C2s qcan τmin : ℝ) (Ctime Cgrad : ℝ≥0) (κ : ℝ) (phi : ℝ → ℝ),
      1 ≤ C1 → 1 ≤ C2 → 1 ≤ C1s → 1 ≤ C2s → 0 < qcan → 0 < τmin → 0 < κ →
      Perelman.AdmissiblePinchingFunction phi →
    ∃ (qh δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      qcan ≤ qh ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
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
  obtain ⟨Rw, mw, hRw, hWw⟩ := hwin P₀ g₀ Ctime Cgrad Dcap θcap hDcap hθcap
  set qh := max qcan q₀ with hqhdef
  have hqh : qcan ≤ qh := le_max_left _ _
  obtain ⟨δX, ρX, εX, hδX, hρX, hεX, hXp⟩ := hXq qh (le_max_right _ _)
  obtain ⟨δ0, ρ0, ε0, hδ0, hρ0, hε0, h0p⟩ := hC qh (hqcan.trans_le hqh)
  obtain ⟨δW, ρW, εW, hδW, hρW, hεW, hWp⟩ := hWw qh (hqcan.trans_le hqh)
  refine ⟨qh, min δX (min δ0 δW), min ρX (min ρ0 ρW), min εX (min ε0 εW), max Rw R0,
    max mcap (max m0 mw), hqh, lt_min hδX (lt_min hδ0 hδW), lt_min hρX (lt_min hρ0 hρW),
    lt_min hεX (lt_min hε0 hεW), lt_max_of_lt_left (by linarith), ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hH hpinch hcan hder hgrad hspat hnon
  have hRw' : Rw ≤ p₀.modelRadius := (le_max_left _ _).trans hrad
  have hR0' : R0 ≤ p₀.modelRadius := (le_max_right _ _).trans hrad
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
        (fun y t => H.CapWindowPoint records k y t Dcap θcap) := by
      intro y t ht hR hcw
      by_cases hc : H.CapWindowPoint records k y t D₀ θ₀
      · exact h₂ y t ht hR hc
      · exact h₂' y t ht hR ⟨hcw, hc⟩
    refine RetainedCoreHistory.stronglyCanonicalBeforeFull_of_where_cover_C12X h₁ hwinW h₃
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
