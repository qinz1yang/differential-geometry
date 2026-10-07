import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowBirthC12X

/-!
# `hwin` assembly: late (Birth) + far-early (Splice) ⇒ window input (C12X, S16G G4)

Design `docs/geometrization/chapter8/out/CH12X-S16-HWIN-design.md` §4 group G5.  Window points
outside the core are late or far-early (`WindowDatum_C12X.late_or_far`); the late ones are paid by
`exists_birth_C12X` (θB, CB depend on ε only).  The far-early branch is the Splice lane's target,
stated here as `HwinFar_C12X Deep ε θ₀ D₀ CS`; per lead ruling (R1, route (β)) it carries an extra
per-history record hypothesis `Deep` (the depth-2 backward necks `IncomingBackwardNeckDeep`, to be
instantiated by the Splice lane).  Hence the window input is assembled in the **v2** form
`HwinYoungDeep_C12X Deep` = the S16F G6 binder with `Deep H records →` inserted after the record
family hypothesis [FROZEN v2]; the S16F G6 binder itself (`HwinYoung_C12X`) is unchanged and
follows from v2 whenever `Deep` holds for every record family (`hwinYoung_of_deep_C12X`).

* `exists_hwinYoungDeep_of_far_C12X`: if for every `θ₀ ∈ (0,1)` some `D₀ CS` satisfy the far branch,
  then `∃ D₀ θ₀ Cu, HwinYoungDeep_C12X Deep ε D₀ θ₀ Cu` (θ₀ := θB, Cu := max CB CS).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- A per-history hypothesis on the record family (lane B: depth-2 backward necks). -/
abbrev RecordHyp_C12X : Type (u + 1) :=
  ∀ (H : RetainedCoreHistory.{u}) {p : CutoffParameters},
    (∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p) → Prop

/-- [FROZEN v2] The S16F G6 window input with the extra record hypothesis `Deep`. -/
def HwinYoungDeep_C12X (Deep : RecordHyp_C12X.{u}) (ε D₀ θ₀ Cu : ℝ) : Prop :=
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime Cgrad : ℝ≥0) (Dw θw τw : ℝ),
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
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records → Deep H records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
      Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
      H.StronglyCanonicalWhereFull_C12X k Gk ε ε Cu (max Cu (Cgrad : ℝ)) qcan
        fun y t => H.CapWindowPoint records k y t Dw θw ∧
          ¬ H.CapWindowPoint records k y t D₀ θ₀ ∧ Gk.flow.scalar t y * (t - H.time k) < τw

/-- The far-early branch (Splice lane target): window points with `D₀ + 1 ≤ ‖x‖` and standard
time `≤ θ₀` get a witness of constants `(CS, max CS Cgrad)` whose neck clause is full. -/
def HwinFar_C12X (Deep : RecordHyp_C12X.{u}) (ε θ₀ D₀ CS : ℝ) : Prop :=
  ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric) (Ctime Cgrad : ℝ≥0) (Dw θw : ℝ),
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
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records → Deep H records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
      Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
    ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) s → qcan < Gk.flow.scalar t y →
    ∀ d : H.WindowDatum_C12X records k y t Dw θw, D₀ + 1 ≤ ‖d.x.val‖ →
      t - H.time d.j.succ ≤ θ₀ * d.scale⁻¹ →
      H.StronglyCanonicalAtFull_C12X k Gk ε ε CS (max CS (Cgrad : ℝ)) y t

/-- The G6 binder follows from v2 when `Deep` holds for every record family. -/
theorem hwinYoung_of_deep_C12X {Deep : RecordHyp_C12X.{u}}
    (hall : ∀ (H : RetainedCoreHistory.{u}) (p : CutoffParameters)
      (records : ∀ i, GeometricCutoffRecord H.toHistory i p), Deep H records)
    {ε D₀ θ₀ Cu : ℝ} (h : HwinYoungDeep_C12X Deep ε D₀ θ₀ Cu) : HwinYoung_C12X.{u} ε D₀ θ₀ Cu := by
  intro P₀ g₀ Ctime Cgrad Dw θw τw hDw hθw
  obtain ⟨Rw, mw, hRw, h⟩ := h P₀ g₀ Ctime Cgrad Dw θw τw hDw hθw
  refine ⟨Rw, mw, hRw, fun qcan hqcan => ?_⟩
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hε, h⟩ := h qcan hqcan
  refine ⟨δmax, ρmax, εcap, hδ, hρ, hε, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec
  exact h p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec (hall H p records)

namespace RetainedCoreHistory

variable {H : RetainedCoreHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s} {ε ε₁ C1 C2 : ℝ} {y : (H.stage k).Carrier} {t : ℝ}

/-- Constant monotonicity of the pointwise predicate (same witness, enlarged constants). -/
theorem StronglyCanonicalAtFull_C12X.mono_constants_C12X {C1' C2' : ℝ}
    (h : H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t) (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2') :
    H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1' C2' y t := by
  obtain ⟨W, hW, hn⟩ := h
  refine ⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2, fun ⟨n, hn'⟩ => hn ?_⟩
  change W.alternative.monoConstant (zero_lt_one.trans_le W.one_le_comparison_constant) hC2
    W.Q_pos.le = Perelman.CanonicalNeighborhood.FiniteHorn.SpatialCanonicalAlternative.neck n
    at hn'
  cases halt : W.alternative with
  | neck data => exact ⟨data, rfl⟩
  | cap data deep =>
    rw [halt] at hn'
    cases hn'
  | positive whole data sec =>
    rw [halt] at hn'
    cases hn'
  | round whole data =>
    rw [halt] at hn'
    cases hn'

end RetainedCoreHistory

/-- **Assembly.**  With `θ₀ := θB(ε)` from the late branch, any far-early branch with constants
`D₀ CS` yields the v2 window input with `Cu := max CB CS`. -/
theorem exists_birth_far_assembly_C12X {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∃ θB : ℝ, 0 < θB ∧ θB < 1 ∧ ∃ CB : ℝ, 1 ≤ CB ∧
    ∀ (Deep : RecordHyp_C12X.{u}) (D₀ CS : ℝ), HwinFar_C12X Deep ε θB D₀ CS →
      HwinYoungDeep_C12X Deep ε D₀ θB (max CB CS) := by
  obtain ⟨θB, CB, hθB, hθB1, hCB, hbirth⟩ := RetainedCoreHistory.exists_birth_C12X.{u} hε hε'
  refine ⟨θB, hθB, hθB1, CB, hCB, fun Deep D₀ CS hfar => ?_⟩
  intro P₀ g₀ Ctime Cgrad Dw θw τw hDw hθw
  obtain ⟨R1, m1, hR1, hB⟩ := hbirth P₀ g₀ Ctime Cgrad Dw θw hDw hθw
  obtain ⟨R2, m2, -, hF⟩ := hfar P₀ g₀ Ctime Cgrad Dw θw hDw hθw
  refine ⟨max R1 R2, max m1 m2, lt_max_of_lt_left hR1, fun qcan hqcan => ?_⟩
  obtain ⟨δ1, ρ1, ε1, hδ1, hρ1, hε1, hB⟩ := hB qcan hqcan
  obtain ⟨δ2, ρ2, ε2, hδ2, hρ2, hε2, hF⟩ := hF qcan hqcan
  refine ⟨min δ1 δ2, min ρ1 ρ2, min ε1 ε2, lt_min hδ1 hδ2, lt_min hρ1 hρ2, lt_min hε1 hε2, ?_⟩
  rintro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec hdeep k s Gk hGk hderiv
    hderG hgrad y t ht hR ⟨hwin, hnc, -⟩
  obtain ⟨d⟩ := RetainedCoreHistory.capWindowPoint_iff_nonempty_windowDatum_C12X.mp hwin
  have hC2 : max CB (Cgrad : ℝ) ≤ max (max CB CS) (Cgrad : ℝ) :=
    max_le_max (le_max_left _ _) le_rfl
  have hC2' : max CS (Cgrad : ℝ) ≤ max (max CB CS) (Cgrad : ℝ) :=
    max_le_max (le_max_right _ _) le_rfl
  rcases d.late_or_far hnc with hlate | ⟨hfarx, hT⟩
  · exact (hB p₀ δbound ρbound (hacc.trans (min_le_left _ _))
      ((le_max_left _ _).trans hrad) ((le_max_left _ _).trans hord)
      (hδb.trans (min_le_left _ _)) (hρb.trans (min_le_left _ _)) H hId hΛδ p records hrec
      k s Gk hGk hderiv hderG y t ht hR d (RetainedCoreHistory.WindowDatum_C12X.late_iff.mp
        hlate)).mono_constants_C12X (le_max_left _ _) hC2
  · exact (hF p₀ δbound ρbound (hacc.trans (min_le_right _ _))
      ((le_max_right _ _).trans hrad) ((le_max_right _ _).trans hord)
      (hδb.trans (min_le_right _ _)) (hρb.trans (min_le_right _ _)) H hId hΛδ p records hrec
      hdeep k s Gk hGk hderiv hderG hgrad y t ht hR d hfarx hT).mono_constants_C12X
      (le_max_right _ _) hC2'

/-- **hwin existence (v2), conditional on the far-early branch.** -/
theorem exists_hwinYoungDeep_of_far_C12X {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11)
    (Deep : RecordHyp_C12X.{u})
    (hfar : ∀ θ₀ : ℝ, 0 < θ₀ → θ₀ < 1 →
      ∃ D₀ CS : ℝ, 0 < D₀ ∧ 1 ≤ CS ∧ HwinFar_C12X Deep ε θ₀ D₀ CS) :
    ∃ D₀ θ₀ Cu : ℝ, 0 < D₀ ∧ 0 < θ₀ ∧ θ₀ < 1 ∧ 1 ≤ Cu ∧ HwinYoungDeep_C12X Deep ε D₀ θ₀ Cu := by
  obtain ⟨θB, hθB, hθB1, CB, hCB, hasm⟩ := exists_birth_far_assembly_C12X.{u} hε hε'
  obtain ⟨D₀, CS, hD₀, hCS, hF⟩ := hfar θB hθB hθB1
  exact ⟨D₀, θB, max CB CS, hD₀, hθB, hθB1, le_max_of_le_left hCB, hasm Deep D₀ CS hF⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
