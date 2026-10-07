import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CapWindowCapWitness

/-!
# Strongly canonical points with full (depth-one) history necks (C12X, S16 G2c)

`StronglyCanonical{At,Before,Where}` and `EventSlabsStronglyCanonical`
(`Surgery/Topology/HistoryStrongNeck`) with `HistoryStrongNeck` replaced by
`HistoryStrongNeckFull_C12X`, their projections to the tree predicates, accuracy monotonicity,
and the two non-crossing branches of `strong_necks_of_cutoff_class`: the old-point branch
(slab `CanonicalBefore`) and the cap-window branch (non-neck witness).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

/-- `StronglyCanonicalAt` with a full history neck. -/
def StronglyCanonicalAtFull_C12X (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 : ℝ) (y : (H.stage k).Carrier)
    (t : ℝ) : Prop :=
  ∃ W : SpatialCanonicalWitness (G.flow.base.metric t) ε C1 C2 y, W.capTubeHasNeckChart ε ∧
    ((∃ n, W.alternative = .neck n) → H.toHistory.HistoryStrongNeckFull_C12X k G ε₁ y t)

/-- `StronglyCanonicalBefore` with a full history neck. -/
def StronglyCanonicalBeforeFull_C12X (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan t₀ : ℝ) : Prop :=
  ∀ (y : (H.stage k).Carrier) (t : ℝ), t ∈ Ioo (H.time k) t₀ → qcan < G.flow.scalar t y →
    H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t

/-- `StronglyCanonicalWhere` with a full history neck. -/
def StronglyCanonicalWhereFull_C12X (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (ε ε₁ C1 C2 qcan : ℝ)
    (S : (H.stage k).Carrier → ℝ → Prop) : Prop :=
  ∀ y t, t ∈ Ioo (H.time k) s → qcan < G.flow.scalar t y → S y t →
    H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t

/-- `EventSlabsStronglyCanonical` with full history necks. -/
def EventSlabsStronglyCanonicalFull_C12X (ε ε₁ C1 C2 qcan : ℝ) (k : Fin (H.eventCount + 1)) :
    Prop :=
  ∀ j : Fin H.eventCount, j.castSucc < k →
    H.StronglyCanonicalBeforeFull_C12X j.castSucc (H.toHistory.event j).incoming ε ε₁ C1 C2 qcan
      (H.time j.succ)

variable {H} {k : Fin (H.eventCount + 1)} {s : ℝ} {G : (H.stage k).IncomingSlab (H.time k) s}
  {ε ε₁ C1 C2 qcan t₀ : ℝ}

theorem StronglyCanonicalAtFull_C12X.toStronglyCanonicalAt {y : (H.stage k).Carrier} {t : ℝ}
    (h : H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t) :
    H.StronglyCanonicalAt k G ε ε₁ C1 C2 y t :=
  h.imp fun _ hW => ⟨hW.1, fun hn => (hW.2 hn).toHistoryStrongNeck_C12X⟩

theorem StronglyCanonicalAtFull_C12X.mono_eps {y : (H.stage k).Carrier} {t : ℝ} {ε₂ : ℝ}
    (h : H.StronglyCanonicalAtFull_C12X k G ε ε₁ C1 C2 y t) (h₁₂ : ε₁ ≤ ε₂) (h₂ : ε₂ < 1 / 11) :
    H.StronglyCanonicalAtFull_C12X k G ε ε₂ C1 C2 y t :=
  h.imp fun _ hW => ⟨hW.1, fun hn => (hW.2 hn).mono_eps h₁₂ h₂⟩

theorem StronglyCanonicalBeforeFull_C12X.toStronglyCanonicalBefore
    (h : H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1 C2 qcan t₀) :
    H.StronglyCanonicalBefore k G ε ε₁ C1 C2 qcan t₀ :=
  fun y t ht hR => (h y t ht hR).toStronglyCanonicalAt

theorem StronglyCanonicalBeforeFull_C12X.mono_eps {ε₂ : ℝ}
    (h : H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1 C2 qcan t₀) (h₁₂ : ε₁ ≤ ε₂)
    (h₂ : ε₂ < 1 / 11) : H.StronglyCanonicalBeforeFull_C12X k G ε ε₂ C1 C2 qcan t₀ :=
  fun y t ht hR => (h y t ht hR).mono_eps h₁₂ h₂

theorem EventSlabsStronglyCanonicalFull_C12X.toEventSlabsStronglyCanonical
    (h : H.EventSlabsStronglyCanonicalFull_C12X ε ε₁ C1 C2 qcan k) :
    H.EventSlabsStronglyCanonical ε ε₁ C1 C2 qcan k :=
  fun j hj => (h j hj).toStronglyCanonicalBefore

theorem EventSlabsStronglyCanonicalFull_C12X.mono_eps {ε₂ : ℝ}
    (h : H.EventSlabsStronglyCanonicalFull_C12X ε ε₁ C1 C2 qcan k) (h₁₂ : ε₁ ≤ ε₂)
    (h₂ : ε₂ < 1 / 11) : H.EventSlabsStronglyCanonicalFull_C12X ε ε₂ C1 C2 qcan k :=
  fun j hj => (h j hj).mono_eps h₁₂ h₂

theorem stronglyCanonicalBeforeFull_of_where_cover_C12X
    {S₁ S₂ S₃ : (H.stage k).Carrier → ℝ → Prop}
    (h₁ : H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1 C2 qcan S₁)
    (h₂ : H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1 C2 qcan S₂)
    (h₃ : H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1 C2 qcan S₃)
    (hcover : ∀ y t, S₁ y t ∨ S₂ y t ∨ S₃ y t) :
    H.StronglyCanonicalBeforeFull_C12X k G ε ε₁ C1 C2 qcan s :=
  fun y t ht hR => (hcover y t).elim (h₁ y t ht hR) fun h => h.elim (h₂ y t ht hR) (h₃ y t ht hR)

/-- Old-point branch: untruncated `stronglyCanonicalWhere_of_canonicalBefore`. -/
theorem stronglyCanonicalWhereFull_of_canonicalBefore_C12X (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) {τmin : ℝ} (hε : ε ≤ ε₁) (hε₁ : ε₁ < 1 / 11)
    (hG : G.CanonicalBefore ε C1 C2 qcan τmin s) :
    H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1 C2 qcan
      fun y t => τmin ≤ G.flow.scalar t y * (t - H.time k) := by
  intro y t ht hR hτ
  obtain ⟨W, hW⟩ := hG y t ht hR hτ
  refine ⟨W.toSpatial, W.capTubeHasNeckChart_toSpatial hW, fun ⟨n, hn⟩ => ?_⟩
  change W.alternative.toSpatial = SpatialCanonicalAlternative.neck n at hn
  cases halt : W.alternative with
  | neck data =>
    exact H.toHistory.historyStrongNeckFull_of_strongNeck_C12X k G (data.strong.mono hε hε₁)
  | cap data deep =>
    rw [halt] at hn
    cases hn
  | positive whole data sec =>
    rw [halt] at hn
    cases hn
  | round whole data =>
    rw [halt] at hn
    cases hn

theorem StronglyCanonicalWhereFull_C12X.mono_constants {S : (H.stage k).Carrier → ℝ → Prop}
    {C1' C2' : ℝ} (hC1 : C1 ≤ C1') (hC2 : C2 ≤ C2')
    (h : H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1 C2 qcan S) :
    H.StronglyCanonicalWhereFull_C12X k G ε ε₁ C1' C2' qcan S := by
  intro y t ht hR hS
  obtain ⟨W, hW, hn⟩ := h y t ht hR hS
  refine ⟨W.enlargeConstants hC1 hC2, hW.enlarge_constants hC1 hC2, fun ⟨n, hn'⟩ => hn ?_⟩
  change W.alternative.monoConstant (zero_lt_one.trans_le W.one_le_comparison_constant) hC2
    W.Q_pos.le = SpatialCanonicalAlternative.neck n at hn'
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

/-- Cap-window branch: `exists_capWindow_stronglyCanonicalWhere` for the full predicate (the
witness is not a neck, so the neck clause is vacuous). -/
theorem exists_capWindow_stronglyCanonicalWhereFull_C12X (P₀ : OrientedThreeStage.{u})
    (g₀ : P₀.Metric) {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 11) :
    ∀ (Ctime Cgrad : ℝ≥0) (Dw θcap : ℝ), 0 < Dw → θcap < 1 →
    ∃ (Cs Rcap : ℝ) (mcap : ℕ), 1 ≤ Cs ∧ Dw + 1 < Rcap ∧
    ∀ qcan : ℝ, 0 < qcan →
    ∃ (δmax ρmax εcap : ℝ), 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Rcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax →
    ∀ H : RetainedCoreHistory.{u}, Nonempty (InitialIdentification P₀ g₀ H.toHistory) →
      p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
      Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
    ∀ ε₁ : ℝ, H.StronglyCanonicalWhereFull_C12X k Gk ε ε₁ Cs (max Cs (Cgrad : ℝ)) qcan
      fun y t => H.CapWindowPoint records k y t Dw θcap := by
  intro Ctime Cgrad Dw θcap hDw hθcap
  obtain ⟨Cs, Rcap, mcap, hCs, hRcap, hq⟩ :=
    exists_capWindowPoint_nonNeck_spatialCanonicalWitness P₀ g₀ hε hε' Ctime Cgrad Dw θcap hDw
      hθcap
  refine ⟨Cs, Rcap, mcap, hCs, hRcap, fun qcan hqcan => ?_⟩
  obtain ⟨δmax, ρmax, εcap, hδ, hρ, hεc, hrest⟩ := hq qcan hqcan
  refine ⟨δmax, ρmax, εcap, hδ, hρ, hεc, ?_⟩
  intro p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k s Gk hGk hderiv hcur
    hgrad ε₁ y t ht hR hcap
  obtain ⟨W, hW, hne⟩ := hrest p₀ δbound ρbound hacc hrad hord hδb hρb H hId hΛδ p records hrec k
    s Gk hGk hderiv t ht.1 ht.2 (fun y' τ hτ hR' => hcur y' τ ⟨hτ.1, hτ.2.trans ht.2⟩ hR') y hcap
    hR (hgrad y t ht hR)
  exact ⟨W, hW, fun ⟨n, hn⟩ => absurd hn (hne n)⟩

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
