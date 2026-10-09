import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongUniformClassYoungC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckParabolicTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckPullbackTransport
import DifferentialGeometry.Geometry.Metric.PullbackScaling

/-!
# `hwin`: shared interface (C12X, S16G G1 "Common")

Shared definitions for the proof of the window input of
`strong_necks_full_uniform_of_youngWindow_C12X` (S16F G6), design
`docs/geometrization/chapter8/out/CH12X-S16-HWIN-design.md` §4:

* `HwinYoung_C12X ε D₀ θ₀ Cu`: the G6 window input, verbatim, as a named `Prop`;
* `RetainedCoreHistory.WindowDatum_C12X`: an unpacked `CapWindowPoint` (one `j A b x`), with
  `capWindowPoint_iff_nonempty_windowDatum_C12X` and the core dichotomy `late_or_far`
  (late: `θ₀ / scale < t − time j.succ`; far-early: `D₀ + 1 ≤ ‖x‖`);
* `ObservedHistory.SurvivorNeckPackage_C12X … first hle`: the survivor-flow body of
  `HistoryStrongNeckFull_C12X` with fixed start `first` (everything but the neck; nonempty by
  `nonempty_survivorNeckPackage_C12X`), and its two producers:
  `full_of_strongNeck` (a neck of the package flow) and `full_of_model` (a neck of a model
  solution `S` on any manifold `N` with `S τ = Ξ^*(q · gflow (t₀ + τ / q))`, exact depth one:
  `time first ≤ t − R⁻¹`, no extra margin).
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped NNReal Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

/-- The window input of `strong_necks_full_uniform_of_youngWindow_C12X` (S16F G6), verbatim. -/
def HwinYoung_C12X (ε D₀ θ₀ Cu : ℝ) : Prop :=
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
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
    ∀ (k : Fin (H.eventCount + 1)) (s : ℝ) (Gk : (H.stage k).IncomingSlab (H.time k) s),
      Gk.flow.base.metric (H.time k) = H.initialMetric k →
      H.EventSlabsDerivative Ctime qcan k →
      Gk.DerivativeBoundBefore Ctime qcan s → Gk.GradientBoundBefore Cgrad qcan s →
      H.StronglyCanonicalWhereFull_C12X k Gk ε ε Cu (max Cu (Cgrad : ℝ)) qcan
        fun y t => H.CapWindowPoint records k y t Dw θw ∧
          ¬ H.CapWindowPoint records k y t D₀ θ₀ ∧ Gk.flow.scalar t y * (t - H.time k) < τw

namespace RetainedCoreHistory

/-- An unpacked `CapWindowPoint records k y t Dw θw`: the event `j`, the backward trace, the
retained boundary `b` and the standard window coordinate `x` of the point. -/
structure WindowDatum_C12X (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (k : Fin (H.eventCount + 1)) (y : (H.stage k).Carrier) (t Dw θw : ℝ) where
  j : Fin H.eventCount
  hl : j.succ ≤ k
  A : BackwardPointTrace H.toHistory j.succ k hl y
  b : (H.toHistory.event j).RetainedBoundaryIndex
  x : standardCapWindow p.modelRadius
  hx : A.point j.succ le_rfl hl = ((records j).static b).window x
  hnorm : ‖x.val‖ < Dw + 1
  htime : t - H.time j.succ ≤ θw * (((records j).static b).neck.scale)⁻¹

variable {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
  {records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p}
  {k : Fin (H.eventCount + 1)} {y : (H.stage k).Carrier} {t Dw θw : ℝ}

/-- The static neck scale of the cap the window point comes from. -/
def WindowDatum_C12X.scale (d : H.WindowDatum_C12X records k y t Dw θw) : ℝ :=
  ((records d.j).static d.b).neck.scale

theorem WindowDatum_C12X.scale_pos (d : H.WindowDatum_C12X records k y t Dw θw) :
    0 < d.scale :=
  ((records d.j).static d.b).neck.scale_pos

theorem capWindowPoint_iff_nonempty_windowDatum_C12X :
    H.CapWindowPoint records k y t Dw θw ↔ Nonempty (H.WindowDatum_C12X records k y t Dw θw) :=
  ⟨fun ⟨j, hl, A, b, x, hx, hn, ht⟩ => ⟨⟨j, hl, A, b, x, hx, hn, ht⟩⟩,
    fun ⟨d⟩ => ⟨d.j, d.hl, d.A, d.b, d.x, d.hx, d.hnorm, d.htime⟩⟩

/-- Core dichotomy: a window point outside the core `CapWindowPoint D₀ θ₀` is, for the same
datum, either late (`T > θ₀`) or far-early (`‖x‖ ≥ D₀ + 1`, `T ≤ θ₀`), where
`T = scale (t − time j.succ)`. -/
theorem WindowDatum_C12X.late_or_far (d : H.WindowDatum_C12X records k y t Dw θw) {D₀ θ₀ : ℝ}
    (hnc : ¬ H.CapWindowPoint records k y t D₀ θ₀) :
    θ₀ * d.scale⁻¹ < t - H.time d.j.succ ∨
      (D₀ + 1 ≤ ‖d.x.val‖ ∧ t - H.time d.j.succ ≤ θ₀ * d.scale⁻¹) := by
  by_cases hT : θ₀ * d.scale⁻¹ < t - H.time d.j.succ
  · exact Or.inl hT
  · refine Or.inr ⟨?_, not_lt.mp hT⟩
    by_contra hx
    exact hnc ⟨d.j, d.hl, d.A, d.b, d.x, d.hx, not_le.mp hx, not_lt.mp hT⟩

/-- Standard time of the window point: `scale · (t − time j.succ)`. -/
theorem WindowDatum_C12X.late_iff {d : H.WindowDatum_C12X records k y t Dw θw} {θ₀ : ℝ} :
    θ₀ * d.scale⁻¹ < t - H.time d.j.succ ↔ θ₀ < d.scale * (t - H.time d.j.succ) := by
  rw [← div_eq_mul_inv, div_lt_iff₀ d.scale_pos, mul_comm]

end RetainedCoreHistory

namespace ObservedHistory

/-- `time first < s` for a survivor package start `first ≤ k`. -/
theorem time_lt_of_le_C12X (H : ObservedHistory.{u}) {k first : Fin (H.eventCount + 1)} {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (hle : first ≤ k) : H.time first < s :=
  (H.time_strictMono.monotone hle).trans_lt G.lt

/-- The survivor-flow body of `HistoryStrongNeckFull_C12X` with fixed start `first ≤ k`: a
solution on the backward survivor domain `first … k` over `[time first, s)` agreeing with every
survivor slab and with `G`. -/
structure SurvivorNeckPackage_C12X (H : ObservedHistory.{u}) (k : Fin (H.eventCount + 1)) {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (first : Fin (H.eventCount + 1))
    (hle : first ≤ k) where
  gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorDomain first k hle)
  slab_eq : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ k),
    ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
      gflow τ = H.backwardSurvivorSlabMetric first k hle j hf hl τ
  cur_eq : ∀ τ ∈ Ico (H.time k) s,
    gflow τ = (G.flow.base.metric τ).restrictOpen (H.backwardSurvivorDomain first k hle)
  sol : IsSolutionOn ({ base := { metric := gflow } } :
    SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
      (RealTimeInterval.closedOpen (H.time first) s (H.time_lt_of_le_C12X G hle)))

variable {H : ObservedHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s} {first : Fin (H.eventCount + 1)} {hle : first ≤ k}

/-- Every start `first ≤ k` carries a survivor package (from
`exists_backwardSurvivor_incomingSlab_flow`). -/
theorem nonempty_survivorNeckPackage_C12X (H : ObservedHistory.{u})
    {k : Fin (H.eventCount + 1)} {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ k)
    (hinit : G.flow.base.metric (H.time k) = H.initialMetric k) :
    Nonempty (H.SurvivorNeckPackage_C12X k G first hle) := by
  obtain ⟨gflow, hslab, hcur, hsol⟩ :=
    H.exists_backwardSurvivor_incomingSlab_flow first k hle G hinit
  exact ⟨⟨gflow, hslab, hcur, hsol⟩⟩

/-- The package flow as a solution on `[time first, s)`. -/
def SurvivorNeckPackage_C12X.flow (P : H.SurvivorNeckPackage_C12X k G first hle) :
    SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first k hle)
      (RealTimeInterval.closedOpen (H.time first) s (H.time_lt_of_le_C12X G hle)) :=
  { base := { metric := P.gflow } }

/-- A neck of the package flow, with exact depth one, is a full history neck. -/
theorem SurvivorNeckPackage_C12X.full_of_strongNeck (P : H.SurvivorNeckPackage_C12X k G first hle)
    {eps t : ℝ} {y : (H.stage k).Carrier} (z : H.backwardSurvivorDomain first k hle)
    (hz : z.val = y) (htk : H.time k ≤ t) (hdepth : H.time first ≤ t - (G.flow.scalar t y)⁻¹)
    (nk : StrongNeck P.flow eps z t) : H.HistoryStrongNeckFull_C12X k G eps y t :=
  ⟨first, hle, H.time_lt_of_le_C12X G hle, P.gflow, htk, hdepth, P.slab_eq, P.cur_eq, P.sol, z,
    hz, ⟨nk⟩⟩

/-- On the current slab the package scalar is the slab scalar. -/
theorem SurvivorNeckPackage_C12X.scalar_eq (P : H.SurvivorNeckPackage_C12X k G first hle) {t : ℝ}
    (ht : t ∈ Ico (H.time k) s) (z : H.backwardSurvivorDomain first k hle) :
    P.flow.scalar t z = G.flow.scalar t z.val := by
  change metricScalarAt (P.gflow t) z = metricScalarAt (G.flow.base.metric t) z.val
  rw [P.cur_eq t ht, metricScalarAt_restrictOpen]

end ObservedHistory

namespace C12X_S16G

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

omit [T2Space M] [SigmaCompactSpace M] in
private theorem rescaledMetric_congr_scale_C12X {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (t : ℝ) {Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (h : Q = Q') : rescaledMetric S t Q hQ = rescaledMetric S t Q' hQ' := by
  subst h
  rfl

/-- Cross-universe copy of the private `MetricComparisonOn.mapIsometryLift`
(`CN/SpatialCanonicalWitnessUniverseTransport`). -/
def mapIsometryLift_C12X {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [CompleteSpace E'] {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} {Z : Type*} [TopologicalSpace Z] [ChartedSpace H' Z]
    [IsManifold J ∞ Z] [T2Space Z] [SigmaCompactSpace Z]
    {k : ℝ → SmoothRiemannianMetric J Z} {g₁ : ℝ → SmoothRiemannianMetric I3 N}
    {g₂ : ℝ → SmoothRiemannianMetric I3 M} {F : Z → N} {V : Set Z} {times : Set ℝ}
    {order : ℕ} {eps : ℝ} (C : MetricComparisonOn k g₁ F V times order eps)
    (e : PartialDiffeomorph I3 I3 N M ∞)
    (hiso : ∀ s, ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      (g₂ s).inner (e z) (mfderiv I3 I3 e z v) (mfderiv I3 I3 e z w) = (g₁ s).inner z v w)
    (hF : ∀ y ∈ V, MDifferentiableAt J I3 F y) (hV : ∀ y ∈ V, F y ∈ e.source) :
    MetricComparisonOn k g₂ (fun y => e (F y)) V times order eps where
  pullback := C.pullback
  pullback_eq s y hy v := by
    have hc : mfderiv J I3 (fun y => e (F y)) y =
        (mfderiv I3 I3 e (F y)).comp (mfderiv J I3 F y) :=
      mfderiv_comp y (e.mdifferentiableAt (by decide) (hV y hy)) (hF y hy)
    rw [C.pullback_eq s y hy v, hc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply, hiso s (F y) (hV y hy)]
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ := C.jet_succ
  equivalence := C.equivalence
  close := C.close

/-- `StrongNeck.ofLocalPullback` with the source manifold in an arbitrary universe. -/
def strongNeck_ofLocalPullback_C12X {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {ι : N → M} (hι : IsLocalDiffeomorph I3 I3 ∞ ι) (hinj : Function.Injective ι)
    {eps t : ℝ} {x : N} (nk : StrongNeck (S.localPullback ι hι) eps x t) :
    StrongNeck S eps (ι x) t := by
  have hex : ∃ e : PartialDiffeomorph I3 I3 N M ∞, e.source = univ ∧ (e : N → M) = ι := by
    obtain ⟨e, hs, -, hf'⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hι.isLocalDiffeomorphOn univ) isOpen_univ ⟨x, trivial⟩ hinj.injOn
    exact ⟨e, hs, hf'⟩
  let e := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hmem : ∀ y : N, y ∈ e.source := fun y => hspec.1 ▸ mem_univ y
  have he : ((e : PartialDiffeomorph I3 I3 N M ∞) : N → M) = ι := hspec.2
  have hQ : S.scalar t (ι x) = (S.localPullback ι hι).scalar t x := by
    change metricScalarAt (S.base.metric t) (ι x) =
      metricScalarAt (localPullMetric (S.base.metric t) ι hι) x
    rw [metricScalarAt_localPull]
  have hQpos : 0 < S.scalar t (ι x) := hQ ▸ nk.Q_pos
  have hiso : ∀ s, ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      (rescaledMetric S t (S.scalar t (ι x)) hQpos s).inner (e z) (mfderiv I3 I3 e z v)
          (mfderiv I3 I3 e z w) =
        (rescaledMetric (S.localPullback ι hι) t ((S.localPullback ι hι).scalar t x)
          nk.Q_pos s).inner z v w := by
    intro s z _ v w
    rw [rescaledMetric_congr_scale_C12X S t hQpos nk.Q_pos hQ]
    simp only [rescaledMetric, scaleMetric_inner, SolutionOn.localPullback_metric,
      localPullMetric_inner]
    rw [he]
  have hF : ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, MDifferentiableAt IC I3 nk.map y := fun y hy =>
    nk.map.mdifferentiableAt (by decide) (nk.domain hy)
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQpos
      cylinder := nk.cylinder
      map := nk.map.trans e
      center := nk.center
      center_eq := ?_
      domain := ?_
      time_domain := by rw [hQ]; exact nk.time_domain
      comparison := mapIsometryLift_C12X nk.comparison e hiso hF (fun y _ => hmem _) }
  · rw [PartialDiffeomorph.trans_apply, nk.center_eq]
    exact congrFun he x
  · intro y hy
    rw [PartialDiffeomorph.trans_source]
    exact ⟨nk.domain hy, hmem _⟩

end C12X_S16G

namespace ObservedHistory

variable {H : ObservedHistory.{u}} {k : Fin (H.eventCount + 1)} {s : ℝ}
  {G : (H.stage k).IncomingSlab (H.time k) s} {first : Fin (H.eventCount + 1)} {hle : first ≤ k}

/-- **Model producer.** A strong neck of a model solution `S` on `N` whose metrics are the
`Ξ`-pullbacks of the parabolically rescaled package flow, `S τ = Ξ^*(q · gflow (t₀ + τ / q))`,
gives a full history neck at `(Ξ z, t₀ + T / q)`, with exact depth one. -/
theorem SurvivorNeckPackage_C12X.full_of_model (P : H.SurvivorNeckPackage_C12X k G first hle)
    {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
    [T2Space N] (Ξ : N → H.backwardSurvivorDomain first k hle) (hΞ : IsLocalDiffeomorph I3 I3 ∞ Ξ)
    (hinj : Function.Injective Ξ) {q t₀ : ℝ} (hq : 0 < q) (ht₀ : t₀ ∈ Ico (H.time first) s)
    {DS : RealTimeInterval} (S : SolutionOn (I := I3) (M := N) DS)
    (hS : ∀ τ, S.base.metric τ = localPullMetric (scaleMetric q hq (P.gflow (t₀ + τ / q))) Ξ hΞ)
    {eps T : ℝ} {z : N} (nk : StrongNeck S eps z T) {y : (H.stage k).Carrier}
    (hyz : (Ξ z).val = y) (htk : H.time k ≤ t₀ + T / q) (hts : t₀ + T / q < s)
    (hdepth : H.time first ≤ t₀ + T / q - (G.flow.scalar (t₀ + T / q) y)⁻¹) :
    H.HistoryStrongNeckFull_C12X k G eps y (t₀ + T / q) := by
  have : SigmaCompactSpace (H.backwardSurvivorDomain first k hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first k hle).isOpen)
  set t := t₀ + T / q with ht
  have ht₀D : t₀ ∈ (RealTimeInterval.closedOpen (H.time first) s
      (H.time_lt_of_le_C12X G hle)).carrier := ht₀
  have hscal : P.flow.scalar t (Ξ z) = G.flow.scalar t y := by
    rw [P.scalar_eq ⟨htk, hts⟩, hyz]
  have hSscal : S.scalar T z = q⁻¹ * G.flow.scalar t y := by
    change metricScalarAt (S.base.metric T) z = _
    rw [hS T, metricScalarAt_localPull, metricScalarAt_scaleMetric, ← ht, ← hscal]
    rfl
  have hRpos : 0 < G.flow.scalar t y := by
    have h := nk.Q_pos
    rw [hSscal] at h
    exact (mul_pos_iff_of_pos_left (inv_pos.mpr hq)).mp h
  have hD : Icc (T - (S.scalar T z)⁻¹) T ⊆
      (parabolicInterval (RealTimeInterval.closedOpen (H.time first) s
        (H.time_lt_of_le_C12X G hle)) t₀ q ht₀D).carrier := by
    intro σ hσ
    change t₀ + σ / q ∈ Ico (H.time first) s
    rw [hSscal, mul_inv, inv_inv] at hσ
    have h1 : (T - q * (G.flow.scalar t y)⁻¹) / q ≤ σ / q :=
      div_le_div_of_nonneg_right hσ.1 hq.le
    have h2 : σ / q ≤ T / q := div_le_div_of_nonneg_right hσ.2 hq.le
    rw [sub_div, mul_div_cancel_left₀ _ hq.ne'] at h1
    constructor <;> linarith
  let nk₁ : StrongNeck (parabolicSolution (P.flow.localPullback Ξ hΞ) t₀ q hq ht₀D) eps z T :=
    nk.ofMetricEq (fun τ => by
      rw [parabolicSolution_metric, hS τ, localPullMetric_scaleMetric]
      rfl) hD
  let nk₂ := (nk₁.ofParabolic t₀ q hq ht₀D T).castTime (show parabolicTime t₀ q T = t from rfl)
  let nk₃ : StrongNeck P.flow eps (Ξ z) t := C12X_S16G.strongNeck_ofLocalPullback_C12X hΞ hinj nk₂
  exact P.full_of_strongNeck (Ξ z) hyz htk hdepth nk₃

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
