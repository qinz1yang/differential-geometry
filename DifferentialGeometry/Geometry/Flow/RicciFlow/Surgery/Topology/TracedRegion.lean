import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace BackwardPointTrace

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}

def isRmBoundedBy (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
    (H.activeStage_mono hat) p) (K : ℝ) : Prop :=
  (∀ (s : Icc (0 : ℝ) H.horizon) (has : a ≤ s) (hst : s ≤ t),
    normSq0S (H.stageMetric (H.activeStage s) s)
      (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst)) 4
      (metricRm04At (H.stageMetric (H.activeStage s) s)
        (A.point (H.activeStage s) (H.activeStage_mono has) (H.activeStage_mono hst))) ≤
      K ^ 2) ∧
  ∀ (i : Fin H.eventCount) (hf : H.activeStage a ≤ i.castSucc) (hl : i.succ ≤ H.activeStage t),
    let x : (H.event i).incoming.terminalRegularOpen :=
      ⟨A.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
        (A.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩
    normSq0S (H.event i).terminal.metric x 4 (metricRm04At (H.event i).terminal.metric x) ≤
      K ^ 2

private theorem pow_four_mul_le_one_iff {r N : ℝ} (hr : 0 < r) :
    r ^ 4 * N ≤ 1 ↔ N ≤ ((r ^ 2)⁻¹) ^ 2 := by
  have h4 : 0 < r ^ 4 := by positivity
  have hK : ((r ^ 2)⁻¹) ^ 2 = 1 / r ^ 4 := by
    rw [inv_pow, ← pow_mul, one_div]
  rw [hK, le_div_iff₀ h4, mul_comm]

theorem isRmControlled_iff_isRmBoundedBy
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {r : ℝ} (hr : 0 < r) :
    A.isRmControlled (hat := hat) r ↔ A.isRmBoundedBy (hat := hat) (r ^ 2)⁻¹ := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun s has hst => (pow_four_mul_le_one_iff hr).1 (h1 s has hst),
      fun i hf hl => (pow_four_mul_le_one_iff hr).1 (h2 i hf hl)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun s has hst => (pow_four_mul_le_one_iff hr).2 (h1 s has hst),
      fun i hf hl => (pow_four_mul_le_one_iff hr).2 (h2 i hf hl)⟩

theorem isRmBoundedBy.mono
    {A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p}
    {K K' : ℝ} (hA : A.isRmBoundedBy (hat := hat) K) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    A.isRmBoundedBy (hat := hat) K' := by
  have hpow := pow_le_pow_left₀ hK hKK' 2
  exact ⟨fun s has hst => (hA.1 s has hst).trans hpow, fun i hf hl => (hA.2 i hf hl).trans hpow⟩

theorem isRmBoundedBy.restrictFirst
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {K : ℝ} (hA : A.isRmBoundedBy (hat := hat) K)
    {b : Icc (0 : ℝ) H.horizon} (hab : a ≤ b) (hbt : b ≤ t) :
    (A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt)).isRmBoundedBy
      (hat := hbt) K :=
  ⟨fun s hbs hst => hA.1 s (hab.trans hbs) hst,
    fun i hf hl => hA.2 i ((H.activeStage_mono hab).trans hf) hl⟩

end BackwardPointTrace

namespace ObservedHistory

variable (H : ObservedHistory.{u})

def isTracedRegion (t : Icc (0 : ℝ) H.horizon) (p : (H.stageAt t).Carrier) (ρ τ K : ℝ) :
    Prop :=
  0 < ρ ∧ 0 < τ ∧ ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), (a : ℝ) = (t : ℝ) - τ ∧
    ∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      ∃ A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
        A.isRmBoundedBy (hat := hat) K

variable {H}

theorem isTracedRegion.radius_pos {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) : 0 < ρ :=
  h.1

theorem isTracedRegion.depth_pos {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) : 0 < τ :=
  h.2.1

theorem isTracedRegion.depth_le_time {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) : τ ≤ (t : ℝ) := by
  obtain ⟨_, _, a, _, heq, _⟩ := h
  have := a.property.1
  rw [heq] at this
  linarith

theorem isParabolicallyRmControlledBall_iff_isTracedRegion (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) (r : ℝ) :
    H.isParabolicallyRmControlledBall t p r ↔ H.isTracedRegion t p r (r ^ 2) (r ^ 2)⁻¹ := by
  constructor
  · rintro ⟨hr, a, hat, ha, htr⟩
    refine ⟨hr, by positivity, a, hat, ha, fun x hx => ?_⟩
    obtain ⟨A, hA⟩ := htr x hx
    exact ⟨A, (A.isRmControlled_iff_isRmBoundedBy hr).1 hA⟩
  · rintro ⟨hr, -, a, hat, ha, htr⟩
    refine ⟨hr, a, hat, ha, fun x hx => ?_⟩
    obtain ⟨A, hA⟩ := htr x hx
    exact ⟨A, (A.isRmControlled_iff_isRmBoundedBy hr).2 hA⟩

theorem isTracedRegion.mono {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K ρ' τ' K' : ℝ} (h : H.isTracedRegion t p ρ τ K) (hρ' : 0 < ρ') (hρρ' : ρ' ≤ ρ)
    (hτ' : 0 < τ') (hττ' : τ' ≤ τ) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    H.isTracedRegion t p ρ' τ' K' := by
  obtain ⟨_, _, a, hat, heq, htrace⟩ := h
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - τ', by have := a.property.1; rw [heq] at this; linarith,
      (sub_le_self _ hτ'.le).trans t.property.2⟩
  have hab : a ≤ b := by change (a : ℝ) ≤ (t : ℝ) - τ'; rw [heq]; linarith
  have hbt : b ≤ t := show (t : ℝ) - τ' ≤ t from sub_le_self _ hτ'.le
  refine ⟨hρ', hτ', b, hbt, rfl, fun x hx => ?_⟩
  obtain ⟨A, hA⟩ := htrace x (riemannianBallOf_mono _ _ hρρ' hx)
  exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt),
    (hA.restrictFirst A hab hbt).mono hK hKK'⟩

theorem isTracedRegion.mono_radius {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K ρ' : ℝ} (h : H.isTracedRegion t p ρ τ K) (hρ' : 0 < ρ') (hρρ' : ρ' ≤ ρ) :
    H.isTracedRegion t p ρ' τ K := by
  obtain ⟨hρ, hτ, a, hat, heq, htrace⟩ := h
  exact ⟨hρ', hτ, a, hat, heq, fun x hx => htrace x (riemannianBallOf_mono _ _ hρρ' hx)⟩

theorem isTracedRegion.mono_depth {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K τ' : ℝ} (h : H.isTracedRegion t p ρ τ K) (hτ' : 0 < τ') (hττ' : τ' ≤ τ) :
    H.isTracedRegion t p ρ τ' K := by
  obtain ⟨hρ, _, a, hat, heq, htrace⟩ := h
  let b : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - τ', by have := a.property.1; rw [heq] at this; linarith,
      (sub_le_self _ hτ'.le).trans t.property.2⟩
  have hab : a ≤ b := by change (a : ℝ) ≤ (t : ℝ) - τ'; rw [heq]; linarith
  have hbt : b ≤ t := show (t : ℝ) - τ' ≤ t from sub_le_self _ hτ'.le
  refine ⟨hρ, hτ', b, hbt, rfl, fun x hx => ?_⟩
  obtain ⟨A, hA⟩ := htrace x hx
  exact ⟨A.restrictFirst (H.activeStage_mono hab) (H.activeStage_mono hbt),
    hA.restrictFirst A hab hbt⟩

theorem isTracedRegion.mono_bound {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K K' : ℝ} (h : H.isTracedRegion t p ρ τ K) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    H.isTracedRegion t p ρ τ K' := by
  obtain ⟨hρ, hτ, a, hat, heq, htrace⟩ := h
  refine ⟨hρ, hτ, a, hat, heq, fun x hx => ?_⟩
  obtain ⟨A, hA⟩ := htrace x hx
  exact ⟨A, hA.mono hK hKK'⟩

theorem isTracedRegion.normSq_le {t : Icc (0 : ℝ) H.horizon} {p : (H.stageAt t).Carrier}
    {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) (x : (H.stageAt t).Carrier)
    (hx : x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ) :
    normSq0S (H.stageMetric (H.activeStage t) t) x 4
      (metricRm04At (H.stageMetric (H.activeStage t) t) x) ≤ K ^ 2 := by
  obtain ⟨_, _, a, hat, _, htrace⟩ := h
  obtain ⟨A, hA⟩ := htrace x hx
  have hbound := hA.1 t hat le_rfl
  have he : A.point (H.activeStage t) (H.activeStage_mono hat) (H.activeStage_mono le_rfl) = x :=
    A.endpoint_eq
  rw [he] at hbound
  exact hbound

end ObservedHistory

namespace ObservedHistory

open TopologicalSpace in
private theorem exists_common_flow_of_isTracedRegion_of_time_gt
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (ht : H.time (H.activeStage t) < t.val) (p : (H.stageAt t).Carrier) {ρ τ K : ℝ}
    (h : H.isTracedRegion t p ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) =
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
            (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) := by
  classical
  obtain ⟨hρ, -, a, hat, ha, htraces⟩ := h
  let U : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat
  let G := (H.closedPrefixAt t ht).restrictIncoming le_rfl (H.closedPrefixAt t ht).lt le_rfl
  let L := (H.closedPrefixAt t ht).endpointTerminalLimitMetric (H.stageAt t)
  have hG (v : ℝ) : G.flow.base.metric v = H.stageMetric last v :=
    H.closedPrefixAt_metric t ht v
  have hinit : G.flow.base.metric (H.time last) = H.initialMetric last :=
    H.closedPrefixAt_initial t ht
  have hsurv (x : U) : x.val ∈ H.backwardSurvivorDomain first last hle :=
    ⟨(htraces x.val x.property).choose⟩
  let Ψ₀ : U → H.backwardSurvivorDomain first last hle := fun x => ⟨x.val, hsurv x⟩
  have hΨ₀ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ₀ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  have hregular (x : U) : Ψ₀ x ∈ H.backwardSurvivorIncomingDomain first last hle G := by
    change x.val ∈ G.terminalRegularRegion
    rw [(H.closedPrefixAt t ht).terminalRegularRegion_eq_univ]
    exact mem_univ _
  let Ψ : U → H.backwardSurvivorIncomingDomain first last hle G :=
    fun x => ⟨Ψ₀ x, hregular x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hregular (hΨ₀ x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) ∘ Ψ
  have hf (j : H.StageInterval first last) :
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (isLocalDiffeomorph_comp
        (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1
          j.property.2)
        (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G)))
      hΨ
  have hflast (x : U) : f ⟨last, hle, le_rfl⟩ x = x.val :=
    H.backwardSurvivorMap_last first last hle (Ψ₀ x)
  obtain ⟨gflow, hslabs, hlast, _, hsol⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  let S₀ : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) t.val
        ((H.time_strictMono.monotone hle).trans ht.le)) := { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorIncomingDomain first last hle G).isOpen)
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t.val hat)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) le_rfl)
    (Ioo_subset_Ioo (H.activeStage_time_le a) le_rfl)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t.val)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    rcases lt_or_eq_of_le hv.2 with hvt | rfl
    · rw [H.metric_eq_stage_pullback_of_backwardSurvivorIncoming first last hle t.val G L gflow
        (fun i hi hl v hv => hslabs i hi hl v (Ico_subset_Icc_self hv))
        (fun v hv => hlast v (Ico_subset_Icc_self hv)) (fun v _ => hG v)
        j.val j.property.1 j.property.2 hjv hvt]
      exact localPullMetric_comp (H.stageMetric j.val v)
        (H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Subtype.val) Ψ
        (isLocalDiffeomorph_comp
          (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1
            j.property.2)
          (isLocalDiffeomorph_subtype_val (H.backwardSurvivorIncomingDomain first last hle G)))
        hΨ (hf j)
    · have hj : j = ⟨last, hle, le_rfl⟩ :=
        Subtype.ext ((H.mem_stageDomain_iff t j.val).mp hjv).symm
      subst j
      rw [hlast _ ⟨ht.le, le_rfl⟩, ObservedHistory.backwardSurvivorIncomingMetric]
      have hend : L.extendedMetric t.val =
          (H.stageMetric last t.val).restrictOpen G.terminalRegularOpen :=
        H.closedPrefixAt_endpointTerminalLimitMetric_extendedMetric t ht le_rfl
      rw [hend, ← localPullMetric_subtype_val]
      let k := H.backwardSurvivorIncomingMap first last hle G
      have hk := H.backwardSurvivorIncomingMap_isLocalDiffeomorph first last hle G
      have hv := isLocalDiffeomorph_subtype_val (I := ThreeModel) G.terminalRegularOpen
      have hc := isLocalDiffeomorph_comp hv (isLocalDiffeomorph_comp hk hΨ)
      rw [localPullMetric_comp _ k Ψ hk hΨ (isLocalDiffeomorph_comp hk hΨ),
        localPullMetric_comp _ Subtype.val (k ∘ Ψ) hv (isLocalDiffeomorph_comp hk hΨ) hc]
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [localPullMetric_inner, localPullMetric_inner]
      have hfend : f ⟨last, hle, le_rfl⟩ = Subtype.val ∘ (k ∘ Ψ) := by
        funext y
        exact H.backwardSurvivorMap_last first last hle (Ψ y).val
      exact congrArg (fun F : U → (H.stage last).Carrier =>
        (H.stageMetric last t.val).inner (F x)
          (mfderiv ThreeModel ThreeModel F x v) (mfderiv ThreeModel ThreeModel F x w)) hfend.symm
  refine ⟨a, hat, ha, U, rfl, f, hf, ?_, ?_, hflast, S, hS, hmetric, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : H.backwardSurvivorDomain first last hle => z.val) hxy))
  · intro i hi hl x
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ψ₀ x)
  · intro v hv x
    let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval first last :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    change normSq0S (S.base.metric v) x 4 (metricRm04At (S.base.metric v) x) ≤ K ^ 2
    rw [hmetric j v hv (H.activeStage_mem v'), normSq0S_metricRm04At_localPullMetric]
    obtain ⟨A, hA⟩ := htraces x.val x.property
    have hpoint : f j x = A.point j.val j.property.1 j.property.2 :=
      H.backwardSurvivorMap_eq_point first last hle j.val j.property.1 j.property.2 (Ψ₀ x) A
    rw [hpoint]
    exact hA.1 v' hav hvt

open TopologicalSpace in
theorem exists_common_flow_of_isTracedRegion
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) =
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
            (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) := by
  classical
  rcases lt_or_eq_of_le (H.activeStage_time_le t) with ht | ht
  · exact H.exists_common_flow_of_isTracedRegion_of_time_gt t ht p h
  obtain ⟨hρ, hτ, a, hat, ha, htraces⟩ := h
  have hatlt : a.val < t.val := by rw [ha]; linarith
  let first := H.activeStage a
  let last := H.activeStage t
  have hle : first ≤ last := H.activeStage_mono hat
  have hlt : first < last := lt_of_le_of_ne hle (by
    intro he
    have hleft := H.activeStage_time_le a
    change H.time first ≤ a.val at hleft
    rw [he, ht] at hleft
    exact (not_le_of_gt hatlt) hleft)
  let U : Opens (H.stageAt t).Carrier :=
    ⟨riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ,
      isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist _ p) continuous_const⟩
  have hsurv (x : U) : x.val ∈ H.backwardSurvivorDomain first last hle :=
    ⟨(htraces x.val x.property).choose⟩
  let Ψ : U → H.backwardSurvivorDomain first last hle := fun x => ⟨x.val, hsurv x⟩
  have hΨ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ψ := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict hsurv (isLocalDiffeomorph_subtype_val U x)
  let f (j : H.StageInterval first last) : U → (H.stage j.val).Carrier :=
    H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2 ∘ Ψ
  have hf (j : H.StageInterval first last) :
      IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j) :=
    isLocalDiffeomorph_comp
      (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j.val j.property.1
        j.property.2) hΨ
  have hflast (x : U) : f ⟨last, hle, le_rfl⟩ x = x.val :=
    H.backwardSurvivorMap_last first last hle (Ψ x)
  obtain ⟨gflow, hslabs, hstages, _, hsol⟩ :=
    H.exists_backwardSurvivor_isSolutionOn first last hlt
  let S₀ : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first last hle)
      (RealTimeInterval.closed (H.time first) (H.time last) (H.time_strictMono hlt).le) :=
    { base := { metric := gflow } }
  let : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
    isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen ThreeModel
        (H.backwardSurvivorDomain first last hle).isOpen)
  let S := (S₀.localPullback Ψ hΨ).timeRestrict (RealTimeInterval.closed a.val t.val hat)
  have hS : IsSolutionOn S := isSolutionOn_timeRestrict (hsol.localPullback Ψ hΨ)
    (Icc_subset_Icc (H.activeStage_time_le a) ht.ge)
    (Ioo_subset_Ioo (H.activeStage_time_le a) ht.ge)
  have hmetric (j : H.StageInterval first last) (v : ℝ) (hv : v ∈ Icc a.val t.val)
      (hjv : v ∈ H.stageDomain j.val) :
      S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j) := by
    change localPullMetric (gflow v) Ψ hΨ = _
    let q := H.backwardSurvivorMap first last hle j.val j.property.1 j.property.2
    have hq := H.backwardSurvivorMap_isLocalDiffeomorph first last hle
      j.val j.property.1 j.property.2
    by_cases hj : j.val = last
    · have hvlast : v = H.time last :=
        le_antisymm (hv.2.trans ht.ge) (hj ▸ H.time_le_of_mem_stageDomain hjv)
      have hvj : v = H.time j.val := hvlast.trans (congrArg H.time hj).symm
      rw [hvj, hstages j.val j.property.1 j.property.2]
      rw [ObservedHistory.backwardSurvivorInitialMetric, ← H.stageMetric_initial]
      exact localPullMetric_comp _ q Ψ hq hΨ (hf j)
    · have hjlt : j.val < last := lt_of_le_of_ne j.property.2 hj
      rcases j with ⟨j, hjfirst, hjlast⟩
      cases j using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last last)) hjlt)
      | cast i =>
        have hil : i.succ ≤ last := hjlt
        have htt : v ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
          simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using hjv
        rw [hslabs i hjfirst hil v (Ico_subset_Icc_self htt),
          ObservedHistory.backwardSurvivorSlabMetric,
          (H.event i).terminal.extendedMetric_before htt.2]
        have hinner :
            localPullMetric (((H.event i).incoming.flow.base.metric v).restrictOpen
              (H.event i).incoming.terminalRegularOpen)
              (H.backwardSurvivorTerminalMap first last hle i hjfirst hil)
              (H.backwardSurvivorTerminalMap_isLocalDiffeomorph first last hle i hjfirst hil) =
            localPullMetric ((H.event i).incoming.flow.base.metric v) q hq := by
          rw [← localPullMetric_subtype_val]
          exact localPullMetric_comp _ _ _ _ _ hq
        rw [hinner]
        simpa only [ObservedHistory.stageMetric, Fin.lastCases_castSucc] using
          (localPullMetric_comp ((H.event i).incoming.flow.base.metric v) q Ψ hq hΨ
            (hf ⟨i.castSucc, hjfirst, hjlast⟩))
  refine ⟨a, hat, ha, U, rfl, f, hf, ?_, ?_, hflast, S, hS, hmetric, ?_⟩
  · intro j
    exact (H.backwardSurvivorMap_injective first last hle j.val j.property.1 j.property.2).comp
      (fun x y hxy => Subtype.ext
        (congrArg (fun z : H.backwardSurvivorDomain first last hle => z.val) hxy))
  · intro i hi hl x
    exact H.backwardSurvivorMap_crossing first last hle i hi hl (Ψ x)
  · intro v hv x
    let v' : Icc (0 : ℝ) H.horizon := ⟨v, a.property.1.trans hv.1, hv.2.trans t.property.2⟩
    have hav : a ≤ v' := hv.1
    have hvt : v' ≤ t := hv.2
    let j : H.StageInterval first last :=
      ⟨H.activeStage v', H.activeStage_mono hav, H.activeStage_mono hvt⟩
    change normSq0S (S.base.metric v) x 4 (metricRm04At (S.base.metric v) x) ≤ K ^ 2
    rw [hmetric j v hv (H.activeStage_mem v'), normSq0S_metricRm04At_localPullMetric]
    obtain ⟨A, hA⟩ := htraces x.val x.property
    have hpoint : f j x = A.point j.val j.property.1 j.property.2 :=
      H.backwardSurvivorMap_eq_point first last hle j.val j.property.1 j.property.2 (Ψ x) A
    rw [hpoint]
    exact hA.1 v' hav hvt

end ObservedHistory

namespace ObservedHistory

open TopologicalSpace in
theorem exists_common_flow_with_compact_neighborhood_of_isTracedRegion
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (p : (H.stageAt t).Carrier) {ρ τ K : ℝ} (h : H.isTracedRegion t p ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stageAt t).Carrier,
        (U : Set (H.stageAt t).Carrier) =
          riemannianBallOf (H.stageMetric (H.activeStage t) t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → U →
            (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ H.activeStage t), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) ∧
              (∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain (H.activeStage t) →
                S.base.metric v = (H.stageMetric (H.activeStage t) v).restrictOpen U) ∧
              ∃ (pU : U) (C : Set U), pU.val = p ∧
                Subtype.val '' C =
                  riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2) ∧
                IsCompact C ∧ pU ∈ interior C ∧
                ∀ x ∈ frontier C,
                  ENNReal.ofReal (ρ / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := by
  classical
  have hρ : 0 < ρ := h.1
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm⟩ :=
    H.exists_common_flow_of_isTracedRegion t p h
  have hcurrent : ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain (H.activeStage t) →
      S.base.metric v = (H.stageMetric (H.activeStage t) v).restrictOpen U := by
    intro v hv hvd
    have h := hmetric ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ v hv hvd
    have heq : f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ = Subtype.val :=
      funext hlast
    simpa only [heq, localPullMetric_subtype_val] using h
  have hterminal : S.base.metric t = (H.stageMetric (H.activeStage t) t).restrictOpen U :=
    hcurrent t ⟨hat, le_rfl⟩ (H.activeStage_mem t)
  have hpU : p ∈ U := by
    change p ∈ (U : Set (H.stageAt t).Carrier)
    rw [hU]
    change riemannianEDistOf (H.stageMetric (H.activeStage t) t) p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  let pU : U := ⟨p, hpU⟩
  let C : Set U := Subtype.val ⁻¹'
    riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2)
  have hclosed :
      IsClosed (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2)) :=
    Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _
  have hsubset : riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2) ⊆
      range (Subtype.val : U → (H.stageAt t).Carrier) := by
    rw [Subtype.range_coe, hU]
    intro x hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith))
  have hC : IsCompact C :=
    U.isOpenEmbedding'.isEmbedding.isInducing.isCompact_preimage' hclosed.isCompact hsubset
  have himage : Subtype.val '' C =
      riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2) :=
    image_preimage_eq_of_subset hsubset
  have hpinterior : pU ∈ interior C := by
    have h := Geometry.Metric.mem_interior_riemannianClosedBallOf
      (H.stageMetric (H.activeStage t) t) p (by linarith : 0 < ρ / 2)
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_interior_of_isOpenEmbedding
        U.isOpenEmbedding' C] at h
    obtain ⟨x, hx, hxp⟩ := h
    exact (show x = pU from Subtype.ext hxp) ▸ hx
  refine ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm,
    hcurrent, pU, C, rfl, himage, hC, hpinterior, ?_⟩
  intro x hx
  have hfrontier : x.val ∈ frontier
      (riemannianClosedBallOf (H.stageMetric (H.activeStage t) t) p (ρ / 2)) := by
    rw [← himage,
      ← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
        U.isOpenEmbedding' hC]
    exact ⟨x, hx, rfl⟩
  have hdist := Geometry.Metric.riemannianEDistOf_eq_of_mem_frontier_riemannianClosedBallOf
    (H.stageMetric (H.activeStage t) t) p hfrontier
  rw [hterminal, ← hdist]
  exact riemannianEDistOf_le_restrictOpen (H.stageMetric (H.activeStage t) t) U pU x

open TopologicalSpace in
theorem exists_stage_common_flow_with_compact_neighborhood_of_isTracedRegion
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (k : Fin (H.eventCount + 1))
    (hk : H.activeStage t = k) (p : (H.stage k).Carrier) (q : (H.stageAt t).Carrier)
    (hpq : HEq q p) {ρ τ K : ℝ} (h : H.isTracedRegion t q ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stage k).Carrier,
        (U : Set (H.stage k).Carrier) = riemannianBallOf (H.stageMetric k t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) k) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ k), ∀ x : U,
              (H.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨k, hk ▸ H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) k,
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) ∧
              (∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain k →
                S.base.metric v = (H.stageMetric k v).restrictOpen U) ∧
              ∃ (pU : U) (C : Set U), pU.val = p ∧
                Subtype.val '' C = riemannianClosedBallOf (H.stageMetric k t) p (ρ / 2) ∧
                IsCompact C ∧ pU ∈ interior C ∧
                ∀ x ∈ frontier C,
                  ENNReal.ofReal (ρ / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := by
  subst hk
  obtain rfl := eq_of_heq hpq
  exact H.exists_common_flow_with_compact_neighborhood_of_isTracedRegion t q h

private theorem time_lt_succ_of_activeStage_eq_castSucc' (H : ObservedHistory.{u})
    (v : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) (hi : H.activeStage v = i.castSucc) :
    (v : ℝ) < H.time i.succ := by
  have hval : (H.activeStage v).val < H.eventCount := by
    rw [hi]
    exact i.isLt
  have h := H.activeStage_before_next v hval
  have he : (⟨(H.activeStage v).val + 1, Nat.succ_lt_succ hval⟩ :
      Fin (H.eventCount + 1)) = i.succ := by
    ext
    simp [hi]
  rw [he] at h
  exact h

theorem mem_stageDomain_castSucc_of_activeStage_eq (H : ObservedHistory.{u})
    (t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount) (hi : H.activeStage t = i.castSucc)
    {v : ℝ} (hv : H.time i.castSucc ≤ v) (hvt : v ≤ t) :
    v ∈ H.stageDomain i.castSucc := by
  simp only [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
  exact ⟨hv, hvt.trans_lt (time_lt_succ_of_activeStage_eq_castSucc' H t i hi)⟩

open TopologicalSpace in
theorem exists_event_common_flow_with_compact_neighborhood_of_isTracedRegion
    (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon) (i : Fin H.eventCount)
    (hi : H.activeStage t = i.castSucc) (p : (H.stage i.castSucc).Carrier)
    (q : (H.stageAt t).Carrier) (hpq : HEq q p) {ρ τ K : ℝ} (h : H.isTracedRegion t q ρ τ K) :
    ∃ (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), a.val = t.val - τ ∧
      ∃ U : Opens (H.stage i.castSucc).Carrier,
        (U : Set (H.stage i.castSucc).Carrier) =
          riemannianBallOf ((H.event i).incoming.flow.base.metric t) p ρ ∧
        ∃ f : (j : H.StageInterval (H.activeStage a) i.castSucc) → U →
            (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i' : Fin H.eventCount) (hi' : H.activeStage a ≤ i'.castSucc)
                (hl : i'.succ ≤ i.castSucc), ∀ x : U,
              (H.event i').RegularCrossing
                (f ⟨i'.castSucc, hi', i'.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i'.succ, hi'.trans i'.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨i.castSucc, hi ▸ H.activeStage_mono hat, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val t.val hat),
              IsSolutionOn S ∧
              (∀ j : H.StageInterval (H.activeStage a) i.castSucc,
                ∀ v ∈ Icc a.val t.val, v ∈ H.stageDomain j.val →
                  S.base.metric v = localPullMetric (H.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val t.val, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) ∧
              (∀ v ∈ Icc a.val t.val, H.time i.castSucc ≤ v →
                S.base.metric v = ((H.event i).incoming.flow.base.metric v).restrictOpen U) ∧
              ∃ (pU : U) (C : Set U), pU.val = p ∧
                Subtype.val '' C =
                  riemannianClosedBallOf ((H.event i).incoming.flow.base.metric t) p (ρ / 2) ∧
                IsCompact C ∧ pU ∈ interior C ∧
                ∀ x ∈ frontier C,
                  ENNReal.ofReal (ρ / 2) ≤ riemannianEDistOf (S.base.metric t) pU x := by
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, hcur, pU, C,
      hpU, himage, hC, hpC, hsep⟩ :=
    H.exists_stage_common_flow_with_compact_neighborhood_of_isTracedRegion t i.castSucc hi p q hpq h
  rw [ObservedHistory.stageMetric_castSucc_apply] at hU himage
  refine ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, ?_, pU, C, hpU,
    himage, hC, hpC, hsep⟩
  intro v hv hvi
  rw [hcur v hv (H.mem_stageDomain_castSucc_of_activeStage_eq t i hi hvi hv.2),
    ObservedHistory.stageMetric_castSucc_apply]

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem activeStage_extendHorizon_eq_last {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (t : Icc (0 : ℝ) (H.extendHorizon T hT S hS).toHistory.horizon)
    (ht : H.time (Fin.last H.eventCount) ≤ t) :
    (H.extendHorizon T hT S hS).toHistory.activeStage t = Fin.last H.eventCount :=
  le_antisymm (Fin.le_last _) ((H.extendHorizon T hT S hS).toHistory.le_activeStage t _ ht)

theorem stageMetric_extendHorizon_last {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    (hlt : H.time (Fin.last H.eventCount) < T) (v : ℝ) :
    (H.extendHorizon T hT S hS).toHistory.stageMetric (Fin.last H.eventCount) v =
      S.flow.base.metric v :=
  ObservedHistory.stageMetric_last_of_lt (H := (H.extendHorizon T hT S hS).toHistory)
    (h := hlt) v

def isTerminalTracedRegion (hend : H.time (Fin.last H.eventCount) = H.horizon) {s : ℝ}
    (G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s)
    (hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount))
    {T : ℝ} (hT : H.time (Fin.last H.eventCount) < T) (hTs : T < s)
    (p : (H.stage (Fin.last H.eventCount)).Carrier) (ρ τ K : ℝ) : Prop :=
  (H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.isTracedRegion
    ⟨T, (H.toHistory.time_nonneg _).trans hT.le, le_rfl⟩
    (cast (congrArg
      (fun k => ((H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG).toHistory.stage
        k).Carrier)
      (H.activeStage_extendHorizon_eq_last (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
        ⟨T, (H.toHistory.time_nonneg _).trans hT.le, le_rfl⟩ hT.le).symm) p) ρ τ K

variable {H} {hend : H.time (Fin.last H.eventCount) = H.horizon} {s : ℝ}
  {G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s}
  {hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount)}
  {T : ℝ} {hT : H.time (Fin.last H.eventCount) < T} {hTs : T < s}
  {p : (H.stage (Fin.last H.eventCount)).Carrier}

theorem isTerminalTracedRegion.radius_pos {ρ τ K : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) : 0 < ρ :=
  ObservedHistory.isTracedRegion.radius_pos h

theorem isTerminalTracedRegion.depth_pos {ρ τ K : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) : 0 < τ :=
  ObservedHistory.isTracedRegion.depth_pos h

theorem isTerminalTracedRegion.depth_le_time {ρ τ K : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) : τ ≤ T :=
  ObservedHistory.isTracedRegion.depth_le_time h

theorem isTerminalTracedRegion.mono {ρ τ K ρ' τ' K' : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) (hρ' : 0 < ρ') (hρρ' : ρ' ≤ ρ)
    (hτ' : 0 < τ') (hττ' : τ' ≤ τ) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    H.isTerminalTracedRegion hend G hG hT hTs p ρ' τ' K' :=
  ObservedHistory.isTracedRegion.mono h hρ' hρρ' hτ' hττ' hK hKK'

theorem isTerminalTracedRegion.mono_radius {ρ τ K ρ' : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) (hρ' : 0 < ρ') (hρρ' : ρ' ≤ ρ) :
    H.isTerminalTracedRegion hend G hG hT hTs p ρ' τ K :=
  ObservedHistory.isTracedRegion.mono_radius h hρ' hρρ'

theorem isTerminalTracedRegion.mono_depth {ρ τ K τ' : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) (hτ' : 0 < τ') (hττ' : τ' ≤ τ) :
    H.isTerminalTracedRegion hend G hG hT hTs p ρ τ' K :=
  ObservedHistory.isTracedRegion.mono_depth h hτ' hττ'

theorem isTerminalTracedRegion.mono_bound {ρ τ K K' : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) (hK : 0 ≤ K) (hKK' : K ≤ K') :
    H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K' :=
  ObservedHistory.isTracedRegion.mono_bound h hK hKK'

open TopologicalSpace in
theorem exists_common_flow_with_compact_neighborhood_of_isTerminalTracedRegion {ρ τ K : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K) :
    let H' := H.extendHorizon T (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG
    let t : Icc (0 : ℝ) H'.toHistory.horizon :=
      ⟨T, (H.toHistory.time_nonneg _).trans hT.le, le_rfl⟩
    ∃ (a : Icc (0 : ℝ) H'.toHistory.horizon) (hat : a ≤ t), a.val = T - τ ∧
      ∃ U : Opens (H.stage (Fin.last H.eventCount)).Carrier,
        (U : Set (H.stage (Fin.last H.eventCount)).Carrier) =
          riemannianBallOf (G.flow.base.metric T) p ρ ∧
        ∃ f : (j : H'.toHistory.StageInterval (H'.toHistory.activeStage a)
            (Fin.last H.eventCount)) → U → (H.stage j.val).Carrier,
          ∃ hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j),
            (∀ j, Function.Injective (f j)) ∧
            (∀ (i : Fin H.eventCount) (hi : H'.toHistory.activeStage a ≤ i.castSucc)
                (hl : i.succ ≤ Fin.last H.eventCount), ∀ x : U,
              (H.toHistory.event i).RegularCrossing
                (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
                (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x)) ∧
            (∀ x : U, f ⟨Fin.last H.eventCount, Fin.le_last _, le_rfl⟩ x = x.val) ∧
            ∃ S : SolutionOn (I := ThreeModel) (M := U)
                (RealTimeInterval.closed a.val T hat),
              IsSolutionOn S ∧
              (∀ j : H'.toHistory.StageInterval (H'.toHistory.activeStage a)
                  (Fin.last H.eventCount),
                ∀ v ∈ Icc a.val T, v ∈ H'.toHistory.stageDomain j.val →
                  S.base.metric v =
                    localPullMetric (H'.toHistory.stageMetric j.val v) (f j) (hf j)) ∧
              (∀ v ∈ Icc a.val T, ∀ x : U,
                normSq0S (S.base.metric v) x 4 (S.base.rm04 v x) ≤ K ^ 2) ∧
              (∀ v ∈ Icc a.val T, H.time (Fin.last H.eventCount) ≤ v →
                S.base.metric v = (G.flow.base.metric v).restrictOpen U) ∧
              ∃ (pU : U) (C : Set U), pU.val = p ∧
                Subtype.val '' C = riemannianClosedBallOf (G.flow.base.metric T) p (ρ / 2) ∧
                IsCompact C ∧ pU ∈ interior C ∧
                ∀ x ∈ frontier C,
                  ENNReal.ofReal (ρ / 2) ≤ riemannianEDistOf (S.base.metric T) pU x := by
  intro H' t
  have hk : H'.toHistory.activeStage t = Fin.last H.eventCount :=
    H.activeStage_extendHorizon_eq_last (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG t hT.le
  have hmet (v : ℝ) : H'.toHistory.stageMetric (Fin.last H.eventCount) v =
      G.flow.base.metric v :=
    H.stageMetric_extendHorizon_last (hend ▸ hT.le) (G.closedPrefix T hT hTs) hG hT v
  obtain ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, hcur, pU, C,
      hpU, himage, hC, hpC, hsep⟩ :=
    H'.toHistory.exists_stage_common_flow_with_compact_neighborhood_of_isTracedRegion t
      (Fin.last H.eventCount) hk p _ (cast_heq _ _) h
  rw [hmet] at hU himage
  refine ⟨a, hat, ha, U, hU, f, hf, hinj, hcross, hlast, S, hS, hmetric, hRm, ?_, pU, C, hpU,
    himage, hC, hpC, hsep⟩
  intro v hv hvl
  have hdom : v ∈ H'.toHistory.stageDomain (Fin.last H.eventCount) := by
    change v ∈ H'.toHistory.stageDomain (Fin.last H'.toHistory.eventCount)
    simp only [ObservedHistory.stageDomain, Fin.lastCases_last]
    exact ⟨hvl, hv.2⟩
  rw [hcur v hv hdom, hmet]
  rfl

theorem isTerminalTracedRegion.normSq_le {ρ τ K : ℝ}
    (h : H.isTerminalTracedRegion hend G hG hT hTs p ρ τ K)
    (x : (H.stage (Fin.last H.eventCount)).Carrier)
    (hx : x ∈ riemannianBallOf (G.flow.base.metric T) p ρ) :
    normSq0S (G.flow.base.metric T) x 4 (metricRm04At (G.flow.base.metric T) x) ≤ K ^ 2 := by
  obtain ⟨a, hat, -, U, hU, -, -, -, -, -, S, -, -, hRm, hcur, -⟩ :=
    exists_common_flow_with_compact_neighborhood_of_isTerminalTracedRegion h
  have hxU : x ∈ U := by
    change x ∈ (U : Set (H.stage (Fin.last H.eventCount)).Carrier)
    rw [hU]
    exact hx
  have hb := hRm T ⟨hat, le_rfl⟩ ⟨x, hxU⟩
  change normSq0S (S.base.metric T) ⟨x, hxU⟩ 4 (metricRm04At (S.base.metric T) ⟨x, hxU⟩) ≤
    K ^ 2 at hb
  rw [hcur T ⟨hat, le_rfl⟩ hT.le, Perelman.CanonicalNeighborhood.rmNormSq_restrictOpen] at hb
  exact hb

end RetainedCoreHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u})

theorem isRmBoundedBy_of_backwardPointTrace_of_derivative_bounds
    {Ctime : ℝ≥0} {qcan M : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    {p : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier}
    (A : BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
      (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) p)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hscalar : metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2) :
    A.isRmBoundedBy (hat := hut) (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) := by
  set K := 8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M with hKdef
  have hK : 0 < K := by
    have := hphi.pos 0
    have := hphi.pos 1
    have : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    rw [hKdef]
    have : 0 < M := by linarith
    positivity
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hr : 0 < 1 / Real.sqrt K := by positivity
  have hr2 : (1 / Real.sqrt K) ^ 2 = K⁻¹ := by rw [div_pow, Real.sq_sqrt hK.le, one_pow, one_div]
  have hrM : (1 / Real.sqrt K) ^ 4 * K ^ 2 ≤ 1 := by
    rw [show (1 / Real.sqrt K) ^ 4 = ((1 / Real.sqrt K) ^ 2) ^ 2 by ring, hr2, inv_pow,
      inv_mul_cancel₀ (by positivity)]
  have hctrl := H.isRmControlled_of_backwardPointTrace_of_derivative_bounds hphi hpinch hut
    hlast A hslabs hcurrent hfinal hM hqcan hscalar htime hrM
  have h := (A.isRmControlled_iff_isRmBoundedBy hr).1 hctrl
  rwa [hr2, inv_inv] at h

theorem isTracedRegion_of_forall_nonempty_backwardPointTrace
    {Ctime : ℝ≥0} {qcan M ρ τ : ℝ} {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) (hpinch : H.EventSlabsPinched phi)
    {u t : Icc (0 : ℝ) H.toHistory.horizon} (hut : u ≤ t) (hρ : 0 < ρ) (hτ : 0 < τ)
    (hu : (u : ℝ) = t - τ)
    (hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
      ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi)
    (y : (H.toHistory.stage (H.toHistory.activeStage t)).Carrier)
    (hslabs : H.EventSlabsDerivative Ctime qcan (H.toHistory.activeStage t))
    (hcurrent : ∀ j : Fin H.eventCount, j.castSucc = H.toHistory.activeStage t →
      (H.toHistory.event j).incoming.DerivativeBoundBefore Ctime qcan t)
    (hfinal : ∀ h : H.time (Fin.last H.eventCount) < H.horizon,
      H.toHistory.activeStage t = Fin.last H.eventCount →
      ((H.finalSlab h).restrictIncoming le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t)
    (hM : 1 ≤ M) (hqcan : qcan ≤ M)
    (hspace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y ρ,
      metricScalarAt (H.toHistory.stageMetric (H.toHistory.activeStage t) t) x ≤ M)
    (htime : Ctime * M * τ ≤ 1 / 2)
    (htrace : ∀ x ∈ riemannianBallOf (H.toHistory.stageMetric (H.toHistory.activeStage t) t)
        y ρ,
      Nonempty (BackwardPointTrace H.toHistory (H.toHistory.activeStage u)
        (H.toHistory.activeStage t) (H.toHistory.activeStage_mono hut) x)) :
    H.toHistory.isTracedRegion t y ρ τ (8 * Real.sqrt 3 * (1 + phi 1 + phi 0) * M) := by
  refine ⟨hρ, hτ, u, hut, hu, fun x hx => ?_⟩
  obtain ⟨A⟩ := htrace x hx
  refine ⟨A, H.isRmBoundedBy_of_backwardPointTrace_of_derivative_bounds hphi hpinch
    hut hlast A hslabs hcurrent hfinal hM hqcan (hspace x hx) ?_⟩
  rw [hu, sub_sub_cancel]
  exact htime

theorem eventSlabsPinched_extendHorizon {phi : ℝ → ℝ} (hpinch : H.EventSlabsPinched phi)
    {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).EventSlabsPinched phi :=
  hpinch

theorem eventSlabsDerivative_extendHorizon {Ctime : ℝ≥0} {qcan : ℝ}
    {k : Fin (H.eventCount + 1)} (hder : H.EventSlabsDerivative Ctime qcan k)
    {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).EventSlabsDerivative Ctime qcan k :=
  hder

theorem eventSlabsGradient_extendHorizon {Cgrad : ℝ≥0} {qcan : ℝ}
    {k : Fin (H.eventCount + 1)} (hgrad : H.EventSlabsGradient Cgrad qcan k)
    {T : ℝ} (hT : H.horizon ≤ T)
    (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
    (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
      H.initialMetric (Fin.last H.eventCount)) :
    (H.extendHorizon T hT S hS).EventSlabsGradient Cgrad qcan k :=
  hgrad

variable {H} {s : ℝ}
  {G : (H.stage (Fin.last H.eventCount)).IncomingSlab (H.time (Fin.last H.eventCount)) s}
  {hG : G.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount)}
  {T : ℝ} {hHT : H.horizon ≤ T} {hT : H.time (Fin.last H.eventCount) < T} {hTs : T < s}

theorem extendHorizon_finalSlab_phiAlmostNonnegative {phi : ℝ → ℝ}
    (hp : Perelman.PhiAlmostNonnegative G.flow (Ico (H.time (Fin.last H.eventCount)) s) phi) :
    ∃ h : H.time (Fin.last H.eventCount) <
        (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).horizon,
      Perelman.PhiAlmostNonnegative
        ((H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).finalSlab h).flow
        (Icc (H.time (Fin.last H.eventCount))
          (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).horizon) phi :=
  ⟨hT, fun v hv x => hp v ⟨hv.1, hv.2.trans_lt hTs⟩ x⟩

theorem extendHorizon_finalSlab_derivativeBoundBefore {Ctime : ℝ≥0} {qcan t₀ : ℝ}
    (hder : G.DerivativeBoundBefore Ctime qcan t₀) {t : ℝ} (ht : t ≤ t₀)
    (h : H.time (Fin.last H.eventCount) <
      (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).horizon) :
    (((H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).finalSlab h).restrictIncoming
      le_rfl h le_rfl).DerivativeBoundBefore Ctime qcan t :=
  fun y v hv hq => hder y v ⟨hv.1, hv.2.trans_le ht⟩ hq

theorem extendHorizon_finalSlab_gradientBoundBefore {Cgrad : ℝ≥0} {qcan t₀ : ℝ}
    (hgrad : G.GradientBoundBefore Cgrad qcan t₀) {t : ℝ} (ht : t ≤ t₀)
    (h : H.time (Fin.last H.eventCount) <
      (H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).horizon) :
    (((H.extendHorizon T hHT (G.closedPrefix T hT hTs) hG).finalSlab h).restrictIncoming
      le_rfl h le_rfl).GradientBoundBefore Cgrad qcan t :=
  fun y v hv hq => hgrad y v ⟨hv.1, hv.2.trans_le ht⟩ hq

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
