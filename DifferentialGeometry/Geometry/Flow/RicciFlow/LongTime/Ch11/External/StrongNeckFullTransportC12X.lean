import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongNeckFullC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorBlockStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckPrefix
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckExtendHorizon

/-!
# Full history strong necks: survivor producer and history transports (C12X, S16 G2b)

Untruncated versions of
* `historyStrongNeck_of_survivor_strongNeck` (`Surgery/Topology/SurvivorBlockStrongNeck`),
* `historyStrongNeck_extendHorizon_iff` (`Surgery/Topology/HistoryStrongNeckExtendHorizon`),
* `historyStrongNeck_of_prefixAt` (`Surgery/Topology/HistoryStrongNeckPrefix`),
for `HistoryStrongNeckFull_C12X`.  The survivor producer keeps the accuracy `ε` of the blow-up
neck (no `ε₁`; use `HistoryStrongNeckFull_C12X.mono_eps`).
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RetainedCoreHistory.backwardPointTraceToPrefix from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckPrefix

universe u

namespace ObservedHistory

section Survivor

variable (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)

private local instance s16b_sigmaSurvivor (first : Fin (H.eventCount + 1))
    (hle : first ≤ H.activeStage t) :
    SigmaCompactSpace (H.backwardSurvivorDomain first (H.activeStage t) hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel
    (H.backwardSurvivorDomain first (H.activeStage t) hle).isOpen)

private local instance s16b_sigmaOpens (W : Opens (H.stageAt t).Carrier) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

/-- Survivor producer: the blow-up neck at the slice transports to a full (depth-one) history
neck of the same accuracy; untruncated `historyStrongNeck_of_survivor_strongNeck`. -/
theorem historyStrongNeckFull_of_survivor_strongNeck_C12X (y : (H.stageAt t).Carrier) {R : ℝ}
    (hR : 0 < R) (hscal : metricScalarAt (H.stageMetric (H.activeStage t) t) y = R) {s : ℝ}
    (G : (H.stage (H.activeStage t)).IncomingSlab (H.time (H.activeStage t)) s) (hts : (t : ℝ) < s)
    (hG : ∀ τ ∈ Icc (H.time (H.activeStage t)) (t : ℝ),
      G.flow.base.metric τ = H.stageMetric (H.activeStage t) τ)
    (k : ℕ) (W : Opens (H.stageAt t).Carrier) (hy : y ∈ W)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t)
    (hWU : ∀ x : W, x.val ∈ H.backwardSurvivorDomain first (H.activeStage t) hle)
    (hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : W =>
      (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain first (H.activeStage t) hle)))
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorDomain first (H.activeStage t) hle))
    (hwin : H.time first ≤ (t : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R)
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
      ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow τ = H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl τ)
    (hcur : ∀ τ ∈ Ico (H.time (H.activeStage t)) s,
      gflow τ = (G.flow.base.metric τ).restrictOpen
        (H.backwardSurvivorDomain first (H.activeStage t) hle))
    (hsol : IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first (H.activeStage t) hle)
        (RealTimeInterval.closedOpen (H.time first) s
          ((H.time_strictMono.monotone hle).trans_lt ((H.activeStage_time_le t).trans_lt hts)))))
    {ε : ℝ} (hfam : ℝ → SmoothRiemannianMetric ThreeModel W)
    (hfam_def : ∀ σ, hfam σ = scaleMetric R hR (localPullMetric (gflow ((t : ℝ) + σ / R))
      (fun x : W => (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain first (H.activeStage t) hle)) hι))
    (nk : StrongNeck ({ base := { metric := hfam } } : SolutionOn (I := ThreeModel) (M := W)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))
      ε ⟨y, hy⟩ 0) :
    H.HistoryStrongNeckFull_C12X (H.activeStage t) G ε y t := by
  have hts' : H.time first < s :=
    (H.time_strictMono.monotone hle).trans_lt ((H.activeStage_time_le t).trans_lt hts)
  let U := H.backwardSurvivorDomain first (H.activeStage t) hle
  let ι : W → U := fun x => ⟨x.val, hWU x⟩
  let SU : SolutionOn (I := ThreeModel) (M := U)
      (RealTimeInterval.closedOpen (H.time first) s hts') :=
    { base := { metric := gflow } }
  have hk2 : (1 : ℝ) ≤ 2 * ((k + 2 : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 2 k
    linarith
  have hRinv : (0 : ℝ) < R⁻¹ := inv_pos.mpr hR
  have hwin1 : H.time first ≤ (t : ℝ) - R⁻¹ := by
    have : R⁻¹ ≤ 2 * ((k + 2 : ℕ) : ℝ) / R := by
      rw [div_eq_mul_inv]
      exact le_mul_of_one_le_left hRinv.le hk2
    linarith
  have hGt : G.flow.scalar t y = R := by
    change metricScalarAt (G.flow.base.metric t) y = R
    rw [hG t ⟨H.activeStage_time_le t, le_rfl⟩]
    exact hscal
  have hQ : SU.scalar t (ι ⟨y, hy⟩) = R := by
    change metricScalarAt (gflow t) (ι ⟨y, hy⟩) = R
    rw [hcur t ⟨H.activeStage_time_le t, hts⟩, metricScalarAt_restrictOpen]
    exact hGt
  have htD : (t : ℝ) ∈ (RealTimeInterval.closedOpen (H.time first) s hts').carrier :=
    ⟨hwin1.trans (sub_le_self _ hRinv.le), hts⟩
  have hnk0 : ({ base := { metric := hfam } } : SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg _)))).scalar 0 ⟨y, hy⟩ = 1 := by
    change metricScalarAt (hfam 0) ⟨y, hy⟩ = 1
    rw [hfam_def, metricScalarAt_scaleMetric, metricScalarAt_localPull, zero_div, add_zero]
    change R⁻¹ * SU.scalar t (ι ⟨y, hy⟩) = 1
    rw [hQ, inv_mul_cancel₀ hR.ne']
  have hD : Icc ((0 : ℝ) - (({ base := { metric := hfam } } : SolutionOn (I := ThreeModel) (M := W)
      (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0
        (neg_nonpos.mpr (Nat.cast_nonneg _)))).scalar 0 ⟨y, hy⟩)⁻¹) 0 ⊆
      (parabolicInterval (RealTimeInterval.closedOpen (H.time first) s hts') t R htD).carrier := by
    rw [hnk0, inv_one, zero_sub]
    intro σ hσ
    change (t : ℝ) + σ / R ∈ Ico (H.time first) s
    have h1 : -1 / R ≤ σ / R := div_le_div_of_nonneg_right hσ.1 hR.le
    have h2 : σ / R ≤ 0 := div_nonpos_of_nonpos_of_nonneg hσ.2 hR.le
    rw [neg_div, one_div] at h1
    constructor <;> linarith
  let nk₁ : StrongNeck (parabolicSolution (SU.localPullback ι hι) t R hR htD) ε ⟨y, hy⟩ 0 :=
    nk.ofMetricEq (fun τ => (hfam_def τ).symm) hD
  let nk₂ := (nk₁.ofParabolic t R hR htD 0).castTime (parabolicTime_zero t R)
  have hinj : Function.Injective ι := fun x₁ x₂ hx =>
    Subtype.ext (congrArg Subtype.val hx : (ι x₁).val = (ι x₂).val)
  let nk₄ : StrongNeck SU ε (ι ⟨y, hy⟩) t := nk₂.ofLocalPullback hι hinj
  refine ⟨first, hle, hts', gflow, H.activeStage_time_le t, ?_, hslabs, hcur, hsol,
    ι ⟨y, hy⟩, rfl, ⟨nk₄⟩⟩
  rw [hGt]
  exact hwin1

end Survivor

/-- Body of `HistoryStrongNeckFull_C12X` with the survivor domain and the terminal maps
abstracted (untruncated `strongNeckBody` / `neckBody`). -/
private def s16b_fullBody (K : ObservedHistory.{u}) (k : Fin (K.eventCount + 1)) {s : ℝ}
    (G : (K.stage k).IncomingSlab (K.time k) s) (eps : ℝ) (y : (K.stage k).Carrier) (t : ℝ)
    (first : Fin (K.eventCount + 1)) (O : Opens (K.stage k).Carrier)
    (f : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O → (K.event j).incoming.terminalRegularOpen)
    (hf : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j hj hl)) : Prop :=
  ∃ (hts : K.time first < s) (gflow : ℝ → SmoothRiemannianMetric ThreeModel O),
    K.time k ≤ t ∧ K.time first ≤ t - (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin K.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (K.time j.castSucc) (K.time j.succ),
        gflow τ = localPullMetric ((K.event j).terminal.extendedMetric τ) (f j hj hl)
          (hf j hj hl)) ∧
    (∀ τ ∈ Ico (K.time k) s, gflow τ = (G.flow.base.metric τ).restrictOpen O) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen (K.time first) s hts)) ∧
    ∃ z : O, z.val = y ∧
      Nonempty (StrongNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := O)
          (RealTimeInterval.closedOpen (K.time first) s hts)) eps z t)

private theorem s16b_full_iff_exists_body {K : ObservedHistory.{u}}
    {k : Fin (K.eventCount + 1)} {s : ℝ} {G : (K.stage k).IncomingSlab (K.time k) s}
    {eps : ℝ} {y : (K.stage k).Carrier} {t : ℝ} :
    K.HistoryStrongNeckFull_C12X k G eps y t ↔ ∃ (first : Fin (K.eventCount + 1))
      (hle : first ≤ k),
      K.s16b_fullBody k G eps y t first (K.backwardSurvivorDomain first k hle)
        (K.backwardSurvivorTerminalMap first k hle)
        (K.backwardSurvivorTerminalMap_isLocalDiffeomorph first k hle) := by
  rfl

private theorem s16b_fullBody_congr {K : ObservedHistory.{u}} {k : Fin (K.eventCount + 1)}
    {s : ℝ} {G : (K.stage k).IncomingSlab (K.time k) s} {eps : ℝ} {y : (K.stage k).Carrier}
    {t : ℝ} {first : Fin (K.eventCount + 1)} {O₁ O₂ : Opens (K.stage k).Carrier}
    (f₁ : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O₁ → (K.event j).incoming.terminalRegularOpen)
    (f₂ : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O₂ → (K.event j).incoming.terminalRegularOpen)
    (hf₁ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₁ j hj hl))
    (hf₂ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₂ j hj hl))
    (hO : O₁ = O₂)
    (hf : ∀ j hj hl (x : O₁), f₁ j hj hl x = f₂ j hj hl ⟨x.val, hO ▸ x.property⟩) :
    K.s16b_fullBody k G eps y t first O₁ f₁ hf₁ ↔
      K.s16b_fullBody k G eps y t first O₂ f₂ hf₂ := by
  subst hO
  have : f₁ = f₂ := funext fun j => funext fun hj => funext fun hl => funext fun x => hf j hj hl x
  subst this
  rfl

end ObservedHistory

namespace RetainedCoreHistory

section ExtendHorizon

variable {H : RetainedCoreHistory.{u}} (T : ℝ) (hT : H.horizon ≤ T)
  (S : (H.stage (Fin.last H.eventCount)).ClosedSlab (H.time (Fin.last H.eventCount)) T)
  (hS : S.flow.base.metric (H.time (Fin.last H.eventCount)) =
    H.initialMetric (Fin.last H.eventCount))

/-- Untruncated `historyStrongNeck_extendHorizon_iff` (`H`, `k`, `G`, `eps`, `y`, `t` implicit). -/
theorem historyStrongNeckFull_extendHorizon_iff_C12X {k : Fin (H.eventCount + 1)} {s : ℝ}
    {G : (H.stage k).IncomingSlab (H.time k) s} {eps : ℝ} {y : (H.stage k).Carrier} {t : ℝ} :
    (H.extendHorizon T hT S hS).toHistory.HistoryStrongNeckFull_C12X k G eps y t ↔
      H.toHistory.HistoryStrongNeckFull_C12X k G eps y t := by
  refine (ObservedHistory.s16b_full_iff_exists_body
    (K := (H.extendHorizon T hT S hS).toHistory) (k := k) (G := G)).trans (Iff.trans ?_
      (ObservedHistory.s16b_full_iff_exists_body (K := H.toHistory) (k := k) (G := G)).symm)
  refine exists_congr fun first => exists_congr fun hle => ?_
  exact ObservedHistory.s16b_fullBody_congr (K := H.toHistory) (first := first) _ _ _ _
    (H.backwardSurvivorDomain_extendHorizon T hT S hS first k hle) fun j hj hl x => by
      apply Subtype.ext
      let A := Classical.choice x.property
      exact (H.toHistory.backwardSurvivorMap_eq_point first k hle j.castSucc hj
        (j.castSucc_lt_succ.le.trans hl) _ ⟨A.point, A.endpoint_eq, A.crossing⟩).symm

end ExtendHorizon

section Prefix

variable (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))

private theorem s16b_fullBody_prefix_transfer {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ)
    (first : Fin ((H.prefixAt k).eventCount + 1))
    {O₁ O₂ : Opens (H.stage k).Carrier} (hO : O₁ = O₂)
    (f₁ : ∀ (j : Fin (H.prefixAt k).eventCount), first ≤ j.castSucc →
      j.succ ≤ Fin.last (H.prefixAt k).eventCount →
      O₁ → ((H.prefixAt k).toHistory.event j).incoming.terminalRegularOpen)
    (hf₁ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₁ j hj hl))
    (f₂ : ∀ (j : Fin H.eventCount),
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ j.castSucc → j.succ ≤ k →
      O₂ → (H.toHistory.event j).incoming.terminalRegularOpen)
    (hf₂ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₂ j hj hl))
    (hf : ∀ (j : Fin H.eventCount)
      (hj : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ j.castSucc)
      (hl : j.succ ≤ k) (x : O₁),
      f₂ j hj hl ⟨x.val, hO ▸ x.2⟩ = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl x)
    (hb : (H.prefixAt k).toHistory.s16b_fullBody (Fin.last (H.prefixAt k).eventCount) G eps y t
      first O₁ f₁ hf₁) :
    H.toHistory.s16b_fullBody k G eps y t
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) O₂ f₂ hf₂ := by
  subst hO
  obtain ⟨hts, gflow, htk, hwin, hslabs, hcur, hsol, z, hz, hnk⟩ := hb
  refine ⟨hts, gflow, htk, hwin, ?_, hcur, hsol, z, hz, hnk⟩
  intro j hj hl τ hτ
  rw [hslabs ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl τ hτ]
  have hfe : f₂ j hj hl = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl := funext fun x => hf j hj hl x
  have key : ∀ (ψ : O₁ → (H.toHistory.event j).incoming.terminalRegularOpen)
      (hψ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ψ),
      ψ = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl →
      localPullMetric ((H.toHistory.event j).terminal.extendedMetric τ)
        (f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl) (hf₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl) =
        localPullMetric ((H.toHistory.event j).terminal.extendedMetric τ) ψ hψ := by
    intro ψ hψ h
    subst h
    rfl
  exact key _ _ hfe

/-- Untruncated `historyStrongNeck_of_prefixAt`. -/
theorem historyStrongNeckFull_of_prefixAt_C12X {s : ℝ}
    (G : (H.stage k).IncomingSlab (H.time k) s) {eps t : ℝ} {y : (H.stage k).Carrier}
    (h : (H.prefixAt k).toHistory.HistoryStrongNeckFull_C12X
      (Fin.last (H.prefixAt k).eventCount) G eps y t) :
    H.toHistory.HistoryStrongNeckFull_C12X k G eps y t := by
  obtain ⟨first, hle, hb⟩ := h
  have hleH : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ k :=
    Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)
  have hO : (H.prefixAt k).toHistory.backwardSurvivorDomain first
      (Fin.last (H.prefixAt k).eventCount) hle =
      H.toHistory.backwardSurvivorDomain
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) k hleH := by
    ext q
    exact ⟨fun ⟨A⟩ => ⟨H.backwardPointTraceOfPrefix k A⟩,
      fun ⟨A⟩ => ⟨RetainedCoreHistory.backwardPointTraceToPrefix H k hle A⟩⟩
  refine ⟨_, hleH, s16b_fullBody_prefix_transfer H k G eps y t first hO _ _ _ _ ?_ hb⟩
  intro j hj hl x
  apply Subtype.ext
  let A := Classical.choice x.property
  exact (H.toHistory.backwardSurvivorMap_eq_point _ k hleH j.castSucc hj
    (j.castSucc_lt_succ.le.trans hl) ⟨x.val, hO ▸ x.2⟩ (H.backwardPointTraceOfPrefix k A)).trans
    ((H.prefixAt k).toHistory.backwardSurvivorMap_eq_point first _ hle
      (⟨j.val, Nat.lt_of_succ_le hl⟩ : Fin (H.prefixAt k).eventCount).castSucc hj
      (Fin.castSucc_lt_succ.le.trans hl) x A).symm

end Prefix

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
