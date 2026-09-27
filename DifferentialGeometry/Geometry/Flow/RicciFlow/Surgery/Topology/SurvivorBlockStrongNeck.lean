import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeckSurvivorSlab
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StrongNeckPullbackTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckParabolicTransport
import DifferentialGeometry.Geometry.Metric.Pullback.LocalComposition

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness (metricScalarAt_restrictOpen)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

open private ObservedHistory.mem_Icc_of_mem_window from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionAncientLimit

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

private theorem localPullMetric_congr_fun {M N : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [TopologicalSpace N]
    [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel N) {φ ψ : M → N}
    (hφ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ φ)
    (hψ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ψ) (h : φ = ψ) :
    localPullMetric g φ hφ = localPullMetric g ψ hψ := by
  subst h
  rfl

variable (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)

private local instance (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t) :
    SigmaCompactSpace (H.backwardSurvivorDomain first (H.activeStage t) hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel
    (H.backwardSurvivorDomain first (H.activeStage t) hle).isOpen)

private local instance (W : Opens (H.stageAt t).Carrier) : SigmaCompactSpace W :=
  isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen ThreeModel W.isOpen)

theorem exists_survivor_flow_of_block {R : ℝ} (hR : 0 < R) {s : ℝ}
    (G : (H.stage (H.activeStage t)).IncomingSlab (H.time (H.activeStage t)) s) (hts : (t : ℝ) < s)
    (hG : ∀ τ ∈ Icc (H.time (H.activeStage t)) (t : ℝ),
      G.flow.base.metric τ = H.stageMetric (H.activeStage t) τ)
    (k : ℕ) (W : Opens (H.stageAt t).Carrier) (h : ℝ → SmoothRiemannianMetric ThreeModel W)
    (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t) (ha : (a : ℝ) = t - 2 * ((k + 2 : ℕ) : ℝ) / R)
    (f : (j : H.StageInterval (H.activeStage a) (H.activeStage t)) → W → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : H.activeStage a ≤ i.castSucc)
      (hl : i.succ ≤ H.activeStage t), ∀ x : W,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_lt_succ.le.trans hl⟩ x)
        (f ⟨i.succ, hi.trans i.castSucc_lt_succ.le, hl⟩ x))
    (htop : ∀ x : W, f ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ x = x.val)
    (hpull : ∀ σ ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0,
      ∀ j : H.StageInterval (H.activeStage a) (H.activeStage t),
        (t : ℝ) + σ / R ∈ H.stageDomain j.val →
          h σ = scaleMetric R hR
            (localPullMetric (H.stageMetric j.val ((t : ℝ) + σ / R)) (f j) (hf j))) :
    ∃ (first : Fin (H.eventCount + 1)) (hle : first ≤ H.activeStage t)
      (hWU : ∀ x : W, x.val ∈ H.backwardSurvivorDomain first (H.activeStage t) hle)
      (hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : W =>
        (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain first (H.activeStage t) hle)))
      (gflow : ℝ → SmoothRiemannianMetric ThreeModel
        (H.backwardSurvivorDomain first (H.activeStage t) hle)),
      H.time first ≤ (t : ℝ) - 2 * ((k + 2 : ℕ) : ℝ) / R ∧
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ H.activeStage t),
        ∀ τ ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow τ = H.backwardSurvivorSlabMetric first (H.activeStage t) hle j hf hl τ) ∧
      (∀ τ ∈ Ico (H.time (H.activeStage t)) s,
        gflow τ = (G.flow.base.metric τ).restrictOpen
          (H.backwardSurvivorDomain first (H.activeStage t) hle)) ∧
      IsSolutionOn ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := H.backwardSurvivorDomain first (H.activeStage t) hle)
          (RealTimeInterval.closedOpen (H.time first) s
            ((H.time_strictMono.monotone hle).trans_lt ((H.activeStage_time_le t).trans_lt hts)))) ∧
      ∀ σ ∈ Icc (-((k + 2 : ℕ) : ℝ)) 0,
        h σ = scaleMetric R hR (localPullMetric (gflow ((t : ℝ) + σ / R))
          (fun x : W => (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain first (H.activeStage t) hle))
          hι) := by
  have hle : H.activeStage a ≤ H.activeStage t := H.activeStage_mono hat
  let A : ∀ x : W, BackwardPointTrace H (H.activeStage a) (H.activeStage t) hle x.val := fun x =>
    { point := fun j hj hl => f ⟨j, hj, hl⟩ x
      endpoint_eq := htop x
      crossing := fun i hi hl => hcross i hi hl x }
  have hWU : ∀ x : W, x.val ∈ H.backwardSurvivorDomain (H.activeStage a) (H.activeStage t) hle :=
    fun x => ⟨A x⟩
  have hsub : W ≤ H.backwardSurvivorDomain (H.activeStage a) (H.activeStage t) hle :=
    fun x hx => hWU ⟨x, hx⟩
  have hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : W =>
      (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain (H.activeStage a) (H.activeStage t) hle)) := by
    change IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Opens.inclusion hsub)
    apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
      (contMDiff_inclusion hsub) _ rfl
    intro x
    rw [mfderiv_opens_incl]
    exact Function.injective_id
  have hmap : ∀ (j : Fin (H.eventCount + 1)) (hj : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t)
      (x : W), H.backwardSurvivorMap (H.activeStage a) (H.activeStage t) hle j hj hl
        ⟨x.val, hWU x⟩ = f ⟨j, hj, hl⟩ x :=
    fun j hj hl x => H.backwardSurvivorMap_eq_point (H.activeStage a) (H.activeStage t) hle j hj hl
      ⟨x.val, hWU x⟩ (A x)
  have hinit : G.flow.base.metric (H.time (H.activeStage t)) =
      H.initialMetric (H.activeStage t) := by
    rw [hG _ ⟨le_rfl, H.activeStage_time_le t⟩, H.stageMetric_initial]
  obtain ⟨gflow, hslabs, hcur, hsol⟩ :=
    H.exists_backwardSurvivor_incomingSlab_flow (H.activeStage a) (H.activeStage t) hle G hinit
  refine ⟨H.activeStage a, hle, hWU, hι, gflow, ?_, hslabs, hcur, hsol, ?_⟩
  · rw [← ha]
    exact H.activeStage_time_le a
  intro σ hσ
  have hk2 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hσ2 : σ ∈ Icc (-(2 * ((k + 2 : ℕ) : ℝ))) 0 := ⟨by linarith [hσ.1], hσ.2⟩
  have hv := ObservedHistory.mem_Icc_of_mem_window hR ha hσ2
  let v : Icc (0 : ℝ) H.horizon := ⟨(t : ℝ) + σ / R, a.2.1.trans hv.1, hv.2.trans t.2.2⟩
  have hav : a ≤ v := hv.1
  have hvt : v ≤ t := hv.2
  obtain ⟨j, hj⟩ : ∃ j : H.StageInterval (H.activeStage a) (H.activeStage t),
      j.val = H.activeStage v :=
    ⟨⟨H.activeStage v, H.activeStage_mono hav, H.activeStage_mono hvt⟩, rfl⟩
  have hmem : (t : ℝ) + σ / R ∈ H.stageDomain j.val := by
    rw [hj]
    exact H.activeStage_mem v
  rw [hpull σ hσ2 j hmem]
  congr 1
  rcases eq_or_lt_of_le (H.activeStage_mono hvt) with heq | hlt
  · have hjtop : j = ⟨H.activeStage t, H.activeStage_mono hat, le_rfl⟩ :=
      Subtype.ext (hj.trans heq)
    subst hjtop
    have hτk : H.time (H.activeStage t) ≤ (t : ℝ) + σ / R := by
      rw [← heq]
      exact H.activeStage_time_le v
    dsimp only
    rw [hcur _ ⟨hτk, hv.2.trans_lt hts⟩, hG _ ⟨hτk, hv.2⟩, ← localPullMetric_subtype_val,
      localPullMetric_comp _ _ _ _ _
        (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _) hι)]
    exact localPullMetric_congr_fun _ _ _ (funext htop)
  · obtain ⟨i, hi⟩ : ∃ i : Fin H.eventCount, H.activeStage v = i.castSucc := by
      cases hav' : H.activeStage v using Fin.lastCases with
      | last => exact absurd ((hav' ▸ hlt).trans_le (Fin.le_last _)) (lt_irrefl _)
      | cast i => exact ⟨i, rfl⟩
    have hji : j.val = i.castSucc := hj.trans hi
    have hf' : H.activeStage a ≤ i.castSucc := hji ▸ j.2.1
    have hl' : i.succ ≤ H.activeStage t := Fin.castSucc_lt_iff_succ_le.mp (hi ▸ hlt)
    have hjeq : j = ⟨i.castSucc, hf', i.castSucc_lt_succ.le.trans hl'⟩ := Subtype.ext hji
    subst hjeq
    have hdom : (t : ℝ) + σ / R ∈ Ico (H.time i.castSucc) (H.time i.succ) := by
      simpa only [stageDomain, Fin.lastCases_castSucc] using hmem
    dsimp only
    rw [hslabs i hf' hl' _ ⟨hdom.1, hdom.2.le⟩, backwardSurvivorSlabMetric,
      localPullMetric_comp _ _ _ _ _ (isLocalDiffeomorph_comp
        (H.backwardSurvivorTerminalMap_isLocalDiffeomorph _ _ _ i _ hl') hι),
      (H.event i).terminal.extendedMetric_before hdom.2, ← localPullMetric_subtype_val,
      localPullMetric_comp _ _ _ _ _ (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
        (isLocalDiffeomorph_comp (H.backwardSurvivorTerminalMap_isLocalDiffeomorph _ _ _ i _ hl')
          hι)),
      stageMetric_castSucc_apply]
    refine localPullMetric_congr_fun _ _ _ (funext fun x => ?_)
    change f ⟨i.castSucc, hf', i.castSucc_lt_succ.le.trans hl'⟩ x =
      (H.backwardSurvivorTerminalMap _ _ _ i hf' hl' ⟨x.val, hWU x⟩).val
    rw [backwardSurvivorTerminalMap_val, hmap]

theorem historyStrongNeck_of_survivor_strongNeck (y : (H.stageAt t).Carrier) {R : ℝ}
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
    {ε ε₁ : ℝ} (hε : ε ≤ ε₁) (hε₁ : ε₁ < 1 / 11)
    (hfam : ℝ → SmoothRiemannianMetric ThreeModel W)
    (hfam_def : ∀ σ, hfam σ = scaleMetric R hR (localPullMetric (gflow ((t : ℝ) + σ / R))
      (fun x : W => (⟨x.val, hWU x⟩ : H.backwardSurvivorDomain first (H.activeStage t) hle)) hι))
    (nk : StrongNeck ({ base := { metric := hfam } } : SolutionOn (I := ThreeModel) (M := W)
        (RealTimeInterval.closed (-((k + 2 : ℕ) : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg _))))
      ε ⟨y, hy⟩ 0) :
    H.HistoryStrongNeck (H.activeStage t) G ε₁ y t := by
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
  have hreg : Ioo ((t : ℝ) - (SU.scalar t (ι ⟨y, hy⟩))⁻¹) t ⊆
      (RealTimeInterval.closedOpen (H.time first) s hts').regular := by
    rw [hQ]
    intro r hr
    exact ⟨hwin1.trans_lt hr.1, hr.2.trans hts⟩
  let tk : TruncatedNeck SU ε (1 / 5) (ι ⟨y, hy⟩) t :=
    TruncatedNeck.ofStrongNeck nk₄ (by norm_num) (by norm_num) fun b r hr z hz v =>
      nk₄.comparison_jet_differentiableWithinAt_of_lt_one hsol (by norm_num) hreg b hr z hz v
  refine ⟨first, hle, hts', gflow, ?_, hslabs, hcur, hsol, ι ⟨y, hy⟩, rfl, ⟨tk.mono hε hε₁⟩⟩
  rw [hGt]
  have : 1 / 5 * R⁻¹ ≤ 2 * ((k + 2 : ℕ) : ℝ) / R := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) hRinv.le
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
