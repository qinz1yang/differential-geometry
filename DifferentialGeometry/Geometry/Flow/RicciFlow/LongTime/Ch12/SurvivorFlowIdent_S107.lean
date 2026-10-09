import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.GronwallStage_S104
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TrackedRestrict_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeStages_S70
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow

set_option autoImplicit false

/-!
# CH12-S107 / G1b-(L): the glued survivor flow is the stage flow pulled back along the survivor map

For the smooth flow `G` on the fixed open domain `D = backwardSurvivorDomain first last` produced by
`ObservedHistory.exists_backwardSurvivor_isSolutionOn` (slab clause + initial-metric clause), at every time
`ρ ≤ time last` of the stage `j ∈ [first, last]` one has `G ρ = ψ_j^* (stageMetric j ρ)`
(`survivorFlow_eq_stage_pullback_S107`), hence the inner product / Ricci tensor of `G ρ` at `y` on `(V, V)`
are those of `stageMetric j ρ` at `ψ_j y` on `(dψ_j V, dψ_j V)`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

instance backwardSurvivorDomain_sigmaCompact_S107 (K : ObservedHistory.{u})
    (first last : Fin (K.eventCount + 1)) (hle : first ≤ last) :
    SigmaCompactSpace (K.backwardSurvivorDomain first last hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (K.backwardSurvivorDomain first last hle).isOpen)

theorem time_le_of_mem_stageDomain_S107 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    {ρ : ℝ} (hρ : ρ ∈ K.stageDomain j) : K.time j ≤ ρ := by
  cases j using Fin.lastCases with
  | last => exact ((ObservedHistory.mem_stageDomain_last K ρ).1 hρ).1
  | cast i =>
    rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hρ
    exact hρ.1

theorem lt_time_succ_of_mem_stageDomain_S107 (K : ObservedHistory.{u}) (i : Fin K.eventCount)
    {ρ : ℝ} (hρ : ρ ∈ K.stageDomain i.castSucc) : ρ < K.time i.succ := by
  rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc] at hρ
  exact hρ.2

/-- (L): the glued survivor flow is the pulled-back stage flow. -/
theorem survivorFlow_eq_stage_pullback_S107 (K : ObservedHistory.{u})
    (first last : Fin (K.eventCount + 1)) (hle : first ≤ last)
    (G : ℝ → SmoothRiemannianMetric ThreeModel (K.backwardSurvivorDomain first last hle))
    (hslab : ∀ (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ t ∈ Icc (K.time i.castSucc) (K.time i.succ),
        G t = K.backwardSurvivorSlabMetric first last hle i hf hl t)
    (hinit : ∀ (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
      G (K.time j) = K.backwardSurvivorInitialMetric first last hle j hj hl)
    (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) {ρ : ℝ}
    (hρ : ρ ∈ K.stageDomain j) (hρl : ρ ≤ K.time last) :
    G ρ = localPullMetric (K.stageMetric j ρ) (K.backwardSurvivorMap first last hle j hj hl)
      (K.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl) := by
  have hleft : K.time j ≤ ρ := time_le_of_mem_stageDomain_S107 K j hρ
  by_cases hρj : ρ = K.time j
  · subst hρj
    rw [hinit j hj hl, K.stageMetric_initial]
    rfl
  · have hlt : K.time j < ρ := lt_of_le_of_ne hleft (Ne.symm hρj)
    have hjl : j ≠ Fin.last K.eventCount := by
      intro hjl
      have : last = j := le_antisymm (hjl ▸ Fin.le_last _) hl
      rw [this] at hρl
      exact absurd hρl (not_le.mpr hlt)
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hjl
    have hil : i.succ ≤ last := Fin.castSucc_lt_iff_succ_le.mp
      (lt_of_le_of_ne hl (by
        intro h
        rw [← h] at hρl
        exact absurd hρl (not_le.mpr hlt)))
    have htt : ρ ∈ Ico (K.time i.castSucc) (K.time i.succ) :=
      ⟨hleft, lt_time_succ_of_mem_stageDomain_S107 K i hρ⟩
    have hp := K.backwardSurvivorMap_isLocalDiffeomorph first last hle i.castSucc hj hl
    rw [hslab i hj hil ρ ⟨htt.1, htt.2.le⟩, ObservedHistory.backwardSurvivorSlabMetric,
      (K.event i).terminal.extendedMetric_before htt.2, ObservedHistory.stageMetric_castSucc_apply]
    rw [← localPullMetric_subtype_val]
    exact localPullMetric_comp _ _ _ _ _ hp

theorem survivorFlow_inner_S107 (K : ObservedHistory.{u})
    (first last : Fin (K.eventCount + 1)) (hle : first ≤ last)
    (G : ℝ → SmoothRiemannianMetric ThreeModel (K.backwardSurvivorDomain first last hle))
    (hslab : ∀ (i : Fin K.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last),
      ∀ t ∈ Icc (K.time i.castSucc) (K.time i.succ),
        G t = K.backwardSurvivorSlabMetric first last hle i hf hl t)
    (hinit : ∀ (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last),
      G (K.time j) = K.backwardSurvivorInitialMetric first last hle j hj hl)
    (j : Fin (K.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) {ρ : ℝ}
    (hρ : ρ ∈ K.stageDomain j) (hρl : ρ ≤ K.time last)
    (y : K.backwardSurvivorDomain first last hle) (V : TangentSpace ThreeModel y) :
    (G ρ).inner y V V =
        (K.stageMetric j ρ).inner (K.backwardSurvivorMap first last hle j hj hl y)
          (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V)
          (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V) ∧
      ricciTensor (G ρ) y V V =
        ricciTensor (K.stageMetric j ρ) (K.backwardSurvivorMap first last hle j hj hl y)
          (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V)
          (mfderiv ThreeModel ThreeModel (K.backwardSurvivorMap first last hle j hj hl) y V) := by
  rw [survivorFlow_eq_stage_pullback_S107 K first last hle G hslab hinit j hj hl hρ hρl,
    localPullMetric_inner, ricciTensor_localPullMetric]
  exact ⟨rfl, rfl⟩

end GC.LongTime.Ch12
