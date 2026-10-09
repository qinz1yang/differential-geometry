import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BridgeIooCore_S89
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33

set_option autoImplicit false

/-!
# CH12-S89 / G2: `Ico` lift datum at an event time ⇒ `Ioo` datum (history-level bridge)

See `[FROZEN] CH12-S89 bridge` in `build-logs/ch12/DELIVERIES.md`.
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem hlift_Ioo_core_S89 {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (K : ObservedHistory.{u})
    {p : CutoffParameters}
    (records : ∀ i : Fin K.eventCount, GeometricCutoffRecord K i p)
    {t0 : ℝ}
    (hscale : ∀ i : Fin K.eventCount, K.time i.succ = t0 →
      ∀ (b : (K.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((records i).static b).neck.scale / 2 ≤
          metricScalarAt ((records i).static b).witness.metric
            (((records i).static b).witness.cap z))
    (hrc : ∀ i : Fin K.eventCount, K.time i.succ = t0 →
      p.recenterConstant * p.delta (K.time i.succ) ≤ 1 / 2)
    (B : Set X) (hB : B.Nonempty) {α : Icc (0 : ℝ) K.horizon → Type u} (S : Set ℝ)
    (y : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ S → X → α r)
    (ht0 : 0 ≤ t0)
    {first last : Fin (K.eventCount + 1)} {ordered : first ≤ last} {a b : ℝ}
    (hat : a ≤ t0) (hS : ∀ r ∈ S, a ≤ r) (htb : t0 < b) (hb : b ≤ K.horizon)
    (stages : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ico a b →
      first ≤ K.activeStage r ∧ K.activeStage r ≤ last)
    (φ : X → K.backwardSurvivorDomain first last ordered)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (B))
    (hheq : ∀ (r : Icc (0 : ℝ) K.horizon) (hr : (r : ℝ) ∈ Ico a b) (hrs : (r : ℝ) ∈ S),
      ∀ p ∈ B,
        HEq (K.backwardSurvivorMap first last ordered (K.activeStage r) (stages r hr).1
          (stages r hr).2 (φ p)) (y r hrs p))
    (hneg : K.time first = t0 → ∀ p ∈ B,
      metricScalarAt (K.initialMetric first)
        (K.backwardSurvivorMap first last ordered first le_rfl ordered (φ p)) ≤ 0) :
    ∃ (first' last' : Fin (K.eventCount + 1)) (ordered' : first' ≤ last') (a' : ℝ)
      (_ : a' < t0) (_ : t0 < b) (_ : b ≤ K.horizon)
      (stages' : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ioo a' b →
        first' ≤ K.activeStage r ∧ K.activeStage r ≤ last')
      (φ' : X → K.backwardSurvivorDomain first' last' ordered'),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ' (B) ∧
      ∀ (r : Icc (0 : ℝ) K.horizon) (hr : (r : ℝ) ∈ Ioo a' b) (hrs : (r : ℝ) ∈ S),
        ∀ p ∈ B,
          HEq (K.backwardSurvivorMap first' last' ordered' (K.activeStage r) (stages' r hr).1
            (stages' r hr).2 (φ' p)) (y r hrs p) := by
  classical
  have hT0 : t0 ∈ Icc (0 : ℝ) K.horizon := ⟨ht0, htb.le.trans hb⟩
  let T0 : Icc (0 : ℝ) K.horizon := ⟨t0, hT0⟩
  have hT0st := stages T0 ⟨hat, htb⟩
  by_cases hnb : ∃ a' : ℝ, a' < t0 ∧ ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ioo a' t0 →
      first ≤ K.activeStage r
  · -- no bridge needed: the stage range already reaches below `t0`
    obtain ⟨a', ha', hfa⟩ := hnb
    have hst : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ioo a' b →
        first ≤ K.activeStage r ∧ K.activeStage r ≤ last := by
      intro r hr
      rcases lt_or_ge (r : ℝ) t0 with hlt | hge
      · exact ⟨hfa r ⟨hr.1, hlt⟩,
          (K.activeStage_mono (show r ≤ T0 from hlt.le)).trans hT0st.2⟩
      · exact stages r ⟨hat.trans hge, hr.2⟩
    exact ⟨first, last, ordered, a', ha', htb, hb, hst, φ, hφ, fun r hr hrs q hq =>
      hheq r ⟨hS _ hrs, hr.2⟩ hrs q hq⟩
  · push Not at hnb
    obtain ⟨i, rfl⟩ : ∃ i : Fin K.eventCount, first = i.succ := by
      rcases Fin.eq_zero_or_eq_succ first with h0 | ⟨i, hi⟩
      · exfalso
        obtain ⟨r, _, hnr⟩ := hnb (t0 - 1) (by linarith)
        exact absurd hnr (not_lt.mpr (by rw [h0]; exact Fin.zero_le _))
      · exact ⟨i, hi⟩
    have hle1 : K.time i.succ ≤ t0 :=
      (K.time_strictMono.monotone hT0st.1).trans (K.activeStage_time_le T0)
    have htime : K.time i.succ = t0 := by
      by_contra hne
      obtain ⟨r, hr, hnr⟩ := hnb (K.time i.succ) (lt_of_le_of_ne hle1 hne)
      exact absurd hnr (not_lt.mpr (K.le_activeStage r i.succ hr.1.le))
    have hord' : i.castSucc ≤ last := i.castSucc_lt_succ.le.trans ordered
    have hlt' : K.time i.castSucc < t0 :=
      htime ▸ K.time_strictMono (Fin.castSucc_lt_succ (i := i))
    -- pointwise extension through the event
    have hex : ∀ q ∈ B,
        ∃ w : K.backwardSurvivorDomain i.castSucc last hord', w.val = (φ q).val ∧
          ∀ (ρ : Fin (K.eventCount + 1)) (hj : i.succ ≤ ρ) (hl : ρ ≤ last),
            K.backwardSurvivorMap i.castSucc last hord' ρ
              ((i.castSucc_lt_succ.le).trans hj) hl w =
            K.backwardSurvivorMap i.succ last ordered ρ hj hl (φ q) := by
      intro q hq
      exact exists_extend_survivor_S89 ordered (φ q)
        (exists_regularCrossing_of_scalar_nonpos_S89 (records i) (hscale i htime) (hrc i htime) _ (hneg htime q hq))
    obtain ⟨p₀, hp₀⟩ := hB
    let φ' : X → K.backwardSurvivorDomain i.castSucc last hord' := fun q =>
      if hq : q ∈ B then Classical.choose (hex q hq)
      else Classical.choose (hex p₀ hp₀)
    have hφ'spec : ∀ q ∈ B,
        (φ' q).val = (φ q).val ∧
          ∀ (ρ : Fin (K.eventCount + 1)) (hj : i.succ ≤ ρ) (hl : ρ ≤ last),
            K.backwardSurvivorMap i.castSucc last hord' ρ
              ((i.castSucc_lt_succ.le).trans hj) hl (φ' q) =
            K.backwardSurvivorMap i.succ last ordered ρ hj hl (φ q) := by
      intro q hq
      have h := Classical.choose_spec (hex q hq)
      simp only [φ', hq, ↓reduceDIte]
      exact h
    have hst : ∀ r : Icc (0 : ℝ) K.horizon, (r : ℝ) ∈ Ioo (K.time i.castSucc) b →
        i.castSucc ≤ K.activeStage r ∧ K.activeStage r ≤ last := by
      intro r hr
      refine ⟨K.le_activeStage r _ hr.1.le, ?_⟩
      rcases lt_or_ge (r : ℝ) t0 with hlt | hge
      · exact (K.activeStage_mono (show r ≤ T0 from hlt.le)).trans hT0st.2
      · exact (stages r ⟨hat.trans hge, hr.2⟩).2
    refine ⟨i.castSucc, last, hord', K.time i.castSucc, hlt', htb, hb, hst, φ', ?_, ?_⟩
    · rw [← DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff
        (K.backwardSurvivorDomain i.castSucc last hord') φ']
      have h1 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ φ)
          (B) :=
        (DifferentialGeometry.Manifold.contMDiffOn_subtypeVal_comp_iff
          (K.backwardSurvivorDomain i.succ last ordered) φ _).mpr hφ
      refine h1.congr fun q hq => ?_
      exact (hφ'spec q hq).1
    · intro r hr hrs q hq
      have hr' : (r : ℝ) ∈ Ico a b := ⟨hS _ hrs, hr.2⟩
      have hspec := (hφ'spec q hq).2 (K.activeStage r) (stages r hr').1 (stages r hr').2
      have : K.backwardSurvivorMap i.castSucc last hord' (K.activeStage r) (hst r hr).1
          (hst r hr).2 (φ' q) =
          K.backwardSurvivorMap i.succ last ordered (K.activeStage r) (stages r hr').1
            (stages r hr').2 (φ q) := hspec
      rw [this]
      exact hheq r hr' hrs q hq

end GC.LongTime.Ch12
