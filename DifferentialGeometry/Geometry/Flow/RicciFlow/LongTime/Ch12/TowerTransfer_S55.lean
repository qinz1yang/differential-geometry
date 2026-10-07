import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CompactPatchEmbed

set_option autoImplicit false

/-! # CH12-S55 G1: tower transfer of survivor lifts

A survivor lift `φ : X → backwardSurvivorDomain first last` in the `n`-th history of an
observation tower gives, for every `N ≥ n`, a survivor lift into the `N`-th history over the
transported stage range (`towerEmb_CPD6`), with the same actual-flow image at every time
`r ≤ n` (heterogeneous equality of the survivor-map values).  This is the n-uniform `hlift` of
`[FROZEN] CH12-S49` F2 / `[FROZEN] CH12-S55`. -/

noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Surgery GC.LongTime
open GC.LongTime.CuspP1
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem contMDiff_carrierHomeo_S55 {A B : OrientedThreeStage.{u}} (h : A = B) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (carrierHomeo_CPD2 h) := by
  subst h
  exact contMDiff_id

theorem contMDiff_domMap_S55 {H K : ObservedHistory.{u}} (E : HistEmb_CPD6 H K)
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (E.domMap first last hle) := by
  refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
  exact (contMDiff_carrierHomeo_S55 (E.stage_eq last)).comp contMDiff_subtype_val

/-- Transport of a survivor lift along an embedding of histories: the lifted map, its smoothness,
and the survivor-map values at the transported stage `j'` (heterogeneous equality). -/
theorem embed_lift_heq_S55 {H K : ObservedHistory.{u}} (E : HistEmb_CPD6 H K)
    {first last : Fin (H.eventCount + 1)} (ordered : first ≤ last)
    (j : Fin (H.eventCount + 1)) (hj1 : first ≤ j) (hj2 : j ≤ last)
    (j' : Fin (K.eventCount + 1)) (hj' : j' = embIdx_CPD6 E.le j)
    (h1 : embIdx_CPD6 E.le first ≤ j') (h2 : j' ≤ embIdx_CPD6 E.le last)
    (z : H.backwardSurvivorDomain first last ordered) :
    HEq (K.backwardSurvivorMap (embIdx_CPD6 E.le first) (embIdx_CPD6 E.le last)
      (embIdx_le_CPD6 E.le ordered) j' h1 h2 (E.domMap first last ordered z))
      (H.backwardSurvivorMap first last ordered j hj1 hj2 z) := by
  subst hj'
  exact ((E.survivorMap_domMap first last ordered j hj1 hj2 z).symm ▸
    (carrierHomeo_heq_CPD2 (E.stage_eq j) _))

/-- **Tower transfer** (n-uniform lift, F2). -/
theorem tower_lift_transfer_S55 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (T : ObservationTower P g) {n N : ℕ} (hnN : n ≤ N)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {S : Set X}
    {first last : Fin ((T.history n).eventCount + 1)} (ordered : first ≤ last)
    (φ : X → (T.history n).backwardSurvivorDomain first last ordered)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S) :
    ∃ (first' last' : Fin ((T.history N).eventCount + 1)) (ordered' : first' ≤ last')
      (φ' : X → (T.history N).backwardSurvivorDomain first' last' ordered'),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ' S ∧
      ∀ (r : Icc (0 : ℝ) (T.history n).horizon) (r' : Icc (0 : ℝ) (T.history N).horizon)
        (_hrr : r'.1 = r.1)
        (hr : first ≤ (T.history n).activeStage r ∧ (T.history n).activeStage r ≤ last),
        ∃ hr' : first' ≤ (T.history N).activeStage r' ∧ (T.history N).activeStage r' ≤ last',
          ∀ p : X, HEq ((T.history N).backwardSurvivorMap first' last' ordered'
              ((T.history N).activeStage r') hr'.1 hr'.2 (φ' p))
            ((T.history n).backwardSurvivorMap first last ordered
              ((T.history n).activeStage r) hr.1 hr.2 (φ p)) := by
  let E := towerEmb_CPD6 T n N hnN
  refine ⟨embIdx_CPD6 E.le first, embIdx_CPD6 E.le last, embIdx_le_CPD6 E.le ordered,
    fun x => E.domMap first last ordered (φ x), ?_, ?_⟩
  · exact (contMDiff_domMap_S55 E first last ordered).comp_contMDiffOn hφ
  · intro r r' hrr hr
    have hact : (T.history N).activeStage r' = embIdx_CPD6 E.le ((T.history n).activeStage r) := by
      have h := E.activeStage_CPD6 r
      have hr'' : r' = ⟨r.1, r.2.1, r.2.2.trans E.horizon_le⟩ := Subtype.ext hrr
      rw [hr'', ← h]
    have h1 : embIdx_CPD6 E.le first ≤ (T.history N).activeStage r' := by
      rw [hact]; exact embIdx_le_CPD6 E.le hr.1
    have h2 : (T.history N).activeStage r' ≤ embIdx_CPD6 E.le last := by
      rw [hact]; exact embIdx_le_CPD6 E.le hr.2
    exact ⟨⟨h1, h2⟩, fun p =>
      embed_lift_heq_S55 E ordered _ hr.1 hr.2 _ hact h1 h2 (φ p)⟩


/-- **n-uniform lift** (`hlift` of `[FROZEN] CH12-S55`): a per-time survivor lift in its own history
`n₀` (the shape of S3 / `hLTF04_S45`) is a survivor lift in every history `N ≥ n₀` on the same
time window `(a, b)`, with the same actual-flow values.  `w` is the actual-flow family on the
window `W` (e.g. `f j` on `Icc (2^j T) (2^(j+1) T)`); `B r` its target type (`postStage r`). -/
theorem lift_uniform_S55 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] (S : Set X)
    (W : Set ℝ) (B : ℝ → Type u) (w : ∀ r : ℝ, r ∈ W → X → B r) (s : ℝ)
    (h0 : ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : X → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (w r hrW p)) :
    ∃ (a b : ℝ) (_ : a < s) (_ : s < b) (n₀ : ℕ), b ≤ n₀ ∧ ∀ N : ℕ, n₀ ≤ N →
      ∃ (first last : Fin ((F.tower.history N).eventCount + 1))
        (ordered : first ≤ last)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history N).horizon, (r : ℝ) ∈ Ioo a b →
          first ≤ (F.tower.history N).toHistory.activeStage r ∧
            (F.tower.history N).toHistory.activeStage r ≤ last)
        (φ : X → (F.tower.history N).toHistory.backwardSurvivorDomain first last ordered),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ S ∧
        ∀ (r : Icc (0 : ℝ) (F.tower.history N).horizon) (hr : (r : ℝ) ∈ Ioo a b)
          (hrW : (r : ℝ) ∈ W), ∀ p ∈ S,
          HEq ((F.tower.history N).toHistory.backwardSurvivorMap first last ordered
            ((F.tower.history N).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
            (w r hrW p) := by
  obtain ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, φ, hφ, hheq⟩ := h0
  refine ⟨a, b, has, hsb, n, by simpa [F.tower.horizon_eq n] using hb, ?_⟩
  intro N hnN
  obtain ⟨first', last', ordered', φ', hφ', hT⟩ :=
    tower_lift_transfer_S55 F.observation hnN ordered φ hφ
  have hbN : ∀ r : Icc (0 : ℝ) (F.tower.history N).horizon, (r : ℝ) ∈ Ioo a b →
      (r : ℝ) ≤ (F.tower.history n).horizon := fun r hr => by
    have := F.tower.horizon_eq n
    have hb' : b ≤ (n : ℝ) := by simpa [this] using hb
    rw [this]; exact (hr.2.le.trans hb')
  let rr : ∀ r : Icc (0 : ℝ) (F.tower.history N).horizon, (r : ℝ) ∈ Ioo a b →
      Icc (0 : ℝ) (F.tower.history n).horizon := fun r hr => ⟨r.1, r.2.1, hbN r hr⟩
  refine ⟨first', last', ordered', fun r hr => (hT (rr r hr) r rfl (stages (rr r hr) hr)).choose, φ', hφ', ?_⟩
  intro r hr hrW p hp
  obtain ⟨hr', hall⟩ := hT (rr r hr) r rfl (stages (rr r hr) hr)
  exact (hall p).trans (hheq (rr r hr) hr hrW p hp)

end GC.LongTime.Ch12
