import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftBridge_S65

set_option autoImplicit false

/-!
# CH12-S65 / G2: the family `fs` of `hLTF04` from one global survivor lift on `[t, 2t]`

Given a lift datum `(n, first, last, a, b, φ)` with `a < t` and `2 t < b ≤ horizon` (so every
`r ∈ [t, 2t]` lies in `(a, b)`) whose initial value at `r = t` is `f`, the family
`fs r p := liftMap_S65 (φ p)` has the smoothness / injectivity / error / lift clauses of the
conclusion of `hLTF04_S45` (all `HEq` bookkeeping is in `LiftBridge_S65`).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12 GC.LongTime.CuspP1
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}

/-- The conclusion clauses of `hLTF04_S45` for one global survivor lift. -/
theorem exists_fs_of_global_lift_S70 (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ)
    (t : ℝ) (ht0 : 0 < t) (f : H.Carrier → (postStage F.observation t).Carrier)
    (hinj : Set.InjOn f (riemannianBallOf H.metric H.basepoint R))
    (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1)) (ordered : first ≤ last)
    (a b : ℝ) (hat : a ≤ t) (htb : 2 * t < b) (hbh : b ≤ (F.tower.history n).horizon)
    (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
      first ≤ (F.tower.history n).toHistory.activeStage r ∧
        (F.tower.history n).toHistory.activeStage r ≤ last)
    (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint R))
    (hIC : ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
      (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
          (φ p)) (f p))
    (herr : ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
      (r : ℝ) ∈ Icc t (2 * t) → ∀ j : ℕ, j ≤ k →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
        ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
          (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
            ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
            (φ q)) j p < ε) :
    ∃ fs : (s : ℝ) → s ∈ Icc t (2 * t) → H.Carrier → (postStage F.observation s).Carrier,
      (∀ p ∈ riemannianBallOf H.metric H.basepoint R, fs t ⟨le_rfl, by linarith⟩ p = f p) ∧
      ∀ (s : ℝ) (hs : s ∈ Icc t (2 * t)),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fs s hs) (riemannianBallOf H.metric H.basepoint R) ∧
        Set.InjOn (fs s hs) (riemannianBallOf H.metric H.basepoint R) ∧
        (∀ j : ℕ, j ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H (postMetric F.observation s) s⁻¹ (fs s hs) j p < ε) ∧
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (φ : H.Carrier →
            (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint R) ∧
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
            (hrs : (r : ℝ) ∈ Icc t (2 * t)),
            ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
              HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                (φ p)) (fs r hrs p) := by
  -- the time `s ∈ [t, 2t]` as a point of the horizon interval, and membership in `(a, b)`
  have hrt : ∀ s : ℝ, s ∈ Icc t (2 * t) → s ∈ Icc (0 : ℝ) (F.tower.history n).horizon :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hab : ∀ s : ℝ, s ∈ Icc t (2 * t) → s ∈ Ico a b :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  let fs : (s : ℝ) → s ∈ Icc t (2 * t) → H.Carrier → (postStage F.observation s).Carrier :=
    fun s hs p => liftMap_S65 (F := F) n first last ordered ⟨s, hrt s hs⟩
      (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 (φ p)
  have hts : t ∈ Icc t (2 * t) := ⟨le_rfl, by linarith⟩
  have hfs_t : ∀ p ∈ riemannianBallOf H.metric H.basepoint R, fs t hts p = f p := by
    intro p hp
    exact eq_of_heq ((liftMap_heq_S65 (F := F) n first last ordered ⟨t, hrt t hts⟩ _ _ (φ p)).symm.trans
      (hIC ⟨t, hrt t hts⟩ (hab t hts) rfl p hp))
  refine ⟨fs, hfs_t, fun s hs => ?_⟩
  have hbsm_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun q => (F.tower.history n).toHistory.backwardSurvivorMap
      first last ordered ((F.tower.history n).toHistory.activeStage ⟨s, hrt s hs⟩)
      (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 (φ q))
      (riemannianBallOf H.metric H.basepoint R) :=
    (((F.tower.history n).toHistory.backwardSurvivorMap_isLocalDiffeomorph first last ordered _
      (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2).contMDiff).comp_contMDiffOn hφ
  refine ⟨?_, ?_, ?_, n, first, last, ordered, a, b, by linarith [hs.1], by linarith [hs.2, htb], hbh,
    stages, φ, hφ, ?_⟩
  · exact contMDiffOn_cast_S65 (postStage_eq_stage_active_CPD2 F.observation n ⟨s, hrt s hs⟩).symm _ _ hbsm_smooth
  · intro p hp q hq hpq
    have h1 : (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨s, hrt s hs⟩)
        (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 (φ p) =
      (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨s, hrt s hs⟩)
        (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 (φ q) :=
      cast_inj_S65 (postStage_eq_stage_active_CPD2 F.observation n ⟨s, hrt s hs⟩).symm hpq
    have h2 := (F.tower.history n).toHistory.backwardSurvivorMap_injective first last ordered _
      (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 h1
    have h3 : (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, hrt t hts⟩)
        (stages ⟨t, hrt t hts⟩ (hab t hts)).1 (stages ⟨t, hrt t hts⟩ (hab t hts)).2 (φ p) =
      (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, hrt t hts⟩)
        (stages ⟨t, hrt t hts⟩ (hab t hts)).1 (stages ⟨t, hrt t hts⟩ (hab t hts)).2 (φ q) :=
      congrArg _ h2
    have h4 : f p = f q := eq_of_heq
      ((hIC ⟨t, hrt t hts⟩ (hab t hts) rfl p hp).symm.trans
        ((heq_of_eq h3).trans (hIC ⟨t, hrt t hts⟩ (hab t hts) rfl q hq)))
    exact hinj hp hq h4
  · intro j hj p hp
    have := herr ⟨s, hrt s hs⟩ (hab s hs) hs j hj p hp
    rw [← ckErr_liftMap_S65 (F := F) H n first last ordered ⟨s, hrt s hs⟩
      (stages ⟨s, hrt s hs⟩ (hab s hs)).1 (stages ⟨s, hrt s hs⟩ (hab s hs)).2 φ s⁻¹ j p] at this
    exact this
  · intro r hr hrs p hp
    exact liftMap_heq_S65 (F := F) n first last ordered r (stages r hr).1 (stages r hr).2 (φ p)

end GC.LongTime.Ch12
