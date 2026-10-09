import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Wiring_S32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HLTF04Assembly_S65
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WeakAssemble_S132
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.IooBridge_S132
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HScaleExact_S119
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiringTail_S118

set_option autoImplicit false

/-!
# CH12-S132 / G3c: `hWA_S132 : hWA v4` (lead ruling A\': `hprof` + `hdec`, no bare `hscale` / `hrc`)

Statement = `[FROZEN v4] CH12-S117 hWA` (scratch/FrozenS117v4.lean) verbatim plus the profile clause `hprof`
(`[FROZEN] CH12-S119`, with `ε₀ := (hscale_of_prof_S119).choose`); `hW2` / `hW1` are kept for the frozen shape
(named `_hW2`, `_hW1`, unused by the proof).  Proof: `hico_S132` (the `Ico` datum on the whole window, G3b),
`hscale_of_prof_S119` (hprof ⟹ the exact S89 `hscale`), `hrc_of_hdec_S118` (hdec ⟹ `hrc` for events at times
`≥ Trc`), the K-level bridge `ioo_of_ico_S132` at the left end `t`, and the restriction `a'' := (a' + t) / 2`.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

theorem hWA_S132 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
      SeedHyperbolicOnFixedBallsSeq_S13 Hp hdec hneg S a v L)
    (_hW2 : ∀ w : ℝ, 0 < w → ∃ T Λ b τ C : ℝ, 0 < T ∧ 1 ≤ Λ ∧ 0 < b ∧ 0 < τ ∧ 0 < C ∧
      τ * b ^ 2 < 1 / 2 ∧
      ∀ s : GC.LongTime.RegularSlice F.observation, T ≤ s.time →
      ∀ (p : (s.history.stageAt (sliceTop_S8 s)).Carrier) (r : ℝ), 0 < r →
        r ≤ b * Real.sqrt s.time →
        (∀ q ∈ riemannianBallOf (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) p r,
          SectionalBoundedBelowAt (s.history.stageMetric (s.history.activeStage (sliceTop_S8 s))
            s.time) q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (s.history.stageMetric
          (s.history.activeStage (sliceTop_S8 s)) s.time) p r →
        (∀ n (i : Fin (F.tower.history n).eventCount),
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time →
          ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
        s.history.isTracedRegion (sliceTop_S8 s) p (2 * r) (τ * r ^ 2) (C / r ^ 2))
    (_hW1 : ∃ (b T C : ℝ → ℝ), (∀ w : ℝ, 0 < w → 0 < b w) ∧ (∀ w, 0 < C w) ∧
      ∀ w : ℝ, 0 < w → ∀ s : RegularSlice F.observation, T w ≤ s.time →
      ∀ (p : s.stage.Carrier) (r : ℝ), 0 < r → r ≤ b w →
        (∃ z ∈ connectedComponent p,
          ¬ SectionalBoundedBelowAt s.normalizedMetric z 0) →
        (∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          SectionalBoundedBelowAt s.normalizedMetric q (-(r ^ 2)⁻¹)) →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume s.normalizedMetric p r →
        ∀ k : ℕ, k ≤ 0 → ∀ q ∈ riemannianBallOf s.normalizedMetric p r,
          curvatureDerivativeNorm s.normalizedMetric k q ≤ C w * (r ^ (k + 2))⁻¹)
    (hprof : Hp.parameters.modelAccuracy ≤ (hscale_of_prof_S119.{u}).choose ∧
      2 ≤ Hp.parameters.modelOrder ∧ StandardCap.transitionEnd + 1 ≤ Hp.parameters.modelRadius) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε η₀ : ℝ), 0 < R → 0 < ε → 0 < η₀ →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H.Carrier)
        (f : H.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δ') →
        ∀ s ∈ Icc t (2 * t),
          ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a < t) (_ : s < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (2 * R)) ∧
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (f p)) ∧
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
                ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                  (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ q)) 0 p < ε) ∧
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
                ∀ V : TangentSpace ThreeModel
                    ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                      ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                      (φ p)),
                  |2 * (r : ℝ) * ricciTensor ((F.tower.history n).toHistory.stageMetric
                      ((F.tower.history n).toHistory.activeStage r) r)
                      ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                        ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                        (φ p)) V V +
                    ((F.tower.history n).toHistory.stageMetric
                      ((F.tower.history n).toHistory.activeStage r) r).inner
                      ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                        ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                        (φ p)) V V| ≤
                    η₀ * ((F.tower.history n).toHistory.stageMetric
                      ((F.tower.history n).toHistory.activeStage r) r).inner
                      ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                        ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                        (φ p)) V V := by
  have hsc := (hscale_of_prof_S119.{u}).choose_spec.2 Hp hprof
  intro H R ε η₀ hR hε hη₀
  obtain ⟨δ', T0, hδ', hT0, hmain⟩ := hico_S132 Hp hdec hneg hLTF03 H R ε η₀ hR hε hη₀
  obtain ⟨Trc, hTrc⟩ := hrc_of_hdec_S118 Hp hdec
  refine ⟨δ', max T0 Trc, hδ', lt_of_lt_of_le hT0 (le_max_left _ _), ?_⟩
  intro t ht0 htT U f hU hf hemb hck s hs
  have hBopen : IsOpen (riemannianBallOf H.metric H.basepoint (2 * R)) :=
    isOpen_riemannianBallOf_S61 H _
  have hBne : (riemannianBallOf H.metric H.basepoint (2 * R)).Nonempty := by
    refine ⟨H.basepoint, ?_⟩
    change riemannianEDistOf H.metric H.basepoint H.basepoint < _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (mul_pos two_pos hR)
  obtain ⟨n, first, last, ordered, a, b, hat, htb, hb, stages, φ, hφ, hHEq, hCK, hDEF, hNEG⟩ :=
    hmain t ht0 ((le_max_left _ _).trans htT) U f hU hf hemb hck
  obtain ⟨first', last', ordered', a', ha', stages', φ', hφ', hEq⟩ :=
    ioo_of_ico_S132 (F.tower.history n).toHistory (Hp.records n) (fun i _ b z => hsc n i b z)
      (fun i hi => hTrc n i (by rw [hi]; exact (le_max_right _ _).trans htT))
      (riemannianBallOf H.metric H.basepoint (2 * R)) hBne ht0.le hat htb hb stages φ hφ hNEG
  have hmem : ∀ r : ℝ, r ∈ Ico ((a' + t) / 2) b → r ∈ Ioo a' b :=
    fun r hr => ⟨by linarith [hr.1], hr.2⟩
  have hr0 : ∀ r : ℝ, r ∈ Icc t (2 * t) → r ∈ Ico a b :=
    fun r hr => ⟨hat.trans hr.1, by linarith [hr.2]⟩
  refine ⟨n, first', last', ordered', (a' + t) / 2, b, by linarith, by linarith [hs.2], hb,
    fun r hr => stages' r (hmem r hr), φ', hφ', ?_, ?_, ?_⟩
  · intro r hr hrt p hp
    have hrI : (r : ℝ) ∈ Icc t (2 * t) := ⟨hrt.ge, by linarith [hrt]⟩
    exact (heq_of_eq (hEq r (hmem r hr) (hr0 r hrI) hrI p hp)).trans (hHEq r (hr0 r hrI) hrt p hp)
  · intro r hr hrI p hp
    have hfe : ∀ q ∈ riemannianBallOf H.metric H.basepoint (2 * R),
        _ = _ := fun q hq => hEq r (hmem r hr) (hr0 r hrI) hrI q hq
    exact (ckErr_congr_open_S110 H _ _ _ ⟨_, hBopen⟩ hfe r⁻¹ 0 p hp).trans_lt
      (hCK r (hr0 r hrI) hrI p hp)
  · intro r hr hrI p hp V
    exact defect_pt_eq_S132 _ (hEq r (hmem r hr) (hr0 r hrI) hrI p hp).symm _ _
      (hDEF r (hr0 r hrI) hrI p hp) V

end GC.LongTime.Ch12
