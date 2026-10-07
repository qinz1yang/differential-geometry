import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LTF03Wiring_S32
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EmptyCoresPost_S37
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LiftFsIco_S70

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

/-- CH12-S65 (W-C assembly): `hLTF04Ico_S70` = [FROZEN v2] CH12-S45 verbatim, from the inline binders
`hWA` (W-A: `hLTF04_lift_k0_S56` shape with `a < t`) and `hWB` (W-B upgrade, [FROZEN] CH12-S65).
`hdec hneg hLTF03 hW2 hW1 Hp` are kept for the frozen consumer shape (unused here: they are the
inputs of the producers of `hWA`, `hWB`). -/
theorem hLTF04Ico_S70 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    (hneg : EventuallyNegativeScalar_S13 F)
    (_hLTF03 : ∀ (S : LatePointSequence_S13 F) (a v L : ℝ),
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
    (hWA :
  ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ), 0 < R → 0 < ε →
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
              (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : s < b)
              (_ : b ≤ (F.tower.history n).horizon)
              (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
                first ≤ (F.tower.history n).toHistory.activeStage r ∧
                  (F.tower.history n).toHistory.activeStage r ≤ last)
              (φ : H.Carrier →
                (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
              ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint R) ∧
              (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
                (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                  HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ p)) (f p)) ∧
              ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
                (r : ℝ) ∈ Icc t (2 * t) →
                ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                  ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                    ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                    (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                      ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                      (φ q)) 0 p < ε     )
    (hWB :
  ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ), 0 < R → 0 < ε →
        ∃ δ' T η₀ : ℝ, 0 < δ' ∧ 0 < T ∧ 0 < η₀ ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
          (U : TopologicalSpace.Opens H.Carrier)
          (f : H.Carrier → (postStage F.observation t).Carrier),
          riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k + 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δ') →
          ∀ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ t) (_ : 2 * t < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint R) →
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (f p)) →
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                  (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ q)) 0 p < η₀) →
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) → ∀ j : ℕ, j ≤ k →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                  (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ q)) j p < ε
    ) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ), 0 < R → 0 < ε →
      ∃ δ' T : ℝ, 0 < δ' ∧ 0 < T ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
        (U : TopologicalSpace.Opens H.Carrier)
        (f : H.Carrier → (postStage F.observation t).Carrier),
        riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U →
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
        (∀ j : ℕ, j ≤ k + 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δ') →
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
  intro H R ε k hR hε
  obtain ⟨δB, TB, η₀, hδB, hTB, hη₀, hB⟩ := hWB H R ε k hR hε
  obtain ⟨δA, TA, hδA, hTA, hA⟩ := hWA H R η₀ hR hη₀
  refine ⟨min δA δB, max TA TB, lt_min hδA hδB, lt_max_of_lt_left hTA, ?_⟩
  intro t ht0 htT U f hU hsm hemb herr0
  have htA : TA ≤ t := le_trans (le_max_left _ _) htT
  have htB : TB ≤ t := le_trans (le_max_right _ _) htT
  have herrA : ∀ j : ℕ, j ≤ 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δA :=
    fun j hj p hp => lt_of_lt_of_le (herr0 j (by omega) p hp) (min_le_left _ _)
  have herrB : ∀ j : ℕ, j ≤ k + 2 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δB :=
    fun j hj p hp => lt_of_lt_of_le (herr0 j hj p hp) (min_le_right _ _)
  obtain ⟨n, first, last, ordered, a, b, hat, htb, hbh, stages, φ, hφ, hIC, h0⟩ :=
    hA t ht0 htA U f hU hsm hemb herrA (2 * t) ⟨by linarith, le_rfl⟩
  have hk := hB t ht0 htB U f hU hsm hemb herrB n first last ordered a b hat htb hbh stages φ hφ hIC h0
  have hball : riemannianBallOf H.metric H.basepoint R ⊆ riemannianBallOf H.metric H.basepoint (2 * R) :=
    riemannianBallOf_mono H.metric H.basepoint (by linarith)
  have hinj : Set.InjOn f (riemannianBallOf H.metric H.basepoint R) := by
    intro p hp q hq hpq
    have := hemb.isEmbedding.injective (a₁ := (⟨p, hU (hball hp)⟩ : U)) (a₂ := ⟨q, hU (hball hq)⟩) hpq
    exact congrArg Subtype.val this
  exact exists_fs_of_global_lift_S70 H R ε k t ht0 f hinj n first last ordered a b hat htb hbh
    stages φ hφ hIC hk

end GC.LongTime.Ch12
