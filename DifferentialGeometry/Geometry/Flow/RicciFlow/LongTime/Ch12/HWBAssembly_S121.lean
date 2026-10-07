import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SurvivorWindowFlow_S121
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.LocalFlowPkg_S110
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.WBNLevelV_S121

set_option autoImplicit false

/-!
# CH12-S121 / G3: `hWB_of_hShi_S121` — the W-B binder `hWB''` (= `hWB'` of S91 with `a < t` and `h0 : j ≤ k + 3`) from the
frozen Shi binder `[FROZEN v2] CH12-S121 hShi` (producer: S122)

Assembly: `wbN_of_hShi_S121` at `N = backwardSurvivorDomain first last`, `g = gStage_S110 …`, `f := φ`, with the flow
`exists_windowFlow_S121` + `localFlow_package_S110`; `h0` / `hC0` / `hdef` / the conclusion are transported along
`ckErr_gStage_eq_post_S110` / `ckErr_gStage_S110` / `defect_gStage_S110`.  `T := 1` (no large-`t` hypothesis is needed).
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set TopologicalSpace
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

theorem hWB_of_hShi_S121 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (hShi : ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ), 0 < R → 0 < ε →
      ∃ KShi : ℝ, 0 ≤ KShi ∧ ∀ δ' η₀ : ℝ, 0 < δ' → δ' ≤ 1 → 0 < η₀ → η₀ ≤ 1 / 2 →
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N]
        (g : ℝ → SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N) (t : ℝ), 0 < t →
        ∀ (hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (ballU_S98 H R))
          (hinj : ∀ y ∈ ballU_S98 H R, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)),
        (∃ (D : RealTimeInterval) (S' : SolutionOn (I := 𝓡 3) (M := ballU_S98 H R) D),
          IsSolutionOn S' ∧ Icc t (2 * t) ⊆ D.regular ∧
          (∀ (x₀ : ballU_S98 H R) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × ballU_S98 H R => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
                (S'.base.metric p.1) x₀ p.2 i j)
              (Icc t (2 * t) ×ˢ
                (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          (∀ r ∈ Icc t (2 * t),
            S'.base.metric r = pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)) →
        (∀ j ≤ k + 3, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g t) t⁻¹ f j p < δ') →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ckErr_S45 H (g r) r⁻¹ f 0 p < η₀) →
        (∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
          ∀ V : TangentSpace (𝓡 3) (f p),
            |2 * r * ricciTensor (g r) (f p) V V + (g r).inner (f p) V V| ≤
              η₀ * (g r).inner (f p) V V) →
        ∀ s ≤ k + 1, ∀ r ∈ Icc t (2 * t), ∀ x : ballU_S98 H R,
          (x : H.Carrier) ∈ riemannianBallOf H.metric H.basepoint
            (2 * R - R / (((k + 1 : ℕ) : ℝ) + 1) / 2) →
          normSq0S (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) x (2 + s)
            (ricCovTower (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj)
              (pullbackRestrict_S57 H (g r) f (ballU_S98 H R) hF hinj) s x) * r ^ (2 + s) ≤
            KShi ^ 2) :
    ∀ (H : FiniteVolumeHyperbolicModel.{u}) (R ε : ℝ) (k : ℕ), 0 < R → 0 < ε →
        ∃ δ' T η₀ : ℝ, 0 < δ' ∧ 0 < T ∧ 0 < η₀ ∧ ∀ (t : ℝ) (_ht0 : 0 < t) (_htT : T ≤ t)
          (U : TopologicalSpace.Opens H.Carrier)
          (f : H.Carrier → (postStage F.observation t).Carrier),
          riemannianBallOf H.metric H.basepoint (2 * R) ⊆ U →
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U →
          IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) →
          (∀ j : ℕ, j ≤ k + 3 → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
            ckErr_S45 H (postMetric F.observation t) t⁻¹ f j p < δ') →
          ∀ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
            (ordered : first ≤ last) (a b : ℝ) (_ : a < t) (_ : 2 * t < b)
            (_ : b ≤ (F.tower.history n).horizon)
            (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
              first ≤ (F.tower.history n).toHistory.activeStage r ∧
                (F.tower.history n).toHistory.activeStage r ≤ last)
            (φ : H.Carrier →
              (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
            ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (2 * R)) →
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) = t → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
                HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                  ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                  (φ p)) (f p)) →
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
                ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                  (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ q)) 0 p < η₀) →
            (∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
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
                        (φ p)) V V) →
            ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b),
              (r : ℝ) ∈ Icc t (2 * t) → ∀ j : ℕ, j ≤ k →
              ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
                ckErr_S45 H ((F.tower.history n).toHistory.stageMetric
                  ((F.tower.history n).toHistory.activeStage r) r) r⁻¹
                  (fun q => (F.tower.history n).toHistory.backwardSurvivorMap first last ordered
                    ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2
                    (φ q)) j p < ε
  := by
  intro H R ε k hR hε
  obtain ⟨δ', η₀, hδ, hδ1, hη, hη1, hmain⟩ := wbN_of_hShi_S121 hShi H k hR hε
  refine ⟨δ', 1, η₀, hδ, one_pos, hη, ?_⟩
  intro t ht0 _htT U f hU hsm hemb herr0 n first last ordered a b hat htb hbh stages φ hφ hheq hIC hdef
  have hth : t ≤ (F.tower.history n).horizon := by linarith
  have htb' : t < b := by linarith
  have : SigmaCompactSpace ((F.tower.history n).toHistory.backwardSurvivorDomain first last ordered) :=
    backwardSurvivorDomain_sigmaCompact_S107 (F.tower.history n).toHistory first last ordered
  let W : Opens H.Carrier := ballU_S98 H R
  have hmem : ∀ r ∈ Icc t (2 * t), r ∈ Ico a b ∧ r ∈ Icc (0 : ℝ) (F.tower.history n).horizon :=
    fun r hr => ⟨⟨hat.le.trans hr.1, by linarith [hr.2]⟩, ht0.le.trans hr.1, by linarith [hr.2]⟩
  have hheq' : ∀ p ∈ W, HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
        ((F.tower.history n).toHistory.activeStage ⟨t, ht0.le, hth⟩)
        (stages ⟨t, ht0.le, hth⟩ ⟨hat.le, by linarith⟩).1
        (stages ⟨t, ht0.le, hth⟩ ⟨hat.le, by linarith⟩).2 (φ p)) (f p) :=
    fun p hp => hheq ⟨t, ht0.le, hth⟩ ⟨hat.le, by linarith⟩ rfl p hp
  have hinjf : ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y) :=
    fun y hy => injective_mfderiv_of_embedding_S67 H f U hsm hemb y (hU hy)
  have hfinj : Set.InjOn f (W : Set H.Carrier) := by
    intro p hp q hq hpq
    have := hemb.isEmbedding.injective (a₁ := (⟨p, hU hp⟩ : U)) (a₂ := ⟨q, hU hq⟩) hpq
    exact congrArg Subtype.val this
  have hdφ := injective_mfderiv_phi_S110 H n first last ordered a b t stages ht0.le hth hat.le htb' f φ W
    hφ hheq' hinjf
  have hφinj := injOn_phi_S121 H n first last ordered a b t stages ht0.le hth hat.le htb' f φ
    (W : Set H.Carrier) hheq' hfinj
  let g0 := (F.tower.history n).toHistory.backwardSurvivorInitialMetric first last ordered last ordered le_rfl
  obtain ⟨D, G, hG, hreg, hjoint, hgG⟩ := exists_windowFlow_S121 (F.tower.history n).toHistory first last
    ordered a b t ht0 hat htb hbh stages g0
  have hLF := localFlow_package_S110 H φ W hφ hdφ hφinj t D G hG hreg hjoint
    (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0) hgG
  have h0 : ∀ j ≤ k + 3, ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 t)
        t⁻¹ φ j p < δ' := by
    intro j hj p hp
    rw [ckErr_gStage_eq_post_S110 H n first last ordered a b t stages g0 ht0.le hth hat.le htb' f φ W hφ
      hheq' j p hp]
    exact herr0 j hj p hp
  have hC0 : ∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ckErr_S45 H (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 r)
        r⁻¹ φ 0 p < η₀ := by
    intro r hr p hp
    obtain ⟨hs, hs0⟩ := hmem r hr
    rw [ckErr_gStage_S110 (F.tower.history n).toHistory first last ordered a b stages H g0 hs hs0 φ W hφ r⁻¹ 0 p hp]
    exact hIC ⟨r, hs0⟩ hs hr p hp
  have hdefN : ∀ r ∈ Icc t (2 * t), ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * R),
      ∀ V : TangentSpace (𝓡 3) (φ p),
        |2 * r * ricciTensor (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 r)
            (φ p) V V +
          (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 r).inner (φ p) V V| ≤
          η₀ * (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 r).inner
            (φ p) V V := by
    intro r hr p hp V
    obtain ⟨hs, hs0⟩ := hmem r hr
    exact defect_gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0 hs hs0 η₀ (φ p)
      (hdef ⟨r, hs0⟩ hs hr p hp) V
  have hfin := hmain (gStage_S110 (F.tower.history n).toHistory first last ordered a b stages g0) φ t ht0
    hφ hdφ hLF h0 hC0 hdefN
  intro r hr hrs j hj p hp
  have hball : riemannianBallOf H.metric H.basepoint R ⊆ riemannianBallOf H.metric H.basepoint (2 * R) :=
    riemannianBallOf_mono H.metric H.basepoint (by linarith)
  have := hfin j hj r hrs p hp
  rw [ckErr_gStage_S110 (F.tower.history n).toHistory first last ordered a b stages H g0 hr r.2 φ W hφ _ j p (hball hp)] at this
  exact this

end GC.LongTime.Ch12

end
