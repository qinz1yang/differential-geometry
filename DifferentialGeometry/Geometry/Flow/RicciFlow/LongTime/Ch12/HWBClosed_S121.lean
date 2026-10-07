import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HWBAssembly_S121
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HShi_S122

set_option autoImplicit false

/-!
# CH12-S121 / G3: `hWB_S121` — `hWB''` (the hWB binder of the FIXed `hLTF04Ico_S91`) with the Shi binder CLOSED by `hShi_S122`
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime GC.LongTime.Ch12
open scoped Manifold ContDiff ENNReal
universe u

namespace GC.LongTime.Ch12

theorem hWB_S121 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} :
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
  := hWB_of_hShi_S121 hShi_S122

end GC.LongTime.Ch12

end
