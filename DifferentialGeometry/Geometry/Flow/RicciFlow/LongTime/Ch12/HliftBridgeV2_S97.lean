import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchWiring_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BridgeIooF_S89
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

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

/-- CH12-S97: `hlift0_of_Ico_S84` v2 = the S84 adapter with the S89 bridge `hlift_Ioo_of_Ico_S89` plugged in
and the left-coverage clause discharged from hLTF04 v4 (`a ≤ t_j`, `t_j = dyadicTime T j ≤ r` on the window).
`hSne` (ball nonempty: basepoint, `ρ j > 0`) and `hs0` (`s ≥ 2^j T ≥ 0`) are derived; `hscale` (cap scalar
lower bound, inline as in S74/O3L) and `hrc` (late-time smallness at events of time `≥ T`) stay inline. -/
theorem hlift0_of_Ico_v2_S97 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ)
    (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T) (ρ : ℕ → ℝ) (hρpos : ∀ j, 0 < ρ j)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (hscale : ∀ n (i : Fin (F.tower.history n).eventCount),
      ∀ (b : ((F.tower.history n).toHistory.event i).RetainedBoundaryIndex) (z : ThreeBall),
        ((Hp.records n i).static b).neck.scale / 2 ≤
          metricScalarAt ((Hp.records n i).static b).witness.metric
            (((Hp.records n i).static b).witness.cap z))
    (hrc : ∀ n (i : Fin (F.tower.history n).eventCount),
      T ≤ (F.tower.history n).toHistory.time i.succ →
      Hp.parameters.recenterConstant *
        Hp.parameters.delta ((F.tower.history n).toHistory.time i.succ) ≤ 1 / 2)
    (hneg : ∀ j (t : ℝ) (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        metricScalarAt (postMetric F.observation t) (f j t ht p) ≤ 0)
    (hlift0Ico : ∀ j (s : ℝ), s ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a ≤ dyadicTime_CX5 T j) (_ : a ≤ s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ico a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ico a b)
        (hrW : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (f j r hrW p)) :
    ∀ j (s : ℝ), s ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
      (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
      (_ : b ≤ (F.tower.history n).horizon)
      (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
        first ≤ (F.tower.history n).toHistory.activeStage r ∧
          (F.tower.history n).toHistory.activeStage r ≤ last)
      (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
        (hrW : (r : ℝ) ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
          ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
          (f j r hrW p) := by
  intro j s hs
  have hTj : T ≤ dyadicTime_CX5 T j := by
    have h1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
    change T ≤ 2 ^ j * T
    nlinarith
  have hTs : T ≤ s := hTj.trans hs.1
  obtain ⟨n, first, last, ordered, a, b, hat0, hat, htb, hb, stages, φ, hφ, hheq⟩ := hlift0Ico j s hs
  exact hlift_Ioo_of_Ico_S89 Hp (riemannianBallOf H.metric H.basepoint (4 * ρ j))
    ⟨H.basepoint, mem_riemannianBallOf_self_O13 H.metric H.basepoint (by linarith [hρpos j])⟩
    (Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))) (fun r hr => f j r hr) s hs
    (hT.le.trans hTs) (fun n i _ => hscale n i)
    (fun n i htime => hrc n i (htime ▸ hTs)) (hneg j s hs)
    ⟨n, first, last, ordered, a, b, hat, fun r hr _ => hat0.trans hr.1, htb, hb, stages, φ, hφ, hheq⟩

end GC.LongTime.Ch12
