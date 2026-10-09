import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ESegPath_S101
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.FlowlineUnique_S115
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroLowPoint_S33
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingPatch_CX5

set_option autoImplicit false

/-! # CH12-S115 G2: the NEW half of `hflow` for `r ≤ t` in ONE dyadic window `j` (the same-window case)

With `x s = smoothedPhysicalMap_CX5 H T hT θ f E s base = f j s (E j (θ (s / (2^j T)), base))` for `s` in
window `j` (`smoothedPhysicalMap_eq_S115`), put `p := E j (θ_t, base)` (`θ_t = θ (t / (2^j T))`).  Then
* the flow-line of `x t` back to time `r` is `s ↦ f j s p` (new data are time-independent in the model), and it is
  lifted at EVERY `s` of the window (`hlift` = S8 conjunct 16 at the fixed point `p ∈ B(4 ρ_j)`), with value
  `f j t p = x t` at `s = t` — this is the input of `flowline_unique_Icc_S115` (G1);
* the two `C¹` pieces of `hflow` (new track): `γ₁` = the `E_j`-segment from `E j (θ_r, base)` to `p`, `γ₂` constant
  at `p`; both in `B(4 ρ_j)` with `h`-speed² `≤ η_j²` (`eseg_path_ball_S101`).
The 2-window case (`r` in window `j`, `t` in window `j+1`) additionally needs `p ∈ B(2ρ_j)` (seam `hend`), see the
HANDOVER (`E_{j+1}(θ_t, base) ∈ B(2ρ_j)` is NOT a consequence of the S8 list). -/
noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open Manifold GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12
universe u

theorem smoothedPhysicalMap_eq_S115 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T)
    (θ : ℝ → ℝ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) → H.Carrier →
      (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (t : ℝ) (htT : T ≤ t) (j : ℕ)
    (hj : dyadicIndex_CX5 T t = j) (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (p : H.Carrier) :
    smoothedPhysicalMap_CX5 H T hT θ f E t htT p = f j t ht (E j (θ (t / (2 ^ j * T)), p)) := by
  subst hj
  rfl

theorem newside_same_window_S115 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T)
    (θ : ℝ → ℝ) (hθ : ∀ s, θ s ∈ Icc (0 : ℝ) 1)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) → H.Carrier →
      (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (j : ℕ) (hρ : 0 < ρ j)
    (hE : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ (E j))
    (hbij : ∀ μ, Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hispeed : ∀ μ ∈ Icc (0 : ℝ) 1, ∀ p : H.Carrier,
      let v := mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E j (r, p)) μ
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ));
      H.metric.inner (E j (μ, p)) v v ≤ η j ^ 2)
    (hlift : ∀ (s : ℝ), s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T) →
      ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
        (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
        (_ : b ≤ (F.tower.history n).horizon)
        (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
          first ≤ (F.tower.history n).toHistory.activeStage r ∧
            (F.tower.history n).toHistory.activeStage r ≤ last)
        (φ : H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
        ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
          (hrs : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 (φ p))
              (f j r hrs p))
    (r t : ℝ) (hr : r ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)) (ht : t ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T))
    (hrj : dyadicIndex_CX5 T r = j) (htj : dyadicIndex_CX5 T t = j)
    (hrT : T ≤ r) (htT : T ≤ t) :
    ∃ (p : H.Carrier) (γ₁ γ₂ : ℝ → H.Carrier),
      p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₁ (Icc 0 1) ∧ ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ₂ (Icc 0 1) ∧
      f j r hr (γ₁ 0) = smoothedPhysicalMap_CX5 H T hT θ f E r hrT H.basepoint ∧
      f j r hr (γ₁ 1) = f j r hr (γ₂ 0) ∧ γ₁ 1 = p ∧ γ₂ 1 = p ∧
      (∀ s ∈ Icc (0 : ℝ) 1, γ₁ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) ∧
        γ₂ s ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      (∀ s ∈ Ioo (0 : ℝ) 1, H.metric.inner (γ₁ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₁ s 1) ≤ η j ^ 2 ∧
        H.metric.inner (γ₂ s) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) γ₂ s 1) ≤ η j ^ 2) ∧
      f j t ht p = smoothedPhysicalMap_CX5 H T hT θ f E t htT H.basepoint ∧
      (∀ s ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T),
        ∃ (n : ℕ) (first last : Fin ((F.tower.history n).eventCount + 1))
          (ordered : first ≤ last) (a b : ℝ) (_ : a < s) (_ : s < b)
          (_ : b ≤ (F.tower.history n).horizon)
          (stages : ∀ r : Icc (0 : ℝ) (F.tower.history n).horizon, (r : ℝ) ∈ Ioo a b →
            first ≤ (F.tower.history n).toHistory.activeStage r ∧
              (F.tower.history n).toHistory.activeStage r ≤ last)
          (y : (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered),
          ∀ (r : Icc (0 : ℝ) (F.tower.history n).horizon) (hr : (r : ℝ) ∈ Ioo a b)
            (hrW : (r : ℝ) ∈ Icc (2 ^ j * T) (2 ^ (j + 1) * T)),
            HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
              ((F.tower.history n).toHistory.activeStage r) (stages r hr).1 (stages r hr).2 y)
              (f j r hrW p)) := by
  have hbase : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) :=
    mem_riemannianBallOf_self_S33 H.metric H.basepoint (by linarith)
  set μr := θ (r / (2 ^ j * T)) with hμr
  set μt := θ (t / (2 ^ j * T)) with hμt
  have hp : E j (μt, H.basepoint) ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) :=
    E_mem_ball_S101 H (E j) hbij hsupp μt hbase
  obtain ⟨γ₁, hγ₁, h10, h11, hγ₁B, hγ₁s⟩ := eseg_path_ball_S101 H (E j) hE hbij hsupp hbase
    (hispeed · · H.basepoint) (hθ (r / (2 ^ j * T))) (hθ (t / (2 ^ j * T)))
  obtain ⟨γ₂, hγ₂, h20, h21, hγ₂B, hγ₂s⟩ := eseg_path_ball_S101 H (E j) hE hbij hsupp hbase
    (hispeed · · H.basepoint) (hθ (t / (2 ^ j * T))) (hθ (t / (2 ^ j * T)))
  refine ⟨E j (μt, H.basepoint), γ₁, γ₂, hp, hγ₁, hγ₂, ?_, ?_, h11, h21,
    fun s hs => ⟨hγ₁B s hs, hγ₂B s hs⟩, fun s hs => ⟨hγ₁s s hs, hγ₂s s hs⟩, ?_, ?_⟩
  · rw [h10, smoothedPhysicalMap_eq_S115 H hT θ f E r hrT j hrj hr]
  · rw [h11, h20]
  · rw [smoothedPhysicalMap_eq_S115 H hT θ f E t htT j htj ht]
  · intro s hs
    obtain ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, φ, -, hφ⟩ := hlift s hs
    exact ⟨n, first, last, ordered, a, b, has, hsb, hb, stages, φ (E j (μt, H.basepoint)),
      fun r' hr' hrW => hφ r' hr' hrW _ hp⟩

end GC.LongTime.Ch12
