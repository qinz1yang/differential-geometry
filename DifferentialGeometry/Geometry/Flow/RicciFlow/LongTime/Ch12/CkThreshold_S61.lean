import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.DiagonalAlpha_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61

set_option autoImplicit false

/-! # CH12-S61 G2b: application of `hcomp` (inline binder, `[FROZEN] CH12-S55`; lane S60 proves it):
the `ckErr` accuracy of the time-smoothed maps `x ↦ f j t (E j (μ, x))` on `B(2m)` for all large
windows `j`.  Together with `exists_diagonal_alpha_S61` this gives the `ckErr` clause of sheet S4. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem smoothed_ckErr_threshold_S61 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (K : ℕ)
    (f : (j : ℕ) → (t : ℝ) → t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1)) →
      H.Carrier → (postStage F.observation t).Carrier)
    (E : ℕ → ℝ × H.Carrier → H.Carrier) (η ρ : ℕ → ℝ) (ν : ℕ → ℕ)
    (hηt : Tendsto η atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop) (hν : Tendsto ν atTop atTop)
    (hEb : ∀ j μ, ContMDiff (𝓡 3) (𝓡 3) ∞ (fun p => E j (μ, p)) ∧
      Function.Bijective (fun p => E j (μ, p)))
    (hsupp : ∀ j μ p, p ∉ riemannianBallOf H.metric H.basepoint (4 * ρ j) → E j (μ, p) = p)
    (hEclose : ∀ j, ∀ μ ∈ Icc (0 : ℝ) 1, ∀ k : ℕ, k ≤ ν j →
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H H.metric 1 (fun x => E j (μ, x)) k p ≤ η j)
    (hacc : ∀ j t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f j t ht) (riemannianBallOf H.metric H.basepoint (4 * ρ j)) ∧
      ∀ k : ℕ, k ≤ ν j → ∀ p ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (f j t ht) k p < η j)
    (hcomp : ∀ (k : ℕ) (R ε : ℝ), 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
        [IsManifold (𝓡 3) ∞ N] (g' : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ)
        (f : H.Carrier → N) (E : H.Carrier → H.Carrier),
        ContMDiff (𝓡 3) (𝓡 3) ∞ E →
        (∀ i : ℕ, i ≤ k → ∀ p ∈ riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H H.metric 1 E i p ≤ δ) →
        (∀ i : ℕ, i ≤ k → ∀ q ∈ E '' riemannianBallOf H.metric H.basepoint R,
          ckErr_S45 H g' c f i q ≤ δ) →
        ∀ p ∈ riemannianBallOf H.metric H.basepoint R, ckErr_S45 H g' c (f ∘ E) k p < ε)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ μ ∈ Icc (0 : ℝ) 1,
      ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ k : ℕ, k ≤ max K m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
          1 / (m : ℝ) := by
  have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hQ : ∀ k : ℕ, ∀ᶠ j in atTop, ∀ μ ∈ Icc (0 : ℝ) 1,
      ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
      ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
          1 / (m : ℝ) := by
    intro k
    obtain ⟨δ, hδ, hδc⟩ := hcomp k (2 * m) (1 / (m : ℝ)) hmpos
    filter_upwards [hηt.eventually (eventually_le_nhds hδ),
      hν.eventually (eventually_ge_atTop k),
      hρ.eventually (eventually_ge_atTop (2 * (m : ℝ)))] with j hηδ hνj hρj μ hμ t ht p hp
    have hball : ∀ q ∈ riemannianBallOf H.metric H.basepoint (2 * m),
        q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) := fun q hq =>
      riemannianBallOf_mono _ _ (by linarith) hq
    have hρ0 : (0 : ℝ) ≤ ρ j := by
      have : (0 : ℝ) ≤ 2 * m := by positivity
      linarith
    have himg : ∀ q ∈ (fun x => E j (μ, x)) '' riemannianBallOf H.metric H.basepoint (2 * m),
        q ∈ riemannianBallOf H.metric H.basepoint (4 * ρ j) := by
      rintro q ⟨x, hx, rfl⟩
      exact isotopy_mem_ball_S49 H (E j) (fun μ => (hEb j μ).2.1) (hsupp j) μ
        (r := 4 * ρ j) (by linarith) (hball x hx)
    exact hδc (postMetric F.observation t) t⁻¹ (f j t ht) (fun x => E j (μ, x)) (hEb j μ).1
      (fun i hi q hq => (hEclose j μ hμ i (hi.trans hνj) q (hball q hq)).trans hηδ)
      (fun i hi q hq => ((hacc j t ht).2 i (hi.trans hνj) q (himg q hq)).le.trans hηδ) p hp
  obtain ⟨J, hJ⟩ := eventually_atTop.1
    ((Filter.eventually_all_finset (Finset.range (max K m + 1))).2 (fun k _ => hQ k))
  exact ⟨J, fun j hj μ hμ t ht k hk p hp =>
    hJ j hj k (Finset.mem_range.2 (Nat.lt_succ_of_le hk)) μ hμ t ht p hp⟩

end GC.LongTime.Ch12
