import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkThreshold_S61

set_option autoImplicit false

/-! # CH12-S61 G2c: `α`, the speed budget and the `ckErr` clause of sheet S4 (from inline `hcomp`)

`exists_alpha_ckErr_S61`: one diagonal `α` (positive, antitone from `start`, tending to 0) with
`α t = 1/m`, the G3 speed budget `4 B η_j < α t`, and the S4 clause
`ckErr < α t` for `k ≤ max K ⌈(α t)⁻¹⌉₊` on `B(2 (α t)⁻¹)`, for the time-smoothed maps
`x ↦ f j t (E j (μ, x))` (every `μ ∈ [0,1]`, in particular `μ = θ(t / t_j)`). -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem exists_alpha_ckErr_S61 {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T) (K : ℕ) (B : ℝ)
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
    :
    ∃ (start : ℝ) (α : ℝ → ℝ), T ≤ start ∧ (∀ t, 0 < α t) ∧ AntitoneOn α (Ici start) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T' : ℝ, ∀ t, T' ≤ t → α t < ε) ∧
      (∀ t, start ≤ t → 4 * B * η (dyadicIndex_CX5 T t) < α t) ∧
      ∀ t, start ≤ t → ∀ μ ∈ Icc (0 : ℝ) 1,
        ∀ ht : t ∈ Icc (dyadicTime_CX5 T (dyadicIndex_CX5 T t))
          (dyadicTime_CX5 T (dyadicIndex_CX5 T t + 1)),
        ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
          ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * (α t)⁻¹),
            ckErr_S45 H (postMetric F.observation t) t⁻¹
              (fun x => f (dyadicIndex_CX5 T t) t ht (E (dyadicIndex_CX5 T t) (μ, x))) k p < α t := by
  classical
  have hth := smoothed_ckErr_threshold_S61 F H K f E η ρ ν hηt hρ hν hEb hsupp hEclose hacc hcomp
  obtain ⟨start, α, hstart, hpos, hanti, hdec, hkey⟩ := exists_diagonal_alpha_S61 hT
    (fun m j => 1 ≤ m → (4 * B * η j < 1 / (m : ℝ) ∧
      ∀ μ ∈ Icc (0 : ℝ) 1, ∀ t (ht : t ∈ Icc (dyadicTime_CX5 T j) (dyadicTime_CX5 T (j + 1))),
        ∀ k : ℕ, k ≤ max K m → ∀ p ∈ riemannianBallOf H.metric H.basepoint (2 * m),
          ckErr_S45 H (postMetric F.observation t) t⁻¹ (fun x => f j t ht (E j (μ, x))) k p <
            1 / (m : ℝ)))
    (fun m => by
      by_cases hm : 1 ≤ m
      · obtain ⟨J, hJ⟩ := hth m hm
        have hmpos : (0 : ℝ) < 1 / (m : ℝ) := by
          have : (0 : ℝ) < m := by exact_mod_cast hm
          positivity
        obtain ⟨J2, hJ2⟩ := eventually_atTop.1
          ((hηt.const_mul (4 * B)).eventually (eventually_lt_nhds (a := (4 * B) * 0) (b := 1 / (m : ℝ))
            (by simpa using hmpos)))
        exact ⟨max J J2, fun j hj _ => ⟨hJ2 j ((le_max_right _ _).trans hj),
          hJ j ((le_max_left _ _).trans hj)⟩⟩
      · exact ⟨0, fun j _ h => absurd h hm⟩)
  refine ⟨start, α, hstart, hpos, hanti, hdec, ?_, ?_⟩
  · intro t ht
    obtain ⟨m, hm, hαm, hP⟩ := hkey t ht
    rw [hαm]; exact (hP hm).1
  · intro t ht μ hμ hw k hk p hp
    obtain ⟨m, hm, hαm, hP⟩ := hkey t ht
    have hinv : (α t)⁻¹ = (m : ℝ) := by rw [hαm]; simp
    have hceil : ⌈(α t)⁻¹⌉₊ = m := by rw [hinv]; exact Nat.ceil_natCast m
    rw [hceil] at hk
    rw [hinv] at hp
    rw [hαm]
    exact (hP hm).2 μ hμ t hw k hk p hp

end GC.LongTime.Ch12
