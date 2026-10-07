import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61

set_option autoImplicit false

/-! # CH12-S61 G2d: shrinking the exhaustion domain so that each slice lies in the ball `B(ρ_{j(t)})`
(needed for `singleModel_S61`: the smoothed map `f j t ∘ E j (θ, ·)` is only controlled on `B(4ρ_j)`).
`Ω'' := Ω ⊓ exhaustionSpaceTime_CX5 (B(ρ_j)) (t_j)`; it keeps the exhaustion property, and patches for
`Ω'' ≤ Ω` come from the `∀ Ω' ≤ Ω` clause of `persistentModelPatch_of_windows_S61`. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12
universe u

theorem exists_slice_in_ball_S61 (H : FiniteVolumeHyperbolicModel.{u}) {T : ℝ} (hT : 0 < T)
    (ρ : ℕ → ℝ) (hρm : Monotone ρ) (hρ : Tendsto ρ atTop atTop)
    (Ω : TopologicalSpace.Opens (ℝ × H.Carrier))
    (hΩ : ∀ m : ℕ, ∃ τ : ℝ, ∀ t, τ < t →
      riemannianBallOf H.metric H.basepoint m ⊆ sourceSlice_CX5 Ω t) :
    ∃ Ω'' : TopologicalSpace.Opens (ℝ × H.Carrier), Ω'' ≤ Ω ∧
      (∀ m : ℕ, ∃ τ : ℝ, ∀ t, τ < t →
        riemannianBallOf H.metric H.basepoint m ⊆ sourceSlice_CX5 Ω'' t) ∧
      ∀ t, T ≤ t → (sourceSlice_CX5 Ω'' t : Set H.Carrier) ⊆
        riemannianBallOf H.metric H.basepoint (ρ (dyadicIndex_CX5 T t)) := by
  let Ub : ℕ → TopologicalSpace.Opens H.Carrier := fun j =>
    ⟨riemannianBallOf H.metric H.basepoint (ρ j), isOpen_riemannianBallOf_S61 H _⟩
  let Ωe := exhaustionSpaceTime_CX5 Ub (fun j => dyadicTime_CX5 T j)
  refine ⟨Ω ⊓ Ωe, inf_le_left, ?_, ?_⟩
  · intro m
    obtain ⟨τ, hτ⟩ := hΩ m
    obtain ⟨N, hN⟩ := exists_exhaustionIndex_S49 hρ m
    refine ⟨max τ (dyadicTime_CX5 T N), fun t ht p hp => ?_⟩
    refine ⟨hτ t ((le_max_left _ _).trans_lt ht) hp, ?_⟩
    exact exhaustionSpaceTime_contains_CX5 Ub (fun j => dyadicTime_CX5 T j) N
      ((le_max_right _ _).trans_lt ht)
      (riemannianBallOf_mono _ _ (hN N le_rfl) hp)
  · intro t ht p hp
    have hp2 : (t, p) ∈ ⋃ n, Ioi (dyadicTime_CX5 T n) ×ˢ (Ub n : Set H.Carrier) := hp.2
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hp2
    exact riemannianBallOf_mono _ _ (hρm (le_dyadicIndex_CX5 hT j hj.1.le)) hj.2

end GC.LongTime.Ch12
