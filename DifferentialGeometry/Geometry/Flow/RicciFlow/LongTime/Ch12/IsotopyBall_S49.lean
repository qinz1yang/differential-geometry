import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingPatch_CX5
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ForwardWindowDef_S45

set_option autoImplicit false

/-! # CH12-S49 G3a: `himage` and the space-time exhaustion indices

* `mem_iff_of_fixed_S49`: a bijection fixing the complement of `S` pointwise preserves `S` (both
  directions) — so a support-in-`B(ρ_j)` diffeomorphism `E_j(μ, ·)` of S8 v2 maps `B(4ρ_j)` to itself
  (`himage` of the CX5 constructor with `A j = B(4 ρ_j)`, `U ⊆ B(4 ρ_j)`);
* `exists_exhaustionIndex_S49`: indices `N₀ n` with `n ≤ ρ_j` for `j ≥ N₀ n` (for
  `Ω = exhaustionSpaceTime_CX5 (B(n)) (t_{N₀ n})`; `p₀ ∈ B(n)`, `t₀ > t_{N₀ n}` then give
  `p₀ ∈ B(ρ_j)` for the window `j` of `t₀` and for `j + 1`). -/

noncomputable section
open Set Filter DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature

namespace GC.LongTime.Ch12
universe u

theorem mem_iff_of_fixed_S49 {X : Type*} (e : X → X) (he : Function.Injective e) {S : Set X}
    (hfix : ∀ p, p ∉ S → e p = p) {p : X} : e p ∈ S ↔ p ∈ S := by
  by_cases hp : p ∈ S
  · refine ⟨fun _ => hp, fun _ => ?_⟩
    by_contra h
    have h2 : e p = p := he (hfix _ h)
    exact h (by rw [h2]; exact hp)
  · rw [hfix p hp]

theorem isotopy_mem_ball_S49 (H : FiniteVolumeHyperbolicModel.{u}) (E : ℝ × H.Carrier → H.Carrier)
    {ρ : ℝ}
    (hinj : ∀ μ, Function.Injective fun p => E (μ, p))
    (hsupp : ∀ μ p, p ∉ riemannianBallOf H.metric H.basepoint ρ → E (μ, p) = p) (μ : ℝ) {r : ℝ}
    (hr : ρ ≤ r) {p : H.Carrier} (hp : p ∈ riemannianBallOf H.metric H.basepoint r) :
    E (μ, p) ∈ riemannianBallOf H.metric H.basepoint r := by
  by_cases h : p ∈ riemannianBallOf H.metric H.basepoint ρ
  · exact riemannianBallOf_mono _ _ hr
      ((mem_iff_of_fixed_S49 (fun q => E (μ, q)) (hinj μ) (hsupp μ)).2 h)
  · rw [hsupp μ p h]; exact hp

theorem exists_exhaustionIndex_S49 {ρ : ℕ → ℝ} (hlim : Tendsto ρ atTop atTop) (m : ℕ) :
    ∃ N : ℕ, ∀ j, N ≤ j → (m : ℝ) ≤ ρ j := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually (eventually_ge_atTop (m : ℝ)))
  exact ⟨N, hN⟩

end GC.LongTime.Ch12
