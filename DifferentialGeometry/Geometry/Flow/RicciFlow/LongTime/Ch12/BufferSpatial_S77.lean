import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferLowCurvMicro_S77

/-!
# CH12-S77, group 1c: the spatial half of the buffer estimate

`buffer_spatial_S77`: for `q ∈ B(p, ρ)` and `a ≤ 1/2`, the buffer `B(q, 2 (a ρ))` lies in the doubled ball
`B(p, 2 ρ)`; hence the doubled-ball scalar bound `hZ0` (`R ≤ C₀ / ρ²` on `B(p, 2ρ)`) is a bound on the whole
spatial buffer at time `s.time`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem buffer_spatial_S77 (g : SmoothRiemannianMetric I M) {p q x : M} {ρ a : ℝ} (hρ : 0 < ρ)
    (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hq : q ∈ riemannianBallOf g p ρ)
    (hx : x ∈ riemannianBallOf g q (2 * (a * ρ))) : x ∈ riemannianBallOf g p (2 * ρ) := by
  have htri := riemannianEDistOf_triangle (I := I) g p q x
  have h1 : riemannianEDistOf (I := I) g p q < ENNReal.ofReal ρ := hq
  have h2 : riemannianEDistOf (I := I) g q x < ENNReal.ofReal (2 * (a * ρ)) := hx
  have hsum : ENNReal.ofReal ρ + ENNReal.ofReal (2 * (a * ρ)) ≤ ENNReal.ofReal (2 * ρ) := by
    rw [← ENNReal.ofReal_add hρ.le]
    · apply ENNReal.ofReal_le_ofReal
      nlinarith
    · positivity
  exact lt_of_le_of_lt htri ((ENNReal.add_lt_add h1 h2).trans_le hsum)

theorem buffer_scalar_of_doubled_S77 (g : SmoothRiemannianMetric I M) {p q : M} {ρ a C₀ : ℝ} (hρ : 0 < ρ)
    (ha0 : 0 < a) (ha : a ≤ 1 / 2) (hq : q ∈ riemannianBallOf g p ρ) {f : M → ℝ}
    (hf : ∀ z ∈ riemannianBallOf g p (2 * ρ), f z ≤ C₀ / ρ ^ 2) :
    ∀ x ∈ riemannianBallOf g q (2 * (a * ρ)), f x ≤ C₀ / ρ ^ 2 :=
  fun _ hx => hf _ (buffer_spatial_S77 g hρ ha0 ha hq hx)

end GC.LongTime.Ch12
