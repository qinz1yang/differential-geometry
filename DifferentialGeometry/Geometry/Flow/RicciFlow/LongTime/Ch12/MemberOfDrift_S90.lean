import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverCkErr_S90

set_option autoImplicit false

/-! # CH12-S90 G2: a point within `A < L √(1-δ)` of the image of `B(R - L)` lies in the image of `B(R)`

`member_of_drift_S90`: `f` smooth + injective on the open `U ⊇ B̄(base, R)` with `(1-δ) h ≤ f^*G`;
if `y` is `G`-closer than `A` to `f q` for some `q ∈ B(base, R - L)` and `A < L √(1-δ)`, then
`y ∈ f '' B(base, R)` (the open ball).  This is the covering half of the slow-patch drift
statement `HDd` of `[FROZEN v3] CH12-S72 NEWESC-fin`: drift (a distance statement) ⇒ membership. -/

noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem member_of_drift_S90 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T3Space N] (G : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier)) {δ : ℝ} (hδ : δ < 1)
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - δ) * H.metric.inner p w w ≤
        G.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w))
    {R L A : ℝ} (hL : 0 < L)
    (hRU : riemannianClosedBallOf H.metric H.basepoint R ⊆ (U : Set H.Carrier))
    (hAL : A < L * Real.sqrt (1 - δ)) {y : N}
    (hy : ∃ q ∈ riemannianBallOf H.metric H.basepoint (R - L),
      riemannianEDistOf G (f q) y < ENNReal.ofReal A) :
    y ∈ f '' riemannianBallOf H.metric H.basepoint R := by
  obtain ⟨q, hq, hd⟩ := hy
  have hA : 0 < A := by
    by_contra hA
    rw [ENNReal.ofReal_of_nonpos (not_lt.mp hA)] at hd
    exact absurd hd (by simp)
  have hsq : 0 < Real.sqrt (1 - δ) := Real.sqrt_pos.mpr (by
    by_contra h0
    have : 1 - δ ≤ 0 := not_lt.mp h0
    have : L * Real.sqrt (1 - δ) = 0 := by
      rw [Real.sqrt_eq_zero_of_nonpos this, mul_zero]
    linarith)
  have hRL : 0 < R - L := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hq)
  have hc : A / Real.sqrt (1 - δ) < L := by
    rw [div_lt_iff₀ hsq]; linarith
  set R' : ℝ := (A / Real.sqrt (1 - δ) + (R - L) + R) / 2 with hR'
  have hR1 : A / Real.sqrt (1 - δ) + (R - L) < R' := by rw [hR']; linarith
  have hR2 : R' < R := by rw [hR']; linarith
  have hRU' : riemannianClosedBallOf H.metric H.basepoint R' ⊆ (U : Set H.Carrier) :=
    (riemannianClosedBallOf_mono H.metric H.basepoint hR2.le).trans hRU
  have hcover := ball_cover_of_lower_S90 H G f U hf hinj hδ hlow hRU' hq hR1
  obtain ⟨x, hx, rfl⟩ := hcover hd
  refine ⟨x, ?_, rfl⟩
  have hR0 : 0 < R := by linarith
  exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff hR0).mpr hR2)

end GC.LongTime.Ch12
