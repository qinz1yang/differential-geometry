import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N] [PreconnectedSpace N]

private local instance comparisonDistanceC1 : IsManifold I3 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

theorem eventually_metricDistance_bounds_on_compact_of_comparisons
    {ι : Type*} {l : Filter ι} {M : ι → Type v}
    [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)]
    (h : ℝ → SmoothRiemannianMetric I3 N) (g : ∀ i, ℝ → SmoothRiemannianMetric I3 (M i))
    (F : ∀ i, PartialDiffeomorph I3 I3 N (M i) ∞)
    {times : Set ℝ} {s eps : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    (hcomplete : RiemannianMetricComplete (h s))
    (hcompare : ∀ K : Set N, IsCompact K → ∀ᶠ i in l, K ⊆ (F i).source ∧
      Nonempty (MetricComparisonOn h (g i) (F i) K times 0 eps))
    {K : Set N} (hK : IsCompact K) :
    ∀ᶠ i in l, ∀ a ∈ K, ∀ b ∈ K,
      Real.sqrt (1 - eps) * metricDistance (h s) a b ≤ metricDistance (g i s) (F i a) (F i b) ∧
        metricDistance (g i s) (F i a) (F i b) ≤ Real.sqrt (1 + eps) * metricDistance (h s) a b := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨p, hp⟩ := hne
  have hcont : Continuous (fun x : N => (riemannianEDistOf (h s) p x).toReal) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (h s) p x)).comp
      (continuous_riemannianEDist (h s) p).continuousAt
  obtain ⟨B, hB⟩ := hK.bddAbove_image hcont.continuousOn
  let rho := max B 0 + 1
  have hrho : 0 < rho := by dsimp only [rho]; linarith [le_max_right B 0]
  have hKR : K ⊆ riemannianClosedBallOf (h s) p rho := by
    intro x hx
    apply (ENNReal.toReal_le_toReal (riemannianEDistOf_ne_top (h s) p x)
      ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hrho.le]
    exact (hB ⟨x, hx, rfl⟩).trans (by dsimp only [rho]; linarith [le_max_left B 0])
  have hm : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith)
  let R := (Real.sqrt (1 + eps) * (3 * rho) + 1) / Real.sqrt (1 - eps)
  have hR : 0 < R := by dsimp only [R]; positivity
  have hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R := by
    dsimp only [R]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  have hball := hcomplete.closedEBall_isCompact p R
  filter_upwards [hcompare _ hball] with i hi
  obtain ⟨hsource, ⟨C⟩⟩ := hi
  have hequiv : ∀ y ∈ riemannianClosedBallOf (h s) p R, ∀ v : TangentSpace I3 y,
      (1 - eps) * (h s).inner y v v ≤ (g i s).inner (F i y)
        (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ∧
      (g i s).inner (F i y) (mfderiv I3 I3 (F i) y v) (mfderiv I3 I3 (F i) y v) ≤
        (1 + eps) * (h s).inner y v v := by
    intro y hy v
    have hh := C.equivalence s hs y hy v
    rwa [C.pullback_eq s y hy (fun _ => v)] at hh
  intro a ha b hb
  exact crossModel_metricDistance_transfer (h s) (g i s) (F i) p hR heps heps1 hrho.le
    hball hsource hequiv hroom a (hKR ha) b (hKR hb)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
