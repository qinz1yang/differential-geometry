import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessCaptureReserve


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M]

private local instance comparisonConstructionC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)


def metricComparisonOnOfGenuineTimeTowers
    (h : ℝ → SmoothRiemannianMetric I N) (g : ℝ → SmoothRiemannianMetric I3 M)
    (F : N → M) (U : Set N) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J) (order : ℕ) (eps : ℝ)
    (A B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      A 0 s y v = (g s).inner (F y) (mfderiv I I3 F y (v 0)) (mfderiv I I3 F y (v 1)))
    (hB₀ : ∀ s y, ∀ v : Fin 2 → TangentSpace I y, B 0 s y v = (h s).inner y (v 0) (v 1))
    (hA : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) J s)
    (hbound : ∀ a b, a + 2 * b ≤ order → ∀ s ∈ J, ∀ y ∈ U,
      tensor02CovDerivNormWith a (A b s - B b s) (h s) (h s) y ≤ eps) :
    MetricComparisonOn h g F U J order eps where
  pullback s := A 0 s
  pullback_eq := hA₀
  jet q s := A q s - B q s
  jet_zero := by
    intro s y v
    change A 0 s y v - B 0 s y v = _
    rw [hB₀]
  jet_succ := by
    intro q s hs y hy v
    have hd := ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hA q s hs y hy)).sub
      ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        s (hB q s hs y hy))
    exact (hd.derivWithin (hJ s hs)).symm
  equivalence := by
    intro s hs y hy v
    apply quadratic_comparison_of_error_norm (h s) (A 0 s) (A 0 s - B 0 s) y ?_
      (hbound 0 0 (by simp) s hs y hy) v
    intro w
    change A 0 s y w - B 0 s y w = _
    rw [hB₀]
  close := hbound


theorem MetricComparisonOn.exists_source_capture_reserve
    (h : ℝ → SmoothRiemannianMetric I N) (g : ℝ → SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I I3 N M ∞) (p : N)
    {J : Set ℝ} (hzero : (0 : ℝ) ∈ J) {order : ℕ} {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1)
    (C : MetricComparisonOn h g F (riemannianClosedBallOf (h 0) p (modelRadius eps)) J order eps)
    (hcompact : IsCompact (riemannianClosedBallOf (h 0) p (modelRadius eps)))
    (hsource : riemannianClosedBallOf (h 0) p (modelRadius eps) ⊆ F.source) :
    ∃ eta : ℝ, 0 < eta ∧
      riemannianClosedBallOf (g 0) (F p) (modelRadius eps - 1 + eta) ⊆
        F '' riemannianClosedBallOf (h 0) p (modelRadius eps) := by
  let R := modelRadius eps
  let L := (Real.sqrt (1 - eps))⁻¹
  have hR : 0 < R := inv_pos.mpr (Real.sqrt_pos.mpr heps)
  have hL : 0 < L := inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hgap : R - 1 < R / L := by
    simpa only [R, L, div_inv_eq_mul] using modelRadius_sub_one_lt_captureRadius heps heps1
  let eta := (R / L - (R - 1)) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hr : R - 1 + eta < R / L := by dsimp only [eta]; linarith
  have hlower : ∀ y ∈ riemannianClosedBallOf (h 0) p R, ∀ v : TangentSpace I y,
      (h 0).inner y v v ≤ L ^ 2 * (g 0).inner (F y)
        (mfderiv I I3 F y v) (mfderiv I I3 F y v) := by
    intro y hy v
    have hh := (C.equivalence 0 hzero y hy v).1
    rw [C.pullback_eq 0 y hy (fun _ => v)] at hh
    have hfactor : L ^ 2 * (1 - eps) = 1 := by
      dsimp only [L]
      rw [inv_pow, Real.sq_sqrt (by linarith)]
      exact inv_mul_cancel₀ (by linarith)
    calc
      _ = L ^ 2 * ((1 - eps) * (h 0).inner y v v) := by
        rw [← mul_assoc, hfactor, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (sq_nonneg L)
  exact ⟨eta, heta, closedBall_subset_image_of_metric_lower_crossModel
    (h 0) (g 0) F p hR hL hr hcompact hsource hlower⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
