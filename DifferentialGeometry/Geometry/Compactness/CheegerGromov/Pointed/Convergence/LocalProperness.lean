import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Metric.Proper
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import DifferentialGeometry.Geometry.Metric.Comparison.IntrinsicBallImage

set_option autoImplicit false
noncomputable section
universe u uE uH
namespace DifferentialGeometry.CheegerGromovCompactness
open Filter Set
open scoped Manifold ContDiff Topology
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem PointedRiemannianConvergenceMaps.isCompact_closed_ball_of_target_coverage
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {σ : ℕ → ℕ}
    (Φ : PointedRiemannianConvergenceMaps X L σ)
    (P : ∀ k, ProperMetricOn (X.obj (σ k))) {rho : ℝ}
    (hcover : ∀ S : ℝ, 0 < S → S < rho → ∀ᶠ k in atTop,
      riemannianClosedBallOf (X.obj (σ k)).metric (X.obj (σ k)).basepoint S ⊆ Φ.target k)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ x ∈ Φ.source k, ∀ v : TangentSpace I x,
        (X.obj (σ k)).metric.inner (Φ.partialDiffeomorph k x)
          (mfderiv I I (Φ.partialDiffeomorph k) x v)
          (mfderiv I I (Φ.partialDiffeomorph k) x v) ≤
        (1 + ε) * L.metric.inner x v v)
    {R : ℝ} (hR : 0 ≤ R) (hRrho : R < rho) :
    IsCompact (riemannianClosedBallOf L.metric L.basepoint R) := by
  let S := (R + rho) / 2
  have hRS : R < S := by dsimp [S]; linarith
  have hSrho : S < rho := by dsimp [S]; linarith
  have hS : 0 < S := hR.trans_lt hRS
  let T := (R + S) / 2
  have hRT : R < T := by dsimp [T]; linarith
  have hTS : T < S := by dsimp [T]; linarith
  have hT : 0 < T := hR.trans_lt hRT
  let C := S / T
  have hC : 1 < C := (one_lt_div hT).mpr hTS
  have hCR : C * R < S := by
    dsimp [C]
    calc
      S / T * R < S / T * T := mul_lt_mul_of_pos_left hRT (div_pos hS hT)
      _ = S := div_mul_cancel₀ S hT.ne'
  obtain ⟨k, hkcover, hkupper⟩ :=
    ((hcover S hS hSrho).and (hupper (C ^ 2 - 1) (by nlinarith))).exists
  let : TopologicalSpace.MetrizableSpace L.M := Manifold.metrizableSpace I L.M
  let : TopologicalSpace.MetrizableSpace (X.obj (σ k)).M :=
    Manifold.metrizableSpace I (X.obj (σ k)).M
  apply PartialDiffeomorph.isCompact_riemannianClosedBallOf_of_metric_upper
    L.metric (X.obj (σ k)).metric (Φ.partialDiffeomorph k) (Φ.base_mem k)
    hR (by linarith : 0 < C) hCR
  · rw [Φ.basepoint_map k]
    exact (P k).isCompact_riemannianClosedBallOf _ _ _
  · rwa [Φ.basepoint_map k]
  · intro x hx v
    simpa only [add_sub_cancel] using hkupper x hx v

end DifferentialGeometry.CheegerGromovCompactness
