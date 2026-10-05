import DifferentialGeometry.Geometry.Collapse.FiniteSurface.CompactFactorRow
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientationApplications

/-!
# Consumer of the LFR16 row: LFR17 for the factor of the finite limit

`exists_finite_model_surface_factor_sphere_or_flat_torus`: under LFR16's hypotheses (oriented
three-dimensional sources, eventual bounds, residual diameter `≤ D`), the compact factor `Z` of
the SAME finite limit has a smooth carrier that is diffeomorphic to `S²` or to a flat `T²`
(LFR16 → LFR17, `surfaceFactor_sphere_or_flat_torus_of_finite_limit`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold Function Module
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.ExactSplitting
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

universe u w

/-- **LFR16 → LFR17.** The factor of the finite limit is a sphere or a flat torus. -/
theorem exists_finite_model_surface_factor_sphere_or_flat_torus
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) 3)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w}
    [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    ∃ (N : Type) (_ : MetricSpace N) (W : Type) (_ : MetricSpace W)
      (e : N ≃ᵢ WithLp 2 (ℝ × W)) (S : Type) (_ : MetricSpace S) (_ : ChartedSpace E2 S)
      (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      Nonempty (S ≃ₜ {x : N // (e x).fst = 0}) ∧
      (Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
        Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨-, -, N, mN, cN, hMN, G, -, -, oN, hprop, hRiem, hconn, -, -, -, -, -, -, -, hsecG, W, m,
      -, hcpt, hdiam, -, e, -, -, -, -⟩ :=
    exists_finite_model_compact_surface_factor K hK hr hv A g hmetric p o hvol hcurv hη hL hsec Φ
      hδ hD
  let := mN
  let := cN
  let := m
  obtain ⟨S, mS, cS, iS, hc, hconn', ho, hφ, htype⟩ :=
    surfaceFactor_sphere_or_flat_torus_of_finite_limit K hK G hRiem hsecG oN hdiam e
  exact ⟨N, mN, W, m, e, S, mS, cS, iS, hc, hconn', ho, hφ, htype⟩

end DifferentialGeometry.Geometry.Collapse
