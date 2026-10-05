import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryAmbientRay

/-!
Actual intrinsic Jacobi density in dimension three has nonincreasing model-radius ratio
on its alive minimizing domain under Ricci ≥ -2κ²g; no conjugacy or ratio conclusion is assumed.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]
  {H : Type*} [ambientModelTopology : TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [ambientModelBoundary : J.Boundaryless] {N : Type*}
  [ambientTopology : TopologicalSpace N] [ambientCharts : ChartedSpace H N]
  [ambientSmooth : IsManifold J ∞ N] [ambientT2 : T2Space N]
  [ambientSigma : SigmaCompactSpace N]
  [ambientBundle : RiemannianBundle (fun x : N => TangentSpace J x)]
  [ambientDistance : PseudoEMetricSpace N] [ambientComplete : CompleteSpace N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem boundary_ambient_jacobi_ratio [ambientRiemannian : IsRiemannianManifold J N]
    [ambientMetricContinuous : IsContinuousRiemannianBundle E (fun x : N => TangentSpace J x)]
    (g : SmoothRiemannianMetric J N) (hEnorm : IsMetricNorm g) (p : N)
    (u : TangentSpace J p) (κ L : ℝ) (hdim : Module.finrank ℝ E = 3)
    (hunit : g.inner p u u = 1)
    (v : Fin (Module.finrank ℝ E - 1) → TangentSpace J p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hRic : let γ := intrinsicGeodesic g hEnorm p u
      ∀ t ∈ boundaryRayDomain g p γ ∩ Ioo (0 : ℝ) L,
        -2 * κ ^ 2 * g.inner (γ t) (curveVelocity γ t) (curveVelocity γ t) ≤
          ricciTensor g (γ t) (curveVelocity γ t) (curveVelocity γ t)) :
    let γ := intrinsicGeodesic g hEnorm p u
    let V := fun i => intrinsicJacobi g hEnorm p u (v i)
    AntitoneOn (fun t => curveDensity g γ V t / modelRadius (-κ ^ 2) t ^ 2)
      (boundaryRayDomain g p γ ∩ Ioo (0 : ℝ) L) := by
  let γ := intrinsicGeodesic g hEnorm p u
  let V := fun i => intrinsicJacobi g hEnorm p u (v i)
  change AntitoneOn (fun t => curveDensity g γ V t / modelRadius (-κ ^ 2) t ^ 2)
    (boundaryRayDomain g p γ ∩ Ioo (0 : ℝ) L)
  intro a ha b hb hab
  obtain ⟨hbpos, T, hbT, hprefix⟩ := hb.1
  let Q : ℝ := min T L
  have hbQ : b < Q := lt_min hbT hb.2.2
  have haQ : a < Q := hab.trans_lt hbQ
  have halive : ∀ s ∈ Ioo (0 : ℝ) Q, s ∈ boundaryRayDomain g p γ := by
    intro s hs
    exact ⟨hs.1, T, hs.2.trans_le (min_le_left _ _), hprefix⟩
  have hno : ∀ s ∈ Ioo (0 : ℝ) Q,
      ¬ IsConjVec g hEnorm p ((s • u : TangentSpace J p) : E) := by
    intro s hs
    exact boundary_ambient_ray_no_conjugate g hEnorm p u hunit s (halive s hs)
  have hadm : ∀ s ∈ Ioo (0 : ℝ) Q, modelRadiusAdmissible (-κ ^ 2) s := by
    intro s hs
    refine ⟨hs.1, ?_⟩
    intro hbad
    exact False.elim ((not_lt_of_ge (neg_nonpos.mpr (sq_nonneg κ))) hbad)
  have hRicQ :
      ∀ s ∈ Ioo (0 : ℝ) Q,
        (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-κ ^ 2)) *
          g.inner (γ s) (curveVelocity γ s) (curveVelocity γ s) ≤
        ricciTensor g (γ s) (curveVelocity γ s) (curveVelocity γ s) := by
    intro s hs
    have hh := hRic s ⟨halive s hs, hs.1, hs.2.trans_le (min_le_right _ _)⟩
    convert hh using 1
    simp only [hdim, Nat.reduceSub, Nat.cast_ofNat]
    ring
  have hratio := intrModelRatioOfFrame_on g hEnorm p u (-κ ^ 2) Q hunit
    (by rw [hdim]; norm_num) hadm v hON hperp hno hRicQ
  have hle := hratio ⟨ha.2.1, haQ⟩ ⟨hb.2.1, hbQ⟩ hab
  simpa only [modelDensity, hdim, Nat.reduceSub, γ, V] using hle

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
