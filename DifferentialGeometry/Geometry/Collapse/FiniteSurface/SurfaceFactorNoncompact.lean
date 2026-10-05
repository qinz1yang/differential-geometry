import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceFactor

/-!
The actual surface factor of an exact line splitting needs no compact residual factor.
The same zero slice, finite atlas, induced metric, and product diffeomorphism are retained.
Compactness and a diameter bound enter only the separate compact consumer.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "P" => Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ

local instance surfaceFactorNoncompact_finrank : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

section Kernel

variable {N W : Type*} [metricN : MetricSpace N] [chartsN : ChartedSpace E3 N]
  [manifoldN : IsManifold 𝓘(ℝ, E3) ∞ N]
  [bundleN : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
  [riemannianN : IsRiemannianManifold 𝓘(ℝ, E3) N]
  [completeN : CompleteSpace N] [metricW : MetricSpace W] {r : ℕ∞}

theorem surfaceFactor_of_exactSplitting_noncompact [connectedN : ConnectedSpace N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI _factorCharts := splittingFactorChartedSpace G hr hnorm e
    letI _factorManifold := splittingFactor_isManifold_one G hr hnorm e
    Module.finrank ℝ E3 - Module.finrank ℝ ℝ = 2 ∧
    ConnectedSpace {x : N // (e x).fst = 0} ∧
    (𝓘(ℝ, P)).Boundaryless ∧
    IsManifold 𝓘(ℝ, P) ((r : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (letI _factorMetric :
        RiemannianBundle (TangentSpace 𝓘(ℝ, P) : {x : N // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric G hr hnorm e).toRiemannianMetric⟩
     IsRiemannianManifold 𝓘(ℝ, P) {x : N // (e x).fst = 0}) ∧
    (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
      0 ≤ (inducedMetric G hr hnorm e).sectionalCurvature z v w) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e) ∧
    ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e).symm ∧
    (∀ (p : ℝ × {x : N // (e x).fst = 0})
      (v w : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) p),
      G.inner (splittingProductDiffeomorph G hr hnorm e p)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G hr hnorm e) p v)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric G hr hnorm e).inner p.2 v.2 w.2) := by
  let factorCharts := splittingFactorChartedSpace G hr hnorm e
  let factorManifold := splittingFactor_isManifold_one G hr hnorm e
  have hs := exactSplitting_regularity G hr hnorm e
  exact ⟨finrank_euclidean_three_sub_one, hs.2.2.2.2.2.2.2.2.1 connectedN,
    inferInstance, hs.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hsec,
    hs.2.2.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.2.2.1,
    hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩


theorem compactSurfaceFactor_from_noncompact [connectedN : ConnectedSpace N]
    [compactW : CompactSpace W]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((r : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    {D : ℝ} (hD : ∀ a b : W, dist a b ≤ D) (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI _factorCharts := splittingFactorChartedSpace G hr hnorm e
    letI _factorManifold := splittingFactor_isManifold_one G hr hnorm e
    Module.finrank ℝ E3 - Module.finrank ℝ ℝ = 2 ∧
    CompactSpace {x : N // (e x).fst = 0} ∧
    ConnectedSpace {x : N // (e x).fst = 0} ∧
    (∀ z z' : {x : N // (e x).fst = 0}, dist z z' ≤ D) ∧
    (𝓘(ℝ, P)).Boundaryless ∧
    IsManifold 𝓘(ℝ, P) ((r : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (letI _factorMetric :
        RiemannianBundle (TangentSpace 𝓘(ℝ, P) : {x : N // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric G hr hnorm e).toRiemannianMetric⟩
     IsRiemannianManifold 𝓘(ℝ, P) {x : N // (e x).fst = 0}) ∧
    (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
      0 ≤ (inducedMetric G hr hnorm e).sectionalCurvature z v w) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e) ∧
    ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) ((r : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G hr hnorm e).symm ∧
    (∀ (p : ℝ × {x : N // (e x).fst = 0})
      (v w : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) p),
      G.inner (splittingProductDiffeomorph G hr hnorm e p)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G hr hnorm e) p v)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G hr hnorm e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric G hr hnorm e).inner p.2 v.2 w.2) := by
  let factorCharts := splittingFactorChartedSpace G hr hnorm e
  let factorManifold := splittingFactor_isManifold_one G hr hnorm e
  rcases surfaceFactor_of_exactSplitting_noncompact G hr hnorm hsec e with
    ⟨hdim, hconn, hboundary, hmanifold, hmetric, hcurvature, hforward, hinverse, hpullback⟩
  let residual := splittingFactorEquiv e
  refine ⟨hdim, residual.toHomeomorph.compactSpace, hconn, ?_, hboundary, hmanifold,
    hmetric, hcurvature, hforward, hinverse, hpullback⟩
  intro z z'
  calc
    dist z z' = dist (residual.symm z) (residual.symm z') :=
      (residual.symm.dist_eq z z').symm
    _ ≤ D := hD (residual.symm z) (residual.symm z')

end Kernel

section FiniteLimit

variable {N W : Type*} [metricN : MetricSpace N] [chartsN : ChartedSpace E3 N]
  [manifoldN : IsManifold 𝓘(ℝ, E3) ∞ N] [metricW : MetricSpace W]

theorem surfaceFactor_of_finite_limit_noncompact [properN : ProperSpace N]
    [connectedN : ConnectedSpace N] (K : ℕ) (hK : 4 ≤ K)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) ((K - 1 : ℕ) : ℕ∞ω) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hRiem : letI _ambientMetric :
        RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E3) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI _ambientMetric :
      RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
    let G' := finiteMetricReindex K hK G
    let hr' := two_le_reindex K hK
    let hnorm' := finiteMetricReindex_enorm K hK G
    letI _factorCharts := splittingFactorChartedSpace G' hr' hnorm' e
    letI _factorManifold := splittingFactor_isManifold_one G' hr' hnorm' e
    Module.finrank ℝ E3 - Module.finrank ℝ ℝ = 2 ∧
    ConnectedSpace {x : N // (e x).fst = 0} ∧
    (𝓘(ℝ, P)).Boundaryless ∧
    IsManifold 𝓘(ℝ, P) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
    (letI _factorMetric :
        RiemannianBundle (TangentSpace 𝓘(ℝ, P) : {x : N // (e x).fst = 0} → Type _) :=
      ⟨(inducedMetric G' hr' hnorm' e).toRiemannianMetric⟩
     IsRiemannianManifold 𝓘(ℝ, P) {x : N // (e x).fst = 0}) ∧
    (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
      0 ≤ (inducedMetric G' hr' hnorm' e).sectionalCurvature z v w) ∧
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G' hr' hnorm' e) ∧
    ContMDiff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
      (splittingProductDiffeomorph G' hr' hnorm' e).symm ∧
    (∀ (p : ℝ × {x : N // (e x).fst = 0})
      (v w : TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) p),
      G'.inner (splittingProductDiffeomorph G' hr' hnorm' e p)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G' hr' hnorm' e) p v)
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3)
          (splittingProductDiffeomorph G' hr' hnorm' e) p w) =
      inner ℝ v.1 w.1 + (inducedMetric G' hr' hnorm' e).inner p.2 v.2 w.2) := by
  let ambientMetric : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) :=
    ⟨G.toRiemannianMetric⟩
  let ambientRiemannian : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  exact surfaceFactor_of_exactSplitting_noncompact (finiteMetricReindex K hK G)
    (two_le_reindex K hK) (finiteMetricReindex_enorm K hK G) (fun x v w => hsec x v w) e

end FiniteLimit

end DifferentialGeometry.Geometry.Collapse
