import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Orthogonality

/-!
The actual pole angular derivative has zero Jacobi Wronskian at every existing ray time.
Its initial zero values and genuine smooth Jacobi equation supply the invariant directly.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

theorem boundaryPoleJacobiLinear_wronskian_zero
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w z : E) (t : ℝ)
    (ht : ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain) :
    jacobiWronskian G (boundaryPoleFlowFamily G y v)
      (fun r => boundaryPoleJacobiLinear (E := E) G y v r w)
      (fun r => boundaryPoleJacobiLinear (E := E) G y v r z) t = 0 := by
  let γ := boundaryPoleFlowFamily G y v
  let s := maximalIntegralCurveInterval G.geodesicSpray
    (⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E)
  have hzero : (0 : ℝ) ∈ s := G.mem_geodesicFlowDomain_zero (r := ⊤) le_top _
  have hs : Convex ℝ s := ordConnected_maximalIntegralCurveInterval.convex
  have hfield (u : E) (a : ℝ) (ha : a ∈ s) :
      ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
        (fun r => (⟨γ r, boundaryPoleJacobiLinear (E := E) G y v r u⟩ :
          TangentBundle 𝓘(ℝ, E) E)) a :=
    (boundaryPoleJacobiLinear_jacobi (E := E) G y v u a ha).2
  have hγ (a : ℝ) (ha : a ∈ s) : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 1 γ a :=
    ((contMDiff_proj (TangentSpace 𝓘(ℝ, E) : E → Type _)).contMDiffAt.comp a
      (hfield 0 a ha)).of_le (by norm_num)
  have hJ (u : E) (a : ℝ) (ha : a ∈ s) :
      MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent
        (fun r => (⟨γ r, boundaryPoleJacobiLinear (E := E) G y v r u⟩ :
          TangentBundle 𝓘(ℝ, E) E)) a :=
    (hfield u a ha).mdifferentiableAt (by simp)
  have hDJ (u : E) (a : ℝ) (ha : a ∈ s) :
      MDifferentiableAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent
        (fun r => (⟨γ r, covDerivAlong G γ
          (fun r => boundaryPoleJacobiLinear (E := E) G y v r u) r⟩ :
          TangentBundle 𝓘(ℝ, E) E)) a := by
    have hregular := contMDiffAt_covDerivAlong G (m := 1) (n := 2)
      (by norm_num) ((hfield u a ha).of_le (by norm_num))
    exact hregular.mdifferentiableAt (by norm_num)
  have hJac (u : E) (a : ℝ) (ha : a ∈ interior s) :
      IsJacobiAt G γ (fun r => boundaryPoleJacobiLinear (E := E) G y v r u) a := by
    have ham : a ∈ s := interior_subset ha
    exact (boundaryPoleJacobiLinear_jacobi (E := E) G y v u a ham).1
  exact jacobiWronskian_eq_zero_of_isJacobiAt G γ
    (fun r => boundaryPoleJacobiLinear (E := E) G y v r w)
    (fun r => boundaryPoleJacobiLinear (E := E) G y v r z)
    hs hγ (hJ w) (hJ z) (hDJ w) (hDJ z) (hJac w) (hJac z) hzero ht
    (boundaryPoleJacobiLinear_initial (E := E) G y v w).1
    (boundaryPoleJacobiLinear_initial (E := E) G y v z).1

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
