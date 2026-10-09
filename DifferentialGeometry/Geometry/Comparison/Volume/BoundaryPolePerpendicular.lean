import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Orthogonality

/-!
The actual pole angular field and its covariant derivative have their initial radial pairings.
Initial directions orthogonal to the pole velocity therefore remain radial-orthogonal.
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

theorem boundaryPoleJacobiLinear_velocity_pairing
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E) (t : ℝ)
    (ht : ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain) :
    G.inner (boundaryPoleFlowFamily G y v t)
        (boundaryPoleJacobiLinear (E := E) G y v t w)
        (curveVelocity (I := 𝓘(ℝ, E)) (boundaryPoleFlowFamily G y v) t) = t * G.inner y w v ∧
      G.inner (boundaryPoleFlowFamily G y v t)
        (covDerivAlong G (boundaryPoleFlowFamily G y v)
          (fun r => boundaryPoleJacobiLinear (E := E) G y v r w) t)
        (curveVelocity (I := 𝓘(ℝ, E)) (boundaryPoleFlowFamily G y v) t) = G.inner y w v := by
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
  have hγ (a : ℝ) (ha : a ∈ s) : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) 2 γ a :=
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
  have hgeo : DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesicOn G γ
      (interior s) := by
    intro a ha
    have ham : a ∈ s := interior_subset ha
    have hi := Bundle.ContMDiffRiemannianMetric.isGeodesicOnWithInitial_geodesicFlow G y v
    exact (hi.isGeodesicAt
      (isOpen_maximalIntegralCurveInterval.mem_nhds ham)).hasGeodesicEquationAt
  have hvel : (curveVelocity (I := 𝓘(ℝ, E)) γ 0 : E) = v := by
    have hMF : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) γ 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight v) :=
      (boundaryPoleFlowFamily_initial (E := E) G y v).2.hasFDerivAt.hasMFDerivAt
    have hh := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hMF.mfderiv
    change (curveVelocity (I := 𝓘(ℝ, E)) γ 0 : E) = (1 : ℝ) • v at hh
    simpa only [one_smul] using hh
  have hbase : γ 0 = y := (boundaryPoleFlowFamily_initial (E := E) G y v).1
  have hinit := boundaryPoleJacobiLinear_initial (E := E) G y v w
  have hstart : G.inner (γ 0)
      (covDerivAlong G γ (fun r => boundaryPoleJacobiLinear (E := E) G y v r w) 0)
      (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = G.inner y w v := by
    rw [hinit.2, hvel, hbase]
  have hinnerZero : G.inner (γ 0) (0 : E)
      (curveVelocity (I := 𝓘(ℝ, E)) γ 0) = 0 := by
    have hz := (G.inner (γ 0)).map_zero
    have hzApplied := congrArg
      (fun A : TangentSpace 𝓘(ℝ, E) (γ 0) →L[ℝ] ℝ =>
        A (curveVelocity (I := 𝓘(ℝ, E)) γ 0)) hz
    exact hzApplied
  have hlinear := inner_curveVelocity_eq_add_mul_of_isJacobiAt G γ
    (fun r => boundaryPoleJacobiLinear (E := E) G y v r w)
    hs hγ hgeo (hJ w) (hDJ w) (hJac w) (a := 0) (t := t) hzero ht
  have hderiv := inner_covDerivAlong_curveVelocity_eq_of_isJacobiAt G γ
    (fun r => boundaryPoleJacobiLinear (E := E) G y v r w)
    hs hγ hgeo (hJ w) (hDJ w) (hJac w) (a := 0) (t := t) hzero ht
  refine ⟨?_, hderiv.trans hstart⟩
  simp only [hinit.1, hinnerZero, zero_add, sub_zero, hstart] at hlinear
  exact hlinear

theorem boundaryPoleJacobiLinear_perpendicular
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (y v w : E)
    (hperp : G.inner y w v = 0) (t : ℝ)
    (ht : ((⟨y, v⟩ : TangentBundle 𝓘(ℝ, E) E), t) ∈ G.geodesicFlowDomain) :
    G.inner (boundaryPoleFlowFamily G y v t)
        (boundaryPoleJacobiLinear (E := E) G y v t w)
        (curveVelocity (I := 𝓘(ℝ, E)) (boundaryPoleFlowFamily G y v) t) = 0 ∧
      G.inner (boundaryPoleFlowFamily G y v t)
        (covDerivAlong G (boundaryPoleFlowFamily G y v)
          (fun r => boundaryPoleJacobiLinear (E := E) G y v r w) t)
        (curveVelocity (I := 𝓘(ℝ, E)) (boundaryPoleFlowFamily G y v) t) = 0 := by
  have hh := boundaryPoleJacobiLinear_velocity_pairing (E := E) G y v w t ht
  simpa only [hperp, mul_zero] using hh

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
