import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCornerRayContinuationOX124
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Geometry.Metric.Euclidean

/-!
# Consumer of O-X124 G2 on the actual Euclidean half-space

The original corner metric is the Euclidean metric on `EuclideanHalfSpace 3` (pulled back by the
model embedding), the pole is the boundary point `0`, the velocity is the genuinely inward unit
vector (normalized `inwardCoordE`), and the orthonormal normal family is any one produced by
`exists_perp_pos` for the actual complete chart metric. The continuation binding then yields an
actual `k`-parallel orthonormal frame normal to the actual phase curve on `(-a, T)` for the
admissible `T = (L - a) / 2`, equal to the chart pole frame near the pole.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison.CornerRayContConsumerOX124

private instance halfT2C_OX124 : T2Space (EuclideanHalfSpace 3) := by
  unfold EuclideanHalfSpace
  infer_instance

private instance halfDimensionC_OX124 :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) := ⟨by simp⟩

private def halfMetricC_OX124 : SmoothRiemannianMetric (𝓡∂ 3) (EuclideanHalfSpace 3) :=
  (DifferentialGeometry.euclideanMetric (E := EuclideanSpace ℝ (Fin 3))).pullback
    (𝓡∂ 3) (𝓡∂ 3).contMDiff (fun p => by
      rw [(𝓡∂ 3).hasMFDerivAt.mfderiv]
      exact Function.injective_id)

private theorem halfInfinityC_OX124 : (∞ : WithTop ℕ∞) ≠ 0 := by simp

private abbrev halfInteriorC_OX124 : Opens (EuclideanHalfSpace 3) :=
  Manifold.intrinsicInterior (𝓡∂ 3) ∞ halfInfinityC_OX124

private abbrev halfYC_OX124 : EuclideanSpace ℝ (Fin 3) :=
  extChartAt (𝓡∂ 3) (0 : EuclideanHalfSpace 3) 0

private abbrev halfVC_OX124 : EuclideanSpace ℝ (Fin 3) :=
  HasSmoothBoundary.inwardCoordE (𝓡∂ 3)

/-- On the actual half-space corner, a genuinely inward unit ray from the boundary pole carries a
`k`-parallel orthonormal frame normal to its velocity on a positive phase interval containing the
seed time `0` (the pole being at phase time `-a`). -/
theorem halfSpace_corner_ray_frame_continuation_OX124 :
    let _interiorCharts := Manifold.interiorChartedSpace (𝓡∂ 3) ∞ (M := halfInteriorC_OX124)
    let _interiorSmooth := Manifold.interiorIsManifold (𝓡∂ 3) ∞ (M := halfInteriorC_OX124)
    let k := boundaryInteriorAtlasMetric halfMetricC_OX124
    ∃ a T : ℝ, 0 < a ∧ 0 < T ∧
    ∃ σ : EuclideanSpace ℝ (Fin 3) → TangentBundle (𝓡 3) halfInteriorC_OX124,
    ∃ v : EuclideanSpace ℝ (Fin 3),
    ∃ F : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) → ∀ r : ℝ,
      TangentSpace (𝓡 3) (boundaryPhasePoint k σ v r),
      (∀ r ∈ Icc (0 : ℝ) T, (σ v, r) ∈ k.geodesicFlowDomain) ∧
      (∀ i r, r ∈ Ioo (-a) T →
        covDerivAlong k (fun q => boundaryPhasePoint k σ v q) (F i) r = 0) ∧
      (∀ r, r ∈ Ioo (-a) T → ∀ i j,
        k.inner (boundaryPhasePoint k σ v r) (F i r) (F j r) = if i = j then 1 else 0) ∧
      (∀ r, r ∈ Ioo (-a) T → ∀ i,
        k.inner (boundaryPhasePoint k σ v r) (F i r)
          (curveVelocity (I := 𝓡 3) (fun q => boundaryPhasePoint k σ v q) r) = 0) := by
  let _interiorCharts := Manifold.interiorChartedSpace (𝓡∂ 3) ∞ (M := halfInteriorC_OX124)
  let _interiorSmooth := Manifold.interiorIsManifold (𝓡∂ 3) ∞ (M := halfInteriorC_OX124)
  let k := boundaryInteriorAtlasMetric halfMetricC_OX124
  dsimp only
  have hp : (𝓡∂ 3).IsBoundaryPoint (0 : EuclideanHalfSpace 3) := by
    simp [ModelWithCorners.IsBoundaryPoint, extChartAt,
      frontier_range_modelWithCornersEuclideanHalfSpace]
    rfl
  have hparam : halfYC_OX124 ∈ range (Geometry.Boundary.modelBoundaryParam (𝓡∂ 3)) := by
    rw [Geometry.Boundary.range_modelBoundaryParam]
    exact hp
  obtain ⟨b, hb⟩ := hparam
  obtain ⟨G, _hcomplete, O, _hpO, _hG, V, ρ, _hρ, _hall, hlaunch⟩ :=
    exists_boundary_corner_ray_frame_OX124 halfMetricC_OX124 0 b hb.symm
  have hVne : halfVC_OX124 ≠ 0 := by
    intro hz
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) hz
    have hhead : halfVC_OX124 0 = 1 := by
      change (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0 = 1
      simp
    simp only [hhead, PiLp.zero_apply] at hh
    norm_num at hh
  let q := G.inner halfYC_OX124 halfVC_OX124 halfVC_OX124
  have hq : 0 < q := G.pos halfYC_OX124 halfVC_OX124 hVne
  let c := (Real.sqrt q)⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hq)
  let v := c • halfVC_OX124
  have hin : ∃ w : HasSmoothBoundary.boundaryE (𝓡∂ 3), ∃ d : ℝ, 0 < d ∧
      v = fderiv ℝ (Geometry.Boundary.modelBoundaryParam (𝓡∂ 3)) b w +
        d • HasSmoothBoundary.inwardCoordE (𝓡∂ 3) :=
    ⟨0, c, hc, by simp [v, halfVC_OX124]⟩
  have hunit : G.inner halfYC_OX124 v v = 1 := by
    have hm : G.inner halfYC_OX124 v v = c * c * q := by
      have hs := DifferentialGeometry.Geometry.Riemannian.Exponential.gInner_smul_self
        G halfYC_OX124 c halfVC_OX124
      exact hs.trans (congrArg (fun r : ℝ => r * q) (pow_two c))
    have hsqrt : q = Real.sqrt q * Real.sqrt q := by
      nlinarith [Real.sq_sqrt hq.le]
    have hscale : c * c * q = 1 := by
      calc
        _ = c * c * (Real.sqrt q * Real.sqrt q) := congrArg (fun r : ℝ => c * c * r) hsqrt
        _ = 1 := by dsimp only [c]; field_simp
    exact hm.trans hscale
  obtain ⟨δ, _hδ, a, ha, σ, _W, _ε, _hv, _hε, _hσ, _hseed, _hmatch, _hentry,
      _hPole, _hlift, _hbirth, _hlimit, _hphys, hframe⟩ := hlaunch v hin
  obtain ⟨e, heON, heperp⟩ := exists_perp_pos G halfYC_OX124 v (by rw [hunit]; norm_num)
  obtain ⟨L, haL, _hLδ, _Φ, _Z, _hsrc, _hmap, _hmet, _hZ0, _hZsm, _hZpar, _hZON, hdom,
      _hFsm, _hFpar, _hFON, _hFperp, hcont⟩ :=
    hframe hunit (fun i => e i) heON
      (fun i => (G.symm halfYC_OX124 v (e i)).trans (heperp i))
  have hT : 0 < (L - a) / 2 := by linarith
  have hdomT : ∀ r ∈ Icc (0 : ℝ) ((L - a) / 2), (σ v, r) ∈ k.geodesicFlowDomain :=
    fun r hr => (hdom r ⟨by linarith [hr.1, ha.1], by linarith [hr.2]⟩).1
  obtain ⟨F, _hFeq, _hFsm', hFpar', hFON', hFperp'⟩ := hcont ((L - a) / 2) hT hdomT
  exact ⟨a, (L - a) / 2, ha.1, hT, σ, v, F, hdomT, hFpar', hFON', hFperp'⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison.CornerRayContConsumerOX124

end
