import DifferentialGeometry.Geometry.Riemannian.Exponential.MfderivAtZero
import DifferentialGeometry.Geometry.Riemannian.Exponential.MinimizingGeodesic

/-!
# The manifold derivative of the intrinsic exponential map at zero is the identity

The chart-fixed exponential map `expMap g p` has `mfderiv ... 0 = id` by
`mfderiv_expMap_at_zero`.  The intrinsic exponential map `expMapIntrinsic g hEnorm p`
agrees with `expMap g p` for every launch vector `v` whose `g`-norm
`√(g_p(v,v))` is below an explicit positive threshold (the side-condition-free
agreement `exists_expMapIntrinsic_eq_expMap_radius`).  Since `v ↦ √(g_p(v,v))` is
continuous and vanishes at `0`, that agreement set is a neighbourhood of the zero
tangent vector, so the two maps are eventually equal near `0`.  The manifold derivative
only depends on the germ of the map at the point, hence the two `mfderiv`s coincide and
`mfderiv (expMapIntrinsic g hEnorm p) 0 = id`.
-/

noncomputable section

open Set Function Filter Metric Bundle Manifold Real
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

set_option linter.unusedSectionVars false in
attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- **The manifold derivative of the intrinsic exponential map at the zero tangent
vector is the identity.** For a smooth Riemannian metric `g` on a connected,
boundaryless, complete Riemannian manifold modelled on a complete inner-product space,
and any base point `p`,

`mfderiv 𝓘(ℝ, E) I (expMapIntrinsic g hEnorm p) 0 = ContinuousLinearMap.id ℝ E`.

The intrinsic exponential map agrees with the chart-fixed `expMap g p` on a
neighbourhood of the zero tangent vector (the small-velocity agreement
`exists_expMapIntrinsic_eq_expMap_radius`, whose threshold is an explicit `g`-norm
radius and whose agreement region is a `𝓝 0` because `v ↦ √(g_p(v,v))` is continuous
and vanishes at `0`).  The manifold derivative depends only on the germ, so the two
derivatives coincide, and the chart-fixed one is the identity by
`mfderiv_expMap_at_zero`. -/
theorem mfderiv_expMapIntrinsic_at_zero
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M] [CompleteSpace E]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    mfderiv 𝓘(ℝ, E) I
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
      (0 : E) =
      ContinuousLinearMap.id ℝ E := by
  classical
  obtain ⟨ρ, hρ_pos, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  have hcont : Continuous (fun v : E => Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))) :=
    continuous_sqrt_gInner_self (I := I) g p
  set S : Set E :=
    {v : E | Real.sqrt (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v)) < ρ} with hS_def
  have hS_open : IsOpen S := hcont.isOpen_preimage (Set.Iio ρ) isOpen_Iio
  have hzero_mem : (0 : E) ∈ S := by
    have h0 : Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
        (show TangentSpace I p from (0 : E))) = 0 := by
      have hgz : g.inner p (show TangentSpace I p from (0 : E))
          (show TangentSpace I p from (0 : E)) = 0 := by
        show g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p) = 0
        simp
      rw [hgz, Real.sqrt_zero]
    show Real.sqrt (g.inner p (show TangentSpace I p from (0 : E))
      (show TangentSpace I p from (0 : E))) < ρ
    rw [h0]; exact hρ_pos
  have hEvEq :
      (fun v : E => (expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)]
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) := by
    refine Filter.eventuallyEq_of_mem (hS_open.mem_nhds hzero_mem) ?_
    intro v hv
    exact hagree hv
  rw [hEvEq.mfderiv_eq]
  exact mfderiv_expMap_at_zero (I := I) g p

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
