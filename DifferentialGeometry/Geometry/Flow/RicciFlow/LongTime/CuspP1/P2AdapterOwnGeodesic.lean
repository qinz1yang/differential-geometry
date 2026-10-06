import DifferentialGeometry.Geometry.Geodesic.Flow.Uniqueness
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Geometry.Geodesic.Maximal.Interval
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.LoopSpace.CircleDegree

/-!
# P2A-13 (step 1a): a geodesic with a zero-velocity instant is constant; embedded loops have
nowhere-vanishing velocity.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Bundle Set
open DifferentialGeometry.Geometry.Riemannian.Geodesic GC.Endpoint
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)]

theorem geodesic_const_of_zero_velocity_P2A (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (hc : Continuous γ) {t₀ : ℝ}
    (h0 : mfderiv 𝓘(ℝ, ℝ) I γ t₀ (1 : ℝ) = 0) (t : ℝ) : γ t = γ t₀ := by
  have h1 : IsMIntegralCurveOn (velocityLift (I := I) γ) (geodesicVectorField (I := I) g) univ :=
    isMIntegralCurveOn_velocityLift (I := I) g isOpen_univ (hγ.isGeodesicOn univ) hc.continuousOn
  have h2 : IsMIntegralCurve (fun _ : ℝ => (⟨γ t₀, (0 : E)⟩ : TangentBundle I M))
      (geodesicVectorField (I := I) g) := by
    refine isMIntegralCurve_const ?_
    exact geodesicVectorField_zero_section (I := I) g (γ t₀)
  have h3 := integralCurve_eqOn (I := I) g isOpen_univ isPreconnected_univ (mem_univ t₀) h1
    (h2.isMIntegralCurveOn univ) (by
      refine Bundle.TotalSpace.ext rfl ?_
      exact heq_of_eq h0)
  exact congrArg Bundle.TotalSpace.proj (h3 (mem_univ t))

end

/-- A topologically embedded smooth geodesic loop in the torus has non-vanishing velocity. -/
theorem loop_velocity_ne_zero_P2A
    (g : SmoothRiemannianMetric torusModel Torus) (loop : freeLoop Torus)
    (hemb : Topology.IsEmbedding loop)
    (hgeo : IsGeodesic (I := torusModel) g (loopLift loop)) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) t (1 : ℝ) ≠ 0 := by
  intro h0
  have hconst := geodesic_const_of_zero_velocity_P2A (I := torusModel) g hgeo
    (loopLift loop).continuous h0
  have hc : ∀ θ : loopCircle, loop θ = loop (t : loopCircle) := by
    intro θ
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact hconst s
  have h01 : ((0 : ℝ) : loopCircle) = ((1 / 2 : ℝ) : loopCircle) :=
    hemb.injective ((hc _).trans (hc _).symm)
  have : ((1 / 2 : ℝ) : loopCircle) ≠ ((0 : ℝ) : loopCircle) := by
    intro h
    have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (hp := ⟨one_pos⟩) (a := 0)
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩).mp h
    norm_num at this
  exact this h01.symm

end GC.LongTime.CuspP1
