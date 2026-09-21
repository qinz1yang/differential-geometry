import DifferentialGeometry.Geometry.Comparison.Distance.EndpointRate
import DifferentialGeometry.Topology.Manifold.CurveExtension
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Analysis.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

theorem abs_mvfderiv_le_of_eventually_riemannian_distance_bound
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (p : M) (C : ℝ)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f p)
    (hbound : ∀ᶠ x in 𝓝 p, |f x - f p| ≤ C * (riemannianEDistOf g x p).toReal)
    (v : TangentSpace I p) :
    |mvfderiv (I := I) f p v| ≤ C * Real.sqrt (g.inner p v v) := by
  obtain ⟨γ, hγ, _, hvel⟩ := exists_contMDiff_curve_with_velocity_range_subset
    (I := I) (x := p) BoundarylessManifold.isInteriorPoint v (U := univ) univ_mem
  have hγ0 : γ 0 = p := congrArg (fun z : TangentBundle I M => z.proj) hvel
  have hnorm : g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) = g.inner p v v :=
    congrArg (fun z : TangentBundle I M => g.inner z.proj z.snd z.snd) hvel
  have hv : (mfderiv 𝓘(ℝ, ℝ) I γ 0 1 : E) = (v : E) :=
    congrArg (fun z : TangentBundle I M => (z.snd : E)) hvel
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 := hγ.contMDiffAt.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hcomp := hasDerivAt_comp_mfderiv_along I f γ 0 (by rwa [hγ0]) hγd
  change HasDerivAt (fun t => f (γ t)) (mvfderiv (I := I) f (γ 0)
    (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) 0 at hcomp
  rw [hv, hγ0] at hcomp
  have hleft : Tendsto (fun t : ℝ => |(f (γ t) - f p) / t|)
      (𝓝[>] 0) (𝓝 |mvfderiv (I := I) f p v|) := by
    have h := hcomp.tendsto_slope_zero_right.abs
    simpa only [zero_add, hγ0, smul_eq_mul, div_eq_inv_mul] using h
  have hright : Tendsto (fun t : ℝ => C * ((riemannianEDistOf g (γ t) p).toReal / t))
      (𝓝[>] 0) (𝓝 (C * Real.sqrt (g.inner p v v))) := by
    have h := (riemannianEDistOf_div_tendsto_speed g γ 0 hγd).const_mul C
    erw [hnorm] at h
    simpa only [zero_add, hγ0] using h
  apply le_of_tendsto_of_tendsto hleft hright
  have hγt : Tendsto γ (𝓝 0) (𝓝 p) := by
    simpa only [hγ0] using hγ.continuous.tendsto 0
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
      |f (γ t) - f p| ≤ C * (riemannianEDistOf g (γ t) p).toReal :=
    nhdsWithin_le_nhds (hγt.eventually hbound)
  filter_upwards [hb, self_mem_nhdsWithin] with t ht htpos
  rw [abs_div, abs_of_pos (show 0 < t from htpos)]
  calc
    _ ≤ (C * (riemannianEDistOf g (γ t) p).toReal) / t :=
      div_le_div_of_nonneg_right ht htpos.le
    _ = _ := mul_div_assoc _ _ _

end DifferentialGeometry.Geometry.Riemannian
