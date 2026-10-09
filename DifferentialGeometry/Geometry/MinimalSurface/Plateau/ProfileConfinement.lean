import DifferentialGeometry.Geometry.Metric.Conformal.BarrierProfile
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConvexBarrier
import DifferentialGeometry.Geometry.HarmonicMap.StrictConvexBarrier
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientCriticalSet

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- A Morrey disk for the conformal completion profile stays in the original
sublevel, has strict interior confinement, and sees the original metric germ.
The disk and its prescribed boundary loop are unchanged. -/
theorem IsMorreyDisk.profile_confinement
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρa : ∀ x, ρ x < a)
    (hbase : ∀ x : M, 0 < ρ x → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v)
    {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : IsMorreyDisk (profileMetric g a ha ρ hρ hρa) γ u)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hboundary : ∀ θ : loopCircle, ρ (γ θ) ≤ 0) :
    (∀ z : closedDisk, ρ (u z) ≤ 0) ∧
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ (u z) < 0) ∧
      ∀ z : closedDisk, ∀ᶠ y in 𝓝 (u z),
        (profileMetric g a ha ρ hρ hρa).inner y = g.inner y ∧
          barrier a (ρ y) = ρ y := by
  let P := profileMetric g a ha ρ hρ hρa
  let f : M → ℝ := fun x => barrier a (ρ x)
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f :=
    barrier_comp_smooth a ha ρ hρ hρa
  have hnonneg (x : M) :
      0 ≤ deriv (logWeight a) (ρ x) *
        g.inner x (gradFun g ρ x) (gradFun g ρ x) :=
    mul_nonneg (deriv_logWeight_nonneg ha (hρa x))
      (metric_inner_self_nonneg g x (gradFun g ρ x))
  have hweak : ∀ z : closedDisk, f (u z) ≤ 0 :=
    IsMorreyDisk.confinement_of_hessian_nonneg P hu hf
      (fun x hx v => by
        have hxρ : 0 < ρ x := lt_of_not_ge fun hle =>
          (not_le_of_gt hx) ((barrier_le_zero_iff ha (hρa x)).2 hle)
        rw [hess_profileMetric_barrier]
        exact mul_nonneg (sq_nonneg _) (add_nonneg (hbase x hxρ v)
          (mul_nonneg (hnonneg x) (metric_inner_self_nonneg g x v))))
      (fun θ => (barrier_le_zero_iff ha (hρa (γ θ))).2 (hboundary θ))
  have hle : ∀ z : closedDisk, ρ (u z) ≤ 0 := fun z =>
    (barrier_le_zero_iff ha (hρa (u z))).1 (hweak z)
  have hpositive (x : M) (hx : f x = 0) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ≠ 0) : 0 < hessFun P f x v v := by
    have hxle : ρ x ≤ 0 := (barrier_le_zero_iff ha (hρa x)).1 hx.le
    have hxzero : ρ x = 0 :=
      (barrier_eq_self ha (hxle.trans (half_pos ha).le)).symm.trans hx
    rw [hess_profileMetric_barrier]
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr ((cutoff_pos_iff ha (ρ x)).2 (hρa x))))
      (add_pos_of_pos_of_nonneg (hcontact x hxzero v hv)
        (mul_nonneg (hnonneg x) (metric_inner_self_nonneg g x v)))
  have hstrict := lt_of_planarTension_eq_zero_of_hessian_pos_of_finite_critical_set
    (U := diskExtension u) (D := ball (0 : ℂ) 1) P hf isOpen_ball
    (hu.smoothInterior.of_le (by simp))
    (by
      intro z hz
      change diskMapTension P (diskExtension u) z = 0
      exact hu.harmonic z hz)
    (fun z _ => hweak (diskRetraction z))
    (fun z _ hz => hpositive (diskExtension u z) hz)
    (fun K hK hKD => hu.finite_mfderiv_eq_zero_of_isCompact hγ hK hKD)
  refine ⟨hle, ?_, ?_⟩
  · intro z hz
    have hzball : (z : ℂ) ∈ ball (0 : ℂ) 1 := by
      simpa only [mem_ball, dist_zero_right] using hz
    have hstrictz : f (u z) < 0 := by
      simpa only [diskExtension_coe] using hstrict (z : ℂ) hzball
    have hfeq : f (u z) = ρ (u z) :=
      barrier_eq_self ha ((hle z).trans (half_pos ha).le)
    exact hfeq ▸ hstrictz
  · intro z
    exact profile_preserved_germs g a ha ρ hρ hρa (u z)
      ((hle z).trans_lt (half_pos ha))

end DifferentialGeometry.Geometry
