import DifferentialGeometry.Geometry.Metric.Conformal.PositiveDomain
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ProfileConfinement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryNondegeneracy
import DifferentialGeometry.Geometry.Operator.Restriction
import DifferentialGeometry.Geometry.Operator.Hessian.Positivity
import DifferentialGeometry.Analysis.Calculus.DiskTraceApproximation
import DifferentialGeometry.Topology.Manifold.OpenTarget

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set Metric TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Metric.BarrierProfile
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Boundary rank is proved for the same completed-target Morrey disk before
projection. No global original-metric Morrey property is asserted. -/
theorem boundary_immersion_of_profile_metric
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : ℝ) (ha : 0 < a)
    (ρ : M → ℝ) (hρ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρ)
    (hbase : ∀ x : M, 0 < ρ x → ρ x < a →
      ∀ v : TangentSpace 𝓘(ℝ, E) x, 0 ≤ hessFun g ρ x v v)
    (hcontact : ∀ x : M, ρ x = 0 → ∀ v : TangentSpace 𝓘(ℝ, E) x,
      v ≠ 0 → 0 < hessFun g ρ x v v) :
    let U : Opens M := ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : M → ℝ := fun x => cutoff a (ρ x)
    let hδ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth a).contMDiff.comp hρ
    let hU : ∀ x : M, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric g hδ U hU
    let ι : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := E) γU → IsMorreyDisk G γU q →
      (∀ θ : loopCircle, ρ (γU θ : M) = 0) →
      ∀ (Q : ℂ → U), SmoothDiskExtension (E := E) q Q →
        SmoothDiskExtension (E := E) (ι.comp q) (Subtype.val ∘ Q) ∧
        ∀ p ∈ sphere (0 : ℂ) 1,
          Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Subtype.val ∘ Q) p) := by
  intro U δ hδ hU G ι γU q hγ hq hγzero Q hQ
  let ρU : U → ℝ := fun x => ρ (x : M)
  have hρU : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ ρU :=
    hρ.comp contMDiff_subtype_val
  have hρUa : ∀ x : U, ρU x < a := fun x => x.property
  have hG : G = profileMetric (g.restrictOpen U) a ha ρU hρU hρUa := rfl
  have hbaseU (x : U) (hx : 0 < ρU x) (v : TangentSpace 𝓘(ℝ, E) x) :
      0 ≤ hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    exact hbase (x : M) hx x.property
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v)
  have hcontactU (x : U) (hx : ρU x = 0) (v : TangentSpace 𝓘(ℝ, E) x)
      (hv : v ≠ 0) : 0 < hessFun (g.restrictOpen U) ρU x v v := by
    rw [hessFun_restrictOpen_of_contMDiff g U ρ hρ]
    simpa only [mfderiv_subtype_val_apply] using hcontact (x : M) hx v hv
  have hqProfile : IsMorreyDisk
      (profileMetric (g.restrictOpen U) a ha ρU hρU hρUa) γU q := hG ▸ hq
  obtain ⟨_, hstrict, _⟩ :=
    IsMorreyDisk.profile_confinement (g.restrictOpen U) a ha ρU hρU hρUa
      hbaseU hcontactU hqProfile hγ (fun θ => (hγzero θ).le)
  have hboundary (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1) : ρU (q z) = 0 := by
    obtain ⟨σ, _, htrace⟩ := hq.trace
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_eq_of_norm_eq_one hz
    have hzθ : diskBoundary θ = z := Subtype.ext hθ
    rw [← hzθ]
    have htraceθ : q (diskBoundary θ) = γU (σ θ) :=
      congrArg (fun η => η θ) htrace
    rw [htraceθ]
    exact hγzero (σ θ)
  let V : Set U := {x | ∀ v : TangentSpace 𝓘(ℝ, E) x, v ≠ 0 →
    0 < hessFun (g.restrictOpen U) ρU x v v}
  have hV : IsOpen V := by
    simpa only [zero_mul] using isOpen_hessFun_gt_mul_inner (g.restrictOpen U) hρU 0
  have hboundaryV (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1) : q z ∈ V :=
    hcontactU (q z) (hboundary z hz)
  let f : U → ℝ := fun x => barrier a (ρU x)
  have hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f :=
    barrier_comp_smooth a ha ρU hρU hρUa
  have hH (x : U) (hx : x ∈ V) (v : TangentSpace 𝓘(ℝ, E) x) :
      0 ≤ hessFun G f x v v := by
    rw [hG]
    change 0 ≤ hessFun (profileMetric (g.restrictOpen U) a ha ρU hρU hρUa)
      (fun y => barrier a (ρU y)) x v v
    rw [hess_profileMetric_barrier]
    apply mul_nonneg (sq_nonneg _)
    apply add_nonneg
    · by_cases hv : v = 0
      · subst v
        simp only [map_zero, le_refl]
      · exact (hx v hv).le
    · exact mul_nonneg
        (mul_nonneg (deriv_logWeight_nonneg ha (hρUa x))
          (metric_inner_self_nonneg (g.restrictOpen U) x (gradFun (g.restrictOpen U) ρU x)))
        (metric_inner_self_nonneg (g.restrictOpen U) x v)
  have hfstrict (z : closedDisk) (hz : ‖(z : ℂ)‖ < 1) : f (q z) < 0 := by
    have hneg := hstrict z hz
    change barrier a (ρU (q z)) < 0
    rw [barrier_eq_self ha (hneg.le.trans (half_pos ha).le)]
    exact hneg
  have hfboundary (z : closedDisk) (hz : ‖(z : ℂ)‖ = 1) : f (q z) = 0 := by
    change barrier a (ρU (q z)) = 0
    rw [hboundary z hz, barrier_eq_self ha (half_pos ha).le]
  have hrank := hq.boundary_immersion_of_hessian_nonneg_near_boundary
    hQ hf hV hboundaryV hH hfstrict hfboundary
  refine ⟨hQ.comp ι contMDiff_subtype_val, ?_⟩
  intro p hp
  rw [DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U Q p]
  exact hrank p hp

end DifferentialGeometry.Geometry
