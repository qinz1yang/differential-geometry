import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Operator.Laplacian.Minimum
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

open Bundle Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private theorem laplacian_sub_of_local_regularity
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (g : SmoothRiemannianMetric I M) (f h : M → ℝ) (x : M)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) f y)
    (hh : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) h y)
    (hgf : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g f y) x)
    (hgh : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g h y) x) :
    laplacian cov g (fun y => f y - h y) x =
      laplacian cov g f x - laplacian cov g h x := by
  have he : gradientFun (I := I) g (fun y => f y - h y) =ᶠ[𝓝 x]
      gradientFun (I := I) g f - gradientFun (I := I) g h := by
    filter_upwards [hf, hh] with y hfy hhy
    exact gradientFun_sub g hfy hhy
  have hr := mdifferentiableAt_sub_section hgf hgh
  have hl : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g (fun z => f z - h z) y) x := by
    apply hr.congr_of_eventuallyEq
    filter_upwards [he] with y hy
    exact congrArg (fun w => (⟨y, w⟩ : TotalSpace E (TangentSpace I))) hy
  have hcov := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hl hr univ_mem he
  calc
    laplacian cov g (fun y => f y - h y) x =
        divergence cov (gradientFun (I := I) g f - gradientFun (I := I) g h) x := by
      unfold laplacian divergence
      rw [hcov]
    _ = laplacian cov g f x - laplacian cov g h x :=
      divergence_sub cov hgf hgh

variable [I.Boundaryless]

theorem le_on_compact_of_laplacian_upper_supports
    (g : SmoothRiemannianMetric I M) (K : Set M) (hK : IsCompact K)
    (u v : M → ℝ) (hu : ContinuousOn u K) (hv_cont : ContinuousOn v K)
    (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v (interior K))
    (hboundary : ∀ x ∈ K \ interior K, v x ≤ u x)
    (hv_lap : ∀ x ∈ interior K, 0 < laplacian (LeviCivita g) g v x)
    (hsupport : ∀ x ∈ interior K, ∀ ε : ℝ, 0 < ε →
      ∃ U : Set M, ∃ φ : M → ℝ,
        IsOpen U ∧ x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ φ U ∧
          φ x = u x ∧ (∀ y ∈ U, u y ≤ φ y) ∧
            laplacian (LeviCivita g) g φ x ≤ ε) :
    ∀ x ∈ K, v x ≤ u x := by
  intro x hx
  by_contra hnot
  have hxneg : u x - v x < 0 := sub_neg.mpr (lt_of_not_ge hnot)
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn ⟨x, hx⟩ (hu.sub hv_cont)
  have hpneg : u p - v p < 0 := (hpmin hx).trans_lt hxneg
  have hpint : p ∈ interior K := by
    by_contra hpi
    exact (not_lt_of_ge (sub_nonneg.mpr (hboundary p ⟨hp, hpi⟩))) hpneg
  have hstrict := hv_lap p hpint
  obtain ⟨U, φ, hU, hpU, hφ, heq, hupper, hφlap⟩ :=
    hsupport p hpint (laplacian (LeviCivita g) g v p / 2) (half_pos hstrict)
  have hcontact : IsLocalMin (fun y => φ y - v y) p := by
    unfold IsLocalMin IsMinFilter
    filter_upwards [hU.mem_nhds hpU, isOpen_interior.mem_nhds hpint] with y hyU hyint
    rw [heq]
    exact (hpmin (interior_subset hyint)).trans (sub_le_sub_right (hupper y hyU) (v y))
  have hφ_near : ∀ᶠ y in 𝓝 p, MDifferentiableAt I 𝓘(ℝ, ℝ) φ y := by
    filter_upwards [hU.mem_nhds hpU] with y hy
    exact ((hφ y hy).contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hv_near : ∀ᶠ y in 𝓝 p, MDifferentiableAt I 𝓘(ℝ, ℝ) v y := by
    filter_upwards [isOpen_interior.mem_nhds hpint] with y hy
    exact ((hv y hy).contMDiffAt (isOpen_interior.mem_nhds hy)).mdifferentiableAt
      (by simp)
  have hdiff_near : ∀ᶠ y in 𝓝 p,
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun z => φ z - v z) y := by
    filter_upwards [hφ_near, hv_near] with y hφy hvy
    exact hφy.sub hvy
  have hφ_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ φ p :=
    (hφ p hpU).contMDiffAt (hU.mem_nhds hpU)
  have hv_at : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ v p :=
    (hv p hpint).contMDiffAt (isOpen_interior.mem_nhds hpint)
  have hφ_grad := gradientFun_mdiffOn g hU hφ hpU
  have hv_grad := gradientFun_mdiffOn g isOpen_interior hv hpint
  have hdiff_grad : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (T% fun y => gradientFun (I := I) g (fun z => φ z - v z) y) p :=
    (gradientFun_contMDiffAt g (hφ_at.sub hv_at)).mdifferentiableAt (by simp)
  have hmc : IsMetricCompatible (I := I) (LeviCivita g) g := by
    simpa only [LeviCivita] using leviCivitaConnectionOfMetric_isMetricCompatible g
  have hnonneg := laplacian_nonneg_at_spatial_min_of_metricCompatible
    (LeviCivita g) g hmc hcontact hdiff_near.self_of_nhds hdiff_near hdiff_grad
  rw [laplacian_sub_of_local_regularity (LeviCivita g) g φ v p
    hφ_near hv_near hφ_grad hv_grad] at hnonneg
  linarith only [hnonneg, hφlap, hstrict]

end DifferentialGeometry.Analysis
end
