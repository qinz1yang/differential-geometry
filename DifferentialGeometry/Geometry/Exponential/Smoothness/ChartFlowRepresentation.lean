import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartFlowGeodesicLink
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartIdentification
import DifferentialGeometry.Geometry.Exponential.ChartFlow.ChartPushVFEq
import DifferentialGeometry.Geometry.Exponential.Defs
import DifferentialGeometry.Geometry.Exponential.Smoothness.ChartFlowVelocitySlice
import DifferentialGeometry.Geometry.Geodesic.SmoothFlow
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Set Function Filter Metric Bundle Manifold
open scoped Topology NNReal Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

section ChartFlowRepresentation

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

def HasC1ChartFlowRepresentationAtZero (g : SmoothRiemannianMetric I M) (p : M) : Prop :=
  ∃ (Φ : (E × E) × ℝ → E × E) (t' ρ : ℝ), 0 < t' ∧ 0 < ρ ∧
    ContMDiffAt 𝓘(ℝ, E) I 1
      (chartFlowCandidate (I := I) Φ p t') (0 : E) ∧
    ∀ v : E, v ∈ Metric.ball (0 : E) ρ →
      (expMap (I := I) g p (show TangentSpace I p from (t' • v)) : M) =
        chartFlowCandidate (I := I) Φ p t' v

end ChartFlowRepresentation

section Headline

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
    [T2Space (TangentBundle I M)] in
theorem expMap_contMDiffAt_zero_of_c1ChartFlowRepresentation
    (g : SmoothRiemannianMetric I M) (p : M)
    (h : HasC1ChartFlowRepresentationAtZero (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, E) I 1
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
      (0 : E) := by
  classical
  obtain ⟨Φ, t', ρ, ht'_pos, hρ_pos, hcand_cd, heq⟩ := h
  set F : E → M := fun w : E =>
    chartFlowCandidate (I := I) Φ p t' ((1 / t') • w)
    with hF_def
  have hsmul_cd : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun w : E => (1 / t') • w) := by
    have : ContDiff ℝ ∞ (fun w : E => (1 / t') • w) :=
      (contDiff_const.smul contDiff_id)
    have h1 : ContDiff ℝ 1 (fun w : E => (1 / t') • w) :=
      this.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
    exact h1.contMDiff
  have hsmul_cda : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1
      (fun w : E => (1 / t') • w) (0 : E) := hsmul_cd.contMDiffAt
  have hval0 : (1 / t') • (0 : E) = 0 := smul_zero _
  have hF_cd : ContMDiffAt 𝓘(ℝ, E) I 1 F (0 : E) := by
    have hcand_cd' : ContMDiffAt 𝓘(ℝ, E) I 1
        (chartFlowCandidate (I := I) Φ p t')
        ((fun w : E => (1 / t') • w) (0 : E)) := by
      change ContMDiffAt 𝓘(ℝ, E) I 1
          (chartFlowCandidate (I := I) Φ p t') ((1 / t') • (0 : E))
      rw [hval0]
      exact hcand_cd
    have hcomp : ContMDiffAt 𝓘(ℝ, E) I 1
        ((chartFlowCandidate (I := I) Φ p t') ∘ (fun w : E => (1 / t') • w))
        (0 : E) := hcand_cd'.comp (0 : E) hsmul_cda
    exact hcomp
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  have hev :
      (fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M))
        =ᶠ[𝓝 (0 : E)] F := by
    have hsmul_cont : Continuous (fun w : E => (1 / t') • w) :=
      continuous_const.smul continuous_id
    have hsmul_at0_zero : (fun w : E => (1 / t') • w) (0 : E) = 0 := hval0
    have hpre : (fun w : E => (1 / t') • w) ⁻¹' Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := by
      have hnhd : Metric.ball (0 : E) ρ ∈ 𝓝 ((fun w : E => (1 / t') • w) (0 : E)) := by
        rw [hsmul_at0_zero]
        exact Metric.ball_mem_nhds _ hρ_pos
      exact hsmul_cont.continuousAt.preimage_mem_nhds hnhd
    filter_upwards [hpre] with w hw
    have hheq := heq ((1 / t') • w) hw
    have htv_eq_w : t' • ((1 / t') • w) = w := by
      rw [smul_smul, mul_one_div, div_self ht'_ne, one_smul]
    rw [htv_eq_w] at hheq
    change (expMap (I := I) g p (show TangentSpace I p from w) : M) = F w
    rw [hF_def]
    exact hheq
  exact hF_cd.congr_of_eventuallyEq hev

end Headline

section Origin

variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

omit [CompleteSpace E] in
omit [NeZero (Module.finrank ℝ E)] in
lemma chartFlowCandidate_zero_matches_expMap_at_origin
    (g : SmoothRiemannianMetric I M) (p : M)
    {Φ : (E × E) × ℝ → E × E}
    (hinit : Φ (((extChartAt I p p, (0 : E)) : E × E), 0) =
      (extChartAt I p p, (0 : E))) :
    chartFlowCandidate (I := I) Φ p 0 (0 : E) =
      expMap (I := I) g p (show TangentSpace I p from (0 : E)) := by
  classical
  rw [show expMap (I := I) g p (show TangentSpace I p from (0 : E)) = p from
    expMap_zero (I := I) g p]
  exact chartFlowCandidate_zero_at_initial (I := I) (Φ := Φ) (p := p) hinit

end Origin

end Exponential
end Riemannian
end Geometry
end DifferentialGeometry

end
