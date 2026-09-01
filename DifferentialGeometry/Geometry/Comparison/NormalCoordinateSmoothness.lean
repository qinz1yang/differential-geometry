import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import DifferentialGeometry.Geometry.Comparison.ExponentialBallPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.Smoothness.OffZero

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open Bundle
open scoped Manifold ContDiff Topology Bundle

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type uE} [NormedAddCommGroup E]
variable {H : Type uH} [TopologicalSpace H]

section NormalChartInftySmooth

variable [NormedSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank Real E)] in
theorem normal_chart_at_cont_mdiff_at_infty
    (g : SmoothRiemannianMetric I M) (p : M) {v₀ : E}
    (hv₀ : ‖v₀‖ < expMapC2Radius (I := I) g p) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      (expMap (I := I) g p (show TangentSpace I p from v₀)) := by
  classical
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  set fexp : E → M := fun v => (expMap (I := I) g p (show TangentSpace I p from v)) with hfexp
  set q : M := fexp v₀ with hq
  set χ : M → E := ⇑(extChartAt I q) with hχ
  have hf_cd : ContMDiffAt 𝓘(ℝ, E) I ∞ fexp v₀ :=
    expMap_contMDiffAt_infty_of_norm_lt_radius (I := I) g p hv₀
  have hmem_ball : v₀ ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    rw [Metric.mem_ball, dist_zero_right]; exact hv₀
  have hf_diffeo : IsLocalDiffeomorphAt 𝓘(ℝ, E) I 1 fexp v₀ :=
    exponential_map_is_local_diffeomorph_on_ball (I := I) g p (le_refl _) ⟨v₀, hmem_ball⟩
  have hD1_inv : (mfderiv 𝓘(ℝ, E) I fexp v₀).IsInvertible :=
    ⟨hf_diffeo.mfderivToContinuousLinearEquiv one_ne_zero,
      hf_diffeo.mfderivToContinuousLinearEquiv_coe one_ne_zero⟩
  have hD2_inv : (mfderiv I 𝓘(ℝ, E) χ q).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := I) (mem_extChartAt_source q)
  have hχ_cd : ContMDiffAt I 𝓘(ℝ, E) ∞ χ q := contMDiffAt_extChartAt (I := I) (x := q)
  have hF_cd : ContDiffAt ℝ ∞ (χ ∘ fexp) v₀ := (hχ_cd.comp v₀ hf_cd).contDiffAt
  have h1 : HasMFDerivAt 𝓘(ℝ, E) I fexp v₀ (mfderiv 𝓘(ℝ, E) I fexp v₀) :=
    (hf_cd.mdifferentiableAt hne).hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, E) χ q (mfderiv I 𝓘(ℝ, E) χ q) :=
    (hχ_cd.mdifferentiableAt hne).hasMFDerivAt
  have hF_mfd : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (χ ∘ fexp) v₀
      ((mfderiv I 𝓘(ℝ, E) χ q).comp (mfderiv 𝓘(ℝ, E) I fexp v₀)) := h2.comp v₀ h1
  have hF_fderiv0 := hasMFDerivAt_iff_hasFDerivAt.mp hF_mfd
  let hModuleTopology : IsModuleTopology ℝ E := isModuleTopologyOfFiniteDimensional
  let hContinuousAdd : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  have hF_fderiv_eq :
      fderiv ℝ (χ ∘ fexp) v₀ =
        (mfderiv I 𝓘(ℝ, E) χ q).comp (mfderiv 𝓘(ℝ, E) I fexp v₀) :=
    @HasFDerivAt.fderiv ℝ inferInstance E inferInstance inferInstance inferInstance
      E inferInstance inferInstance inferInstance (χ ∘ fexp)
        ((mfderiv I 𝓘(ℝ, E) χ q).comp (mfderiv 𝓘(ℝ, E) I fexp v₀)) v₀
          hContinuousAdd inferInstance hContinuousAdd inferInstance inferInstance hF_fderiv0
  have hfd_inv : (fderiv ℝ (χ ∘ fexp) v₀).IsInvertible := by
    rw [hF_fderiv_eq]
    exact hD2_inv.comp hD1_inv
  obtain ⟨e, he⟩ := hfd_inv
  have hF_fderiv : HasFDerivAt (χ ∘ fexp) (e : E →L[ℝ] E) v₀ := by
    rw [he]; exact hF_fderiv0.differentiableAt.hasFDerivAt
  have hinv := hF_cd.to_localInverse hF_fderiv hne
  set Φ : OpenPartialHomeomorph E E :=
    hF_cd.toOpenPartialHomeomorph (χ ∘ fexp) hF_fderiv hne with hΦ
  have hloc_eq : hF_cd.localInverse hF_fderiv hne = Φ.symm := rfl
  rw [hloc_eq] at hinv
  have hv₀_Φsrc : v₀ ∈ Φ.source :=
    hF_cd.mem_toOpenPartialHomeomorph_source hF_fderiv hne
  have hv₀_src : v₀ ∈ (expMapDiffeo (I := I) g p).source := by
    have h := ball_subset_normalChartAt_target (I := I) g p hv₀
    rwa [normalChartAt_target_eq] at h
  have hq_tgt : q ∈ (expMapDiffeo (I := I) g p).target := by
    have hev : expMapDiffeo (I := I) g p v₀ = q := by
      rw [expMapDiffeo_apply_eq (I := I) g p hv₀_src]
    rw [← hev]; exact (expMapDiffeo (I := I) g p).map_source hv₀_src
  have hsymm_cm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ Φ.symm (χ q) :=
    (contMDiffAt_iff_contDiffAt).mpr hinv
  have hcomp : ContMDiffAt I 𝓘(ℝ, E) ∞ (Φ.symm ∘ χ) q := hsymm_cm.comp q hχ_cd
  have hΦcoe : (Φ : E → E) = χ ∘ fexp :=
    hF_cd.toOpenPartialHomeomorph_coe hF_fderiv hne
  have hncq : normalChartAt (I := I) g p q = v₀ := by
    have hv₀_nctgt : v₀ ∈ (normalChartAt (I := I) g p).target := by
      rw [normalChartAt_target_eq]; exact hv₀_src
    have hq_eq : q = (normalChartAt (I := I) g p).symm v₀ := by
      rw [normalChartAt_symm_apply (I := I) g p hv₀_nctgt]
    rw [hq_eq]; exact normalChartAt_right_inv (I := I) g p hv₀_nctgt
  have hq_src : q ∈ (normalChartAt (I := I) g p).source := by
    rw [normalChartAt_source_eq]; exact hq_tgt
  have heqEv : normalChartAt (I := I) g p =ᶠ[nhds q] (Φ.symm ∘ χ) := by
    have hUopen : IsOpen ((normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source) :=
      ((normalChartAt_contMDiffOn (I := I) g p).continuousOn).isOpen_inter_preimage
        (normalChartAt (I := I) g p).open_source Φ.open_source
    have hqU : q ∈ (normalChartAt (I := I) g p).source ∩
        normalChartAt (I := I) g p ⁻¹' Φ.source :=
      ⟨hq_src, by rw [Set.mem_preimage, hncq]; exact hv₀_Φsrc⟩
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hqU) (fun q' hq' => ?_)
    obtain ⟨hq'_src, hq'_pre⟩ := hq'
    rw [Set.mem_preimage] at hq'_pre
    set v' := normalChartAt (I := I) g p q' with hv'def
    have hv'_symmsrc : v' ∈ (normalChartAt (I := I) g p).symm.source :=
      (normalChartAt (I := I) g p).map_source hq'_src
    have hfv' : fexp v' = q' := by
      change (expMap (I := I) g p (show TangentSpace I p from v') : M) = q'
      rw [← normalChartAt_symm_apply (I := I) g p hv'_symmsrc]
      exact normalChartAt_left_inv (I := I) g p hq'_src
    have hΦv' : Φ v' = χ q' := by
      have hc : (χ ∘ fexp) v' = χ q' := by rw [Function.comp_apply, hfv']
      rw [hΦcoe]; exact hc
    change normalChartAt (I := I) g p q' = (Φ.symm ∘ χ) q'
    rw [Function.comp_apply, ← hΦv', Φ.left_inv hq'_pre]
  exact hcomp.congr_of_eventuallyEq heqEv

omit [NeZero (Module.finrank Real E)] in
theorem normal_chart_at_cont_mdiff_on_infty
    (g : SmoothRiemannianMetric I M) (p : M) :
    ContMDiffOn I 𝓘(ℝ, E) ∞ (normalChartAt (I := I) g p)
      ((fun v : E => (expMap (I := I) g p (show TangentSpace I p from v) : M)) ''
        Metric.ball (0 : E) (expMapC2Radius (I := I) g p)) := by
  rintro q ⟨v₀, hv₀ball, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hv₀ball
  exact (normal_chart_at_cont_mdiff_at_infty (I := I) g p hv₀ball).contMDiffWithinAt

end NormalChartInftySmooth

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
