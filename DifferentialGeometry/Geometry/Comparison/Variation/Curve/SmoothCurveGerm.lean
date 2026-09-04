import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section


open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_contMDiffAt_hasMFDerivAt_of_tangent (x : M) (v : TangentSpace I x) :
    ∃ c : ℝ → M, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ c 0 ∧ c 0 = x ∧
      HasMFDerivAt 𝓘(ℝ, ℝ) I c 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v) := by
  set φ : E := extChartAt I x x with hφ
  let w : E := v
  set L : ℝ → E := fun r => φ + r • w with hL
  have hL0 : L 0 = φ := by simp [hL]
  have hLcm : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ L 0 := by
    rw [contMDiffAt_iff_contDiffAt]
    have : ContDiffAt ℝ ∞ (fun r : ℝ => φ + r • w) 0 := by fun_prop
    simpa [hL] using this
  have hLine : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) L 0 ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    have hadd : HasFDerivAt L ((0 : ℝ →L[ℝ] E) + (1 : ℝ →L[ℝ] ℝ).smulRight w) 0 := by
      rw [hL]
      refine HasFDerivAt.add (hasFDerivAt_const φ (0 : ℝ)) ?_
      refine (((1 : ℝ →L[ℝ] ℝ).smulRight w).hasFDerivAt (x := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards with r using by simp [ContinuousLinearMap.smulRight_apply]
    rw [zero_add] at hadd
    exact hadd.hasMFDerivAt
  have hsymmC : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm φ := by
    refine (contMDiffOn_extChartAt_symm (n := (∞ : WithTop ℕ∞)) x).contMDiffAt ?_
    simpa [hφ] using extChartAt_target_mem_nhds x
  have hsymmD : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I x).symm (L 0)
      (ContinuousLinearMap.id ℝ E) := by
    have hmem : φ ∈ (extChartAt I x).target := by rw [hφ]; exact mem_extChartAt_target x
    have hdiff : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ := by
      have := mdifferentiableWithinAt_extChartAt_symm (I := I) (x := x) hmem
      rwa [I.range_eq_univ] at this
    have heq : mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
        = ContinuousLinearMap.id ℝ E := by
      rw [hφ, ← I.range_eq_univ]
      exact mfderivWithin_range_extChartAt_symm
    have hwd : HasMFDerivWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm univ φ
        (ContinuousLinearMap.id ℝ E) := heq ▸ hdiff.hasMFDerivWithinAt
    rw [hL0]
    exact hasMFDerivWithinAt_univ.mp hwd
  refine ⟨fun r => (extChartAt I x).symm (L r), ?_, ?_, ?_⟩
  · exact (hsymmC.comp_of_eq hLcm hL0 :)
  · simp [hL, hφ]
  · have hcomp := hsymmD.comp 0 hLine
    rw [Function.comp_def] at hcomp
    exact hcomp

omit [I.Boundaryless] in
theorem exists_contMDiff_tangentCurve_reparametrization
    {alpha : ℝ → M} {Y : ∀ s, TangentSpace I (alpha s)}
    {K : Set ℝ} {s0 b : ℝ}
    (hKopen : IsOpen K) (hsb : s0 < b) (hseg : Icc s0 b ⊆ K)
    (hfield : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (Y s) : TangentBundle I M)) K) :
    ∃ rho : ℝ → ℝ, ∃ a d : ℝ,
      a < s0 ∧ b < d ∧ ContDiff ℝ ∞ rho ∧
      Set.EqOn rho id (Icc a d) ∧
      (∀ s ∈ Icc a d, HasDerivAt rho 1 s) ∧
      (∀ s : ℝ, rho s ∈ K) ∧
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun s : ℝ ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha (rho s)) (Y (rho s)) : TangentBundle I M)) ∧
      Set.EqOn
        (fun s : ℝ ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha (rho s)) (Y (rho s)) : TangentBundle I M))
        (fun s : ℝ ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (Y s) : TangentBundle I M))
        (Icc a d) := by
  obtain ⟨rho, a, d, has0, hbd, hrho, hrho_id, hrho_deriv, hrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      hKopen hsb hseg
  have hrhoMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun s : ℝ ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha (rho s)) (Y (rho s)) : TangentBundle I M)) := by
    rw [← contMDiffOn_univ]
    exact hfield.comp hrhoMD.contMDiffOn (fun s _hs ↦ hrange s)
  refine ⟨rho, a, d, has0, hbd, hrho, ?_, hrho_deriv, hrange,
    hsmooth, ?_⟩
  · intro s hs
    simpa only [id_eq] using hrho_id hs
  · intro s hs
    change TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (alpha (rho s)) (Y (rho s)) =
      TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
        (alpha s) (Y s)
    rw [hrho_id hs]
    simp only [id_eq]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry
