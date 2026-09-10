import DifferentialGeometry.Topology.Manifold.NonvanishingHomotopy
import DifferentialGeometry.Topology.Connected.RectangleComplement
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ParameterizedConstantFlow
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ConstantHyperplaneFlow
import Mathlib.Dynamics.Flow

noncomputable section
open Set
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

theorem exists_rectangle_deformation_with_smooth_flows
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hne : ∀ z, f z ≠ 0)
    (a b c d : ℝ)
    (hfixed : ∀ z : ℂ, z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im → f z = 1) :
    ∃ V : ℝ × ℂ → ℂ, ContDiff ℝ ∞ V ∧
      (∀ p z, V (p, z) ≠ 0) ∧ (∀ z, V (0, z) = f z) ∧ (∀ z, V (1, z) = 1) ∧
      (∀ p z, z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im → V (p, z) = 1) ∧
      ∃ φ : ℝ → _root_.Flow ℝ ℂ,
        ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ ↦ φ q.1 q.2.1 q.2.2) ∧
        (∀ p ∈ Icc (0 : ℝ) 1, ∀ z t,
          HasDerivAt (fun s ↦ φ p s z) (V (p, φ p t z)) t) ∧
        ∀ t z, φ 1 t z = z + t • (1 : ℂ) := by
  obtain ⟨V, hVm, hnz, hzero, hone, hout⟩ :=
    exists_smooth_nonvanishing_homotopy_relative hf.contMDiff hne
      (Poincare.Topology.isConnected_compl_openRectangle a b c d) hfixed
  have hparam : ContMDiff 𝓘(ℝ, ℝ × ℂ) (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) ∞
      (fun p : ℝ × ℂ ↦ p) := contDiff_fst.contMDiff.prodMk contDiff_snd.contMDiff
  have hV : ContDiff ℝ ∞ V := (hVm.comp hparam).contDiff
  let K : Set ℂ := Complex.reProdIm (Icc a b) (Icc c d)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have houtside (p : ℝ) (z : ℂ) (hz : z ∉ K) : V (p, z) = 1 := by
    apply hout p z
    by_contra h
    change ¬ (z.re ≤ a ∨ b ≤ z.re ∨ z.im ≤ c ∨ d ≤ z.im) at h
    push Not at h
    exact hz ⟨⟨h.1.le, h.2.1.le⟩, h.2.2.1.le, h.2.2.2.le⟩
  obtain ⟨D, hD, hderiv, hDzero, hadd, _⟩ :=
    Poincare.Analysis.exists_smoothFlow_family_of_uniform_const_off_compact hV (1 : ℂ)
      (isCompact_Icc (a := (0 : ℝ)) (b := 1)) hK houtside
  let φ (p : ℝ) : _root_.Flow ℝ ℂ := {
    toFun := fun t z ↦ D p t z
    cont' := (hD.comp (contDiff_const.prodMk contDiff_id)).continuous
    map_add' := fun t s z ↦ by rw [add_comm, hadd]; rfl
    map_zero' := fun z ↦ by rw [hDzero]; rfl }
  refine ⟨V, hV, hnz, hzero, hone, hout, φ, hD, hderiv, ?_⟩
  intro t z
  have he := Poincare.Analysis.integralCurve_eq_translation_on_constant_hyperplane
    ((hV.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp))
    (0 : ℂ →L[ℝ] ℝ) (1 : ℂ) (b := 0) (by simp) (fun w _ ↦ hone w)
    (γ := fun s ↦ φ 1 s z) (fun s ↦ hderiv 1 (by norm_num) z s) (t := 0) (by simp) t
  simpa only [(φ 1).map_zero_apply, sub_zero] using he

end Poincare.Topology.Manifold
