import DifferentialGeometry.Topology.Manifold.Diffeomorph.CompactTranslation
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Function Manifold
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace Poincare.Manifold.Interval

theorem exists_smooth_compression_with_diffeomorph {ε r : ℝ} [Fact ((0 : ℝ) < ε)]
    (hr : 0 < r) (hrε : 2 * r ≤ ε) :
    ∃ a : ℝ, 0 < a ∧ a < r ∧
      ∃ (σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε)) (d : ℝ ≃ₘ[ℝ] ℝ),
        (∀ t : Icc (0 : ℝ) ε, (σ t).val = d t.val) ∧
        ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ ∧ StrictMono σ ∧
        range σ = {t : Icc (0 : ℝ) ε | a ≤ t.val} ∧
        (∀ t : Icc (0 : ℝ) ε, t.val ≤ r → (σ t).val = t.val + a) ∧
        ∀ t : Icc (0 : ℝ) ε, 2 * r ≤ t.val → σ t = t := by
  obtain ⟨a, ha, har, d, hd, hnear, hfar, _, _⟩ :=
    Poincare.Manifold.Diffeomorph.exists_compact_translation hr
  have h0 : d 0 = a := by simpa using hnear 0 ⟨by linarith, hr.le⟩
  have hε : d ε = ε := hfar ε (hrε.trans (le_abs_self ε))
  let σ : C(Icc (0 : ℝ) ε, Icc (0 : ℝ) ε) :=
    ⟨fun t => ⟨d t.val, by
      constructor
      · exact ha.le.trans (h0 ▸ hd.monotone t.property.1)
      · exact (hd.monotone t.property.2).trans hε.le⟩,
      by fun_prop⟩
  have hσ : ContMDiff (𝓡∂ 1) (𝓡∂ 1) ∞ σ := by
    intro t
    apply (ContMDiffAt.iff_comp_isImmersionAtOfComplement (f := σ)
      (isImmersionOfComplement_subtypeVal_Icc (x := (0 : ℝ)) (y := ε) (n := ∞) (σ t))).mpr
    refine ⟨σ.continuous.continuousAt, ?_⟩
    exact d.contMDiff.contMDiffAt.comp t contMDiff_subtypeVal_Icc.contMDiffAt
  refine ⟨a, ha, har, σ, d, (fun _ => rfl), hσ, fun _ _ h => hd h, ?_, ?_, ?_⟩
  · ext t
    constructor
    · rintro ⟨s, rfl⟩
      exact h0 ▸ hd.monotone s.property.1
    · intro ht
      have hL : 0 ≤ d.symm t.val := by
        apply hd.le_iff_le.mp
        rw [h0, d.apply_symm_apply]
        exact ht
      have hU : d.symm t.val ≤ ε := by
        apply hd.le_iff_le.mp
        rw [d.apply_symm_apply, hε]
        exact t.property.2
      exact ⟨⟨d.symm t.val, hL, hU⟩, Subtype.ext (d.apply_symm_apply t.val)⟩
  · intro t ht
    exact hnear t.val ⟨by linarith [t.property.1], ht⟩
  · intro t ht
    exact Subtype.ext (hfar t.val (ht.trans (le_abs_self t.val)))

end Poincare.Manifold.Interval
