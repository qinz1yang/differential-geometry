import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.Convex

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

private theorem upper_unique_diff : UniqueDiffOn ℝ {z : ℂ | 0 ≤ z.im} := by
  apply uniqueDiffOn_convex (convex_halfSpace_im_ge 0)
  refine ⟨Complex.I, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
    (by simp : (0 : ℝ) < Complex.I.im)) (fun z hz => (show 0 < z.im from hz).le)

theorem iteratedDeriv_real_trace_eq_iteratedFDerivWithin
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}))
    {s : ℝ} (hs : (s : ℂ) ∈ U) :
    iteratedDeriv n (fun r : ℝ => f (r : ℂ)) s =
      iteratedFDerivWithin ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}) (s : ℂ)
        (fun _ : Fin n => (1 : ℂ)) := by
  let S := U ∩ {z : ℂ | 0 ≤ z.im}
  let J := Complex.ofRealCLM ⁻¹' S
  have hJ : J = Complex.ofRealCLM ⁻¹' U := by
    ext r
    simp [J, S]
  have hJO : IsOpen J := by
    rw [hJ]
    exact hU.preimage Complex.ofRealCLM.continuous
  have hSD : UniqueDiffOn ℝ S := by
    simpa only [S, inter_comm] using upper_unique_diff.inter hU
  have hsS : Complex.ofRealCLM s ∈ S := ⟨hs, by simp⟩
  have htrace : ContDiffAt ℝ n (f ∘ Complex.ofRealCLM) s :=
    (hf.comp_continuousLinearMap Complex.ofRealCLM).contDiffAt (hJO.mem_nhds hsS)
  calc
    iteratedDeriv n (fun r : ℝ => f (r : ℂ)) s =
        iteratedDerivWithin n (f ∘ Complex.ofRealCLM) J s :=
      (iteratedDerivWithin_eq_iteratedDeriv hJO.uniqueDiffOn htrace hsS).symm
    _ = _ := by
      rw [iteratedDerivWithin,
        Complex.ofRealCLM.iteratedFDerivWithin_comp_right hf hSD hJO.uniqueDiffOn hsS le_rfl]
      rfl

theorem iteratedFDerivWithin_tangent_eq_zero_of_real_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hzero : ∀ r : ℝ, (r : ℂ) ∈ U → f (r : ℂ) = 0)
    {s : ℝ} (hs : (s : ℂ) ∈ U) :
    iteratedFDerivWithin ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}) (s : ℂ)
      (fun _ : Fin n => (1 : ℂ)) = 0 := by
  rw [← iteratedDeriv_real_trace_eq_iteratedFDerivWithin hU hf hs]
  have he : (fun r : ℝ => f (r : ℂ)) =ᶠ[𝓝 s] fun _ => (0 : F) := by
    filter_upwards [(hU.preimage Complex.ofRealCLM.continuous).mem_nhds hs] with r hr
    exact hzero r hr
  rw [he.iteratedDeriv_eq n]
  simp

end DifferentialGeometry.Analysis
