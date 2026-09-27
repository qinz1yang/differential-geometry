import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.DirectionalJets
import Mathlib.Analysis.Convex.Topology
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

private theorem upper_half_plane_geometry {U : Set ℂ} (hU : IsOpen U) :
    UniqueDiffOn ℝ (U ∩ {z : ℂ | 0 ≤ z.im}) ∧
      U ∩ {z : ℂ | 0 ≤ z.im} ⊆ closure (interior (U ∩ {z : ℂ | 0 ≤ z.im})) := by
  have hne : (interior {z : ℂ | 0 ≤ z.im}).Nonempty := by
    refine ⟨Complex.I, mem_interior_iff_mem_nhds.mpr ?_⟩
    exact mem_of_superset ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
      (by simp : (0 : ℝ) < Complex.I.im)) (fun z hz => (show 0 < z.im from hz).le)
  constructor
  · simpa only [inter_comm] using upper_unique_diff.inter hU
  · intro z hz
    rw [interior_inter, hU.interior_eq]
    apply hU.inter_closure
    refine ⟨hz.1, ?_⟩
    rw [(convex_halfSpace_im_ge 0).closure_interior_eq_closure_of_nonempty_interior hne]
    exact subset_closure hz.2

theorem fderivWithin_tangent_eq_iteratedDeriv_normal_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f (U ∩ {z : ℂ | 0 ≤ z.im}))
    {s : ℝ} (hs : (s : ℂ) ∈ U) :
    fderivWithin ℝ
      (fun z => iteratedFDerivWithin ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}) z
        (fun _ : Fin n => (1 : ℂ)))
      (U ∩ {z : ℂ | 0 ≤ z.im}) (s : ℂ) Complex.I =
      iteratedDeriv n (fun r : ℝ =>
        fderivWithin ℝ f (U ∩ {z : ℂ | 0 ≤ z.im}) (r : ℂ) Complex.I) s := by
  obtain ⟨hUD, hcl⟩ := upper_half_plane_geometry hU
  have hsS : (s : ℂ) ∈ U ∩ {z : ℂ | 0 ≤ z.im} := ⟨hs, by simp⟩
  have hC1 : ContDiffWithinAt ℝ 1
      (iteratedFDerivWithin ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}))
      (U ∩ {z : ℂ | 0 ≤ z.im}) (s : ℂ) := by
    apply (hf _ hsS).iteratedFDerivWithin_right hUD _ hsS
    norm_cast
    omega
  rw [fderivWithin_continuousMultilinear_apply_const_apply (hUD _ hsS)
    (hC1.differentiableWithinAt (by simp))]
  rw [fderivWithin_iteratedFDerivWithin_apply_eq hUD hcl n (by simpa using hf) Complex.I _ hsS]
  have hD : ContDiffOn ℝ n
      (fun z => fderivWithin ℝ f (U ∩ {z : ℂ | 0 ≤ z.im}) z Complex.I)
      (U ∩ {z : ℂ | 0 ≤ z.im}) :=
    (hf.fderivWithin hUD (by simp)).clm_apply contDiffOn_const
  exact (iteratedDeriv_real_trace_eq_iteratedFDerivWithin hU hD hs).symm

theorem fderivWithin_tangent_eq_zero_of_neumann_trace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set ℂ} (hU : IsOpen U) {f : ℂ → F} {n : ℕ}
    (hf : ContDiffOn ℝ (n + 1) f (U ∩ {z : ℂ | 0 ≤ z.im}))
    (hzero : ∀ r : ℝ, (r : ℂ) ∈ U →
      fderivWithin ℝ f (U ∩ {z : ℂ | 0 ≤ z.im}) (r : ℂ) Complex.I = 0)
    {s : ℝ} (hs : (s : ℂ) ∈ U) :
    fderivWithin ℝ
      (fun z => iteratedFDerivWithin ℝ n f (U ∩ {z : ℂ | 0 ≤ z.im}) z
        (fun _ : Fin n => (1 : ℂ)))
      (U ∩ {z : ℂ | 0 ≤ z.im}) (s : ℂ) Complex.I = 0 := by
  rw [fderivWithin_tangent_eq_iteratedDeriv_normal_trace hU hf hs]
  have he : (fun r : ℝ =>
      fderivWithin ℝ f (U ∩ {z : ℂ | 0 ≤ z.im}) (r : ℂ) Complex.I) =ᶠ[𝓝 s]
      fun _ => (0 : F) := by
    filter_upwards [(hU.preimage Complex.ofRealCLM.continuous).mem_nhds hs] with r hr
    exact hzero r hr
  rw [he.iteratedDeriv_eq n]
  simp


end DifferentialGeometry.Analysis
