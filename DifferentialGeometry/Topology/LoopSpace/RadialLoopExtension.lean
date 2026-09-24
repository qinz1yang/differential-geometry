import DifferentialGeometry.Topology.LoopSpace.SpanningDisk
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section

open Set Function Manifold ContinuousMap
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

theorem loopCircle_coe_intCast (m : ℤ) : ((m : ℝ) : loopCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp [zsmul_eq_mul]⟩

theorem circleMap_arg_twoPi (t : ℝ) :
    (Complex.arg (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) / (2 * Real.pi) : loopCircle)
      = (t : loopCircle) := by
  have hsub : Complex.arg (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) - 2 * Real.pi * t
      = 2 * Real.pi * (⌊(Real.pi - 2 * Real.pi * t) / (2 * Real.pi)⌋ : ℤ) := by
    rw [Complex.exp_mul_I]
    exact Complex.arg_cos_add_sin_mul_I_sub (2 * Real.pi * t)
  have harg : Complex.arg (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))
      = (t + (⌊(Real.pi - 2 * Real.pi * t) / (2 * Real.pi)⌋ : ℤ)) * (2 * Real.pi) := by
    linarith
  have hval : Complex.arg (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) / (2 * Real.pi)
      = t + (⌊(Real.pi - 2 * Real.pi * t) / (2 * Real.pi)⌋ : ℤ) := by
    rw [harg, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ) * Real.pi ≠ 0)]
  rw [hval, add_comm]
  rw [AddCircle.coe_add, loopCircle_coe_intCast, zero_add]

theorem contDiffAt_arg_of_mem_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog : ContDiffAt ℝ ∞ Complex.log z := (Complex.contDiffAt_log hz).restrict_scalars ℝ
  have him : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.imCLM (Complex.log w)) z :=
    ContDiffAt.comp z Complex.imCLM.contDiff.contDiffAt hlog
  simpa only [Complex.imCLM_apply, Complex.log_im] using him

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem contMDiffOn_arg_loop (γ : freeLoop M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun z : ℂ => γ (((Complex.arg z / (2 * Real.pi) : ℝ) : loopCircle)))
      Complex.slitPlane := by
  refine hγ.comp_contMDiffOn (contMDiffOn_iff_contDiffOn.mpr ?_)
  intro z hz
  exact ((contDiffAt_arg_of_mem_slitPlane hz).div_const (2 * Real.pi)).contDiffWithinAt

theorem contMDiffOn_arg_neg_loop (γ : freeLoop M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun z : ℂ => γ (((Complex.arg (-z) / (2 * Real.pi) + 1 / 2 : ℝ) : loopCircle)))
      {z : ℂ | -z ∈ Complex.slitPlane} := by
  refine hγ.comp_contMDiffOn (contMDiffOn_iff_contDiffOn.mpr ?_)
  intro z hz
  exact ((((contDiffAt_arg_of_mem_slitPlane hz).comp z (contDiff_neg.contDiffAt)).div_const
    (2 * Real.pi)).add (contDiffAt_const (c := (1 / 2 : ℝ)))).contDiffWithinAt

theorem arg_neg_twoPi_add_half_eq (z : ℂ) (hz : z.im ≠ 0) :
    ((Complex.arg z / (2 * Real.pi) : ℝ) : loopCircle) =
      ((Complex.arg (-z) / (2 * Real.pi) + 1 / 2 : ℝ) : loopCircle) := by
  rcases lt_or_gt_of_ne hz with h | h
  · rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]
    have h1 : (Complex.arg z + Real.pi) / (2 * Real.pi) + 1 / 2
        = Complex.arg z / (2 * Real.pi) + 1 := by
      field_simp
      ring
    rw [h1, AddCircle.coe_add, AddCircle.coe_period, add_zero]
  · rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]
    have h1 : (Complex.arg z - Real.pi) / (2 * Real.pi) + 1 / 2
        = Complex.arg z / (2 * Real.pi) := by
      field_simp
      ring
    rw [h1]

def radialLoopExtension₀ (γ : freeLoop M) (z : ℂ) : M :=
  γ (((Complex.arg z / (2 * Real.pi) : ℝ) : loopCircle))

def radialLoopExtension₁ (γ : freeLoop M) (z : ℂ) : M :=
  γ (((Complex.arg (-z) / (2 * Real.pi) + 1 / 2 : ℝ) : loopCircle))

def radialLoopExtension (γ : freeLoop M) (z : ℂ) : M := by
  classical
  exact if z ∈ Complex.slitPlane then radialLoopExtension₀ γ z
    else if z = 0 then γ ((1 : ℝ) : loopCircle) else radialLoopExtension₁ γ z

theorem radialLoopExtension_zero (γ : freeLoop M) :
    radialLoopExtension γ 0 = γ ((1 : ℝ) : loopCircle) := by
  rw [radialLoopExtension, if_neg (by simp [Complex.slitPlane]), if_pos rfl]

theorem radialLoopExtension_eq₀ (γ : freeLoop M) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    radialLoopExtension γ z = radialLoopExtension₀ γ z := by
  rw [radialLoopExtension, if_pos hz]

theorem radialLoopExtension_eq₁ (γ : freeLoop M) {z : ℂ} (hz : -z ∈ Complex.slitPlane) :
    radialLoopExtension γ z = radialLoopExtension₁ γ z := by
  have hz0 : z ≠ 0 := fun h => by
    rw [h] at hz
    simp [Complex.slitPlane] at hz
  rw [radialLoopExtension]
  by_cases h : z ∈ Complex.slitPlane
  · rw [if_pos h]
    have him : z.im ≠ 0 := by
      intro him
      rcases Complex.mem_slitPlane_iff.mp h with h' | h'
      · rcases Complex.mem_slitPlane_iff.mp hz with h2 | h2
        · rw [Complex.neg_re] at h2
          linarith
        · exact h2 (by rw [Complex.neg_im, him, neg_zero])
      · exact h' him
    rw [radialLoopExtension₀, radialLoopExtension₁]
    exact congrArg γ (arg_neg_twoPi_add_half_eq z him)
  · rw [if_neg h, if_neg hz0]

theorem isOpen_radialSlitPlane : IsOpen {z : ℂ | -z ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage continuous_neg

theorem isOpen_ne_zero : IsOpen {z : ℂ | z ≠ 0} := isOpen_compl_singleton

theorem contMDiffOn_radialLoopExtension (γ : freeLoop M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (radialLoopExtension γ) {z : ℂ | z ≠ 0} := by
  have h₀ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (radialLoopExtension γ) Complex.slitPlane :=
    (contMDiffOn_arg_loop γ hγ).congr fun z hz => radialLoopExtension_eq₀ γ hz
  have h₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (radialLoopExtension γ)
      {z : ℂ | -z ∈ Complex.slitPlane} :=
    (contMDiffOn_arg_neg_loop γ hγ).congr fun z hz => radialLoopExtension_eq₁ γ hz
  intro z hz
  by_cases h : z ∈ Complex.slitPlane
  · exact (h₀.contMDiffAt (Complex.isOpen_slitPlane.mem_nhds h)).contMDiffWithinAt
  · have hre : z.re ≤ 0 := by
      by_contra hc
      exact h (Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_not_ge hc)))
    have him : z.im = 0 := by
      by_contra hc
      exact h (Complex.mem_slitPlane_iff.mpr (Or.inr hc))
    have hlt : z.re < 0 :=
      lt_of_le_of_ne hre fun hcon => hz (Complex.ext hcon him)
    have hz' : -z ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using neg_pos.mpr hlt))
    exact (h₁.contMDiffAt (isOpen_radialSlitPlane.mem_nhds hz')).contMDiffWithinAt

theorem radialLoopExtension_diskBoundary (γ : freeLoop M) (θ : loopCircle) :
    radialLoopExtension γ (diskBoundary θ : ℂ) = γ θ := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
  have hz : (diskBoundary (t : loopCircle) : ℂ)
      = Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) := diskBoundary_coe t
  rw [hz]
  by_cases hmem : Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) ∈ Complex.slitPlane
  · rw [radialLoopExtension_eq₀ γ hmem, radialLoopExtension₀, circleMap_arg_twoPi t]
  · have hz0 : Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I) ≠ 0 :=
      Complex.exp_ne_zero _
    have him : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)).im = 0 := by
      by_contra hc
      exact hmem (Complex.mem_slitPlane_iff.mpr (Or.inr hc))
    have hle : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)).re ≤ 0 := by
      by_contra hc
      exact hmem (Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_not_ge hc)))
    have hlt : (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)).re < 0 :=
      lt_of_le_of_ne hle fun hcon => hz0 (Complex.ext hcon him)
    have hargz : Complex.arg (Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I)) = Real.pi :=
      Complex.arg_eq_pi_iff.mpr ⟨hlt, him⟩
    have hargneg :
        Complex.arg (-(Complex.exp ((2 * Real.pi * t : ℝ) * Complex.I))) = 0 := by
      refine Complex.arg_eq_zero_iff.mpr ⟨?_, ?_⟩
      · rw [Complex.neg_re]
        linarith
      · rw [Complex.neg_im, him, neg_zero]
    rw [radialLoopExtension_eq₁ γ (by
      refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
      rw [Complex.neg_re]
      linarith),
      radialLoopExtension₁, hargneg]
    congr 1
    have hhalf : (0 : ℝ) / (2 * Real.pi) + 1 / 2 = Real.pi / (2 * Real.pi) := by
      field_simp
      ring
    rw [hhalf]
    have h := circleMap_arg_twoPi t
    rw [hargz] at h
    exact h

theorem exists_contMDiffOn_radialLoopExtension (γ : freeLoop M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun t : ℝ => γ (t : loopCircle))) :
    ∃ Γ : ℂ → M, ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Γ {z : ℂ | z ≠ 0} ∧
      ∀ θ : loopCircle, Γ (diskBoundary θ : ℂ) = γ θ :=
  ⟨radialLoopExtension γ, contMDiffOn_radialLoopExtension γ hγ,
    radialLoopExtension_diskBoundary γ⟩

end DifferentialGeometry.Topology
