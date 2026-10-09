import DifferentialGeometry.Topology.Manifold.Curve
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-!
# Escaping a corner along a curve (lane O-G6C, G2j)

`exists_escape_of_surjective_G6C`: at an interior point `p` of a manifold, if two real functions
`g, T` differentiable at `p` have jointly onto differentials, then every neighbourhood of `p`
contains a point where both `g` and `T` are strictly larger than at `p` (follow a curve with
velocity `v`, `dg v = dT v = 1`).
-/

set_option autoImplicit false

open Set Filter Function Bundle
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A real function along a curve: positive derivative gives larger values just after `0`. -/
theorem eventually_lt_of_hasDerivAt_pos_G6C {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hd : 0 < d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), f 0 < f t := by
  have hs := (hasDerivAt_iff_tendsto_slope.mp hf).eventually_const_lt hd
  have hs' : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < slope f 0 t :=
    hs.filter_mono (nhdsWithin_mono _ fun t ht => ne_of_gt ht)
  filter_upwards [hs', self_mem_nhdsWithin] with t ht htpos
  rw [slope_def_field, sub_zero] at ht
  have htp : (0 : ℝ) < t := htpos
  have := (div_pos_iff_of_pos_right htp).mp ht
  linarith

/-- **Escaping a corner.** -/
theorem exists_escape_of_surjective_G6C {g T : M → ℝ} {p : M} (hp : I.IsInteriorPoint p)
    (hg : MDifferentiableAt I 𝓘(ℝ, ℝ) g p) (hT : MDifferentiableAt I 𝓘(ℝ, ℝ) T p)
    (hsurj : Surjective fun v : TangentSpace I p => (mvfderiv I g p v, mvfderiv I T p v))
    {N : Set M} (hN : N ∈ 𝓝 p) : ∃ q ∈ N, g p < g q ∧ T p < T q := by
  obtain ⟨v, hv⟩ := hsurj (1, 1)
  have hv1 : mfderiv I 𝓘(ℝ, ℝ) g p v = (1 : ℝ) := congrArg Prod.fst hv
  have hv2 : mfderiv I 𝓘(ℝ, ℝ) T p v = (1 : ℝ) := congrArg Prod.snd hv
  obtain ⟨ε, hε, γ, hγs, hγN, hγ0⟩ :=
    exists_contMDiff_curve_with_velocity (n := ∞) (by simp) hp v hN
  have h0 : γ 0 = p := congrArg TotalSpace.proj hγ0
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
    (hγs.contMDiffAt (Icc_mem_nhds (by linarith) hε)).mdifferentiableAt (by simp)
  subst h0
  have hD : mfderiv 𝓘(ℝ, ℝ) I γ 0 ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1) = v :=
    eq_of_heq (TotalSpace.mk.inj hγ0).2
  have hder : ∀ G : M → ℝ, MDifferentiableAt I 𝓘(ℝ, ℝ) G (γ 0) →
      HasDerivAt (G ∘ γ) (mfderiv I 𝓘(ℝ, ℝ) G (γ 0) v) 0 := by
    intro G hG
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (G ∘ γ) 0 := hG.comp 0 hγd
    have hdiff : DifferentiableAt ℝ (G ∘ γ) 0 := mdifferentiableAt_iff_differentiableAt.mp hcd
    have hc := hG.hasMFDerivAt.comp 0 hγd.hasMFDerivAt
    have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (G ∘ γ) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (G ∘ γ) 0)) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr hdiff.hasDerivAt.hasFDerivAt
    have h3 := hc.mfderiv.symm.trans h2.mfderiv
    have h4 := congrArg (fun L => L (show TangentSpace 𝓘(ℝ, ℝ) (0 : ℝ) from (1 : ℝ))) h3
    have hval : deriv (G ∘ γ) 0 = mfderiv I 𝓘(ℝ, ℝ) G (γ 0) v := by
      rw [← hD]
      have h5 : ((1 : ℝ →L[ℝ] ℝ).smulRight (deriv (G ∘ γ) 0)) (1 : ℝ) = deriv (G ∘ γ) 0 := by
        simp
      exact h5.symm.trans h4.symm
    rw [← hval]
    exact hdiff.hasDerivAt
  have hg' := eventually_lt_of_hasDerivAt_pos_G6C (hder g hg) (by rw [hv1]; norm_num)
  have hT' := eventually_lt_of_hasDerivAt_pos_G6C (hder T hT) (by rw [hv2]; norm_num)
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Icc (-ε) ε :=
    mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds (by linarith) hε)
  obtain ⟨t, ht1, ht2, ht3⟩ := (hg'.and (hT'.and hsmall)).exists
  exact ⟨γ t, hγN ht3, ht1, ht2⟩

end DifferentialGeometry.Topology.Manifold
