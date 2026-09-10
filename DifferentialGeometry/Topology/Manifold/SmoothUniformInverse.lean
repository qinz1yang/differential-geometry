import DifferentialGeometry.Topology.Manifold.ParameterizedInverse
import DifferentialGeometry.Topology.Manifold.StripExtension
import DifferentialGeometry.Analysis.Calculus.Inverse.UniformInverse
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

omit [I.Boundaryless] in
set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_verticalDeriv {h : M × ℝ → ℝ} (hh : ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h) :
    ContMDiff (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun q : M × ℝ ↦ deriv (fun r ↦ h (q.1, r)) q.2) := by
  intro q
  have hf : ContMDiff ((I.prod 𝓘(ℝ)).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun z : (M × ℝ) × ℝ ↦ h (z.1.1, z.2)) :=
    hh.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  have hd := ContMDiffAt.mfderiv_apply (I := 𝓘(ℝ)) (I' := 𝓘(ℝ))
    (fun (q : M × ℝ) r ↦ h (q.1, r)) Prod.snd id (fun _ : M × ℝ ↦ (1 : ℝ))
    (hf.contMDiffAt (x := (q, q.2))) contMDiffAt_snd contMDiffAt_id contMDiffAt_const
    (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv, id_eq] using hd

set_option backward.isDefEq.respectTransparency false in
theorem contMDiffOn_inverse_of_continuousOn [CompleteSpace E]
    {h : M × ℝ → ℝ} {U S : Set (M × ℝ)} {R : M × ℝ → ℝ}
    (hh : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h U) (hU : IsOpen U)
    (hR : ContinuousOn R S)
    (hRU : ∀ q ∈ S, (q.1, R q) ∈ U)
    (heq : ∀ q ∈ S, h (q.1, R q) = q.2)
    (hvertical : ∀ q ∈ S, deriv (fun r ↦ h (q.1, r)) (R q) ≠ 0) :
    ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ R S := by
  intro q hq
  obtain ⟨e, hp, _, _, heinv, he, _⟩ := exists_localInverse_preserving_parameter
    hh hU (hRU q hq) (hvertical q hq)
  have heq' : e (q.1, R q) = q := by rw [he _ hp, heq q hq]
  have htarget : q ∈ e.target := heq' ▸ e.map_source hp
  have hinv := contMDiffAt_snd.comp q (heinv.contMDiffAt (e.open_target.mem_nhds htarget))
  have hnear : ∀ᶠ z in 𝓝[S] q, (z.1, R z) ∈ e.source :=
    (continuousWithinAt_fst.prodMk (hR q hq)).preimage_mem_nhdsWithin
      (e.open_source.mem_nhds hp)
  have hagree : R =ᶠ[𝓝[S] q] fun z ↦ (e.symm z).2 := by
    filter_upwards [hnear, self_mem_nhdsWithin] with z hz hzS
    have hz' : e (z.1, R z) = z := by rw [he _ hz, heq z hzS]
    have h := congrArg Prod.snd (e.left_inv hz)
    simpa only [hz'] using h.symm
  have hat : R q = (e.symm q).2 := by
    have h := congrArg Prod.snd (e.left_inv hp)
    simpa only [heq'] using h.symm
  exact hinv.contMDiffWithinAt.congr_of_eventuallyEq hagree hat

set_option backward.isDefEq.respectTransparency false in
theorem exists_uniform_contMDiffOn_inverse_of_one_sided
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {h : M × ℝ → ℝ} {K : Set M} {ρ : ℝ}
    (hK : IsCompact K) (hρ : 0 < ρ)
    (hh : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ h (univ ×ˢ Icc 0 ρ))
    (hzero : ∀ p ∈ K, h (p, 0) = 0)
    (hpos : ∀ p ∈ K, 0 < derivWithin (fun r ↦ h (p, r)) (Icc 0 ρ) 0) :
    ∃ ε > 0, ε ≤ ρ ∧ ∃ σ > 0, ∃ R : M × ℝ → ℝ,
      ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ R (K ×ˢ Icc 0 σ) ∧
      (∀ p ∈ K, R (p, 0) = 0) ∧
      ∀ q ∈ K ×ˢ Icc 0 σ,
        R q ∈ Icc 0 ε ∧ h (q.1, R q) = q.2 ∧
        ∀ r ∈ Icc 0 ε, h (q.1, r) = q.2 → r = R q := by
  obtain ⟨g, hg, hgh⟩ := exists_contMDiff_extension_on_Icc hρ hh
  let dg : M × ℝ → ℝ := fun q ↦ deriv (fun r ↦ g (q.1, r)) q.2
  have hdg : Continuous dg := (contMDiff_verticalDeriv hg).continuous
  have hgd : ∀ p r, HasDerivAt (fun t ↦ g (p, t)) (dg (p, r)) r := by
    intro p r
    exact ((hg.comp (contMDiff_const.prodMk contMDiff_id)).contDiff.differentiable
      (by simp) r).hasDerivAt
  have hzero' : ∀ p ∈ K, g (p, 0) = 0 := by
    intro p hp
    exact (hgh ⟨mem_univ _, le_rfl, hρ.le⟩).trans (hzero p hp)
  have hpos' : ∀ p ∈ K, 0 < dg (p, 0) := by
    intro p hp
    have hd : HasDerivWithinAt (fun r ↦ h (p, r)) (dg (p, 0)) (Icc 0 ρ) 0 :=
      (hgd p 0).hasDerivWithinAt.congr
        (fun r hr ↦ (hgh ⟨mem_univ _, hr⟩).symm)
        (hgh ⟨mem_univ _, le_rfl, hρ.le⟩).symm
    rw [← hd.derivWithin (uniqueDiffOn_Icc hρ 0 ⟨le_rfl, hρ.le⟩)]
    exact hpos p hp
  obtain ⟨ε, hε, hερ, σ, hσ, R, hc, hRzero, hR⟩ :=
    Poincare.Analysis.exists_uniform_continuous_inverse_of_pos_deriv hK hρ
      hg.continuous.continuousOn hdg.continuousOn
      (fun p _ r _ ↦ (hgd p r).hasDerivWithinAt) hzero' hpos'
  have hsub : Icc (0 : ℝ) ε ⊆ Icc 0 ρ := Icc_subset_Icc_right hερ
  have hs : ContMDiffOn (I.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ R (K ×ˢ Icc 0 σ) :=
    contMDiffOn_inverse_of_continuousOn hg.contMDiffOn isOpen_univ hc
      (fun _ _ ↦ mem_univ _) (fun q hq ↦ (hR q hq).2.1)
      (fun q hq ↦ ne_of_gt (hR q hq).2.2.2)
  refine ⟨ε, hε, hερ, σ, hσ, R, hs, hRzero, ?_⟩
  intro q hq
  refine ⟨(hR q hq).1, ?_, ?_⟩
  · exact (hgh ⟨mem_univ _, hsub (hR q hq).1⟩).symm.trans (hR q hq).2.1
  · intro r hr heq
    exact (hR q hq).2.2.1 r hr ((hgh ⟨mem_univ _, hsub hr⟩).trans heq)

end Poincare.Topology.Manifold
