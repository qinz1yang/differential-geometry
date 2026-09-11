import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowBox
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set Function Manifold Filter
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_positive_flowBox_of_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {Φ : (ℝ × E) × ℝ → ℝ × E} (hΦ : ContDiff ℝ ∞ Φ)
    (hzero : ∀ y, Φ (y, 0) = y) {g : ℝ × E → ℝ × E}
    (hg : Continuous g)
    (hder : ∀ x t, HasDerivAt (fun s => Φ (x, s)) (g (Φ (x, t))) t)
    {z : E} (hpos : 0 < (g (0, z)).1)
    {N : Set (ℝ × E)} (hN : N ∈ 𝓝 ((0 : ℝ), z)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) 1,
      (0, z) ∈ e.source ∧ (e : ℝ × E → ℝ × E) = (fun p => Φ ((0, p.2), p.1)) ∧
      e.target ⊆ N ∧
      (∀ p ∈ e.source, 0 ≤ (e p).1 ↔ 0 ≤ p.1) ∧
      (∀ p ∈ e.source, (e p).1 = 0 ↔ p.1 = 0) ∧
      ∀ p ∈ e.source, ∀ t ∈ Icc (0 : ℝ) p.1,
        Φ ((0, p.2), t) ∈ N ∧ 0 ≤ (Φ ((0, p.2), t)).1 := by
  let Ψ : ℝ × E → ℝ × E := fun p => Φ ((0, p.2), p.1)
  have hΨ : ContDiff ℝ ∞ Ψ := hΦ.comp ((contDiff_const.prodMk contDiff_snd).prodMk contDiff_fst)
  have hspeed : {x | 0 < (g x).1} ∈ 𝓝 ((0 : ℝ), z) :=
    (isOpen_lt continuous_const hg.fst).mem_nhds hpos
  have hstay : Ψ ⁻¹' (N ∩ {x | 0 < (g x).1}) ∈ 𝓝 ((0 : ℝ), z) := by
    apply hΨ.continuous.continuousAt.preimage_mem_nhds
    change N ∩ {x | 0 < (g x).1} ∈ 𝓝 (Φ ((0, z), 0))
    rw [hzero]
    exact inter_mem hN hspeed
  obtain ⟨T, hT, B, hB, hTB⟩ := mem_nhds_prod_iff.mp hstay
  obtain ⟨W, hWB, hW, hzW⟩ := mem_nhds_iff.mp hB
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp hT
  let ε := r / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ∀ w ∈ W, ∀ t ∈ Icc (-ε) ε,
      Ψ (t, w) ∈ N ∩ {x | 0 < (g x).1} := by
    intro w hw t ht
    apply hTB ⟨hrT ?_, hWB hw⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    dsimp [ε] at ht
    constructor <;> linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hmono : ∀ w ∈ W, StrictMonoOn (fun t => (Ψ (t, w)).1) (Icc (-ε) ε) := by
    intro w hw
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((hΨ.continuous.comp (continuous_id.prodMk continuous_const)).fst.continuousOn)
    intro t ht
    have hd := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t (hder (0, w) t)
    change HasDerivAt (fun t => (Ψ (t, w)).1) (g (Ψ (t, w))).1 t at hd
    change 0 < deriv (fun t => (Ψ (t, w)).1) t
    rw [hd.deriv]
    exact (hsmall w hw t (interior_subset ht)).2
  obtain ⟨e, he, heq⟩ := exists_flowBox_of_flow hΦ hzero
    (by simpa only [hzero] using hder (0, z) 0) hpos.ne'
  let S : Set (ℝ × E) := Ioo (-ε) ε ×ˢ W
  have hS : IsOpen S := isOpen_Ioo.prod hW
  let e' := e.toOpenPartialHomeomorph.restrOpen S hS
  let e'' : PartialDiffeomorph 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ × E) (ℝ × E) (ℝ × E) 1 := {
    toPartialEquiv := e'.toPartialEquiv
    open_source := e'.open_source
    open_target := e'.open_target
    contMDiffOn_toFun := e.contMDiffOn_toFun.mono inter_subset_left
    contMDiffOn_invFun := e.contMDiffOn_invFun.mono inter_subset_left }
  have hsource (p : ℝ × E) (hp : p ∈ e''.source) : p.1 ∈ Icc (-ε) ε ∧ p.2 ∈ W :=
    ⟨⟨hp.2.1.1.le, hp.2.1.2.le⟩, hp.2.2⟩
  have heq' : (e'' : ℝ × E → ℝ × E) = Ψ := heq
  refine ⟨e'', ⟨he, ⟨by linarith, hε⟩, hzW⟩, heq', ?_, ?_, ?_, ?_⟩
  · intro y hy
    have hp := e''.toPartialEquiv.map_target hy
    have hh := hsmall (e''.symm y).2 (hsource _ hp).2 (e''.symm y).1 (hsource _ hp).1
    have hh' : e'' (e''.symm y) ∈ N := by rw [heq']; exact hh.1
    have hright : e'' (e''.symm y) = y := e''.toPartialEquiv.right_inv hy
    rwa [hright] at hh'
  · intro p hp
    have hh := (hmono p.2 (hsource p hp).2).le_iff_le h0 (hsource p hp).1
    simpa only [Ψ, hzero, heq'] using hh
  · intro p hp
    have hh := (hmono p.2 (hsource p hp).2).eq_iff_eq (hsource p hp).1 h0
    simpa only [Ψ, hzero, heq'] using hh
  · intro p hp t ht
    have htp : t ∈ Icc (-ε) ε := ⟨h0.1.trans ht.1, ht.2.trans (hsource p hp).1.2⟩
    refine ⟨(hsmall p.2 (hsource p hp).2 t htp).1, ?_⟩
    have hh := (hmono p.2 (hsource p hp).2).monotoneOn h0 htp ht.1
    simpa only [Ψ, hzero] using hh

end DifferentialGeometry.Manifold.BoundaryCollar
