import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Extension
import DifferentialGeometry.Analysis.ODE.Flow.CompactSupport

open Set Function Manifold Filter
open scoped Topology ContDiff
set_option autoImplicit false
noncomputable section

namespace Poincare.Manifold.BoundaryCollar

private theorem exists_complete_euclidean_flow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (g : E → E) (hg : ContDiff ℝ ∞ g) (hgK : HasCompactSupport g) :
    ∃ Φ : E × ℝ → E, ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (x, 0) = x) ∧
      (∀ x s t, Φ (Φ (x, s), t) = Φ (x, s + t)) ∧
      (∀ t, Injective (fun x => Φ (x, t))) ∧
      ∀ x t, HasDerivAt (fun s => Φ (x, s)) (g (Φ (x, t))) t := by
  let V : (x : E) → TangentSpace 𝓘(ℝ, E) x := g
  have hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hg
  let hc := DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport V hV hgK
  let Φ : E × ℝ → E := fun p => DifferentialGeometry.Analysis.ODE.curveAt V hc p.1 p.2
  have hΦ : ContDiff ℝ ∞ Φ := by
    have hh := (DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      V hV hgK).comp (contMDiff_snd.prodMk contMDiff_fst)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact contMDiff_iff_contDiff.mp hh
  refine ⟨Φ, hΦ, DifferentialGeometry.Analysis.ODE.curveAt_zero V hc, ?_, ?_, ?_⟩
  · intro x s t
    exact (DifferentialGeometry.Analysis.ODE.curveAt_add V
      (hV.of_le (by norm_num)) hc x s t).symm
  · exact DifferentialGeometry.Analysis.ODE.curveAt_injective V (hV.of_le (by norm_num)) hc
  · intro x t
    have hd : HasFDerivAt (fun s => Φ (x, s))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (g (Φ (x, t)))) t := by
      exact (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve V hc x t).hasFDerivAt
    simpa using hd.hasDerivAt

theorem exists_inward_halfSpace_localFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} (hU : IsOpen U) {z : E} (hz : (0, z) ∈ U)
    {f : ℝ × E → ℝ × E}
    (hf : ContDiffOn ℝ ∞ f ((Ici (0 : ℝ) ×ˢ (univ : Set E)) ∩ U))
    (hpos : 0 < (f (0, z)).1) :
    ∃ Φ : (ℝ × E) × ℝ → ℝ × E, ContDiff ℝ ∞ Φ ∧
      (∀ x, Φ (x, 0) = x) ∧
      (∀ x s t, Φ (Φ (x, s), t) = Φ (x, s + t)) ∧
      (∀ t, Injective (fun x => Φ (x, t))) ∧
      ∃ W : Set (ℝ × E), IsOpen W ∧ (0, z) ∈ W ∧ W ⊆ U ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x ∈ W, 0 ≤ x.1 → ∀ t ∈ Icc (0 : ℝ) ε,
            Φ (x, t) ∈ U ∧ 0 ≤ (Φ (x, t)).1 ∧
            HasDerivAt (fun s => Φ (x, s)) (f (Φ (x, t))) t ∧
            (0 < t → 0 < (Φ (x, t)).1) := by
  obtain ⟨g, hg, hgK, hgf⟩ := exists_contDiff_halfSpace_extension hU hz hf
  obtain ⟨Φ, hΦ, hzero, hadd, hinj, hder⟩ := exists_complete_euclidean_flow g hg hgK
  have hgpos : 0 < (g (0, z)).1 := by
    rw [hgf.eq_of_nhdsWithin (by simp)]
    exact hpos
  obtain ⟨A, hA, hAgf⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hgf
  have hspeed : {x | 0 < (g x).1} ∈ 𝓝 ((0 : ℝ), z) :=
    (isOpen_lt continuous_const (hg.continuous.fst)).mem_nhds hgpos
  have hstay : {p | Φ p ∈ U ∩ A ∩ {x | 0 < (g x).1}} ∈ 𝓝 (((0 : ℝ), z), (0 : ℝ)) := by
    apply hΦ.continuous.continuousAt.preimage_mem_nhds
    rw [hzero]
    exact inter_mem (inter_mem (hU.mem_nhds hz) hA) hspeed
  obtain ⟨B, hB, T, hT, hBT⟩ := mem_nhds_prod_iff.mp hstay
  obtain ⟨W, hWB, hW, hzW⟩ := mem_nhds_iff.mp (inter_mem hB (hU.mem_nhds hz))
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhds_iff.mp hT
  let ε := r / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ∀ x ∈ W, ∀ t ∈ Icc (0 : ℝ) ε,
      Φ (x, t) ∈ U ∩ A ∩ {y | 0 < (g y).1} := by
    intro x hx t ht
    apply hBT ⟨(hWB hx).1, hrT ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    dsimp [ε] at ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨Φ, hΦ, hzero, hadd, hinj, W, hW, hzW, fun x hx => (hWB hx).2, ε, hε, ?_⟩
  intro x hx hxpos t ht
  have hmono : StrictMonoOn (fun s => (Φ (x, s)).1) (Icc (0 : ℝ) ε) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      ((hΦ.continuous.comp (continuous_const.prodMk continuous_id)).fst.continuousOn)
    intro s hs
    have hds := (ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt s (hder x s)
    change HasDerivAt (fun s => (Φ (x, s)).1) (g (Φ (x, s))).1 s at hds
    change 0 < deriv (fun s => (Φ (x, s)).1) s
    rw [hds.deriv]
    exact (hsmall x hx s (interior_subset hs)).2
  have hn : 0 ≤ (Φ (x, t)).1 := by
    have hh := hmono.monotoneOn (show (0 : ℝ) ∈ Icc (0 : ℝ) ε from ⟨le_rfl, hε.le⟩) ht ht.1
    rw [hzero] at hh
    exact hxpos.trans hh
  refine ⟨(hsmall x hx t ht).1.1, hn, ?_, ?_⟩
  · rw [← hAgf ⟨(hsmall x hx t ht).1.2, hn, mem_univ _⟩]
    exact hder x t
  · intro htpos
    have hh := hmono (show (0 : ℝ) ∈ Icc (0 : ℝ) ε from ⟨le_rfl, hε.le⟩) ht htpos
    change (Φ (x, 0)).1 < (Φ (x, t)).1 at hh
    rw [hzero] at hh
    exact hxpos.trans_lt hh

end Poincare.Manifold.BoundaryCollar
