import DifferentialGeometry.Analysis.ODE.Flow.Planar.TransverseCoordinates
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLine.Parametric
import DifferentialGeometry.Analysis.ODE.Flow.GlobalSliceSmoothness
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_inward_localFlow_of_one_sided
    {v : E × ℝ → E × ℝ} {V : Set E} {p : E} {ρ : ℝ}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hv : ContDiffOn ℝ ∞ v (V ×ˢ Icc 0 ρ)) (hinward : 0 < (v (p, 0)).2) :
    ∃ ε > 0, ∃ U : Set (E × ℝ), IsOpen U ∧ (p, 0) ∈ U ∧
      ∃ Φ : (E × ℝ) × ℝ → E × ℝ,
        (∀ z ∈ U, Φ (z, 0) = z) ∧
        ContDiffOn ℝ ∞ Φ (U ×ˢ Ioo (-ε) ε) ∧
        (∀ z ∈ U, StrictMonoOn (fun t ↦ (Φ (z, t)).2) (Ioo (-ε) ε)) ∧
        ∀ z ∈ U, 0 ≤ z.2 → ∀ t ∈ Ico 0 ε,
          Φ (z, t) ∈ V ×ˢ Icc 0 ρ ∧ z.2 ≤ (Φ (z, t)).2 ∧
          HasDerivAt (fun s ↦ Φ (z, s)) (v (Φ (z, t))) t := by
  obtain ⟨gext, W₀, hW₀, hgext, hext⟩ := DifferentialGeometry.Analysis.borel_interval_extend_param
    (fun t x ↦ v (x, t)) ρ hρ V p (by simpa only [hV.interior_eq] using hp)
    (hv.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun z hz ↦ ⟨hz.2, hz.1⟩))
  obtain ⟨W, hWW₀, hW, hpW⟩ := mem_nhds_iff.mp hW₀
  let g : E × ℝ → E × ℝ := fun z ↦ gext z.2 z.1
  let D := (W ∩ V) ×ˢ (univ : Set ℝ)
  have hD : IsOpen D := (hW.inter hV).prod isOpen_univ
  have hg : ContDiffOn ℝ ∞ g D :=
    hgext.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun z hz ↦ ⟨mem_univ _, hWW₀ hz.1.1⟩)
  have hgeq : ∀ z ∈ D, z.2 ∈ Icc 0 ρ → g z = v z :=
    fun z hz hr ↦ hext z.2 hr z.1 (hWW₀ hz.1.1)
  let Ω := D ∩ {z | 0 < (g z).2} ∩ {z : E × ℝ | z.2 < ρ}
  have hΩ : IsOpen Ω := by
    exact (hg.continuousOn.snd.isOpen_inter_preimage hD isOpen_Ioi).inter
      (isOpen_lt continuous_snd continuous_const)
  have hpD : (p, (0 : ℝ)) ∈ D := ⟨⟨hpW, hp⟩, mem_univ _⟩
  have hpΩ : (p, (0 : ℝ)) ∈ Ω := by
    refine ⟨⟨hpD, ?_⟩, hρ⟩
    change 0 < (g (p, 0)).2
    rw [hgeq _ hpD ⟨le_rfl, hρ.le⟩]
    exact hinward
  obtain ⟨ε, hε, hflow⟩ := DifferentialGeometry.Analysis.ODE.Flow.exists_flow_on hΩ
    (hg.mono (fun _ hz ↦ hz.1.1)) isCompact_singleton (singleton_subset_iff.mpr hpΩ)
  obtain ⟨U, hU, hpU, Φ, hΦzero, hΦ, hΦderiv, hΦΩ⟩ := hflow (p, 0) (mem_singleton _)
  have hnormal : ∀ z ∈ U, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s ↦ (Φ (z, s)).2) (g (Φ (z, t))).2 t := by
    intro z hz t ht
    exact (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivAt t (hΦderiv z hz t ht)
  have hmono : ∀ z ∈ U, StrictMonoOn (fun t ↦ (Φ (z, t)).2) (Ioo (-ε) ε) := by
    intro z hz
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro t ht
      exact (hnormal z hz t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioo] at ht
      rw [(hnormal z hz t ht).deriv]
      exact (hΦΩ ⟨hz, ht⟩).1.2
  refine ⟨ε, hε, U, hU, hpU, Φ, hΦzero, hΦ, hmono, ?_⟩
  intro z hz hzpos t ht
  have ht' : t ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], ht.2⟩
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hle : z.2 ≤ (Φ (z, t)).2 := by
    simpa only [hΦzero z hz] using (hmono z hz).monotoneOn h0 ht' ht.1
  have hr : (Φ (z, t)).2 ∈ Icc 0 ρ :=
    ⟨hzpos.trans hle, (hΦΩ ⟨hz, ht'⟩).2.le⟩
  refine ⟨⟨(hΦΩ ⟨hz, ht'⟩).1.1.1.2, hr⟩, hle, ?_⟩
  rw [← hgeq _ (hΦΩ ⟨hz, ht'⟩).1.1 hr]
  exact hΦderiv z hz t ht'

theorem exists_inward_flow_coordinates_of_one_sided
    {v : E × ℝ → E × ℝ} {V : Set E} {p : E} {ρ : ℝ}
    (hV : IsOpen V) (hp : p ∈ V) (hρ : 0 < ρ)
    (hv : ContDiffOn ℝ ∞ v (V ×ˢ Icc 0 ρ)) (hinward : 0 < (v (p, 0)).2) :
    ∃ e : OpenPartialHomeomorph (E × ℝ) (E × ℝ),
      (p, 0) ∈ e.source ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ x, (x, 0) ∈ e.source → e (x, 0) = (x, 0)) ∧
      (∀ z ∈ e.source, 0 ≤ (e z).2 ↔ 0 ≤ z.2) ∧
      (∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0) ∧
      ∀ z ∈ e.source, 0 ≤ z.2 →
        e z ∈ V ×ˢ Icc 0 ρ ∧
        HasDerivAt (fun t ↦ e (z.1, t)) (v (e z)) z.2 := by
  obtain ⟨ε, hε, U, hU, hpU, Φ, hzero, hΦ, hmono, hflow⟩ :=
    exists_inward_localFlow_of_one_sided hV hp hρ hv hinward
  let D := {z : E × ℝ | (z.1, (0 : ℝ)) ∈ U} ∩ (univ ×ˢ Ioo (-ε) ε)
  have hD : IsOpen D := (hU.preimage (continuous_fst.prodMk continuous_const)).inter
    (isOpen_univ.prod isOpen_Ioo)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_neg_of_pos hε, hε⟩
  have hpD : (p, (0 : ℝ)) ∈ D := ⟨hpU, mem_univ _, h0⟩
  let f : E × ℝ → E × ℝ := fun z ↦ Φ ((z.1, 0), z.2)
  have hf : ContDiffOn ℝ ∞ f D :=
    hΦ.comp ((contDiffOn_fst.prodMk contDiffOn_const).prodMk contDiffOn_snd)
      (fun z hz ↦ ⟨hz.1, hz.2.2⟩)
  have hfzero : ∀ x, (x, 0) ∈ D → f (x, 0) = (x, 0) :=
    fun x hx ↦ hzero (x, 0) hx.1
  have hd : HasDerivAt (fun t ↦ f (p, t)) (v (p, 0)) 0 := by
    have h := (hflow (p, 0) hpU le_rfl 0 ⟨le_rfl, hε⟩).2.2
    simpa only [hzero _ hpU] using h
  obtain ⟨e, hpe, heD, he, heinv, heq⟩ := exists_localInverse_of_transverse_zeroSlice
    hf hD hpD hfzero (by rw [hd.deriv]; exact ne_of_gt hinward)
  have hnonneg : ∀ z ∈ e.source, 0 ≤ (e z).2 ↔ 0 ≤ z.2 := by
    intro z hz
    have h := (hmono (z.1, 0) (heD hz).1).le_iff_le h0 (heD hz).2.2
    simpa only [hzero _ (heD hz).1, heq, f] using h
  have hezero : ∀ z ∈ e.source, (e z).2 = 0 ↔ z.2 = 0 := by
    intro z hz
    constructor
    · intro hez
      have h : (Φ ((z.1, 0), z.2)).2 = (Φ ((z.1, 0), 0)).2 := by
        simpa only [hzero _ (heD hz).1, heq, f] using hez
      exact (hmono (z.1, 0) (heD hz).1).injOn (heD hz).2.2 h0 h
    · intro hzr
      rw [heq]
      change (Φ ((z.1, 0), z.2)).2 = 0
      rw [hzr, hzero _ (heD hz).1]
  refine ⟨e, hpe, he, heinv, ?_, hnonneg, hezero, ?_⟩
  · intro x hx
    exact (heq _).trans (hfzero x (heD hx))
  · intro z hz hzr
    have h := hflow (z.1, 0) (heD hz).1 le_rfl z.2 ⟨hzr, (heD hz).2.2.2⟩
    refine ⟨?_, ?_⟩
    · simpa only [heq, f] using h.1
    · simpa only [heq, f] using h.2.2

end DifferentialGeometry.Analysis
