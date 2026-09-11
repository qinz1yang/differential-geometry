import DifferentialGeometry.Analysis.ODE.Flow.Planar.LeftEdgeCoordinates

open Set
open scoped ContDiff

namespace DifferentialGeometry.Analysis

theorem mem_square_iff_time_mem_Icc
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v z = 1)
    {y T : ℝ} (hy : y ∈ Icc 0 1) (hT : (φ T (y • Complex.I)).re = 1) (t : ℝ) :
    φ t (y • Complex.I) ∈ Complex.reProdIm (Icc 0 1) (Icc 0 1) ↔ t ∈ Icc 0 T := by
  let γ : ℝ → ℂ := fun t ↦ φ t (y • Complex.I)
  have hγ (t : ℝ) : HasDerivAt γ (v (γ t)) t := hderiv (y • Complex.I) t
  have hright (z : ℂ) (hz : 1 ≤ z.re) : v z = 1 := hfixed z (Or.inr (Or.inl hz))
  have hrealray {s r : ℝ} (hs : 1 ≤ (γ s).re) (hr : 0 ≤ r) :
      (γ (s + r)).re = (γ s).re + r := by
    have he := integralCurve_eq_translation_in_constant_halfSpace hv Complex.reCLM (1 : ℂ)
      (by simp) hright hγ hs hr
    simpa [Complex.real_smul] using congrArg Complex.re he
  constructor
  · intro hz
    obtain ⟨u, _, s, hs, _, huniq⟩ := exists_leftEdge_flow_coordinates φ hv hnz hderiv hfixed
      hz.1 hz.2
    have hts : t = s := (huniq y t rfl).2
    refine ⟨hts ▸ hs, ?_⟩
    by_contra ht
    have he := hrealray hT.ge (sub_nonneg.mpr (lt_of_not_ge ht).le)
    rw [add_sub_cancel] at he
    have hzre : (γ t).re ≤ 1 := hz.1.2
    linarith [hzre]
  · intro ht
    have hleft : 0 ≤ (γ t).re :=
      le_of_integralCurve_constant_incoming_halfSpace hv Complex.reCLM (1 : ℂ)
        (by simp) (fun z hz ↦ hfixed z (Or.inl hz)) hγ
        (by simp [γ, Complex.real_smul]) ht.1
    have hupper : (γ t).re ≤ 1 := by
      by_contra hu
      have he := hrealray (lt_of_not_ge hu).le (sub_nonneg.mpr ht.2)
      rw [add_sub_cancel] at he
      linarith [ht.2]
    have hlo := le_iff_of_integralCurve_constant_hyperplane (hv.of_le (by simp))
      (-Complex.imCLM) 1 (by simp) (b := 0)
      (fun z hz ↦ hfixed z (Or.inr (Or.inr (Or.inl (by simpa using hz.ge))))) hγ t 0
    have hhi := le_iff_of_integralCurve_constant_hyperplane (hv.of_le (by simp))
      Complex.imCLM 1 (by simp) (b := 1)
      (fun z hz ↦ hfixed z (Or.inr (Or.inr (Or.inr hz.ge)))) hγ t 0
    refine ⟨⟨hleft, hupper⟩, ?_, ?_⟩
    · simpa [γ] using hlo.mpr (by simpa [γ, Complex.real_smul] using hy.1)
    · exact hhi.mpr (by simpa [γ, Complex.real_smul] using hy.2)

theorem bijOn_leftEdge_flow_strip
    (φ : _root_.Flow ℝ ℂ) {v : ℂ → ℂ} (hv : ContDiff ℝ ∞ v)
    (hnz : ∀ z, v z ≠ 0)
    (hderiv : ∀ z t, HasDerivAt (fun s ↦ φ s z) (v (φ t z)) t)
    (hfixed : ∀ z : ℂ, z.re ≤ 0 ∨ 1 ≤ z.re ∨ z.im ≤ 0 ∨ 1 ≤ z.im → v z = 1)
    {τ : ℝ → ℝ} (hexit : ∀ y ∈ Icc (0 : ℝ) 1, (φ (τ y) (y • Complex.I)).re = 1) :
    BijOn (fun p : ℝ × ℝ ↦ φ p.2 (p.1 • Complex.I))
      {p | p.1 ∈ Icc 0 1 ∧ p.2 ∈ Icc 0 (τ p.1)}
      (Complex.reProdIm (Icc 0 1) (Icc 0 1)) := by
  refine ⟨fun p hp ↦ (mem_square_iff_time_mem_Icc φ hv hnz hderiv hfixed hp.1
      (hexit p.1 hp.1) p.2).mpr hp.2,
    (injective_leftEdge_flow_coordinates φ hv hderiv (fun z hz ↦ hfixed z (Or.inl hz))).injOn, ?_⟩
  intro z hz
  obtain ⟨y, hy, t, _, he, _⟩ := exists_leftEdge_flow_coordinates φ hv hnz hderiv hfixed hz.1 hz.2
  refine ⟨(y, t), ⟨hy, ?_⟩, he⟩
  exact (mem_square_iff_time_mem_Icc φ hv hnz hderiv hfixed hy (hexit y hy) t).mp (he.symm ▸ hz)

end DifferentialGeometry.Analysis
