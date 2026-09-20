import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Composition

noncomputable section
open Set Filter MeasureTheory
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open scoped Topology ENNReal NNReal ContDiff

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)


theorem IsHomogeneousWeakSolution.ae_le_of_memH01_sub
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {A : EllipticCoeff d Ω} {u h : E → ℝ} (hh : IsHomogeneousWeakSolution A h)
    (hu : MemW1pWitness 2 u Ω) (hhu : MemW01p 2 (fun x => h x - u x) Ω)
    {k : ℝ} (huk : ∀ᵐ x ∂volume.restrict Ω, u x ≤ k) : ∀ᵐ x ∂volume.restrict Ω, h x ≤ k := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  let hw := MemW1p.someWitness hh.1
  let hwk := hw.subConst hΩ k
  let huk' := hu.subConst hΩ k
  have hdif : MemW01p 2 (fun x => (h x - k) - (u x - k)) Ω := by
    simpa only [sub_sub_sub_cancel_right] using hhu
  have hβder (s : ℝ) : ‖deriv Real.smoothTransition s‖ ≤ Mst := by
    exact_mod_cast smoothTransition_nnnorm_deriv_le s
  let ψ := fun x => Real.smoothTransition (h x - k)
  have hψ0 : MemH01 ψ Ω := MemW01p.comp_smooth_of_eq_zero_on_datum hΩ huk' hdif
    Real.smoothTransition Real.smoothTransition.contDiff Real.smoothTransition.zero hβder
    (huk.mono fun x hx => Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx))
  let hψ : MemW1pWitness 2 ψ Ω := hwk.compSmoothBounded hΩ Real.smoothTransition
    Real.smoothTransition.contDiff Real.smoothTransition.zero
    ⟨(Mst : ℝ), by simpa only [Real.norm_eq_abs] using hβder⟩
  have hzero := hh.2 hw ψ hψ0 hψ
  let b := bilinFormIntegrandOfCoeff A hw hψ
  have hrepr (x : E) : b x = deriv Real.smoothTransition (h x - k) *
      inner ℝ (hw.weakGrad x) (matMulE (A.a x) (hw.weakGrad x)) := by
    change inner ℝ (matMulE (A.a x) (hw.weakGrad x))
      (deriv Real.smoothTransition (h x - k) • hw.weakGrad x) = _
    rw [real_inner_smul_right, real_inner_comm]
  have hβpos (s : ℝ) : 0 ≤ deriv Real.smoothTransition s :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hbpos : 0 ≤ᵐ[volume.restrict Ω] b := by
    filter_upwards [A.coercive] with x hx
    rw [hrepr]
    exact mul_nonneg (hβpos _) ((mul_nonneg A.hlam.le (sq_nonneg _)).trans (hx _))
  have hbae : b =ᵐ[volume.restrict Ω] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hbpos
      (integrable_bilinFormIntegrandOfCoeff A hw hψ)).mp hzero
  have hψgrad : hψ.weakGrad =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hbae, A.coercive] with x hbx hAx
    have he : deriv Real.smoothTransition (h x - k) *
        (A.lam * ‖hw.weakGrad x‖ ^ 2) ≤ 0 := by
      have hm := mul_le_mul_of_nonneg_left (hAx (hw.weakGrad x)) (hβpos (h x - k))
      rw [← hrepr, hbx] at hm
      exact hm
    have hz : deriv Real.smoothTransition (h x - k) = 0 ∨ hw.weakGrad x = 0 := by
      have hp := hβpos (h x - k)
      have hg := sq_nonneg ‖hw.weakGrad x‖
      have hn : deriv Real.smoothTransition (h x - k) * ‖hw.weakGrad x‖ ^ 2 = 0 := by
        nlinarith [A.hlam]
      rcases mul_eq_zero.mp hn with hβ | hG
      · exact Or.inl hβ
      · exact Or.inr (norm_eq_zero.mp (sq_eq_zero_iff.mp hG))
    change deriv Real.smoothTransition (h x - k) • hw.weakGrad x = 0
    exact hz.elim (fun hβ => by rw [hβ, zero_smul]) (fun hG => by rw [hG, smul_zero])
  have hψLp : gradLpOfWitness hψ = 0 := by
    apply Lp.ext
    filter_upwards [hψ.weakGrad_memLp.coeFn_toLp, hψgrad,
      Lp.coeFn_zero E 2 (volume.restrict Ω)] with x hx hzx h0
    change hψ.weakGrad_memLp.toLp _ x = _
    rw [hx, hzx, h0]
  have hψAE := ae_eq_zero_of_memH01_of_gradLpOfWitness_eq_zero hd hΩ hΩb hψ0 hψ hψLp
  filter_upwards [hψAE] with x hx
  exact sub_nonpos.mp (Real.smoothTransition.zero_iff_nonpos.mp hx)

theorem IsHomogeneousWeakSolution.smul
    {Ω : Set E} (hΩ : IsOpen Ω) {A : EllipticCoeff d Ω} {h : E → ℝ}
    (hh : IsHomogeneousWeakSolution A h) (c : ℝ) :
    IsHomogeneousWeakSolution A (fun x => c * h x) := by
  let hw := MemW1p.someWitness hh.1
  refine ⟨(hw.smul c).memW1p, ?_⟩
  intro hc φ hφ0 hφ
  rw [bilinFormOfCoeff_eq_left hΩ A hc (hw.smul c) hφ,
    bilinFormOfCoeff_smul_left, hh.2 hw φ hφ0 hφ, mul_zero]

theorem IsHomogeneousWeakSolution.ae_abs_le_of_memH01_sub
    {Ω : Set E} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {A : EllipticCoeff d Ω} {u h : E → ℝ} (hh : IsHomogeneousWeakSolution A h)
    (hu : MemW1pWitness 2 u Ω) (hhu : MemW01p 2 (fun x => h x - u x) Ω)
    {k : ℝ} (huk : ∀ᵐ x ∂volume.restrict Ω, |u x| ≤ k) : ∀ᵐ x ∂volume.restrict Ω, |h x| ≤ k := by
  have hup := hh.ae_le_of_memH01_sub hd hΩ hΩb hu hhu
    (huk.mono fun x hx => (le_abs_self _).trans hx)
  have hneg0 : MemW01p 2 (fun x => -1 * h x - -1 * u x) Ω := by
    simpa only [mul_sub] using hhu.smul (-1)
  have hlo := (hh.smul hΩ (-1)).ae_le_of_memH01_sub hd hΩ hΩb (hu.smul (-1)) hneg0
    (huk.mono fun x hx => by have ha := (abs_le.mp hx).1; linarith)
  filter_upwards [hup, hlo] with x hx hy
  exact abs_le.mpr ⟨by linarith, hx⟩

end DeGiorgi

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem IsHomogeneousWeakSolution.subConst
    {Ω : Set V} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {A : EllipticCoeff d Ω} {h : V → ℝ} (hh : IsHomogeneousWeakSolution A h) (c : ℝ) :
    IsHomogeneousWeakSolution A (fun x => h x - c) := by
  let hw := MemW1p.someWitness hh.1
  let hs := hw.subConst hΩ c
  refine ⟨hs.memW1p, ?_⟩
  intro hu φ hφ0 hφ
  rw [bilinFormOfCoeff_eq_left hΩ A hu hs hφ]
  exact hh.2 hw φ hφ0 hφ

theorem IsHomogeneousWeakSolution.ae_abs_sub_le_of_memH01_sub
    {Ω : Set V} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {A : EllipticCoeff d Ω} {u h : V → ℝ} (hh : IsHomogeneousWeakSolution A h)
    (hu : MemW1pWitness 2 u Ω) (hhu : MemW01p 2 (fun x => h x - u x) Ω)
    (c : ℝ) {k : ℝ} (huk : ∀ᵐ x ∂volume.restrict Ω, |u x - c| ≤ k) :
    ∀ᵐ x ∂volume.restrict Ω, |h x - c| ≤ k := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    isFiniteMeasure_restrict.mpr hΩb.measure_lt_top.ne
  have htrace : MemW01p 2 (fun x => (h x - c) - (u x - c)) Ω := by
    simpa only [sub_sub_sub_cancel_right] using hhu
  exact (hh.subConst hΩ c).ae_abs_le_of_memH01_sub hd hΩ hΩb (hu.subConst hΩ c) htrace huk

end DeGiorgi

end
