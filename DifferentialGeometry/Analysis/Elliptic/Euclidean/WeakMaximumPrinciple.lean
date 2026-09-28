import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroTrace.Composition
import DifferentialGeometry.External.DeGiorgi.PositivePart
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph

section

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

end

section

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

private theorem memW01p_pos_part
    {Ω : Set V} (hΩ : IsOpen Ω) [IsFiniteMeasure (volume.restrict Ω)]
    {u : V → ℝ} (hu : MemW01p 2 u Ω) : MemW01p 2 (fun x => max (u x) 0) Ω := by
  obtain ⟨_, hw, φ, hφs, hφc, hφΩ, hφf, hφg⟩ := hu
  let htw (n : ℕ) := smoothTestWitness hΩ (⟨hφs n, hφc n, hφΩ n⟩ : IsSmoothTestOn Ω (φ n))
  let hpw (n : ℕ) := (htw n).posPart hΩ ⟨fun _ => φ n,
    fun _ => (hφs n).of_le (by norm_cast), fun _ => hφc n,
    by simp, fun i => by simp [htw, smoothTestWitness, smoothGradField]⟩
  have hpc (n : ℕ) : HasCompactSupport (fun x => max (φ n x) 0) := by
    apply (hφc n).mono
    intro x hx
    by_contra hz
    apply hx
    simp only [Function.notMem_support.mp hz, max_self]
  have hpsub (n : ℕ) : tsupport (fun x => max (φ n x) 0) ⊆ Ω := by
    apply (closure_mono (show Function.support (fun x => max (φ n x) 0) ⊆
      Function.support (φ n) from ?_)).trans (hφΩ n)
    intro x hx hz
    apply hx
    simp only [hz, max_self]
  have hp0 (n : ℕ) : MemW01p 2 (fun x => max (φ n x) 0) Ω := by
    have hm : MemW1p (ENNReal.ofReal 2) (fun x => max (φ n x) 0) Ω := by
      simpa only [ENNReal.ofReal_ofNat] using (hpw n).memW1p
    simpa only [ENNReal.ofReal_ofNat] using memW01p_of_memW1p_of_tsupport_subset hΩ
      (by norm_num : (1 : ℝ) < 2) hm (hpc n) (hpsub n)
  have hgv : Tendsto (fun n => eLpNorm (fun x => (htw n).weakGrad x - hw.weakGrad x)
      2 (volume.restrict Ω)) atTop (𝓝 0) :=
    tendsto_eLpNorm_vector_of_componentwise
      (fun n i => ((htw n).weakGrad_component_memLp i).sub (hw.weakGrad_component_memLp i)) hφg
  have hgLp : Tendsto (fun n => gradLpOfWitness (htw n)) atTop (𝓝 (gradLpOfWitness hw)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (f_ℒp := fun n => (htw n).weakGrad_memLp) (f_lim_ℒp := hw.weakGrad_memLp)).mpr hgv
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hgLp).exists_norm_le
  have hbound (n : ℕ) : ‖gradLpOfWitness (Classical.choose (hp0 n).2)‖ ≤ C := by
    have heq : gradLpOfWitness (Classical.choose (hp0 n).2) = gradLpOfWitness (hpw n) := by
      apply MemLp.toLp_congr
      exact MemW1pWitness.ae_eq hΩ _ _
    rw [heq]
    apply le_trans _ (hC _ (mem_range_self n))
    rw [gradLpOfWitness, gradLpOfWitness, Lp.norm_toLp, Lp.norm_toLp]
    apply ENNReal.toReal_mono (htw n).weakGrad_memLp.eLpNorm_ne_top
    apply eLpNorm_mono_ae (hpw n).weakGrad_memLp.aestronglyMeasurable
    filter_upwards with x
    change ‖if 0 < φ n x then (htw n).weakGrad x else 0‖ ≤ ‖(htw n).weakGrad x‖
    split_ifs <;> simp
  have hpLp : MemLp (fun x => max (u x) 0) 2 (volume.restrict Ω) := by
    exact hw.memLp.pos_part
  have hlim : Tendsto (fun n => eLpNorm (fun x => max (φ n x) 0 - max (u x) 0)
      2 (volume.restrict Ω)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hφf (fun _ => zero_le)
    intro n
    apply eLpNorm_mono_ae ((hpw n).memLp.sub hpLp).aestronglyMeasurable
    filter_upwards with x
    simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.dist_eq, NNReal.coe_one, one_mul] using
      (MeasureTheory.Lp.lipschitzWith_pos_part.dist_le_mul (φ n x) (u x))
  exact (exists_weakly_convergent_gradients_of_tendsto_L2 hΩ hp0 hpLp hbound hlim).1


theorem IsSubsolution.ae_le_zero_of_memH01
    {Ω : Set V} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {A : EllipticCoeff d Ω} {u : V → ℝ} (hu : IsSubsolution A u)
    (hu0 : MemH01 u Ω) : ∀ᵐ x ∂volume.restrict Ω, u x ≤ 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  have hp0 : MemH01 (fun x => max (u x) 0) Ω := memW01p_pos_part hΩ hu0
  obtain ⟨_, hw, φ, hφs, hφc, _, hφf, hφg⟩ := hu0
  let hpw := hw.posPart hΩ ⟨φ, fun n => (hφs n).of_le (by norm_cast), hφc, hφf, hφg⟩
  have htest := hu.2 hw (fun x => max (u x) 0) hp0 hpw (fun x => le_max_right _ _)
  have he : bilinFormOfCoeff A hw hpw = bilinFormOfCoeff A hpw hpw := by
    apply integral_congr_ae
    filter_upwards with x
    change inner ℝ (matMulE (A.a x) (hw.weakGrad x))
        (if 0 < u x then hw.weakGrad x else 0) =
      inner ℝ (matMulE (A.a x) (if 0 < u x then hw.weakGrad x else 0))
        (if 0 < u x then hw.weakGrad x else 0)
    split_ifs <;> simp
  rw [he] at htest
  have hc := (bilinForm_coercive A hpw).trans htest
  have hi : Integrable (fun x => ‖hpw.weakGrad x‖ ^ (2 : ℕ)) (volume.restrict Ω) :=
    hpw.weakGrad_memLp.integrable_norm_pow (by norm_num)
  have hInt : (∫ x in Ω, ‖hpw.weakGrad x‖ ^ (2 : ℕ)) = 0 := by
    have hn : 0 ≤ (∫ x in Ω, ‖hpw.weakGrad x‖ ^ (2 : ℕ)) := integral_nonneg (fun _ => sq_nonneg _)
    nlinarith [A.hlam]
  have hG : hpw.weakGrad =ᵐ[volume.restrict Ω] 0 := by
    have hh := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun x => sq_nonneg ‖hpw.weakGrad x‖) hi).mp hInt
    filter_upwards [hh] with x hx
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hx)
  have hLp : gradLpOfWitness hpw = 0 := by
    apply Lp.ext
    filter_upwards [hpw.weakGrad_memLp.coeFn_toLp, hG,
      Lp.coeFn_zero V 2 (volume.restrict Ω)] with x hx hg hz
    exact hx.trans (hg.trans hz.symm)
  have hzero := ae_eq_zero_of_memH01_of_gradLpOfWitness_eq_zero hd hΩ hΩb hp0 hpw hLp
  filter_upwards [hzero] with x hx
  exact (le_max_left (u x) 0).trans (le_of_eq hx)


theorem IsSubsolution.ae_le_of_memH01_sub
    {Ω : Set V} (hd : 2 ≤ d) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {A : EllipticCoeff d Ω} {u v : V → ℝ} (hu : IsSubsolution A u)
    (hv : IsSupersolution A v) (huv : MemH01 (fun x => u x - v x) Ω) :
    ∀ᵐ x ∂volume.restrict Ω, u x ≤ v x := by
  let hwu := hu.1.someWitness
  let hwv := hv.1.someWitness
  let hw := hwu.add (hwv.smul (-1))
  have hsub : IsSubsolution A (fun x => u x - v x) := by
    refine ⟨huv.memW1p, ?_⟩
    intro hw' φ hφ0 hφ hφpos
    have hu' := hu.2 hwu φ hφ0 hφ hφpos
    have hv' := hv.2 hwv φ hφ0 hφ hφpos
    let hw'' : MemW1pWitness 2 (fun x => u x - v x) Ω :=
      { memLp := by simpa only [sub_eq_add_neg, neg_one_mul] using hw.memLp
        weakGrad := hw.weakGrad
        weakGrad_component_memLp := hw.weakGrad_component_memLp
        isWeakGrad := by simpa only [sub_eq_add_neg, neg_one_mul] using hw.isWeakGrad }
    rw [bilinFormOfCoeff_eq_left hΩ A hw' hw'' hφ]
    have hsplit : bilinFormOfCoeff A hw'' hφ =
        bilinFormOfCoeff A hwu hφ + -1 * bilinFormOfCoeff A hwv hφ := by
      change bilinFormOfCoeff A hw hφ = _
      rw [bilinFormOfCoeff_add_left, bilinFormOfCoeff_smul_left]
    rw [hsplit]
    linarith
  filter_upwards [hsub.ae_le_zero_of_memH01 hd hΩ hΩb huv] with x hx
  exact sub_nonpos.mp hx

end DeGiorgi

end

end
