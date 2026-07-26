import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpQuot
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.MorreyHigherOrder
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Completeness.IteratedSobolevCauchy
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevSpace.IteratedSobolevQuant

/-!
# The local `W^{3,p}` to `C^{2,alpha}` bridge

The tensor quotient completeness theorem supplies a genuine `W^{3,p}` limit.
For the quasilinear coefficient map one also needs a pointwise `C^2`
representative whose second derivatives retain a quantitative Morrey modulus.
This file derives exactly that local statement from the existing scalar
Morrey representative and the recursive weak-partial API.

The constant in `w3p_morrey_c2` depends only on the dimension and exponent;
the function enters only through its `W^{3,p}` norm.  No metric or quotient
instance is installed.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Sobolev.EuclideanMorrey

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

private lemma eucl_norm_le_sum (v : EuclN) :
    ‖v‖ ≤ ∑ i : Fin d, ‖v i‖ := by
  classical
  have hv : v = ∑ i : Fin d, EuclideanSpace.single i (v i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [hv]
  refine (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => by simp

/-- A finite-regularity version of the canonical weak/classical first-partial
identification. -/
private theorem chosen_cont_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {u : EuclN → ℝ} (huC1 : ContDiff ℝ 1 u)
    (huW1 : DeGiorgi.MemW1p p u Ω) (i : Fin d) :
    chosenWeakPartial' p i u Ω =ᵐ[volume.restrict Ω]
      fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1) := by
  have hchosen : DeGiorgi.HasWeakPartialDeriv i
      (chosenWeakPartial' p i u Ω) u Ω :=
    chosenWeakPartial'_isWeakPartial_of_mem huW1 i
  have hclass : DeGiorgi.HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) u Ω :=
    DeGiorgi.HasWeakPartialDeriv.of_contDiff hΩ huC1
  have hchosen_loc : LocallyIntegrable (chosenWeakPartial' p i u Ω)
      (volume.restrict Ω) :=
    (chosenWeakPartial'_memLp_of_mem huW1 i).locallyIntegrable hp
  have hclass_loc : LocallyIntegrable
      (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1))
      (volume.restrict Ω) := by
    have hc : Continuous
        (fun x => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      (huC1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact hc.locallyIntegrable.mono_measure Measure.restrict_le_self
  exact DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ hchosen hclass
    hchosen_loc hclass_loc

private theorem weak2_mem
    {p : ℝ≥0∞} {Ω : Set EuclN} {u : EuclN → ℝ}
    (hu : MemWkp (d := d) 3 p u Ω) (β : Fin 2 → Fin d) :
    MemWkp (d := d) 1 p (iterWeakPartial (d := d) p 2 β u Ω) Ω := by
  rw [iterWeakPartial_succ, iterWeakPartial_succ, iterWeakPartial_zero]
  exact (hu.chosenWeakPartial_mem (β 0)).chosenWeakPartial_mem (β (Fin.succ 0))

private theorem weak2_norm_le
    {p : ℝ≥0∞} {Ω : Set EuclN} (hΩ : IsOpen Ω)
    (u : EuclN → ℝ) (β : Fin 2 → Fin d) :
    wkpNorm (d := d) 1 p (iterWeakPartial (d := d) p 2 β u Ω) Ω ≤
      wkpNorm (d := d) 3 p u Ω := by
  rw [iterWeakPartial_succ, iterWeakPartial_succ, iterWeakPartial_zero]
  exact (wkpNorm_chosenWeakPartial_le (d := d) 1 hΩ
    (chosenWeakPartial' p (β 0) u Ω) (β (Fin.succ 0))).trans
      (wkpNorm_chosenWeakPartial_le (d := d) 2 hΩ u (β 0))

/-- The norm of the chosen weak gradient of a `W^{1,p}` function is bounded,
after `toReal`, by the finite sum of its order-one Sobolev norm. -/
private theorem weakGrad_real_le
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set EuclN}
    {v : EuclN → ℝ} (hv : MemWkp (d := d) 1 p v Ω) :
    let hw := (MemWkp.one_iff_memW1p.mp hv).someWitness
    (eLpNorm (fun x => ‖hw.weakGrad x‖) p (volume.restrict Ω)).toReal ≤
      ∑ _i : Fin d, (wkpNorm (d := d) 1 p v Ω).toReal := by
  classical
  dsimp only
  let hW1 : DeGiorgi.MemW1p p v Ω := MemWkp.one_iff_memW1p.mp hv
  let hw := hW1.someWitness
  let G : ℝ≥0∞ := eLpNorm (fun x => ‖hw.weakGrad x‖) p
    (volume.restrict Ω)
  have hcomp : ∀ i : Fin d,
      (fun x => hw.weakGrad x i) = chosenWeakPartial' p i v Ω := by
    intro i
    funext x
    unfold chosenWeakPartial'
    simp only [dif_pos hW1]
    rfl
  have hmono : G ≤ eLpNorm (fun x => ∑ i : Fin d, ‖hw.weakGrad x i‖) p
      (volume.restrict Ω) := by
    refine eLpNorm_mono ?_
    intro x
    rw [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
    exact eucl_norm_le_sum (d := d) (hw.weakGrad x)
  have hsum : eLpNorm (fun x => ∑ i : Fin d, ‖hw.weakGrad x i‖) p
      (volume.restrict Ω) ≤
      ∑ i : Fin d, eLpNorm (fun x => ‖hw.weakGrad x i‖) p
        (volume.restrict Ω) := by
    have heq : (fun x => ∑ i : Fin d, ‖hw.weakGrad x i‖) =
        ∑ i : Fin d, (fun x => ‖hw.weakGrad x i‖) := by
      ext x
      simp [Finset.sum_apply]
    rw [heq]
    exact eLpNorm_sum_le
      (fun i _ => (hw.weakGrad_component_memLp i).aestronglyMeasurable.norm) hp
  have hterm : ∀ i : Fin d,
      eLpNorm (fun x => ‖hw.weakGrad x i‖) p (volume.restrict Ω) ≤
        wkpNorm (d := d) 1 p v Ω := by
    intro i
    rw [eLpNorm_norm, hcomp i]
    simpa [iterWeakPartial_succ, iterWeakPartial_zero] using
      (eLpNorm_iterWeakPartial_le_wkpNorm (d := d) p v Ω 1 le_rfl
        (fun _ : Fin 1 => i))
  have hG : G ≤ ∑ _i : Fin d, wkpNorm (d := d) 1 p v Ω :=
    hmono.trans (hsum.trans (Finset.sum_le_sum fun i _ => hterm i))
  have hfinite : wkpNorm (d := d) 1 p v Ω ≠ ∞ :=
    (wkpNorm_lt_top_of_memWkp hv).ne
  have hsum_finite : (∑ _i : Fin d, wkpNorm (d := d) 1 p v Ω) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun i _ => hfinite
  have hreal := ENNReal.toReal_mono hsum_finite hG
  rw [ENNReal.toReal_sum (fun i _ => hfinite)] at hreal
  exact hreal

/-- For a `C^2` representative in `W^{3,p}`, the canonical order-two weak
partials are the corresponding classical coordinate partials a.e. -/
private theorem weak2_classical_ae
    {p : ℝ≥0∞} (hp : 1 ≤ p) {Ω : Set EuclN} (hΩ : IsOpen Ω)
    {v : EuclN → ℝ} (hv : MemWkp (d := d) 3 p v Ω)
    (hvC2 : ContDiff ℝ 2 v) (β : Fin 2 → Fin d) :
    iterWeakPartial (d := d) p 2 β v Ω =ᵐ[volume.restrict Ω]
      iterClassicalPartial (d := d) 2 β v := by
  let i₀ : Fin d := β 0
  let i₁ : Fin d := β (Fin.succ 0)
  let v₁ : EuclN → ℝ := chosenWeakPartial' p i₀ v Ω
  let c₁ : EuclN → ℝ :=
    fun x => (fderiv ℝ v x) (EuclideanSpace.single i₀ 1)
  have hvW2 : MemWkp (d := d) 2 p v Ω :=
    MemWkp.le_of_le (by omega) hv
  have hvW1 : DeGiorgi.MemW1p p v Ω := hvW2.memW1p
  have hfirst : v₁ =ᵐ[volume.restrict Ω] c₁ :=
    chosen_cont_ae (d := d) hp hΩ (hvC2.of_le (by norm_num)) hvW1 i₀
  have hv₁W : MemWkp (d := d) 1 p v₁ Ω :=
    hvW2.chosenWeakPartial_mem i₀
  have hc₁W : MemWkp (d := d) 1 p c₁ Ω :=
    (MemWkp_congr_ae (d := d) hp hΩ hfirst).mp hv₁W
  have hcongr : chosenWeakPartial' p i₁ v₁ Ω =ᵐ[volume.restrict Ω]
      chosenWeakPartial' p i₁ c₁ Ω :=
    chosenWeakPartial'_ae_congr (d := d) hp hΩ hfirst i₁
  have hc₁C1 : ContDiff ℝ 1 c₁ := by
    exact (hvC2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hsecond : chosenWeakPartial' p i₁ c₁ Ω =ᵐ[volume.restrict Ω]
      fun x => (fderiv ℝ c₁ x) (EuclideanSpace.single i₁ 1) :=
    chosen_cont_ae (d := d) hp hΩ hc₁C1
      (MemWkp.one_iff_memW1p.mp hc₁W) i₁
  simpa [iterWeakPartial_succ, iterWeakPartial_zero,
    iterClassicalPartial_succ, iterClassicalPartial_zero, i₀, i₁, v₁, c₁]
    using hcongr.trans hsecond

/-- Local quantitative Morrey embedding at the order used by the
Ricci--DeTurck contraction.  A `W^{3,p}` scalar component, `p > d`, has a
`C^2` representative on the quarter ball, and every coordinate component of
its second derivative is `alpha = 1 - d/p` Hölder on the next quarter ball.
The Hölder constant is a fixed dimension/exponent constant times the original
`W^{3,p}` norm. -/
theorem w3p_morrey_c2
    {p : ℝ} (hp_dim : (d : ℝ) < p)
    {x₀ : EuclN} {R : ℝ} (hR : 0 < R) {u : EuclN → ℝ}
    (hu : MemWkp (d := d) 3 (ENNReal.ofReal p) u (Metric.ball x₀ R)) :
    ∃ v : EuclN → ℝ,
      ContDiff ℝ 2 v ∧
      u =ᵐ[volume.restrict (Metric.ball x₀ (R / 4))] v ∧
      ∀ β : Fin 2 → Fin d, ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Metric.ball x₀ ((R / 4) / 4),
          ∀ y ∈ Metric.ball x₀ ((R / 4) / 4),
          ‖iterClassicalPartial (d := d) 2 β v x -
              iterClassicalPartial (d := d) 2 β v y‖ ≤
            C * (dist x y) ^ (1 - (d : ℝ) / p) *
              (wkpNorm (d := d) 3 (ENNReal.ofReal p) u
                (Metric.ball x₀ R)).toReal := by
  classical
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (NeZero.pos d)
  have hp_pos : 0 < p := lt_trans hd_pos hp_dim
  have hp_one_real : (1 : ℝ) ≤ p := by
    have hd_one : (1 : ℝ) ≤ d := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    linarith
  have hp_one : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hp_one_real
  obtain ⟨v, hvC2, huv⟩ :=
    morrey_iteratedFDeriv_representative (d := d) hp_dim hR 2 hu
  refine ⟨v, hvC2, huv, ?_⟩
  let Ω : Set EuclN := Metric.ball x₀ R
  let Ω₄ : Set EuclN := Metric.ball x₀ (R / 4)
  let Ω₁₆ : Set EuclN := Metric.ball x₀ ((R / 4) / 4)
  have hR₄ : 0 < R / 4 := by positivity
  have hΩ₄Ω : Ω₄ ⊆ Ω := by
    intro z hz
    change dist z x₀ < R / 4 at hz
    change dist z x₀ < R
    linarith
  have hΩ₁₆Ω₄ : Ω₁₆ ⊆ Ω₄ := by
    intro z hz
    change dist z x₀ < (R / 4) / 4 at hz
    change dist z x₀ < R / 4
    linarith
  have hu₄ : MemWkp (d := d) 3 (ENNReal.ofReal p) u Ω₄ :=
    hu.mono_set hp_one Metric.isOpen_ball Metric.isOpen_ball hΩ₄Ω
  have hv₄ : MemWkp (d := d) 3 (ENNReal.ofReal p) v Ω₄ :=
    (MemWkp_congr_ae (d := d) hp_one Metric.isOpen_ball huv).mp hu₄
  intro β
  let w₂ : EuclN → ℝ :=
    iterWeakPartial (d := d) (ENNReal.ofReal p) 2 β u Ω₄
  have hw₂W : MemWkp (d := d) 1 (ENNReal.ofReal p) w₂ Ω₄ :=
    weak2_mem (d := d) hu₄ β
  let hw₂ : DeGiorgi.MemW1pWitness (ENNReal.ofReal p) w₂ Ω₄ :=
    (MemWkp.one_iff_memW1p.mp hw₂W).someWitness
  obtain ⟨w, C₀, hw_cont, hC₀, hw_ae, hw_holder⟩ :=
    morrey_holder_representative (d := d) hp_dim hR₄ hw₂
  have hweak_congr : w₂ =ᵐ[volume.restrict Ω₄]
      iterWeakPartial (d := d) (ENNReal.ofReal p) 2 β v Ω₄ :=
    iterWeakPartial_ae_congr (d := d) hp_one Metric.isOpen_ball 2 β huv
  have hweak_class :
      iterWeakPartial (d := d) (ENNReal.ofReal p) 2 β v Ω₄ =ᵐ[
        volume.restrict Ω₄] iterClassicalPartial (d := d) 2 β v :=
    weak2_classical_ae (d := d) hp_one Metric.isOpen_ball hv₄ hvC2 β
  have hae₁₆ : w =ᵐ[volume.restrict Ω₁₆]
      iterClassicalPartial (d := d) 2 β v := by
    have htail := ae_restrict_of_ae_restrict_of_subset
      (μ := volume) hΩ₁₆Ω₄ (hweak_congr.trans hweak_class)
    exact hw_ae.trans htail
  have hclass_cont : Continuous (iterClassicalPartial (d := d) 2 β v) := by
    rw [iterClassicalPartial_succ, iterClassicalPartial_succ,
      iterClassicalPartial_zero]
    have hfirst : ContDiff ℝ 1
        (fun x => (fderiv ℝ v x) (EuclideanSpace.single (β 0) 1)) :=
      (hvC2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    exact (hfirst.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have heqOn : Set.EqOn w (iterClassicalPartial (d := d) 2 β v) Ω₁₆ :=
    MeasureTheory.Measure.eqOn_of_ae_eq hae₁₆ hw_cont.continuousOn
      hclass_cont.continuousOn (by
        rw [Metric.isOpen_ball.interior_eq]
        exact subset_closure)
  have hG :
      (eLpNorm (fun x => ‖hw₂.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict Ω₄)).toReal ≤
        ∑ _i : Fin d, (wkpNorm (d := d) 1 (ENNReal.ofReal p) w₂ Ω₄).toReal :=
    weakGrad_real_le (d := d) hp_one hw₂W
  have hweak_norm : wkpNorm (d := d) 1 (ENNReal.ofReal p) w₂ Ω₄ ≤
      wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω := by
    exact (weak2_norm_le (d := d) Metric.isOpen_ball u β).trans
      (wkpNorm_mono_set (d := d) hp_one Metric.isOpen_ball Metric.isOpen_ball
        hΩ₄Ω hu)
  have htotal_finite : wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω ≠ ∞ :=
    (wkpNorm_lt_top_of_memWkp hu).ne
  have hweak_real :
      (wkpNorm (d := d) 1 (ENNReal.ofReal p) w₂ Ω₄).toReal ≤
        (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal :=
    ENNReal.toReal_mono htotal_finite hweak_norm
  let D : ℝ := ∑ _i : Fin d, (1 : ℝ)
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => zero_le_one
  have hG_total :
      (eLpNorm (fun x => ‖hw₂.weakGrad x‖) (ENNReal.ofReal p)
        (volume.restrict Ω₄)).toReal ≤
        D * (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal := by
    refine hG.trans ?_
    calc
      ∑ _i : Fin d, (wkpNorm (d := d) 1 (ENNReal.ofReal p) w₂ Ω₄).toReal ≤
      ∑ _i : Fin d, (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal :=
        Finset.sum_le_sum fun i _ => hweak_real
      _ = D * (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal := by
        dsimp [D]
        rw [Finset.sum_mul]
        simp only [one_mul]
  refine ⟨C₀ * D, mul_nonneg hC₀ hD, ?_⟩
  intro x hx y hy
  have hholder := hw_holder x hx y hy
  calc
    ‖iterClassicalPartial (d := d) 2 β v x -
        iterClassicalPartial (d := d) 2 β v y‖ = ‖w x - w y‖ := by
      rw [← heqOn hx, ← heqOn hy]
    _ ≤ C₀ * (dist x y) ^ (1 - (d : ℝ) / p) *
        (eLpNorm (fun z => ‖hw₂.weakGrad z‖) (ENNReal.ofReal p)
          (volume.restrict Ω₄)).toReal := hholder
    _ ≤ C₀ * (dist x y) ^ (1 - (d : ℝ) / p) *
        (D * (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal) := by
      exact mul_le_mul_of_nonneg_left hG_total
        (mul_nonneg hC₀ (Real.rpow_nonneg _ _))
    _ = (C₀ * D) * (dist x y) ^ (1 - (d : ℝ) / p) *
        (wkpNorm (d := d) 3 (ENNReal.ofReal p) u Ω).toReal := by ring

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
