import DifferentialGeometry.Analysis.Elliptic.Euclidean.RayleighMinimizer_EG
import DifferentialGeometry.Analysis.Elliptic.Euclidean.WeakMaximumPrinciple

/-!
# `|u| ∈ H¹₀(Ω)` with the same Dirichlet energy (S-W-EIG, G2)

Positive part of an `H¹₀` function stays in `H¹₀` with gradient `1_{u>0}∇u`; hence `|u|` is in `H¹₀`
and `‖∇|u|‖ = ‖∇u‖` a.e.  (The private `memW01p_pos_part` of `WeakMaximumPrinciple` is re-proved
here, with the witness formula exposed.)
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Topology

namespace DeGiorgi
open DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]
local notation "V" => EuclideanSpace ℝ (Fin d)

theorem posPart_h01_EG {Ω : Set V} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {u : V → ℝ}
    (hu0 : MemW01p 2 u Ω) :
    MemW01p 2 (fun x => max (u x) 0) Ω ∧
      ∃ hp : MemW1pWitness 2 (fun x => max (u x) 0) Ω,
        ∀ x, hp.weakGrad x = if 0 < u x then (h01Wit_EG hu0).weakGrad x else 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  obtain ⟨φ, hφs, hφc, hφΩ, hφf, hφg⟩ := Classical.choose_spec hu0.2
  let hw : MemW1pWitness 2 u Ω := h01Wit_EG hu0
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
  refine ⟨(exists_weakly_convergent_gradients_of_tendsto_L2 hΩ hp0 hpLp hbound hlim).1,
    hw.posPart hΩ ⟨φ, fun n => (hφs n).of_le (by norm_cast), hφc, hφf, hφg⟩, ?_⟩
  intro x
  rfl

theorem exists_abs_h01_EG {Ω : Set V} (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {u : V → ℝ}
    (hu0 : MemW01p 2 u Ω) (hu : MemW1pWitness 2 u Ω) :
    MemW01p 2 (fun x => |u x|) Ω ∧ ∃ ha : MemW1pWitness 2 (fun x => |u x|) Ω,
      (∫ x in Ω, ‖ha.weakGrad x‖ ^ 2) = ∫ x in Ω, ‖hu.weakGrad x‖ ^ 2 := by
  obtain ⟨hp0₁, hp₁, hg₁⟩ := posPart_h01_EG hΩ hΩb hu0
  have hu0' : MemW01p 2 (fun x => (-1 : ℝ) * u x) Ω := hu0.smul (-1)
  obtain ⟨hp0₂, hp₂, hg₂⟩ := posPart_h01_EG hΩ hΩb hu0'
  have e : (fun x => |u x|) = fun x => max (u x) 0 + max ((-1 : ℝ) * u x) 0 := by
    ext x
    rcases le_total 0 (u x) with h | h
    · simp [abs_of_nonneg h, h]
    · simp [abs_of_nonpos h, h]
  rw [e]
  refine ⟨hp0₁.add hp0₂, hp₁.add hp₂, ?_⟩
  rw [dir_congr_EG hΩ hu (h01Wit_EG hu0)]
  apply integral_congr_ae
  have hneg := MemW1pWitness.ae_eq hΩ (h01Wit_EG hu0') ((h01Wit_EG hu0).smul (-1))
  have hz := (h01Wit_EG hu0).weakGrad_ae_eq_zero_on_zeroSet hΩ
  filter_upwards [hneg, ae_all_iff.mpr hz] with x hx hz'
  change ‖hp₁.weakGrad x + hp₂.weakGrad x‖ ^ 2 = ‖(h01Wit_EG hu0).weakGrad x‖ ^ 2
  rw [hg₁ x, hg₂ x]
  rcases lt_trichotomy (u x) 0 with h | h | h
  · have h1 : ¬ 0 < u x := not_lt.mpr h.le
    have h2 : 0 < (-1 : ℝ) * u x := by linarith
    simp only [h1, h2, ↓reduceIte, zero_add]
    rw [hx]
    change ‖(-1 : ℝ) • (h01Wit_EG hu0).weakGrad x‖ ^ 2 = _
    rw [norm_smul]
    simp
  · have h1 : ¬ 0 < u x := by rw [h]; exact lt_irrefl _
    have h2 : ¬ 0 < (-1 : ℝ) * u x := by rw [h]; simp
    have hg0 : (h01Wit_EG hu0).weakGrad x = 0 := by
      ext i
      simpa using hz' i h
    simp only [h1, h2, ↓reduceIte, hg0]
    simp
  · have h2 : ¬ 0 < (-1 : ℝ) * u x := by linarith
    simp only [h, h2, ↓reduceIte, add_zero]

end DeGiorgi
