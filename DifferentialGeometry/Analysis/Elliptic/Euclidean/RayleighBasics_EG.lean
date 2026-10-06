import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.Existence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.ZeroBoundaryGraph
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Rellich.Vector

/-!
# Rayleigh-quotient kernel for `-Δ + W` on `H¹₀(Ω)` (S-W-EIG, G1 basics)

Chosen weak-gradient witnesses on `H¹₀`, `L²` bookkeeping, `L²`-continuity of weighted
quadratic forms with a bounded weight, and the Rellich/weak-gradient compactness extraction
for bounded sequences in `H¹₀(Ω)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

local notation "E" => EuclideanSpace ℝ (Fin d)


theorem integral_sq_eq_norm_sq_EG {v : E → ℝ} (hv : MemLp v 2 (volume.restrict Ω)) :
    (∫ x in Ω, v x ^ 2) = ‖hv.toLp v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem integral_mul_le_norm_mul_norm_EG {f g : E → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) :
    |∫ x in Ω, f x * g x| ≤ ‖hf.toLp f‖ * ‖hg.toLp g‖ := by
  have h := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [L2.inner_def] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [mul_comm]

theorem memLp_weight_mul_EG {c : E → ℝ} (hcm : Measurable c) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict Ω), |c x| ≤ B) {a : E → ℝ}
    (ha : MemLp a 2 (volume.restrict Ω)) : MemLp (fun x => c x * a x) 2 (volume.restrict Ω) := by
  refine MemLp.of_le_mul (g := a) (c := B) ha
    (hcm.aestronglyMeasurable.mul ha.aestronglyMeasurable) ?_
  filter_upwards [hB] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

theorem integrable_weight_sq_EG {c : E → ℝ} (hcm : Measurable c) {B : ℝ}
    (hB : ∀ᵐ x ∂(volume.restrict Ω), |c x| ≤ B) {a : E → ℝ}
    (ha : MemLp a 2 (volume.restrict Ω)) :
    Integrable (fun x => c x * a x ^ 2) (volume.restrict Ω) := by
  have := (memLp_weight_mul_EG hcm hB ha).integrable_mul ha
  refine this.congr ?_
  filter_upwards with x
  simp [sq, mul_assoc]

theorem abs_integral_weight_sq_sub_le_EG {c : E → ℝ} (hcm : Measurable c) {B : ℝ}
    (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂(volume.restrict Ω), |c x| ≤ B) {a b : E → ℝ}
    (ha : MemLp a 2 (volume.restrict Ω)) (hb : MemLp b 2 (volume.restrict Ω)) :
    |(∫ x in Ω, c x * a x ^ 2) - ∫ x in Ω, c x * b x ^ 2| ≤
      B * ((eLpNorm (fun x => a x - b x) 2 (volume.restrict Ω)).toReal *
        ((eLpNorm a 2 (volume.restrict Ω)).toReal +
          (eLpNorm b 2 (volume.restrict Ω)).toReal)) := by
  have hab : MemLp (fun x => a x - b x) 2 (volume.restrict Ω) := ha.sub hb
  have hsum : MemLp (fun x => a x + b x) 2 (volume.restrict Ω) := ha.add hb
  have hF : MemLp (fun x => c x * (a x - b x)) 2 (volume.restrict Ω) :=
    memLp_weight_mul_EG hcm hB hab
  have hid : (∫ x in Ω, c x * a x ^ 2) - ∫ x in Ω, c x * b x ^ 2 =
      ∫ x in Ω, (c x * (a x - b x)) * (a x + b x) := by
    rw [← integral_sub (integrable_weight_sq_EG hcm hB ha) (integrable_weight_sq_EG hcm hB hb)]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hid]
  refine (integral_mul_le_norm_mul_norm_EG hF hsum).trans ?_
  have h1 : ‖hF.toLp _‖ ≤ B * ‖hab.toLp _‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hF.coeFn_toLp, hab.coeFn_toLp, hB] with x hx hy hz
    rw [hx, hy, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have h2 : ‖hsum.toLp _‖ ≤ ‖ha.toLp a‖ + ‖hb.toLp b‖ := by
    have := norm_add_le (ha.toLp a) (hb.toLp b)
    rwa [← MemLp.toLp_add] at this
  simp only [Lp.norm_toLp] at h1 h2 ⊢
  have hn1 : 0 ≤ (eLpNorm (fun x => a x + b x) 2 (volume.restrict Ω)).toReal :=
    ENNReal.toReal_nonneg
  calc _ ≤ (B * (eLpNorm (fun x => a x - b x) 2 (volume.restrict Ω)).toReal) *
        ((eLpNorm a 2 (volume.restrict Ω)).toReal + (eLpNorm b 2 (volume.restrict Ω)).toReal) :=
        mul_le_mul h1 h2 hn1 (mul_nonneg hB0 ENNReal.toReal_nonneg)
    _ = _ := by ring


variable [NeZero d]

/-- The chosen weak-gradient witness of an `H¹₀(Ω)` function. -/
def h01Wit_EG {v : E → ℝ} (hv : DeGiorgi.MemW01p 2 v Ω) : DeGiorgi.MemW1pWitness 2 v Ω :=
  Classical.choose hv.2

omit [NeZero d] in
theorem gradient_coordinate_sum_le_EG {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω) :
    (∑ j : Fin d, eLpNorm (fun x => hu.weakGrad x j) 2 (volume.restrict Ω)) ≤
      ENNReal.ofReal ((d : ℝ) * ‖DeGiorgi.gradLpOfWitness hu‖) := by
  have hnorm : eLpNorm hu.weakGrad 2 (volume.restrict Ω) =
      ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ := by
    rw [DeGiorgi.gradLpOfWitness, Lp.norm_toLp,
      ENNReal.ofReal_toReal hu.weakGrad_memLp.eLpNorm_lt_top.ne]
  have hcoord (j : Fin d) : eLpNorm (fun x => hu.weakGrad x j) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ := by
    rw [← hnorm]
    exact eLpNorm_mono_ae (hu.weakGrad_component_memLp j).aestronglyMeasurable
      (Eventually.of_forall fun x => PiLp.norm_apply_le _ j)
  calc
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal ‖DeGiorgi.gradLpOfWitness hu‖ :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = ENNReal.ofReal (∑ _j : Fin d, ‖DeGiorgi.gradLpOfWitness hu‖) :=
      (ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _).symm
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [NeZero d] in
theorem gradLp_eq_of_weak_EG (hΩ : IsOpen Ω) {v : E → ℝ} (hw : DeGiorgi.MemW1pWitness 2 v Ω)
    (G : Lp E 2 (volume.restrict Ω))
    (hG : ∀ i : Fin d, DeGiorgi.HasWeakPartialDeriv i (fun x => G x i) v Ω) :
    DeGiorgi.gradLpOfWitness hw = G := by
  have hcoord (i : Fin d) : (fun x => hw.weakGrad x i) =ᵐ[volume.restrict Ω]
      (fun x => G x i) :=
    DeGiorgi.HasWeakPartialDeriv.ae_eq hΩ (hw.isWeakGrad i) (hG i)
      ((hw.weakGrad_component_memLp i).locallyIntegrable (by norm_num))
      (((Lp.memLp G).eval_piLp i).locallyIntegrable (by norm_num))
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, hw.weakGrad_memLp.coeFn_toLp] with x hx h₁x
  change hw.weakGrad_memLp.toLp hw.weakGrad x = G x
  rw [h₁x]
  exact PiLp.ext hx

theorem exists_limit_EG (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {f : ℕ → E → ℝ} (hf : ∀ n, DeGiorgi.MemW01p 2 (f n) Ω) {R C : ℝ}
    (hR : ∀ n, eLpNorm (f n) 2 (volume.restrict Ω) ≤ ENNReal.ofReal R)
    (hC : ∀ n, ‖DeGiorgi.gradLpOfWitness (h01Wit_EG (hf n))‖ ≤ C) :
    ∃ (φ : ℕ → ℕ) (w : E → ℝ) (hw : DeGiorgi.MemW01p 2 w Ω), StrictMono φ ∧
      Tendsto (fun n => eLpNorm (fun x => f (φ n) x - w x) 2 (volume.restrict Ω)) atTop
        (𝓝 0) ∧
      ∀ z, Tendsto (fun n => ⟪DeGiorgi.gradLpOfWitness (h01Wit_EG (hf (φ n))), z⟫_ℝ) atTop
        (𝓝 ⟪DeGiorgi.gradLpOfWitness (h01Wit_EG hw), z⟫_ℝ) := by
  let R' : ℝ := max R ((d : ℝ) * C)
  obtain ⟨φ, v, hφ, hv, hlim⟩ :=
    DifferentialGeometry.Analysis.Sobolev.rellich_kondrachov_W01p_seq_coordinates
    (ι := Unit) hΩ hΩb (p := 2) (by norm_num) (by norm_num) (fun _ n => f n)
    (fun _ n => hf n) (fun _ => R')
    (fun _ n => (hR n).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
    (fun _ n => (gradient_coordinate_sum_le_EG (h01Wit_EG (hf n))).trans
      (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (hC n) (Nat.cast_nonneg d)).trans
        (le_max_right _ _))))
  obtain ⟨hw, σ, G, hσ, hGC, hweak, hG⟩ :=
    exists_weakly_convergent_gradients_of_tendsto_L2 hΩ
    (f := fun n => f (φ n)) (v := v ()) (fun n => hf (φ n)) (hv ()) (C := C)
    (fun n => hC (φ n)) (hlim ())
  refine ⟨φ ∘ σ, v (), hw, hφ.comp hσ, (hlim ()).comp hσ.tendsto_atTop, ?_⟩
  rw [gradLp_eq_of_weak_EG hΩ (h01Wit_EG hw) G hG]
  exact hweak


theorem dir_congr_EG (hΩ : IsOpen Ω) {v : E → ℝ} (h₁ h₂ : DeGiorgi.MemW1pWitness 2 v Ω) :
    (∫ x in Ω, ‖h₁.weakGrad x‖ ^ 2) = ∫ x in Ω, ‖h₂.weakGrad x‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [DeGiorgi.MemW1pWitness.ae_eq hΩ h₁ h₂] with x hx
  rw [hx]

omit [NeZero d] in
theorem dir_smul_EG {v : E → ℝ} (hv : DeGiorgi.MemW1pWitness 2 v Ω) (c : ℝ) :
    (∫ x in Ω, ‖(hv.smul c).weakGrad x‖ ^ 2) =
      c ^ 2 * ∫ x in Ω, ‖hv.weakGrad x‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  change ‖c • hv.weakGrad x‖ ^ 2 = _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

theorem norm_sq_le_of_weak_EG {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {V : ℕ → H} {G : H} (hw : ∀ z, Tendsto (fun n => ⟪V n, z⟫_ℝ) atTop (𝓝 ⟪G, z⟫_ℝ))
    {a : ℝ}
    (ha : Tendsto (fun n => ‖V n‖ ^ 2) atTop (𝓝 a)) : ‖G‖ ^ 2 ≤ a := by
  have h1 : Tendsto (fun n => 2 * ⟪V n, G⟫_ℝ - ‖G‖ ^ 2) atTop
      (𝓝 (2 * ⟪G, G⟫_ℝ - ‖G‖ ^ 2)) :=
    ((hw G).const_mul 2).sub_const _
  rw [real_inner_self_eq_norm_sq, show 2 * ‖G‖ ^ 2 - ‖G‖ ^ 2 = ‖G‖ ^ 2 by ring] at h1
  refine le_of_tendsto_of_tendsto h1 ha (Eventually.of_forall fun n => ?_)
  have := sq_nonneg ‖V n - G‖
  have h2 : ‖V n - G‖ ^ 2 = ‖V n‖ ^ 2 - 2 * ⟪V n, G⟫_ℝ + ‖G‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  nlinarith [norm_nonneg (V n - G)]

end DifferentialGeometry.Analysis.Sobolev.Euclidean
