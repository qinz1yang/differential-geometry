import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

open Set Module MeasureTheory
open scoped ENNReal Function

namespace Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem card_le_of_separated_closedBall (s : Finset E) (o : E) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hs : ∀ c ∈ s, dist c o ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ dist c d) :
    (s.card : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := ε / 2
  let ρ : ℝ := R + δ
  have hδ : 0 < δ := half_pos hε
  have hρ : 0 < ρ := add_pos_of_nonneg_of_pos hR hδ
  set A := ⋃ c ∈ s, ball (c : E) δ with hA
  have hd : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) δ) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    calc
      δ + δ = ε := by dsimp [δ]; ring
      _ ≤ dist c d := hsep c hc d hd hcd
  have hAsubset : A ⊆ ball o ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    calc
      δ + dist c o ≤ δ + R := add_le_add le_rfl (hs c hc)
      _ = ρ := by dsimp [ρ]; ring
  have hvolume :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [hA, measure_biUnion_finset hd fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball o ρ) := measure_mono hAsubset
      _ = ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) :=
        μ.addHaar_ball_of_pos o hρ
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
        ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvolume
  have hreal : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using h
  have hratio : ρ / δ = 1 + 2 * R / ε := by
    dsimp [ρ, δ]
    field_simp [hε.ne']
    ring
  calc
    (s.card : ℝ) ≤ ρ ^ finrank ℝ E / δ ^ finrank ℝ E :=
      (le_div_iff₀ (pow_pos hδ _)).mpr hreal
    _ = (ρ / δ) ^ finrank ℝ E := (div_pow ρ δ _).symm
    _ = (1 + 2 * R / ε) ^ finrank ℝ E := by rw [hratio]

theorem card_le_of_separated_family_closedBall {ι : Type*} [Fintype ι]
    (f : ι → E) (o : E) {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hf : ∀ i, dist (f i) o ≤ R)
    (hsep : ∀ i j, i ≠ j → ε ≤ dist (f i) (f j)) :
    (Fintype.card ι : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E := by
  classical
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have h := hsep i j hne
    rw [hij, dist_self] at h
    exact (not_le_of_gt hε) h
  have h := card_le_of_separated_closedBall (Finset.univ.image f) o hR hε
    (by
      intro c hc
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      exact hf i)
    (by
      intro c hc d hd hcd
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hd
      exact hsep i j (fun hij => hcd (congrArg f hij)))
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ] using h

end Metric
