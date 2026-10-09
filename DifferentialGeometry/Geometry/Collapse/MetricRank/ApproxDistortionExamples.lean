import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxRankWiring
import DifferentialGeometry.Geometry.Collapse.MetricRank.RankAdaptersExamples

/-!
# Explicit consumers of the product-approximation wiring (review 75, section C, S-X144b group G7)

The thin factor is `ZT = [0, 1/400]` (distances `≤ D = 1/400`); the product approximation is the
identity of `A ×₂ ZT` at the tolerance `δ = 1/200 = δ₀`, so `ε_m = δ + D = 3/400 ≤ 1/100`.

Kernel level (`X = A ×₂ ZT`, no splitting of the review's ranks at the register tolerances):

* thin plane `ℝ² ×₂ ZT`: no splitting of rank `3` at `3/20` (`thin_plane_no_rank_three_SMR`);
* thin line `ℝ ×₂ ZT`: no splitting of rank `2` at `1/10`, rank `3` at `3/20`
  (`thin_line_no_rank_two_SMR`, `thin_line_no_rank_three_SMR`);
* thin half plane `H ×₂ ZT` at `((0, 1/50), 0)`: no splitting of rank `2` at `1/10`, rank `3` at
  `3/20` (`thin_halfplane_no_rank_two_SMR`, `thin_halfplane_no_rank_three_SMR`).

Rank level (scale `ρ ≡ 1`, register `β = (1/20, 1/10, 3/20)` of `RankAdaptersExamples`): the thin
plane has scaled rank exactly `2`, the thin line exactly `1`, the thin half plane at most `1`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

local notation "ZT" => {t : ℝ // t ∈ Set.Icc (0 : ℝ) (1 / 400)}
local notation "HP" => {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}

/-- All distances of the thin factor `ZT` are `≤ 1/400`. -/
theorem thin_factor_dist_SMR (z₁ z₂ : ZT) : dist z₁ z₂ ≤ 1 / 400 := by
  rw [Subtype.dist_eq, Real.dist_eq, abs_le]
  have h1 := z₁.2
  have h2 := z₂.2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The base point of the thin factor. -/
def thinBase_SMR : ZT := ⟨0, by norm_num⟩

/-- The identity of a product `A ×₂ ZT` is a Kleiner-Lott `1/200`-approximation of itself at any
point. -/
theorem thin_identity_approx_SMR {A : Type*} [MetricSpace A] (a : A) :
    Nonempty (KleinerLottApprox (WithLp.toLp 2 (a, thinBase_SMR) : WithLp 2 (A × ZT))
      (WithLp.toLp 2 (a, thinBase_SMR) : WithLp 2 (A × ZT)) (1 / 200)) :=
  ⟨(IsometryEquiv.refl (WithLp 2 (A × ZT))).toKleinerLottApprox rfl (by norm_num)
    (by norm_num)⟩

/-- **Thin plane, kernel level.** `ℝ² ×₂ ZT` at `(0, 0)` has no splitting of rank `3` at `3/20`. -/
theorem thin_plane_no_rank_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), thinBase_SMR) :
        WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT)) 3 (3 / 20) :=
  not_hasEuclideanSplitting_ge_three_of_thin_plane_SMR (D := 1 / 400)
    (thin_identity_approx_SMR _).some thin_factor_dist_SMR (by norm_num) le_rfl le_rfl

/-- **Thin line, kernel level.** `ℝ ×₂ ZT` at `(0, 0)` has no splitting of rank `2` at `1/10`. -/
theorem thin_line_no_rank_two_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) 2 (1 / 10) :=
  not_hasEuclideanSplitting_ge_two_of_thin_line_SMR (D := 1 / 400)
    (thin_identity_approx_SMR _).some thin_factor_dist_SMR (by norm_num) (by norm_num) le_rfl

/-- **Thin line, kernel level.** The same point has no splitting of rank `3` at `3/20`. -/
theorem thin_line_no_rank_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) 3 (3 / 20) :=
  not_hasEuclideanSplitting_ge_two_of_thin_line_SMR (D := 1 / 400)
    (thin_identity_approx_SMR _).some thin_factor_dist_SMR (by norm_num) le_rfl (by norm_num)

/-- The point `(0, 1/50)` of the half plane. -/
noncomputable def halfplanePoint_SMR : HP :=
  ⟨EuclideanSpace.single (1 : Fin 2) (1 / 50 : ℝ), by simp⟩

/-- **Thin half plane, kernel level.** `H ×₂ ZT` at `((0, 1/50), 0)` has no splitting of rank `2`
at `1/10`. -/
theorem thin_halfplane_no_rank_two_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (WithLp.toLp 2 (halfplanePoint_SMR, thinBase_SMR) : WithLp 2 (HP × ZT)) 2 (1 / 10) :=
  not_hasEuclideanSplitting_ge_two_of_thin_halfplane_SMR (D := 1 / 400) (h := 1 / 50)
    (thin_identity_approx_SMR _).some thin_factor_dist_SMR (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by simp [halfplanePoint_SMR]) (by simp [halfplanePoint_SMR])
    le_rfl

/-- **Thin half plane, kernel level.** The same point has no splitting of rank `3` at `3/20`. -/
theorem thin_halfplane_no_rank_three_SMR :
    ¬ HasEuclideanSplitting.{0, 0}
      (WithLp.toLp 2 (halfplanePoint_SMR, thinBase_SMR) : WithLp 2 (HP × ZT)) 3 (3 / 20) :=
  not_hasEuclideanSplitting_ge_two_of_thin_halfplane_SMR (D := 1 / 400) (h := 1 / 50)
    (thin_identity_approx_SMR _).some thin_factor_dist_SMR (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by simp [halfplanePoint_SMR]) (by simp [halfplanePoint_SMR])
    (by norm_num)

/-- The identity of `A ×₂ ZT` is a Kleiner-Lott `δ`-approximation of itself at the metric rescaled
by `1⁻¹` (the scaled metric at scale `ρ ≡ 1`), for every `δ ∈ (0, 1)`. -/
theorem thin_identity_rescaled_approx_SMR {A : Type*} [MetricSpace A] (a : A) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Nonempty (@KleinerLottApprox (WithLp 2 (A × ZT)) (WithLp 2 (A × ZT))
      ((inferInstance : MetricSpace (WithLp 2 (A × ZT))).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos))
      _ (WithLp.toLp 2 (a, thinBase_SMR)) (WithLp.toLp 2 (a, thinBase_SMR)) δ) :=
  kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr one_pos) id
    (fun x y => by rw [inv_one, one_mul]; rfl) Function.surjective_id rfl hδ hδ1

/-- **Thin plane, rank level.** `M = ℝ² ×₂ ZT` at `(0, 0)`, scale `ρ ≡ 1`, register
`β = (1/20, 1/10, 3/20)`: scaled rank exactly `2` (`δ = 1/200`, `D = 1/400`; two-splitting at
`1/10` from the identity). -/
theorem thin_plane_scaledSplittingRank_two_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT) => (1 : ℝ))
      (fun _ => one_pos) betaRegister_SMR
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), thinBase_SMR)) = 2 := by
  have h2 : @HasEuclideanSplitting.{0, 0} (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT))
      ((inferInstance : MetricSpace (WithLp 2 (EuclideanSpace ℝ (Fin 2) × ZT))).rescale
        (1 : ℝ)⁻¹ (inv_pos.mpr one_pos))
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), thinBase_SMR)) 2 (betaRegister_SMR 2) := by
    refine ⟨ZT, inferInstance, thinBase_SMR, ?_⟩
    rw [betaRegister_two_SMR]
    exact thin_identity_rescaled_approx_SMR _ (by norm_num) (by norm_num)
  exact scaledSplittingRank_eq_two_of_thin_plane_SMR (D := 1 / 400)
    (thin_identity_rescaled_approx_SMR _ (δ := 1 / 200) (by norm_num) (by norm_num)).some
    thin_factor_dist_SMR (by norm_num) h2 (by rw [betaRegister_three_SMR])

/-- **Thin line, rank level.** `M = ℝ ×₂ ZT` at `(0, 0)`, scale `ρ ≡ 1`: scaled rank exactly `1`
(one-splitting at `1/20` from `(x, z) ↦ (!₂[x], z)`). -/
theorem thin_line_scaledSplittingRank_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (ℝ × ZT) => (1 : ℝ)) (fun _ => one_pos)
      betaRegister_SMR (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR)) = 1 := by
  have h1 : @HasEuclideanSplitting.{0, 0} (WithLp 2 (ℝ × ZT))
      ((inferInstance : MetricSpace (WithLp 2 (ℝ × ZT))).rescale (1 : ℝ)⁻¹
        (inv_pos.mpr one_pos))
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR)) 1 (betaRegister_SMR 1) := by
    refine ⟨ZT, inferInstance, thinBase_SMR, ?_⟩
    rw [betaRegister_one_SMR]
    refine kleinerLott_of_scaled_surjective_SMR (inv_pos.mpr one_pos)
      (fun w : WithLp 2 (ℝ × ZT) =>
        (WithLp.toLp 2 ((!₂[w.fst] : EuclideanSpace ℝ (Fin 1)), w.snd) :
          WithLp 2 (EuclideanSpace ℝ (Fin 1) × ZT))) ?_ ?_ ?_ (by norm_num) (by norm_num)
    · intro v w
      have h1 := WithLp.prod_dist_sq_eq_add_sq
        (WithLp.toLp 2 ((!₂[v.fst] : EuclideanSpace ℝ (Fin 1)), v.snd) :
          WithLp 2 (EuclideanSpace ℝ (Fin 1) × ZT))
        (WithLp.toLp 2 ((!₂[w.fst] : EuclideanSpace ℝ (Fin 1)), w.snd))
      have h2 := WithLp.prod_dist_sq_eq_add_sq v w
      simp only [WithLp.toLp_fst, WithLp.toLp_snd] at h1
      rw [inv_one, one_mul]
      refine (sq_eq_sq₀ dist_nonneg dist_nonneg).mp ?_
      rw [h1, h2, dist_sq_euclideanOne_SMR, Real.dist_eq, sq_abs]
    · rintro ⟨a, z⟩
      refine ⟨WithLp.toLp 2 (a 0, z), ?_⟩
      have ha : (!₂[a 0] : EuclideanSpace ℝ (Fin 1)) = a := by
        ext i
        fin_cases i
        rfl
      change WithLp.toLp 2 ((!₂[a 0] : EuclideanSpace ℝ (Fin 1)), z) = _
      rw [ha]
    · simp
  exact scaledSplittingRank_eq_one_of_thin_line_SMR (D := 1 / 400)
    (thin_identity_rescaled_approx_SMR (0 : ℝ) (δ := 1 / 200) (by norm_num) (by norm_num)).some
    thin_factor_dist_SMR (by norm_num) h1 (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR])

/-- **Thin half plane, rank level.** `M = H ×₂ ZT` at `((0, 1/50), 0)`, scale `ρ ≡ 1`: scaled rank
at most `1`. -/
theorem thin_halfplane_scaledSplittingRank_le_one_SMR :
    scaledSplittingRank.{0, 0} (fun _ : WithLp 2 (HP × ZT) => (1 : ℝ)) (fun _ => one_pos)
      betaRegister_SMR (WithLp.toLp 2 (halfplanePoint_SMR, thinBase_SMR)) ≤ 1 :=
  scaledSplittingRank_le_one_of_thin_halfplane_SMR (D := 1 / 400) (h := 1 / 50)
    (thin_identity_rescaled_approx_SMR halfplanePoint_SMR (δ := 1 / 200) (by norm_num)
      (by norm_num)).some
    thin_factor_dist_SMR (by norm_num) (by rw [betaRegister_two_SMR]; norm_num)
    (by rw [betaRegister_three_SMR]) (by norm_num) (by norm_num) (by simp [halfplanePoint_SMR])
    (by simp [halfplanePoint_SMR])

end GC.MetricGeometry
