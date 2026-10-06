import DifferentialGeometry.Geometry.Collapse.MetricRank.KLRelax
import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxDistortionExamples

/-!
# Explicit consumers of the tolerance relaxation (S-X144c, group G9)

* the identity of the thin product `ℝ ×₂ [0, 1/400]`, a Kleiner-Lott `1/200`-approximation of
  itself (`thin_identity_approx_SMR`), is a `β`-approximation for `β = 1/100` (`2 δ = 1/100`,
  the borderline case of `KleinerLottApprox.relax_SMR`), `1/20`, `1/10` and `3/20`
  (`thin_identity_relax_SMR`);
* the identity of `ℝ` at tolerance `1/300` is a `1/100`-approximation by the `3 δ ≤ β` form
  (`real_identity_relax_three_SMR`);
* splitting level: the scaled plane `(ℝ², dist / 1)` has a two-splitting at tolerance `1/200`
  (`hasSplitting_euclidean_scaled_SMR`), hence at the register values `β 2 = 1/10`,
  `β 3 = 3/20` (`plane_splitting_relax_SMR`), and the scaled line has a one-splitting at `1/20`
  from the tolerance `1/50` (`line_splitting_relax_SMR`).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

local notation "ZT" => {t : ℝ // t ∈ Set.Icc (0 : ℝ) (1 / 400)}
local notation "mR1" =>
  (MetricSpace.rescale (inferInstance : MetricSpace ℝ) (1 : ℝ)⁻¹ (inv_pos.mpr one_pos))
local notation "mR2" =>
  (MetricSpace.rescale (inferInstance : MetricSpace (EuclideanSpace ℝ (Fin 2))) (1 : ℝ)⁻¹
    (inv_pos.mpr one_pos))

/-- The identity of the thin product at tolerance `1/200` relaxes to the tolerances
`1/100`, `1/20`, `1/10`, `3/20`. -/
theorem thin_identity_relax_SMR :
    Nonempty (KleinerLottApprox
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT))
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) (1 / 100)) ∧
    Nonempty (KleinerLottApprox
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT))
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) (1 / 20)) ∧
    Nonempty (KleinerLottApprox
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT))
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) (1 / 10)) ∧
    Nonempty (KleinerLottApprox
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT))
      (WithLp.toLp 2 ((0 : ℝ), thinBase_SMR) : WithLp 2 (ℝ × ZT)) (3 / 20)) := by
  have f := (thin_identity_approx_SMR (0 : ℝ)).some
  exact ⟨⟨f.relax_SMR (by norm_num) (by norm_num)⟩, ⟨f.relax_SMR (by norm_num) (by norm_num)⟩,
    ⟨f.relax_SMR (by norm_num) (by norm_num)⟩, ⟨f.relax_SMR (by norm_num) (by norm_num)⟩⟩

/-- The `3 δ ≤ β` form: the identity of `ℝ` at tolerance `1/300` is a `1/100`-approximation. -/
theorem real_identity_relax_three_SMR :
    Nonempty (KleinerLottApprox (0 : ℝ) (0 : ℝ) (1 / 100)) :=
  ⟨((IsometryEquiv.refl ℝ).toKleinerLottApprox (p := (0 : ℝ)) (q := 0) rfl (δ := 1 / 300)
    (by norm_num) (by norm_num)).relax_three_SMR (by norm_num) (by norm_num)⟩

/-- The plane `(ℝ², dist / 1)` has a two-splitting at the register tolerances `1/10`, `3/20`,
obtained from the tolerance `1/200`. -/
theorem plane_splitting_relax_SMR :
    @HasEuclideanSplitting.{0, 0} (EuclideanSpace ℝ (Fin 2))
      ((inferInstance : MetricSpace (EuclideanSpace ℝ (Fin 2))).rescale (1 : ℝ)⁻¹
        (inv_pos.mpr one_pos)) 0 2 (1 / 10) ∧
    @HasEuclideanSplitting.{0, 0} (EuclideanSpace ℝ (Fin 2))
      ((inferInstance : MetricSpace (EuclideanSpace ℝ (Fin 2))).rescale (1 : ℝ)⁻¹
        (inv_pos.mpr one_pos)) 0 2 (3 / 20) := by
  have h := hasSplitting_euclidean_scaled_SMR 2 (r := 1) one_pos (δ := 1 / 200) (by norm_num)
    (by norm_num)
  exact ⟨@HasEuclideanSplitting.relax_SMR.{0, 0} _ mR2 _ _ _ _ h (by norm_num) (by norm_num),
    @HasEuclideanSplitting.relax_three_SMR.{0, 0} _ mR2 _ _ _ _ h (by norm_num) (by norm_num)⟩

/-- The line `(ℝ, dist / 1)` has a one-splitting at tolerance `1/20` (the register value
`β 1`) obtained from the tolerance `1/50`, with the `3 δ ≤ β` form borderline
`3 / 60 = 1/20` at `δ = 1/60`. -/
theorem line_splitting_relax_SMR :
    @HasEuclideanSplitting.{0, 0} ℝ
      ((inferInstance : MetricSpace ℝ).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)) 0 1 (1 / 20) ∧
    @HasEuclideanSplitting.{0, 0} ℝ
      ((inferInstance : MetricSpace ℝ).rescale (1 : ℝ)⁻¹ (inv_pos.mpr one_pos)) 0 1 (1 / 20) := by
  have h50 := hasSplitting_real_scaled_SMR one_pos (δ := 1 / 50) (by norm_num) (by norm_num)
  have h60 := hasSplitting_real_scaled_SMR one_pos (δ := 1 / 60) (by norm_num) (by norm_num)
  exact ⟨@HasEuclideanSplitting.relax_SMR.{0, 0} _ mR1 _ _ _ _ h50 (by norm_num) (by norm_num),
    @HasEuclideanSplitting.relax_three_SMR.{0, 0} _ mR1 _ _ _ _ h60 (by norm_num)
      (by norm_num)⟩

end GC.MetricGeometry
