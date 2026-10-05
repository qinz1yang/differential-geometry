import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspStandingSequenceInstApplications

/-!
# The double-cusp instance takes the PRODUCT branch (lane BDRY-INST2)

The boundary producers conclude "product OR separation": either `W ≅ T² × [0, 1]` by a
diffeomorphism carrying two labelled boundary components `i ≠ j` to the two ends, or the cusp
collars are separated. For the double cusp `T² × [0, 240]` the product alternative holds with the
ORIGINAL labels `0, 1` and the tree's polar diffeomorphism `torusMonodromyPolarDiffeomorph`.

* `doubleCusp_product_alternative_INST2`: any nearly cuspidal boundary on `annulusCircleCarrier`
  (any metric) whose components are `doubleCuspBoundary` satisfies the product alternative;
* `exists_doubleCusp_standing_sequence_product_INST2`: the corrected standing sequence of
  `exists_doubleCusp_standing_sequence_ratio_INST`, with the product alternative for each member.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **The product alternative for the double cusp.** For every metric `g` on the carrier
`T² × [0, 240]` and every nearly cuspidal boundary whose two components are the two ends
`doubleCuspBoundary`, the labels `0 ≠ 1` and the inverse polar diffeomorphism
`Torus × [0, 1] ≅ T² × [0, 240]` carry component `0` to `{t = 0}` and component `1` to `{t = 1}`. -/
theorem doubleCusp_product_alternative_INST2
    {g : SmoothRiemannianMetric annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier}
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary annulusCircleCarrier.{u} g K δ)
    (hc : B.count = 2) (hcomp : ∀ i, B.component i = doubleCuspBoundary.{u} (Fin.cast hc i)) :
    ∃ (i j : Fin B.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) annulusCircleCarrier.{u}.model
          (Torus × Set.Icc (0 : ℝ) 1) annulusCircleCarrier.{u}.Carrier ∞,
        (∀ p, D p ∈ B.component i ↔ p.2.1 = 0) ∧ ∀ p, D p ∈ B.component j ↔ p.2.1 = 1 := by
  refine ⟨Fin.cast hc.symm 0, Fin.cast hc.symm 1, fun h => ?_,
    torusMonodromyPolarDiffeomorph.{u}.symm, fun p => ?_, fun p => ?_⟩
  · have h' := congrArg (Fin.cast hc) h
    simp at h'
  · rw [hcomp, Fin.cast_cast, Fin.cast_eq_self]
    change (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm p)).2 =
      (if (0 : Fin 2) = 0 then 0 else 1) ↔ _
    rw [Diffeomorph.apply_symm_apply, ite_eq_left_of_eq_true _ _ (eq_self _), Subtype.ext_iff]
    rfl
  · rw [hcomp, Fin.cast_cast, Fin.cast_eq_self]
    change (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyPolarDiffeomorph.{u}.symm p)).2 =
      (if (1 : Fin 2) = 0 then 0 else 1) ↔ _
    rw [Diffeomorph.apply_symm_apply, ite_eq_right_of_eq_false _ _ (eq_false (by decide)),
      Subtype.ext_iff]
    rfl

/-- **The corrected standing sequence, in the product branch.** One `A` (positive everywhere),
then for every `δ₀ > 0` connected universe-`0` double cusps with the three standing hypotheses at
`δ_{n+1}` (two boundary components each) AND, for each member, the product alternative of the
boundary producers for the same `B n` with its original labels. -/
theorem exists_doubleCusp_standing_sequence_product_INST2 (K : ℕ) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧ ∀ δ₀ : ℝ, 0 < δ₀ →
      ∃ (W : ℕ → CompactCarrier.{0}) (_ : ∀ n, ConnectedSpace (W n).Carrier)
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, (B n).count = 2) ∧
        (∀ n, ∃ (i j : Fin (B n).count), i ≠ j ∧
          ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (W n).model (Torus × Set.Icc (0 : ℝ) 1)
            (W n).Carrier ∞,
            (∀ p, D p ∈ (B n).component i ↔ p.2.1 = 0) ∧
              ∀ p, D p ∈ (B n).component j ↔ p.2.1 = 1) ∧
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) ∧
        ∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1)) := by
  obtain ⟨A, hA, hctrl⟩ := doubleCusp_curvatureDerivativesControlled_INST.{0} K
  obtain ⟨V, hV, hvol⟩ := exists_doubleCuspMetric_volume_bound_INST.{0}
  obtain ⟨R, hR, _, hfloor⟩ := exists_doubleCuspMetric_curvatureRadius_floor_INST.{0}
  obtain ⟨D, hD, hdiam⟩ := exists_standardCuspTorus_diameter_INST
  refine ⟨A, hA, fun δ₀ hδ₀ => ?_⟩
  have hd (n : ℕ) : 0 < boundaryCounterexampleRatio δ₀ (n + 1) :=
    boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)
  have hscale (n : ℕ) := exists_doubleCuspStandingScale_INST hD hV hR (hd n)
  choose a ha ha1 haD haV using hscale
  refine ⟨fun _ => annulusCircleCarrier.{0}, fun _ => connectedSpace_productSet (Or.inl rfl),
    fun n => doubleCuspMetric.{0} (a n) (ha n),
    fun n => doubleCuspNearlyCuspidalBoundaryAt.{0} (a n) (ha n) D hD.le hdiam K
      (boundaryCounterexampleRatio δ₀ (n + 1)) (haD n), fun _ => rfl,
    fun n => doubleCusp_product_alternative_INST2 _ rfl (fun _ => rfl), fun n => ?_,
    fun n => hctrl (a n) (ha n) (ha1 n) _ (hd n)⟩
  exact boundaryVolumeCollapsed_of_floor_INST annulusCircleCarrier.{0}
    (doubleCuspMetric.{0} (a n) (ha n)) (hd n) hR (hfloor (a n) (ha n))
    ((hvol (a n) (ha n)).trans (ENNReal.ofReal_le_ofReal (haV n)))

end DifferentialGeometry.Geometry.Collapse
