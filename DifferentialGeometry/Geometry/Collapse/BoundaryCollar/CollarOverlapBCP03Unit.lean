import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapBCP03
import DifferentialGeometry.Topology.Ehresmann.Interval

/-!
# Row BCP03 on the unit interval: `M ≅ T² × [0, 1]` keeping the two labels

Blueprint 207B, BCP03 (`B:8323–8441`) states the product alternative as a diffeomorphism onto
`T² × [0, 1]` that preserves the two external boundary labels. `NearlyCuspidalBoundary.bcp03`
(BCP23) produces `T² × [a, b]` through the regular height `u` of E7; composing with the affine
diffeomorphism `[0, 1] ≃ [a, b]` (`affineIntervalDiffeomorph`) gives the blueprint's form.

* `NearlyCuspidalBoundary.bcp03_product_unit`: overlapping enlarged collars `e_i{z < 92}`,
  `e_j{z < 92}` (`i ≠ j`) give `D : T² × [0, 1] ≃ W` with `T² × {0}` onto `∂_i W` and `T² × {1}`
  onto `∂_j W`, and a regular smooth `u` with `u ∘ D = a + (b - a) t` for some `a < b`.
* `NearlyCuspidalBoundary.bcp03_unit` (row BCP03, blueprint form): either some two distinct
  components give such a `D`, or all enlarged collars are pairwise disjoint and the BCP01.c inner
  collars are pairwise disjoint at distance `≥ 1` (BCP03.b).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Ehresmann
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- A diffeomorphism `T² × [a, b] ≃ W` reparametrised on `T² × [0, 1]` by the affine map
`t ↦ a + (b - a) t`. -/
def torusIccUnitDiffeomorph {a b : ℝ} [Fact (a < b)]
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞) :
    Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞ :=
  ((Diffeomorph.refl torusModel Torus ∞).prodCongr (affineIntervalDiffeomorph a b)).trans D

theorem torusIccUnitDiffeomorph_apply {a b : ℝ} [Fact (a < b)]
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞)
    (p : Torus × Icc (0 : ℝ) 1) :
    torusIccUnitDiffeomorph D p = D (p.1, affineIntervalDiffeomorph a b p.2) := rfl

/-- The bottom label: if `T² × {a}` is the preimage of `S` under `D`, then `T² × {0}` is its
preimage under the reparametrised map. -/
theorem torusIccUnitDiffeomorph_mem_iff_bot {a b : ℝ} [Fact (a < b)]
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞)
    {S : Set W.Carrier} (hS : ∀ p, D p ∈ S ↔ p.2.1 = a) {p : Torus × Icc (0 : ℝ) 1} :
    torusIccUnitDiffeomorph D p ∈ S ↔ p.2.1 = 0 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Fact.out : a < b).ne'
  rw [torusIccUnitDiffeomorph_apply, hS, affineIntervalDiffeomorph_apply]
  constructor
  · intro h
    have h' : (b - a) * p.2.1 = 0 := by linarith
    exact (mul_eq_zero.mp h').resolve_left hba
  · intro h
    rw [h]
    ring

/-- The top label: if `T² × {b}` is the preimage of `S` under `D`, then `T² × {1}` is its
preimage under the reparametrised map. -/
theorem torusIccUnitDiffeomorph_mem_iff_top {a b : ℝ} [Fact (a < b)]
    (D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞)
    {S : Set W.Carrier} (hS : ∀ p, D p ∈ S ↔ p.2.1 = b) {p : Torus × Icc (0 : ℝ) 1} :
    torusIccUnitDiffeomorph D p ∈ S ↔ p.2.1 = 1 := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Fact.out : a < b).ne'
  rw [torusIccUnitDiffeomorph_apply, hS, affineIntervalDiffeomorph_apply]
  constructor
  · intro h
    have h' : (b - a) * (p.2.1 - 1) = 0 := by linarith
    have := (mul_eq_zero.mp h').resolve_left hba
    linarith
  · intro h
    rw [h]
    ring

/-- **BCP03, product alternative on `T² × [0, 1]`.** -/
theorem NearlyCuspidalBoundary.bcp03_product_unit [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    {i j : Fin B.count} (hij : i ≠ j)
    (hover : ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} ∩
      (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}).Nonempty) :
    ∃ (u : W.Carrier → ℝ) (a b : ℝ), a < b ∧ ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, u (D p) = a + (b - a) * p.2.1) ∧ (∀ p, D p ∈ B.component i ↔ p.2.1 = 0) ∧
          ∀ p, D p ∈ B.component j ↔ p.2.1 = 1 := by
  obtain ⟨u, a, b, hab, hu, hureg, D, hDu, hDi, hDj⟩ := B.bcp03_product hK hδ0 hδ hij hover
  have hfact_BCP23b : Fact (a < b) := ⟨hab⟩
  refine ⟨u, a, b, hab, hu, hureg, torusIccUnitDiffeomorph D, fun p => ?_,
    fun _ => torusIccUnitDiffeomorph_mem_iff_bot D hDi,
    fun _ => torusIccUnitDiffeomorph_mem_iff_top D hDj⟩
  rw [torusIccUnitDiffeomorph_apply, hDu, affineIntervalDiffeomorph_apply]
  ring

/-- **Row BCP03, blueprint form.** For a nearly cuspidal boundary on a connected carrier
(`K ≥ 1`, `0 ≤ δ ≤ 1/1000`): either the carrier is diffeomorphic to `T² × [0, 1]` with
`T² × {0}` onto `∂_i W` and `T² × {1}` onto `∂_j W` for two distinct components, or the enlarged
collars `e_i{z < 92}` are pairwise disjoint and the BCP01.c inner collars `{F_i ≤ 90}`, each
containing its boundary component, are pairwise disjoint at distance `≥ 1` (BCP03.b). -/
theorem NearlyCuspidalBoundary.bcp03_unit [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) :
    (∃ (i j : Fin B.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ B.component i ↔ p.2.1 = 0) ∧ ∀ p, D p ∈ B.component j ↔ p.2.1 = 1) ∨
    ∀ i j : Fin B.count, i ≠ j →
      Disjoint ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      ∃ Fi Fj : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi ∧
        ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj ∧ (∀ x ∈ B.component i, Fi x ≤ 90) ∧
        (∀ x ∈ B.component j, Fj x ≤ 90) ∧ Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
        ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  rcases B.bcp03 hK hδ0 hδ with ⟨i, j, hij, -, a, b, hab, -, -, D, -, hDi, hDj⟩ | hdisj
  · have hfact_BCP23b : Fact (a < b) := ⟨hab⟩
    exact Or.inl ⟨i, j, hij, torusIccUnitDiffeomorph D,
      fun _ => torusIccUnitDiffeomorph_mem_iff_bot D hDi,
      fun _ => torusIccUnitDiffeomorph_mem_iff_top D hDj⟩
  · exact Or.inr hdisj

end DifferentialGeometry.Geometry.Collapse
