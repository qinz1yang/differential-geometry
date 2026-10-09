import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapBCP03

/-!
# Consumers of row BCP03

* `NearlyCuspidalBoundary.bcp03_pair`: for two distinct components `i ≠ j`, overlapping enlarged
  collars give the torus product `W ≅ T² × [a, b]` (labels `∂_i`, `∂_j`), and disjoint enlarged
  collars give separated inner collars (BCP03.b).
* `NearlyCuspidalBoundary.vertical_sign_of_overlap`: on two overlapping collars, at every point of
  the `i`-collar of height `3 ≤ z_i ≤ 97.5` lying in `e_j{z ≤ 97}`, the BCP01 height `η_j` of the
  `j`-th collar strictly decreases along the `i`-vertical: `∂_z(η_j ∘ e_i) ≤ −7/10` (the
  transversality input of E7).
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- BCP03 for one pair of components. -/
theorem NearlyCuspidalBoundary.bcp03_pair [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    {i j : Fin B.count} (hij : i ≠ j) :
    (((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} ∩
        (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}).Nonempty →
      ∃ (u : W.Carrier → ℝ) (a b : ℝ) (hab : a < b), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u ∧
        (∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) ∧
        haveI : Fact (a < b) := ⟨hab⟩
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
          (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ B.component i ↔ p.2.1 = a) ∧
            ∀ p, D p ∈ B.component j ↔ p.2.1 = b) ∧
    (Disjoint ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) →
      ∃ Fi Fj : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi ∧
        ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj ∧ (∀ x ∈ B.component i, Fi x ≤ 90) ∧
        (∀ x ∈ B.component j, Fj x ≤ 90) ∧ Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
        ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y) :=
  ⟨fun hover => B.bcp03_product hK hδ0 hδ hij hover,
    fun hdisj => B.bcp03b_inner_collars hK hδ0 hδ hdisj⟩

/-- On two collars, the BCP01 height of the `j`-th collar decreases along the `i`-verticals. -/
theorem NearlyCuspidalBoundary.vertical_sign_of_overlap (B : NearlyCuspidalBoundary W g K δ)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {i j : Fin B.count} (hij : i ≠ j) :
    ∃ η : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
        |η ((B.collar j).toFun p) - p.2.val 0| < 1 / 1000) ∧
      ∀ (t t' : Torus) (h z' : ℝ), 3 ≤ h → h ≤ 975 / 10 → 0 ≤ z' → z' ≤ 97 →
        (B.collar i).toFun (t, halfSpaceOneLift h) =
          (B.collar j).toFun (t', halfSpaceOneLift z') →
        (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ (B.collar i).toFun)
          (t, halfSpaceOneLift h) cuspUnitVertical) ≤ -7 / 10 := by
  obtain ⟨η, -, -, -, hη, -, hηz, hηv, hdη, hH, -⟩ :=
    (B.collar j).exists_global_height hK hδ0 hδ (ε := 1 / 1000) (by norm_num) le_rfl
  exact ⟨η, hη, hηz, fun t t' h z' hh3 hh hz'0 hz' hx =>
    B.vertical_transversal hij hK hδ hη le_rfl hηz hηv hdη hH hh3 hh hz'0 hz' hx⟩

end DifferentialGeometry.Geometry.Collapse
