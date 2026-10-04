import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlap

/-!
# Consumer of BCP03.b: the level-90 collars of two components are separated

* `NearlyCuspidalBoundary.bcp03b_inner_collars`: for two distinct components with disjoint
  enlarged collars `e_i{z < 92}`, `e_j{z < 92}`, the BCP01.c inner collars `B̄_i = {F_i ≤ 90}`,
  `B̄_j = {F_j ≤ 90}` (each containing its boundary component) are disjoint and at distance
  `≥ 1`.
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- The inner collar of BCP01 contains its boundary component and lies in `e{z ≤ 90.5}`. -/
theorem CuspEmbedding.exists_inner_collar_bcp03 {X : Set W.Carrier} (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) :
    ∃ F : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x ∈ X, F x ≤ 90) ∧
      ∀ y, F y ≤ 90 → y ∈ e.toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 181 / 2} := by
  obtain ⟨η, F, a, har, hη, hF, hb, -, hchar, -⟩ :=
    e.bcp01 hK hδ0 hδ (ε := 1 / 1000) (by norm_num) le_rfl
  refine ⟨F, hF, fun x hx => ?_, fun y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (Set.ext_iff.mp e.boundary_image x).mpr hx
    refine (hchar _).mpr ⟨(t, halfZero), ?_, rfl, Or.inl ?_⟩
    · change (0 : ℝ) < 100
      norm_num
    · change (0 : ℝ) ≤ 2
      norm_num
  · obtain ⟨p, hp, rfl, hcase⟩ := (hchar y).mp hy
    refine ⟨p, ?_, rfl⟩
    change p.2.val 0 ≤ 181 / 2
    rcases hcase with h2 | ⟨h98, hη90⟩
    · linarith
    · rcases le_or_gt (p.2.val 0) 2 with h2 | h2
      · linarith
      · have h := (hb p hp h2.le h98).1
        linarith [(abs_lt.mp h).1]

/-- **BCP03.b for the inner collars.** -/
theorem NearlyCuspidalBoundary.bcp03b_inner_collars (B : NearlyCuspidalBoundary W g K δ)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {i j : Fin B.count}
    (hdisj : Disjoint ((B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92})
      ((B.collar j).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92})) :
    ∃ Fi Fj : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj ∧ (∀ x ∈ B.component i, Fi x ≤ 90) ∧
      (∀ x ∈ B.component j, Fj x ≤ 90) ∧ Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
      ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  obtain ⟨Fi, hFi, hXi, hsubi⟩ := (B.collar i).exists_inner_collar_bcp03 hK hδ0 hδ
  obtain ⟨Fj, hFj, hXj, hsubj⟩ := (B.collar j).exists_inner_collar_bcp03 hK hδ0 hδ
  obtain ⟨hd, hsep⟩ := B.bcp03b (by linarith) hdisj hsubi hsubj
  exact ⟨Fi, Fj, hFi, hFj, hXi, hXj, hd, hsep⟩

end DifferentialGeometry.Geometry.Collapse
