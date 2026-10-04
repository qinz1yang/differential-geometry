import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.TwoCollarGlue

/-!
# Consumers of the two-collar product (E7, the product alternative of BCP03)

For a nearly cuspidal boundary whose components are exactly `i ≠ j`:

* `NearlyCuspidalBoundary.exists_diffeomorph_torus_Icc_of_regular`: one regular smooth function
  from component `i` (level `a`) to component `j` (level `b`) makes `W ≅ T² × [a, b]`, with
  `T² × {a}` onto `∂_i W` and `T² × {b}` onto `∂_j W`;
* `NearlyCuspidalBoundary.exists_diffeomorph_torus_Icc_of_two_collars`: the same from the two
  collar functions `F_i`, `F_j` and the transition hypotheses (the BCP03 overlap output).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- A boundary point lies in one of the two components `i`, `j` when these are all of them. -/
theorem NearlyCuspidalBoundary.mem_or_mem_of_isBoundaryPoint (B : NearlyCuspidalBoundary W g K δ)
    {i j : Fin B.count} (hcover : ∀ k, k = i ∨ k = j) {x : W.Carrier}
    (hx : W.model.IsBoundaryPoint x) : x ∈ B.component i ∨ x ∈ B.component j := by
  have hxb : x ∈ W.model.boundary W.Carrier := hx
  rw [← B.covers, mem_iUnion] at hxb
  obtain ⟨k, hk⟩ := hxb
  rcases hcover k with rfl | rfl
  · exact Or.inl hk
  · exact Or.inr hk

/-- The `j`-th boundary component is nonempty. -/
theorem NearlyCuspidalBoundary.component_nonempty (B : NearlyCuspidalBoundary W g K δ)
    (j : Fin B.count) : (B.component j).Nonempty := by
  obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
  have h : (B.collar j).toFun (t₀, halfZero) ∈
      range (fun t : Torus => (B.collar j).toFun (t, halfZero)) := mem_range_self t₀
  rw [(B.collar j).boundary_image] at h
  exact ⟨_, h⟩

/-- **E7 for a nearly cuspidal boundary with two components.** -/
theorem NearlyCuspidalBoundary.exists_diffeomorph_torus_Icc_of_regular
    (B : NearlyCuspidalBoundary W g K δ) {i j : Fin B.count} (hcover : ∀ k, k = i ∨ k = j)
    {u : W.Carrier → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u)
    (hreg : ∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) (ha : ∀ x ∈ B.component i, u x = a)
    (hb : ∀ x ∈ B.component j, u x = b) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
      (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ B.component i ↔ p.2.1 = a) ∧
        ∀ p, D p ∈ B.component j ↔ p.2.1 = b :=
  (B.collar i).exists_diffeomorph_torus_Icc_of_regular hab hu hreg ha hb
    (fun _ hx => B.mem_or_mem_of_isBoundaryPoint hcover hx) (B.component_nonempty j)

/-- **E7 from the two collar functions** (the BCP03 product alternative, labels kept). -/
theorem NearlyCuspidalBoundary.exists_diffeomorph_torus_Icc_of_two_collars
    (B : NearlyCuspidalBoundary W g K δ) {i j : Fin B.count} (hcover : ∀ k, k = i ∨ k = j)
    {Fi Fj : W.Carrier → ℝ} {ai aj c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hFi : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi) (hFj : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj)
    (hXi : ∀ x ∈ B.component i, Fi x = ai) (hai : ai < c₁)
    (hXj : ∀ x ∈ B.component j, Fj x = aj) (hXjc : ∀ x ∈ B.component j, c₂ ≤ Fi x)
    (hregi : ∀ x, Fi x < c₁ → mfderiv W.model 𝓘(ℝ, ℝ) Fi x ≠ 0)
    (hregj : ∀ x, c₂ < Fi x → mfderiv W.model 𝓘(ℝ, ℝ) Fj x ≠ 0)
    (htr : ∀ x, c₁ ≤ Fi x → Fi x ≤ c₂ → ∃ v : TangentSpace W.model x,
      0 < (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fi x v) ∧
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fj x v) < 0) :
    ∃ (a b : ℝ) (hab : a < b),
      haveI : Fact (a < b) := ⟨hab⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
        (∀ p, D p ∈ B.component i ↔ p.2.1 = a) ∧ ∀ p, D p ∈ B.component j ↔ p.2.1 = b := by
  obtain ⟨-, -, a, b, hab, -, -, -, -, D, -, hDi, hDj⟩ :=
    (B.collar i).exists_diffeomorph_torus_Icc_of_two_collars (B.collar j) hc hFi hFj hXi hai
      hXj hXjc (fun _ hx => B.mem_or_mem_of_isBoundaryPoint hcover hx) hregi hregj htr
  exact ⟨a, b, hab, D, hDi, hDj⟩

end DifferentialGeometry.Geometry.Collapse
