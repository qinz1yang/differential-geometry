import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightBCP01
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit

/-!
# Row BCP03: the nonproduct alternative (separation of the collars, BCP03.b)

Blueprint 207B, BCP03 (`B:8323–8441`). The enlarged collars `B_i⁺` are taken in the original
heights, `e_i{z < 92}` (the blueprint cuts at `η_i = 92`; `|η_i − z_i| < ε`).

* `NearlyCuspidalBoundary.not_mem_image_of_mem_component`: the `j`-th boundary component meets
  no point of the `i`-th collar `e_i(T² × [0, 100))`, `i ≠ j`.
* `NearlyCuspidalBoundary.bcp03b_heights` (BCP03.b, height form): if `e_i{z < 92}` and
  `e_j{z < 92}` are disjoint, then `d_g(x, y) ≥ √(1 − δ)(92 − z_i(x)) ≥ 1` for every `x` of
  `e_i{z ≤ 90.5}` and every `y` of `e_j{z < 92}` (first exit, statement E.3).
* `NearlyCuspidalBoundary.bcp03b` (BCP03.b for the source's level-90 collars): for any
  functions `F_i`, `F_j` whose sublevels `{F ≤ 90}` lie in `e{z ≤ 90.5}` (the BCP01.c / E6
  collars, `CuspEmbedding.bcp01_sublevel_subset`), disjoint enlarged collars give disjoint
  `B̄_i = {F_i ≤ 90}`, `B̄_j = {F_j ≤ 90}` at distance `≥ 1`.
* `CuspEmbedding.bcp01_sublevel_subset`: the inner collar of BCP01 (the SAME `F` as clause (c)
  of `CuspEmbedding.bcp01`, recalled with its product structure) lies in `e{z ≤ 90 + ε}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- The `j`-th boundary component contains no point of the `i`-th collar (`i ≠ j`): the only
boundary points of `e_i(T² × [0, 100))` are at height `0`, i.e. on the `i`-th component. -/
theorem NearlyCuspidalBoundary.not_mem_image_of_mem_component
    (B : NearlyCuspidalBoundary W g K δ) {i j : Fin B.count} (hij : i ≠ j) {y : W.Carrier}
    (hy : y ∈ B.component j) : y ∉ (B.collar i).toFun '' cuspDomain := by
  rintro ⟨p, hp, rfl⟩
  have hbd : (B.collar i).toFun p ∈ W.model.boundary W.Carrier := by
    rw [← B.covers]
    exact mem_iUnion.mpr ⟨j, hy⟩
  have hz : p.2.val 0 = 0 := ((B.collar i).boundary_preimage hp).mp hbd
  have hpi : (B.collar i).toFun p ∈ B.component i := by
    refine (Set.ext_iff.mp (B.collar i).boundary_image _).mp ⟨p.1, ?_⟩
    change (B.collar i).toFun (p.1, halfZero) = (B.collar i).toFun p
    rw [← cusp_eq_halfZero_of_height_eq_zero hz]
  exact (Set.disjoint_left.mp (B.disjoint hij)) hpi hy

/-- **BCP03.b, height form.** If the enlarged collars `e_i{z < 92}` and `e_j{z < 92}` are
disjoint, every point of `e_i{z ≤ 90.5}` is at distance `≥ 1` (for `δ ≤ 1/2`) from every point of
`e_j{z < 92}`; in particular `e_i{z ≤ 90.5}` and `e_j{z ≤ 90.5}` are disjoint. -/
theorem NearlyCuspidalBoundary.bcp03b_heights (B : NearlyCuspidalBoundary W g K δ)
    (hδ : δ ≤ 1 / 2) {i j : Fin B.count}
    (hdisj : Disjoint ((B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92})
      ((B.collar j).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92}))
    {x y : W.Carrier} (hx : x ∈ (B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 181 / 2})
    (hy : y ∈ (B.collar j).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92}) :
    ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hp' : p.2.val 0 ≤ 181 / 2 := hp
  have hy' : y ∉ (B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92} :=
    fun h => Set.disjoint_left.mp hdisj h hy
  have h := (B.collar i).ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt
    (h := 92) (by norm_num [cuspDepth]) (by linarith) hy'
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
  have hs : 7 / 10 ≤ Real.sqrt (1 - δ) := by
    rw [show (7 / 10 : ℝ) = Real.sqrt ((7 / 10) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith)
  nlinarith

/-- **BCP03.b for the level-90 collars.** Let `F_i`, `F_j` be functions whose sublevels
`{F ≤ 90}` lie in `e{z ≤ 90.5}` (the inner collars of BCP01.c). If the enlarged collars
`e_i{z < 92}` and `e_j{z < 92}` are disjoint, then `{F_i ≤ 90}` and `{F_j ≤ 90}` are disjoint
and every two of their points are at distance `≥ 1` (for `δ ≤ 1/2`). -/
theorem NearlyCuspidalBoundary.bcp03b (B : NearlyCuspidalBoundary W g K δ) (hδ : δ ≤ 1 / 2)
    {i j : Fin B.count}
    (hdisj : Disjoint ((B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92})
      ((B.collar j).toFun '' {p : CuspHalfSpace | p.2.val 0 < 92}))
    {Fi Fj : W.Carrier → ℝ}
    (hFi : ∀ y, Fi y ≤ 90 → y ∈ (B.collar i).toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 181 / 2})
    (hFj : ∀ y, Fj y ≤ 90 → y ∈ (B.collar j).toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 181 / 2}) :
    Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
      ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  have hsep : ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
    intro x y hx hy
    obtain ⟨q, hq, rfl⟩ := hFj y hy
    have hq' : q.2.val 0 ≤ 181 / 2 := hq
    exact B.bcp03b_heights hδ hdisj (hFi x hx) ⟨q, (by linarith : q.2.val 0 < 92), rfl⟩
  refine ⟨Set.disjoint_left.mpr fun x hx hx' => ?_, hsep⟩
  have h := hsep x x hx hx'
  rw [riemannianEDistOf_self] at h
  have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal 1 := by norm_num
  exact absurd (h1.trans_le h) (lt_irrefl 0)

/-- **The inner collar of BCP01 lies in `e{z ≤ 90 + ε}`.** With `F` and `η` of
`CuspEmbedding.bcp01` (clause (c): `{F ≤ 90} = e{z ≤ 2 ∨ (z ≤ 98 ∧ η ≤ 90)}`, a smooth compact
manifold with boundary `X ∪ {F = 90}`, diffeomorphic to `T² × [a, 90]`), every point of
`{F ≤ 90}` is `e p` with `z(p) ≤ 90 + ε`. -/
theorem CuspEmbedding.bcp01_sublevel_subset {X : Set W.Carrier} (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    ∃ (η F : W.Carrier → ℝ) (a : ℝ) (har : a < 90), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η ∧
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ F ∧
      (∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) ∧
      (∀ y, F y ≤ 90 → ∃ p ∈ cuspDomain, e.toFun p = y ∧ p.2.val 0 ≤ 90 + ε) ∧
      ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // F x ≤ 90},
        letI := cs
        IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // F x ≤ 90} ∧
        (∀ y : {x : W.Carrier // F x ≤ 90}, (𝓡∂ 3).IsBoundaryPoint y ↔
          (y.1 ∈ X ∨ F y.1 = 90)) ∧
        haveI : Fact (a < 90) := ⟨har⟩
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc a 90)
            {x : W.Carrier // F x ≤ 90} ∞,
          (∀ p, F (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ X ↔ p.2.1 = a := by
  obtain ⟨η, F, a, har, hη, hF, hb, -, hchar, cs, hman, -, hbd, D, hD⟩ :=
    e.bcp01 hK hδ0 hδ hε hε1
  refine ⟨η, F, a, har, hη, hF, fun p hp h2 h98 => (hb p hp h2 h98).1, ?_, cs, hman, hbd, D, hD⟩
  intro y hy
  obtain ⟨p, hp, rfl, hcase⟩ := (hchar y).mp hy
  refine ⟨p, hp, rfl, ?_⟩
  rcases hcase with h2 | ⟨h98, hη90⟩
  · linarith
  · rcases le_or_gt (p.2.val 0) 2 with h2 | h2
    · linarith
    · have h := (hb p hp h2.le h98).1
      linarith [(abs_lt.mp h).1]

end DifferentialGeometry.Geometry.Collapse
