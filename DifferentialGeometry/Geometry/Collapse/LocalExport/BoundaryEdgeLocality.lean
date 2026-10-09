import DifferentialGeometry.Geometry.Collapse.RankStrataBallLocality
import DifferentialGeometry.Geometry.Metric.Approximation.EdgePoint

/-!
# Weak-edge distance locality (lane BDRY-5, G19)

Review 45 §2.2 (T2: "weak-edge distance: prove local identification on active edge domains, no
rewrite of the edge vocabulary"). The weak-edge distance `x ↦ d(x, closure A)`,
`A = {y | y is a (Δ, β, σ)-edge point at scale ρ(y)}`, is local:

* `infDist_le_of_local_match_BDRY5`, `infDist_eq_of_local_match_BDRY5`: two distance functions to
  sets agree at `x`, `x'` if both are `< r` and the points of the sets within `r` correspond with
  equal distances;
* `isEdgePoint_of_ballIsometry_BDRY5`: an edge point pulls back along a ball isometry of radius
  `≥ β⁻¹` (the `β`-map lives on `B(p, β⁻¹)`; the interval map on the factor is untouched);
* `isEdgePoint_rescale_iff_of_ballIsometry_BDRY5`: at scale `c`, edge points correspond along a
  ball isometry of radius `R c`, `R ≥ β⁻¹`;
* `infDist_weakEdge_eq_of_ballIsometry_BDRY5`: if `φ` is a ball isometry from `B(j', R_b)` onto
  `B(φ j', R_b)` with `R_b ≥ 3a + β⁻¹ ρ(y)` on `B(j', 3a)` and `j'` lies in the closure of the
  weak-edge set, the weak-edge distances agree at every `x' ∈ B(j', a)`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function

namespace GC.MetricGeometry

universe u u' v

section InfDist

variable {X : Type u} {X' : Type u'} [PseudoMetricSpace X] [PseudoMetricSpace X']

/-- One inequality of distance-function locality. -/
theorem infDist_le_of_local_match_BDRY5 {x : X} {x' : X'} {S : Set X} {S' : Set X'} {r : ℝ}
    (hS : infDist x S < r) (hne : S.Nonempty)
    (h : ∀ y ∈ S, dist x y < r → ∃ y' ∈ S', dist x' y' = dist x y) :
    infDist x' S' ≤ infDist x S := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff hne).mp (lt_min hc hS)
  obtain ⟨y', hy', hd⟩ := h y hy (hxy.trans_le (min_le_right _ _))
  calc infDist x' S' ≤ dist x' y' := infDist_le_dist_of_mem hy'
    _ = dist x y := hd
    _ < c := hxy.trans_le (min_le_left _ _)

/-- **Distance-function locality.** If `d(x, S) < r`, `d(x', S') < r`, both sets are nonempty and
the points of `S` (resp. `S'`) within `r` of `x` (resp. `x'`) have partners in `S'` (resp. `S`)
at the same distance, then `d(x, S) = d(x', S')`. -/
theorem infDist_eq_of_local_match_BDRY5 {x : X} {x' : X'} {S : Set X} {S' : Set X'} {r : ℝ}
    (hS : infDist x S < r) (hS' : infDist x' S' < r) (hne : S.Nonempty) (hne' : S'.Nonempty)
    (h₁ : ∀ y ∈ S, dist x y < r → ∃ y' ∈ S', dist x' y' = dist x y)
    (h₂ : ∀ y' ∈ S', dist x' y' < r → ∃ y ∈ S, dist x y = dist x' y') :
    infDist x S = infDist x' S' :=
  le_antisymm (infDist_le_of_local_match_BDRY5 hS' hne' h₂)
    (infDist_le_of_local_match_BDRY5 hS hne h₁)

end InfDist

section EdgeLocality

variable {X : Type u} {X' : Type u'} [MetricSpace X] [MetricSpace X']

/-- **Ball locality of edge points.** A `(Δ, β, σ)`-edge point at `p` pulls back along a map
sending `p'` to `p`, preserving distances on `B(p', R)` and covering `B(p, R)`, `R ≥ β⁻¹`. -/
theorem isEdgePoint_of_ballIsometry_BDRY5 (φ : X' → X) {p' : X'} {p : X} (hp : φ p' = p) {R : ℝ}
    (hdist : ∀ x ∈ ball p' R, ∀ y ∈ ball p' R, dist (φ x) (φ y) = dist x y)
    (honto : ball p R ⊆ φ '' ball p' R) {Δ β σ : ℝ} (hβR : β⁻¹ ≤ R)
    (h : isEdgePoint.{u, v} p Δ β σ) : isEdgePoint.{u', v} p' Δ β σ := by
  obtain ⟨Y, mY, q, C, hC, hlen, ⟨F⟩, hG⟩ := h
  obtain ⟨hd, ho⟩ := ballIsometry_mono_BDRY1 φ hp hβR hdist honto
  exact ⟨Y, mY, q, C, hC, hlen, ⟨F.pullback_BDRY1 φ hp hd ho⟩, hG⟩

end EdgeLocality

section Scaled

variable {M : Type u} {M' : Type u'}

/-- **Edge points at scale `c` along a ball isometry.** If `φ` sends `p'` to `p`, preserves
distances on `B(p', R c)` and maps it onto `B(p, R c)` with `R ≥ β⁻¹`, then `p'` is a
`(Δ, β, σ)`-edge point of `(M', c⁻¹ d')` iff `p` is one of `(M, c⁻¹ d)`. -/
theorem isEdgePoint_rescale_iff_of_ballIsometry_BDRY5 (m : MetricSpace M) (m' : MetricSpace M')
    (φ : M' → M) {p' : M'} {p : M} (hp : φ p' = p) {c c' : ℝ} (hc : 0 < c) (hc' : 0 < c')
    (hcc : c' = c) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ x ∈ @ball M' m'.toPseudoMetricSpace p' (R * c),
      ∀ y ∈ @ball M' m'.toPseudoMetricSpace p' (R * c),
        @dist M m.toDist (φ x) (φ y) = @dist M' m'.toDist x y)
    (himage : φ '' @ball M' m'.toPseudoMetricSpace p' (R * c) =
      @ball M m.toPseudoMetricSpace p (R * c))
    {Δ β σ : ℝ} (hβR : β⁻¹ ≤ R) :
    @isEdgePoint.{u', v} M' (m'.rescale c'⁻¹ (inv_pos.mpr hc')) p' Δ β σ ↔
      @isEdgePoint.{u, v} M (m.rescale c⁻¹ (inv_pos.mpr hc)) p Δ β σ := by
  subst hcc
  let mR := m.rescale c'⁻¹ (inv_pos.mpr hc)
  let mR' := m'.rescale c'⁻¹ (inv_pos.mpr hc')
  have hN : Nonempty M' := ⟨p'⟩
  have hballR : @ball M mR.toPseudoMetricSpace p R = @ball M m.toPseudoMetricSpace p (R * c') :=
    rescale_inv_ball_BDRY1 m hc p R
  have hballR' : @ball M' mR'.toPseudoMetricSpace p' R =
      @ball M' m'.toPseudoMetricSpace p' (R * c') :=
    rescale_inv_ball_BDRY1 m' hc' p' R
  have hdR : ∀ x ∈ @ball M' mR'.toPseudoMetricSpace p' R,
      ∀ y ∈ @ball M' mR'.toPseudoMetricSpace p' R,
        @dist M mR.toDist (φ x) (φ y) = @dist M' mR'.toDist x y := by
    intro x hx y hy
    rw [hballR'] at hx hy
    change c'⁻¹ * @dist M m.toDist (φ x) (φ y) = c'⁻¹ * @dist M' m'.toDist x y
    rw [hdist x hx y hy]
  have hiR : φ '' @ball M' mR'.toPseudoMetricSpace p' R = @ball M mR.toPseudoMetricSpace p R := by
    rw [hballR, hballR', himage]
  obtain ⟨hψp, hψd, hψo⟩ := @ballIsometry_symm_BDRY1 M M' mR mR' hN φ p' p hp R hR hdR hiR
  constructor
  · intro h
    exact @isEdgePoint_of_ballIsometry_BDRY5 M' M mR' mR
      (invFunOn φ (@ball M' mR'.toPseudoMetricSpace p' R)) p p' hψp R hψd hψo Δ β σ hβR h
  · intro h
    exact @isEdgePoint_of_ballIsometry_BDRY5 M M' mR mR' φ p' p hp R hdR hiR.symm.subset Δ β σ hβR h

end Scaled

section WeakEdge

variable {M : Type u} {M' : Type u'} [m : MetricSpace M] [m' : MetricSpace M']

/-- **Weak-edge distance locality along a ball isometry.** Let `φ : M' → M` preserve distances on
`B(j', R_b)` and map it onto `B(φ j', R_b)`, with scales `ρ' = ρ ∘ φ` and the budget
`3a + β⁻¹ ρ'(y) ≤ R_b` on `B(j', 3a)`. If `j'` lies in the closure of the `(Δ, β, σ)`-edge set of
`M'`, then at every `x' ∈ B(j', a)` the distance to the closure of the edge set of `M'` equals the
distance of `φ x'` to the closure of the edge set of `M`. -/
theorem infDist_weakEdge_eq_of_ballIsometry_BDRY5 (φ : M' → M) (ρ : M → ℝ) (hρ : ∀ y, 0 < ρ y)
    (ρ' : M' → ℝ) (hρ' : ∀ y, 0 < ρ' y) (hρφ : ∀ y, ρ' y = ρ (φ y))
    {Δ β σ a Rb : ℝ} (ha : 0 < a) (hβ : 0 < β) {j' : M'}
    (hdist : ∀ x ∈ ball j' Rb, ∀ y ∈ ball j' Rb, dist (φ x) (φ y) = dist x y)
    (himage : φ '' ball j' Rb = ball (φ j') Rb)
    (hbudget : ∀ y ∈ ball j' (3 * a), 3 * a + β⁻¹ * ρ' y ≤ Rb)
    (hj : j' ∈ closure {y | @isEdgePoint.{u', v} M' (m'.rescale (ρ' y)⁻¹ (inv_pos.mpr (hρ' y)))
      y Δ β σ})
    (x' : M') (hx : x' ∈ ball j' a) :
    infDist x' (closure {y | @isEdgePoint.{u', v} M' (m'.rescale (ρ' y)⁻¹ (inv_pos.mpr (hρ' y)))
        y Δ β σ}) =
      infDist (φ x') (closure {y | @isEdgePoint.{u, v} M (m.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y)))
        y Δ β σ}) := by
  set S' := {y | @isEdgePoint.{u', v} M' (m'.rescale (ρ' y)⁻¹ (inv_pos.mpr (hρ' y))) y Δ β σ}
    with hS'
  set S := {y | @isEdgePoint.{u, v} M (m.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ β σ} with hS
  rw [infDist_closure, infDist_closure]
  have hj3 : j' ∈ ball j' (3 * a) := mem_ball_self (by positivity)
  have hRb3 : 3 * a < Rb := by
    have h1 := hbudget j' hj3
    have h2 : 0 < β⁻¹ * ρ' j' := mul_pos (inv_pos.mpr hβ) (hρ' j')
    linarith
  have hjRb : j' ∈ ball j' Rb := mem_ball_self (by linarith)
  have h3Rb : ∀ y ∈ ball j' (3 * a), y ∈ ball j' Rb := fun y hy => ball_subset_ball hRb3.le hy
  -- the edge-point transfer at every point of `B(j', 3a)`
  have htrans : ∀ y' ∈ ball j' (3 * a), (y' ∈ S' ↔ φ y' ∈ S) := by
    intro y' hy'
    have hb := hbudget y' hy'
    have hsub : ball y' (β⁻¹ * ρ' y') ⊆ ball j' Rb := fun z hz => by
      rw [mem_ball] at hz hy' ⊢
      calc dist z j' ≤ dist z y' + dist y' j' := dist_triangle _ _ _
        _ < β⁻¹ * ρ' y' + 3 * a := add_lt_add hz hy'
        _ ≤ Rb := by linarith
    have hy'Rb : y' ∈ ball j' Rb := h3Rb y' hy'
    have hdist' : ∀ x ∈ ball y' (β⁻¹ * ρ (φ y')), ∀ y ∈ ball y' (β⁻¹ * ρ (φ y')),
        dist (φ x) (φ y) = dist x y := by
      rw [← hρφ]
      exact fun x hx y hy => hdist x (hsub hx) y (hsub hy)
    have himage' : φ '' ball y' (β⁻¹ * ρ (φ y')) = ball (φ y') (β⁻¹ * ρ (φ y')) := by
      rw [← hρφ]
      apply Subset.antisymm
      · rintro _ ⟨z, hz, rfl⟩
        rw [mem_ball, hdist z (hsub hz) y' hy'Rb]
        exact hz
      · intro w hw
        have hwj : w ∈ ball (φ j') Rb := by
          rw [mem_ball] at hw hy' ⊢
          calc dist w (φ j') ≤ dist w (φ y') + dist (φ y') (φ j') := dist_triangle _ _ _
            _ = dist w (φ y') + dist y' j' := by rw [hdist y' hy'Rb j' hjRb]
            _ < β⁻¹ * ρ' y' + 3 * a := add_lt_add hw hy'
            _ ≤ Rb := by linarith
        rw [← himage] at hwj
        obtain ⟨z, hz, rfl⟩ := hwj
        refine ⟨z, ?_, rfl⟩
        rw [mem_ball, ← hdist z hz y' hy'Rb]
        exact hw
    exact isEdgePoint_rescale_iff_of_ballIsometry_BDRY5 m m' φ rfl (hρ (φ y')) (hρ' y') (hρφ y')
      (inv_pos.mpr hβ) hdist' himage' le_rfl
  obtain ⟨y0, hy0S, hy0⟩ := Metric.mem_closure_iff.mp hj a ha
  have hxj : dist x' j' < a := hx
  have hy0j : dist y0 j' < a := by rw [dist_comm]; exact hy0
  have hy03 : y0 ∈ ball j' (3 * a) := by rw [mem_ball]; linarith
  have hx3 : x' ∈ ball j' (3 * a) := by rw [mem_ball]; linarith
  have hxy0 : dist x' y0 < 2 * a := by
    calc dist x' y0 ≤ dist x' j' + dist j' y0 := dist_triangle _ _ _
      _ < a + a := add_lt_add hxj hy0
      _ = 2 * a := by ring
  have hφy0 : φ y0 ∈ S := (htrans y0 hy03).mp hy0S
  have hdxy0 : dist (φ x') (φ y0) = dist x' y0 := hdist x' (h3Rb x' hx3) y0 (h3Rb y0 hy03)
  refine infDist_eq_of_local_match_BDRY5 (r := 2 * a)
    ((infDist_le_dist_of_mem hy0S).trans_lt hxy0)
    ((infDist_le_dist_of_mem hφy0).trans_lt (hdxy0 ▸ hxy0)) ⟨y0, hy0S⟩ ⟨φ y0, hφy0⟩ ?_ ?_
  · intro y' hy'S hxy'
    have hy'3 : y' ∈ ball j' (3 * a) := by
      rw [mem_ball]
      calc dist y' j' ≤ dist y' x' + dist x' j' := dist_triangle _ _ _
        _ < 2 * a + a := by rw [dist_comm]; exact add_lt_add hxy' hxj
        _ = 3 * a := by ring
    exact ⟨φ y', (htrans y' hy'3).mp hy'S, hdist x' (h3Rb x' hx3) y' (h3Rb y' hy'3)⟩
  · intro y hyS hxy
    have hyj : y ∈ ball (φ j') Rb := by
      rw [mem_ball]
      calc dist y (φ j') ≤ dist y (φ x') + dist (φ x') (φ j') := dist_triangle _ _ _
        _ = dist y (φ x') + dist x' j' := by rw [hdist x' (h3Rb x' hx3) j' hjRb]
        _ < 2 * a + a := by rw [dist_comm]; exact add_lt_add hxy hxj
        _ ≤ Rb := by linarith
    rw [← himage] at hyj
    obtain ⟨y', hy'Rb, rfl⟩ := hyj
    have hy'3 : y' ∈ ball j' (3 * a) := by
      rw [mem_ball, ← hdist y' hy'Rb j' hjRb]
      calc dist (φ y') (φ j') ≤ dist (φ y') (φ x') + dist (φ x') (φ j') := dist_triangle _ _ _
        _ = dist (φ y') (φ x') + dist x' j' := by rw [hdist x' (h3Rb x' hx3) j' hjRb]
        _ < 2 * a + a := by rw [dist_comm]; exact add_lt_add hxy hxj
        _ = 3 * a := by ring
    exact ⟨y', (htrans y' hy'3).mpr hyS, (hdist x' (h3Rb x' hx3) y' hy'Rb).symm⟩

end WeakEdge

end GC.MetricGeometry
