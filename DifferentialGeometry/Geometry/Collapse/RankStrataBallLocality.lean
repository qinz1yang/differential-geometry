import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank
import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# Ball locality of Kleiner–Lott maps and splitting ranks (lane BDRY-1)

A `KleinerLottApprox p q δ` constrains its map only on `B(p, δ⁻¹)`. Hence:

* `KleinerLottApprox.pullback_BDRY1`: a `δ`-map at `p` pulls back along any map `φ` with
  `φ p' = p` that preserves distances on `B(p', δ⁻¹)` and covers `B(p, δ⁻¹)`;
* `ballIsometry_mono_BDRY1`, `ballIsometry_symm_BDRY1`: ball isometries restrict to smaller radii
  and invert (`invFunOn`);
* `hasEuclideanSplitting_of_ballIsometry_BDRY1`, `splittingRank_eq_of_ballIsometry_BDRY1`: the
  splitting rank at a point depends only on the ball of radius `max_k (β k)⁻¹`;
* `rescale_inv_ball_BDRY1`, `scaledSplittingRank_eq_of_ballIsometry_BDRY1`: the scaled rank
  (`scaledSplittingRank`, LC16) depends only on the ball of radius `R ρ(p)`, `R ≥ (β k)⁻¹`.

Used for the boundary carrier (LC88 / BCP04: ranks of the interior completion agree with the ranks
of the carrier away from the boundary) and usable for any localisation of the strata.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function

namespace GC.MetricGeometry

universe u u' v

section BallLocality

variable {X : Type u} {X' : Type u'} {Y : Type v} [MetricSpace X] [MetricSpace X'] [MetricSpace Y]

/-- **Ball locality of Kleiner–Lott maps.** A `δ`-map at `p` pulls back along any map `φ` sending
`p'` to `p` that preserves distances on `B(p', δ⁻¹)` and covers `B(p, δ⁻¹)`. -/
def KleinerLottApprox.pullback_BDRY1 {p : X} {q : Y} {δ : ℝ} (f : KleinerLottApprox p q δ)
    (φ : X' → X) {p' : X'} (hp : φ p' = p)
    (hdist : ∀ x ∈ ball p' δ⁻¹, ∀ y ∈ ball p' δ⁻¹, dist (φ x) (φ y) = dist x y)
    (honto : ball p δ⁻¹ ⊆ φ '' ball p' δ⁻¹) : KleinerLottApprox p' q δ where
  error_pos := f.error_pos
  error_lt_one := f.error_lt_one
  toFun := f.toFun ∘ φ
  basepoint := by simp only [comp_apply, hp, f.basepoint]
  distortion x hx x' hx' := by
    have hp' : p' ∈ ball p' δ⁻¹ := mem_ball_self (inv_pos.mpr f.error_pos)
    have hφ : ∀ z ∈ ball p' δ⁻¹, φ z ∈ ball p δ⁻¹ := fun z hz => by
      rw [mem_ball, ← hp, hdist z hz p' hp']
      exact hz
    rw [← hdist x hx x' hx']
    exact f.distortion _ (hφ x hx) _ (hφ x' hx')
  coverage y hy := by
    refine le_trans ?_ (f.coverage y hy)
    refine infDist_le_infDist_of_subset ?_ f.image_nonempty
    rw [image_comp]
    exact image_mono honto

/-- A map preserving distances on `B(p', R)`, sending `p'` to `p` and `B(p', R)` onto `B(p, R)`,
restricts to the same properties on every smaller concentric ball. -/
theorem ballIsometry_mono_BDRY1 (φ : X' → X) {p' : X'} {p : X} (hp : φ p' = p) {R r : ℝ}
    (hrR : r ≤ R)
    (hdist : ∀ x ∈ ball p' R, ∀ y ∈ ball p' R, dist (φ x) (φ y) = dist x y)
    (honto : ball p R ⊆ φ '' ball p' R) :
    (∀ x ∈ ball p' r, ∀ y ∈ ball p' r, dist (φ x) (φ y) = dist x y) ∧
      ball p r ⊆ φ '' ball p' r := by
  refine ⟨fun x hx y hy => hdist x (ball_subset_ball hrR hx) y (ball_subset_ball hrR hy),
    fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := honto (ball_subset_ball hrR hz)
  have hpR : p' ∈ ball p' R := mem_ball_self (lt_of_le_of_lt dist_nonneg hx)
  refine ⟨x, ?_, rfl⟩
  rw [mem_ball, ← hdist x hx p' hpR, hp]
  exact hz

/-- Euclidean splittings at `p` pull back along a ball isometry of radius `R ≥ ε⁻¹`. -/
theorem hasEuclideanSplitting_of_ballIsometry_BDRY1 (φ : X' → X) {p' : X'} {p : X}
    (hp : φ p' = p) {R : ℝ}
    (hdist : ∀ x ∈ ball p' R, ∀ y ∈ ball p' R, dist (φ x) (φ y) = dist x y)
    (honto : ball p R ⊆ φ '' ball p' R) {k : ℕ} {ε : ℝ} (hεR : ε⁻¹ ≤ R)
    (h : HasEuclideanSplitting.{u, v} p k ε) : HasEuclideanSplitting.{u', v} p' k ε := by
  obtain ⟨Y, mY, q, ⟨f⟩⟩ := h
  obtain ⟨hd, ho⟩ := ballIsometry_mono_BDRY1 φ hp hεR hdist honto
  exact ⟨Y, mY, q, ⟨f.pullback_BDRY1 φ hp hd ho⟩⟩

/-- The inverse direction of a ball isometry: `invFunOn φ (B(p', R))` is a ball isometry from
`B(p, R)` onto `B(p', R)`. -/
theorem ballIsometry_symm_BDRY1 [Nonempty X'] (φ : X' → X) {p' : X'} {p : X} (hp : φ p' = p) {R : ℝ}
    (hR : 0 < R)
    (hdist : ∀ x ∈ ball p' R, ∀ y ∈ ball p' R, dist (φ x) (φ y) = dist x y)
    (himage : φ '' ball p' R = ball p R) :
    invFunOn φ (ball p' R) p = p' ∧
      (∀ x ∈ ball p R, ∀ y ∈ ball p R,
        dist (invFunOn φ (ball p' R) x) (invFunOn φ (ball p' R) y) = dist x y) ∧
      ball p' R ⊆ invFunOn φ (ball p' R) '' ball p R := by
  have hinj : InjOn φ (ball p' R) := fun x hx y hy hxy => by
    have h := hdist x hx y hy
    rw [hxy, dist_self] at h
    exact dist_eq_zero.mp h.symm
  have hmem : ∀ z ∈ ball p R, invFunOn φ (ball p' R) z ∈ ball p' R ∧
      φ (invFunOn φ (ball p' R) z) = z := fun z hz => by
    rw [← himage] at hz
    exact ⟨invFunOn_mem hz, invFunOn_eq hz⟩
  have hp'R : p' ∈ ball p' R := mem_ball_self hR
  have hpR : p ∈ ball p R := mem_ball_self hR
  have hleft : ∀ x ∈ ball p' R, invFunOn φ (ball p' R) (φ x) = x := fun x hx =>
    hinj (hmem (φ x) (himage ▸ mem_image_of_mem φ hx)).1 hx
      (hmem (φ x) (himage ▸ mem_image_of_mem φ hx)).2
  refine ⟨hp ▸ hleft p' hp'R, fun x hx y hy => ?_, fun x hx => ?_⟩
  · rw [← hdist _ (hmem x hx).1 _ (hmem y hy).1, (hmem x hx).2, (hmem y hy).2]
  · exact ⟨φ x, himage ▸ mem_image_of_mem φ hx, hleft x hx⟩

/-- **Ball locality of the splitting rank.** If `φ` sends `p'` to `p`, preserves distances on
`B(p', R)` and maps it onto `B(p, R)`, with `R ≥ (β k)⁻¹` for all `k ≤ N`, the splitting ranks
at `p'` and `p` agree. -/
theorem splittingRank_eq_of_ballIsometry_BDRY1 [Nonempty X'] (φ : X' → X) {p' : X'} {p : X}
    (hp : φ p' = p) {R : ℝ} (hR : 0 < R)
    (hdist : ∀ x ∈ ball p' R, ∀ y ∈ ball p' R, dist (φ x) (φ y) = dist x y)
    (himage : φ '' ball p' R = ball p R) (β : ℕ → ℝ) (N : ℕ)
    (hβR : ∀ k ≤ N, (β k)⁻¹ ≤ R) :
    splittingRank.{u', v} p' β N = splittingRank.{u, v} p β N := by
  obtain ⟨hψp, hψd, hψo⟩ := ballIsometry_symm_BDRY1 φ hp hR hdist himage
  have hiff : ∀ k ≤ N, HasEuclideanSplitting.{u', v} p' k (β k) ↔
      HasEuclideanSplitting.{u, v} p k (β k) := fun k hk =>
    ⟨hasEuclideanSplitting_of_ballIsometry_BDRY1 (invFunOn φ (ball p' R)) hψp hψd hψo (hβR k hk),
      hasEuclideanSplitting_of_ballIsometry_BDRY1 φ hp hdist himage.symm.subset (hβR k hk)⟩
  obtain ⟨hkN, hks, hkmax⟩ :=
    (splittingRank_eq_iff p β N (splittingRank.{u, v} p β N)).mp rfl
  exact (splittingRank_eq_iff p' β N _).mpr ⟨hkN, fun h0 => (hiff _ hkN).mpr (hks h0),
    fun j hkj hjN hj => hkmax j hkj hjN ((hiff j hjN).mp hj)⟩

end BallLocality

section Scaled

variable {M : Type u} {M' : Type u'}

/-- Balls of the metric rescaled by `c⁻¹` are the balls of radius `R c`. -/
theorem rescale_inv_ball_BDRY1 (m : MetricSpace M) {c : ℝ} (hc : 0 < c) (p : M) (R : ℝ) :
    @ball M (m.rescale c⁻¹ (inv_pos.mpr hc)).toPseudoMetricSpace p R =
      @ball M m.toPseudoMetricSpace p (R * c) := by
  ext x
  change c⁻¹ * @dist M m.toDist x p < R ↔ @dist M m.toDist x p < R * c
  rw [inv_mul_lt_iff₀ hc, mul_comm]

/-- **Ball locality of the scaled splitting rank** (`N = 3`). If `φ` sends `p'` to `p`, the scales
agree there, and `φ` preserves distances on `B(p', R ρ(p))` and maps it onto `B(p, R ρ(p))`, with
`R ≥ (β k)⁻¹` for `k ≤ 3`, the scaled splitting ranks at `p'` and `p` agree. -/
theorem scaledSplittingRank_eq_of_ballIsometry_BDRY1 (m : MetricSpace M) (m' : MetricSpace M')
    (φ : M' → M) {p' : M'} {p : M} (hp : φ p' = p) (ρ : M → ℝ) (hρ : ∀ x, 0 < ρ x)
    (ρ' : M' → ℝ) (hρ' : ∀ x, 0 < ρ' x) (hρp : ρ' p' = ρ p) (β : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ R)
    (hdist : ∀ x ∈ @ball M' m'.toPseudoMetricSpace p' (R * ρ p),
      ∀ y ∈ @ball M' m'.toPseudoMetricSpace p' (R * ρ p),
        @dist M m.toDist (φ x) (φ y) = @dist M' m'.toDist x y)
    (himage : φ '' @ball M' m'.toPseudoMetricSpace p' (R * ρ p) =
      @ball M m.toPseudoMetricSpace p (R * ρ p)) :
    @scaledSplittingRank.{u', v} M' m' ρ' hρ' β p' = @scaledSplittingRank.{u, v} M m ρ hρ β p := by
  unfold scaledSplittingRank
  let mR := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))
  let mR' := m'.rescale (ρ' p')⁻¹ (inv_pos.mpr (hρ' p'))
  have hN : Nonempty M' := ⟨p'⟩
  have hballR : @ball M mR.toPseudoMetricSpace p R = @ball M m.toPseudoMetricSpace p (R * ρ p) :=
    rescale_inv_ball_BDRY1 m (hρ p) p R
  have hballR' : @ball M' mR'.toPseudoMetricSpace p' R =
      @ball M' m'.toPseudoMetricSpace p' (R * ρ p) := by
    rw [rescale_inv_ball_BDRY1 m' (hρ' p') p' R, hρp]
  refine @splittingRank_eq_of_ballIsometry_BDRY1 M M' mR mR' hN φ p' p hp R hR ?_ ?_ β 3 hβR
  · intro x hx y hy
    rw [hballR'] at hx hy
    change (ρ p)⁻¹ * @dist M m.toDist (φ x) (φ y) = (ρ' p')⁻¹ * @dist M' m'.toDist x y
    rw [hρp, hdist x hx y hy]
  · rw [hballR, hballR', himage]

end Scaled

end GC.MetricGeometry
