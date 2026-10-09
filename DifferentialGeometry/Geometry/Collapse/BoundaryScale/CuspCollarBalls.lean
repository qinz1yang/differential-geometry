import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit

/-!
# Balls of a nearly cuspidal collar stay in the collar (statement G, BSA01 (ii), (vi))

For a cusp embedding `e : CuspEmbedding W g K δ X`, `z` the height and `m = √(1 - δ)`
(blueprint 207B, BSA01, `B:7591–7672`; BCP01 proof `B:8159–8162`):

* `CuspEmbedding.riemannianBallOf_subset_image_height_window`: the intrinsic ball `B(e p, r)` lies
  in the collar band `z(p) - r/m < z < z(p) + r/m` whenever `z(p) + r/m < 100` (first exit
  through either level of the band);
* `CuspEmbedding.riemannianBallOf_subset_image_window_of_le_hundredth`,
  `CuspEmbedding.riemannianBallOf_subset_image_height_lt`: for `δ ≤ 1/100`, `z(p) ≤ 96` and
  `r ≤ 1` the WHOLE ball lies in `e(T² × [0, 98))`, inside a height interval of length `2.02 r`
  (BSA01 (ii) with `96` in place of `95`, which is also the `z ≤ 96` version used by BCP01).

BSA01 (iii) (`d(p, ∂W) ≤ 10` puts `p` in a collar at height `< 11`) is
`NearlyCuspidalBoundary.exists_collar_height_lt_eleven` (`CuspCollarLocalization.lean`).

The statements hold for all curves of the distance (the first exit is proved for every `C¹`
competitor), not only for minimizing ones.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- For `δ ≤ 1/100`, `1/√(1 - δ) ≤ 1.01`. -/
theorem inv_sqrt_one_sub_le_of_le_hundredth (hδ : δ ≤ 1 / 100) :
    (Real.sqrt (1 - δ))⁻¹ ≤ 101 / 100 := by
  have hs : (100 / 101 : ℝ) ≤ Real.sqrt (1 - δ) := Real.le_sqrt_of_sq_le (by nlinarith)
  rw [inv_le_comm₀ (Real.sqrt_pos.mpr (by linarith)) (by norm_num)]
  calc ((101 / 100 : ℝ))⁻¹ = 100 / 101 := by norm_num
    _ ≤ _ := hs

/-- For `δ ≤ 1/100` and `0 ≤ r`, `r / √(1 - δ) ≤ 1.01 r`. -/
theorem div_sqrt_one_sub_le_of_le_hundredth (hδ : δ ≤ 1 / 100) {r : ℝ} (hr : 0 ≤ r) :
    r / Real.sqrt (1 - δ) ≤ 101 / 100 * r := by
  rw [div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (inv_sqrt_one_sub_le_of_le_hundredth hδ) hr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Height window.** The intrinsic ball `B(e p, r)` lies in the collar band
`z(p) - r/m < z < z(p) + r/m`, `m = √(1 - δ)`, provided `z(p) + r/m < 100`. -/
theorem CuspEmbedding.riemannianBallOf_subset_image_height_window (e : CuspEmbedding W g K δ X)
    (hδ : δ < 1) {p : CuspHalfSpace} {r : ℝ}
    (hp : p.2.val 0 + r / Real.sqrt (1 - δ) < cuspDepth) :
    riemannianBallOf g (e.toFun p) r ⊆
      e.toFun '' {q : CuspHalfSpace | p.2.val 0 - r / Real.sqrt (1 - δ) < q.2.val 0 ∧
        q.2.val 0 < p.2.val 0 + r / Real.sqrt (1 - δ)} := by
  intro y hy
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  have hy' : Manifold.riemannianEDist W.model (e.toFun p) y < ENNReal.ofReal r := hy
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hy')
  set m := Real.sqrt (1 - δ) with hm
  have hmpos : 0 < m := Real.sqrt_pos.mpr (by linarith)
  have hrm : 0 < r / m := div_pos hr hmpos
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy'
  by_contra hnot
  obtain ⟨q, -, hqside, hq⟩ := e.exists_exit_le_pathELength hγ hp
    (show p.2.val 0 - r / m < p.2.val 0 by linarith)
    (show p.2.val 0 < p.2.val 0 + r / m by linarith) hγ0 (by rw [hγ1]; exact hnot)
  have habs : |q.2.val 0 - p.2.val 0| = r / m := by
    rcases hqside with h | h
    · rw [h, show p.2.val 0 - r / m - p.2.val 0 = -(r / m) by ring, abs_neg, abs_of_pos hrm]
    · rw [h, show p.2.val 0 + r / m - p.2.val 0 = r / m by ring, abs_of_pos hrm]
  rw [habs, mul_div_cancel₀ _ hmpos.ne'] at hq
  exact absurd (hq.trans_lt hlen) (lt_irrefl _)

/-- BSA01 (ii)/(vi), height form: for `δ ≤ 1/100`, `z(p) ≤ 96` and `r ≤ 1`, the ball `B(e p, r)`
lies in the band `|z - z(p)| < 1.01 r`, `z < 98` (a height interval of length `2.02 r`). -/
theorem CuspEmbedding.riemannianBallOf_subset_image_window_of_le_hundredth
    (e : CuspEmbedding W g K δ X) (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96)
    {r : ℝ} (hr : r ≤ 1) :
    riemannianBallOf g (e.toFun p) r ⊆
      e.toFun '' {q : CuspHalfSpace | |q.2.val 0 - p.2.val 0| < 101 / 100 * r ∧
        q.2.val 0 < 98} := by
  rcases le_or_gt r 0 with hr0 | hr0
  · intro y hy
    have hy' : riemannianEDistOf g (e.toFun p) y < ENNReal.ofReal r := hy
    rw [ENNReal.ofReal_of_nonpos hr0] at hy'
    exact absurd hy' (not_lt.mpr zero_le)
  have hw := div_sqrt_one_sub_le_of_le_hundredth hδ hr0.le
  have hsub := e.riemannianBallOf_subset_image_height_window (by linarith) (p := p) (r := r)
    (by change _ < (100 : ℝ); linarith)
  refine hsub.trans (image_mono fun q hq => ?_)
  obtain ⟨h1, h2⟩ := hq
  refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, by linarith⟩

/-- BSA01 (ii)/(vi), the ball clause: for `δ ≤ 1/100`, `z(p) ≤ 96` and `r ≤ 1`, the WHOLE
intrinsic ball `B(e p, r)` lies in the collar `e(T² × [0, 98))`. -/
theorem CuspEmbedding.riemannianBallOf_subset_image_height_lt (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 1 / 100) {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 96) {r : ℝ} (hr : r ≤ 1) :
    riemannianBallOf g (e.toFun p) r ⊆ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 98} :=
  (e.riemannianBallOf_subset_image_window_of_le_hundredth hδ hp hr).trans
    (image_mono fun _ hq => hq.2)

end DifferentialGeometry.Geometry.Collapse
