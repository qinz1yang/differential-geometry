import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# LFR10, containment clause: almost isometric open maps cover a smaller target ball

Blueprint 207A, LFR10 (`prop:collapse-actual-buffered-embeddings`, A:25488–25555), second
assertion: for comparison maps `f i : N → M i` with `f i p = p i` and pointed distortion tending
to zero, eventually `B_{M i}(p i, r) ⊆ f i (B_N(p, R))` for `r < R`.

The blueprint lifts minimizing geodesics using the injectivity proved first. The argument here
needs no injectivity: along an almost minimizing curve `c` from `p i` to a point of the small
ball, the set of parameters whose point lies in `f i '' B_N(p,R)` is open (the image is open) and
closed (by the distortion bound it equals the preimage of the compact image of a closed ball), so
it is the whole unit interval. The inputs are metric abstractions of the row's hypotheses:
`N` proper (complete Riemannian), `f i` continuous with open image of the ball (local
diffeomorphism), distortion on the ball, and almost minimizing curves in the targets (the
length-space input `hcurves` of W3-F1, discharged for Riemannian targets by
`exists_arbitrarily_short_riemannian_curve`).
-/

set_option autoImplicit false

open Set Filter Metric

namespace GC.MetricGeometry

/-- Every point of a curve from `a` whose variation is below `r` lies within distance `r` of
`a`. -/
theorem dist_lt_of_eVariationOn_lt {Z : Type*} [MetricSpace Z] {c : unitInterval → Z} {a : Z}
    {r : ℝ} (h0 : c 0 = a) (hvar : eVariationOn c univ < ENNReal.ofReal r)
    (t : unitInterval) : dist a (c t) < r := by
  have hle : edist a (c t) ≤ eVariationOn c univ := by
    rw [← h0]
    exact eVariationOn.edist_le c (mem_univ _) (mem_univ _)
  have hlt := hle.trans_lt hvar
  rw [edist_dist] at hlt
  exact ((ENNReal.ofReal_lt_ofReal_iff').1 hlt).1

/-- **LFR10, containment, one map.** A map continuous on `B(p,R)` with open image of that ball,
whose distortion against the basepoint is below `R - r`, covers `B(f p, r)` as soon as every
point of that ball is reached by almost minimizing curves from `f p`. -/
theorem ball_subset_image_of_basepoint_distortion {N M : Type*} [MetricSpace N] [ProperSpace N]
    [MetricSpace M] (f : N → M) (p : N) {r R : ℝ} (hR : 0 < R)
    (hcont : ContinuousOn f (ball p R)) (hopen : IsOpen (f '' ball p R))
    (hdist : ∀ x ∈ ball p R, dist x p < dist (f p) (f x) + (R - r))
    (hcurves : ∀ y : M, ∀ η : ℝ, 0 < η → ∃ c : unitInterval → M, Continuous c ∧ c 0 = f p ∧
      c 1 = y ∧ eVariationOn c univ < ENNReal.ofReal (dist (f p) y + η)) :
    ball (f p) r ⊆ f '' ball p R := by
  intro y hy
  have hy' : dist (f p) y < r := by rw [dist_comm]; exact hy
  obtain ⟨c, hc, h0, h1, hvar⟩ := hcurves y (r - dist (f p) y) (by linarith)
  rw [add_sub_cancel] at hvar
  have hin : ∀ t, dist (f p) (c t) < r := dist_lt_of_eVariationOn_lt h0 hvar
  obtain ⟨t₀, -, ht₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
    ((continuous_const.dist hc).continuousOn : ContinuousOn (fun t => dist (f p) (c t)) univ)
  set m : ℝ := dist (f p) (c t₀) with hm
  have hmr : m < r := hin t₀
  have hmax : ∀ t, dist (f p) (c t) ≤ m := fun t => ht₀ (mem_univ t)
  have hsub : closedBall p (m + (R - r)) ⊆ ball p R := closedBall_subset_ball (by linarith)
  have hclosedImg : IsClosed (f '' closedBall p (m + (R - r))) :=
    ((isCompact_closedBall p _).image_of_continuousOn (hcont.mono hsub)).isClosed
  have hEq : c ⁻¹' (f '' ball p R) = c ⁻¹' (f '' closedBall p (m + (R - r))) := by
    ext t
    simp only [mem_preimage, mem_image]
    constructor
    · rintro ⟨x, hx, hxt⟩
      refine ⟨x, ?_, hxt⟩
      have h := hdist x hx
      rw [hxt] at h
      rw [mem_closedBall]
      linarith [hmax t]
    · rintro ⟨x, hx, hxt⟩
      exact ⟨x, hsub hx, hxt⟩
  have hclopen : IsClopen (c ⁻¹' (f '' ball p R)) :=
    ⟨hEq ▸ hclosedImg.preimage hc, hopen.preimage hc⟩
  have h0mem : (0 : unitInterval) ∈ c ⁻¹' (f '' ball p R) := by
    rw [mem_preimage, h0]
    exact mem_image_of_mem f (mem_ball_self hR)
  have huniv := hclopen.eq_univ ⟨0, h0mem⟩
  have h1mem : (1 : unitInterval) ∈ c ⁻¹' (f '' ball p R) := by rw [huniv]; exact mem_univ _
  rw [mem_preimage, h1] at h1mem
  exact h1mem

/-- **LFR10, containment clause (kernel).** Maps `f i : N → M i` from a proper space, pointed at
`f i p = q i`, eventually continuous on `B(p,R)` with open image of that ball, and with distortion
on `B(p,R)` tending to zero, into length-type targets: for every `r < R`, eventually
`B(q i, r) ⊆ f i '' B(p, R)`. No injectivity and no dense-image premise is used. -/
theorem eventually_ball_subset_image_of_distortion {N : Type*} [MetricSpace N] [ProperSpace N]
    {M : ℕ → Type*} [∀ i, MetricSpace (M i)] (f : ∀ i, N → M i) (p : N) (q : ∀ i, M i)
    (hp : ∀ i, f i p = q i) {R : ℝ}
    (hcont : ∀ᶠ i in atTop, ContinuousOn (f i) (ball p R))
    (hopen : ∀ᶠ i in atTop, IsOpen (f i '' ball p R))
    (hdist : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball p R, ∀ y ∈ ball p R,
      |dist (f i x) (f i y) - dist x y| < ε)
    (hcurves : ∀ i, ∀ a b : M i, ∀ η : ℝ, 0 < η → ∃ c : unitInterval → M i, Continuous c ∧
      c 0 = a ∧ c 1 = b ∧ eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    {r : ℝ} (hr : r < R) : ∀ᶠ i in atTop, ball (q i) r ⊆ f i '' ball p R := by
  rcases le_or_gt R 0 with hR | hR
  · refine Eventually.of_forall fun i y hy => ?_
    exact absurd (lt_of_le_of_lt dist_nonneg (mem_ball.1 hy)) (by linarith)
  filter_upwards [hcont, hopen, hdist (R - r) (by linarith)] with i hci hoi hdi
  rw [← hp i]
  refine ball_subset_image_of_basepoint_distortion (f i) p hR hci hoi (fun x hx => ?_)
    (fun y η hη => hcurves i (f i p) y η hη)
  have h := hdi p (mem_ball_self hR) x hx
  rw [dist_comm p x] at h
  linarith [(abs_lt.1 h).1]

end GC.MetricGeometry
