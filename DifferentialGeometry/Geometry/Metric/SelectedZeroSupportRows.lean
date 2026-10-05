import DifferentialGeometry.Geometry.Metric.RadialSupportBuffer
import DifferentialGeometry.Topology.MetricSpace.ZeroSetSmallCoreCover
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# FC09 and FC13 on the selected zero balls (LC62 / LC64)

Blueprint `master207B.tex`: FC09 (`lem:fibration-zero-support`, lines 534–579) and FC13
(`lem:fibration-zero-shell`, lines 784–825). Both rows retain "the LC62 comparison" of the selected
zero balls. Here the comparison is PRODUCED, not assumed:

* `fc09_of_maximal_doubling`, `fc13_of_maximal_doubling`: the rows for zero balls whose centres
  are LC62 maximal doubling candidates (the defining property of LC62's set `V`), with
  `T ρ ≤ r`; the local ratio `R_j / ρ(q) ≥ T / 20` on the closed ten-radius ball comes from
  `Metric.radius_le_of_maximal_doubling_ball`.
* `fc09_fc13_selected_zero_balls`: on a compact metric space (an actual compact Riemannian
  manifold with its distance), LC64's selection `Metric.exists_zero_set_small_core_cover` gives a
  finite family of maximal doubling balls, pairwise disjoint, meeting `Z`, whose five-radius balls
  cover `Z`, such that for EVERY family of closed supports FC09's conclusion holds (at most one
  support meets `D = B(p, L ρ(p))`) and FC13's conclusion holds (`R/ρ(p) ≥ T/20` and
  `D ⊆ {3/20 ≤ d(z,·)/R ≤ 19/20}`) for every radial function with the row's value error.
* `fc13_contMDiffOn_of_shell`: FC13's "in particular" clause: a radial function smooth on the open
  shell `{1/10 < d(z,·)/R < 10}` is smooth on `D`.

Kernels: Codex X81 (`GC.MetricGeometry.subsingleton_zero_supports_meeting_ball`,
`GC.MetricGeometry.radial_support_test_ball_buffer`).
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

/-- LC62's local ratio from maximality: on the closed ten-radius ball of a maximal doubling centre
`v`, `T / 20 ≤ r v / ρ q`, provided `T ρ ≤ r`. -/
theorem lc62_ratio_of_maximal_doubling (Z : Set X) (r ρ : X → ℝ) (hρpos : ∀ x, 0 < ρ x) {T : ℝ}
    (hT : 0 < T) (hlower : ∀ q, T * ρ q ≤ r q) {v : X} (hv : (ball v (r v) ∩ Z).Nonempty)
    (hmax : ∀ q, (ball q (r q) ∩ Z).Nonempty → ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v)
    {q : X} (hq : dist v q ≤ 10 * r v) : T / 20 ≤ r v / ρ q := by
  have hrv : 0 < r v := (mul_pos hT (hρpos v)).trans_le (hlower v)
  have h20 := Metric.radius_le_of_maximal_doubling_ball r Z hv hrv hmax hq
  rw [le_div_iff₀ (hρpos q)]
  linarith [hlower q]

/-- FC09 for supports of zero balls centred at LC62 maximal doubling candidates. -/
theorem fc09_of_maximal_doubling {ι : Type*} (Z : Set X) (r ρ : X → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {T : ℝ} (hlower : ∀ q, T * ρ q ≤ r q)
    (z : ι → X) (hZ : ∀ i, (ball (z i) (r (z i)) ∩ Z).Nonempty)
    (hmax : ∀ i q, (ball q (r q) ∩ Z).Nonempty → ball (z i) (r (z i)) ⊆ ball q (r q) →
      r q ≤ 2 * r (z i))
    (S : ι → Set X) {p : X} {L θ : ℝ} (hL : 0 < L) (hθ : θ < 1) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 40 * L < T) (hTθ : 40 * L / (1 - θ) < T)
    (hsupport : ∀ i, S i ⊆ closedBall (z i) (θ * r (z i)))
    (hdisjoint : Pairwise fun i j => Disjoint (ball (z i) (r (z i))) (ball (z j) (r (z j)))) :
    {i | (S i ∩ ball p (L * ρ p)).Nonempty}.Subsingleton := by
  have hT0 : 0 < T := by linarith
  exact subsingleton_zero_supports_meeting_ball hρ hρpos z (fun i => r (z i)) S hL hθ hΛ hT hTθ
    (fun i => hlower (z i))
    (fun i _ hq => lc62_ratio_of_maximal_doubling Z r ρ hρpos hT0 hlower (hZ i) (hmax i) hq)
    hsupport hdisjoint

/-- FC13 for a zero ball centred at an LC62 maximal doubling candidate. -/
theorem fc13_of_maximal_doubling (Z : Set X) (r ρ η : X → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {T : ℝ} (hlower : ∀ q, T * ρ q ≤ r q)
    {z : X} (hZ : (ball z (r z) ∩ Z).Nonempty)
    (hmax : ∀ q, (ball q (r q) ∩ Z).Nonempty → ball z (r z) ⊆ ball q (r q) → r q ≤ 2 * r z)
    {p : X} {L e : ℝ} (hL : 0 < L) (hΛ : L * Λ ≤ 1 / 4) (hT : 1600 * L ≤ T) (he : e < 1 / 40)
    {S : Set X} (herror : ∀ x ∈ S, |η x - dist z x / r z| < e)
    (hvalue : ∀ x ∈ S, η x ∈ Icc (1 / 5) (9 / 10)) (hmeet : (S ∩ ball p (L * ρ p)).Nonempty) :
    T / 20 ≤ r z / ρ p ∧ ∀ x ∈ ball p (L * ρ p), dist z x / r z ∈ Icc (3 / 20) (19 / 20) := by
  have hT0 : 0 < T := by linarith
  exact radial_support_test_ball_buffer hρ (hρpos p) (hρpos z) hL hΛ hT (hlower z) he
    (fun hq => lc62_ratio_of_maximal_doubling Z r ρ hρpos hT0 hlower hZ hmax hq) herror hvalue
    hmeet

/-- FC09 and FC13 on LC64's actual selection of maximal doubling zero balls in a compact metric
space: the selection is finite, pairwise disjoint, meets `Z` and its five-radius balls cover `Z`;
for every family of closed supports at most one meets `B(p, L ρ p)` (FC09), and every meeting
support with the row's radial value error has the FC13 ratio and shell buffer. -/
theorem fc09_fc13_selected_zero_balls [CompactSpace X] (Z : Set X) (r ρ : X → ℝ) {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x) {T U : ℝ} (hT : 0 < T) (hTU : T ≤ U)
    (hlower : ∀ q, T * ρ q ≤ r q) (hupper : ∀ q, r q ≤ U * ρ q) :
    ∃ J : Set X, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ J, (ball i (r i) ∩ Z).Nonempty) ∧ Z ⊆ ⋃ i ∈ J, ball i (5 * r i) ∧
      (∀ (S : X → Set X) (p : X) (L θ : ℝ), 0 < L → θ < 1 → L * Λ ≤ 1 / 4 → 40 * L < T →
        40 * L / (1 - θ) < T → (∀ i ∈ J, S i ⊆ closedBall i (θ * r i)) →
        {i | i ∈ J ∧ (S i ∩ ball p (L * ρ p)).Nonempty}.Subsingleton) ∧
      (∀ (S : X → Set X) (η : X → X → ℝ) (p : X) (L e : ℝ), 0 < L → L * Λ ≤ 1 / 4 →
        1600 * L ≤ T → e < 1 / 40 → ∀ i ∈ J, (∀ x ∈ S i, |η i x - dist i x / r i| < e) →
        (∀ x ∈ S i, η i x ∈ Icc (1 / 5) (9 / 10)) → (S i ∩ ball p (L * ρ p)).Nonempty →
        T / 20 ≤ r i / ρ p ∧ ∀ x ∈ ball p (L * ρ p), dist i x / r i ∈ Icc (3 / 20) (19 / 20)) := by
  obtain ⟨J, hfin, hmaxJ, hdisj, -, hcover, -⟩ :=
    Metric.exists_zero_set_small_core_cover Z r ρ hρ.continuous hρpos hT hTU hlower hupper
  refine ⟨J, hfin, hdisj, fun i hi => (hmaxJ i hi).1, hcover, ?_, ?_⟩
  · intro S p L θ hL hθ hΛ hT40 hTθ hsupport
    have hsub := fc09_of_maximal_doubling Z r ρ hρ hρpos hlower (fun i : J => (i : X))
      (fun i => (hmaxJ i i.2).1) (fun i => (hmaxJ i i.2).2) (fun i => S i) (p := p) hL hθ hΛ hT40
      hTθ
      (fun i => hsupport i i.2)
      (fun i j hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h)))
    intro a ha b hb
    have := @hsub ⟨a, ha.1⟩ ha.2 ⟨b, hb.1⟩ hb.2
    exact congrArg Subtype.val this
  · intro S η p L e hL hΛ hT1600 he i hi herror hvalue hmeet
    exact fc13_of_maximal_doubling Z r ρ (η i) hρ hρpos hlower (hmaxJ i hi).1 (hmaxJ i hi).2 hL
      hΛ hT1600 he herror hvalue hmeet

/-- FC13's "in particular" clause: a radial function smooth on the open shell
`{1/10 < d(z,·)/R < 10}` is smooth on `D = B(p, L ρ p)` once `D` lies in the closed shell
`[3/20, 19/20]`. -/
theorem fc13_contMDiffOn_of_shell {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners 𝕜 E H} [ChartedSpace H X] {n : WithTop ℕ∞} {z : X} {R : ℝ}
    {f : X → 𝕜} {D : Set X} (hD : ∀ x ∈ D, dist z x / R ∈ Icc (3 / 20) (19 / 20))
    (hsmooth : ContMDiffOn I 𝓘(𝕜, 𝕜) n f {x | 1 / 10 < dist z x / R ∧ dist z x / R < 10}) :
    ContMDiffOn I 𝓘(𝕜, 𝕜) n f D := by
  refine hsmooth.mono fun x hx => ?_
  have h := hD x hx
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end GC.MetricGeometry
