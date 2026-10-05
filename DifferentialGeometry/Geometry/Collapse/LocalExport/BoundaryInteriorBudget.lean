import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCut

/-!
# LC88 / BCP04, packet P2 start: the one-tail radius budget (lane BDRY-1, G7)

Review 45 §1.3: every radius actually used by a consumer must be budgeted on one tail through the
BCP04.a estimate `n d/(d + 3) < d/ρ` (BSA06, `bsa06_row_eventually`), i.e. `ρ_n(p) < (D_n(p) + 3)/n`.
* `buffer_lt_of_bcp04a_BDRY1` (arithmetic): `d > 5`, `24 C ≤ n` ⇒ `3 C ρ + 4 < d`;
* `ofReal_buffer_lt_distanceToBoundary_BDRY1`: the same on the carrier at every `p ∈ U₀ = {D > 5}`;
* consumer `image_val_ball_of_budget_BDRY1`: with the completion at cut height `4`, every budgeted
  buffer ball `B_ĝ(q, 3 C ρ(q))`, `q ∈ U₀`, is the actual `g`-ball of `W`.
The budget constants of the frozen T2 (`201·10⁴`, `2·10⁶Δ`, `400V`, `β₁⁻¹`, `b⁻¹`) enter as `C` on the
tail `n ≥ 24 C`; `400V` only after `V` (review 45 §2.5: … → V → late n).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped ENNReal Manifold
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-- **Radius budget, arithmetic form (review 45 §1.3, cut height 4).** From BCP04.a
`n d / (d + 3) < d / ρ` at a point with `d > 5`, every buffer `3 C ρ` with `24 C ≤ n` stays below
`d − 4`. -/
theorem buffer_lt_of_bcp04a_BDRY1 {d ρ n C : ℝ} (hd : 5 < d) (hρ : 0 < ρ)
    (hn : 24 * C ≤ n) (hbcp : n * d / (d + 3) < d / ρ) : 3 * C * ρ + 4 < d := by
  have hd0 : 0 < d := by linarith
  have hd3 : 0 < d + 3 := by linarith
  have hnρ : n * ρ < d + 3 := by
    rw [div_lt_div_iff₀ hd3 hρ] at hbcp
    nlinarith
  have h24 : 24 * C * ρ ≤ n * ρ := mul_le_mul_of_nonneg_right hn hρ.le
  nlinarith

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- **Radius budget on the carrier.** If `ρ > 0` satisfies BCP04.a at every point of positive
boundary distance (the BSA06 tail, `bsa06_row_eventually`), then for every `C ≥ 0` with `24 C ≤ n`
and every `p` with `D(p) > 5`: `3 C ρ(p) + 4 < D(p)`. Hence every fixed buffer `C ρ` at the rank
region `U₀ = {D > 5}` is protected by the completion at cut height `4` (ball identity and pairwise
distances, `BoundaryInteriorCut.lean`). -/
theorem ofReal_buffer_lt_distanceToBoundary_BDRY1 (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p)
    {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {C : ℝ} (hC : 0 ≤ C) (hn : 24 * C ≤ n) (p : W.Carrier)
    (hp : ENNReal.ofReal 5 < distanceToBoundary W g p) :
    ENNReal.ofReal (3 * C * ρ p + 4) < distanceToBoundary W g p := by
  have hpos : 0 < distanceToBoundary W g p := lt_of_le_of_lt zero_le hp
  have h := hbcp p hpos
  have htop : distanceToBoundary W g p ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    simp at h
  have hd : 5 < (distanceToBoundary W g p).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by norm_num) htop).mp hp
  rw [← ENNReal.ofReal_toReal htop]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by nlinarith [hρ p])).mpr
    (buffer_lt_of_bcp04a_BDRY1 hd (hρ p) hn h)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- **Consumer: budgeted buffers are actual balls.** For `ĝ = g°` on `{D ≥ 4}` and `ρ` with
BCP04.a, every buffer ball `B_ĝ(q, 3 C ρ(q))` (`C ≥ 0`, `24 C ≤ n`) at `q ∈ U₀ = {D > 5}` is the
`g`-ball of `W` of the same radius. -/
theorem image_val_ball_of_budget_BDRY1 [ConnectedSpace W.Carrier]
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {C : ℝ} (hC : 0 ≤ C) (hn : 24 * C ≤ n) (q : W.pieceInterior ⊤)
    (hq : ENNReal.ofReal 5 < distanceToBoundary W g q) :
    Subtype.val '' riemannianBallOf ĝ q (3 * C * ρ q) = riemannianBallOf g q.val (3 * C * ρ q) :=
  image_val_riemannianBallOf_cut_BDRY1 W g ĝ (by norm_num) heq q
    (mul_nonneg (mul_nonneg (by norm_num) hC) (hρ q).le)
    (ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp hC hn q hq).le

end DifferentialGeometry.Geometry.Collapse
