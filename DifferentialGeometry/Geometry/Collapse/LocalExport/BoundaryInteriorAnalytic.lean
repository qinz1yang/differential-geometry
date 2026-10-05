import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorBudget

/-!
# LC88 / BCP04, packet P2: the BSA06 → complete-source analytic adapter (lane BDRY-1, G8)

Review 45 §1.6 order: boundary premises ⟹ BSA04/BSA06 data on the ORIGINAL carrier ⟹ local inputs
of the completion. With the completion at cut height `4` and the BCP04.a budget (G7):
* `normalizedBall_budget_BDRY1`: at `q ∈ U₀ = {D > 5}` the normalized balls of radius `R ≤ n/8` of
  `ρ(q)⁻² ĝ` are the normalized balls of `ρ(q)⁻² g` on `W` and lie in `{D > 4}`;
* `completion_normalized_data_BDRY1`: every sectional lower bound and curvature-derivative bound of
  `ρ(q)⁻² g` on such a ball (BSA06's clauses) holds verbatim for `ρ(q)⁻² ĝ`, and the normalized
  ball volumes agree — the LPA01 data of the complete source `(W°, ĝ)` at eligible centres, in the
  per-fixed-radius form (`R ≤ n/8`) that the pointed-sequence inputs use (review 45 §1.5).
The scale is the original `ρ` of `W`; no curvature radius is transferred.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold
open scoped ENNReal Manifold
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

variable (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
  (g : SmoothRiemannianMetric W.model W.Carrier)
  (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- **Normalized balls under the budget.** With the completion at cut height `4` and BCP04.a, at
`q ∈ U₀ = {D > 5}` every normalized ball of radius `R ≤ n/8` of `ρ(q)⁻² ĝ` is the normalized ball of
`ρ(q)⁻² g` on `W`, and it lies in `{D > 4}`. -/
theorem normalizedBall_budget_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 5 < distanceToBoundary W g q)
    {R : ℝ} (hR : 0 ≤ R) (hRn : 8 * R ≤ n) :
    Subtype.val '' riemannianBallOf (normalizedCenterMetric ĝ (ρ q) (hρ q)) q R =
        riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R ∧
      riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R ⊆
        {x | ENNReal.ofReal 4 < distanceToBoundary W g x} := by
  have hC : (0 : ℝ) ≤ R / 3 := by positivity
  have hn : 24 * (R / 3) ≤ n := by linarith
  have hbud := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp hC hn q hq
  have hr : 3 * (R / 3) * ρ q = R * ρ q := by ring
  rw [hr] at hbud
  have himg := image_val_ball_of_budget_BDRY1 W g ĝ heq ρ hρ hbcp hC hn q hq
  rw [hr] at himg
  rw [normalizedCenterMetric_ball, normalizedCenterMetric_ball]
  exact ⟨himg, riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g
    (mul_nonneg hR (hρ q).le) (by norm_num) hbud.le⟩

/-- **The BSA06 → complete-source analytic adapter (P2).** At `q ∈ U₀`, with the completion at
cut height `4` and BCP04.a: on the normalized ball of radius `R ≤ n/8` of `ρ(q)⁻² ĝ`, every
sectional lower bound and every curvature-derivative bound of `ρ(q)⁻² g` on the corresponding ball
of `W` holds verbatim, and the normalized ball volumes agree. Applied to BSA06's clauses
(`bsa06_row_eventually`) this gives the LPA01 data of `(W°, ĝ)` at every eligible centre. -/
theorem completion_normalized_data_BDRY1
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ}
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (q : W.pieceInterior ⊤) (hq : ENNReal.ofReal 5 < distanceToBoundary W g q)
    {R : ℝ} (hR : 0 ≤ R) (hRn : 8 * R ≤ n) {κ : ℝ}
    (hsec : ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R,
      SectionalBoundedBelowAt (normalizedCenterMetric g (ρ q) (hρ q)) y κ)
    {K : ℕ} {bound : ℝ}
    (hder : ∀ k ≤ K, ∀ y ∈ riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R,
      curvatureDerivativeNorm (normalizedCenterMetric g (ρ q) (hρ q)) k y ≤ bound) :
    (∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ (ρ q) (hρ q)) q R,
      SectionalBoundedBelowAt (normalizedCenterMetric ĝ (ρ q) (hρ q)) y κ) ∧
    (∀ k ≤ K, ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ (ρ q) (hρ q)) q R,
      curvatureDerivativeNorm (normalizedCenterMetric ĝ (ρ q) (hρ q)) k y ≤ bound) ∧
    ballVolume (normalizedCenterMetric ĝ (ρ q) (hρ q)) q R =
      ballVolume (normalizedCenterMetric g (ρ q) (hρ q)) q.val R := by
  obtain ⟨himg, hsub⟩ := normalizedBall_budget_BDRY1 W g ĝ heq ρ hρ hbcp q hq hR hRn
  have hdata := completion_cut_local_data_BDRY1 W g ĝ (by norm_num) heq (hρ q)
  have hmem : ∀ y ∈ riemannianBallOf (normalizedCenterMetric ĝ (ρ q) (hρ q)) q R,
      y.val ∈ riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R ∧
        ENNReal.ofReal 4 < distanceToBoundary W g y := fun y hy => by
    have hy' : y.val ∈ riemannianBallOf (normalizedCenterMetric g (ρ q) (hρ q)) q.val R :=
      himg ▸ ⟨y, hy, rfl⟩
    exact ⟨hy', hsub hy'⟩
  refine ⟨fun y hy => ?_, fun k hk y hy => ?_, ?_⟩
  · obtain ⟨hy', hd⟩ := hmem y hy
    exact ((hdata.1 y hd κ).2).mpr (hsec _ hy')
  · obtain ⟨hy', hd⟩ := hmem y hy
    rw [((hdata.2.1 y hd k).2)]
    exact hder k hk _ hy'
  · have hC : (0 : ℝ) ≤ R / 3 := by positivity
    have hbud := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp hC (by linarith) q hq
    have hr : 3 * (R / 3) * ρ q = R * ρ q := by ring
    rw [hr] at hbud
    exact (hdata.2.2 q hR hbud.le).2

end DifferentialGeometry.Geometry.Collapse
