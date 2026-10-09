import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorTransfer
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorRanks

/-!
# LC88 / BCP04, packet P1: the interior completion at a general cut height (lane BDRY-1, G5)

Review 45 (binding dispositions 2026-10-05) asks for the completion at a general cut height `a` and
uses `a = 4`, so that the rank region `U₀ = {D > 5}` keeps a fixed physical margin. NEW theorems (the
delivered `a = 5` forms in `BoundaryInteriorCompletion.lean` / `BoundaryInteriorTransfer.lean` stay):

* T1′ `exists_interior_completion_cut_BDRY1`: complete `ĝ` on `W°` with `ĝ = g°` on an OPEN set
  `O ⊇ {D ≥ a}` and `ĝ ≥ g°`;
* for any `ĝ = g°` on `{D ≥ a}`: the inverse inclusion is isometric on `regionCut_BDRY1 = {D > a}`
  (`completion_isometric_cut_BDRY1`); balls `val '' B_ĝ(q, r) = B_g(q, r)` for `r + a ≤ D(q)`
  (`image_val_riemannianBallOf_cut_BDRY1`); distances on the quarter balls
  (`riemannianEDistOf_cut_eq_BDRY1`); scaled splitting ranks for the ORIGINAL scale `ρ` at
  `4 R ρ + a ≤ D` (`scaledSplittingRank_cut_eq_BDRY1`); sectional bounds, curvature derivative norms
  and ball volumes, also for the normalized metrics (`completion_cut_local_data_BDRY1`);
* consumer `exists_interior_completion_four_ranks_BDRY1` (`a = 4`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u v

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

section Cut

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- **T1′ (review 45 §2.1): the interior completion at a general cut height `a > 0`.** One complete
metric `ĝ` on `W°` (interior atlas) with `ĝ = g°` on an OPEN set `O ⊇ {D ≥ a}` and `ĝ ≥ g°`. -/
theorem exists_interior_completion_cut_BDRY1 {a : ℝ} (ha : 0 < a) :
    ∃ ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤), ∃ O : Set (W.pieceInterior ⊤),
      RiemannianMetricComplete (I := 𝓡 3) ĝ ∧ IsOpen O ∧
      {x : W.pieceInterior ⊤ | ENNReal.ofReal a ≤ distanceToBoundary W g x} ⊆ O ∧
      (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v := by
  obtain ⟨ĝ, O, hcomplete, hO, hKO, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (pieceInteriorMetric W g ⊤)
      (isCompact_le_distanceToBoundary_BDRY1 W g ha)
  exact ⟨ĝ, O, hcomplete, hO, hKO, heq, hle⟩

/-- The region `{D > a}` as an open set. -/
def regionCut_BDRY1 (a : ℝ) : TopologicalSpace.Opens W.Carrier :=
  ⟨{x | ENNReal.ofReal a < distanceToBoundary W g x}, isOpen_lt_distanceToBoundary_BDRY1 W g a⟩

variable [ConnectedSpace W.Carrier] (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- For `ĝ = g°` on `{D ≥ a}`, the inverse inclusion is isometric from `(g, ĝ)` on
`{D > a}`, which lies in its source. -/
theorem completion_isometric_cut_BDRY1 {a : ℝ}
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) :
    have := connectedSpace_pieceInterior_top_BDRY1 W
    ((regionCut_BDRY1 W g a : Set W.Carrier) ⊆ (interiorInclusion_BDRY1 W).symm.source) ∧
    ∀ x ∈ (regionCut_BDRY1 W g a : Set W.Carrier), ∀ v w : TangentSpace W.model x,
      g.inner x v w = ĝ.inner ((interiorInclusion_BDRY1 W).symm x)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x v)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x w) := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  have hint : ∀ x ∈ (regionCut_BDRY1 W g a : Set W.Carrier), x ∈ W.model.interior W.Carrier :=
    fun x hx => mem_interior_of_distanceToBoundary_pos_BDRY1 W g
      (lt_of_le_of_lt zero_le (show ENNReal.ofReal a < distanceToBoundary W g x from hx))
  refine ⟨fun x hx => mem_interiorInclusion_target_BDRY1 W (hint x hx), fun x hx v w => ?_⟩
  have hsrc : x ∈ (interiorInclusion_BDRY1 W).symm.source :=
    mem_interiorInclusion_target_BDRY1 W (hint x hx)
  have hd : ENNReal.ofReal a ≤ distanceToBoundary W g ((interiorInclusion_BDRY1 W).symm x) := by
    rw [val_interiorInclusion_symm_BDRY1 W (hint x hx)]
    exact (show ENNReal.ofReal a < distanceToBoundary W g x from hx).le
  rw [heq _ hd]
  exact interiorInclusion_symm_isometric_BDRY1 W g x hsrc v w

/-- **Balls at cut height `a`.** If `r + a ≤ D(q)` (`r, a ≥ 0`), the `ĝ`-ball of radius `r` about
`q ∈ W°` is the `g`-ball of `W`. -/
theorem image_val_riemannianBallOf_cut_BDRY1 {a : ℝ} (ha : 0 ≤ a)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) {r : ℝ} (hr : 0 ≤ r)
    (hq : ENNReal.ofReal (r + a) ≤ distanceToBoundary W g q) :
    Subtype.val '' riemannianBallOf ĝ q r = riemannianBallOf g q.val r := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_cut_BDRY1 W g ĝ heq
  have hball : riemannianBallOf g q.val r ⊆ (regionCut_BDRY1 W g a : Set W.Carrier) :=
    riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g hr ha hq
  have himage := image_riemannianBallOf_of_isometricOnOpen_BDRY1 g ĝ
    (interiorInclusion_BDRY1 W).symm hsrc hiso hball
  rw [interiorInclusion_symm_val_BDRY1 W q] at himage
  rw [← himage, Set.image_image]
  refine (Set.image_congr fun y hy => ?_).trans (Set.image_id _)
  exact val_interiorInclusion_symm_BDRY1 W (mem_interior_of_distanceToBoundary_pos_BDRY1 W g
    (lt_of_le_of_lt zero_le (hball hy)))

/-- **Distances at cut height `a`.** If `r + a ≤ D(q)`, the `ĝ`-distance of two points of the
`ĝ`-ball of radius `r / 4` about `q` is their distance in `W`. -/
theorem riemannianEDistOf_cut_eq_BDRY1 {a : ℝ} (ha : 0 ≤ a)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) {r : ℝ} (hr : 0 ≤ r)
    (hq : ENNReal.ofReal (r + a) ≤ distanceToBoundary W g q) {x y : W.pieceInterior ⊤}
    (hx : x ∈ riemannianBallOf ĝ q (r / 4)) (hy : y ∈ riemannianBallOf ĝ q (r / 4)) :
    riemannianEDistOf ĝ x y = riemannianEDistOf g x.val y.val := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_cut_BDRY1 W g ĝ heq
  have hball : riemannianBallOf g q.val r ⊆ (regionCut_BDRY1 W g a : Set W.Carrier) :=
    riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g hr ha hq
  have hq4 : ENNReal.ofReal (r / 4 + a) ≤ distanceToBoundary W g q :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hq
  have hb4 := image_val_riemannianBallOf_cut_BDRY1 W g ĝ ha heq q (by linarith) hq4
  have hx' : x.val ∈ riemannianBallOf g q.val (r / 4) := hb4 ▸ ⟨x, hx, rfl⟩
  have hy' : y.val ∈ riemannianBallOf g q.val (r / 4) := hb4 ▸ ⟨y, hy, rfl⟩
  have h := riemannianEDistOf_of_isometricOnOpen_BDRY1 g ĝ (interiorInclusion_BDRY1 W).symm hsrc
    hiso hball hx' hy'
  rwa [interiorInclusion_symm_val_BDRY1 W x, interiorInclusion_symm_val_BDRY1 W y] at h

/-- **Ranks at cut height `a`.** At every `q ∈ W°` with `4 R ρ(q) + a ≤ D(q)` (`R ≥ (β k)⁻¹`,
`k ≤ 3`) the scaled splitting ranks of `(W°, d_ĝ, ρ ∘ val)` and `(W, d_g, ρ)` agree. -/
theorem scaledSplittingRank_cut_eq_BDRY1 {a : ℝ} (ha : 0 ≤ a)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x) (β : ℕ → ℝ) {R : ℝ} (hR : 0 < R)
    (hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ R) (q : W.pieceInterior ⊤)
    (hq : ENNReal.ofReal (4 * (R * ρ q) + a) ≤ distanceToBoundary W g q) :
    have := connectedSpace_pieceInterior_top_BDRY1 W
    @scaledSplittingRank.{u, v} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
        (fun x => ρ x) (fun x => hρ x) β q =
      @scaledSplittingRank.{u, v} W.Carrier (inducedMetricSpace g) ρ hρ β q.val := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  have hRρ : 0 ≤ R * ρ q := (mul_pos hR (hρ q)).le
  have hq1 : ENNReal.ofReal (R * ρ q + a) ≤ distanceToBoundary W g q :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hq
  have hball := image_val_riemannianBallOf_cut_BDRY1 W g ĝ ha heq q hRρ hq1
  have hballN : @Metric.ball (W.pieceInterior ⊤) (inducedMetricSpace ĝ).toPseudoMetricSpace q
      (R * ρ q) = riemannianBallOf ĝ q (R * ρ q) := inducedMetricSpace_ball ĝ q _
  have hballW : @Metric.ball W.Carrier (inducedMetricSpace g).toPseudoMetricSpace q.val
      (R * ρ q) = riemannianBallOf g q.val (R * ρ q) := inducedMetricSpace_ball g q.val _
  refine scaledSplittingRank_eq_of_ballIsometry_BDRY1 (inducedMetricSpace g) (inducedMetricSpace ĝ)
    Subtype.val rfl ρ hρ (fun x => ρ x) (fun x => hρ x) rfl β hR hβR ?_ ?_
  · intro x hx y hy
    rw [hballN] at hx hy
    have h4 : R * ρ q = 4 * (R * ρ q) / 4 := by ring
    rw [h4] at hx hy
    have h := riemannianEDistOf_cut_eq_BDRY1 W g ĝ ha heq q (by linarith) hq hx hy
    rw [inducedMetricSpace_dist g, inducedMetricSpace_dist ĝ, h]
  · rw [hballN, hballW, hball]

/-- **Local analytic data at cut height `a`**: at `x ∈ W°` with `D(x) > a`, the sectional bounds
and the curvature derivative norms of `ĝ` and of `ρ⁻² ĝ` are those of `g` and `ρ⁻² g`; if
`r ρ + a ≤ D(q)`, the ball volumes of radius `r ρ` (resp. normalized radius `r`) agree. -/
theorem completion_cut_local_data_BDRY1 {a : ℝ} (ha : 0 ≤ a)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal a ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ x : W.pieceInterior ⊤, ENNReal.ofReal a < distanceToBoundary W g x → ∀ κ : ℝ,
      (SectionalBoundedBelowAt ĝ x κ ↔ SectionalBoundedBelowAt g x.val κ) ∧
      (SectionalBoundedBelowAt (normalizedCenterMetric ĝ ρ hρ) x κ ↔
        SectionalBoundedBelowAt (normalizedCenterMetric g ρ hρ) x.val κ)) ∧
    (∀ x : W.pieceInterior ⊤, ENNReal.ofReal a < distanceToBoundary W g x → ∀ k : ℕ,
      curvatureDerivativeNorm ĝ k x = curvatureDerivativeNorm g k x.val ∧
      curvatureDerivativeNorm (normalizedCenterMetric ĝ ρ hρ) k x =
        curvatureDerivativeNorm (normalizedCenterMetric g ρ hρ) k x.val) ∧
    ∀ (q : W.pieceInterior ⊤) {r : ℝ}, 0 ≤ r →
      ENNReal.ofReal (r * ρ + a) ≤ distanceToBoundary W g q →
      ballVolume ĝ q (r * ρ) = ballVolume g q.val (r * ρ) ∧
        ballVolume (normalizedCenterMetric ĝ ρ hρ) q r =
          ballVolume (normalizedCenterMetric g ρ hρ) q.val r := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨hsrc, hiso⟩ := completion_isometric_cut_BDRY1 W g ĝ heq
  have hisoN := scaleMetric_isometric_BDRY1 g ĝ _ hiso (inv_pos.mpr (sq_pos_of_pos hρ))
  refine ⟨fun x hx κ => ?_, fun x hx k => ?_, fun q r hr hq => ?_⟩
  · have hx' : x.val ∈ (regionCut_BDRY1 W g a : Set W.Carrier) := hx
    have h1 := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 g ĝ
      (interiorInclusion_BDRY1 W).symm (regionCut_BDRY1 W g a).isOpen hsrc hiso hx' (κ := κ)
    have h2 := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1
      (normalizedCenterMetric g ρ hρ) (normalizedCenterMetric ĝ ρ hρ)
      (interiorInclusion_BDRY1 W).symm (regionCut_BDRY1 W g a).isOpen hsrc hisoN hx' (κ := κ)
    rw [interiorInclusion_symm_val_BDRY1 W x] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · have hx' : x.val ∈ (regionCut_BDRY1 W g a : Set W.Carrier) := hx
    have h1 := curvatureDerivativeNorm_of_isometricOnOpen_BDRY1 g ĝ
      (interiorInclusion_BDRY1 W).symm (regionCut_BDRY1 W g a) hsrc hiso k hx'
    have h2 := curvatureDerivativeNorm_of_isometricOnOpen_BDRY1 (normalizedCenterMetric g ρ hρ)
      (normalizedCenterMetric ĝ ρ hρ) (interiorInclusion_BDRY1 W).symm (regionCut_BDRY1 W g a)
      hsrc hisoN k hx'
    rw [interiorInclusion_symm_val_BDRY1 W x] at h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · have hball : riemannianBallOf g q.val (r * ρ) ⊆ (regionCut_BDRY1 W g a : Set W.Carrier) :=
      riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g (mul_nonneg hr hρ.le) ha hq
    have hballN : riemannianBallOf (normalizedCenterMetric g ρ hρ) q.val r ⊆
        (regionCut_BDRY1 W g a : Set W.Carrier) := by
      rw [normalizedCenterMetric_ball]
      exact hball
    have h1 := ballVolume_of_isometricOnOpen_BDRY1 g ĝ (interiorInclusion_BDRY1 W).symm
      (regionCut_BDRY1 W g a).isOpen hsrc hiso hball
    have h2 := ballVolume_of_isometricOnOpen_BDRY1 (normalizedCenterMetric g ρ hρ)
      (normalizedCenterMetric ĝ ρ hρ) (interiorInclusion_BDRY1 W).symm
      (regionCut_BDRY1 W g a).isOpen hsrc hisoN hballN
    rw [interiorInclusion_symm_val_BDRY1 W q] at h1 h2
    exact ⟨h1, h2⟩

/-- **Consumer (a = 4, review 45).** There is a complete `ĝ` on `W°`, equal to `g°` on an open set
containing `{D ≥ 4}`, whose induced metric space is complete and whose scaled splitting ranks (for
the ORIGINAL scale `ρ` of `W`, used as `ρ ∘ val`) agree with those of `W` at every `q` with
`4 R ρ(q) + 4 ≤ D(q)`, `R ≥ (β k)⁻¹` (`k ≤ 3`). -/
theorem exists_interior_completion_four_ranks_BDRY1 (ρ : W.Carrier → ℝ) (hρ : ∀ x, 0 < ρ x)
    (β : ℕ → ℝ) {R : ℝ} (hR : 0 < R) (hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ R) :
    have := connectedSpace_pieceInterior_top_BDRY1 W
    ∃ ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤),
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      (letI := inducedMetricSpace ĝ
      CompleteSpace (W.pieceInterior ⊤)) ∧
      ∀ q : W.pieceInterior ⊤, ENNReal.ofReal (4 * (R * ρ q) + 4) ≤ distanceToBoundary W g q →
        @scaledSplittingRank.{u, v} (W.pieceInterior ⊤) (inducedMetricSpace ĝ)
            (fun x => ρ x) (fun x => hρ x) β q =
          @scaledSplittingRank.{u, v} W.Carrier (inducedMetricSpace g) ρ hρ β q.val := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨ĝ, O, hcomplete, -, hKO, heqO, -⟩ :=
    exists_interior_completion_cut_BDRY1 W g (by norm_num : (0 : ℝ) < 4)
  have heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x := fun x hx => heqO x (hKO hx)
  refine ⟨ĝ, heq, ?_, fun q hq => scaledSplittingRank_cut_eq_BDRY1 W g ĝ (by norm_num) heq ρ hρ β
    hR hβR q hq⟩
  let := inducedMetricSpace ĝ
  let : RiemannianBundle (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
    ⟨ĝ.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
    ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
  exact hcomplete.complete

end Cut

end DifferentialGeometry.Geometry.Collapse
