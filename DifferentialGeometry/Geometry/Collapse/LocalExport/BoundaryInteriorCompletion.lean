import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Geometry.Metric.CurveVariation.Distance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.ForwardTransfer
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPremises

/-!
# LC88 / BCP04: the interior completion of a carrier with boundary (lane BDRY-1, G2)

Blueprint LC88 (`def:collapse-boundary-packet`, master207A) allows interior closed-manifold lemmas
"on balls contained in the controlled interior or after a specified extension whose metric agrees
there"; BCP04 (master207B) restricts the interior families to centres with `d(p, ∂W) > 10`. This
module specifies that extension once for the whole carrier:

* `interiorCharted_BDRY1`, `interiorManifold_BDRY1`: the interior atlas (model `𝓡 3`) on the open
  interior `W° = W.pieceInterior ⊤` (named; enable with `attribute [local instance]`);
  `coe_pieceInterior_top_BDRY1`, `connectedSpace_pieceInterior_top_BDRY1` (connected carrier);
* `isCompact_le_distanceToBoundary_BDRY1`: `{d ≥ c}` is compact in `W°` for `c > 0`;
* **T1** `exists_interior_completion_BDRY1`: ONE complete metric `ĝ` on `W°` with `ĝ = g°` on
  `{d ≥ 5}` and `ĝ ≥ g°`, where `g° = pieceInteriorMetric W g ⊤` (lane B2) — by
  `exists_riemannianMetricComplete_eqOn_of_isCompact`;
* the inclusion as a partial diffeomorphism `interiorInclusion_BDRY1` (source `univ`, target the
  manifold interior) and the transfer lemmas for any such `ĝ`: balls
  (`image_val_riemannianBallOf_completion_BDRY1`: `val '' B_ĝ(q, r) = B_g(q, r)` when
  `r + 5 ≤ d(q, ∂W)`), distances on the quarter balls (`riemannianEDistOf_completion_eq_BDRY1`), and
  the global comparison `d_g(a, b) ≤ d_ĝ(a, b)` (`riemannianEDistOf_val_le_completion_BDRY1`);
* consumer `exists_interior_completion_metric_BDRY1`: the induced metric space `(W°, d_ĝ)` is
  complete, has `hmetric`, and dominates `d_W` — the input form of the closed-chain kernels.

No new structure; no named hypothesis. Sheet: `build-logs/resume/sheet-BDRY-1.md`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold Bundle
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Interior

variable (W : CompactCarrier.{u})

/-- The interior atlas (model `𝓡 3`) on the open interior `W° = W.pieceInterior ⊤`. Not a
global instance; enable with `attribute [local instance]`. -/
@[reducible] def interiorCharted_BDRY1 : ChartedSpace E3 (W.pieceInterior ⊤) :=
  Manifold.interiorChartedSpace W.model ∞

attribute [local instance] interiorCharted_BDRY1

/-- `W°` is a smooth manifold in the interior atlas. -/
theorem interiorManifold_BDRY1 : IsManifold (𝓡 3) ∞ (W.pieceInterior ⊤) :=
  Manifold.interiorIsManifold W.model ∞

attribute [local instance] interiorManifold_BDRY1

/-- The points of `W°` are the manifold-interior points of `W`. -/
theorem coe_pieceInterior_top_BDRY1 :
    ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) =
      W.model.interior W.Carrier := by
  ext x
  simp [CompactCarrier.pieceInterior, CompactCarrier.interior, Manifold.intrinsicInterior]

/-- The interior of a connected carrier is connected. -/
theorem connectedSpace_pieceInterior_top_BDRY1 [ConnectedSpace W.Carrier] :
    ConnectedSpace (W.pieceInterior ⊤) := by
  have : IsManifold W.model 1 W.Carrier := IsManifold.of_le (n := ∞) (by decide)
  have hpre := DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior
    (I := W.model) (M := W.Carrier)
  have hne : (W.model.interior W.Carrier).Nonempty :=
    (DifferentialGeometry.Topology.Manifold.dense_manifold_interior (I := W.model)
      (M := W.Carrier)).nonempty
  have hconn : IsConnected ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) :
      Set W.Carrier) := by
    rw [coe_pieceInterior_top_BDRY1]
    exact ⟨hne, hpre⟩
  exact isConnected_iff_connectedSpace.mp hconn

variable (g : SmoothRiemannianMetric W.model W.Carrier)

/-- The distance to the boundary is upper semicontinuous (an infimum of continuous functions). -/
theorem upperSemicontinuous_distanceToBoundary_BDRY1 :
    UpperSemicontinuous (distanceToBoundary W g) := by
  have hcont : ∀ q : W.model.boundary W.Carrier,
      Continuous fun p : W.Carrier => riemannianEDistOf g p q := by
    intro q
    simp_rw [riemannianEDistOf_comm g _ (q : W.Carrier)]
    exact continuous_riemannianEDist g q
  exact upperSemicontinuous_iInf fun q => (hcont q).upperSemicontinuous

/-- A point at positive distance from the boundary is a manifold-interior point. -/
theorem mem_interior_of_distanceToBoundary_pos_BDRY1 {y : W.Carrier}
    (hy : 0 < distanceToBoundary W g y) : y ∈ W.model.interior W.Carrier := by
  rw [← W.model.compl_boundary]
  intro hb
  have h := distanceToBoundary_le_riemannianEDistOf W g (p := y) hb
  rw [riemannianEDistOf_self] at h
  exact (lt_irrefl _) (hy.trans_le h)

/-- For `c > 0`, the points of `W°` at boundary distance `≥ c` form a compact set. -/
theorem isCompact_le_distanceToBoundary_BDRY1 {c : ℝ} (hc : 0 < c) :
    IsCompact {x : W.pieceInterior ⊤ | ENNReal.ofReal c ≤ distanceToBoundary W g x} := by
  have hS : IsClosed {y : W.Carrier | ENNReal.ofReal c ≤ distanceToBoundary W g y} :=
    (upperSemicontinuous_distanceToBoundary_BDRY1 W g).isClosed_preimage (ENNReal.ofReal c)
  have hsub : {y : W.Carrier | ENNReal.ofReal c ≤ distanceToBoundary W g y} ⊆
      range (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
    intro y hy
    have hpos : 0 < distanceToBoundary W g y :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hc) hy
    have hyi := mem_interior_of_distanceToBoundary_pos_BDRY1 W g hpos
    rw [← coe_pieceInterior_top_BDRY1 W] at hyi
    exact ⟨⟨y, hyi⟩, rfl⟩
  exact Topology.IsInducing.subtypeVal.isCompact_preimage' hS.isCompact hsub

/-- **T1: the interior completion.** `W°` (interior atlas) carries a complete metric `ĝ` equal to
the pulled-back metric `g°` on `{d(·, ∂W) ≥ 5}` and dominating `g°` everywhere. -/
theorem exists_interior_completion_BDRY1 :
    ∃ ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤),
      RiemannianMetricComplete (I := 𝓡 3) ĝ ∧
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v := by
  obtain ⟨ĝ, O, hcomplete, -, hKO, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (pieceInteriorMetric W g ⊤)
      (isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num : (0 : ℝ) < 5))
  exact ⟨ĝ, hcomplete, fun x hx => heq x (hKO hx), hle⟩

/-- Triangle buffer: a point of `B(p, r)` with `r + 5 ≤ d(p, ∂W)` has boundary distance `> 5`. -/
theorem ofReal_five_lt_distanceToBoundary_BDRY1 {p x : W.Carrier} {r : ℝ} (hr : 0 ≤ r)
    (hp : ENNReal.ofReal (r + 5) ≤ distanceToBoundary W g p)
    (hx : x ∈ riemannianBallOf g p r) :
    ENNReal.ofReal 5 < distanceToBoundary W g x := by
  by_contra hle
  push Not at hle
  have hpx : riemannianEDistOf g p x < ENNReal.ofReal r := hx
  have htri := distanceToBoundary_le_add W g p x
  have hlt : distanceToBoundary W g x + riemannianEDistOf g p x <
      ENNReal.ofReal 5 + ENNReal.ofReal r :=
    ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle) hle hpx
  rw [← ENNReal.ofReal_add (by norm_num) hr, add_comm (5 : ℝ) r] at hlt
  exact (lt_irrefl _) ((hp.trans htri).trans_lt hlt)

/-- Interior points of `W` are at positive distance from the boundary; a radius `s > 0` with
`s ≤ d(x, ∂W)`. -/
theorem exists_pos_ofReal_le_distanceToBoundary_BDRY1 (x : W.pieceInterior ⊤) :
    ∃ s : ℝ, 0 < s ∧ ENNReal.ofReal s ≤ distanceToBoundary W g x := by
  have hx : x.val ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W]
    exact x.property
  obtain ⟨s, -, hs0, hs⟩ :=
    ENNReal.lt_iff_exists_real_btwn.mp (distanceToBoundary_pos_of_mem_interior W g hx)
  exact ⟨s, ENNReal.ofReal_pos.mp hs0, hs.le⟩

/-! ### The inclusion `W° → W` as a partial diffeomorphism -/

section Inclusion

variable [Nonempty (W.pieceInterior ⊤)]

/-- The inclusion `W° → W` (interior atlas on `W°`) as a partial diffeomorphism with source
`univ` and target the manifold interior. -/
def interiorInclusion_BDRY1 :
    PartialDiffeomorph (𝓡 3) W.model (W.pieceInterior ⊤) W.Carrier ∞ :=
  partialDiffeomorphOfInjOn Subtype.val ⊤
    (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff.contMDiffOn
    (isLocalDiffeomorph_comp (isLocalDiffeomorph_pieceInterior_val W ⊤)
      (isLocalDiffeomorph_subtype_val (I := 𝓡 3) ⊤))
    Subtype.val_injective.injOn

theorem interiorInclusion_apply_BDRY1 (x : W.pieceInterior ⊤) :
    interiorInclusion_BDRY1 W x = x.val := rfl

theorem interiorInclusion_source_BDRY1 : (interiorInclusion_BDRY1 W).source = univ := rfl

theorem mem_interiorInclusion_target_BDRY1 {y : W.Carrier}
    (hy : y ∈ W.model.interior W.Carrier) : y ∈ (interiorInclusion_BDRY1 W).target := by
  rw [← coe_pieceInterior_top_BDRY1 W] at hy
  exact ⟨⟨y, hy⟩, trivial, rfl⟩

theorem interiorInclusion_symm_val_BDRY1 (x : W.pieceInterior ⊤) :
    (interiorInclusion_BDRY1 W).symm x.val = x :=
  (interiorInclusion_BDRY1 W).left_inv' trivial

theorem val_interiorInclusion_symm_BDRY1 {y : W.Carrier}
    (hy : y ∈ W.model.interior W.Carrier) :
    ((interiorInclusion_BDRY1 W).symm y).val = y :=
  (interiorInclusion_BDRY1 W).right_inv' (mem_interiorInclusion_target_BDRY1 W hy)

/-- The inverse of the inclusion is isometric from `g` to `g°` on the whole interior. -/
theorem interiorInclusion_symm_isometric_BDRY1 :
    ∀ x ∈ (interiorInclusion_BDRY1 W).symm.source, ∀ v w : TangentSpace W.model x,
      g.inner x v w = (pieceInteriorMetric W g ⊤).inner ((interiorInclusion_BDRY1 W).symm x)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x v)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x w) :=
  isometricOn_symm g (pieceInteriorMetric W g ⊤) (interiorInclusion_BDRY1 W)
    (fun z _ a b => pieceInteriorMetric_inner W g ⊤ z a b)

/-- On `{d > 5}` the inverse of the inclusion is isometric from `g` to any `ĝ` that equals `g°`
on `{d ≥ 5}`. -/
theorem interiorInclusion_symm_isometric_of_eq_BDRY1
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    {x : W.Carrier} (hx : ENNReal.ofReal 5 < distanceToBoundary W g x) (v w : TangentSpace W.model x) :
    ĝ.inner ((interiorInclusion_BDRY1 W).symm x)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x v)
        (mfderiv W.model (𝓡 3) (interiorInclusion_BDRY1 W).symm x w) = g.inner x v w := by
  have hint := mem_interior_of_distanceToBoundary_pos_BDRY1 W g
    (lt_of_le_of_lt zero_le hx)
  have hsrc : x ∈ (interiorInclusion_BDRY1 W).symm.source :=
    mem_interiorInclusion_target_BDRY1 W hint
  have hd : ENNReal.ofReal 5 ≤ distanceToBoundary W g ((interiorInclusion_BDRY1 W).symm x) := by
    rw [val_interiorInclusion_symm_BDRY1 W hint]
    exact hx.le
  rw [heq _ hd]
  exact (interiorInclusion_symm_isometric_BDRY1 W g x hsrc v w).symm

/-- **Balls.** If `r + 5 ≤ d(q, ∂W)`, the `ĝ`-ball of radius `r` about `q ∈ W°` is the `g`-ball of
`W` about `q`. -/
theorem image_val_riemannianBallOf_completion_BDRY1
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) {r : ℝ} (hr : 0 ≤ r)
    (hq : ENNReal.ofReal (r + 5) ≤ distanceToBoundary W g q) :
    Subtype.val '' riemannianBallOf ĝ q r = riemannianBallOf g q.val r := by
  set Φ := (interiorInclusion_BDRY1 W).symm with hΦ
  have h5 : ∀ x ∈ riemannianBallOf g q.val r, ENNReal.ofReal 5 < distanceToBoundary W g x :=
    fun x hx => ofReal_five_lt_distanceToBoundary_BDRY1 W g hr hq hx
  have hint : ∀ x ∈ riemannianBallOf g q.val r, x ∈ W.model.interior W.Carrier :=
    fun x hx => mem_interior_of_distanceToBoundary_pos_BDRY1 W g
      (lt_of_le_of_lt zero_le (h5 x hx))
  have hsource : riemannianBallOf g q.val r ⊆ Φ.source :=
    fun x hx => mem_interiorInclusion_target_BDRY1 W (hint x hx)
  have himage := image_riemannianBallOf_eq_of_isometricOn g ĝ Φ hsource
    (fun x hx v => interiorInclusion_symm_isometric_of_eq_BDRY1 W g ĝ heq (h5 x hx) v v)
  rw [hΦ, interiorInclusion_symm_val_BDRY1 W q] at himage
  rw [← himage, Set.image_image]
  refine (Set.image_congr fun y hy => ?_).trans (Set.image_id _)
  exact val_interiorInclusion_symm_BDRY1 W (hint y hy)

/-- **Distances on small balls.** If `r + 5 ≤ d(q, ∂W)`, the `ĝ`-distance between two points of
the `ĝ`-ball of radius `r / 4` about `q` is their distance in `W`. -/
theorem riemannianEDistOf_completion_eq_BDRY1
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (q : W.pieceInterior ⊤) {r : ℝ} (hr : 0 ≤ r)
    (hq : ENNReal.ofReal (r + 5) ≤ distanceToBoundary W g q) {x y : W.pieceInterior ⊤}
    (hx : x ∈ riemannianBallOf ĝ q (r / 4)) (hy : y ∈ riemannianBallOf ĝ q (r / 4)) :
    riemannianEDistOf ĝ x y = riemannianEDistOf g x.val y.val := by
  set Φ := (interiorInclusion_BDRY1 W).symm with hΦ
  have h5 : ∀ z ∈ riemannianBallOf g q.val r, ENNReal.ofReal 5 < distanceToBoundary W g z :=
    fun z hz => ofReal_five_lt_distanceToBoundary_BDRY1 W g hr hq hz
  have hsource : riemannianBallOf g q.val r ⊆ Φ.source := fun z hz =>
    mem_interiorInclusion_target_BDRY1 W (mem_interior_of_distanceToBoundary_pos_BDRY1 W g
      (lt_of_le_of_lt zero_le (h5 z hz)))
  have hq4 : ENNReal.ofReal (r / 4 + 5) ≤ distanceToBoundary W g q :=
    (ENNReal.ofReal_le_ofReal (by linarith)).trans hq
  have hball := image_val_riemannianBallOf_completion_BDRY1 W g ĝ heq q (by linarith) hq4
  have hx' : x.val ∈ riemannianBallOf g q.val (r / 4) := hball ▸ ⟨x, hx, rfl⟩
  have hy' : y.val ∈ riemannianBallOf g q.val (r / 4) := hball ▸ ⟨y, hy, rfl⟩
  have h := riemannianEDistOf_map_eq_of_isometricOn g ĝ Φ hsource
    (fun z hz v => interiorInclusion_symm_isometric_of_eq_BDRY1 W g ĝ heq (h5 z hz) v v) hx' hy'
  rwa [hΦ, interiorInclusion_symm_val_BDRY1 W x, interiorInclusion_symm_val_BDRY1 W y] at h

/-- The inclusion `(W°, g°) → (W, g)` does not increase distances. -/
theorem riemannianEDistOf_val_le_pieceInterior_BDRY1 [ConnectedSpace W.Carrier]
    (a b : W.pieceInterior ⊤) :
    riemannianEDistOf g a.val b.val ≤ riemannianEDistOf (pieceInteriorMetric W g ⊤) a b := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  set Φ := (interiorInclusion_BDRY1 W).symm with hΦ
  have hloc : ∀ x : W.pieceInterior ⊤, ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → W.pieceInterior ⊤),
      a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
      riemannianCurveVariation (pieceInteriorMetric W g ⊤) γ a b ≠ ⊤ →
      riemannianCurveVariation g (Subtype.val ∘ γ) a b ≤
        (1 : ℝ≥0) * riemannianCurveVariation (pieceInteriorMetric W g ⊤) γ a b := by
    intro x
    obtain ⟨s, hs, hsd⟩ := exists_pos_ofReal_le_distanceToBoundary_BDRY1 W g x
    have hsource : riemannianBallOf g x.val s ⊆ Φ.source := fun z hz =>
      mem_interiorInclusion_target_BDRY1 W (riemannianBallOf_subset_interior W g hsd hz)
    have hdist : ∀ y z : W.pieceInterior ⊤, y.val ∈ riemannianBallOf g x.val (s / 4) →
        z.val ∈ riemannianBallOf g x.val (s / 4) →
        riemannianEDistOf g y.val z.val = riemannianEDistOf (pieceInteriorMetric W g ⊤) y z := by
      intro y z hy hz
      have h := riemannianEDistOf_map_eq_of_isometricOn g (pieceInteriorMetric W g ⊤) Φ hsource
        (fun w hw v => (interiorInclusion_symm_isometric_BDRY1 W g w (hsource hw) v v).symm)
        hy hz
      rw [hΦ, interiorInclusion_symm_val_BDRY1 W y, interiorInclusion_symm_val_BDRY1 W z] at h
      exact h.symm
    have hU : IsOpen (Subtype.val ⁻¹' riemannianBallOf g x.val (s / 4) :
        Set (W.pieceInterior ⊤)) :=
      (isOpen_lt (continuous_riemannianEDist g x.val) continuous_const).preimage
        continuous_subtype_val
    have hxU : x ∈ (Subtype.val ⁻¹' riemannianBallOf g x.val (s / 4) :
        Set (W.pieceInterior ⊤)) := by
      change riemannianEDistOf g x.val x.val < ENNReal.ofReal (s / 4)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr (by linarith)
    refine ⟨_, hU.mem_nhds hxU, fun a b γ _ _ hγ _ => ?_⟩
    rw [ENNReal.coe_one, one_mul]
    unfold riemannianCurveVariation
    refine iSup_mono fun p => Finset.sum_le_sum fun i _ => le_of_eq ?_
    exact hdist _ _ (hγ (p.2.2.2 (i + 1))) (hγ (p.2.2.2 i))
  have h := riemannianEDistOf_comp_le_of_local_riemannianCurveVariation
    (pieceInteriorMetric W g ⊤) g Subtype.val 1 hloc a b
  simpa only [ENNReal.coe_one, one_mul] using h

/-- **Global comparison.** For a metric `ĝ ≥ g°` on `W°`, the inclusion `(W°, ĝ) → (W, g)` does not
increase distances. -/
theorem riemannianEDistOf_val_le_completion_BDRY1 [ConnectedSpace W.Carrier]
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (a b : W.pieceInterior ⊤) :
    riemannianEDistOf g a.val b.val ≤ riemannianEDistOf ĝ a b := by
  refine (riemannianEDistOf_val_le_pieceInterior_BDRY1 W g a b).trans ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  set r : ℝ := (riemannianEDistOf ĝ a b).toReal + ε with hr
  have hb : b ∈ riemannianBallOf ĝ a r := by
    change riemannianEDistOf ĝ a b < ENNReal.ofReal r
    rw [hr, ← ENNReal.ofReal_toReal hfin.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (by rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]; linarith [hε])
  have hsub := riemannianBallOf_subset_of_inner_le_mul ĝ (pieceInteriorMetric W g ⊤) a
    (r := r) (Q := 1) one_pos (fun q _ v => by rw [one_mul]; exact hle q v)
  have hlt : riemannianEDistOf (pieceInteriorMetric W g ⊤) a b < ENNReal.ofReal r := by
    have := hsub hb
    rwa [Real.sqrt_one, one_mul] at this
  refine hlt.le.trans (le_of_eq ?_)
  rw [hr, ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hfin.ne,
    ENNReal.ofReal_coe_nnreal]

end Inclusion

/-- **Consumer: the metric space `(W°, d_ĝ)`.** For a connected carrier there is a complete metric
`ĝ` on `W°` with `ĝ = g°` on `{d ≥ 5}` whose induced metric space is complete, has the Riemannian
distance of `ĝ` as distance, and dominates the distance of `W`. -/
theorem exists_interior_completion_metric_BDRY1 [ConnectedSpace W.Carrier] :
    ∃ ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤),
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      have := connectedSpace_pieceInterior_top_BDRY1 W
      letI := inducedMetricSpace ĝ
      CompleteSpace (W.pieceInterior ⊤) ∧
        (∀ a b : W.pieceInterior ⊤, riemannianEDistOf ĝ a b = ENNReal.ofReal (dist a b)) ∧
        ∀ a b : W.pieceInterior ⊤, riemannianEDistOf g a.val b.val ≤ ENNReal.ofReal (dist a b) := by
  have := connectedSpace_pieceInterior_top_BDRY1 W
  obtain ⟨ĝ, hcomplete, heq, hle⟩ := exists_interior_completion_BDRY1 W g
  refine ⟨ĝ, heq, ?_⟩
  let := inducedMetricSpace ĝ
  have hm := inducedMetricSpace_hmetric ĝ
  refine ⟨?_, hm, fun a b => ?_⟩
  · let : RiemannianBundle (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
      ⟨ĝ.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E3 (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
      ⟨ĝ.inner, ĝ.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact hcomplete.complete
  · rw [← hm]
    exact riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle a b

end Interior

section Frozen

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

/-- The frozen G1 form of T1 (Targets.lean), with the unused collar argument `B` and the
connectedness conjunct; the production theorem drops `B` (strengthening). -/
example (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {δ : ℝ}
    (_B : NearlyCuspidalBoundary W g K δ) :
    ConnectedSpace (W.pieceInterior ⊤) ∧
    ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤),
      RiemannianMetricComplete ĝ ∧
      (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 5 ≤ distanceToBoundary W g x →
        ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      ∀ (x : W.pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v :=
  ⟨connectedSpace_pieceInterior_top_BDRY1 W, exists_interior_completion_BDRY1 W g⟩

end Frozen

end DifferentialGeometry.Geometry.Collapse
