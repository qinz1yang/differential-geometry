import DifferentialGeometry.Geometry.Collapse.GraphManifold
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleEverywhere
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace

/-!
# LC88: the premise layer of the boundary-collapse packet

Blueprint row LC88 (`def:collapse-boundary-packet`, master207A) first records the four premises
of KL 16.1, with `K, A` fixed before `w₀`, and the depth-100 cusp collar as an embedding of PAIRS
whose boundary goes onto the labelled boundary component. With the repaired field
`CuspEmbedding.boundary_preimage` (`p ∈ cuspDomain → (toFun p ∈ ∂W ↔ height p = 0)`), this module
encodes that layer and proves the pair-collar facts it gives; all statements reuse the tree's
`NearlyCuspidalBoundary`, `boundaryVolumeCollapsed`, `curvatureDerivativesControlled` and
`boundaryCollapseHypotheses` (`Geometry/Collapse/CuspBoundary.lean`, `GraphManifold.lean`).

* `BoundaryCollapsePremises`: the four premises as data (collar data, interior volume collapse,
  derivative control); `nonempty_iff` identifies it with `boundaryCollapseHypotheses`; the
  operations `weaken` (larger `w₀`) and `restrictOrder` (smaller `K`) keep `A`.
* Pair collar: the collar maps its face `{height = 0}` onto the labelled component
  (`CuspEmbedding.image_face_eq`), the component lies in `∂W` (`CuspEmbedding.subset_boundary`),
  the preimage of `∂W` in the collar domain is exactly the face
  (`CuspEmbedding.preimage_boundary_eq`),
  and points of positive depth go to the manifold interior
  (`CuspEmbedding.mem_interior_of_depth_pos`), hence to positive boundary distance.
* Boundary centres: every boundary point is the image of a face point of the collar of exactly one
  labelled component (`NearlyCuspidalBoundary.exists_face_of_mem_boundary`,
  `NearlyCuspidalBoundary.eq_of_mem_component`); the first volume scale is positive and attained at
  every face point for `w < ω₃/2` (Codex X88's half-ball volume) and at every point of positive
  depth for `w < ω₃` (BSA03 at interior centres).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature Bundle Manifold
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

/-- LC88, first layer: the four premises of KL 16.1 for a compact carrier with boundary, recorded
as data with `K` and `A` fixed before `w₀`: nearly cuspidal collar data (boundary size and the
depth-100 pair collars), interior volume collapse at boundary distance greater than ten, and the
whole-ball derivative control. -/
structure BoundaryCollapsePremises (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ : ℝ) where
  /-- Premises 1 and 2: boundary components of diameter at most `w₀` with depth-100 collars. -/
  cusp : NearlyCuspidalBoundary W g K w₀
  /-- Premise 3: volume collapse at the curvature scale away from the boundary. -/
  volume : boundaryVolumeCollapsed W g w₀
  /-- Premise 4: whole-ball derivative control. -/
  derivatives : curvatureDerivativesControlled g K A w₀

namespace BoundaryCollapsePremises

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ : ℝ}

/-- The premise record is inhabited exactly when the tree's boundary collapse hypotheses hold. -/
theorem nonempty_iff :
    Nonempty (BoundaryCollapsePremises W g K A w₀) ↔ boundaryCollapseHypotheses W g K A w₀ :=
  ⟨fun ⟨P⟩ => ⟨⟨P.cusp⟩, P.volume, P.derivatives⟩,
    fun ⟨⟨B⟩, hv, hd⟩ => ⟨⟨B, hv, hd⟩⟩⟩

/-- A choice of premise data from the tree's boundary collapse hypotheses. -/
def ofHypotheses (h : boundaryCollapseHypotheses W g K A w₀) :
    BoundaryCollapsePremises W g K A w₀ :=
  Classical.choice (nonempty_iff.mpr h)

/-- The premises at `w₀` give the premises at any larger threshold, with the same `K` and `A`. -/
def weaken (P : BoundaryCollapsePremises W g K A w₀) {w₁ : ℝ} (hw : w₀ ≤ w₁) :
    BoundaryCollapsePremises W g K A w₁ where
  cusp := P.cusp.weaken hw
  volume := fun p hp => volumeCollapsedAtCurvatureScale_mono g hw p (P.volume p hp)
  derivatives := curvatureDerivativesControlled_mono_threshold g K A hw P.derivatives

/-- The premises at order `K` give the premises at any smaller order, with the same `A`. -/
def restrictOrder (P : BoundaryCollapsePremises W g K A w₀) {K' : ℕ} (hK : K' ≤ K) :
    BoundaryCollapsePremises W g K' A w₀ where
  cusp := P.cusp.restrictOrder hK
  volume := P.volume
  derivatives := fun p w' hw' hwc r hr hR hv k hk q hq =>
    P.derivatives p w' hw' hwc r hr hR hv k (hk.trans hK) q hq

end BoundaryCollapsePremises

/-- A point of the half line of height zero is the base point `halfZero`. -/
theorem eq_halfZero_of_val_zero {z : EuclideanHalfSpace 1} (hz : z.val 0 = 0) : z = halfZero := by
  apply Subtype.ext
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simpa [halfZero, halfPoint] using hz

/-- The base point `halfZero` has height zero. -/
theorem halfZero_val_zero : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := by
  simp [halfZero, halfPoint]

/-- The face points `(t, halfZero)` lie in the depth-100 collar domain. -/
theorem mem_cuspDomain_halfZero (t : Torus) : ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
  change (halfZero : EuclideanHalfSpace 1).val 0 < cuspDepth
  rw [halfZero_val_zero, cuspDepth]
  norm_num

section PairCollar

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {δ : ℝ} {X : Set W.Carrier}

/-- Pair collar: the labelled component lies in the boundary. -/
theorem CuspEmbedding.subset_boundary (e : CuspEmbedding W g K δ X) :
    X ⊆ W.model.boundary W.Carrier := by
  intro x hx
  rw [← e.boundary_image] at hx
  obtain ⟨t, rfl⟩ := hx
  exact (e.boundary_preimage (mem_cuspDomain_halfZero t)).mpr halfZero_val_zero

/-- Pair collar: the face `{height = 0}` of the collar domain goes onto the labelled component. -/
theorem CuspEmbedding.image_face_eq (e : CuspEmbedding W g K δ X) :
    e.toFun '' {p | p ∈ cuspDomain ∧ p.2.val 0 = 0} = X := by
  refine Eq.trans ?_ e.boundary_image
  ext x
  constructor
  · rintro ⟨p, ⟨-, hz⟩, rfl⟩
    refine ⟨p.1, ?_⟩
    rw [← eq_halfZero_of_val_zero hz]
  · rintro ⟨t, rfl⟩
    exact ⟨(t, halfZero), ⟨mem_cuspDomain_halfZero t, halfZero_val_zero⟩, rfl⟩

/-- Pair collar: inside the collar domain, the preimage of the boundary is exactly the face. -/
theorem CuspEmbedding.preimage_boundary_eq (e : CuspEmbedding W g K δ X) :
    {p | p ∈ cuspDomain ∧ e.toFun p ∈ W.model.boundary W.Carrier} =
      {p | p ∈ cuspDomain ∧ p.2.val 0 = 0} := by
  ext p
  exact ⟨fun h => ⟨h.1, (e.boundary_preimage h.1).mp h.2⟩,
    fun h => ⟨h.1, (e.boundary_preimage h.1).mpr h.2⟩⟩

/-- Pair collar: points of positive depth are not mapped to the boundary. -/
theorem CuspEmbedding.notMem_boundary_of_depth_pos (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) :
    e.toFun p ∉ W.model.boundary W.Carrier :=
  fun hb => hz.ne' ((e.boundary_preimage hp).mp hb)

/-- Pair collar: points of positive depth are mapped to the manifold interior. -/
theorem CuspEmbedding.mem_interior_of_depth_pos (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (hz : 0 < p.2.val 0) :
    e.toFun p ∈ W.model.interior W.Carrier :=
  (W.model.isInteriorPoint_iff_not_isBoundaryPoint (e.toFun p)).mpr
    (e.notMem_boundary_of_depth_pos hp hz)

end PairCollar

/-- A manifold-interior point of a compact carrier has positive distance to the boundary. -/
theorem distanceToBoundary_pos_of_mem_interior (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {p : W.Carrier}
    (hp : p ∈ W.model.interior W.Carrier) : 0 < distanceToBoundary W g p := by
  have : TopologicalSpace.MetrizableSpace W.Carrier := Manifold.metrizableSpace W.model W.Carrier
  have hzero : riemannianClosedBallOf g p 0 ⊆ W.model.interior W.Carrier := by
    intro x hx
    change riemannianEDistOf g p x ≤ ENNReal.ofReal 0 at hx
    rw [ENNReal.ofReal_zero] at hx
    let em : EMetricSpace W.Carrier := inducedEMetricSpace g
    have hd : edist p x = 0 := le_zero_iff.mp hx
    rwa [← eq_of_edist_eq_zero hd]
  simpa only [ENNReal.ofReal_zero] using
    (ofReal_lt_distanceToBoundary_iff (W := W) (g := g) (r := 0)).mpr hzero

section Centres

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {δ : ℝ}

/-- Pair collar: points of positive depth have positive boundary distance. -/
theorem CuspEmbedding.distanceToBoundary_pos_of_depth_pos {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hz : 0 < p.2.val 0) : 0 < distanceToBoundary W g (e.toFun p) :=
  distanceToBoundary_pos_of_mem_interior W g (e.mem_interior_of_depth_pos hp hz)

/-- Nearly cuspidal collar data force a nonempty boundary. -/
theorem NearlyCuspidalBoundary.boundary_nonempty (B : NearlyCuspidalBoundary W g K δ) :
    (W.model.boundary W.Carrier).Nonempty := by
  obtain ⟨x, hx⟩ := (B.connected ⟨0, B.count_pos⟩).nonempty
  exact ⟨x, B.covers ▸ Set.mem_iUnion.mpr ⟨_, hx⟩⟩

/-- Boundary centres: every boundary point lies on the face of the collar of some labelled
component. -/
theorem NearlyCuspidalBoundary.exists_face_of_mem_boundary (B : NearlyCuspidalBoundary W g K δ)
    {x : W.Carrier} (hx : x ∈ W.model.boundary W.Carrier) :
    ∃ (i : Fin B.count) (t : Torus), x ∈ B.component i ∧ (B.collar i).toFun (t, halfZero) = x := by
  rw [← B.covers] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hi' := hi
  rw [← (B.collar i).boundary_image] at hi'
  obtain ⟨t, ht⟩ := hi'
  exact ⟨i, t, hi, ht⟩

/-- Boundary centres: the labelled component containing a point is unique. -/
theorem NearlyCuspidalBoundary.eq_of_mem_component (B : NearlyCuspidalBoundary W g K δ)
    {x : W.Carrier} {i j : Fin B.count} (hi : x ∈ B.component i) (hj : x ∈ B.component j) :
    i = j := by
  by_contra hij
  exact Set.disjoint_left.mp (B.disjoint hij) hi hj

/-- Boundary centres: at every face point of a collar, the first volume scale `r_x(w)` is positive
and attained, with the strict cubic barrier below it, for `0 < w < ω₃/2` (X88's half-ball
volume at actual boundary centres). -/
theorem CuspEmbedding.firstVolumeScale_spec_face {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) (t : Torus) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) :
    0 < firstVolumeScale g (e.toFun (t, halfZero)) w ∧
      (ballVolume g (e.toFun (t, halfZero)) (firstVolumeScale g (e.toFun (t, halfZero)) w)).toReal =
        w * firstVolumeScale g (e.toFun (t, halfZero)) w ^ 3 ∧
      ∀ r : ℝ, 0 < r → r < firstVolumeScale g (e.toFun (t, halfZero)) w →
        w * r ^ 3 < (ballVolume g (e.toFun (t, halfZero)) r).toReal :=
  firstVolumeScale_spec_of_boundary W g _
    ((e.boundary_preimage (mem_cuspDomain_halfZero t)).mpr halfZero_val_zero) hw hwc

/-- At every collar point of positive depth, the first volume scale is positive and attained, with
the strict cubic barrier below it, for `0 < w < ω₃` (BSA03 at interior centres). -/
theorem CuspEmbedding.firstVolumeScale_spec_of_depth_pos {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hz : 0 < p.2.val 0) {w : ℝ} (hw : 0 < w) (hwc : w < euclideanThreeUnitBallVolume) :
    0 < firstVolumeScale g (e.toFun p) w ∧
      (ballVolume g (e.toFun p) (firstVolumeScale g (e.toFun p) w)).toReal =
        w * firstVolumeScale g (e.toFun p) w ^ 3 ∧
      ∀ r : ℝ, 0 < r → r < firstVolumeScale g (e.toFun p) w →
        w * r ^ 3 < (ballVolume g (e.toFun p) r).toReal :=
  firstVolumeScale_spec_of_distanceToBoundary_pos W g _
    (e.distanceToBoundary_pos_of_depth_pos hp hz) hw hwc

/-- Boundary centres, whole layer: every boundary point `x` is the face image of exactly one
labelled collar, and its first volume scale is positive and attained for `0 < w < ω₃/2`. -/
theorem NearlyCuspidalBoundary.boundary_centre (B : NearlyCuspidalBoundary W g K δ)
    {x : W.Carrier} (hx : x ∈ W.model.boundary W.Carrier) {w : ℝ} (hw : 0 < w)
    (hwc : w < euclideanThreeUnitBallVolume / 2) :
    (∃ i : Fin B.count, x ∈ B.component i ∧ (∃ t : Torus, (B.collar i).toFun (t, halfZero) = x) ∧
        ∀ j : Fin B.count, x ∈ B.component j → j = i) ∧
      0 < firstVolumeScale g x w ∧
      (ballVolume g x (firstVolumeScale g x w)).toReal = w * firstVolumeScale g x w ^ 3 := by
  obtain ⟨i, t, hi, ht⟩ := B.exists_face_of_mem_boundary hx
  obtain ⟨h1, h2, -⟩ := firstVolumeScale_spec_of_boundary W g x hx hw hwc
  exact ⟨⟨i, hi, ⟨t, ht⟩, fun j hj => B.eq_of_mem_component hj hi⟩, h1, h2⟩

end Centres

end DifferentialGeometry.Geometry.Collapse
