import DifferentialGeometry.Geometry.Collapse.CutPieceBallsImage
import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovSectionalThree
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Metric.RestrictionDistance

/-!
# Bishop–Gromov on compact carriers with boundary, below the boundary distance (B2)

Let `W` be a compact carrier (`GC.Endpoint.CompactCarrier`, possibly with boundary) with a
smooth metric `g`, and let `d(p, ∂W)` be the distance to the boundary
(`distanceToBoundary`, `Geometry/Collapse/CuspBoundary.lean:57`).

* T1. `riemannianClosedBallOf_subset_interior_of_lt`: if `r < d(p, ∂W)` the closed `r`-ball lies
  in the manifold interior; on a compact carrier this is an equivalence,
  `ofReal_lt_distanceToBoundary_iff` (the boundary is compact and the distance from `p` attains
  its minimum on it). The buffered form of the design (closed `3R`-ball) is the case `r = 3R`.
* T2. On the open interior with the restricted metric, two points of `B(p, R)` have the ambient
  distance as soon as `3R ≤ d(p, ∂W)` (`riemannianEDistOf_restrictOpen_interior_eq`, the
  `c = 3R` case of `riemannianEDistOf_restrictOpen_eq_of_ball_subset`), and balls of radius
  `r ≤ d(p, ∂W)` are the ambient balls (`image_val_riemannianBallOf_restrictOpen_interior`).
  In the interior atlas (model `𝓡 3`, as in `CompactCarrier.InteriorGeometry`) the metric of a
  piece interior, `pieceInteriorMetric`, has the ambient balls and ball volumes below the
  boundary distance (`pieceInteriorMetric_ball_and_volume`); generically, volumes are carried by
  any partial diffeomorphism from a compact manifold, isometric on its source, into a manifold with
  boundaryless model (`ballVolume_eq_of_isometricOn`).
* T3. `localBishopGromov_cross_of_distanceToBoundary`: if `sec ≥ -κ` (`κ ≥ 0`) on `B(p, R)` and
  `R < d(p, ∂W)`, the relative volume comparison of `X68`
  (`localBishopGromov_cross_endpoint_sectional_three`) holds for the concentric balls of radii
  `s ≤ R`; `modelVolume_cross_of_sectional_three_interior_buffer` is the `3R`-buffer form of the
  merged design (§5.3), and `localBishopGromov_relative_ratios_of_distanceToBoundary` gives the
  ratio form, with positivity from the open ball and finiteness from the compactness of `W`.
* T4. The volume bounds LC03 (`volume_upper_at_modified_scale_of_distanceToBoundary`, and
  `scaled_…` for `ρ⁻² g`) and LC04 (`volume_lower_at_modified_scale_of_distanceToBoundary`) of
  X68 on a compact carrier, below the boundary distance (`2ρ`, resp. `u`); in LC04 the ball
  `B(p, ρ)`, `ρ ≤ 2u`, may leave the curvature ball and the buffer, its volume is finite because
  `W` is compact.

## Route of T3: a complete extension, not a localized polar formula

The existing comparison (`BishopGromovLocal.lean`) writes the ball volume through the polar
formula of the segment domain, which needs a total exponential map and Hopf–Rinow, i.e.
`CompleteSpace` and a boundaryless model. Instead, with `R < ρ ≤ d(p, ∂W)`:

1. `U = B(p, ρ)` is open, path-connected and contained in the interior of `W`; with the interior
   atlas (`Manifold.interiorChartedSpace`) it is a manifold with model `𝓡 3`, and the inclusion
   is a local diffeomorphism, so `g` pulls back to `gU` on `U`.
2. The closed ball `B̄(p, R)` is compact and contained in `U`; by
   `exists_riemannianMetricComplete_eqOn_of_isCompact` there is a complete metric `g'` on `U`
   that equals `gU` on an open set `O` containing it.
3. The inverse of the inclusion of `O` is a partial diffeomorphism `Φ : W ⇀ U` isometric on its
   source `O ⊇ B̄(p, R)`. Since `W` is compact, `Φ` maps the `g`-balls of radius `≤ R` about `p`
   onto the `g'`-balls about `Φ p` (`image_riemannianBallOf_eq_of_isometricOn`, lifting of short
   curves; no global comparison of `g'` with `g` is needed), preserves their volume
   (`riemannianVolumeMeasure_image_eq_of_isometricOn`) and the sectional curvature
   (`metricRm04StandardAt_eq_of_partialDiffeomorph_restriction`).
4. On the complete, connected, boundaryless `(U, g')` the comparison of X68 applies.

Steps 3–4 are the generic statements `sectionalBoundedBelowAt_iff_of_isometricOn`,
`ballVolume_eq_of_isometricOn` and `localBishopGromov_cross_of_isometricOn`.
Only `R < d(p, ∂W)` is used; the buffer `3R` of the design is needed for the two-point distance
identity of T2, not for the comparison.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature GC.Endpoint
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal NNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-! ## T1: closed balls below the boundary distance -/

section Boundary

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- T1. A closed ball whose radius is strictly below the distance of its centre to the boundary
lies in the manifold interior. -/
theorem riemannianClosedBallOf_subset_interior_of_lt {p : W.Carrier} {r : ℝ}
    (hr : ENNReal.ofReal r < distanceToBoundary W g p) :
    riemannianClosedBallOf g p r ⊆ W.model.interior W.Carrier := by
  intro x hx
  rw [← W.model.compl_boundary]
  intro hxb
  have hle : riemannianEDistOf g p x ≤ ENNReal.ofReal r := hx
  exact (lt_irrefl _)
    (((distanceToBoundary_le_riemannianEDistOf W g hxb).trans hle).trans_lt hr)

end Boundary

/-- T1, equivalence on a compact carrier: the radius is strictly below the distance to the
boundary iff the closed ball lies in the interior. The boundary is compact and the distance from
`p` attains its minimum on it. -/
theorem ofReal_lt_distanceToBoundary_iff {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {p : W.Carrier} {r : ℝ} :
    ENNReal.ofReal r < distanceToBoundary W g p ↔
      riemannianClosedBallOf g p r ⊆ W.model.interior W.Carrier := by
  refine ⟨riemannianClosedBallOf_subset_interior_of_lt W g, fun hsub => ?_⟩
  rcases (W.model.boundary W.Carrier).eq_empty_or_nonempty with hempty | hne
  · rw [distanceToBoundary_eq_top_of_boundary_empty W g hempty p]
    exact ENNReal.ofReal_lt_top
  · have hcpt : IsCompact (W.model.boundary W.Carrier) :=
      (W.model.isClosed_boundary (M := W.Carrier) (n := ∞) (by simp)).isCompact
    obtain ⟨q, hq, hmin⟩ := hcpt.exists_isMinOn hne
      (f := fun x => riemannianEDistOf g p x)
      (continuous_riemannianEDist g p).continuousOn
    have hle : riemannianEDistOf g p q ≤ distanceToBoundary W g p :=
      le_iInf fun b => isMinOn_iff.mp hmin b b.property
    refine lt_of_lt_of_le ?_ hle
    by_contra hnot
    have hqi := hsub (show q ∈ riemannianClosedBallOf g p r from not_lt.mp hnot)
    rw [← W.model.compl_boundary] at hqi
    exact hqi hq

/-! ## T2: the restricted metric on the open interior -/

section Interior

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- T2 (distances). With the buffer `3R ≤ d(p, ∂W)`, the restriction of `g` to the open interior
has the ambient distance between any two points of `B(p, R)`. -/
theorem riemannianEDistOf_restrictOpen_interior_eq {p : W.Carrier} {R : ℝ}
    (hdepth : ENNReal.ofReal (3 * R) ≤ distanceToBoundary W g p) {x y : W.interior}
    (hx : (x : W.Carrier) ∈ riemannianBallOf g p R)
    (hy : (y : W.Carrier) ∈ riemannianBallOf g p R) :
    riemannianEDistOf (g.restrictOpen W.interior) x y = riemannianEDistOf g x y := by
  have hR : 0 < R :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le (show riemannianEDistOf g p x <
      ENNReal.ofReal R from hx))
  have hthird : (Real.toNNReal (3 * R) / 3 : ℝ≥0) = Real.toNNReal R := by
    ext
    simp only [NNReal.coe_div, Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 3 * R),
      Real.coe_toNNReal _ hR.le, NNReal.coe_ofNat]
    ring
  apply Geometry.Metric.riemannianEDistOf_restrictOpen_eq_of_ball_subset g W.interior p
    (Real.toNNReal (3 * R))
  · intro q hq
    exact riemannianBallOf_subset_interior W g hdepth hq
  · rw [hthird]
    exact hx
  · rw [hthird]
    exact hy

/-- T2 (balls). Below the distance to the boundary, the balls of the restriction of `g` to the
open interior are the ambient balls. -/
theorem image_val_riemannianBallOf_restrictOpen_interior (p : W.interior) {r : ℝ}
    (hr : ENNReal.ofReal r ≤ distanceToBoundary W g p) :
    Subtype.val '' riemannianBallOf (g.restrictOpen W.interior) p r =
      riemannianBallOf g p r := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact lt_of_le_of_lt (riemannianEDistOf_le_restrictOpen g W.interior p x) hx
  · intro hq
    have hqi : q ∈ W.interior := riemannianBallOf_subset_interior W g hr hq
    exact ⟨⟨q, hqi⟩,
      Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset g W.interior
        p ⟨q, hqi⟩ (riemannianBallOf_subset_interior W g hr) hq, rfl⟩

end Interior

/-! ## Partial diffeomorphisms isometric on their source -/

section Isometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space N] [T2Space M] in
/-- The inverse of a partial diffeomorphism that is isometric on its source is isometric on its
source. -/
theorem isometricOn_symm (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Ψ : PartialDiffeomorph J I M N ∞)
    (hΨ : ∀ z ∈ Ψ.source, ∀ a b : TangentSpace J z,
      g.inner z a b = h.inner (Ψ z) (mfderiv J I Ψ z a) (mfderiv J I Ψ z b)) :
    ∀ x ∈ Ψ.symm.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Ψ.symm x) (mfderiv I J Ψ.symm x v) (mfderiv I J Ψ.symm x w) := by
  intro x hx v w
  have hxt : x ∈ Ψ.target := hx
  have hmd : Ψ.toOpenPartialHomeomorph.MDifferentiable J I :=
    ⟨Ψ.contMDiffOn_toFun.mdifferentiableOn (by simp),
      Ψ.contMDiffOn_invFun.mdifferentiableOn (by simp)⟩
  have hd := hmd.comp_symm_deriv hxt
  have hv : mfderiv J I Ψ (Ψ.symm x) (mfderiv I J Ψ.symm x v) = v := congrArg (fun D => D v) hd
  have hw : mfderiv J I Ψ (Ψ.symm x) (mfderiv I J Ψ.symm x w) = w := congrArg (fun D => D w) hd
  have hxx : Ψ (Ψ.symm x) = x := Ψ.right_inv' hxt
  have hz : Ψ.symm x ∈ Ψ.source := Ψ.map_target' hxt
  rw [hΨ (Ψ.symm x) hz, hv, hw, hxx]

/-- A partial diffeomorphism isometric on its source preserves the sectional lower bounds at the
points of its source. -/
theorem sectionalBoundedBelowAt_iff_of_isometricOn (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞)
    (hmetric : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {x : N} (hx : x ∈ Φ.source) {κ : ℝ} :
    SectionalBoundedBelowAt h x κ ↔ SectionalBoundedBelowAt g (Φ x) κ := by
  let S : TopologicalSpace.Opens N := ⟨Φ.source, Φ.open_source⟩
  have hrm := metricRm04StandardAt_eq_of_partialDiffeomorph_restriction Φ S subset_rfl h g
    (fun y v w => hmetric y.val y.property v w) ⟨x, hx⟩
  have hloc : IsLocalDiffeomorphAt I J ∞ Φ x := ⟨Φ, hx, fun _ _ => rfl⟩
  let e := hloc.mfderivToContinuousLinearEquiv (by simp)
  have he : ∀ v, e v = mfderiv I J Φ x v := fun _ => rfl
  constructor
  · intro hs a b
    obtain ⟨v, rfl⟩ := e.surjective a
    obtain ⟨w, rfl⟩ := e.surjective b
    simp only [he]
    rw [← hmetric x hx v v, ← hmetric x hx w w, ← hmetric x hx v w, ← hrm v w w v]
    exact hs v w
  · intro hs v w
    rw [hmetric x hx v v, hmetric x hx w w, hmetric x hx v w, hrm v w w v]
    exact hs _ _

/-- A partial diffeomorphism from a compact manifold into a manifold with boundaryless model,
isometric on its source, preserves the volume of the balls contained in its source. -/
theorem ballVolume_eq_of_isometricOn [CompactSpace N] [J.Boundaryless]
    [SigmaCompactSpace N] [SigmaCompactSpace M]
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞)
    (hmetric : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {p : N} {r : ℝ} (hball : riemannianBallOf h p r ⊆ Φ.source) :
    ballVolume g (Φ p) r = ballVolume h p r := by
  have himage := image_riemannianBallOf_eq_of_isometricOn h g Φ hball
    (fun x hx v => (hmetric x (hball hx) v v).symm)
  unfold ballVolume
  rw [← himage]
  exact (riemannianVolumeMeasure_image_eq_of_isometricOn h g Φ hmetric
    (isOpen_lt (continuous_riemannianEDist h p) continuous_const) hball).symm

end Isometric

/-! ## Ball volumes on a compact manifold -/

section Compact

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N]

/-- On a compact manifold (any model, e.g. with boundary) every ball has finite Riemannian
volume: the volume measure is finite. No curvature assumption is involved. -/
theorem ballVolume_lt_top_of_compactSpace (h : SmoothRiemannianMetric I N) (p : N) (r : ℝ) :
    ballVolume h p r < ⊤ := by
  have := Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) h
  exact measure_lt_top _ _

omit [CompactSpace N] in
/-- A ball of positive radius has positive Riemannian volume (any model). -/
theorem ballVolume_pos_of_pos [SigmaCompactSpace N] (h : SmoothRiemannianMetric I N) (p : N)
    {r : ℝ} (hr : 0 < r) : 0 < ballVolume h p r := by
  have := Integral.Measure.riemannianVolumeMeasure_isOpenPosMeasure (I := I) h
  have hp : p ∈ riemannianBallOf h p r := by
    change riemannianEDistOf h p p < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  exact (isOpen_lt (continuous_riemannianEDist h p) continuous_const).measure_pos
    (Integral.Measure.riemannianVolumeMeasure I N h) ⟨p, hp⟩

/-- Ball volumes are monotone in the radius. -/
theorem ballVolume_mono (h : SmoothRiemannianMetric I N) (p : N) {r r' : ℝ} (hrr' : r ≤ r') :
    ballVolume h p r ≤ ballVolume h p r' :=
  measure_mono (riemannianBallOf_mono h p hrr')

end Compact

/-! ## Bishop–Gromov through a partial diffeomorphism into a complete manifold -/

section Comparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

/-- Bishop–Gromov transported along a partial diffeomorphism `Φ : N ⇀ M` isometric on its source,
from a compact manifold `N` (of any model) into a complete connected three-dimensional manifold
with boundaryless model: if the `h`-ball `B(p, R)` lies in the source and `sec ≥ -κ` on it, the
relative volume comparison holds for the `h`-balls of radii `s ≤ R` about `p`. -/
theorem localBishopGromov_cross_of_isometricOn
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (hg : RiemannianMetricComplete (I := J) g) (hdim : Module.finrank ℝ F = 3)
    (Φ : PartialDiffeomorph I J N M ∞)
    (hmetric : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    (p : N) {κ s R : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hball : riemannianBallOf h p R ⊆ Φ.source)
    (hsec : ∀ q ∈ riemannianBallOf h p R, SectionalBoundedBelowAt h q (-κ)) :
    ballVolume h p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume h p s := by
  have hballs : riemannianBallOf h p s ⊆ Φ.source :=
    (riemannianBallOf_mono h p hsR).trans hball
  have himage := image_riemannianBallOf_eq_of_isometricOn h g Φ hball
    (fun x hx v => (hmetric x (hball hx) v v).symm)
  have hsecM : ∀ q ∈ riemannianBallOf g (Φ p) R, SectionalBoundedBelowAt g q (-κ) := by
    rw [← himage]
    rintro _ ⟨y, hy, rfl⟩
    exact (sectionalBoundedBelowAt_iff_of_isometricOn h g Φ hmetric (hball hy)).mp (hsec y hy)
  rw [← ballVolume_eq_of_isometricOn h g Φ hmetric hball,
    ← ballVolume_eq_of_isometricOn h g Φ hmetric hballs]
  let : NeZero (Module.finrank ℝ F) := ⟨by rw [hdim]; norm_num⟩
  let : IsManifold J 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace J M
  let : RiemannianBundle (fun x : M => TangentSpace J x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle F (fun x : M => TangentSpace J x) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric J M
  have : CompleteSpace M := hg.complete
  have : IsRiemannianManifold J M := ⟨fun _ _ => rfl⟩
  have : T2Space (TangentBundle J M) := inferInstance
  have hEnorm : IsMetricNorm (I := J) g := isMetricNorm_of_riemannianBundle (I := J) g
  have hcross := localBishopGromov_cross_endpoint_sectional_three g hEnorm hdim (Φ p) hκ hs hsR
    hsecM
  rwa [← collapseBallVolume_eq_comparison g hEnorm, ← collapseBallVolume_eq_comparison g hEnorm]
    at hcross

end Comparison

/-! ## T2 in the interior atlas: balls and volumes of a piece interior -/

section PieceInterior

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
  (U : TopologicalSpace.Opens W.Carrier)

/-- The inclusion of the interior of a piece `U` of `W`, with its interior atlas (model `𝓡 3`,
as in `CompactCarrier.InteriorGeometry`), is a local diffeomorphism into `W`. -/
theorem isLocalDiffeomorph_pieceInterior_val :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
    IsLocalDiffeomorph (𝓡 3) W.model ∞ (Subtype.val : W.pieceInterior U → W.Carrier) :=
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
  isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := W.model) (W.pieceInterior U))
    (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.pieceInterior U)).symm.isLocalDiffeomorph

/-- The metric `g` on the interior of a piece `U`, in the interior atlas (model `𝓡 3`). -/
def pieceInteriorMetric :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior U)
    SmoothRiemannianMetric (𝓡 3) (W.pieceInterior U) :=
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior U)
  localPullMetric g Subtype.val (isLocalDiffeomorph_pieceInterior_val W U)

theorem pieceInteriorMetric_inner (x : W.pieceInterior U) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior U)
    ∀ v w : TangentSpace (𝓡 3) x, (pieceInteriorMetric W g U).inner x v w =
      g.inner x (mfderiv (𝓡 3) W.model Subtype.val x v)
        (mfderiv (𝓡 3) W.model Subtype.val x w) := by
  let := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
  let := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior U)
  intro v w
  exact localPullMetric_inner g Subtype.val (isLocalDiffeomorph_pieceInterior_val W U) x v w

/-- T2 (balls and volumes in the interior atlas). If the ball `B(p, r)` lies in the piece `U` and
`r ≤ d(p, ∂W)`, its points are exactly those of the ball of radius `r` of the metric of the piece
interior in the interior atlas, and the two balls have the same Riemannian volume. -/
theorem pieceInteriorMetric_ball_and_volume (p : W.pieceInterior U) {r : ℝ}
    (hU : riemannianBallOf g p r ⊆ U) (hr : ENNReal.ofReal r ≤ distanceToBoundary W g p) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior U)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior U)
    Subtype.val '' riemannianBallOf (pieceInteriorMetric W g U) p r = riemannianBallOf g p r ∧
      ballVolume (pieceInteriorMetric W g U) p r = ballVolume g p r := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (W.pieceInterior U) :=
    Manifold.interiorChartedSpace W.model ∞
  have : IsManifold (𝓡 3) ∞ (W.pieceInterior U) := Manifold.interiorIsManifold W.model ∞
  have : Nonempty (W.pieceInterior U) := ⟨p⟩
  have hι := isLocalDiffeomorph_pieceInterior_val W U
  let Ψ : PartialDiffeomorph (𝓡 3) W.model (W.pieceInterior U) W.Carrier ∞ :=
    partialDiffeomorphOfInjOn Subtype.val ⊤ hι.contMDiff.contMDiffOn
      (isLocalDiffeomorph_comp hι (isLocalDiffeomorph_subtype_val (I := 𝓡 3) ⊤))
      Subtype.val_injective.injOn
  have hmetric := isometricOn_symm g (pieceInteriorMetric W g U) Ψ
    (fun z _ a b => pieceInteriorMetric_inner W g U z a b)
  have hball : riemannianBallOf g p r ⊆ Ψ.symm.source := fun y hy =>
    ⟨⟨y, hU hy, riemannianBallOf_subset_interior W g hr hy⟩, trivial, rfl⟩
  have hp : Ψ.symm p = p := Ψ.left_inv' trivial
  have himage := image_riemannianBallOf_eq_of_isometricOn g (pieceInteriorMetric W g U) Ψ.symm
    hball (fun x hx v => (hmetric x (hball hx) v v).symm)
  have hvol := ballVolume_eq_of_isometricOn g (pieceInteriorMetric W g U) Ψ.symm hmetric hball
  rw [hp] at himage hvol
  refine ⟨?_, hvol⟩
  rw [← himage, Set.image_image]
  refine (Set.image_congr fun y hy => ?_).trans (Set.image_id _)
  exact Ψ.right_inv' (hball hy)

end PieceInterior

/-! ## T3: Bishop–Gromov on a compact carrier below the boundary distance -/

section Carrier

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- T3. On a compact carrier (possibly with boundary), if `sec ≥ -κ` (`κ ≥ 0`) on `B(p, R)` and
`R` is strictly below the distance of `p` to the boundary, the balls about `p` satisfy the
relative volume comparison for all radii `0 < s ≤ R`. -/
theorem localBishopGromov_cross_of_distanceToBoundary (p : W.Carrier) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hdepth : ENNReal.ofReal R < distanceToBoundary W g p)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  have hR : 0 < R := hs.trans_le hsR
  -- a radius `ρ` with `R < ρ ≤ d(p, ∂W)`
  obtain ⟨ρ, hρ0, hRρ', hρd⟩ := ENNReal.lt_iff_exists_real_btwn.mp hdepth
  have hRρ : R < ρ := (ENNReal.ofReal_lt_ofReal_iff'.mp hRρ').1
  have hρ : 0 < ρ := hR.trans hRρ
  -- the open set `U = B(p, ρ)` in the interior
  let U : TopologicalSpace.Opens W.Carrier :=
    ⟨riemannianBallOf g p ρ, isOpen_lt (continuous_riemannianEDist g p) continuous_const⟩
  have hUint : (U : Set W.Carrier) ⊆ W.model.interior W.Carrier :=
    riemannianBallOf_subset_interior W g hρd.le
  have hpU : p ∈ U := by
    change riemannianEDistOf g p p < ENNReal.ofReal ρ
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hcloU : riemannianClosedBallOf g p R ⊆ U := fun x hx =>
    lt_of_le_of_lt (show riemannianEDistOf g p x ≤ ENNReal.ofReal R from hx) hRρ'
  -- `U` with the interior atlas: a connected σ-compact manifold with model `𝓡 3`
  have : BoundarylessManifold W.model U :=
    ⟨fun x => W.model.isInteriorPoint_iff_isInteriorPoint_val.mpr (hUint x.property)⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) U := Manifold.interiorChartedSpace W.model ∞
  have : IsManifold (𝓡 3) ∞ U := Manifold.interiorIsManifold W.model ∞
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen W.model U.isOpen)
  have : ConnectedSpace U :=
    isConnected_iff_connectedSpace.mp (isPathConnected_riemannianBallOf g p hρ).isConnected
  have : Nonempty U := ⟨⟨p, hpU⟩⟩
  -- the inclusion is a local diffeomorphism from the interior atlas
  have hι : IsLocalDiffeomorph (𝓡 3) W.model ∞ (Subtype.val : U → W.Carrier) :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val (I := W.model) U)
      (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := U)).symm.isLocalDiffeomorph
  let gU : SmoothRiemannianMetric (𝓡 3) U := localPullMetric g Subtype.val hι
  -- a complete metric on `U` equal to `gU` near the closed `R`-ball
  let K : Set U := Subtype.val ⁻¹' riemannianClosedBallOf g p R
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    change IsCompact (Subtype.val '' (Subtype.val ⁻¹' riemannianClosedBallOf g p R))
    rw [Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hcloU hx⟩, rfl⟩)]
    exact (Geometry.Metric.isClosed_riemannianClosedBallOf g p R).isCompact
  obtain ⟨g', O, hg', hO, hKO, hg'O, -⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := 𝓡 3) gU hK
  -- the inverse of the inclusion of `O`, isometric on its source
  let O' : TopologicalSpace.Opens U := ⟨O, hO⟩
  have hF : IsLocalDiffeomorph (𝓡 3) W.model ∞ (fun x : O' => (x : U).val) :=
    isLocalDiffeomorph_comp hι (isLocalDiffeomorph_subtype_val (I := 𝓡 3) O')
  let Ψ : PartialDiffeomorph (𝓡 3) W.model U W.Carrier ∞ :=
    partialDiffeomorphOfInjOn Subtype.val O' hι.contMDiff.contMDiffOn hF
      Subtype.val_injective.injOn
  have hmetric := isometricOn_symm g g' Ψ (fun z hz a b => by
    rw [hg'O z hz]
    exact localPullMetric_inner g Subtype.val hι z a b)
  have hball : riemannianBallOf g p R ⊆ Ψ.symm.source := by
    intro y hy
    have hyc : y ∈ riemannianClosedBallOf g p R :=
      show riemannianEDistOf g p y ≤ ENNReal.ofReal R from le_of_lt hy
    exact ⟨⟨y, hcloU hyc⟩, hKO hyc, rfl⟩
  exact localBishopGromov_cross_of_isometricOn g g' hg' (finrank_euclideanSpace_fin) Ψ.symm
    hmetric p hκ hs hsR hball hsec

/-- T3, the buffered form of the merged design (§5.3): depth `3R`. -/
theorem modelVolume_cross_of_sectional_three_interior_buffer (p : W.Carrier) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hdepth : ENNReal.ofReal (3 * R) < distanceToBoundary W g p)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s :=
  localBishopGromov_cross_of_distanceToBoundary W g p hκ hs hsR
    ((ENNReal.ofReal_le_ofReal (by linarith)).trans_lt hdepth) hsec

/-- T3, real form (the ball volumes are finite since `W` is compact). -/
theorem localBishopGromov_real_cross_of_distanceToBoundary (p : W.Carrier) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hdepth : ENNReal.ofReal R < distanceToBoundary W g p)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    (ballVolume g p R).toReal * modelVolume (-κ) 3 s ≤
      modelVolume (-κ) 3 R * (ballVolume g p s).toReal := by
  have hm (r : ℝ) (hr : 0 < r) : 0 < modelVolume (-κ) 3 r :=
    modelVolume_pos (by norm_num) hr
      ⟨hr.le, fun hpos => (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim⟩
  have hcross := localBishopGromov_cross_of_distanceToBoundary W g p hκ hs hsR hdepth hsec
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ballVolume_lt_top_of_compactSpace g p s).ne)
    hcross
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hm s hs).le,
    ENNReal.toReal_ofReal (hm R (hs.trans_le hsR)).le] using hreal

/-- T3, relative-ratio form (the shape of X68's
`localBishopGromov_relative_ratios_sectional_three`): positivity from the open balls,
finiteness from the compactness of `W`. -/
theorem localBishopGromov_relative_ratios_of_distanceToBoundary (p : W.Carrier) {κ s R : ℝ}
    (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hdepth : ENNReal.ofReal R < distanceToBoundary W g p)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    0 < (ballVolume g p s).toReal ∧ 0 < (ballVolume g p R).toReal ∧
      ballVolume g p s < ⊤ ∧ ballVolume g p R < ⊤ ∧
      (ballVolume g p R).toReal / (ballVolume g p s).toReal ≤
        modelVolume (-κ) 3 R / modelVolume (-κ) 3 s ∧
      modelVolume (-κ) 3 s / modelVolume (-κ) 3 R ≤
        (ballVolume g p s).toReal / (ballVolume g p R).toReal := by
  have hsfin := ballVolume_lt_top_of_compactSpace g p s
  have hRfin := ballVolume_lt_top_of_compactSpace g p R
  have hsreal := ENNReal.toReal_pos (ballVolume_pos_of_pos g p hs).ne' hsfin.ne
  have hRreal := ENNReal.toReal_pos (ballVolume_pos_of_pos g p (hs.trans_le hsR)).ne' hRfin.ne
  have hm (r : ℝ) (hr : 0 < r) : 0 < modelVolume (-κ) 3 r :=
    modelVolume_pos (by norm_num) hr
      ⟨hr.le, fun hpos => (not_lt_of_ge (neg_nonpos.mpr hκ) hpos).elim⟩
  have hcross := localBishopGromov_real_cross_of_distanceToBoundary W g p hκ hs hsR hdepth hsec
  refine ⟨hsreal, hRreal, hsfin, hRfin, ?_, ?_⟩
  · exact (div_le_div_iff₀ hsreal (hm s hs)).mpr hcross
  · apply (div_le_div_iff₀ (hm R (hs.trans_le hsR)) hRreal).mpr
    simpa only [mul_comm] using hcross

end Carrier

/-! ## T4: the volume bounds LC03/LC04 at the modified scale, below the boundary distance -/

section Consumers

variable (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- T4, LC03 on a compact carrier: an attained volume `w r³` at a radius `r ≤ 2ρ`, with
`sec ≥ -(2ρ)⁻²` on `B(p, 2ρ)` and `2ρ < d(p, ∂W)`, bounds the volume ratio at `2ρ` by
`3 ∫₀¹ sinh² · w`. -/
theorem volume_upper_at_modified_scale_of_distanceToBoundary (p : W.Carrier) {w r ρ : ℝ}
    (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hdepth : ENNReal.ofReal (2 * ρ) < distanceToBoundary W g p)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (ballVolume g p (2 * ρ)).toReal / (2 * ρ) ^ 3 ≤
      (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w := by
  have hR : 0 < 2 * ρ := mul_pos (by norm_num) hρ
  have hκ : 0 ≤ ((2 * ρ) ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hcross := localBishopGromov_real_cross_of_distanceToBoundary W g p hκ hr hrρ hdepth hsec
  rw [hvol, ENNReal.toReal_ofReal (mul_pos hw (pow_pos hr 3)).le,
    sectionalThree_model_at_inverse_radius hR] at hcross
  have hmodel := sectionalThree_euclidean_le_model hκ hr.le
  have hstep :
      ((ballVolume g p (2 * ρ)).toReal * euclideanUnitBallVolume 3) * r ^ 3 ≤
        ((2 * ρ) ^ 3 * modelVolume (-1) 3 1 * w) * r ^ 3 := by
    calc
      _ = (ballVolume g p (2 * ρ)).toReal *
          (euclideanUnitBallVolume 3 * r ^ 3) := by ring
      _ ≤ (ballVolume g p (2 * ρ)).toReal *
          modelVolume (-((2 * ρ) ^ 2)⁻¹) 3 r :=
        mul_le_mul_of_nonneg_left hmodel ENNReal.toReal_nonneg
      _ ≤ _ := by nlinarith only [hcross]
  have hcancel := (mul_le_mul_iff_left₀ (pow_pos hr 3)).mp hstep
  rw [sectionalThree_model_hyperbolic_integral] at hcancel
  apply (div_le_iff₀ (pow_pos hR 3)).mpr
  apply (mul_le_mul_iff_left₀ (euclideanUnitBallVolume_pos 3)).mp
  nlinarith only [hcancel]

/-- T4, LC03 for the rescaled metric `ρ⁻² g` on a compact carrier: the ball of radius `2` has
volume at most `8 · 3 ∫₀¹ sinh² · w`. -/
theorem scaled_volume_upper_at_modified_scale_of_distanceToBoundary (p : W.Carrier)
    {w r ρ : ℝ} (hw : 0 < w) (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r ≤ 2 * ρ)
    (hdepth : ENNReal.ofReal (2 * ρ) < distanceToBoundary W g p)
    (hvol : ballVolume g p r = ENNReal.ofReal (w * r ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p (2 * ρ),
      SectionalBoundedBelowAt g q (-((2 * ρ) ^ 2)⁻¹)) :
    (ballVolume (scaleMetric (ρ ^ 2)⁻¹ (inv_pos.mpr (sq_pos_of_pos hρ)) g) p 2).toReal ≤
      8 * (3 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) * w := by
  have hbound := volume_upper_at_modified_scale_of_distanceToBoundary W g p hw hr hρ hrρ hdepth
    hvol hsec
  rw [sectionalThree_rescaled_ballVolume g finrank_euclideanSpace_fin p hρ]
  apply (div_le_iff₀ (pow_pos hρ 3)).mpr
  have hR : 0 < 2 * ρ := mul_pos (by norm_num) hρ
  have hmul := (div_le_iff₀ (pow_pos hR 3)).mp hbound
  nlinarith only [hmul]

/-- T4, LC04 on a compact carrier: an attained volume `w u³` at `u < d(p, ∂W)`, with
`sec ≥ -u⁻²` on `B(p, u)`, gives the lower volume ratio `w / (24 ∫₀¹ sinh²)` at every radius
`0 < ρ ≤ 2u`. The ball `B(p, ρ)` may reach beyond the curvature ball and beyond `d(p, ∂W)`; its
volume is finite because `W` is compact. -/
theorem volume_lower_at_modified_scale_of_distanceToBoundary (p : W.Carrier) {w u ρ : ℝ}
    (hw : 0 < w) (hu : 0 < u) (hρ : 0 < ρ) (hρu : ρ ≤ 2 * u)
    (hdepth : ENNReal.ofReal u < distanceToBoundary W g p)
    (hvol : ballVolume g p u = ENNReal.ofReal (w * u ^ 3))
    (hsec : ∀ q ∈ riemannianBallOf g p u, SectionalBoundedBelowAt g q (-(u ^ 2)⁻¹)) :
    0 < w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      w / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ≤ (ballVolume g p ρ).toReal / ρ ^ 3 := by
  have hI := sectionalThree_hyperbolic_integral_pos
  have hs : 0 < ρ / 2 := half_pos hρ
  have hsu : ρ / 2 ≤ u := by linarith
  have hκ : 0 ≤ (u ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
  have hcross := localBishopGromov_real_cross_of_distanceToBoundary W g p hκ hs hsu hdepth hsec
  rw [hvol, ENNReal.toReal_ofReal (mul_pos hw (pow_pos hu 3)).le,
    sectionalThree_model_at_inverse_radius hu] at hcross
  have hmodel := sectionalThree_euclidean_le_model hκ hs.le
  have hmono : (ballVolume g p (ρ / 2)).toReal ≤ (ballVolume g p ρ).toReal :=
    ENNReal.toReal_mono (ballVolume_lt_top_of_compactSpace g p ρ).ne
      (ballVolume_mono g p (by linarith))
  have hM : 0 < modelVolume (-1) 3 1 :=
    modelVolume_pos (by norm_num) zero_lt_one ⟨zero_le_one, by norm_num⟩
  have hstep :
      u ^ 3 * (w * euclideanUnitBallVolume 3 * (ρ / 2) ^ 3) ≤
        u ^ 3 * (modelVolume (-1) 3 1 * (ballVolume g p ρ).toReal) := by
    calc
      _ = (w * u ^ 3) * (euclideanUnitBallVolume 3 * (ρ / 2) ^ 3) := by ring
      _ ≤ (w * u ^ 3) * modelVolume (-(u ^ 2)⁻¹) 3 (ρ / 2) :=
        mul_le_mul_of_nonneg_left hmodel (mul_pos hw (pow_pos hu 3)).le
      _ ≤ (u ^ 3 * modelVolume (-1) 3 1) * (ballVolume g p (ρ / 2)).toReal :=
        hcross
      _ ≤ _ := by
        nlinarith only [mul_le_mul_of_nonneg_left hmono (mul_pos (pow_pos hu 3) hM).le]
  have hcancel := (mul_le_mul_iff_right₀ (pow_pos hu 3)).mp hstep
  rw [sectionalThree_model_hyperbolic_integral] at hcancel
  refine ⟨div_pos hw (mul_pos (by norm_num) hI), ?_⟩
  apply (div_le_div_iff₀ (mul_pos (by norm_num) hI) (pow_pos hρ 3)).mpr
  apply (mul_le_mul_iff_left₀ (euclideanUnitBallVolume_pos 3)).mp
  nlinarith only [hcancel]

end Consumers

end DifferentialGeometry.Geometry.Collapse
