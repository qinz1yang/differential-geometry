import DifferentialGeometry.Geometry.Collapse.CutPieceBallsImage
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Curvature.Metric.DerivativeNormBridge
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.LocalPullback
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

/-!
# Cut pieces: curvature and curvature scale below the boundary distance (A7 CPI, T4)

Let `h` be the metric induced on the piece `W = D.component i` by `g`
(`isInducedCutMetric g D i h`). On the interior `W°` of the piece the cut-piece map is an
injective local isometry (T2), so every pointwise curvature quantity of `h` at an interior point
equals the corresponding quantity of `g` at the image point:

* `curvatureDerivativeNorm_cutPieceMap_of_mem_interior` / `curvatureDerivativeNorm_cutPieceMap_of_mem_ball`
  (plan T4, on the ball `B_h(p, r)` with `r ≤ d_h(p, ∂W)`): `|∇^k Rm_h|(q) = |∇^k Rm_g|(Φ q)`;
* `metricRm04StandardAt_cutPieceMap_of_mem_interior` and
  `sectionalBoundedBelowAt_cutPieceMap_iff_of_mem_interior`: the curvature tensor and the
  sectional lower bounds correspond.

With T3 (balls below the boundary distance correspond), the admissible radii of the curvature
scale agree below the boundary distance (`curvatureAdmissible_cutPieceMap_iff`), and since both
admissible sets are downward closed,

* `min_curvatureRadius_cutPieceMap` (plan T4):
  `min (R_h p) (d_h(p, ∂W)) = min (R_g (Φ p)) (d_h(p, ∂W))`;
* consequences: equal curvature scales as soon as one of them is below the boundary distance
  (`curvatureRadius_cutPieceMap_eq_of_lt`, `…_of_lt'`), the same strict radius tests
  (`ofReal_lt_curvatureRadius_cutPieceMap_iff`), equal ball volumes
  (`ballVolume_cutPieceMap_of_le`), and the same volume-collapse test at the curvature scale
  (`volumeCollapsedAtCurvatureScale_cutPieceMap_iff`).

Proof of the pointwise identities. With `ι : W° → W` the open inclusion and
`Φ° = cutPieceMap D i ∘ ι : W° → M` (both local diffeomorphisms, T2), the pulled-back metrics
`ι^* h` and `Φ°^* g` on `W°` coincide (`localPullMetric_subtype_val_eq_cutPiece`, from the chain
rule and `isInducedCutMetric`). The naturality of the curvature derivative norms
(`CheegerGromovCompactness.curvDerivNorm_localPullMetric`,
`Geometry/Curvature/CurvatureOperator/Derivatives/LocalPullback.lean:62`) and of the curvature
tensor (`Curvature.metricRm04StandardAt_localPullMetric`,
`Geometry/Curvature/Naturality/Pullback/LocalCross.lean:34`) along `ι` and along `Φ°` give the
identities; lane A4's bridge `curvatureDerivativeNorm_eq_curvDerivNorm`
(`Geometry/Curvature/Metric/DerivativeNormBridge.lean`) converts the norms. Boundary points of the
piece are never used: no finite-order boundary-chart transport is needed.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open Set
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ## Downward closed admissible radii -/

section Admissible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : Type*} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The radii admissible for the curvature scale are downward closed. -/
theorem curvatureAdmissible_anti (g : SmoothRiemannianMetric I X) (p : X) {r s : ℝ}
    (hs : 0 < s) (hsr : s ≤ r)
    (hP : ∀ q ∈ riemannianBallOf g p r, SectionalBoundedBelowAt g q (-(r ^ 2)⁻¹)) :
    ∀ q ∈ riemannianBallOf g p s, SectionalBoundedBelowAt g q (-(s ^ 2)⁻¹) := by
  intro q hq
  refine (hP q (riemannianBallOf_mono g p hsr hq)).mono ?_
  exact neg_le_neg (inv_anti₀ (pow_pos hs 2) (pow_le_pow_left₀ hs.le hsr 2))

/-- Truncated suprema over downward closed sets of radii that agree below `d` agree after
truncation at `d` (one inequality). -/
theorem min_iSup_ofReal_le_of_agree {P Q : ℝ → Prop} {d : ℝ≥0∞}
    (hP : ∀ r s : ℝ, 0 < s → s ≤ r → P r → P s)
    (hPQ : ∀ r : ℝ, 0 < r → ENNReal.ofReal r ≤ d → P r → Q r) :
    min (⨆ (r : ℝ) (_ : 0 < r) (_ : P r), ENNReal.ofReal r) d ≤
      min (⨆ (r : ℝ) (_ : 0 < r) (_ : Q r), ENNReal.ofReal r) d := by
  refine le_min ?_ (min_le_right _ _)
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t, -, hlt1, hlt2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have htP : ENNReal.ofReal t < ⨆ (r : ℝ) (_ : 0 < r) (_ : P r), ENNReal.ofReal r :=
    lt_of_lt_of_le hlt2 (min_le_left _ _)
  have htd : ENNReal.ofReal t ≤ d := (lt_of_lt_of_le hlt2 (min_le_right _ _)).le
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp htP
  obtain ⟨hr0, hr⟩ := lt_iSup_iff.mp hr
  obtain ⟨hPr, hr⟩ := lt_iSup_iff.mp hr
  have htpos : 0 < t := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hlt1)
  have htr : t ≤ r := ((ENNReal.ofReal_lt_ofReal_iff hr0).mp hr).le
  have hQt : Q t := hPQ t htpos htd (hP r t htpos htr hPr)
  have hle : ENNReal.ofReal t ≤ ⨆ (r : ℝ) (_ : 0 < r) (_ : Q r), ENNReal.ofReal r :=
    le_iSup_of_le t (le_iSup_of_le htpos (le_iSup_of_le hQt le_rfl))
  exact (not_lt.mpr hle) hlt1

end Admissible

/-! ## T4 for cut pieces -/

section CutPiece

variable {M : ConnectedClosedOrientedManifold.{u} 3}

/-- The derivative of the cut-piece map on the interior is that of the cut-piece map. -/
theorem mfderiv_cutPieceInteriorMap_apply (D : TorusDecomposition M) (i : Fin D.components.count)
    (z : (D.component i).interior) (v : TangentSpace (D.component i).model z) :
    mfderiv (D.component i).model (𝓡 3) (cutPieceInteriorMap D i) z v =
      mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z.val v := by
  have hΦ : MDifferentiableAt (D.component i).model (𝓡 3) (cutPieceMap D i) z.val :=
    ((contMDiff_cutPieceMap D i) z.val).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (D.component i).model (D.component i).model
      (Subtype.val : (D.component i).interior → (D.component i).Carrier) z :=
    (hasMFDerivAt_subtype_val (I := (D.component i).model) (D.component i).interior z).mdifferentiableAt
  change mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i ∘ Subtype.val) z v = _
  rw [mfderiv_comp_apply z hΦ hι, mfderiv_subtype_val_apply]

/-- On the interior of the piece, the restriction of `h` and the pull-back of `g` by the
cut-piece map are the same metric. -/
theorem localPullMetric_subtype_val_eq_cutPiece (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) :
    localPullMetric h (Subtype.val : (D.component i).interior → (D.component i).Carrier)
        (isLocalDiffeomorph_subtype_val _) =
      localPullMetric g (cutPieceInteriorMap D i) (isLocalDiffeomorph_cutPieceInteriorMap D i) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  rw [localPullMetric_inner, localPullMetric_inner, mfderiv_cutPieceInteriorMap_apply,
    mfderiv_cutPieceInteriorMap_apply, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply]
  exact hind z.val v w

/-- T4 (pointwise). At an interior point of the piece, the norms of the covariant derivatives of
the curvature of `h` and of `g` at the image point agree. -/
theorem curvatureDerivativeNorm_cutPieceMap_of_mem_interior
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (k : ℕ) {q : (D.component i).Carrier}
    (hq : q ∈ (D.component i).interior) :
    curvatureDerivativeNorm h k q = curvatureDerivativeNorm g k (cutPieceMap D i q) := by
  rw [curvatureDerivativeNorm_eq_curvDerivNorm, curvatureDerivativeNorm_eq_curvDerivNorm]
  have h1 := CheegerGromovCompactness.curvDerivNorm_localPullMetric h
    (Subtype.val : (D.component i).interior → (D.component i).Carrier)
    (isLocalDiffeomorph_subtype_val _) k ⟨q, hq⟩
  have h2 := CheegerGromovCompactness.curvDerivNorm_localPullMetric g
    (cutPieceInteriorMap D i) (isLocalDiffeomorph_cutPieceInteriorMap D i) k ⟨q, hq⟩
  rw [localPullMetric_subtype_val_eq_cutPiece g D i h hind] at h1
  exact h1.symm.trans h2

/-- T4 (plan statement). On the intrinsic ball of radius at most the boundary distance, the
norms of the covariant derivatives of the curvature of `h` and of `g` agree. -/
theorem curvatureDerivativeNorm_cutPieceMap_of_mem_ball (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (k : ℕ) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p)
    {q : (D.component i).Carrier} (hq : q ∈ riemannianBallOf h p r) :
    curvatureDerivativeNorm h k q = curvatureDerivativeNorm g k (cutPieceMap D i q) :=
  curvatureDerivativeNorm_cutPieceMap_of_mem_interior g D i h hind k
    (riemannianBallOf_subset_interior (D.component i) h hd hq)

/-- At an interior point of the piece the curvature tensor of `h` is the pull-back of that of
`g` (stated at a point of the interior subtype). -/
theorem metricRm04StandardAt_cutPieceMap_interior
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (z : (D.component i).interior)
    (X Y Z T : TangentSpace (D.component i).model z) :
    metricRm04StandardAt h z.val X Y Z T =
      metricRm04StandardAt g (cutPieceMap D i z.val)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z.val X)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z.val Y)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z.val Z)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z.val T) := by
  have h1 := metricRm04StandardAt_localPullMetric h
    (Subtype.val : (D.component i).interior → (D.component i).Carrier)
    (isLocalDiffeomorph_subtype_val _) z X Y Z T
  have h2 := metricRm04StandardAt_localPullMetric g
    (cutPieceInteriorMap D i) (isLocalDiffeomorph_cutPieceInteriorMap D i) z X Y Z T
  rw [localPullMetric_subtype_val_eq_cutPiece g D i h hind] at h1
  rw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
    mfderiv_subtype_val_apply] at h1
  rw [mfderiv_cutPieceInteriorMap_apply, mfderiv_cutPieceInteriorMap_apply,
    mfderiv_cutPieceInteriorMap_apply, mfderiv_cutPieceInteriorMap_apply] at h2
  exact h1.symm.trans h2

/-- At an interior point of the piece the curvature tensor of `h` is the pull-back of that of
`g`. -/
theorem metricRm04StandardAt_cutPieceMap_of_mem_interior
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {q : (D.component i).Carrier}
    (hq : q ∈ (D.component i).interior) (X Y Z T : TangentSpace (D.component i).model q) :
    metricRm04StandardAt h q X Y Z T =
      metricRm04StandardAt g (cutPieceMap D i q)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) q X)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) q Y)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) q Z)
        (mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) q T) :=
  metricRm04StandardAt_cutPieceMap_interior g D i h hind ⟨q, hq⟩ X Y Z T

/-- At an interior point of the piece, `h` and `g` (at the image point) satisfy the same
sectional lower bounds. -/
theorem sectionalBoundedBelowAt_cutPieceMap_iff_of_mem_interior
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) {D : TorusDecomposition M}
    {i : Fin D.components.count}
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {q : (D.component i).Carrier}
    (hq : q ∈ (D.component i).interior) {κ : ℝ} :
    SectionalBoundedBelowAt h q κ ↔ SectionalBoundedBelowAt g (cutPieceMap D i q) κ := by
  have hloc := isLocalDiffeomorphAt_cutPieceMap D i hq
  let e := hloc.mfderivToContinuousLinearEquiv (by simp)
  have he : ∀ v, e v = mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) q v := fun _ => rfl
  constructor
  · intro hs a b
    obtain ⟨v, rfl⟩ := e.surjective a
    obtain ⟨w, rfl⟩ := e.surjective b
    simp only [he]
    rw [← hind q v v, ← hind q w w, ← hind q v w,
      ← metricRm04StandardAt_cutPieceMap_of_mem_interior g D i h hind hq]
    exact hs v w
  · intro hs v w
    rw [hind q v v, hind q w w, hind q v w,
      metricRm04StandardAt_cutPieceMap_of_mem_interior g D i h hind hq]
    exact hs _ _

/-- Below the boundary distance, a radius is admissible for the curvature scale of `h` at `p`
iff it is admissible for that of `g` at the image point (any curvature level `κ`). -/
theorem curvatureAdmissible_cutPieceMap_iff (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    {D : TorusDecomposition M} {i : Fin D.components.count}
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) {κ : ℝ} :
    (∀ q ∈ riemannianBallOf h p r, SectionalBoundedBelowAt h q κ) ↔
      ∀ y ∈ riemannianBallOf g (cutPieceMap D i p) r, SectionalBoundedBelowAt g y κ := by
  rw [← image_cutPieceMap_riemannianBallOf g D i h hind hd, Set.forall_mem_image]
  exact forall₂_congr fun q hq => sectionalBoundedBelowAt_cutPieceMap_iff_of_mem_interior g h hind
    (riemannianBallOf_subset_interior (D.component i) h hd hq)

/-- T4 (plan statement). Truncated at the boundary distance, the curvature scales of `h` at `p`
and of `g` at the image point agree. -/
theorem min_curvatureRadius_cutPieceMap (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (p : (D.component i).Carrier) :
    min (curvatureRadius h p) (distanceToBoundary (D.component i) h p) =
      min (curvatureRadius g (cutPieceMap D i p)) (distanceToBoundary (D.component i) h p) := by
  unfold curvatureRadius
  apply le_antisymm
  · exact min_iSup_ofReal_le_of_agree
      (P := fun r => ∀ q ∈ riemannianBallOf h p r, SectionalBoundedBelowAt h q (-(r ^ 2)⁻¹))
      (Q := fun r => ∀ y ∈ riemannianBallOf g (cutPieceMap D i p) r,
        SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹))
      (fun _ _ hs hsr hP => curvatureAdmissible_anti h p hs hsr hP)
      (fun _ _ hrd => (curvatureAdmissible_cutPieceMap_iff g h hind hrd).mp)
  · exact min_iSup_ofReal_le_of_agree
      (P := fun r => ∀ y ∈ riemannianBallOf g (cutPieceMap D i p) r,
        SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹))
      (Q := fun r => ∀ q ∈ riemannianBallOf h p r, SectionalBoundedBelowAt h q (-(r ^ 2)⁻¹))
      (fun _ _ hs hsr hP => curvatureAdmissible_anti g _ hs hsr hP)
      (fun _ _ hrd => (curvatureAdmissible_cutPieceMap_iff g h hind hrd).mpr)

/-- If the curvature scale of `h` at `p` is below the boundary distance, it is the curvature
scale of `g` at the image point. -/
theorem curvatureRadius_cutPieceMap_eq_of_lt (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier}
    (hlt : curvatureRadius h p < distanceToBoundary (D.component i) h p) :
    curvatureRadius g (cutPieceMap D i p) = curvatureRadius h p := by
  have hmin := min_curvatureRadius_cutPieceMap g D i h hind p
  rw [min_eq_left hlt.le] at hmin
  rcases le_total (curvatureRadius g (cutPieceMap D i p)) (distanceToBoundary (D.component i) h p)
    with hle | hle
  · rw [min_eq_left hle] at hmin
    exact hmin.symm
  · rw [min_eq_right hle] at hmin
    exact absurd hmin hlt.ne

/-- If the curvature scale of `g` at the image of `p` is below the boundary distance of `p`, it
is the curvature scale of `h` at `p`. -/
theorem curvatureRadius_cutPieceMap_eq_of_lt' (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier}
    (hlt : curvatureRadius g (cutPieceMap D i p) < distanceToBoundary (D.component i) h p) :
    curvatureRadius g (cutPieceMap D i p) = curvatureRadius h p := by
  have hmin := min_curvatureRadius_cutPieceMap g D i h hind p
  rw [min_eq_left hlt.le] at hmin
  rcases le_total (curvatureRadius h p) (distanceToBoundary (D.component i) h p) with hle | hle
  · rw [min_eq_left hle] at hmin
    exact hmin.symm
  · rw [min_eq_right hle] at hmin
    exact absurd hmin.symm hlt.ne

/-- Strictly below the boundary distance, the strict radius tests against the two curvature
scales agree. -/
theorem ofReal_lt_curvatureRadius_cutPieceMap_iff (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    {D : TorusDecomposition M} {i : Fin D.components.count}
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r < distanceToBoundary (D.component i) h p) :
    ENNReal.ofReal r < curvatureRadius h p ↔
      ENNReal.ofReal r < curvatureRadius g (cutPieceMap D i p) := by
  have hmin := min_curvatureRadius_cutPieceMap g D i h hind p
  constructor
  · intro hr
    have h1 : ENNReal.ofReal r <
        min (curvatureRadius g (cutPieceMap D i p)) (distanceToBoundary (D.component i) h p) :=
      hmin ▸ lt_min hr hd
    exact (lt_min_iff.mp h1).1
  · intro hr
    have h1 : ENNReal.ofReal r <
        min (curvatureRadius h p) (distanceToBoundary (D.component i) h p) :=
      hmin.symm ▸ lt_min hr hd
    exact (lt_min_iff.mp h1).1

/-- Below the boundary distance, the intrinsic and the ambient ball have the same volume. -/
theorem ballVolume_cutPieceMap_of_le (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    ballVolume h p r = ballVolume g (cutPieceMap D i p) r :=
  riemannianVolumeMeasure_cutPieceMap_riemannianBallOf g D i h hind hd

/-- If the curvature scale of `h` at `p` is below the boundary distance, the volume-collapse
test at the curvature scale reads the same for `h` at `p` and for `g` at the image point. -/
theorem volumeCollapsedAtCurvatureScale_cutPieceMap_iff
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) {D : TorusDecomposition M}
    {i : Fin D.components.count}
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {w : ℝ} {p : (D.component i).Carrier}
    (hlt : curvatureRadius h p < distanceToBoundary (D.component i) h p) :
    volumeCollapsedAtCurvatureScale h w p ↔
      volumeCollapsedAtCurvatureScale g w (cutPieceMap D i p) := by
  have hR := curvatureRadius_cutPieceMap_eq_of_lt g D i h hind hlt
  unfold volumeCollapsedAtCurvatureScale
  rw [hR]
  refine forall₂_congr fun r _ => forall_congr' fun hr => ?_
  rw [ballVolume_cutPieceMap_of_le g D i h hind (hr ▸ hlt).le]

end CutPiece

end DifferentialGeometry.Geometry.Collapse
