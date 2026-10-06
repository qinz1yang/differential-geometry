import DifferentialGeometry.Geometry.Collapse.CutMetricBalls
import DifferentialGeometry.Geometry.Collapse.CurvatureRadiusBounds
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

private theorem sectionalBoundedBelowAt_cutPieceMap_iff
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (x : (D.component i).Carrier) (hx : (D.component i).model.IsInteriorPoint x) (K : ℝ) :
    SectionalBoundedBelowAt h x K ↔ SectionalBoundedBelowAt g (cutPieceMap D i x) K := by
  let U := (D.component i).interior
  let f : U → M.Carrier := fun y => cutPieceMap D i y.val
  have hf : IsLocalDiffeomorph (D.component i).model (𝓡 3) ∞ f :=
    isLocalDiffeomorph_cutPieceMap_interior D i
  have hdf (y : U) :
      mfderiv (D.component i).model (𝓡 3) f y =
        mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) y.val := by
    exact DifferentialGeometry.mfderiv_restrict_open
      (I := (D.component i).model) (J := 𝓡 3) (cutPieceMap D i) U y
  have hmetric : h.restrictOpen U =
      localPullMetric (I := (D.component i).model) (J := 𝓡 3) g f hf := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner, hdf y]
    exact hinduced y.val v w
  let xU : U := ⟨x, hx⟩
  have hinner (v w : TangentSpace (D.component i).model x) :
      h.inner x v w = g.inner (f xU)
        (mfderiv (D.component i).model (𝓡 3) f xU v)
        (mfderiv (D.component i).model (𝓡 3) f xU w) := by
    rw [hdf xU]
    exact hinduced x v w
  have hRm (v w : TangentSpace (D.component i).model x) :
      metricRm04StandardAt h x v w w v = metricRm04StandardAt g (f xU)
        (mfderiv (D.component i).model (𝓡 3) f xU v)
        (mfderiv (D.component i).model (𝓡 3) f xU w)
        (mfderiv (D.component i).model (𝓡 3) f xU w)
        (mfderiv (D.component i).model (𝓡 3) f xU v) := by
    have hrestrict : metricRm04StandardAt (h.restrictOpen U) xU v w w v =
        metricRm04StandardAt h x v w w v := by
      have hv (z : TangentSpace (D.component i).model xU) :
          mfderiv (D.component i).model (D.component i).model
            (Subtype.val : U → (D.component i).Carrier) xU z = z :=
        DifferentialGeometry.mfderiv_subtype_val_apply
          (I := (D.component i).model) U xU z
      have hh := metricRm04StandardAt_restrictOpen
        (I := (D.component i).model) h U xU v w w v
      rw [hv v, hv w] at hh
      exact hh
    rw [← hrestrict, hmetric]
    exact metricRm04StandardAt_localPullMetric g f hf xU v w w v
  have hsurj : Function.Surjective (mfderiv (D.component i).model (𝓡 3) f xU) :=
    (hf.mfderivToContinuousLinearEquiv (by simp) xU).surjective
  constructor
  · intro hsec a b
    obtain ⟨v, rfl⟩ := hsurj a
    obtain ⟨w, rfl⟩ := hsurj b
    have hh := hsec v w
    change K * (h.inner x v v * h.inner x w w - h.inner x v w ^ 2) ≤
      metricRm04StandardAt h x v w w v at hh
    rw [hinner v v, hinner w w, hinner v w, hRm v w] at hh
    exact hh
  · intro hsec v w
    change K * (h.inner x v v * h.inner x w w - h.inner x v w ^ 2) ≤
      metricRm04StandardAt h x v w w v
    rw [hinner v v, hinner w w, hinner v w, hRm v w]
    exact hsec (mfderiv (D.component i).model (𝓡 3) f xU v)
      (mfderiv (D.component i).model (𝓡 3) f xU w)

private theorem forall_ball_sectionalBoundedBelowAt_cutPieceMap_iff
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (p : (D.component i).Carrier) (r K : ℝ)
    (hboundary : ENNReal.ofReal r < distanceToBoundary (D.component i) h p) :
    (∀ q ∈ riemannianBallOf h p r, SectionalBoundedBelowAt h q K) ↔
      ∀ q ∈ riemannianBallOf g (cutPieceMap D i p) r, SectionalBoundedBelowAt g q K := by
  have hsub : ∀ q ∈ riemannianBallOf h p r, (D.component i).model.IsInteriorPoint q := by
    intro q hq
    by_contra hqi
    have hqb : q ∈ (D.component i).model.boundary (D.component i).Carrier :=
      ((D.component i).model.isBoundaryPoint_iff_not_isInteriorPoint q).mpr hqi
    have hdle : distanceToBoundary (D.component i) h p ≤ riemannianEDistOf h p q := by
      unfold distanceToBoundary
      exact iInf_le (fun z : (D.component i).model.boundary (D.component i).Carrier =>
        riemannianEDistOf h p z.val) ⟨q, hqb⟩
    exact (not_lt_of_ge hdle) (hq.trans hboundary)
  have himage := image_riemannianBallOf_cutPieceMap g D i h hinduced p r hboundary
  constructor
  · intro hsec q hq
    rw [← himage] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact (sectionalBoundedBelowAt_cutPieceMap_iff g D i h hinduced x (hsub x hx) K).mp
      (hsec x hx)
  · intro hsec q hq
    have hmap : cutPieceMap D i q ∈ riemannianBallOf g (cutPieceMap D i p) r := by
      rw [← himage]
      exact ⟨q, hq, rfl⟩
    exact (sectionalBoundedBelowAt_cutPieceMap_iff g D i h hinduced q (hsub q hq) K).mpr
      (hsec (cutPieceMap D i q) hmap)

theorem min_curvatureRadius_distanceToBoundary_cutPieceMap
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (p : (D.component i).Carrier) :
    min (curvatureRadius h p) (distanceToBoundary (D.component i) h p) =
      min (curvatureRadius g (cutPieceMap D i p)) (distanceToBoundary (D.component i) h p) := by
  let d := distanceToBoundary (D.component i) h p
  have compare (a b : ℝ≥0∞)
      (htransfer : ∀ s : ℝ, 0 < s → ENNReal.ofReal s < a →
        ENNReal.ofReal s < d → ENNReal.ofReal s ≤ b) :
      min a d ≤ min b d := by
    by_contra hnot
    obtain ⟨s, hslo, hshi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hnot)
    have hspos : 0 < (s : ℝ) := by
      have hsenn : (0 : ℝ≥0∞) < s := bot_le.trans_lt hslo
      exact_mod_cast hsenn
    have hsa : ENNReal.ofReal (s : ℝ) < a := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hshi.trans_le (min_le_left a d)
    have hsd : ENNReal.ofReal (s : ℝ) < d := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hshi.trans_le (min_le_right a d)
    have hsb : (s : ℝ≥0∞) ≤ b := by
      simpa only [ENNReal.ofReal_coe_nnreal] using htransfer s hspos hsa hsd
    exact (not_lt_of_ge (le_min hsb (hshi.trans_le (min_le_right a d)).le)) hslo
  apply le_antisymm
  · apply compare
    intro s hs hsR hsD
    have hsec : ∀ q ∈ riemannianBallOf h p s, SectionalBoundedBelowAt h q (-(s ^ 2)⁻¹) :=
      fun q hq => sectionalBoundedBelowAt_of_lt_curvatureRadius h hsR hq
    have hambient :=
      (forall_ball_sectionalBoundedBelowAt_cutPieceMap_iff g D i h hinduced p s (-(s ^ 2)⁻¹)
        hsD).mp hsec
    unfold curvatureRadius
    exact le_iSup_of_le s (le_iSup_of_le hs (le_iSup_of_le hambient le_rfl))
  · apply compare
    intro s hs hsR hsD
    have hsec : ∀ q ∈ riemannianBallOf g (cutPieceMap D i p) s,
        SectionalBoundedBelowAt g q (-(s ^ 2)⁻¹) :=
      fun q hq => sectionalBoundedBelowAt_of_lt_curvatureRadius g hsR hq
    have hcut :=
      (forall_ball_sectionalBoundedBelowAt_cutPieceMap_iff g D i h hinduced p s (-(s ^ 2)⁻¹)
        hsD).mpr hsec
    unfold curvatureRadius
    exact le_iSup_of_le s (le_iSup_of_le hs (le_iSup_of_le hcut le_rfl))

theorem curvatureRadius_cutPieceMap_of_lt_distanceToBoundary
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (p : (D.component i).Carrier)
    (hbelow : curvatureRadius h p < distanceToBoundary (D.component i) h p) :
    curvatureRadius h p = curvatureRadius g (cutPieceMap D i p) := by
  have hmin := min_curvatureRadius_distanceToBoundary_cutPieceMap g D i h hinduced p
  by_cases hambient : curvatureRadius g (cutPieceMap D i p) ≤ distanceToBoundary (D.component i) h p
  · simpa only [min_eq_left hbelow.le, min_eq_left hambient] using hmin
  · rw [min_eq_left hbelow.le, min_eq_right (lt_of_not_ge hambient).le] at hmin
    exact ((ne_of_lt hbelow) hmin).elim

end DifferentialGeometry.Geometry.Collapse
