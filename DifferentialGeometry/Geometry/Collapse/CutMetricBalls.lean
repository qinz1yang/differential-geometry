import DifferentialGeometry.Geometry.Collapse.CutMetricTransport
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem image_riemannianBallOf_cutPieceMap
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (p : (D.component i).Carrier) (r : ℝ)
    (hboundary : ENNReal.ofReal r < distanceToBoundary (D.component i) h p) :
    cutPieceMap D i '' riemannianBallOf h p r =
      riemannianBallOf g (cutPieceMap D i p) r := by
  by_cases hrpos : 0 < r
  · obtain ⟨R, hrR, hRD⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hboundary
    have hRpos : 0 < (R : ℝ) := by
      have hRenn : (0 : ℝ≥0∞) < R := (ENNReal.ofReal_pos.mpr hrpos).trans hrR
      exact_mod_cast hRenn
    have hrRreal : r < (R : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hRpos).mp (by
        simpa only [ENNReal.ofReal_coe_nnreal] using hrR)
    have hRboundary : ENNReal.ofReal (R : ℝ) < distanceToBoundary (D.component i) h p := by
      simpa only [ENNReal.ofReal_coe_nnreal] using hRD
    let U := (D.component i).interior
    have hsub : riemannianClosedBallOf h p (R : ℝ) ⊆ (U : Set (D.component i).Carrier) := by
      intro q hq
      by_contra hqi
      change ¬ (D.component i).model.IsInteriorPoint q at hqi
      have hqb : q ∈ (D.component i).model.boundary (D.component i).Carrier :=
        ((D.component i).model.isBoundaryPoint_iff_not_isInteriorPoint q).mpr hqi
      have hdle : distanceToBoundary (D.component i) h p ≤ riemannianEDistOf h p q := by
        unfold distanceToBoundary
        exact iInf_le _ (⟨q, hqb⟩ : (D.component i).model.boundary (D.component i).Carrier)
      exact (not_lt_of_ge (hdle.trans hq)) hRboundary
    have hpU : p ∈ U := hsub (by
      change riemannianEDistOf h p p ≤ ENNReal.ofReal (R : ℝ)
      rw [riemannianEDistOf_self]
      exact bot_le)
    have hlocal : IsLocalDiffeomorphOn (D.component i).model (𝓡 3) ∞
        (cutPieceMap D i) (U : Set (D.component i).Carrier) := by
      intro x
      exact isLocalDiffeomorphAt_of_comp
        (f := (Subtype.val : U → (D.component i).Carrier)) (g := cutPieceMap D i)
        (isLocalDiffeomorph_cutPieceMap_interior D i x)
        (isLocalDiffeomorph_subtype_val U x)
    obtain ⟨Φ, hΦsource, _, hΦfun⟩ :=
      DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
        hlocal U.isOpen ⟨p, hpU⟩ (injOn_cutPieceMap_interior D i)
    have hΦmap : (Φ : (D.component i).Carrier → M.Carrier) = cutPieceMap D i := hΦfun
    have hΦder (z : (D.component i).Carrier) :
        mfderiv (D.component i).model (𝓡 3)
          (Φ.toPartialEquiv : (D.component i).Carrier → M.Carrier) z =
        mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) z :=
      mfderiv_congr (I := (D.component i).model) (I' := 𝓡 3) (x := z) hΦmap
    have hcpt : IsCompact (riemannianClosedBallOf h p (R : ℝ)) :=
      (Geometry.Metric.isClosed_riemannianClosedBallOf h p (R : ℝ)).isCompact
    have hsource : riemannianClosedBallOf h p (R : ℝ) ⊆ Φ.source := by
      rw [hΦsource]
      exact hsub
    have hupper : ∀ z ∈ riemannianClosedBallOf h p (R : ℝ),
        ∀ v : TangentSpace (D.component i).model z,
        g.inner (Φ z) (mfderiv (D.component i).model (𝓡 3) Φ z v)
          (mfderiv (D.component i).model (𝓡 3) Φ z v) ≤ (1 : ℝ) ^ 2 * h.inner z v v := by
      intro z _ v
      rw [hΦder z, congrFun hΦmap z, one_pow, one_mul]
      exact (hinduced z v v).ge
    have hlower : ∀ z ∈ riemannianClosedBallOf h p (R : ℝ),
        ∀ v : TangentSpace (D.component i).model z,
        h.inner z v v ≤ (1 : ℝ) ^ 2 *
          g.inner (Φ z) (mfderiv (D.component i).model (𝓡 3) Φ z v)
            (mfderiv (D.component i).model (𝓡 3) Φ z v) := by
      intro z _ v
      rw [hΦder z, congrFun hΦmap z, one_pow, one_mul]
      exact (hinduced z v v).le
    apply Set.Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hxR : riemannianEDistOf h p x < ENNReal.ofReal (R : ℝ) :=
        hx.trans ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hrRreal)
      have hle := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
        h g Φ p x hRpos (show (0 : ℝ) < 1 by norm_num) hsource hupper hxR
      have hle' : riemannianEDistOf g (cutPieceMap D i p) (cutPieceMap D i x) ≤
          riemannianEDistOf h p x := by
        simpa only [hΦmap, ENNReal.ofReal_one, one_mul] using hle
      exact hle'.trans_lt hx
    · intro y hy
      have hfin : riemannianEDistOf g (cutPieceMap D i p) y ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy.le
      let d := (riemannianEDistOf g (cutPieceMap D i p) y).toReal
      have hd : 0 ≤ d := ENNReal.toReal_nonneg
      have hdr : d < r := ENNReal.toReal_lt_of_lt_ofReal hy
      have hdeq : ENNReal.ofReal d = riemannianEDistOf g (cutPieceMap D i p) y :=
        ENNReal.ofReal_toReal hfin
      have hyΦ : y ∈ riemannianClosedBallOf g (Φ p) d := by
        change riemannianEDistOf g (Φ p) y ≤ ENNReal.ofReal d
        rw [hΦmap, hdeq]
      obtain ⟨hyt, hxd⟩ := PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
        h g Φ p hd (show (0 : ℝ) < 1 by norm_num)
        (by simpa only [one_mul] using hdr.trans hrRreal) hcpt hsource hlower y hyΦ
      refine ⟨Φ.symm y, ?_, ?_⟩
      · have hxd' : riemannianEDistOf h p (Φ.symm y) ≤ ENNReal.ofReal d := by
          change riemannianEDistOf h p (Φ.symm y) ≤ ENNReal.ofReal (1 * d) at hxd
          simpa only [one_mul] using hxd
        exact hxd'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hdr)
      · have hright : Φ (Φ.symm y) = y := Φ.right_inv' hyt
        simpa only [hΦmap] using hright
  · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
    simp [riemannianBallOf, ENNReal.ofReal_eq_zero.mpr hrnonpos]

end DifferentialGeometry.Geometry.Collapse
