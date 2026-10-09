import DifferentialGeometry.Geometry.Collapse.CutMetricBalls
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open GC.Endpoint GC.Topology Set MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

theorem ballVolume_cutPieceMap
    {M : ConnectedClosedOrientedManifold.{u} 3}
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hinduced : isInducedCutMetric g D i h)
    (p : (D.component i).Carrier) (r : ℝ)
    (hboundary : ENNReal.ofReal r < distanceToBoundary (D.component i) h p) :
    ballVolume h p r = ballVolume g (cutPieceMap D i p) r := by
  by_cases hrpos : 0 < r
  · let U := (D.component i).interior
    have hsub : riemannianBallOf h p r ⊆ (U : Set (D.component i).Carrier) := by
      intro q hq
      by_contra hqi
      change ¬ (D.component i).model.IsInteriorPoint q at hqi
      have hqb : q ∈ (D.component i).model.boundary (D.component i).Carrier :=
        ((D.component i).model.isBoundaryPoint_iff_not_isInteriorPoint q).mpr hqi
      have hdle : distanceToBoundary (D.component i) h p ≤ riemannianEDistOf h p q := by
        unfold distanceToBoundary
        exact iInf_le _ (⟨q, hqb⟩ : (D.component i).model.boundary (D.component i).Carrier)
      exact (not_lt_of_ge hdle) (hq.trans hboundary)
    have hpU : p ∈ U := hsub (by
      change riemannianEDistOf h p p < ENNReal.ofReal r
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrpos)
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
    have hsource : riemannianBallOf h p r ⊆ Φ.source := by
      rw [hΦsource]
      exact hsub
    have himage : (Φ : (D.component i).Carrier → M.Carrier) '' riemannianBallOf h p r =
        riemannianBallOf g (cutPieceMap D i p) r := by
      simpa only [hΦfun] using
        image_riemannianBallOf_cutPieceMap g D i h hinduced p r hboundary
    have htarget : riemannianBallOf g (cutPieceMap D i p) r ⊆ Φ.target := by
      rw [← himage]
      rintro y ⟨x, hx, rfl⟩
      exact Φ.map_source' (hsource hx)
    have hinverse : (Φ.symm : M.Carrier → (D.component i).Carrier) ''
        riemannianBallOf g (cutPieceMap D i p) r = riemannianBallOf h p r := by
      rw [← himage]
      ext q
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        have hleft : (Φ.symm : M.Carrier → (D.component i).Carrier)
            ((Φ : (D.component i).Carrier → M.Carrier) x) = x :=
          Φ.left_inv' (hsource hx)
        rw [hleft]
        exact hx
      · intro hq
        exact ⟨Φ q, ⟨q, hq, rfl⟩, Φ.left_inv' (hsource hq)⟩
    have hforward (x : (D.component i).Carrier)
        (v w : TangentSpace (D.component i).model x) :
        h.inner x v w = g.inner (Φ x)
          (mfderiv (D.component i).model (𝓡 3) Φ x v)
          (mfderiv (D.component i).model (𝓡 3) Φ x w) := by
      have hΦmap : (Φ : (D.component i).Carrier → M.Carrier) = cutPieceMap D i := hΦfun
      have hΦder :
          mfderiv (D.component i).model (𝓡 3)
            (Φ.toPartialEquiv : (D.component i).Carrier → M.Carrier) x =
          mfderiv (D.component i).model (𝓡 3) (cutPieceMap D i) x :=
        mfderiv_congr (I := (D.component i).model) (I' := 𝓡 3) (x := x) hΦmap
      rw [hΦder, congrFun hΦmap x]
      exact hinduced x v w
    let Ψ := PartialDiffeomorph.ofLE Φ.symm
      (by norm_num : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    have hmetric : ∀ y ∈ Ψ.source, ∀ v w,
        g.inner y v w = h.inner (Ψ y)
          (mfderiv (𝓡 3) (D.component i).model Ψ y v)
          (mfderiv (𝓡 3) (D.component i).model Ψ y w) := by
      intro y hy v w
      change y ∈ Φ.target at hy
      change g.inner y v w = h.inner (Φ.symm y)
        (mfderiv (𝓡 3) (D.component i).model Φ.symm y v)
        (mfderiv (𝓡 3) (D.component i).model Φ.symm y w)
      have heq : (Φ : (D.component i).Carrier → M.Carrier) ∘ Φ.symm =ᶠ[𝓝 y] id := by
        filter_upwards [Φ.open_target.mem_nhds hy] with z hz
        exact Φ.right_inv' hz
      have hchain (z : TangentSpace (𝓡 3) y) :
          mfderiv (D.component i).model (𝓡 3) Φ (Φ.symm y)
            (mfderiv (𝓡 3) (D.component i).model Φ.symm y z) = z := by
        have hd := (mfderiv_comp y
          (Φ.mdifferentiableAt (by simp) (Φ.map_target' hy))
          (Φ.symm.mdifferentiableAt (by simp) hy)).symm.trans heq.mfderiv_eq
        have hz := DFunLike.congr_fun hd z
        rw [mfderiv_id] at hz
        change mfderiv (D.component i).model (𝓡 3) Φ (Φ.symm y)
          (mfderiv (𝓡 3) (D.component i).model Φ.symm y z) = z at hz
        exact hz
      have hpull := hforward (Φ.symm y)
        (mfderiv (𝓡 3) (D.component i).model Φ.symm y v)
        (mfderiv (𝓡 3) (D.component i).model Φ.symm y w)
      rw [hchain v, hchain w] at hpull
      have hpoint : g.inner (Φ (Φ.symm y)) v w = g.inner y v w :=
        congrArg (fun z : M.Carrier => g.inner z
          (show EuclideanSpace ℝ (Fin 3) from v) (show EuclideanSpace ℝ (Fin 3) from w))
          (Φ.right_inv' hy)
      exact hpoint.symm.trans hpull.symm
    let : MeasurableSpace M.Carrier := borel M.Carrier
    let : BorelSpace M.Carrier := ⟨rfl⟩
    have hmeas : MeasurableSet (riemannianBallOf g (cutPieceMap D i p) r) :=
      (isOpen_lt (Riemannian.continuous_riemannianEDist g (cutPieceMap D i p))
        continuous_const).measurableSet
    have hvolume := riemannianVolumeMeasure_image_of_partialIsometry g h Ψ hmetric
      hmeas htarget
    change ballVolume g (cutPieceMap D i p) r =
      riemannianVolumeMeasure (D.component i).model (D.component i).Carrier h
        ((Φ.symm : M.Carrier → (D.component i).Carrier) ''
          riemannianBallOf g (cutPieceMap D i p) r) at hvolume
    rw [hinverse] at hvolume
    exact hvolume.symm
  · have hrnonpos : r ≤ 0 := le_of_not_gt hrpos
    simp [ballVolume, riemannianBallOf, ENNReal.ofReal_eq_zero.mpr hrnonpos]

end DifferentialGeometry.Geometry.Collapse
