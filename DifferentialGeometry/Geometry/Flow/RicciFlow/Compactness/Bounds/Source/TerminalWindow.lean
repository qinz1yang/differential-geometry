import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.TerminalWindow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension

set_option autoImplicit false
noncomputable section
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Filter Set DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem StaticTerminalLimit.source_curvature_jets_uniform_on_closed_window
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound) (p : L.space.M)
    {radius : ℝ} (hradius : 0 ≤ radius) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
      ∀ m : ℕ, ∀ t ∈ Set.Icc (-width) 0,
      ∀ x ∈ riemannianClosedBallOf (I := I3) L.space.metric p radius,
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) (X.term (L.subseq i)).S
          m t (L.maps.map i x)) ≤ C m := by
  let width' := (width + depthBound) / 2
  have hww' : width < width' := by dsimp only [width']; linarith
  have hw'd : width' < depthBound := by dsimp only [width']; linarith
  have hw' : 0 < width' := hw.trans hww'
  let tau := (width' - width) / 2
  have htau : 0 < tau := by dsimp only [tau]; linarith
  have hcomplete : RiemannianMetricComplete (I := I3) L.space.metric :=
    ⟨MetricComplete.complete (I := I3) L.space L.complete⟩
  let K := riemannianClosedBallOf (I := I3) L.space.metric p (radius + 1)
  have hK : IsCompact K := hcomplete.closedEBall_isCompact p (radius + 1)
  obtain ⟨B, hB, heq⟩ := L.eventually_metric_uniformly_equivalent_on_compact hK hw' hw'd
  obtain ⟨C₀, hC₀⟩ := L.slab_bounds K hK width' hw' hw'd
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let Kc := Real.sqrt (max C₀ 0) + 1
  have hKc : 0 < Kc := by dsimp only [Kc]; positivity
  have hCK : C₀ ≤ Kc ^ 2 := by
    have hs := Real.sq_sqrt (le_max_right C₀ 0)
    have hn := Real.sqrt_nonneg (max C₀ 0)
    dsimp only [Kc]
    nlinarith [le_max_left C₀ 0]
  let r := 1 / (2 * B)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hrB : r < 1 / B := by
    dsimp only [r]
    exact div_lt_div_of_pos_left zero_lt_one hBp (by linarith)
  let R := r * Real.sqrt Kc
  have hR : 0 < R := mul_pos hr (Real.sqrt_pos.mpr hKc)
  have hrad : R / Real.sqrt Kc = r := by
    dsimp only [R]
    exact mul_div_cancel_right₀ r (Real.sqrt_pos.mpr hKc).ne'
  let C : ℕ → ℝ := fun m => max 0
    (shiLocalUniformBound (Module.finrank ℝ ThreeSpace) m (Kc * tau) R *
      Kc / Real.sqrt tau ^ m)
  refine ⟨C, fun m => le_max_left _ _, ?_⟩
  filter_upwards [heq, hC₀] with i hi hcurv
  have hsource : K ⊆ (L.maps.partialDiffeomorph i).source := hi.1
  have hsub (x : L.space.M)
      (hx : x ∈ riemannianClosedBallOf (I := I3) L.space.metric p radius) :
      riemannianClosedBallOf (I := I3) L.space.metric x 1 ⊆ K := by
    intro y hy
    calc
      riemannianEDistOf (I := I3) L.space.metric p y ≤
          riemannianEDistOf (I := I3) L.space.metric p x +
            riemannianEDistOf (I := I3) L.space.metric x y :=
        riemannianEDistOf_triangle L.space.metric p x y
      _ ≤ ENNReal.ofReal radius + ENNReal.ofReal 1 := add_le_add hx hy
      _ = ENNReal.ofReal (radius + 1) := (ENNReal.ofReal_add hradius zero_le_one).symm
  have hcpt (s : ℝ) (hs : s ∈ Set.Icc (-width') 0)
      (x : L.space.M) (hx : x ∈ riemannianClosedBallOf (I := I3) L.space.metric p radius) :
      IsCompact (riemannianClosedBallOf (I := I3)
        ((X.term (L.subseq i)).S.base.metric s) (L.maps.map i x) r) ∧
      riemannianClosedBallOf (I := I3) ((X.term (L.subseq i)).S.base.metric s)
        (L.maps.map i x) r ⊆ (L.maps.partialDiffeomorph i) '' K := by
    have hball := hcomplete.closedEBall_isCompact x 1
    have hsmall := hsub x hx
    have himage : IsCompact ((L.maps.partialDiffeomorph i) ''
        riemannianClosedBallOf (I := I3) L.space.metric x 1) :=
      hball.image_of_continuousOn
        ((L.maps.partialDiffeomorph i).contMDiffOn_toFun.continuousOn.mono (hsmall.trans hsource))
    have hcap := closedBall_subset_image_of_metric_lower L.space.metric
      ((X.term (L.subseq i)).S.base.metric s) (L.maps.partialDiffeomorph i) x
      zero_lt_one hBp hrB hball (hsmall.trans hsource) (fun y hy v => by
        have hh := (hi.2 s hs y (hsmall hy) v).1
        have hmul := mul_le_mul_of_nonneg_left hh hBp.le
        rw [← mul_assoc, mul_inv_cancel₀ hBp.ne', one_mul] at hmul
        have hnn : 0 ≤ ((X.term (L.subseq i)).S.base.metric s).inner
            (L.maps.map i y) (mfderiv I3 I3 (L.maps.map i) y v)
            (mfderiv I3 I3 (L.maps.map i) y v) := by
          let g := (X.term (L.subseq i)).S.base.metric s
          let z : (X.term (L.subseq i)).M := L.maps.map i y
          let w : TangentSpace I3 z := mfderiv I3 I3 (L.maps.map i) y v
          change 0 ≤ g.inner z w w
          by_cases hw : w = 0
          · rw [hw]
            simp only [map_zero, le_refl]
          · exact (g.pos z w hw).le
        exact hmul.trans (mul_le_mul_of_nonneg_right (by nlinarith : B ≤ B ^ 2) hnn))
    refine ⟨himage.of_isClosed_subset ?_ hcap, hcap.trans (Set.image_mono hsmall)⟩
    exact isClosed_le
      (continuous_riemannianEDist ((X.term (L.subseq i)).S.base.metric s) (L.maps.map i x))
      continuous_const
  have hbound (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ico (-width) 0)
      (x : L.space.M) (hx : x ∈ riemannianClosedBallOf (I := I3) L.space.metric p radius) :
      Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) (X.term (L.subseq i)).S
        m t (L.maps.map i x)) ≤ C m := by
    have hstart : t - tau ∈ Set.Icc (-width') 0 := by
      dsimp only [tau]
      constructor <;> linarith [ht.1, ht.2]
    have hshi := shi_bound_on_sliding_regular_window
      (X.term (L.subseq i)).S (X.term (L.subseq i)).isSolution
      (show -width' < 0 by linarith) htau hKc hR
      (L.window_subset_carrier hw'd.le (L.subseq i))
      (L.open_window_subset_regular hw'd.le (L.subseq i))
      (show t ∈ Set.Ioo (-width' + tau) 0 from
        ⟨by dsimp only [tau]; linarith [ht.1], ht.2⟩) (L.maps.map i x)
      (by simpa only [hrad, riemannianClosedBallOf] using (hcpt _ hstart x hx).1)
      (by
        intro s hs y hy
        have hy' : y ∈ riemannianClosedBallOf (I := I3)
            ((X.term (L.subseq i)).S.base.metric (t - tau)) (L.maps.map i x) r := by
          simpa only [hrad, riemannianClosedBallOf, Set.mem_ofPred_eq] using hy
        obtain ⟨y, hyK, rfl⟩ := (hcpt _ hstart x hx).2 hy'
        have hh := (hcurv s ⟨hstart.1.trans hs.1, hs.2.trans ht.2.le⟩ y hyK).trans hCK
        simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero,
          PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04] using hh)
      m (L.maps.map i x) (by erw [riemannianEDistOf_self]; exact bot_le)
    exact hshi.trans (le_max_right _ _)
  intro m t ht x hx
  by_cases ht0 : t = 0
  · subst t
    have hc := solution_nablaKRm04NormSqIntrinsic_continuousWithinAt_terminal
      (X.term (L.subseq i)).S (X.term (L.subseq i)).isSolution
      (show -width' < 0 by linarith) (L.window_subset_carrier hw'd.le (L.subseq i))
      (L.open_window_subset_regular hw'd.le (L.subseq i)) m (L.maps.map i x)
    apply le_of_tendsto ((hc.mono Set.Iio_subset_Iic_self).sqrt)
    filter_upwards [Ioo_mem_nhdsLT (show -width < (0 : ℝ) by linarith)] with s hs
    exact hbound m s ⟨hs.1.le, hs.2⟩ x hx
  · exact hbound m t ⟨ht.1, lt_of_le_of_ne ht.2 ht0⟩ x hx

theorem StaticTerminalLimit.source_curvature_jets_uniform_on_compact
    {X : FlowSequence.{u}} {depthBound : ℝ} (L : StaticTerminalLimit X depthBound)
    {width : ℝ} (hw : 0 < width) (hwd : width < depthBound)
    {K : Set L.space.M} (hK : IsCompact K) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧ ∀ᶠ i in atTop,
      ∀ m : ℕ, ∀ t ∈ Set.Icc (-width) 0, ∀ x ∈ K,
        Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) (X.term (L.subseq i)).S
          m t (L.maps.map i x)) ≤ C m := by
  let : ConnectedSpace L.space.M := L.connected
  let p := L.space.basepoint
  let d : L.space.M → ℝ := fun x => (riemannianEDistOf (I := I3) L.space.metric p x).toReal
  have hd : Continuous d := continuous_iff_continuousAt.mpr fun x =>
    (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top L.space.metric p x)).comp
      (continuous_riemannianEDist L.space.metric p).continuousAt
  obtain ⟨R, hR⟩ := hK.bddAbove_image hd.continuousOn
  have hsub : K ⊆ riemannianClosedBallOf (I := I3) L.space.metric p (max R 0) := by
    intro x hx
    exact (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top L.space.metric p x)
      (le_max_right R 0)).mpr ((hR (Set.mem_image_of_mem d hx)).trans (le_max_left R 0))
  obtain ⟨C, hC, hbound⟩ := L.source_curvature_jets_uniform_on_closed_window
    hw hwd p (le_max_right R 0)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with i hi
  exact fun m t ht x hx => hi m t ht x (hsub hx)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
