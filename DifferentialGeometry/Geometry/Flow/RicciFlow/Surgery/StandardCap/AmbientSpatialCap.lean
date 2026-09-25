import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowSpatialCap
import DifferentialGeometry.Geometry.Neck.SpatialIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.WindowRadius

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private local instance (V : Opens ThreeSpace) : SigmaCompactSpace V :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel V.isOpen)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]

theorem exists_spatial_cap_frontier_of_window_metric_close
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    {s : ℝ} (hs : s ∈ Ioo (-eps⁻¹) eps⁻¹)
    (g : SmoothRiemannianMetric (𝓡 3) (standardCapWindow D))
    (h : SmoothRiemannianMetric I3 M)
    (Φ : standardCapWindow D → M) (hΦ : IsLocalDiffeomorph I3 I3 ∞ Φ)
    (hinj : Injective Φ)
    (hmetric : ∀ (x : standardCapWindow D) (v w : TangentSpace I3 x),
      g.inner x v w = h.inner (Φ x) (mfderiv I3 I3 Φ x v) (mfderiv I3 I3 Φ x w))
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 40000) (hηeps : 20000 * η ≤ eps)
    (hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹}
      ⌈eps⁻¹⌉₊ g (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η) :
    ∃ (p z : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ z.val = 0 ∧
      ∃ (nk : SpatialNeck h eps (Φ p)) (K : CompactDomain M),
        K.carrier = Φ '' {x : standardCapWindow D | ‖x.val‖ ≤ r+s} ∧
        Nonempty (CapCore K.carrier) ∧ Φ z ∈ interior K.carrier ∧
        (∀ x : standardCapWindow D, ‖x.val‖ < r+s → Φ x ∈ interior K.carrier) ∧
        (∀ w : neckBuffer eps, ∃ x : standardCapWindow D,
          x.val = (r+w.val.2) • (w.val.1 : ThreeSpace) ∧ nk.map w.val = Φ x) ∧
        frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,s)) ∧
        IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,s)) ∧
        (∀ q : Sphere 2, ∀ t : ℝ, s+t ∈ Ioo (-eps⁻¹) eps⁻¹ →
          (nk.map (q,s+t) ∈ K.carrier ↔ t ≤ 0)) ∧
        |metricScalarAt h (Φ p) - 1| ≤ 4323 * η ∧
        K.carrier ⊆ riemannianBallOf h (Φ z) (2*(r+s)) := by
  obtain ⟨p,z,hp,hz,old,K0,hK0,hmodel,hcenter,hmap,hfront,_,hside,hscalar⟩ :=
    exists_window_spatial_cap_frontier_of_metric_close D r eps heps hsmall hr hfit hs
      g hη hηsmall hηeps hclose
  obtain ⟨nk,_,hnk,_⟩ := old.exists_image_of_local_isometry Φ hΦ hinj hmetric
  obtain ⟨F,hsource,_,hF⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun x : (univ : Set (standardCapWindow D)) => hΦ x.val) isOpen_univ
    (show (univ : Set (standardCapWindow D)).Nonempty from ⟨z,mem_univ _⟩) hinj.injOn
  have hKsource : K0.carrier ⊆ F.source := hsource ▸ subset_univ _
  let K := K0.map F hKsource
  have hK : K.carrier = Φ '' K0.carrier := by
    change F '' K0.carrier = _
    rw [hF]
  have hnkeq : ∀ q t, nk.map (q,t) = Φ (old.map (q,t)) := fun q t => hnk (q,t)
  refine ⟨p,z,hp,hz,nk,K,hK.trans (congrArg (fun V => Φ '' V) hK0),?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hrs : 0 < r+s := by linarith [transitionEnd_pos,hs.1]
    let dil := (LinearEquiv.smulOfNeZero ℝ ThreeSpace (r+s)
      hrs.ne').toContinuousLinearEquiv.toDiffeomorph
    let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
      (I := I3) (standardCapWindow D) ⟨z⟩
    have hinc : inc.target = (standardCapWindow D : Set ThreeSpace) :=
      (standardCapWindow D).openPartialHomeomorphSubtypeCoe_target ⟨z⟩
    let B := dil.toPartialDiffeomorph.trans inc.symm
    have hballD : Metric.closedBall (0 : ThreeSpace) (r+s) ⊆ standardCapWindow D := by
      intro y hy
      have hn : ‖y‖ ≤ r+s := by simpa only [Metric.mem_closedBall,dist_zero_right,mem_ofPred_eq]
        using hy
      change ‖y‖ < D+1
      linarith [hs.2]
    have hdil : dil '' Metric.closedBall (0 : ThreeSpace) 1 =
        Metric.closedBall (0 : ThreeSpace) (r+s) := by
      change (fun y : ThreeSpace => (r+s) • y) '' Metric.closedBall 0 1 = _
      rw [Set.image_smul,smul_closedBall' hrs.ne']
      simp only [smul_zero,Real.norm_eq_abs,abs_of_pos hrs,mul_one]
    have hBsource : Metric.closedBall (0 : ThreeSpace) 1 ⊆ B.source := by
      intro y hy
      refine ⟨mem_univ _,?_⟩
      change dil y ∈ inc.target
      rw [hinc]
      exact hballD (hdil ▸ mem_image_of_mem dil hy)
    have hBimage : B '' Metric.closedBall (0 : ThreeSpace) 1 = K0.carrier := by
      rw [hK0]
      ext y
      constructor
      · rintro ⟨a,ha,rfl⟩
        have haD := hballD (hdil ▸ mem_image_of_mem dil ha)
        change ‖(inc.symm (dil a)).val‖ ≤ r+s
        have he : (inc.symm (dil a)).val = dil a := by
          exact inc.right_inv' (hinc.symm ▸ haD)
        rw [he]
        have hm : dil a ∈ Metric.closedBall (0 : ThreeSpace) (r+s) :=
          hdil ▸ mem_image_of_mem dil ha
        simpa only [Metric.mem_closedBall,dist_zero_right] using hm
      · intro hy
        have hyball : y.val ∈ Metric.closedBall (0 : ThreeSpace) (r+s) := by
          simpa only [Metric.mem_closedBall,dist_zero_right,mem_ofPred_eq] using hy
        obtain ⟨a,ha,hea⟩ := hdil.symm ▸ hyball
        refine ⟨a,ha,?_⟩
        change inc.symm (dil a) = y
        rw [hea]
        exact inc.left_inv' (mem_univ y)
    change Nonempty (CapCore (F '' K0.carrier))
    refine ⟨CapCore.ball (B.trans F) (fun y hy => ⟨hBsource hy,?_⟩) ?_⟩
    · exact hKsource (hBimage ▸ mem_image_of_mem B hy)
    · change (F ∘ B) '' Metric.closedBall (0 : ThreeSpace) 1 = F '' K0.carrier
      exact (Set.image_image (f := B) (g := F) (s := Metric.closedBall (0 : ThreeSpace)
        1)).symm.trans
        (congrArg (fun V => F '' V) hBimage)
  · rw [hK,← show F '' interior K0.carrier = interior (Φ '' K0.carrier) from by
      simpa only [hF] using K0.image_interior F hKsource]
    exact ⟨z,hcenter,congrFun hF z⟩
  · intro x hx
    have hxint : x ∈ interior K0.carrier := by
      rw [hK0]
      let O : Set (standardCapWindow D) := {y | ‖y.val‖ < r+s}
      have hO : IsOpen O := isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
      exact mem_interior.mpr ⟨O,(fun y hy => show ‖y.val‖ ≤ r+s from hy.le),hO,hx⟩
    change Φ x ∈ interior (F '' K0.carrier)
    rw [← K0.image_interior F hKsource]
    exact ⟨x,hxint,congrFun hF x⟩
  · intro w
    exact ⟨old.map w.val,hmap w,hnk w.val⟩
  · change frontier (F '' K0.carrier) = _
    rw [← K0.image_frontier F hKsource,hfront,hF]
    ext y
    constructor
    · rintro ⟨x,⟨q,rfl⟩,rfl⟩
      exact ⟨q,hnkeq q s⟩
    · rintro ⟨q,rfl⟩
      exact ⟨old.map (q,s),mem_range_self q,(hnkeq q s).symm⟩
  · exact nk.isSmoothEmbedding_level (abs_lt.mpr hs)
  · intro q t ht
    rw [hK,hnkeq,hinj.mem_set_image]
    exact hside q t ht
  · have hsc := (curvature_of_injective_local_isometry g h Φ hΦ hinj hmetric p).1
    rwa [hsc] at hscalar
  · have hrs : 0 < r+s := by linarith [transitionEnd_pos,hs.1]
    have hR : r+s < r+eps⁻¹ := by linarith [hs.2]
    have hRD : r+eps⁻¹ < D := by linarith
    have hnorm : ∀ x : standardCapWindow D, ‖x.val‖ ≤ r+eps⁻¹ →
        metricDerivNorm 0 g (metric.restrictOpen (standardCapWindow D))
          (metric.restrictOpen (standardCapWindow D)) x ≤ 1 := by
      intro x hx
      have hh := metricDerivNorm_lt_of_sup_lt _ _ _ _ _ hclose (Nat.zero_le _) hx
      exact hh.le.trans (by linarith)
    obtain ⟨z',hz',hball⟩ := window_image_closedBall_subset_ball_of_metric_close
      h hrs hR hRD Φ hΦ hinj g hmetric hnorm
    have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
    rw [hzz] at hball
    rw [hK,hK0]
    exact hball


universe u

theorem eventually_spatial_cap_frontier_of_metric_cp_convergence
    (D r eps : ℝ) (heps : 0 < eps) (hsmall : eps < 1 / 11)
    (hr : transitionEnd + eps⁻¹ + 1 < r) (hfit : r + eps⁻¹ + 1 ≤ D)
    (N : ℕ) (hN : ⌈eps⁻¹⌉₊ ≤ N)
    (g : ℕ → SmoothRiemannianMetric I3 (standardCapWindow D))
    (hconv : MetricCPConvergenceOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹} N g
      (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)))
    (P : ℕ → Type u) [∀ n, TopologicalSpace (P n)] [∀ n, ChartedSpace ThreeSpace (P n)]
    [∀ n, IsManifold I3 ∞ (P n)] [∀ n, T2Space (P n)]
    (h : ∀ n, SmoothRiemannianMetric I3 (P n))
    (Φ : ∀ n, standardCapWindow D → P n)
    (hΦ : ∀ n, IsLocalDiffeomorph I3 I3 ∞ (Φ n)) (hinj : ∀ n, Injective (Φ n))
    (hmetric : ∀ n (x : standardCapWindow D) (v w : TangentSpace I3 x),
      (g n).inner x v w = (h n).inner (Φ n x)
        (mfderiv I3 I3 (Φ n) x v) (mfderiv I3 I3 (Φ n) x w)) :
    ∀ᶠ n in Filter.atTop,
      ∃ (p z : standardCapWindow D), p.val = r • (spherePoint : ThreeSpace) ∧ z.val = 0 ∧
        ∃ (nk : SpatialNeck (h n) eps (Φ n p)) (K : CompactDomain (P n)),
          K.carrier = Φ n '' {x : standardCapWindow D | ‖x.val‖ ≤ r} ∧
          Nonempty (CapCore K.carrier) ∧ Φ n z ∈ interior K.carrier ∧
          (∀ x : standardCapWindow D, ‖x.val‖ ≤ transitionEnd →
            Φ n x ∈ interior K.carrier) ∧
          (∀ w : neckBuffer eps, ∃ x : standardCapWindow D,
            x.val = (r+w.val.2) • (w.val.1 : ThreeSpace) ∧ nk.map w.val = Φ n x) ∧
          frontier K.carrier = range (fun q : Sphere 2 => nk.map (q,0)) ∧
          IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere 2 => nk.map (q,0)) ∧
          (∀ q : Sphere 2, ∀ t : ℝ, t ∈ Ioo (-eps⁻¹) eps⁻¹ →
            (nk.map (q,t) ∈ K.carrier ↔ t ≤ 0)) ∧
          |metricScalarAt (h n) (Φ n p) - 1| ≤ eps ∧
          K.carrier ⊆ riemannianBallOf (h n) (Φ n z) (2*r) := by
  let η : ℝ := min (1 / 40000) (eps / 20000) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηsmall : η ≤ 1 / 40000 := by
    have h := min_le_left (1 / 40000 : ℝ) (eps / 20000)
    dsimp [η]
    linarith
  have hηeps : 20000 * η ≤ eps := by
    have h := min_le_right (1 / 40000 : ℝ) (eps / 20000)
    dsimp [η]
    linarith
  have hK : IsCompact {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹} := by
    have hc : IsCompact {x : ThreeSpace | ‖x‖ ≤ r+eps⁻¹} := by
      simpa only [Metric.closedBall, dist_zero_right] using
        isCompact_closedBall (0 : ThreeSpace) (r+eps⁻¹)
    exact _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' hc (by
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change ‖x‖ < D+1
      change ‖x‖ ≤ r+eps⁻¹ at hx
      linarith)
  obtain ⟨n₀, hn₀⟩ := hconv η hη
  refine Filter.eventually_atTop.mpr ⟨n₀, ?_⟩
  intro n hn
  have hclose : metricDerivENormSupOn {x : standardCapWindow D | ‖x.val‖ ≤ r+eps⁻¹}
      ⌈eps⁻¹⌉₊ (g n) (metric.restrictOpen (standardCapWindow D))
      (metric.restrictOpen (standardCapWindow D)) < ENNReal.ofReal η := by
    apply (metricDerivENormSupOn_mono (subset_refl _) hN (g n) _ _).trans_lt
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact hK]
    exact (ENNReal.ofReal_lt_ofReal_iff hη).mpr (hn₀ n hn)
  have hs : (0 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr heps), inv_pos.mpr heps⟩
  obtain ⟨p,z,hp,hz,nk,K,hcarrier,hcap,hzero,hinterior,hmap,hfront,hemb,hside,hscalar,hball⟩ :=
    exists_spatial_cap_frontier_of_window_metric_close D r eps heps hsmall hr hfit hs
      (g n) (h n) (Φ n) (hΦ n) (hinj n) (hmetric n) hη hηsmall hηeps hclose
  refine ⟨p,z,hp,hz,nk,K,?_,hcap,hzero,?_,hmap,hfront,hemb,?_,?_,?_⟩
  · simpa only [add_zero] using hcarrier
  · intro x hx
    apply hinterior x
    linarith [inv_pos.mpr heps]
  · simpa only [zero_add] using hside
  · exact hscalar.trans (by linarith)
  · simpa only [add_zero] using hball

end DifferentialGeometry.PDE.RicciFlow.StandardCap
