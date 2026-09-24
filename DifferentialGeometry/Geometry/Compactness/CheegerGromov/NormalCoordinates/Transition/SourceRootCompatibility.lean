import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.NormalCoordinates.RootCompatibility
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Transition.ReceivingCoordinates
import DifferentialGeometry.Geometry.Exponential.NormalBall.DiagonalInverseBranch
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.IntrinsicDistance
import DifferentialGeometry.Geometry.Exponential.NormalBall.Recenter
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.RecenterConvergence
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallChartMetric

noncomputable section
open Bundle Filter Manifold Set
open scoped ContDiff Manifold Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type*}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)]
  [∀ k, IsManifold I ∞ (M k)] [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [∀ k, RiemannianBundle (fun x : M k ↦ TangentSpace I x)]
  [∀ k, PseudoEMetricSpace (M k)] [∀ k, IsRiemannianManifold I (M k)]
  [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k ↦ TangentSpace I x)]

theorem IntrinsicBallChart.eventually_eqOn_recentered_hom_of_invVelocity_roots
    (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k, IsMetricNorm (I := I) (M := M k) (g k))
    (p q : ∀ k, M k) {rho : ℝ} (hrho : 0 < rho)
    (c : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (p k) rho)
    (d : ∀ k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (q k) rho)
    (hell₁ : ∀ k, ∀ z ∈ Metric.ball (0 : E) rho, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (p k) z v v ≤ 2 * ‖v‖ ^ 2)
    (hell₂ : ∀ k, ∀ z ∈ Metric.ball (0 : E) rho, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (q k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (q k) z v v ≤ 2 * ‖v‖ ^ 2)
    (hnear : ∀ᶠ k in atTop, edist (q k) (p k) < ENNReal.ofReal (rho / 4))
    {J : E → E}
    (hJ : MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (rho / 2))
      (fun k => ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).transition
        ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho)) J)
    (hJc : ContinuousOn J (Metric.ball (0 : E) (rho / 2)))
    (a b : E) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hball₁ : ∀ k, Metric.ball a r₁ ⊆ Metric.ball (0 : E)
      ((c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho).radius)
    (hball₂ : ∀ k, Metric.ball b r₂ ⊆ Metric.ball (0 : E)
      ((d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho).radius) :
    let nc := fun k => (c k).toNormalBallChart (g k) (hEnorm k) (p k) hrho
    let nd := fun k => (d k).toNormalBallChart (g k) (hEnorm k) (q k) hrho
    let cc := fun k => (nc k).recenter a hr₁ (hball₁ k)
    let dd := fun k => (nd k).recenter b hr₂ (hball₂ k)
    ∀ (e₁ e₂ : ℕ → OpenPartialHomeomorph (E × E) (E × E))
      (q₁ q₂ qInner ε₁ ε₂ rTube : ℝ), 0 < q₁ → 0 < q₂ → qInner < q₁ → 0 < rTube →
      (∀ k, (e₁ k).source = Metric.ball (0 : E × E) q₁ ∧ e₁ k 0 = 0 ∧
        Metric.closedBall (0 : E × E) ε₁ ⊆ (e₁ k).target ∧
        ContDiffOn ℝ ∞ ((e₁ k).symm : E × E → E × E) (e₁ k).target ∧
        (∀ z ∈ (e₁ k).source,
          (cc k).pair (e₁ k z) = Exponential.diagExp (g k) (hEnorm k) ((cc k).tangent z)) ∧
        ∀ z ∈ (e₁ k).source,
          z.1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e₁ k z).1 ∈ Metric.ball (0 : E) (cc k).radius ∧
          (e₁ k z).2 ∈ Metric.ball (0 : E) (cc k).radius) →
      (∀ k, (e₂ k).source = Metric.ball (0 : E × E) q₂ ∧ e₂ k 0 = 0 ∧
        Metric.closedBall (0 : E × E) ε₂ ⊆ (e₂ k).target ∧
        ContDiffOn ℝ ∞ ((e₂ k).symm : E × E → E × E) (e₂ k).target ∧
        (∀ z ∈ (e₂ k).source,
          (dd k).pair (e₂ k z) = Exponential.diagExp (g k) (hEnorm k) ((dd k).tangent z)) ∧
        ∀ z ∈ (e₂ k).source,
          z.1 ∈ Metric.ball (0 : E) (dd k).radius ∧
          (e₂ k z).1 ∈ Metric.ball (0 : E) (dd k).radius ∧
          (e₂ k z).2 ∈ Metric.ball (0 : E) (dd k).radius) →
      (∀ᶠ k in atTop, MapsTo (e₁ k).symm (Metric.closedBall 0 ε₁) (Metric.ball 0 qInner)) →
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι]
        (weights₁ weights₂ : E → ι → ℝ) (xi₁ xi₂ : ℕ → E → ι → E)
        (Phi₁ Phi₂ : ℕ → E → E) (points : ∀ k, E → ι → M k)
        (W₁ W₂ K : Set E),
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (rho / 8))
        (fun k z => (weights₁ z, xi₁ k z)) (fun z => (weights₁ z, fun _ => z - a)) →
      MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (rho / 8))
        (fun k z => (weights₂ z, xi₂ k z)) (fun z => (weights₂ z, fun _ => z - b)) →
      MapCInfConvergenceOnCompacts W₂ Phi₂ (fun z => z - b) →
      W₂ ⊆ Metric.ball (0 : E) (rho / 8) →
      IsCompact K → K ⊆ W₂ → MapsTo J K W₁ → W₁ ⊆ Metric.ball (0 : E) (rho / 8) →
      (∀ z ∈ W₁, z - a ∈ Metric.ball (0 : E) ε₁) →
      (∀ z ∈ W₂, z - b ∈ Metric.ball (0 : E) q₂ ∧ z - b ∈ Metric.ball (0 : E) ε₂) →
      EqOn (fun z => weights₁ (J z)) weights₂ K →
      (∀ᶠ k in atTop, ∀ z ∈ K, ∀ i, weights₂ z i ≠ 0 →
        (cc k).hom (xi₁ k (J z) i) = points k z i ∧
        (dd k).hom (xi₂ k z i) = points k z i) →
      (∀ᶠ k in atTop, ∀ z ∈ W₂,
        invVelocitySum (e₂ k) (weights₂ z) (xi₂ k z) (Phi₂ k z) = 0) →
      (∀ᶠ k in atTop, ∀ z ∈ W₁, ∀ y, dist y (z - a) < rTube →
        invVelocitySum (e₁ k) (weights₁ z) (xi₁ k z) y = 0 → y = Phi₁ k z) →
      ∀ᶠ k in atTop, EqOn (fun z => (cc k).hom (Phi₁ k (J z)))
        (fun z => (dd k).hom (Phi₂ k z)) K := by
  intro nc nd cc dd e₁ e₂ q₁ q₂ qInner ε₁ ε₂ rTube hq₁ hq₂ hqInner hrTube hstage₁ hstage₂
    hcapture ι instι instNonempty weights₁ weights₂ xi₁ xi₂ Phi₁ Phi₂ points W₁ W₂ K
    hcfg₁ hcfg₂ hPhi hW₂ hK hKW₂ hJK hW₁ hcenter₁ hcenter₂ hweights hatoms hroot hunique
  have hid : (fun z : E => b + (z - b)) = id := by
    funext z
    dsimp
    abel
  have hPhiOriginal : MapCInfConvergenceOnCompacts W₂ (fun k z => b + Phi₂ k z) id := by
    simpa only [hid] using hPhi.const_add b
  have hmap : MapsTo (id : E → E) K (Metric.ball (0 : E) (rho / 8)) := hKW₂.trans hW₂
  have hrecv := IntrinsicBallChart.eventually_recenter_inv_pairs_mem_ball
    g hEnorm q p hrho (show rho / 8 < rho / 2 by linarith) d c hnear hJ hJc
    hPhiOriginal hK hKW₂ continuousOn_id hmap a hr₁ hball₁
    weights₁ xi₁ hcfg₁ J (fun _ _ => rfl) (hJK.mono_right hW₁)
    (fun z hz => hcenter₁ _ (hJK hz))
  have hcloseOriginal := IntrinsicBallChart.eventually_mem_target_and_dist_inv_lt
    g hEnorm q p hrho (show rho / 8 < rho / 2 by linarith) d c hnear hJ hJc
    hPhiOriginal hK hKW₂ continuousOn_id hmap hrTube
  have hPhiUnif := tendstoUniformlyOn_of_cPConvergence (hPhi K hK hKW₂ 0)
  have hcfgUnif := tendstoUniformlyOn_of_cPConvergence (hcfg₂ K hK (hKW₂.trans hW₂) 0)
  have hxiUnif := uniformContinuous_snd.comp_tendstoUniformlyOn hcfgUnif
  have hpairsDonor := hPhiUnif.eventually_forall_pair_mem_ball_of_isCompact hxiUnif hK
    (continuousOn_id.sub continuousOn_const) (fun z hz => (hcenter₂ z (hKW₂ hz)).2)
  have hnormDonor := hPhi.eventually_mapsTo hK hKW₂
    (continuousOn_id.sub continuousOn_const) Metric.isOpen_ball
    (fun z hz => (hcenter₂ z (hKW₂ hz)).1)
  have hcfg₂W : MapCInfConvergenceOnCompacts W₂
      (fun k z => (weights₂ z, xi₂ k z)) (fun z => (weights₂ z, fun _ => z - b)) :=
    fun L hL hLW => hcfg₂ L hL (hLW.trans hW₂)
  have hdist := IntrinsicBallChart.eventually_riemannianEDist_lt_of_configuration_convergence
    g hEnorm q d (show rho / 8 < rho by linarith) (C := 2)
    (Eventually.of_forall fun k z hz v => by
      have h := (hell₂ k z hz v).2
      norm_num
      nlinarith [sq_nonneg ‖v‖])
    hPhi hcfg₂W hK hKW₂ (continuousOn_id.sub continuousOn_const) b
    (by simpa only [hid] using hmap)
    (show 0 < min q₁ q₂ / 2 from div_pos (lt_min hq₁ hq₂) (by norm_num))
  have hmetric₁ : ∀ k, (nc k).MetricEquivOn (g k) (Metric.ball (0 : E) (nc k).radius) :=
    fun k => (c k).metricEquivOn_of_intrinsicFrameMetric (g k) (hEnorm k) (p k) hrho (hell₁ k)
  have hmetric₂ : ∀ k, (nd k).MetricEquivOn (g k) (Metric.ball (0 : E) (nd k).radius) :=
    fun k => (d k).metricEquivOn_of_intrinsicFrameMetric (g k) (hEnorm k) (q k) hrho (hell₂ k)
  have hreceiving : ∀ᶠ k in atTop, ∀ z ∈ K,
      (dd k).hom (Phi₂ k z) ∈ (cc k).restrictBall.target ∧
      ‖(cc k).inv ((dd k).hom (Phi₂ k z))‖ < q₁ ∧
      ∀ i, ((cc k).inv ((dd k).hom (Phi₂ k z)), xi₁ k (J z) i) ∈ (e₁ k).target := by
    filter_upwards [hrecv, hcapture] with k hk hcap z hz
    have hpair := fun i => (hstage₁ k).2.2.1 (Metric.ball_subset_closedBall ((hk z hz).2 i))
    let i₀ : ι := Classical.choice instNonempty
    have hy : (dd k).hom (Phi₂ k z) ∈ (nc k).hom.target := by
      obtain ⟨w, hw, hwy⟩ := (hk z hz).1
      change (d k).hom (b + Phi₂ k z) ∈ (nc k).hom.target
      rw [← hwy]
      exact (nc k).hom.map_source ((nc k).ball_subset hw)
    refine ⟨(nc k).mem_recenter_target_of_inverse_pair_mem a hr₁ (hball₁ k)
      (e₁ k) (hstage₁ k).2.2.2.2.1 (hstage₁ k).2.2.2.2.2 hy (hpair i₀), ?_, hpair⟩
    exact ((cc k).diagonal_inverse_norm_lt (e₁ k) (hstage₁ k).2.2.2.2.1
      (hstage₁ k).2.2.2.2.2 (hpair i₀)
      (hcap (Metric.ball_subset_closedBall ((hk z hz).2 i₀)))).trans hqInner
  have hdonor : ∀ᶠ k in atTop, ∀ z ∈ K,
      ‖Phi₂ k z‖ < q₂ ∧ Phi₂ k z ∈ Metric.ball (0 : E) (dd k).radius ∧
      ∀ i, (Phi₂ k z, xi₂ k z i) ∈ (e₂ k).target := by
    filter_upwards [hnormDonor, hpairsDonor] with k hn hp z hz
    have hpair := fun i => (hstage₂ k).2.2.1 (Metric.ball_subset_closedBall (hp z hz i))
    let i₀ : ι := Classical.choice instNonempty
    have hf := ((hstage₂ k).2.2.2.2.2 _ ((e₂ k).map_target (hpair i₀))).1
    rw [(dd k).diagonal_inverse_fst (e₂ k) (hstage₂ k).2.2.2.2.1
      (hstage₂ k).2.2.2.2.2 (hpair i₀)] at hf
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hn hz, hf, hpair⟩
  apply Exponential.eventually_eqOn_of_chart_invVelocity_roots g hEnorm cc dd e₁ e₂
    (Eventually.of_forall fun k => (hstage₁ k).1)
    (Eventually.of_forall fun k => (hstage₂ k).1)
    (Eventually.of_forall fun k => (hstage₁ k).2.1)
    (Eventually.of_forall fun k => (hstage₂ k).2.1)
    (Eventually.of_forall fun k => (hstage₁ k).2.2.2.1)
    (Eventually.of_forall fun k => (hstage₂ k).2.2.2.1)
    (Eventually.of_forall fun k => (hstage₁ k).2.2.2.2.1)
    (Eventually.of_forall fun k => (hstage₂ k).2.2.2.2.1)
    (Eventually.of_forall fun k => (hstage₁ k).2.2.2.2.2)
    (Eventually.of_forall fun k => (hstage₂ k).2.2.2.2.2)
    (fun _ => weights₂) points (fun k z => xi₁ k (J z)) xi₂
    (hreceiving.mono fun k hk z hz => (hk z hz).1)
    (hreceiving.mono fun k hk z hz => (hk z hz).2.1)
    (hdonor.mono fun k hk z hz => (hk z hz).1)
  · filter_upwards [hreceiving] with k hk z hz v
    exact ((hmetric₁ k).recenter_inv (g k) a hr₁ (hball₁ k) (hk z hz).1 v).1
  · filter_upwards [hdonor] with k hk z hz v
    exact (NormalBallChart.MetricEquivOn.recenter (g k) b hr₂ (hball₂ k)
      (fun w hw => hmetric₂ k w (hball₂ k hw)) _ (hk z hz).2.1 v).1
  · filter_upwards [hcloseOriginal] with k hk z hz
    change dist (-a + (c k).hom.symm ((d k).hom (b + Phi₂ k z))) (J z - a) < rTube
    rw [add_comm (-a), ← sub_eq_add_neg, dist_sub_right]
    exact (hk z hz).2
  · filter_upwards [hunique] with k hk z hz y hy hrootY
    apply hk (J z) (hJK hz) y hy
    have hw : weights₁ (J z) = weights₂ z := hweights hz
    rw [hw]
    exact hrootY
  · intro i
    filter_upwards [hdist, hatoms] with k hd ha z hz hi
    rw [← (ha z hz i hi).2]
    exact hd z hz i
  · intro i
    exact hatoms.mono fun k hk z hz hi => (hk z hz i hi).1
  · intro i
    exact hatoms.mono fun k hk z hz hi => (hk z hz i hi).2
  · intro i
    exact hreceiving.mono fun k hk z hz _ => (hk z hz).2.2 i
  · intro i
    exact hdonor.mono fun k hk z hz _ => (hk z hz).2.2 i
  · exact hroot.mono fun k hk z hz => hk z (hKW₂ hz)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
end
