import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornCentralSphereSeparation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.OfMetricDerivNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalMetricCompactComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarCurvature
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Neck.SpatialTolerance

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private local instance terminalRegularOpenSigmaCompact {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_riemannianBallOf_subset_image_closedBall
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen) {r : ℝ} (hr : 0 < r)
    (hK : IsCompact (riemannianClosedBallOf L.metric x r)) :
    ∀ᶠ t in 𝓝[<] s, riemannianBallOf (G.flow.base.metric t) (x : P.Carrier) (16 * r / 17) ⊆
      Subtype.val '' riemannianClosedBallOf L.metric x r := by
  obtain ⟨d, hd, hbound⟩ := L.exists_compact_quad_bound hK (ε := 33 / 256) (by norm_num)
  filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
  let F := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel
    G.terminalRegularOpen ⟨x⟩
  have h := DifferentialGeometry.PartialDiffeomorph.ball_subset_image_closedBall_of_metric_lower
    L.metric (G.flow.base.metric t) F x hr (by norm_num : (0 : ℝ) < 17 / 16) hK
    (fun _ _ => mem_univ _) ?_
  · have hrad : r / (17 / 16) = 16 * r / 17 := by ring
    rw [hrad] at h
    exact h
  · intro y hy v
    have hb := hbound t ht y hy v
    have hres : ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen).inner y v v =
        (G.flow.base.metric t).inner y.val v v := rfl
    change L.metric.inner y v v ≤ (17 / 16) ^ 2 * (G.flow.base.metric t).inner y.val
      (mfderiv ThreeModel ThreeModel (Subtype.val : G.terminalRegularOpen → P.Carrier) y v)
      (mfderiv ThreeModel ThreeModel (Subtype.val : G.terminalRegularOpen → P.Carrier) y v)
    rw [DifferentialGeometry.mfderiv_subtype_val_apply]
    rw [hres] at hb
    linarith

theorem TerminalLimitMetric.eventually_exists_spatialNeck_of_normalizedNeck
    (L : G.TerminalLimitMetric) {δ : ℝ} {k : ℕ} (N : NormalizedNeck L.metric δ k)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (hδ : δ ≤ neckModelTolerance alpha / 2)
    (hk : ⌈(neckModelTolerance alpha / 2)⁻¹⌉₊ ≤ k) :
    ∀ᶠ t in 𝓝[<] s, ∃ nk : SpatialNeck (G.flow.base.metric t) (2 * alpha) (N.center : P.Carrier),
      ∀ z : neckBuffer δ, nk.map z.val = (N.chart z : P.Carrier) := by
  have hm0 : 0 < neckModelTolerance alpha := neckModelTolerance_pos ha
  have hma : neckModelTolerance alpha ≤ alpha := neckModelTolerance_le alpha
  obtain ⟨nk0, -, hnk0⟩ := N.exists_spatialNeck hδ (by linarith) hk
  let nk : SpatialNeck L.metric (neckModelTolerance alpha) N.center :=
    nk0.mono (by linarith) (by linarith)
  have hinv : alpha⁻¹ < (neckModelTolerance alpha / 2)⁻¹ :=
    (inv_lt_inv₀ ha (by positivity)).mpr (by linarith)
  have hsrc : univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹ ⊆ nk.map.source := fun y hy =>
    nk0.domain ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  set K : Set G.terminalRegularOpen := nk.map '' (univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹) with hKdef
  have hK : IsCompact K := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hsrc)
  have hq : 0 < metricScalarAt L.metric N.center := N.scale_scalar ▸ N.scale_pos
  set q := metricScalarAt L.metric N.center with hqdef
  have hσ : 0 < neckSourceTolerance alpha := neckSourceTolerance_pos ha
  set σ := neckSourceTolerance alpha with hσdef
  set order := ⌈(2 * alpha)⁻¹⌉₊ with horder
  set n := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ) with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  have hq1 : 1 ≤ 1 + q⁻¹ := by linarith [inv_pos.mpr hq]
  set B := (1 + q⁻¹) ^ (order + 2) with hB
  have hB1 : 1 ≤ B := one_le_pow₀ hq1
  set eps0 := min (1 / 2) (σ / (4 * B * q)) with heps0
  have heps0pos : 0 < eps0 := lt_min (by norm_num) (by positivity)
  have heps01 : eps0 < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have heps0B : eps0 * (4 * B * q) ≤ σ :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  set eta := σ / (2 * (n + 1)) with heta
  have heta0 : 0 < eta := by positivity
  have hetan : eta * n ≤ σ / 2 := by
    have h1 : eta * (2 * (n + 1)) = σ := div_mul_cancel₀ σ (by positivity)
    nlinarith
  have hconv : ∀ᶠ t in 𝓝[<] s, ∀ j : Fin (order + 1), ∀ y ∈ K,
      metricDerivNorm j ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen)
        L.metric L.metric y < eps0 := by
    refine eventually_all.mpr fun j => ?_
    obtain ⟨d, hd, hb⟩ := L.converges K hK j eps0 heps0pos
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    exact hb t ht
  have hclose : ∀ᶠ t in 𝓝[<] s,
      |metricScalarAt (G.flow.base.metric t) (N.center : P.Carrier) - q| < min q (eta * q) := by
    have h := Metric.tendsto_nhds.mp (L.tendsto_metricScalarAt N.center) (min q (eta * q))
      (lt_min hq (by positivity))
    filter_upwards [h] with t ht
    rwa [Real.dist_eq] at ht
  filter_upwards [hconv, hclose] with t hct hqt
  set c := metricScalarAt (G.flow.base.metric t) (N.center : P.Carrier) with hcdef
  have hqt1 := (abs_lt.mp (hqt.trans_le (min_le_left _ _)))
  have hqt2 := hqt.trans_le (min_le_right _ _)
  have hc : 0 < c := by linarith [hqt1.1]
  have hc2 : c ≤ 2 * q := by linarith [hqt1.2]
  have hratio : |c / q - 1| ≤ eta := by
    rw [show c / q - 1 = (c - q) / q by field_simp, abs_div, abs_of_pos hq,
      div_le_iff₀ hq]
    exact hqt2.le
  have happly : ∀ y ∈ K, ∀ v : Fin 2 → TangentSpace ThreeModel y,
      Tensor0SBundle.metricTensorField
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) y v =
        (G.flow.base.metric t).inner y.val
          (mfderiv ThreeModel ThreeModel (Subtype.val : G.terminalRegularOpen → P.Carrier) y (v 0))
          (mfderiv ThreeModel ThreeModel (Subtype.val : G.terminalRegularOpen → P.Carrier) y
            (v 1)) := by
    intro y _ v
    rw [Tensor0SBundle.metricTensorField_apply, DifferentialGeometry.mfderiv_subtype_val_apply,
      DifferentialGeometry.mfderiv_subtype_val_apply]
    rfl
  let Dm := MapMetricApproximationOn.ofMetricDerivNorm (K := K) (p := order)
    (F := (Subtype.val : G.terminalRegularOpen → P.Carrier))
    ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric (G.flow.base.metric t)
    heps0pos heps01 contMDiff_subtype_val.contMDiffOn happly
    (fun j hj y hy => (hct ⟨j, Nat.lt_succ_of_le hj⟩ y hy).le)
  have hweight : ∀ j ≤ order, Real.sqrt (q⁻¹ ^ (j + 2)) * c * eps0 +
      |c / q - 1| * Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ) ≤ σ := by
    intro j hj
    have hpow : q⁻¹ ^ (j + 2) ≤ B :=
      (pow_le_pow_left₀ (inv_pos.mpr hq).le (by linarith) _).trans
        (pow_le_pow_right₀ hq1 (by omega))
    have hsqrt : Real.sqrt (q⁻¹ ^ (j + 2)) ≤ B :=
      Real.sqrt_le_iff.mpr ⟨by linarith, hpow.trans (by nlinarith)⟩
    have h1 : Real.sqrt (q⁻¹ ^ (j + 2)) * c ≤ B * (2 * q) :=
      mul_le_mul hsqrt hc2 hc.le (by linarith)
    have h2 : Real.sqrt (q⁻¹ ^ (j + 2)) * c * eps0 ≤ σ / 2 := by
      have h3 := mul_le_mul_of_nonneg_right h1 heps0pos.le
      nlinarith
    have h4 : |c / q - 1| * n ≤ σ / 2 :=
      (mul_le_mul_of_nonneg_right hratio hn0).trans hetan
    linarith
  have Cm := (MetricComparisonOn.ofMapMetricApproximation Dm ({0} : Set ℝ)).staticRescale
    (t := 0) rfl q c hq hc hσ.le hweight
  let Fm := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph ThreeModel
    G.terminalRegularOpen ⟨N.center⟩
  obtain ⟨nk', hnk'⟩ := nk.exists_transport_of_local_comparisons hc Fm Cm ha hsmall hσ.le le_rfl
    le_rfl rfl (fun y hy => ⟨y, ⟨hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩) (fun _ _ => mem_univ _)
  refine ⟨nk', fun z => ?_⟩
  rw [hnk']
  exact congrArg Subtype.val (hnk0 z)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation

universe u

open private horn_sides_of_complementPair from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornCentralSphereSeparation

theorem exists_deep_horn_centralSphere_side_points :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ e : P.hornIndex c, ∃ Q : ℝ, 0 < Q ∧
        ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k), δ ≤ ε →
          ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e → Q < N.scale →
          ∀ {r : ℝ}, 0 < r → IsCompact (riemannianClosedBallOf D.terminal.metric N.center r) →
          (∀ w ∈ frontier (P.core c),
            ENNReal.ofReal r < riemannianEDistOf D.terminal.metric N.center w) →
          ∃ U V : Set D.slab.terminalRegularOpen, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
            (N.chart '' {z | z.val.2 = 0})ᶜ ⊆ U ∪ V ∧
            ∃ y ∈ U, ∃ z ∈ V,
              riemannianEDistOf D.terminal.metric N.center y = ENNReal.ofReal r ∧
              riemannianEDistOf D.terminal.metric N.center z = ENNReal.ofReal r := by
  obtain ⟨eta, heta, hdeep⟩ := exists_deep_horn_neck_end_separation_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε c hc e
  obtain ⟨Q, hQ, hQdeep⟩ := hdeep P hε c hc e 0
  refine ⟨Q, hQ, ?_⟩
  intro δ k N hδ hk hcenter hscale r hr hK hbase
  obtain ⟨Θ, -, hmap, -, p, R, -, hfl, hfr, -, hclr, -, -, hlo, hhi, -⟩ :=
    hQdeep N hδ hk hcenter hscale
  obtain ⟨hVo, hsub, hleft, -, -⟩ := horn_sides_of_complementPair P c e p hclr hlo
  let c0 : neckCentralOpen δ := ⟨(N.sphereMark, 0), mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos), inv_pos.mpr N.delta_pos⟩
  have hx : P.horn c e ((Θ c0).val.1, (Θ c0).val.2) = N.center := by
    change P.horn c e (Θ c0).val = N.center
    rw [hmap c0]
    exact N.marked
  have hs0 : 0 < (Θ c0).val.2 := (Θ c0).property.2
  have hbase0 : P.horn c e ((Θ c0).val.1, 0) ∈ frontier (P.core c) := by
    rw [P.horn_base_covers_boundary c hc]
    exact mem_iUnion.mpr ⟨e, (Θ c0).val.1, rfl⟩
  obtain ⟨a, b, ha, hb, hda, hdb⟩ := P.exists_horn_side_points_at_distance c e p
    (fun w hw => frontier_subset_closure (hfl.symm ▸ hw))
    (fun w hw => frontier_subset_closure (hfr.symm ▸ hw))
    (Θ c0).val.1 hs0 ⟨N.sphereMark, rfl⟩ (A := r) hr (Real.exp_pos (-R))
    (by rw [hx]; exact hK) (by rw [hx]; exact hbase _ hbase0) hlo hhi
  rw [hx] at hda hdb
  set V := P.positiveHornMap c e '' p.right with hVdef
  refine ⟨(closure V)ᶜ, V, isClosed_closure.isOpen_compl, hVo,
    disjoint_compl_left_iff_subset.mpr subset_closure, ?_, P.positiveHornMap c e a,
    fun hcl => disjoint_left.mp hleft ⟨a, ha, rfl⟩ hcl, P.positiveHornMap c e b,
    ⟨b, hb, rfl⟩, hda, hdb⟩
  intro w hwS
  by_cases hcl : w ∈ closure V
  · rcases hsub hcl with h | ⟨_, ⟨q, rfl⟩, rfl⟩
    · exact Or.inr h
    · refine absurd ⟨TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ)
        ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
          inv_pos.mpr N.delta_pos⟩, rfl, ?_⟩ hwS
      exact (hmap _).symm
  · exact Or.inl hcl

open OrientedThreeStage.IncomingSlab in
theorem exists_strongNeck_threshold_of_horn_point_at_slice
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ A Q₀ theta eta : ℝ, 0 < A ∧ 0 < Q₀ ∧ 0 < theta ∧ 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ e : P.hornIndex c, ∃ Q : ℝ, 0 < Q ∧
        ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k), δ ≤ ε →
          ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e → Q < N.scale → ∀ {K : ℝ},
          (∀ w ∈ frontier (P.core c), ENNReal.ofReal
              (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
            riemannianEDistOf D.terminal.metric N.center w) →
          (∀ z ∈ riemannianBallOf D.terminal.metric N.center
              (5 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)),
            metricScalarAt D.terminal.metric z ≤ K) →
          ∀ᶠ τ in 𝓝[<] D.endTime,
            Q₀ ≤ D.slab.flow.scalar τ N.center.val →
            D.startTime ≤ τ - theta / D.slab.flow.scalar τ N.center.val →
            Perelman.PhiAlmostNonnegative D.slab.flow
              (Icc (τ - theta / D.slab.flow.scalar τ N.center.val) τ) Phi →
            (∀ (τ' : (RealTimeInterval.closedOpen D.startTime D.endTime D.slab.lt).FlowTime)
              (B : Perelman.FlowMetricBall D.slab.flow τ'),
              τ - theta / D.slab.flow.scalar τ N.center.val ≤ τ' → (τ' : ℝ) ≤ τ →
                B.radius ≤ rho → B.IsParabolicallyRmControlled →
                  B.IsKappaNoncollapsed kappa) →
            Nonempty (StrongNeck D.slab.flow delta N.center.val τ) := by
  obtain ⟨A, Q₀, theta, hA, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_locally_separating_centralSphere.{u}
      hdelta hdelta1 hkappa hrho hPhi
  obtain ⟨eta1, heta1, hsides⟩ := exists_deep_horn_centralSphere_side_points.{u}
  have hα : (0 : ℝ) < 1 / 504 := by norm_num
  have hm := neckModelTolerance_pos hα
  refine ⟨A, Q₀, theta, min eta1 (neckModelTolerance (1 / 504) / 2), hA, hQ₀, htheta,
    lt_min heta1 (by positivity), ?_⟩
  intro D ε Λ P hε c hc e
  obtain ⟨Q, hQ, hQside⟩ := hsides P (hε.trans (min_le_left _ _)) c hc e
  refine ⟨Q, hQ, ?_⟩
  intro δ k N hδ hk hcenter hscale K hbase hbd
  have hq : 0 < metricScalarAt D.terminal.metric N.center := N.scale_scalar ▸ N.scale_pos
  set q := metricScalarAt D.terminal.metric N.center with hqdef
  set sq := Real.sqrt q with hsqdef
  have hsq : 0 < sq := Real.sqrt_pos.mpr hq
  have hsq2 : sq ^ 2 = q := Real.sq_sqrt hq.le
  have hxc : ConnectedComponents.mk N.center = c := by
    have h : N.center ∈ {w : D.slab.terminalRegularOpen | ConnectedComponents.mk w = c} := by
      rw [P.horn_covers_component c hc]
      exact Or.inr (mem_iUnion.mpr ⟨e, hcenter⟩)
    exact h
  have hcpt : ∀ m : ℝ, 0 < m → m < 5 →
      IsCompact (riemannianClosedBallOf D.terminal.metric N.center (m * A / sq)) :=
    fun m hm0 hm5 => P.isCompact_riemannianClosedBallOf_of_scalar_le c hc hxc (by positivity)
      (div_lt_div_of_pos_right (by nlinarith) hsq) hbd
  obtain ⟨U, V, hU, hV, hUV, hcov, y, hyU, z, hzV, hy, hz⟩ :=
    hQside N hδ hk hcenter hscale (r := 2 * A / sq) (by positivity)
      (hcpt 2 (by norm_num) (by norm_num)) hbase
  have hεpos : 0 < ε := P.epsilon_pos
  have hεm : ε ≤ neckModelTolerance (1 / 504) / 2 := hε.trans (min_le_right _ _)
  have hkm : ⌈(neckModelTolerance (1 / 504) / 2)⁻¹⌉₊ ≤ k :=
    (Nat.ceil_mono (inv_anti₀ hεpos hεm)).trans ((Nat.ceil_le_floor_add_one _).trans hk)
  have hneck := D.terminal.eventually_exists_spatialNeck_of_normalizedNeck N hα (by norm_num)
    (hδ.trans hεm) hkm
  have hball := D.terminal.eventually_riemannianBallOf_subset_image_closedBall N.center
    (by positivity) (hcpt (19 / 4) (by norm_num) (by norm_num))
  have hlow := D.terminal.eventually_riemannianBallOf_subset_image_closedBall N.center
    (by positivity) (hcpt (7 / 4) (by norm_num) (by norm_num))
  have hlt23 : ENNReal.ofReal (2 * A / sq) < ENNReal.ofReal (3 * A / sq) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (by linarith) hsq)
  have hupy := D.terminal.eventually_riemannianEDistOf_lt N.center y (hy ▸ hlt23)
  have hupz := D.terminal.eventually_riemannianEDistOf_lt N.center z (hz ▸ hlt23)
  have hscal : ∀ᶠ τ in 𝓝[<] D.endTime,
      |metricScalarAt (D.slab.flow.base.metric τ) N.center.val - q| < q / 10 := by
    have h := Metric.tendsto_nhds.mp (D.terminal.tendsto_metricScalarAt N.center) (q / 10)
      (by positivity)
    filter_upwards [h] with τ hτ
    rwa [Real.dist_eq] at hτ
  filter_upwards [hneck, hball, hlow, hupy, hupz, hscal, self_mem_nhdsWithin]
    with τ hnk hb19 hb7 hy' hz' hs hτ
  intro hQτ hwin hpinch hnc
  set gτ := D.slab.flow.base.metric τ with hgτ
  set Rτ := D.slab.flow.scalar τ N.center.val with hRτ
  obtain ⟨nk, hnkmap⟩ := hnk
  have hRτq : Rτ = metricScalarAt gτ N.center.val := rfl
  rw [← hRτq] at hs
  have hs1 := abs_lt.mp hs
  have hRpos : 0 < Rτ := by linarith [hs1.1]
  set sR := Real.sqrt Rτ with hsR
  have hsR : 0 < sR := Real.sqrt_pos.mpr hRpos
  have hsRlo : 9 / 10 * sq ≤ sR :=
    (Real.le_sqrt (by positivity) hRpos.le).mpr (by nlinarith [hs1.1])
  have hsRhi : sR ≤ 4 / 3 * sq :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [hs1.2]⟩
  have hr19 : 4 * A / sR ≤ 16 * (19 / 4 * A / sq) / 17 := by
    rw [show 16 * (19 / 4 * A / sq) / 17 = 76 * A / (17 * sq) by field_simp; ring,
      div_le_div_iff₀ hsR (by positivity)]
    nlinarith
  have hr7 : A / sR ≤ 16 * (7 / 4 * A / sq) / 17 := by
    rw [show 16 * (7 / 4 * A / sq) / 17 = 28 * A / (17 * sq) by field_simp; ring,
      div_le_div_iff₀ hsR (by positivity)]
    nlinarith
  have hr3 : 3 * A / sq ≤ 4 * A / sR := by
    rw [div_le_div_iff₀ hsq hsR]
    nlinarith
  have hcover : riemannianBallOf gτ N.center.val (4 * A / sR) \
      nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ Subtype.val '' U ∪ Subtype.val '' V := by
    rintro w ⟨hwB, hwS⟩
    have hwB' : riemannianEDistOf gτ N.center.val w <
        ENNReal.ofReal (16 * (19 / 4 * A / sq) / 17) :=
      lt_of_lt_of_le hwB (ENNReal.ofReal_le_ofReal hr19)
    obtain ⟨w', -, rfl⟩ := hb19 hwB'
    have hw' : w' ∈ (N.chart '' {z | z.val.2 = 0})ᶜ := by
      rintro ⟨z0, hz0, rfl⟩
      exact hwS ⟨z0.val, ⟨mem_univ _, hz0⟩, hnkmap z0⟩
    rcases hcov hw' with h | h
    · exact Or.inl ⟨w', h, rfl⟩
    · exact Or.inr ⟨w', h, rfl⟩
  have hfar : ∀ w : D.slab.terminalRegularOpen,
      riemannianEDistOf D.terminal.metric N.center w = ENNReal.ofReal (2 * A / sq) →
      ENNReal.ofReal (A / sR) ≤ riemannianEDistOf gτ N.center.val w.val := by
    intro w hw
    by_contra hcon
    have hmem : riemannianEDistOf gτ N.center.val w.val <
        ENNReal.ofReal (16 * (7 / 4 * A / sq) / 17) :=
      lt_of_lt_of_le (not_le.mp hcon) (ENNReal.ofReal_le_ofReal hr7)
    obtain ⟨w', hw', hww⟩ := hb7 hmem
    rw [Subtype.val_injective hww] at hw'
    change riemannianEDistOf D.terminal.metric N.center w ≤ _ at hw'
    rw [hw, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hw'
    exact absurd hw' (not_le.mpr (div_lt_div_of_pos_right (by linarith) hsq))
  have hup3 : ENNReal.ofReal (3 * A / sq) ≤ ENNReal.ofReal (4 * A / sR) :=
    ENNReal.ofReal_le_ofReal hr3
  exact hthr D.stage D.startTime D.endTime D.slab N.center.val τ hτ hQτ hwin hpinch hnc nk
    (by norm_num) (Subtype.val '' U) (Subtype.val '' V)
    (D.slab.terminalRegularOpen.isOpen.isOpenMap_subtype_val U hU)
    (D.slab.terminalRegularOpen.isOpen.isOpenMap_subtype_val V hV)
    ((disjoint_image_iff Subtype.val_injective).mpr hUV) hcover y.val z.val
    ⟨y, hyU, rfl⟩ ⟨z, hzV, rfl⟩ (hfar y hy) (hy'.trans_le hup3) (hfar z hz)
    (hz'.trans_le hup3)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
