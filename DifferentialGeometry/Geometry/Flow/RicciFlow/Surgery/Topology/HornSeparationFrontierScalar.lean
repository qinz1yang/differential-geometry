import Batteries.Tactic.OpenPrivate
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornSeparationSliceTransfer

set_option autoImplicit false

noncomputable section

open Set Filter Function TopologicalSpace Manifold
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation

universe u

open private horn_sides_of_complementPair from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornCentralSphereSeparation

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s} :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem neck_chart_notMem_core_of_frontier_scalar_lt
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hcenter : N.center ∈ hornHalfRange P c e)
    (hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale)
    {z : neckBuffer δ} (hz : z ∈ neckCentralDomain δ) : N.chart z ∉ P.core c := by
  have hlow : ∀ q ∈ neckCentralDomain δ,
      (1 - 4323 * δ) * N.scale ≤ metricScalarAt D.terminal.metric (N.chart q) := by
    intro q hq
    have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk hδ q ⟨hq.1.le, hq.2.le⟩)).1
    exact (le_div_iff₀ N.scale_pos).mp (by linarith)
  have hδpos := N.delta_pos
  let z0 : neckBuffer δ := ⟨(N.sphereMark, 0), by
    change -δ⁻¹ - 1 < 0 ∧ 0 < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr hδpos]⟩
  have hz0 : z0 ∈ neckCentralDomain δ := by
    change -δ⁻¹ < 0 ∧ 0 < δ⁻¹
    constructor <;> linarith [inv_pos.mpr hδpos]
  have hmark : N.chart z0 = N.center := N.marked
  have hS : IsPreconnected (N.chart '' neckCentralDomain δ) :=
    (isPreconnected_neckCentralDomain δ).image _ N.chart.continuous.continuousOn
  have hcenter_core : N.center ∉ P.core c := by
    intro hcore
    have hbase : N.center ∈ (range fun p : HalfNeckCylinder => P.horn c e p.1) ∩ P.core c :=
      ⟨hcenter, hcore⟩
    rw [P.horn_meets_core] at hbase
    have hfr : N.center ∈ frontier (P.core c) := by
      rw [P.horn_base_covers_boundary c hc]
      exact mem_iUnion.mpr ⟨e, hbase⟩
    have h := hfront _ hfr
    rw [← N.scale_scalar] at h
    have hpos : 0 < 4323 * δ * N.scale := by have := N.scale_pos; positivity
    linarith
  intro hzcore
  have hsub : N.chart '' neckCentralDomain δ ⊆
      interior (P.core c) ∪ (closure (P.core c))ᶜ := by
    rintro _ ⟨q, hq, rfl⟩
    by_cases hi : N.chart q ∈ interior (P.core c)
    · exact Or.inl hi
    · exact Or.inr fun hcl => absurd (hfront _ ⟨hcl, hi⟩) (not_lt.mpr (hlow q hq))
  rcases hS.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      ((disjoint_compl_right (a := closure (P.core c))).mono_left interior_subset_closure)
      hsub with h | h
  · exact hcenter_core (hmark ▸ interior_subset (h (mem_image_of_mem _ hz0)))
  · exact h (mem_image_of_mem _ hz) (subset_closure hzcore)

theorem neckCentralDomain_subset_horn_of_frontier_scalar_lt
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hcenter : N.center ∈ hornHalfRange P c e)
    (hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale) :
    N.chart '' neckCentralDomain δ ⊆ hornHalfRange P c e := by
  have hδpos := N.delta_pos
  let z : neckBuffer δ := ⟨(N.sphereMark, 0), by
    change -δ⁻¹ - 1 < 0 ∧ 0 < δ⁻¹ + 1
    constructor <;> linarith [inv_pos.mpr hδpos]⟩
  have hz : z ∈ neckCentralDomain δ := by
    change -δ⁻¹ < 0 ∧ 0 < δ⁻¹
    constructor <;> linarith [inv_pos.mpr hδpos]
  have hmark : N.chart z = N.center := N.marked
  let S := N.chart '' neckCentralDomain δ
  have hS : IsPreconnected S :=
    (isPreconnected_neckCentralDomain δ).image _ N.chart.continuous.continuousOn
  have hne : S.Nonempty := ⟨N.chart z, ⟨z, hz, rfl⟩⟩
  have hcenterS : N.center ∈ S := hmark ▸ mem_image_of_mem N.chart hz
  have hcenterc : ConnectedComponents.mk N.center = c := by
    have hmem : N.center ∈ P.core c ∪ ⋃ e, hornHalfRange P c e :=
      Or.inr (mem_iUnion.mpr ⟨e, hcenter⟩)
    change N.center ∈ P.core c ∪ ⋃ e, range (fun p : HalfNeckCylinder => P.horn c e p.val)
      at hmem
    rw [← P.horn_covers_component c hc] at hmem
    exact hmem
  have hcomp : ∀ y ∈ S, ConnectedComponents.mk y = c := by
    intro y hy
    exact (ConnectedComponents.coe_eq_coe'.mpr
      (hS.subset_connectedComponent hcenterS hy)).trans hcenterc
  have hcore : ∀ y ∈ S, y ∉ P.core c := by
    rintro y ⟨q, hq, rfl⟩
    exact P.neck_chart_notMem_core_of_frontier_scalar_lt c hc e N hk hδ hcenter hfront hq
  obtain ⟨e', he'⟩ := P.exists_hornHalfRange_superset_of_isPreconnected hc hS hne hcomp hcore
  have heq : e' = e := P.hornHalfRange_unique (he' hcenterS) hcenter
  exact heq ▸ he'

theorem exists_neck_coordinates_in_horn_of_frontier_scalar_lt
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k)
    (hk : 2 ≤ k) (hδ : δ ≤ 1 / 2) (hcenter : N.center ∈ hornHalfRange P c e)
    (hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale) :
    ∃ Θ : neckCentralOpen δ → positiveHornDomain,
      IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ ∧
      ∀ q : neckCentralOpen δ,
        P.horn c e (Θ q).val = N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) := by
  have hmemImage : ∀ q : neckCentralOpen δ,
      N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q) ∈
        (P.positiveHornMap_local c e).image := by
    intro q
    have hz : Opens.inclusion (neckCentralOpen_le_buffer δ) q ∈ neckCentralDomain δ :=
      q.property.2
    obtain ⟨p, hp⟩ := P.neckCentralDomain_subset_horn_of_frontier_scalar_lt c hc e N hk hδ
      hcenter hfront (mem_image_of_mem N.chart hz)
    have hcore := P.neck_chart_notMem_core_of_frontier_scalar_lt c hc e N hk hδ hcenter hfront hz
    have hpos : 0 < p.val.2 := by
      by_contra hn
      have hzero : p.val.2 = 0 := le_antisymm (le_of_not_gt hn) p.property
      have hp0 : P.horn c e p.val ∈ P.core c := by
        convert P.horn_base_mem_core c e p.val.1 using 1
        exact congrArg (P.horn c e) (Prod.ext rfl hzero)
      exact hcore (hp ▸ hp0)
    exact ⟨⟨p.val, mem_univ _, hpos⟩, hp⟩
  let F : neckCentralOpen δ → (P.positiveHornMap_local c e).image :=
    fun q => ⟨N.chart (Opens.inclusion (neckCentralOpen_le_buffer δ) q), hmemImage q⟩
  let Θ := (P.positiveHornDiffeomorph c e).symm ∘ F
  have hinc : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞
      (Opens.inclusion (neckCentralOpen_le_buffer δ)) := by
    apply isSmoothEmbedding_intoOpen NeckCylinderModel NeckCylinderModel (neckBuffer δ)
    exact IsSmoothEmbedding.of_opens (I := NeckCylinderModel) (neckCentralOpen δ)
  have hcomp : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞
      ((N.chart : neckBuffer δ → D.slab.terminalRegularOpen) ∘
        Opens.inclusion (neckCentralOpen_le_buffer δ)) :=
    IsSmoothEmbedding.comp N.chart_smooth hinc (by simp)
  have hF : IsSmoothEmbedding NeckCylinderModel ThreeModel ∞ F :=
    isSmoothEmbedding_intoOpen NeckCylinderModel ThreeModel _ F hcomp
  have hΘ : IsSmoothEmbedding NeckCylinderModel NeckCylinderModel ∞ Θ :=
    IsSmoothEmbedding.comp (Perelman.KappaSolutions.diffeomorph_isSmoothEmbedding
      (P.positiveHornDiffeomorph c e).symm) hF (by simp)
  refine ⟨Θ, hΘ, ?_⟩
  intro q
  exact diffeomorphOntoImage_symm_apply (P.positiveHornMap c e) (P.positiveHornMap_local c e)
    (P.horn_interior_embedding c e).isEmbedding.injective (F q)

theorem exists_horn_centralSphere_side_points_of_frontier_scalar_lt :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e →
          (∀ w ∈ frontier (P.core c), 2 * metricScalarAt D.terminal.metric w < N.scale) →
          ∀ {r : ℝ}, 0 < r → IsCompact (riemannianClosedBallOf D.terminal.metric N.center r) →
          (∀ w ∈ frontier (P.core c),
            ENNReal.ofReal r < riemannianEDistOf D.terminal.metric N.center w) →
          ∃ U V : Set D.slab.terminalRegularOpen, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
            (N.chart '' {z | z.val.2 = 0})ᶜ ⊆ U ∪ V ∧
            ∃ y ∈ U, ∃ z ∈ V,
              riemannianEDistOf D.terminal.metric N.center y = ENNReal.ofReal r ∧
              riemannianEDistOf D.terminal.metric N.center z = ENNReal.ofReal r := by
  obtain ⟨eta, heta, hsep⟩ := exists_horn_neck_end_separation_tolerance.{u}
  refine ⟨min eta (1 / 8646), lt_min heta (by norm_num), ?_⟩
  intro D ε Λ P hε c hc e δ k N hδ hk hcenter hfs r hr hK hbase
  have hεsmall : ε ≤ 1 / 8646 := hε.trans (min_le_right _ _)
  have hεpos : 0 < ε := N.delta_pos.trans_le hδ
  have hlarge : (1 : ℝ) ≤ ε⁻¹ := (le_inv_comm₀ (by norm_num) hεpos).mpr (by linarith)
  have hfloor : 1 ≤ ⌊ε⁻¹⌋₊ := (Nat.le_floor_iff (by positivity)).mpr (by exact_mod_cast hlarge)
  have hk2 : 2 ≤ k := by omega
  have hδs : δ ≤ 1 / 8646 := hδ.trans hεsmall
  have hfront : ∀ w ∈ frontier (P.core c),
      metricScalarAt D.terminal.metric w < (1 - 4323 * δ) * N.scale := by
    intro w hw
    have h := hfs w hw
    have hhalf : (1 / 2 : ℝ) * N.scale ≤ (1 - 4323 * δ) * N.scale :=
      mul_le_mul_of_nonneg_right (by linarith) N.scale_pos.le
    linarith
  obtain ⟨Θ, hΘ, hmap⟩ := P.exists_neck_coordinates_in_horn_of_frontier_scalar_lt c hc e N hk2
    (hδs.trans (by norm_num)) hcenter hfront
  obtain ⟨p, R, -, hfl, hfr, -, hclr, -, -, hlo, hhi, -⟩ := hsep P (hε.trans (min_le_left _ _))
    c e N hδ ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk) Θ hΘ hmap
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
theorem exists_strongNeck_threshold_of_horn_point_at_slice_of_frontier_scalar_lt :
    ∃ eta : ℝ, 0 < eta ∧
    ∀ {delta : ℝ}, 0 < delta → delta < 1 / 11 → ∀ {kappa : ℝ}, 0 < kappa →
    ∀ {rho : ℝ}, 0 < rho → ∀ {Phi : ℝ → ℝ}, Perelman.AdmissiblePinchingFunction Phi →
    ∃ A Q₀ theta : ℝ, 0 < A ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ (e : P.hornIndex c) {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k),
          δ ≤ ε → ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e →
          (∀ w ∈ frontier (P.core c), 2 * metricScalarAt D.terminal.metric w < N.scale) →
          ∀ {K : ℝ},
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
  obtain ⟨eta1, heta1, hsides⟩ := exists_horn_centralSphere_side_points_of_frontier_scalar_lt.{u}
  have hα : (0 : ℝ) < 1 / 504 := by norm_num
  have hm := neckModelTolerance_pos hα
  refine ⟨min eta1 (neckModelTolerance (1 / 504) / 2), lt_min heta1 (by positivity), ?_⟩
  intro delta hdelta hdelta1 kappa hkappa rho hrho Phi hPhi
  obtain ⟨A, Q₀, theta, hA, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_locally_separating_centralSphere.{u}
      hdelta hdelta1 hkappa hrho hPhi
  refine ⟨A, Q₀, theta, hA, hQ₀, htheta, ?_⟩
  intro D ε Λ P hε c hc e δ k N hδ hk hcenter hfs K hbase hbd
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
    hsides P (hε.trans (min_le_left _ _)) c hc e N hδ hk hcenter hfs (r := 2 * A / sq)
      (by positivity)
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
