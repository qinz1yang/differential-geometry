import DifferentialGeometry.Geometry.Neck.SpatialRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckRestriction
import DifferentialGeometry.Topology.Manifold.ConnectedComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSphericalBarrier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapSlabCapture
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation

noncomputable section

open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_spatial_neck_slab_subset_cap_core
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    {p x : G.terminalRegularOpen} {eps epsc : ℝ}
    (nk : SpatialNeck L.metric eps p) (heps : eps ≤ 1 / 8646)
    (q : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hx : nk.map (q, level) = x)
    {U : ℕ → Set P.Carrier}
    (cap : ∀ n, LocalCap G.flow epsc x.val (τ n) (U n))
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y) :
    ∀ᶠ n in atTop, Subtype.val '' (nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) ⊆
      interior (cap n).core.carrier := by
  let Q := metricScalarAt L.metric p
  have hQ : 0 < Q := nk.Q_pos
  have hroot := Real.sqrt_pos.mpr hQ
  have hlen : (100 : ℝ) < eps⁻¹ :=
    (lt_inv_comm₀ (by norm_num) nk.eps_pos).mpr (by linarith)
  let K := riemannianClosedBallOf L.metric p (30 / Real.sqrt Q)
  have hslab : (univ : Set (Sphere 2)) ×ˢ Icc (-100 : ℝ) 100 ⊆
      univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hcompactSlab : IsCompact (nk.map '' (univ ×ˢ Icc (-100 : ℝ) 100)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      (nk.map.contMDiffOn_toFun.continuousOn.mono (hslab.trans nk.domain))
  have hminus : 1 / 2 < Real.sqrt (1 - eps) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 - eps by linarith)
    nlinarith [Real.sqrt_nonneg (1 - eps)]
  have hK : IsCompact K := by
    apply hcompactSlab.of_isClosed_subset
      (isClosed_le (continuous_riemannianEDist L.metric p) continuous_const)
    intro y hy
    apply nk.ball_subset_image_slab (by norm_num : (0 : ℝ) < 100) hlen
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity :
      0 < 100 * Real.sqrt (1 - eps) / Real.sqrt Q)).mpr
      (div_lt_div_of_pos_right (by linarith) hroot))
  obtain ⟨d, hd, hclose⟩ := L.converges K hK 0 1 zero_lt_one
  have htime := hτ.eventually (Ioo_mem_nhdsLT hd.2)
  have hxx : x ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) :=
    ⟨(q, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hx⟩
  have hscalarx := nk.abs_scalar_ratio_sub_one_le
    (show (q, level) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ from
      ⟨mem_univ _, by constructor <;> linarith [(abs_le.mp hlevel).1, (abs_le.mp hlevel).2]⟩)
  rw [hx] at hscalarx
  have hQx : 0 < metricScalarAt L.metric x := by
    have hr : 0 < metricScalarAt L.metric x / Q := by
      change 0 < metricScalarAt L.metric x / metricScalarAt L.metric p
      linarith [(abs_le.mp hscalarx).1]
    exact (div_pos_iff.mp hr).elim (fun h => h.1) (fun h => (hQ.not_gt h.2).elim)
  have hQxle : metricScalarAt L.metric x ≤ 2 * Q := by
    apply (div_le_iff₀ hQ).mp
    change metricScalarAt L.metric x / metricScalarAt L.metric p ≤ 2
    linarith [(abs_le.mp hscalarx).2]
  have hscalar := hτ.eventually ((L.tendsto_metricScalarAt x).eventually_lt_const
    (show metricScalarAt L.metric x < 4 * Q by linarith))
  have hpositive := hτ.eventually ((L.tendsto_metricScalarAt x).eventually
    (Ioi_mem_nhds hQx))
  filter_upwards [htime, hscalar, hpositive] with n hn hsn hRn
  change G.flow.scalar (τ n) x.val < 4 * Q at hsn
  change 0 < G.flow.scalar (τ n) x.val at hRn
  let gt := (G.flow.base.metric (τ n)).restrictOpen G.terminalRegularOpen
  have hupper : ∀ z ∈ K, ∀ v : TangentSpace I3 z,
      gt.inner z v v ≤ (2 : ℝ)^2 * L.metric.inner z v v := by
    intro z hz v
    have hb := (Geometry.Metric.inner_bounds_of_metricDerivNorm_le
      L.metric gt z (hclose (τ n) hn z hz).le v).2
    have hnn := metric_inner_self_nonneg L.metric z v
    nlinarith
  have hsmall : (4 : ℝ) < eps⁻¹ := by linarith
  have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1 + eps by linarith [nk.eps_pos]),
      Real.sqrt_nonneg (1 + eps)]
  have hb (y : G.terminalRegularOpen) (hy : y ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
      riemannianEDistOf L.metric p y ≤ ENNReal.ofReal (20 / Real.sqrt Q) := by
    exact (nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 4) hsmall hy).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by nlinarith) hroot.le))
  have hcap := Geometry.Metric.riemannianEDistOf_ball_subset_of_le_frontier_distance
    (G.flow.base.metric (τ n)) (cap n).center_inside
    (r := ENNReal.ofReal (10000 / Real.sqrt (G.flow.scalar (τ n) x.val))) (by
      intro z hz
      have hztube : z ∈ (cap n).tube := ((cap n).overlap_eq.symm ▸ hz).2
      exact (ENNReal.ofReal_le_ofReal (depth n z hztube)).trans ENNReal.ofReal_toReal_le)
  have hdist' (y : G.terminalRegularOpen)
      (hy : y ∈ nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4)) :
      riemannianEDistOf (G.flow.base.metric (τ n)) p.val y.val ≤
        ENNReal.ofReal (40 / Real.sqrt Q) := by
    have hdy : riemannianEDistOf L.metric p y < ENNReal.ofReal (30 / Real.sqrt Q) :=
      (hb y hy).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
        (div_lt_div_of_pos_right (by norm_num) hroot))
    have hdist := KappaSolutions.edistOf_map_le_of_metric_upper_on_ball L.metric gt
      (DifferentialGeometry.PartialDiffeomorph.refl G.terminalRegularOpen) p y
      (by positivity : 0 < 30 / Real.sqrt Q) (by norm_num : (0 : ℝ) < 2)
      (by intro z hz; trivial) (by
        intro z hz v
        change gt.inner z (mfderiv I3 I3 id z v) (mfderiv I3 I3 id z v) ≤ _
        simpa only [mfderiv_id, ContinuousLinearMap.id_apply] using hupper z hz v) hdy
    apply (riemannianEDistOf_le_restrictOpen (G.flow.base.metric (τ n))
      G.terminalRegularOpen p y).trans
    apply hdist.trans
    calc
      ENNReal.ofReal 2 * riemannianEDistOf L.metric p y ≤
          ENNReal.ofReal 2 * ENNReal.ofReal (20 / Real.sqrt Q) := mul_le_mul' le_rfl (hb y hy)
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
  rintro _ ⟨y, hy, rfl⟩
  apply hcap
  have hxy : riemannianEDistOf (G.flow.base.metric (τ n)) x.val y.val ≤
      ENNReal.ofReal (80 / Real.sqrt Q) := by
    have hpx := hdist' x hxx
    rw [riemannianEDistOf_comm] at hpx
    apply ((riemannianEDistOf_triangle (G.flow.base.metric (τ n)) x.val p.val y.val).trans
      (add_le_add hpx (hdist' y hy))).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hrootn : Real.sqrt (G.flow.scalar (τ n) x.val) ≤ 2 * Real.sqrt Q := by
    nlinarith [Real.sq_sqrt hRn.le, Real.sq_sqrt hQ.le,
      Real.sqrt_nonneg (G.flow.scalar (τ n) x.val)]
  apply hxy.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity :
    0 < 10000 / Real.sqrt (G.flow.scalar (τ n) x.val))).mpr
  apply (div_lt_div_iff₀ hroot (Real.sqrt_pos.mpr hRn)).mpr
  nlinarith

theorem TerminalLimitMetric.eventually_canonical_cap_core
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hx : 0 < metricScalarAt L.metric x)
    {epsCanonical eps C1 C2 : ℝ}
    (W : ∀ n, CanonicalWitness G.flow epsCanonical C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (cap : ∀ n, LocalCap G.flow epsCanonical x.val (τ n) (W n).domain.carrier)
    (depth : ∀ n, ∀ y ∈ (cap n).tube,
      10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
        metricDistance (G.flow.base.metric (τ n)) x.val y)
    (hcap : ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) :
    ∀ᶠ n in atTop, ∃ K : CompactDomain G.terminalRegularOpen,
      Subtype.val '' K.carrier = (cap n).core.carrier ∧
      Nonempty (CapCore K.carrier) ∧ x ∈ interior K.carrier ∧
      (∀ y ∈ K.carrier,
        3 * metricScalarAt L.metric x / (4 * C2) < metricScalarAt L.metric y ∧
        metricScalarAt L.metric y < 3 * C2 * metricScalarAt L.metric x / 2) := by
  obtain ⟨K₀, hK₀, v, neck, _, _, hcapture⟩ :=
    L.eventually_cap_neck_compact_capture hτ x W hW cap depth hcap
  have hbound := L.eventually_scalar_bounds_on_canonical_domains hτ x hx W hK₀
    (hcapture.mono fun n hn => subset_union_left.trans hn)
  filter_upwards [hcapture, hbound] with n hcn hbn
  have hcoreU : (cap n).core.carrier ⊆ (W n).domain.carrier :=
    (cap n).core_inside.trans interior_subset
  have hcore : (cap n).core.carrier ⊆ G.terminalRegularOpen := by
    intro y hy
    obtain ⟨z, _, hz⟩ := hcn (Or.inl (hcoreU hy))
    exact hz ▸ z.property
  let K := (cap n).core.restrictOpen G.terminalRegularOpen hcore
  refine ⟨K, (cap n).core.image_restrictOpen_carrier _ _,
    (cap n).coreModel.nonempty_preimage_open _ hcore, ?_, ?_⟩
  · rw [CompactDomain.interior_restrictOpen_carrier]
    exact (cap n).center_inside
  · intro y hy
    exact hbn y (hcoreU hy)

private theorem spatial_neck_or_cap_core_of_canonical_sequence
    (L : G.TerminalLimitMetric) {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝[<] s))
    (x : G.terminalRegularOpen) (hxpos : 0 < metricScalarAt L.metric x)
    {eps δ C1 C2 : ℝ} (hδsmall : δ ≤ 1 / 8646)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n))
    (hW : ∀ n, (W n).capTubeHasNeckChart eps)
    (halternatives :
      (∃ neck : ∀ n, LocalNeck G.flow eps x.val (τ n) (W n).domain.carrier,
        ∀ n, (W n).alternative = CanonicalAlternative.neck (neck n)) ∨
      ∃ cap : ∀ n, LocalCap G.flow eps x.val (τ n) (W n).domain.carrier,
        ∃ depth : ∀ n, ∀ w ∈ (cap n).tube,
          10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
            metricDistance (G.flow.base.metric (τ n)) x.val w,
          ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n))
    {p : G.terminalRegularOpen} (nk : SpatialNeck L.metric δ p)
    (z : Sphere 2) {level : ℝ} (hlevel : |level| ≤ 4) (hxmap : nk.map (z, level) = x) :
    Nonempty (SpatialNeck L.metric δ x) ∨
      ∃ K : CompactDomain G.terminalRegularOpen,
        Nonempty (CapCore K.carrier) ∧
        nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
        (∀ w ∈ K.carrier,
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
            metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  have hC2pos : 0 < C2 := zero_lt_one.trans_le (W 0).one_le_comparison_constant
  have hδ11 : δ < 1 / 11 := hδsmall.trans_lt (by norm_num)
  rcases halternatives with hn | hc
  · obtain ⟨neck, _⟩ := hn
    obtain ⟨n, newNeck, _, _⟩ := (L.eventually_spatialNeck_of_incoming_strongNecks
      hτ x hxpos nk.eps_pos hδ11 hepsδ hfit (fun n => (neck n).strong)).exists
    exact Or.inl ⟨newNeck⟩
  · obtain ⟨cap, depth, hcap⟩ := hc
    have hcore := L.eventually_canonical_cap_core hτ x hxpos W hW cap depth hcap
    have hslab := L.eventually_spatial_neck_slab_subset_cap_core hτ nk hδsmall
      z hlevel hxmap cap depth
    obtain ⟨n, ⟨K, hK, hmodel, _, hscalar⟩, hinside⟩ := (hcore.and hslab).exists
    have hpre : K.carrier = (Subtype.val ⁻¹' (cap n).core.carrier : Set G.terminalRegularOpen) := by
      rw [← hK, preimage_image_eq _ Subtype.val_injective]
    have hlow : metricScalarAt L.metric x / (2 * C2) <
        3 * metricScalarAt L.metric x / (4 * C2) := by
      apply (div_lt_div_iff₀ (by positivity : 0 < 2 * C2) (by positivity : 0 < 4 * C2)).mpr
      nlinarith
    have hupp : 3 * C2 * metricScalarAt L.metric x / 2 <
        (2 * C2) * metricScalarAt L.metric x := by
      nlinarith [mul_pos hC2pos hxpos]
    have hband : ∀ w ∈ K.carrier,
        metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
          metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x :=
      fun w hw => ⟨hlow.trans (hscalar w hw).1, (hscalar w hw).2.trans hupp⟩
    refine Or.inr ⟨K, hmodel, ?_, hband⟩
    · rw [hpre, ← G.terminalRegularOpen.isOpenEmbedding'.isOpenMap.preimage_interior_eq_interior_preimage
        G.terminalRegularOpen.isOpenEmbedding'.continuous]
      intro w hw
      exact hinside ⟨w, hw, rfl⟩

theorem exists_uniform_spatial_neck_or_cap_core
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8646) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (p x y : G.terminalRegularOpen),
        q < metricScalarAt L.metric x → y.val ∈ connectedComponent x.val →
        C * metricScalarAt L.metric y < metricScalarAt L.metric x →
        ∀ (nk : SpatialNeck L.metric δ p) (z : Sphere 2) (level : ℝ),
          |level| ≤ 4 → nk.map (z, level) = x →
          Nonempty (SpatialNeck L.metric δ x) ∨
          ∃ K : CompactDomain G.terminalRegularOpen,
            Nonempty (CapCore K.carrier) ∧
            nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
            (∀ w ∈ K.carrier,
              metricScalarAt L.metric x / C < metricScalarAt L.metric w ∧
                metricScalarAt L.metric w < C * metricScalarAt L.metric x) ∧
            y ∉ K.carrier := by
  let eps := δ / 4
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsδ : eps < δ := by dsimp [eps]; linarith
  have hδ11 : δ < 1 / 11 := hδsmall.trans_lt (by norm_num)
  have hfit : δ⁻¹ + 1 ≤ eps⁻¹ := by
    change δ⁻¹ + 1 ≤ (δ / 4)⁻¹
    rw [inv_div]
    apply (le_div_iff₀ hδ).mpr
    field_simp
    linarith
  obtain ⟨C, hC, hsequence⟩ := exists_uniform_canonical_neck_or_cap_sequence.{u}
    heps (hepsδ.trans hδ11)
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨2 * C, by linarith, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hseq⟩ := hsequence P a s G
  refine ⟨q, hq, ?_⟩
  intro L p x y hqx hy hgap nk z level hlevel hxmap
  have hxpos : 0 < metricScalarAt L.metric x := hq.trans hqx
  have hgap' : C * metricScalarAt L.metric y < metricScalarAt L.metric x := by
    by_cases hypos : 0 ≤ metricScalarAt L.metric y
    · nlinarith [mul_nonneg hCpos.le hypos]
    · exact (mul_nonpos_of_nonneg_of_nonpos hCpos.le (le_of_not_ge hypos)).trans_lt hxpos
  obtain ⟨τ, _, _, hτ, W, hW, halt⟩ := hseq L x y hqx hy hgap'
  rcases spatial_neck_or_cap_core_of_canonical_sequence L hτ x hxpos hδsmall
    hepsδ hfit W hW halt nk z hlevel hxmap with hn | hc
  · exact Or.inl hn
  · obtain ⟨K, hmodel, hinside, hband⟩ := hc
    refine Or.inr ⟨K, hmodel, hinside, hband, ?_⟩
    intro hyK
    have hlowy := (div_lt_iff₀ (by positivity : 0 < 2 * C)).mp (hband y hyK).1
    nlinarith

theorem TerminalLimitMetric.spatial_neck_or_cap_core_of_canonical_neighborhoods_of_not_isCompact
    (L : G.TerminalLimitMetric) {δ q C1 C2 : ℝ}
    (hδsmall : δ ≤ 1 / 8646) (hq : 0 < q)
    (p x : G.terminalRegularOpen)
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x.val →
      ∃ W : CanonicalWitness G.flow (δ / 4) C1 C2 x.val t,
        W.capTubeHasNeckChart (δ / 4))
    (hqx : q < metricScalarAt L.metric x)
    (hnoncompact : ¬ IsCompact (connectedComponent x))
    (nk : SpatialNeck L.metric δ p) (z : Sphere 2) (level : ℝ)
    (hlevel : |level| ≤ 4) (hxmap : nk.map (z, level) = x) :
    Nonempty (SpatialNeck L.metric δ x) ∨
      ∃ K : CompactDomain G.terminalRegularOpen,
        Nonempty (CapCore K.carrier) ∧
        nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
        (∀ w ∈ K.carrier,
          metricScalarAt L.metric x / (2 * C2) < metricScalarAt L.metric w ∧
            metricScalarAt L.metric w < (2 * C2) * metricScalarAt L.metric x) := by
  have hδ : 0 < δ := nk.eps_pos
  have hepsδ : δ / 4 < δ := by linarith
  have hfit : δ⁻¹ + 1 ≤ (δ / 4)⁻¹ := by
    rw [inv_div]
    apply (le_div_iff₀ hδ).mpr
    field_simp
    linarith
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hqx)
  have hbranch := L.eventually_canonical_neck_or_cap_of_not_isCompact
    x hnoncompact (δ / 4) C1 C2
  obtain ⟨τ, _, _, hτ, W, hW, halt⟩ :=
    exists_canonical_neck_or_cap_sequence_of_eventually hcanonical hhigh hbranch
  exact spatial_neck_or_cap_core_of_canonical_sequence L hτ x (hq.trans hqx)
    hδsmall hepsδ hfit W hW halt nk z hlevel hxmap

theorem exists_uniform_spatial_neck_or_cap_core_of_not_isCompact
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8646) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (p x : G.terminalRegularOpen),
        q < metricScalarAt L.metric x → ¬ IsCompact (connectedComponent x) →
        ∀ (nk : SpatialNeck L.metric δ p) (z : Sphere 2) (level : ℝ),
          |level| ≤ 4 → nk.map (z, level) = x →
          Nonempty (SpatialNeck L.metric δ x) ∨
          ∃ K : CompactDomain G.terminalRegularOpen,
            Nonempty (CapCore K.carrier) ∧
            nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
            (∀ w ∈ K.carrier,
              metricScalarAt L.metric x / C < metricScalarAt L.metric w ∧
                metricScalarAt L.metric w < C * metricScalarAt L.metric x) := by
  obtain ⟨C, hC, hcanonical⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u}
      (show 0 < δ / 4 by positivity)
      (show δ / 4 < 1 / 11 by linarith)
  refine ⟨2 * C, by linarith, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hqcanonical⟩ := hcanonical P a s G
  refine ⟨q, hq, ?_⟩
  intro L p x hqx hnoncompact nk z level hlevel hxmap
  exact L.spatial_neck_or_cap_core_of_canonical_neighborhoods_of_not_isCompact
    hδsmall hq p x
    (fun t ht hx => hqcanonical x.val t ⟨ht.1.le, ht.2⟩ hx.le)
    hqx hnoncompact nk z level hlevel hxmap


theorem exists_uniform_spatial_neck_or_cap_core_on_component
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8646) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (c : G.terminalRegularOpen),
        let U := connectedComponentOpen (I := I3) c
        ∀ (p x y : U),
          q < metricScalarAt (L.metric.restrictOpen U) x →
          C * metricScalarAt (L.metric.restrictOpen U) y <
            metricScalarAt (L.metric.restrictOpen U) x →
          ∀ (nk : SpatialNeck (L.metric.restrictOpen U) δ p) (z : Sphere 2) (level : ℝ),
            |level| ≤ 4 → nk.map (z, level) = x →
            Nonempty (SpatialNeck (L.metric.restrictOpen U) δ x) ∨
            ∃ K : CompactDomain U,
              Nonempty (CapCore K.carrier) ∧
              nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
              (∀ w ∈ K.carrier,
                metricScalarAt (L.metric.restrictOpen U) x / C <
                  metricScalarAt (L.metric.restrictOpen U) w ∧
                  metricScalarAt (L.metric.restrictOpen U) w <
                    C * metricScalarAt (L.metric.restrictOpen U) x) ∧
              y ∉ K.carrier := by
  obtain ⟨C, hC, hmain⟩ := exists_uniform_spatial_neck_or_cap_core.{u} hδ hδsmall
  refine ⟨C, hC, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hqmain⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L c U p x y hqx hgap nk z level hlevel hx
  have hcomp : connectedComponent x.val = connectedComponent c :=
    (connectedComponent_eq x.property).symm
  have hxy : y.val ∈ connectedComponent x.val := hcomp.symm ▸ y.property
  have hxyambient : y.val.val ∈ connectedComponent x.val.val :=
    (continuous_subtype_val.image_connectedComponent_subset x.val) ⟨y.val, hxy, rfl⟩
  obtain ⟨nk₀, _, hmap, _, _, _⟩ := nk.exists_of_restrictOpen
  have hx₀ : nk₀.map (z, level) = x.val := by
    rw [hmap, hx]
  have hq₀ : q < metricScalarAt L.metric x.val := by
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hqx
  have hgap₀ : C * metricScalarAt L.metric y.val < metricScalarAt L.metric x.val := by
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hgap
  rcases hqmain L p.val x.val y.val hq₀ hxyambient hgap₀ nk₀ z level hlevel hx₀ with
    hn | hc
  · obtain ⟨newNeck⟩ := hn
    have hcapture : newNeck.map '' (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) ⊆ (U : Set G.terminalRegularOpen) := by
      change _ ⊆ connectedComponent c
      rw [← hcomp]
      exact newNeck.controlled_range_subset_connectedComponent
    exact Or.inl ⟨newNeck.restrictOpen hcapture⟩
  · obtain ⟨K₀, ⟨model⟩, hinside, hscalar, hyK⟩ := hc
    have hxK : x.val ∈ K₀.carrier := interior_subset (hinside
        ⟨(z, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hx₀⟩)
    have hKU : K₀.carrier ⊆ U := by
      change K₀.carrier ⊆ connectedComponent c
      rw [← hcomp]
      exact K₀.connected.subset_connectedComponent hxK
    let K := K₀.restrictOpen U hKU
    refine Or.inr ⟨K, model.nonempty_preimage_open U hKU, ?_, ?_, hyK⟩
    · rw [CompactDomain.interior_restrictOpen_carrier]
      rintro w ⟨v, hv, rfl⟩
      exact hinside ⟨v, hv, hmap v⟩
    · intro w hw
      simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hscalar w.val hw


theorem exists_uniform_spatial_neck_or_cap_core_on_noncompact_component
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8646) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
      ∀ (L : G.TerminalLimitMetric) (c : G.terminalRegularOpen),
        let U := connectedComponentOpen (I := I3) c
        ¬ IsCompact (connectedComponent c) → ∀ (p x : U),
          q < metricScalarAt (L.metric.restrictOpen U) x →
          ∀ (nk : SpatialNeck (L.metric.restrictOpen U) δ p) (z : Sphere 2) (level : ℝ),
            |level| ≤ 4 → nk.map (z, level) = x →
            Nonempty (SpatialNeck (L.metric.restrictOpen U) δ x) ∨
            ∃ K : CompactDomain U,
              Nonempty (CapCore K.carrier) ∧
              nk.map '' (univ ×ˢ Icc (-4 : ℝ) 4) ⊆ interior K.carrier ∧
              (∀ w ∈ K.carrier,
                metricScalarAt (L.metric.restrictOpen U) x / C <
                  metricScalarAt (L.metric.restrictOpen U) w ∧
                  metricScalarAt (L.metric.restrictOpen U) w <
                    C * metricScalarAt (L.metric.restrictOpen U) x) := by
  obtain ⟨C, hC, hmain⟩ := exists_uniform_spatial_neck_or_cap_core_of_not_isCompact.{u} hδ hδsmall
  refine ⟨C, hC, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hqmain⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L c U hnoncompact p x hqx nk z level hlevel hx
  have hcomp : connectedComponent x.val = connectedComponent c :=
    (connectedComponent_eq x.property).symm
  have hxnoncompact : ¬ IsCompact (connectedComponent x.val) := by
    rwa [hcomp]
  obtain ⟨nk₀, _, hmap, _, _, _⟩ := nk.exists_of_restrictOpen
  have hx₀ : nk₀.map (z, level) = x.val := by
    rw [hmap, hx]
  have hq₀ : q < metricScalarAt L.metric x.val := by
    simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hqx
  rcases hqmain L p.val x.val hq₀ hxnoncompact nk₀ z level hlevel hx₀ with
    hn | hc
  · obtain ⟨newNeck⟩ := hn
    have hcapture : newNeck.map '' (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹) ⊆ (U : Set G.terminalRegularOpen) := by
      change _ ⊆ connectedComponent c
      rw [← hcomp]
      exact newNeck.controlled_range_subset_connectedComponent
    exact Or.inl ⟨newNeck.restrictOpen hcapture⟩
  · obtain ⟨K₀, ⟨model⟩, hinside, hscalar⟩ := hc
    have hxK : x.val ∈ K₀.carrier := interior_subset (hinside
        ⟨(z, level), ⟨mem_univ _, abs_le.mp hlevel⟩, hx₀⟩)
    have hKU : K₀.carrier ⊆ U := by
      change K₀.carrier ⊆ connectedComponent c
      rw [← hcomp]
      exact K₀.connected.subset_connectedComponent hxK
    let K := K₀.restrictOpen U hKU
    refine Or.inr ⟨K, model.nonempty_preimage_open U hKU, ?_, ?_⟩
    · rw [CompactDomain.interior_restrictOpen_carrier]
      rintro w ⟨v, hv, rfl⟩
      exact hinside ⟨v, hv, hmap v⟩
    · intro w hw
      simpa only [DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen] using hscalar w.val hw

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
