import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckChainAxialArms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornNeckEssentiality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.HornEndpointRadius
import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Riemannian

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private theorem isClosed_riemannianClosedBallOf (g : SmoothRiemannianMetric I3 M) (x : M)
    (r : ℝ) : IsClosed (riemannianClosedBallOf g x r) := by
  have hdist : Continuous (fun z => riemannianEDistOf g x z) := continuous_riemannianEDist g x
  exact isClosed_le hdist continuous_const

private theorem ofReal_le_of_le_add {a b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ENNReal.ofReal a ≤ ENNReal.ofReal b + ENNReal.ofReal c) : a ≤ b + c := by
  rw [← ENNReal.ofReal_add hb hc] at h
  exact (ENNReal.ofReal_le_ofReal_iff (add_nonneg hb hc)).mp h

private theorem exists_minimizingArm_of_isCompact_closedBall (g : SmoothRiemannianMetric I3 M)
    {x y : M} {ell r : ℝ} (hell : 0 < ell) (hy : ENNReal.ofReal ell ≤ riemannianEDistOf g x y)
    (hy' : riemannianEDistOf g x y < ENNReal.ofReal r)
    (hK : IsCompact (riemannianClosedBallOf g x r)) :
    ∃ a : MinimizingArm g x, ell ≤ a.length ∧ a.point a.length = y ∧
      riemannianEDistOf g x y = ENNReal.ofReal a.length ∧
      ∀ s ∈ Icc 0 a.length, riemannianEDistOf g x (a.point s) = ENNReal.ofReal s := by
  obtain ⟨γ, h0, h1, _, hmin⟩ :=
    exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall g x y hy' hK
  have hfin : riemannianEDistOf g x y ≠ ⊤ := ne_top_of_lt hy'
  set L := (riemannianEDistOf g x y).toReal with hL
  have hellL : ell ≤ L := (ENNReal.ofReal_le_iff_le_toReal hfin).mp hy
  have hLpos : 0 < L := hell.trans_le hellL
  have h0L : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hLpos.le⟩
  refine ⟨{ length := L
            length_pos := hLpos
            point := γ
            start := h0
            minimizing := fun s hs t ht => by
              unfold metricDistance
              rw [hmin s hs t ht, ENNReal.toReal_ofReal (abs_nonneg _)] },
    hellL, h1, (ENNReal.ofReal_toReal hfin).symm, ?_⟩
  intro s hs
  have h := hmin 0 h0L s hs
  rw [h0, zero_sub, abs_neg, abs_of_nonneg hs.1] at h
  exact h

private theorem exists_arm_point_mem_side {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M}
    (nk : SpatialNeck g eps x) {D r : ℝ} (hD : 7 < D)
    (hK : IsCompact (riemannianClosedBallOf g x r)) {W W' : Set M} (hW : IsOpen W)
    (hW' : IsOpen W') (hWW' : Disjoint W W')
    (hcover : riemannianBallOf g x r \ nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ W ∪ W')
    {y : M} (hyW : y ∈ W)
    (hy : ENNReal.ofReal (D / Real.sqrt (metricScalarAt g x)) ≤ riemannianEDistOf g x y)
    (hy' : riemannianEDistOf g x y < ENNReal.ofReal r) :
    ∃ a : MinimizingArm g x, D / Real.sqrt (metricScalarAt g x) ≤ a.length ∧
      a.point (D / Real.sqrt (metricScalarAt g x)) ∈ W ∧
      riemannianEDistOf g x (a.point (D / Real.sqrt (metricScalarAt g x))) =
        ENNReal.ofReal (D / Real.sqrt (metricScalarAt g x)) := by
  set sQ := Real.sqrt (metricScalarAt g x) with hsQdef
  have hsQ : 0 < sQ := Real.sqrt_pos.mpr nk.Q_pos
  set ell := D / sQ with hell
  have hellpos : 0 < ell := div_pos (by linarith) hsQ
  obtain ⟨a, hla, hend, hlen, hdist⟩ :=
    exists_minimizingArm_of_isCompact_closedBall g hellpos hy hy' hK
  have hsub : a.point '' Icc ell a.length ⊆ W ∪ W' := by
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : s ∈ Icc (0 : ℝ) a.length := ⟨hellpos.le.trans hs.1, hs.2⟩
    have hds := hdist s hs0
    refine hcover ⟨?_, ?_⟩
    · change riemannianEDistOf g x (a.point s) < ENNReal.ofReal r
      rw [hds]
      exact (ENNReal.ofReal_le_ofReal hs.2).trans_lt (hlen ▸ hy')
    · intro hS
      have hb := nk.central_sphere_subset_closedBall hS
      change riemannianEDistOf g x (a.point s) ≤ ENNReal.ofReal (7 / sQ) at hb
      rw [hds] at hb
      have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
      have h7 : 7 / sQ < ell := div_lt_div_of_pos_right hD hsQ
      linarith [hs.1]
  have hpre : IsPreconnected (a.point '' Icc ell a.length) :=
    isPreconnected_Icc.image _ (a.continuousOn_point.mono (Icc_subset_Icc_left hellpos.le))
  have hyT : y ∈ a.point '' Icc ell a.length := ⟨a.length, ⟨hla, le_rfl⟩, hend⟩
  have hpT : a.point ell ∈ a.point '' Icc ell a.length := ⟨ell, ⟨le_rfl, hla⟩, rfl⟩
  rcases hpre.subset_or_subset hW hW' hWW' hsub with hT | hT
  · exact ⟨a, hla, hT hpT, hdist ell ⟨hellpos.le, hla⟩⟩
  · exact absurd (hT hyT) (disjoint_left.mp hWW' hyW)

theorem SpatialNeck.exists_minimizingArms_of_locally_separating_centralSphere
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {x : M} (nk : SpatialNeck g eps x)
    {D r : ℝ} (hD : 28 ≤ D) (hr : 3 * (D / Real.sqrt (metricScalarAt g x)) < r)
    (hK : IsCompact (riemannianClosedBallOf g x r)) {U V : Set M} (hU : IsOpen U)
    (hV : IsOpen V) (hUV : Disjoint U V)
    (hcover : riemannianBallOf g x r \ nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ U ∪ V)
    {y z : M} (hyU : y ∈ U) (hzV : z ∈ V)
    (hy : ENNReal.ofReal (D / Real.sqrt (metricScalarAt g x)) ≤ riemannianEDistOf g x y)
    (hy' : riemannianEDistOf g x y < ENNReal.ofReal r)
    (hz : ENNReal.ofReal (D / Real.sqrt (metricScalarAt g x)) ≤ riemannianEDistOf g x z)
    (hz' : riemannianEDistOf g x z < ENNReal.ofReal r) :
    ∃ (arms : Fin 2 → MinimizingArm g x) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g x) * ell j ∈ Icc D (2 * D)) ∧
      Real.pi / 2 ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  set S := nk.map '' (univ ×ˢ ({0} : Set ℝ)) with hSdef
  set sQ := Real.sqrt (metricScalarAt g x) with hsQdef
  have hsQ : 0 < sQ := Real.sqrt_pos.mpr nk.Q_pos
  set ell := D / sQ with hell
  have hellpos : 0 < ell := div_pos (by linarith) hsQ
  obtain ⟨a, ha, hpU, hpx⟩ :=
    exists_arm_point_mem_side nk (by linarith) hK hU hV hUV hcover hyU hy hy'
  obtain ⟨b, hb, hqV, hqx⟩ :=
    exists_arm_point_mem_side nk (by linarith) hK hV hU hUV.symm
      (by rw [union_comm]; exact hcover) hzV hz hz'
  set p := a.point ell with hp
  set q := b.point ell with hq
  have hpq : riemannianEDistOf g p q ≤ ENNReal.ofReal (2 * ell) := by
    calc riemannianEDistOf g p q ≤ riemannianEDistOf g p x + riemannianEDistOf g x q :=
          riemannianEDistOf_triangle g p x q
      _ = ENNReal.ofReal ell + ENNReal.ofReal ell := by
          rw [riemannianEDistOf_comm g p x, hpx, hqx]
      _ = ENNReal.ofReal (2 * ell) := by
          rw [← ENNReal.ofReal_add hellpos.le hellpos.le]
          ring_nf
  have hrl : 0 < r - ell := by linarith
  have hKp : IsCompact (riemannianClosedBallOf g p (r - ell)) := by
    refine hK.of_isClosed_subset (isClosed_riemannianClosedBallOf g p _) ?_
    intro w hw
    change riemannianEDistOf g p w ≤ ENNReal.ofReal (r - ell) at hw
    change riemannianEDistOf g x w ≤ ENNReal.ofReal r
    calc riemannianEDistOf g x w ≤ riemannianEDistOf g x p + riemannianEDistOf g p w :=
          riemannianEDistOf_triangle g x p w
      _ ≤ ENNReal.ofReal ell + ENNReal.ofReal (r - ell) := by rw [hpx]; gcongr
      _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_add hellpos.le hrl.le]
          ring_nf
  have hpq' : riemannianEDistOf g p q < ENNReal.ofReal (r - ell) :=
    hpq.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hrl).mpr (by linarith))
  obtain ⟨γ, hγ0, hγ1, hγs, hγmin⟩ :=
    exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall g p q hpq' hKp
  have hfin : riemannianEDistOf g p q ≠ ⊤ := ne_top_of_lt hpq'
  set L := (riemannianEDistOf g p q).toReal with hLdef
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hL2 : L ≤ 2 * ell := ENNReal.toReal_le_of_le_ofReal (by positivity) hpq
  have h0L : (0 : ℝ) ∈ Icc 0 L := ⟨le_rfl, hL0⟩
  have hLL : L ∈ Icc 0 L := ⟨hL0, le_rfl⟩
  have hcross : ∃ s ∈ Icc 0 L, γ s ∈ S := by
    by_contra hno
    have hnone : ∀ s ∈ Icc 0 L, γ s ∉ S := fun s hs h => hno ⟨s, hs, h⟩
    have hsub : γ '' Icc 0 L ⊆ U ∪ V := by
      rintro _ ⟨s, hs, rfl⟩
      refine hcover ⟨?_, hnone s hs⟩
      change riemannianEDistOf g x (γ s) < ENNReal.ofReal r
      have hps := hγmin 0 h0L s hs
      rw [hγ0, zero_sub, abs_neg, abs_of_nonneg hs.1] at hps
      calc riemannianEDistOf g x (γ s) ≤ riemannianEDistOf g x p + riemannianEDistOf g p (γ s) :=
            riemannianEDistOf_triangle g x p (γ s)
        _ = ENNReal.ofReal (ell + s) := by
            rw [hpx, hps, ENNReal.ofReal_add hellpos.le hs.1]
        _ < ENNReal.ofReal r :=
            (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith [hs.2])
    have hpre : IsPreconnected (γ '' Icc 0 L) := isPreconnected_Icc.image _ hγs.continuousOn
    rcases hpre.subset_or_subset hU hV hUV hsub with hT | hT
    · exact disjoint_left.mp hUV (hT ⟨L, hLL, hγ1⟩) hqV
    · exact disjoint_left.mp hUV hpU (hT ⟨0, h0L, hγ0⟩)
  obtain ⟨s, hs, hsS⟩ := hcross
  have hwx : riemannianEDistOf g x (γ s) ≤ ENNReal.ofReal (7 / sQ) :=
    nk.central_sphere_subset_closedBall hsS
  have hws : riemannianEDistOf g (γ s) p = ENNReal.ofReal s := by
    have h := hγmin s hs 0 h0L
    rw [hγ0, sub_zero, abs_of_nonneg hs.1] at h
    exact h
  have hwq : riemannianEDistOf g (γ s) q = ENNReal.ofReal (L - s) := by
    have h := hγmin s hs L hLL
    rw [hγ1, abs_sub_comm, abs_of_nonneg (by linarith [hs.2])] at h
    exact h
  have h7 : (0 : ℝ) ≤ 7 / sQ := by positivity
  have hle1 : ell ≤ 7 / sQ + s := by
    apply ofReal_le_of_le_add h7 hs.1
    calc ENNReal.ofReal ell = riemannianEDistOf g x p := hpx.symm
      _ ≤ riemannianEDistOf g x (γ s) + riemannianEDistOf g (γ s) p :=
          riemannianEDistOf_triangle g x (γ s) p
      _ ≤ ENNReal.ofReal (7 / sQ) + ENNReal.ofReal s := by rw [hws]; gcongr
  have hle2 : ell ≤ 7 / sQ + (L - s) := by
    apply ofReal_le_of_le_add h7 (by linarith [hs.2])
    calc ENNReal.ofReal ell = riemannianEDistOf g x q := hqx.symm
      _ ≤ riemannianEDistOf g x (γ s) + riemannianEDistOf g (γ s) q :=
          riemannianEDistOf_triangle g x (γ s) q
      _ ≤ ENNReal.ofReal (7 / sQ) + ENNReal.ofReal (L - s) := by rw [hwq]; gcongr
  have h14 : 2 * (7 / sQ) ≤ ell / 2 := by
    rw [hell, div_div, mul_div_assoc', div_le_div_iff₀ hsQ (by positivity)]
    nlinarith
  have hdpq : metricDistance g p q = L := rfl
  have hw : 3 / 2 * ell ≤ metricDistance g p q := by rw [hdpq]; linarith
  refine ⟨![a, b], fun _ => ell, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨hellpos, ha⟩
    · exact ⟨hellpos, hb⟩
  · intro j
    have hmul : sQ * ell = D := by
      rw [hell]
      field_simp
    change sQ * ell ∈ Icc D (2 * D)
    rw [hmul]
    exact ⟨le_rfl, by linarith⟩
  · change Real.pi / 2 ≤ comparisonAngle ell ell (metricDistance g p q)
    refine le_of_not_gt fun hlt => ?_
    have hpos := Real.arccos_lt_pi_div_two.mp hlt
    have hnum : ell ^ 2 + ell ^ 2 - metricDistance g p q ^ 2 ≤ 0 := by
      have h1 : 0 ≤ 3 / 2 * ell := by positivity
      have h2 := mul_self_le_mul_self h1 hw
      nlinarith
    have hden : 0 ≤ 2 * ell * ell := by positivity
    have hnp := div_nonpos_of_nonpos_of_nonneg hnum hden
    linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_strongNeck_threshold_of_locally_separating_centralSphere
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ D Q₀ theta : ℝ, 0 < D ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (x : P.Carrier) (t : ℝ), t < s → Q₀ ≤ G.flow.scalar t x →
        a ≤ t - theta / G.flow.scalar t x →
        Perelman.PhiAlmostNonnegative G.flow (Icc (t - theta / G.flow.scalar t x) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t x ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        ∀ {eps : ℝ} (nk : SpatialNeck (G.flow.base.metric t) eps x), eps ≤ 1 / 252 →
        ∀ U V : Set P.Carrier, IsOpen U → IsOpen V → Disjoint U V →
          riemannianBallOf (G.flow.base.metric t) x (4 * D / Real.sqrt (G.flow.scalar t x)) \
            nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ U ∪ V →
        ∀ y z : P.Carrier, y ∈ U → z ∈ V →
          ENNReal.ofReal (D / Real.sqrt (G.flow.scalar t x)) ≤
            riemannianEDistOf (G.flow.base.metric t) x y →
          riemannianEDistOf (G.flow.base.metric t) x y <
            ENNReal.ofReal (4 * D / Real.sqrt (G.flow.scalar t x)) →
          ENNReal.ofReal (D / Real.sqrt (G.flow.scalar t x)) ≤
            riemannianEDistOf (G.flow.base.metric t) x z →
          riemannianEDistOf (G.flow.base.metric t) x z <
            ENNReal.ofReal (4 * D / Real.sqrt (G.flow.scalar t x)) →
          Nonempty (StrongNeck G.flow delta x t) := by
  obtain ⟨D, Q₀, theta, hD, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_minimizing_arms.{u} hdelta hdelta1 Real.pi_div_two_pos
      hkappa hrho hPhi
  refine ⟨D, Q₀, theta, hD, hQ₀, htheta, ?_⟩
  intro P a s G x t hts hQ hwin hpinch hnc eps nk heps U V hU hV hUV hcover y z hyU hzV
    hy hy' hz hz'
  have heps0 := nk.eps_pos
  have hg : RiemannianMetricComplete (G.flow.base.metric t) := RiemannianMetricComplete.of_compact _
  rcases lt_or_ge (9 * D) eps⁻¹ with hsmall | hlarge
  · obtain ⟨arms, ell, hell, hlen, hang⟩ := nk.exists_axial_minimizingArms hg hD hsmall
    refine hthr P a s G x t hts hQ hwin hpinch hnc arms ell hell hlen (le_trans ?_ hang)
    refine le_of_not_gt fun hlt => ?_
    have hpos := Real.arccos_lt_pi_div_two.mp hlt
    have hnp : (3 * eps - 1) / (1 + eps) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hinv : (252 : ℝ) ≤ eps⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) heps0, ← one_div]
      exact heps
    have hsQ : 0 < Real.sqrt (G.flow.scalar t x) := Real.sqrt_pos.mpr nk.Q_pos
    have hr : 3 * (D / Real.sqrt (G.flow.scalar t x)) < 4 * D / Real.sqrt (G.flow.scalar t x) := by
      rw [mul_div_assoc']
      exact div_lt_div_of_pos_right (by linarith) hsQ
    have hK : IsCompact (riemannianClosedBallOf (G.flow.base.metric t) x
        (4 * D / Real.sqrt (G.flow.scalar t x))) :=
      (isClosed_le (continuous_riemannianEDist (G.flow.base.metric t) x)
        continuous_const).isCompact
    obtain ⟨arms, ell, hell, hlen, hang⟩ :=
      nk.exists_minimizingArms_of_locally_separating_centralSphere (by linarith) hr hK hU hV hUV
        hcover hyU hzV hy hy' hz hz'
    exact hthr P a s G x t hts hQ hwin hpinch hnc arms ell hell hlen hang

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Topology.SphereSeparation

universe u

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s} :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

variable {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ)

theorem closure_positiveHornMap_image_subset (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) {A : Set positiveHornDomain} {a : ℝ} (ha : 0 < a)
    (hA : ∀ q ∈ A, a ≤ q.val.2) :
    closure (P.positiveHornMap c e '' A) ⊆ P.positiveHornMap c e '' closure A := by
  let ι : positiveHornDomain → HalfNeckCylinder := fun q => ⟨q.val, q.property.2.le⟩
  let F : HalfNeckCylinder → D.slab.terminalRegularOpen := fun p => P.horn c e p.1
  have hF : IsClosedMap F := (P.horn_proper c e).isClosedMap
  have hιc : Continuous ι := continuous_subtype_val.subtype_mk _
  have hind : Topology.IsInducing ι :=
    Topology.IsInducing.of_comp hιc continuous_subtype_val Topology.IsInducing.subtypeVal
  have himg : P.positiveHornMap c e '' A = F '' (ι '' A) := by
    rw [image_image]
    rfl
  have hcl : closure (F '' (ι '' A)) ⊆ F '' closure (ι '' A) :=
    closure_minimal (image_mono subset_closure) (hF _ isClosed_closure)
  rw [himg]
  intro w hw
  obtain ⟨h, hh, rfl⟩ := hcl hw
  have hclosed : IsClosed {h : HalfNeckCylinder | a ≤ h.1.2} :=
    isClosed_le continuous_const (continuous_snd.comp continuous_subtype_val)
  have hge : a ≤ h.1.2 := by
    refine closure_minimal ?_ hclosed hh
    rintro _ ⟨q, hq, rfl⟩
    exact hA q hq
  let q : positiveHornDomain := ⟨h.1, mem_univ _, ha.trans_le hge⟩
  have hq : ι q = h := rfl
  have hqA : q ∈ closure A := by
    rw [hind.closure_eq_preimage_closure_image]
    change ι q ∈ closure (ι '' A)
    rw [hq]
    exact hh
  exact ⟨q, hqA, rfl⟩

private theorem horn_sides_of_complementPair (c : ConnectedComponents D.slab.terminalRegularOpen)
    (e : P.hornIndex c) {S : Set positiveHornDomain} (p : ComplementPair S)
    (hclr : closure p.right = p.right ∪ S) {R : ℝ}
    (hlo : ∀ q : positiveHornDomain, q.val.2 < Real.exp (-R) → q ∈ p.left) :
    IsOpen (P.positiveHornMap c e '' p.right) ∧
    closure (P.positiveHornMap c e '' p.right) ⊆
      P.positiveHornMap c e '' p.right ∪ P.positiveHornMap c e '' S ∧
    Disjoint (P.positiveHornMap c e '' p.left) (closure (P.positiveHornMap c e '' p.right)) ∧
    Disjoint (P.positiveHornMap c e '' S) (P.positiveHornMap c e '' p.right) ∧
    Disjoint (P.core c) (closure (P.positiveHornMap c e '' p.right)) := by
  have hinj : Function.Injective (P.positiveHornMap c e) := fun q q' h =>
    Subtype.ext (P.horn_injOn c e
      ⟨mem_univ _, le_of_lt (show (0 : ℝ) < q.val.2 from q.property.2)⟩
      ⟨mem_univ _, le_of_lt (show (0 : ℝ) < q'.val.2 from q'.property.2)⟩ h)
  have hsub : closure (P.positiveHornMap c e '' p.right) ⊆
      P.positiveHornMap c e '' p.right ∪ P.positiveHornMap c e '' S := by
    have h := P.closure_positiveHornMap_image_subset c e (A := p.right) (Real.exp_pos (-R))
      (fun q hq => le_of_not_gt fun hlt => disjoint_left.mp p.disjoint (hlo q hlt) hq)
    rw [hclr, image_union] at h
    exact h
  refine ⟨(P.positiveHornMap_local c e).isOpenMap _ p.isOpen_right, hsub, ?_, ?_, ?_⟩
  · rw [disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ hcl
    rcases hsub hcl with ⟨q', hq', he⟩ | ⟨q', hq', he⟩
    · exact disjoint_left.mp p.disjoint hq (hinj he ▸ hq')
    · exact disjoint_left.mp p.left_disjoint_sphere hq (hinj he ▸ hq')
  · rw [disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ ⟨q', hq', he⟩
    exact disjoint_left.mp p.right_disjoint_sphere (hinj he ▸ hq') hq
  · rw [disjoint_left]
    intro w hw hcl
    rcases hsub hcl with ⟨q, _, rfl⟩ | ⟨q, _, rfl⟩ <;>
      exact P.horn_pos_notMem_core c e q.val.1 q.property.2 hw

theorem exists_deep_horn_centralSphere_sides :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ e : P.hornIndex c, ∃ Q : ℝ, 0 < Q ∧
        ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k), δ ≤ ε →
          ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e → Q < N.scale →
          ∃ U V : Set D.slab.terminalRegularOpen, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
            U ∪ V = (N.chart '' {z | z.val.2 = 0})ᶜ ∧ P.core c ⊆ U ∧
            (∃ u₀ : ℝ, ∀ y u, u₀ < u → P.horn c e (y, u) ∈ V) ∧
            ∀ w ∈ U, ∀ z ∈ V, z ∉ connectedComponentIn (N.chart '' {z | z.val.2 = 0})ᶜ w := by
  obtain ⟨eta, heta, hdeep⟩ := exists_deep_horn_neck_end_separation_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro D ε Λ P hε c hc e
  obtain ⟨Q, hQ, hQdeep⟩ := hdeep P hε c hc e 0
  refine ⟨Q, hQ, ?_⟩
  intro δ k N hδ hk hcenter hscale
  obtain ⟨Θ, -, hmap, -, p, R, -, -, hfr, -, hclr, -, -, hlo, hhi, -⟩ :=
    hQdeep N hδ hk hcenter hscale
  obtain ⟨hVo, hsub, -, hSV, hcore⟩ := P.horn_sides_of_complementPair c e p hclr hlo
  have hSig : N.chart '' {z | z.val.2 = 0} = P.positiveHornMap c e '' range (fun q : Sphere 2 =>
      Θ ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
        inv_pos.mpr N.delta_pos⟩) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨_, ⟨z.val.1, rfl⟩, ?_⟩
      change P.horn c e (Θ _).val = _
      rw [hmap]
      congr 1
      exact Subtype.ext (Prod.ext rfl (Eq.symm hz))
    · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨_, rfl, (hmap _).symm⟩
  have hcont : Continuous (P.positiveHornMap c e) :=
    (P.positiveHornMap_local c e).contMDiff.continuous
  have hSsub : P.positiveHornMap c e '' range (fun q : Sphere 2 =>
      Θ ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
        inv_pos.mpr N.delta_pos⟩) ⊆ closure (P.positiveHornMap c e '' p.right) := by
    refine (image_mono ?_).trans (image_closure_subset_closure_image hcont)
    exact fun w hw => frontier_subset_closure (hfr.symm ▸ hw)
  set V := P.positiveHornMap c e '' p.right with hVdef
  have hUo : IsOpen (closure V)ᶜ := isClosed_closure.isOpen_compl
  have hdisj : Disjoint (closure V)ᶜ V := disjoint_compl_left_iff_subset.mpr subset_closure
  have hUV : (closure V)ᶜ ∪ V = (N.chart '' {z | z.val.2 = 0})ᶜ := by
    rw [hSig]
    ext w
    constructor
    · rintro (hw | hw) hS
      · exact hw (hSsub hS)
      · exact disjoint_left.mp hSV hS hw
    · intro hw
      by_cases h : w ∈ closure V
      · rcases hsub h with h1 | h1
        · exact Or.inr h1
        · exact absurd h1 hw
      · exact Or.inl h
  refine ⟨(closure V)ᶜ, V, hUo, hVo, hdisj, hUV, fun w hw hcl => disjoint_left.mp hcore hw hcl,
    ⟨Real.exp R, fun y u hu => ⟨⟨(y, u), mem_univ _, (Real.exp_pos R).trans hu⟩,
      hhi _ hu, rfl⟩⟩, ?_⟩
  intro w hw z hz hzc
  have hwS : w ∈ (N.chart '' {z | z.val.2 = 0})ᶜ := hUV ▸ Or.inl hw
  have hsubc : connectedComponentIn (N.chart '' {z | z.val.2 = 0})ᶜ w ⊆ (closure V)ᶜ ∪ V := by
    rw [hUV]
    exact connectedComponentIn_subset _ _
  rcases isPreconnected_connectedComponentIn.subset_or_subset hUo hVo hdisj hsubc with h | h
  · exact disjoint_left.mp hdisj (h hzc) hz
  · exact disjoint_left.mp hdisj hw (h (mem_connectedComponentIn hwS))

theorem isCompact_riemannianClosedBallOf_of_scalar_le
    (c : ConnectedComponents D.slab.terminalRegularOpen) (hc : c ∈ P.component)
    {x : D.slab.terminalRegularOpen} (hx : ConnectedComponents.mk x = c) {r r' K : ℝ}
    (hr : 0 < r) (hr' : r' < r)
    (hK : ∀ z ∈ riemannianBallOf D.terminal.metric x r, metricScalarAt D.terminal.metric z ≤ K) :
    IsCompact (riemannianClosedBallOf D.terminal.metric x r') := by
  have := P.hornIndex_finite c
  choose uL huL using fun e' : P.hornIndex c => P.horn_scalar_diverges c e' K
  have hKset : IsCompact (P.core c ∪
      ⋃ e' : P.hornIndex c, P.horn c e' '' (univ ×ˢ Icc 0 (uL e'))) :=
    (P.core_isCompact c hc).union (isCompact_iUnion fun e' =>
      (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
        ((P.horn_smooth c e').continuousOn.mono (prod_mono subset_rfl Icc_subset_Ici_self)))
  refine hKset.of_isClosed_subset
    (isClosed_le (continuous_riemannianEDist D.terminal.metric x) continuous_const) ?_
  intro z hz
  change riemannianEDistOf D.terminal.metric x z ≤ ENNReal.ofReal r' at hz
  have hlt : riemannianEDistOf D.terminal.metric x z < ENNReal.ofReal r :=
    hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hr')
  have hRz := hK z hlt
  obtain ⟨γ, hγ0, hγ1, hγ, -⟩ := DifferentialGeometry.exists_lt_of_edistOf_lt D.terminal.metric hlt
  have hconn : z ∈ connectedComponent x :=
    (isPreconnected_Icc.image γ hγ.continuousOn).subset_connectedComponent
      ⟨0, ⟨le_rfl, zero_le_one⟩, hγ0⟩ ⟨1, ⟨zero_le_one, le_rfl⟩, hγ1⟩
  have hzc : z ∈ {w : D.slab.terminalRegularOpen | ConnectedComponents.mk w = c} := by
    change ConnectedComponents.mk z = c
    rw [← hx]
    exact ConnectedComponents.coe_eq_coe'.mpr hconn
  rw [P.horn_covers_component c hc] at hzc
  rcases hzc with hzc | hzc
  · exact Or.inl hzc
  · obtain ⟨e', ⟨q, hq0⟩, rfl⟩ := mem_iUnion.mp hzc
    refine Or.inr (mem_iUnion.mpr ⟨e', q, ⟨mem_univ _, hq0, ?_⟩, rfl⟩)
    by_contra hge
    exact absurd hRz (not_le.mpr (huL e' q.1 q.2 (le_of_not_ge hge)))

theorem exists_minimizingArms_of_horn_point :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ {D : OneStepIncoming.{u}} {ε Λ : ℝ} (P : TerminalCorePresentation D ε Λ), ε ≤ eta →
        ∀ (c : ConnectedComponents D.slab.terminalRegularOpen), c ∈ P.component →
        ∀ e : P.hornIndex c, ∃ Q : ℝ, 0 < Q ∧
        ∀ {δ : ℝ} {k : ℕ} (N : NormalizedNeck D.terminal.metric δ k), δ ≤ ε →
          ⌊ε⁻¹⌋₊ + 1 ≤ k → N.center ∈ hornHalfRange P c e → Q < N.scale →
          ∀ {A Cb : ℝ}, 28 ≤ A →
          (∀ w ∈ frontier (P.core c), ENNReal.ofReal
              (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
            riemannianEDistOf D.terminal.metric N.center w) →
          (∀ z ∈ riemannianBallOf D.terminal.metric N.center
              (5 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)),
            metricScalarAt D.terminal.metric z ≤ Cb * metricScalarAt D.terminal.metric N.center) →
          ∃ (arms : Fin 2 → MinimizingArm D.terminal.metric N.center) (ell : Fin 2 → ℝ),
            (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
            (∀ j, Real.sqrt (metricScalarAt D.terminal.metric N.center) * ell j ∈
              Icc A (2 * A)) ∧
            Real.pi / 2 ≤ comparisonAngle (ell 0) (ell 1)
              (metricDistance D.terminal.metric ((arms 0).point (ell 0))
                ((arms 1).point (ell 1))) := by
  obtain ⟨eta, heta, hdeep⟩ := exists_deep_horn_neck_end_separation_tolerance.{u}
  refine ⟨min eta (1 / 12), lt_min heta (by norm_num), ?_⟩
  intro D ε Λ P hε c hc e
  obtain ⟨Q, hQ, hQdeep⟩ := hdeep P (hε.trans (min_le_left _ _)) c hc e 0
  refine ⟨Q, hQ, ?_⟩
  intro δ k N hδ hk hcenter hscale A Cb hA hbase hbd
  obtain ⟨Θ, -, hmap, -, p, R, -, hfl, hfr, -, hclr, -, -, hlo, hhi, -⟩ :=
    hQdeep N hδ hk hcenter hscale
  obtain ⟨hVo, hsub, hleft, -, -⟩ := P.horn_sides_of_complementPair c e p hclr hlo
  have hsmall : ε < 1 / 11 := (hε.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨nk, -, hnk⟩ :=
    N.exists_spatialNeck hδ hsmall ((Nat.ceil_le_floor_add_one ε⁻¹).trans hk)
  have hsQ : 0 < Real.sqrt (metricScalarAt D.terminal.metric N.center) :=
    Real.sqrt_pos.mpr nk.Q_pos
  let c0 : neckCentralOpen δ := ⟨(N.sphereMark, 0), mem_univ _,
    neg_lt_zero.mpr (inv_pos.mpr N.delta_pos), inv_pos.mpr N.delta_pos⟩
  have hx : P.horn c e ((Θ c0).val.1, (Θ c0).val.2) = N.center := by
    change P.horn c e (Θ c0).val = N.center
    rw [hmap c0]
    exact N.marked
  have hs0 : 0 < (Θ c0).val.2 := (Θ c0).property.2
  have hxc : ConnectedComponents.mk N.center = c := by
    have h : N.center ∈ {w : D.slab.terminalRegularOpen | ConnectedComponents.mk w = c} := by
      rw [P.horn_covers_component c hc]
      exact Or.inr (mem_iUnion.mpr ⟨e, hcenter⟩)
    exact h
  have hK4 : IsCompact (riemannianClosedBallOf D.terminal.metric N.center
      (4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center))) :=
    P.isCompact_riemannianClosedBallOf_of_scalar_le c hc hxc (by positivity)
      (div_lt_div_of_pos_right (by linarith) hsQ) hbd
  have hK2 : IsCompact (riemannianClosedBallOf D.terminal.metric N.center
      (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center))) :=
    P.isCompact_riemannianClosedBallOf_of_scalar_le c hc hxc (by positivity)
      (div_lt_div_of_pos_right (by linarith) hsQ) hbd
  have hbase0 : P.horn c e ((Θ c0).val.1, 0) ∈ frontier (P.core c) := by
    rw [P.horn_base_covers_boundary c hc]
    exact mem_iUnion.mpr ⟨e, (Θ c0).val.1, rfl⟩
  obtain ⟨a, b, ha, hb, hda, hdb⟩ := P.exists_horn_side_points_at_distance c e p
    (fun w hw => frontier_subset_closure (hfl.symm ▸ hw))
    (fun w hw => frontier_subset_closure (hfr.symm ▸ hw))
    (Θ c0).val.1 hs0 ⟨N.sphereMark, rfl⟩ (A := 2 * A / Real.sqrt
      (metricScalarAt D.terminal.metric N.center)) (by positivity) (Real.exp_pos (-R))
    (by rw [hx]; exact hK2) (by rw [hx]; exact hbase _ hbase0) hlo hhi
  rw [hx] at hda hdb
  set V := P.positiveHornMap c e '' p.right with hVdef
  have hcover : riemannianBallOf D.terminal.metric N.center
      (4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) \
        nk.map '' (univ ×ˢ ({0} : Set ℝ)) ⊆ (closure V)ᶜ ∪ V := by
    rintro w ⟨-, hwS⟩
    by_cases hcl : w ∈ closure V
    · rcases hsub hcl with h | ⟨_, ⟨q, rfl⟩, rfl⟩
      · exact Or.inr h
      · refine absurd ⟨(q, 0), ⟨mem_univ _, rfl⟩, ?_⟩ hwS
        change nk.map (q, 0) = P.horn c e (Θ _).val
        rw [hmap]
        exact hnk (TopologicalSpace.Opens.inclusion (neckCentralOpen_le_buffer δ)
          ⟨(q, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr N.delta_pos),
            inv_pos.mpr N.delta_pos⟩)
    · exact Or.inl hcl
  have hr : 3 * (A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
      4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center) := by
    rw [mul_div_assoc']
    exact div_lt_div_of_pos_right (by linarith) hsQ
  have hlo2 : ENNReal.ofReal (A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) ≤
      ENNReal.ofReal (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) :=
    ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by linarith) hsQ.le)
  have hhi2 : ENNReal.ofReal (2 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) <
      ENNReal.ofReal (4 * A / Real.sqrt (metricScalarAt D.terminal.metric N.center)) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
      (div_lt_div_of_pos_right (by linarith) hsQ)
  exact nk.exists_minimizingArms_of_locally_separating_centralSphere hA hr hK4
    isClosed_closure.isOpen_compl hVo (disjoint_compl_left_iff_subset.mpr subset_closure) hcover
    (fun hcl => disjoint_left.mp hleft ⟨a, ha, rfl⟩ hcl) ⟨b, hb, rfl⟩
    (hda ▸ hlo2) (hda ▸ hhi2) (hdb ▸ hlo2) (hdb ▸ hhi2)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TerminalCorePresentation
