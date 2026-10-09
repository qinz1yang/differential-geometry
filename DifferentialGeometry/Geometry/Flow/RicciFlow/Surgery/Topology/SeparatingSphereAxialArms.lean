import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckChainAxialArms

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private exists_minimizingArm_of_edist_ne_top from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRegionAxialArms

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private theorem exists_arm_mem_connectedComponentIn_compl_centralSphere
    {g : SmoothRiemannianMetric I3 M} (hg : RiemannianMetricComplete g) {eps : ℝ} {x y : M}
    (nk : SpatialNeck g eps x) {D : ℝ} (hD : 7 < D)
    (hy : D ≤ Real.sqrt (metricScalarAt g x) * metricDistance g x y) :
    ∃ a : MinimizingArm g x, D / Real.sqrt (metricScalarAt g x) ≤ a.length ∧
      y ∈ connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ y ∧
      a.point (D / Real.sqrt (metricScalarAt g x)) ∈
        connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ y := by
  set sQ := Real.sqrt (metricScalarAt g x) with hsQdef
  have hsQ : 0 < sQ := Real.sqrt_pos.mpr nk.Q_pos
  have hfin : riemannianEDistOf g x y ≠ ⊤ := by
    intro h
    have h0 : metricDistance g x y = 0 := by
      unfold metricDistance
      rw [h, ENNReal.toReal_top]
    rw [h0, mul_zero] at hy
    linarith
  have hxy : x ≠ y := by
    rintro rfl
    have h0 : metricDistance g x x = 0 := by
      unfold metricDistance
      rw [DifferentialGeometry.riemannianEDistOf_self, ENNReal.toReal_zero]
    rw [h0, mul_zero] at hy
    linarith
  obtain ⟨a, hlen, hend⟩ := exists_minimizingArm_of_edist_ne_top g hg hxy hfin
  set ell := D / sQ with hell
  have hell0 : 0 ≤ ell := div_nonneg (by linarith) hsQ.le
  have hellLen : ell ≤ a.length := by
    rw [hlen, hell, div_le_iff₀ hsQ, mul_comm]
    exact hy
  have h0 : (0 : ℝ) ∈ Icc 0 a.length := ⟨le_rfl, a.length_pos.le⟩
  have hsub : a.point '' Icc ell a.length ⊆ (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ := by
    rintro _ ⟨s, hs, rfl⟩ hS
    have hb := nk.central_sphere_subset_closedBall hS
    have hs0 : s ∈ Icc (0 : ℝ) a.length := ⟨hell0.trans hs.1, hs.2⟩
    have he := a.edistOf_eq h0 hs0
    rw [a.start] at he
    change riemannianEDistOf g x (a.point s) ≤ ENNReal.ofReal (7 / sQ) at hb
    rw [he, zero_sub, abs_neg, abs_of_nonneg hs0.1] at hb
    have hle := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
    have h7 : 7 / sQ < ell := div_lt_div_of_pos_right hD hsQ
    linarith [hs.1]
  have hpre : IsPreconnected (a.point '' Icc ell a.length) :=
    isPreconnected_Icc.image _ (a.continuousOn_point.mono (Icc_subset_Icc_left hell0))
  have hyT : y ∈ a.point '' Icc ell a.length := ⟨a.length, ⟨hellLen, le_rfl⟩, hend⟩
  have hpT : a.point ell ∈ a.point '' Icc ell a.length := ⟨ell, ⟨le_rfl, hellLen⟩, rfl⟩
  have hT := hpre.subset_connectedComponentIn hyT hsub
  exact ⟨a, hellLen, hT hyT, hT hpT⟩

private def separationTriple {M : Type u} (p x q : M) : ℕ → M
  | 0 => p
  | 1 => x
  | _ => q

private theorem exists_minimizingArms_of_separating_centralSphere_of_le
    {g : SmoothRiemannianMetric I3 M} (hg : RiemannianMetricComplete g) {eps : ℝ} {x : M}
    (nk : SpatialNeck g eps x) {D : ℝ} (hD : 28 ≤ D) {y z : M}
    (hy : D ≤ Real.sqrt (metricScalarAt g x) * metricDistance g x y)
    (hz : D ≤ Real.sqrt (metricScalarAt g x) * metricDistance g x z)
    (hsep : z ∉ connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ y) :
    ∃ (arms : Fin 2 → MinimizingArm g x) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g x) * ell j ∈ Icc D (2 * D)) ∧
      Real.pi / 2 ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  set S := nk.map '' (univ ×ˢ ({0} : Set ℝ)) with hSdef
  set sQ := Real.sqrt (metricScalarAt g x) with hsQdef
  have hsQ : 0 < sQ := Real.sqrt_pos.mpr nk.Q_pos
  obtain ⟨a, ha, hya, hpa⟩ :=
    exists_arm_mem_connectedComponentIn_compl_centralSphere hg nk (by linarith) hy
  obtain ⟨b, hb, hzb, hqb⟩ :=
    exists_arm_mem_connectedComponentIn_compl_centralSphere hg nk (by linarith) hz
  set ell := D / sQ with hell
  have hellpos : 0 < ell := div_pos (by linarith) hsQ
  set p := a.point ell with hp
  set q := b.point ell with hq
  have hnot : q ∉ connectedComponentIn Sᶜ p := by
    intro hqp
    rw [← connectedComponentIn_eq hpa] at hqp
    apply hsep
    rw [connectedComponentIn_eq hqp, ← connectedComponentIn_eq hqb]
    exact hzb
  have ha0 : (0 : ℝ) ∈ Icc 0 a.length := ⟨le_rfl, a.length_pos.le⟩
  have hb0 : (0 : ℝ) ∈ Icc 0 b.length := ⟨le_rfl, b.length_pos.le⟩
  have hal : ell ∈ Icc 0 a.length := ⟨hellpos.le, ha⟩
  have hbl : ell ∈ Icc 0 b.length := ⟨hellpos.le, hb⟩
  have hpx : riemannianEDistOf g p x ≠ ⊤ := by
    have he := a.edistOf_eq hal ha0
    rw [a.start] at he
    rw [he]
    exact ENNReal.ofReal_ne_top
  have hxq : riemannianEDistOf g x q ≠ ⊤ := by
    have he := b.edistOf_eq hb0 hbl
    rw [b.start] at he
    rw [he]
    exact ENNReal.ofReal_ne_top
  have dpx : metricDistance g p x = ell := by
    have hd := a.minimizing ell hal 0 ha0
    rw [a.start, sub_zero, abs_of_pos hellpos] at hd
    exact hd
  have dxq : metricDistance g x q = ell := by
    have hd := b.minimizing 0 hb0 ell hbl
    rw [b.start, zero_sub, abs_neg, abs_of_pos hellpos] at hd
    exact hd
  let c : ℕ → M := separationTriple p x q
  let slice : ℕ → Set M := fun k => if k = 1 then S else {q}
  let e : ℕ → ℝ := fun k => if k = 1 then 7 / sQ else 0
  have he : ∀ k, 0 ≤ e k := by
    intro k
    simp only [e]
    split_ifs <;> positivity
  have hmem : ∀ k, 0 < k → k ≤ 2 → c k ∈ slice k := by
    intro k hk1 hk2
    interval_cases k
    · exact ⟨(nk.center, 0), ⟨mem_univ _, mem_singleton 0⟩, nk.center_eq⟩
    · exact mem_singleton q
  have hnear : ∀ k, 0 < k → k ≤ 2 → ∀ w ∈ slice k,
      riemannianEDistOf g (c k) w ≤ ENNReal.ofReal (e k) := by
    intro k hk1 hk2 w hw
    interval_cases k
    · exact nk.central_sphere_subset_closedBall hw
    · have hwq : w = q := hw
      rw [hwq]
      change riemannianEDistOf g q q ≤ _
      rw [DifferentialGeometry.riemannianEDistOf_self]
      exact zero_le
  have hstep : ∀ k, 0 ≤ k → k < 2 → riemannianEDistOf g (c k) (c (k + 1)) ≠ ⊤ := by
    intro k _ hk2
    interval_cases k
    · exact hpx
    · exact hxq
  have hsepc : ∀ k, 0 < k → k < 2 →
      Disjoint (slice (k + 1)) (connectedComponentIn (slice k)ᶜ (c 0)) := by
    intro k hk1 hk2
    interval_cases k
    exact Set.disjoint_singleton_left.mpr hnot
  have hineq := metricDistance_ge_of_separating_slices hg c slice e (i := 0) (m := 2)
    (by norm_num) he hmem hnear hstep hsepc
  have hsum1 : ∑ j ∈ Finset.Ico 0 2, metricDistance g (c j) (c (j + 1)) =
      metricDistance g p x + metricDistance g x q := by
    simp [Finset.sum_range_succ, c, separationTriple]
  have hsum2 : ∑ j ∈ Finset.Ico 1 2, e j = 7 / sQ := by
    simp [e]
  have hc2 : c 2 = q := rfl
  have hc0 : c 0 = p := rfl
  rw [hsum1, hsum2, hc0, hc2, dpx, dxq] at hineq
  have h14 : 2 * (7 / sQ) ≤ ell / 2 := by
    rw [hell, div_div, mul_div_assoc', div_le_div_iff₀ hsQ (by positivity)]
    nlinarith
  have hw : 3 / 2 * ell ≤ metricDistance g p q := by linarith
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

theorem SpatialNeck.exists_minimizingArms_of_separating_centralSphere
    {g : SmoothRiemannianMetric I3 M} (hg : RiemannianMetricComplete g) {eps : ℝ} {x : M}
    (nk : SpatialNeck g eps x) (heps : eps ≤ 1 / 252) {D : ℝ} (hD : 0 < D) {y z : M}
    (hy : D ≤ Real.sqrt (metricScalarAt g x) * metricDistance g x y)
    (hz : D ≤ Real.sqrt (metricScalarAt g x) * metricDistance g x z)
    (hsep : z ∉ connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ y) :
    ∃ (arms : Fin 2 → MinimizingArm g x) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g x) * ell j ∈ Icc D (2 * D)) ∧
      Real.pi / 2 ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  have heps0 := nk.eps_pos
  rcases lt_or_ge (9 * D) eps⁻¹ with hsmall | hlarge
  · obtain ⟨arms, ell, hell, hlen, hang⟩ := nk.exists_axial_minimizingArms hg hD hsmall
    refine ⟨arms, ell, hell, hlen, le_trans ?_ hang⟩
    refine le_of_not_gt fun hlt => ?_
    have hpos := Real.arccos_lt_pi_div_two.mp hlt
    have hnp : (3 * eps - 1) / (1 + eps) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have hinv : (252 : ℝ) ≤ eps⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) heps0, ← one_div]
      exact heps
    exact exists_minimizingArms_of_separating_centralSphere_of_le hg nk (by linarith) hy hz hsep

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_strongNeck_threshold_of_separating_centralSphere
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
        ∀ y z : P.Carrier,
          D ≤ Real.sqrt (G.flow.scalar t x) * metricDistance (G.flow.base.metric t) x y →
          D ≤ Real.sqrt (G.flow.scalar t x) * metricDistance (G.flow.base.metric t) x z →
          z ∉ connectedComponentIn (nk.map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ y →
          Nonempty (StrongNeck G.flow delta x t) := by
  obtain ⟨D, Q₀, theta, hD, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_minimizing_arms.{u} hdelta hdelta1 Real.pi_div_two_pos
      hkappa hrho hPhi
  refine ⟨D, Q₀, theta, hD, hQ₀, htheta, ?_⟩
  intro P a s G x t hts hQ hwin hpinch hnc eps nk heps y z hy hz hsep
  obtain ⟨arms, ell, hell, hlen, hang⟩ :=
    nk.exists_minimizingArms_of_separating_centralSphere
      (RiemannianMetricComplete.of_compact _) heps hD hy hz hsep
  exact hthr P a s G x t hts hQ hwin hpinch hnc arms ell hell hlen hang

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
