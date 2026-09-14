import DifferentialGeometry.Topology.Manifold.BallChartStraighteningTube
import DifferentialGeometry.Topology.Manifold.OrientedBallChartTransitionDet
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingRelativeTransitionTube

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric Filter Topology
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology (BallChart)

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

theorem orientedBallChartIsotopicAwayFromCompact_of_common_center {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U]
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U)
    (hC : IsCompact C)
    (hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (hcenter : b.chart (0 : ThreeSpace) = b'.chart (0 : ThreeSpace)) :
    orientedBallChartIsotopicAwayFromCompact o b b' C :=
  orientedBallChartIsotopicAwayFromCompact_of_center_eq o b b' C hC hdisj hdisj'
    (b.transition_fderiv_det_pos b' (ballChart_center_mem_target_of_center_eq b.toBallChart
      b'.toBallChart hcenter))
    hcenter

def orientedBallChartCenterNormalizable {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o)
    (C : Set U) : Prop :=
  ∃ b₀ : OrientedBallEmbedding U o, b₀.chart (0 : ThreeSpace) = b'.chart (0 : ThreeSpace) ∧
    Disjoint (b₀.chart '' Metric.closedBall (0 : ThreeSpace) 1) C ∧
    orientedBallChartIsotopicAwayFromCompact o b b₀ C

private def orientedBallChartIsotopyConcat {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) :
    ℝ → Diffeomorph ThreeModel ThreeModel U U ∞ :=
  fun t => (J (Real.smoothTransition t)).trans (J' (Real.smoothTransition t))

private lemma orientedBallChartIsotopyConcat_zero {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : J 0 = Diffeomorph.refl ThreeModel U ∞)
    (hJ' : J' 0 = Diffeomorph.refl ThreeModel U ∞) :
    orientedBallChartIsotopyConcat J J' 0 = Diffeomorph.refl ThreeModel U ∞ := by
  change (J (Real.smoothTransition 0)).trans (J' (Real.smoothTransition 0)) = _
  rw [Real.smoothTransition.zero, hJ, hJ', Diffeomorph.refl_trans]

private lemma contMDiff_orientedBallChartIsotopyConcat {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞ (fun q : ℝ × U => J q.1 q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' q.1 q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => orientedBallChartIsotopyConcat J J' q.1 q.2) := by
  have hσ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Real.smoothTransition q.1) :=
    (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_fst
  have h₁ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J (Real.smoothTransition q.1) q.2) :=
    hJ.comp (hσ.prodMk contMDiff_snd)
  have h₂ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => J' (Real.smoothTransition q.1) (J (Real.smoothTransition q.1) q.2)) :=
    hJ'.comp (hσ.prodMk h₁)
  exact h₂

private lemma contMDiff_orientedBallChartIsotopyConcat_symm {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞)
    (hJ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J q.1).symm q.2))
    (hJ' : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J' q.1).symm q.2)) :
    ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (orientedBallChartIsotopyConcat J J' q.1).symm q.2) := by
  have hσ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × U => Real.smoothTransition q.1) :=
    (Real.smoothTransition.contDiff.contMDiff).comp contMDiff_fst
  have h₁ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J' (Real.smoothTransition q.1)).symm q.2) :=
    hJ'.comp (hσ.prodMk contMDiff_snd)
  have h₂ : ContMDiff (𝓘(ℝ, ℝ).prod ThreeModel) ThreeModel ∞
      (fun q : ℝ × U => (J (Real.smoothTransition q.1)).symm
        ((J' (Real.smoothTransition q.1)).symm q.2)) :=
    hJ.comp (hσ.prodMk h₁)
  exact h₂

private lemma orientedBallChartIsotopyConcat_apply_eq_of_notMem {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) {K K' : Set U}
    (hJ : ∀ t, Set.EqOn (J t) (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t) (id : U → U) K'ᶜ) {t : ℝ} {x : U} (hx : x ∉ K ∪ K') :
    orientedBallChartIsotopyConcat J J' t x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : J (Real.smoothTransition t) x = x := hJ _ hxK
  have h2 : J' (Real.smoothTransition t) x = x := hJ' _ hxK'
  change J' (Real.smoothTransition t) (J (Real.smoothTransition t) x) = x
  rw [h1, h2]

private lemma orientedBallChartIsotopyConcat_symm_apply_eq_of_notMem {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U]
    (J J' : ℝ → Diffeomorph ThreeModel ThreeModel U U ∞) {K K' : Set U}
    (hJ : ∀ t, Set.EqOn (J t).symm (id : U → U) Kᶜ)
    (hJ' : ∀ t, Set.EqOn (J' t).symm (id : U → U) K'ᶜ) {t : ℝ} {x : U}
    (hx : x ∉ K ∪ K') : (orientedBallChartIsotopyConcat J J' t).symm x = x := by
  have hxK : x ∉ K := fun h => hx (Or.inl h)
  have hxK' : x ∉ K' := fun h => hx (Or.inr h)
  have h1 : (J' (Real.smoothTransition t)).symm x = x := hJ' _ hxK'
  have h2 : (J (Real.smoothTransition t)).symm x = x := hJ _ hxK
  change (J (Real.smoothTransition t)).symm ((J' (Real.smoothTransition t)).symm x) = x
  rw [h1, h2]

theorem orientedBallChartIsotopicAwayFromCompact.trans {U : Type u} [TopologicalSpace U]
    [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U]
    {o : ManifoldOrientation ThreeModel U 3} {b b₀ b' : OrientedBallEmbedding U o} {C : Set U}
    (h : orientedBallChartIsotopicAwayFromCompact o b b₀ C)
    (h' : orientedBallChartIsotopicAwayFromCompact o b₀ b' C) :
    orientedBallChartIsotopicAwayFromCompact o b b' C := by
  obtain ⟨J, K, hK, hKC, hJ0, hJc, hJi, hJfix, hJfixi, hJact⟩ := h
  obtain ⟨J', K', hK', hK'C, hJ'0, hJ'c, hJ'i, hK'fix, hK'fixi, hK'act⟩ := h'
  refine ⟨orientedBallChartIsotopyConcat J J', K ∪ K',
    hK.union hK', Set.disjoint_left.mpr fun x hx hxC => by
      rcases hx with hx | hx
      · exact Set.disjoint_left.mp hKC hx hxC
      · exact Set.disjoint_left.mp hK'C hx hxC,
    orientedBallChartIsotopyConcat_zero J J' hJ0 hJ'0,
    contMDiff_orientedBallChartIsotopyConcat J J' hJc hJ'c,
    contMDiff_orientedBallChartIsotopyConcat_symm J J' hJi hJ'i, ?_, ?_, ?_⟩
  · intro t x hx
    exact orientedBallChartIsotopyConcat_apply_eq_of_notMem J J' hJfix hK'fix hx
  · intro t x hx
    exact orientedBallChartIsotopyConcat_symm_apply_eq_of_notMem J J' hJfixi hK'fixi hx
  · intro x hx
    change J' (Real.smoothTransition 1) (J (Real.smoothTransition 1) (b.chart x)) = b'.chart x
    rw [Real.smoothTransition.one, hJact x hx, hK'act x hx]

theorem orientedBallChartIsotopicAwayFromCompact_of_centerNormalizable {U : Type u}
    [TopologicalSpace U] [ChartedSpace ThreeSpace U] [IsManifold ThreeModel ∞ U] [T2Space U]
    (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U)
    (hC : IsCompact C)
    (hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C)
    (h : orientedBallChartCenterNormalizable o b b' C) :
    orientedBallChartIsotopicAwayFromCompact o b b' C := by
  obtain ⟨b₀, hctr, hdisj₀, halign⟩ := h
  exact halign.trans
    (orientedBallChartIsotopicAwayFromCompact_of_common_center o b₀ b' C hC hdisj₀ hdisj' hctr)

theorem orientedBallChartStraighteningAwayFromCompact_of_centerNormalization
    (h : ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
      [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
      (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U),
      IsCompact C →
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
      orientedBallChartCenterNormalizable o b b' C) :
    orientedBallChartStraighteningAwayFromCompact.{u} := by
  intro U _ _ _ _ _ o b b' C hC hdisj hdisj'
  exact orientedBallChartIsotopicAwayFromCompact_of_centerNormalizable o b b' C hC hdisj'
    (h U o b b' C hC hdisj hdisj')

theorem not_orientedBallChartStraighteningAwayFromCompact :
    ¬ orientedBallChartStraighteningAwayFromCompact.{0} := by
  intro h
  let M : DifferentialGeometry.Topology.ClosedOrientedManifold.{0} 3 :=
    DifferentialGeometry.Topology.standardThreeSphereLift.{0}.toClosedOrientedManifold
  let c : DifferentialGeometry.Topology.OrientedBallChart M :=
    DifferentialGeometry.Topology.orientedBallChart
      DifferentialGeometry.Topology.standardThreeSphereLift.{0}
  set s : ThreeSpace := (3 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with hsdef
  have hnorm : ‖s‖ = 3 / 2 := by
    rw [hsdef, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hr : (0 : ℝ) < 1 / 8 := by norm_num
  have hs : ‖s‖ + 2 * (1 / 8 : ℝ) ≤ 2 := by rw [hnorm]; norm_num
  set ρ : ℝ := 6 / 5 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; norm_num
  have hρle : ρ ≤ 2 := by rw [hρdef]; norm_num
  have hρgt1 : 1 < ρ := by rw [hρdef]; norm_num
  have hρlt : ρ + 1 / 8 < ‖s‖ := by rw [hρdef, hnorm]; norm_num
  let b : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart c
  let b' : OrientedBallEmbedding M.Carrier M.orientation :=
    OrientedBallEmbedding.ofOrientedBallChart (c.affine s (1 / 8) hr hs)
  let C : Set M.Carrier := c.chart '' Metric.sphere (0 : ThreeSpace) ρ
  have hb : b.chart = c.chart := rfl
  have hb' : b'.chart = (c.affine s (1 / 8) hr hs).chart := rfl
  have hsrc : ∀ {x : ThreeSpace}, ‖x‖ ≤ 2 → x ∈ c.chart.source := fun hx =>
    c.closedBall_subset_source (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)
  have hcontSph : ContinuousOn (c.chart : ThreeSpace → M.Carrier)
      (Metric.sphere (0 : ThreeSpace) ρ) :=
    c.chart.contMDiffOn_toFun.continuousOn.mono fun x hx => by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
      exact hsrc (by rw [hx]; exact hρle)
  have hcontBall : ContinuousOn (c.chart : ThreeSpace → M.Carrier)
      (Metric.closedBall (0 : ThreeSpace) ρ) :=
    c.chart.contMDiffOn_toFun.continuousOn.mono fun x hx => by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      exact hsrc (le_trans hx hρle)
  have hC : IsCompact C := (isCompact_sphere (0 : ThreeSpace) ρ).image_of_continuousOn hcontSph
  have hCclosed : IsClosed (c.chart '' Metric.closedBall (0 : ThreeSpace) ρ) :=
    ((isCompact_closedBall (0 : ThreeSpace) ρ).image_of_continuousOn hcontBall).isClosed
  have hdisj : Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C := by
    rw [hb, Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzy⟩
    have hx1 : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      exact hx
    have hzρ : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      exact hz
    have hinj : x = z :=
      c.chart.toPartialEquiv.injOn (hsrc (by linarith)) (hsrc (by linarith)) hzy.symm
    rw [← hinj] at hzρ
    linarith
  have hdisj' : Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C := by
    rw [hb', Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ ⟨z, hz, hzy⟩
    rw [DifferentialGeometry.Topology.OrientedBallChart.affine_apply] at hzy
    have hx1 : ‖x‖ ≤ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
      exact hx
    have hzρ : ‖z‖ = ρ := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hz
      exact hz
    have hshift2 : ‖s + (1 / 8 : ℝ) • x‖ ≤ 2 := by
      have hsm : ‖(1 / 8 : ℝ) • x‖ = 1 / 8 * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
      calc ‖s + (1 / 8 : ℝ) • x‖ ≤ ‖s‖ + ‖(1 / 8 : ℝ) • x‖ := norm_add_le _ _
        _ = 3 / 2 + 1 / 8 * ‖x‖ := by rw [hnorm, hsm]
        _ ≤ 2 := by nlinarith
    have hinj : s + (1 / 8 : ℝ) • x = z :=
      c.chart.toPartialEquiv.injOn (hsrc hshift2) (hsrc (by linarith)) hzy.symm
    have hstep : ‖s‖ - 1 / 8 ≤ ‖z‖ := by
      rw [← hinj]
      have h := norm_sub_le (s + (1 / 8 : ℝ) • x) ((1 / 8 : ℝ) • x)
      rw [add_sub_cancel_right] at h
      have hsm : ‖(1 / 8 : ℝ) • x‖ ≤ 1 / 8 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
        linarith
      linarith
    rw [hzρ] at hstep
    linarith
  obtain ⟨J, K, hK, hKC, hJ0, hJc, hJi, hfix, hfixi, hmatch⟩ :=
    h M.Carrier M.orientation b b' C hC hdisj hdisj'
  let γ : ℝ → M.Carrier := fun t => J t (b.chart 0)
  have hγcont : Continuous γ :=
    hJc.continuous.comp (Continuous.prodMk_left (b.chart 0))
  have hγ0 : γ 0 = c.chart 0 := by
    simp only [γ, hJ0, Diffeomorph.coe_refl, id_eq, hb]
  have hγ1 : γ 1 = c.chart s := by
    have h1 := hmatch (0 : ThreeSpace) (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
    rw [hb', DifferentialGeometry.Topology.OrientedBallChart.affine_apply] at h1
    simpa only [smul_zero, add_zero] using h1
  have hb0notC : b.chart 0 ∉ C := fun hmem =>
    Set.disjoint_left.mp hdisj ⟨0, Metric.mem_closedBall_self (by norm_num), rfl⟩ hmem
  have havoid : ∀ t, γ t ∉ C := by
    intro t ht
    have htK : γ t ∉ K := fun hk => Set.disjoint_left.mp hKC hk ht
    have h1 : (J t).symm (J t (b.chart 0)) = b.chart 0 := (J t).symm_apply_apply (b.chart 0)
    have h2 : (J t).symm (J t (b.chart 0)) = γ t := hfixi t htK
    have heq : (b.chart 0 : M.Carrier) = γ t := by rw [← h1, h2]
    rw [← heq] at ht
    exact hb0notC ht
  have hUopen : IsOpen (c.chart '' Metric.ball (0 : ThreeSpace) ρ) :=
    c.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source Metric.isOpen_ball fun x hx => by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hx
      exact hsrc (by linarith)
  have hsame : γ ⁻¹' (c.chart '' Metric.closedBall (0 : ThreeSpace) ρ)
      = γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ) := by
    ext t
    constructor
    · rintro ⟨y, hy, hyw⟩
      have hy2 : ‖y‖ ≤ ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hy
        exact hy
      have hne : ‖y‖ ≠ ρ := fun hρy =>
        havoid t (by
          refine ⟨y, ?_, hyw⟩
          rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
          exact hρy)
      exact ⟨y, by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact lt_of_le_of_ne hy2 hne, hyw⟩
    · rintro ⟨y, hy, hyw⟩
      exact ⟨y, Metric.ball_subset_closedBall hy, hyw⟩
  have hUclosed : IsClosed (γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ)) := by
    rw [← hsame]
    exact hCclosed.preimage hγcont
  have h0mem : (0 : ℝ) ∈ γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ) :=
    ⟨(0 : ThreeSpace), by simpa using hρpos, hγ0.symm⟩
  have hsep : Set.Icc (0 : ℝ) 1 ⊆ (γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ))
      ∪ (γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ))ᶜ := by
    intro t _
    by_cases ht : t ∈ γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ)
    · exact Or.inl ht
    · exact Or.inr ht
  have hUpre : IsOpen (γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ)) :=
    hUopen.preimage hγcont
  rcases IsPreconnected.subset_or_subset (s := Set.Icc (0 : ℝ) 1)
      (u := γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ))
      (v := (γ ⁻¹' (c.chart '' Metric.ball (0 : ThreeSpace) ρ))ᶜ)
      hUpre hUclosed.isOpen_compl disjoint_compl_right hsep isPreconnected_Icc with hsub | hsub
  · obtain ⟨y, hy, hyw⟩ := hsub ⟨by norm_num, le_rfl⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    have hyeq : y = s := c.chart.toPartialEquiv.injOn (hsrc (by linarith))
      (hsrc (by rw [hnorm]; norm_num)) (by rw [hyw, hγ1])
    rw [hyeq, hnorm] at hy
    linarith
  · exact absurd h0mem (hsub ⟨le_rfl, zero_le_one⟩)

theorem ballEmbeddingIsotopy_of_centerNormalization
    (h : ∀ (U : Type u) [TopologicalSpace U] [ChartedSpace ThreeSpace U]
      [IsManifold ThreeModel ∞ U] [T2Space U] [ConnectedSpace U]
      (o : ManifoldOrientation ThreeModel U 3) (b b' : OrientedBallEmbedding U o) (C : Set U),
      IsCompact C →
      Disjoint (b.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
      Disjoint (b'.chart '' Metric.closedBall (0 : ThreeSpace) 1) C →
      orientedBallChartCenterNormalizable o b b' C)
    (horient : isotopyPreservesOrientation.{u}) :
    ballEmbeddingIsotopy.{u} :=
  ballEmbeddingIsotopy_of_orientedBallChartStraighteningAwayFromCompact
    (orientedBallChartStraighteningAwayFromCompact_of_centerNormalization h) horient

theorem BallMarking.relativeTransitionTube_singleton
    {M : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}
    (c : DifferentialGeometry.Topology.OrientedBallChart M) :
    (DifferentialGeometry.Topology.BallMarking.singleton c).RelativeTransitionTube
      (DifferentialGeometry.Topology.BallMarking.singleton c) :=
  DifferentialGeometry.Topology.BallMarking.relativeTransitionTube_refl_of_subsingleton
    (DifferentialGeometry.Topology.BallMarking.singleton c)

theorem relativeCollarUniqueness_conclusion_of_self {S : Type u} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
    (c : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) (S × EuclideanHalfSpace 1)
      (EuclideanHalfSpace 3) ∞)
    (hunif : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < 1 → (p, t) ∈ c.source)
    {U : Set (EuclideanHalfSpace 3)}
    (hε : ∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
      c (p, t) ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
        (p, t) ∈ c.source ∧ (p, t) ∈ c.source ∧ c (p, t) ∈ U ∧ c (p, t) ∈ U) ∧
      ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) (EuclideanHalfSpace 3)
          (EuclideanHalfSpace 3) ∞,
        (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ → Φ (c (p, t)) = c (p, t)) ∧
        Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ := by
  obtain ⟨ε, hεpos, hεU⟩ := hε
  have hsrc : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < min ε 1 → (p, t) ∈ c.source :=
    fun p t ht => hunif p t (lt_of_lt_of_le ht (min_le_right _ _))
  have hU' : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < min ε 1 → c (p, t) ∈ U :=
    fun p t ht => hεU p t (lt_of_lt_of_le ht (min_le_left _ _))
  exact ⟨min ε 1, lt_min hεpos one_pos, fun p t ht => ⟨hsrc p t ht, hsrc p t ht, hU' p t ht,
    hU' p t ht⟩, Diffeomorph.refl (𝓡∂ 3) (EuclideanHalfSpace 3) ∞, fun p t _ => rfl,
    fun z _ => rfl, fun z _ => rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Topology

universe u

namespace OrientedBallChart

variable {M : ClosedOrientedManifold.{u} 3}

def centerAligned (c c' : OrientedBallChart M)
    (hp : ‖c.chart.symm (c'.chart 0)‖ < 2) : OrientedBallChart M :=
  c.affine (c.chart.symm (c'.chart 0)) ((2 - ‖c.chart.symm (c'.chart 0)‖) / 4)
    (by linarith) (by linarith)

theorem centerAligned_chart_zero (c c' : OrientedBallChart M)
    (h : c'.chart (0 : EuclideanSpace ℝ (Fin 3)) ∈ c.chart.target)
    (hp : ‖c.chart.symm (c'.chart 0)‖ < 2) :
    (c.centerAligned c' hp).chart (0 : EuclideanSpace ℝ (Fin 3)) = c'.chart 0 := by
  have hcoe : (c.centerAligned c' hp).chart (0 : EuclideanSpace ℝ (Fin 3))
      = c.chart (c.chart.symm (c'.chart 0)
        + ((2 - ‖c.chart.symm (c'.chart 0)‖) / 4) • (0 : EuclideanSpace ℝ (Fin 3))) := rfl
  rw [hcoe, smul_zero, add_zero]
  exact PartialDiffeomorph.apply_symm_apply c.chart h

theorem centerAligned_center_mem_target (c c' : OrientedBallChart M)
    (h : c'.chart (0 : EuclideanSpace ℝ (Fin 3)) ∈ c.chart.target)
    (hp : ‖c.chart.symm (c'.chart 0)‖ < 2) :
    (c.centerAligned c' hp).chart (0 : EuclideanSpace ℝ (Fin 3)) ∈ c'.chart.target :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChart_center_mem_target_of_center_eq
    _ _ (c.centerAligned_chart_zero c' h hp)

theorem centerAligned_centerTubeWithin (c c' : OrientedBallChart M)
    (h : c'.chart (0 : EuclideanSpace ℝ (Fin 3)) ∈ c.chart.target)
    (hp : ‖c.chart.symm (c'.chart 0)‖ < 2) {C : Set M.Carrier}
    (hdisj : Disjoint (c'.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) C) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartCenterTubeWithin
      (c.centerAligned c' hp).toBallChart c'.toBallChart C :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ballChartCenterTubeWithin_of_center_eq
    _ _ (c.centerAligned_chart_zero c' h hp) hdisj

end OrientedBallChart

end DifferentialGeometry.Topology
