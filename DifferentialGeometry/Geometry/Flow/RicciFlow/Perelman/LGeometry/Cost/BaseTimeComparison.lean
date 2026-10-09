import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Retiming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SquareClock
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CarrierJoinCost
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientVolumeComparison

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold ContDiff

section

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

private theorem contMDiffOn_comp_sqrt_sub_sq
    {d a c : ℝ} (hd : 0 ≤ d) (ha : 0 < a)
    {n : WithTop ℕ∞} {alpha : ℝ → M} (halpha : ContMDiff 𝓘(ℝ, ℝ) I n alpha) :
    ContMDiffOn 𝓘(ℝ, ℝ) I n (fun s => alpha (Real.sqrt (s ^ 2 - d)))
      (Icc (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d))) := by
  have hneq : ∀ s ∈ Icc (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)),
      s ^ 2 - d ≠ 0 := by
    intro s hs
    have hsquare : (Real.sqrt (a ^ 2 + d)) ^ 2 ≤ s ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hs.1 2
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) hd)] at hsquare
    have hradicand : a ^ 2 ≤ s ^ 2 - d := (le_sub_iff_add_le).mpr hsquare
    exact ne_of_gt ((sq_pos_of_pos ha).trans_le hradicand)
  have hclock : ContDiffOn ℝ n (fun s : ℝ => Real.sqrt (s ^ 2 - d))
      (Icc (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d))) :=
    ((contDiffOn_id.pow 2).sub contDiffOn_const).sqrt hneq
  exact halpha.comp_contMDiffOn hclock.contMDiffOn

end

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

private theorem lCost_le_sqrt_mul_lRegularizedAction_add
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Iic 0)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (Iic 0))
    {R : ℝ} (hscalar : ∀ t ≤ 0, ∀ x : M, 0 ≤ S.scalar t x ∧ S.scalar t x ≤ R)
    (hRm : ∃ K : ℝ, ∀ t ≤ 0, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    {d a c : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (hac : a < c)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lCost S 0 (alpha 0) (alpha c) (c ^ 2 + d) ≤
      (Real.sqrt (a ^ 2 + d) / a) * lRegularizedAction S (-d) alpha 0 c +
        2 * R * (Real.sqrt (a ^ 2 + d)) ^ 3 := by
  let s0 : ℝ := Real.sqrt (a ^ 2 + d)
  let s1 : ℝ := Real.sqrt (c ^ 2 + d)
  let k : ℝ := a / s0
  let prefixCurve : ℝ → M := fun s => alpha (k * s)
  let tail : ℝ → M := fun s => alpha (Real.sqrt (s ^ 2 - d))
  have hc : 0 < c := ha.trans hac
  have hs0 : 0 < s0 := Real.sqrt_pos.mpr (by positivity)
  have hs1 : 0 < s1 := Real.sqrt_pos.mpr (by positivity)
  have hs0sq : s0 ^ 2 = a ^ 2 + d := Real.sq_sqrt (by positivity)
  have hs1sq : s1 ^ 2 = c ^ 2 + d := Real.sq_sqrt (by positivity)
  have has0 : a ≤ s0 := by
    apply (sq_le_sq₀ ha.le hs0.le).mp
    rw [hs0sq]
    linarith
  have hs01 : s0 < s1 := by
    apply Real.sqrt_lt_sqrt (by positivity)
    nlinarith
  have hkpos : 0 < k := div_pos ha hs0
  have hk : k ≤ 1 := (div_le_one hs0).mpr has0
  have hks0 : k * s0 = a := div_mul_cancel₀ a hs0.ne'
  have hk2 : k ^ 2 * s0 ^ 2 = a ^ 2 := by
    dsimp only [k]
    field_simp [hs0.ne']
  have hshift : (1 - k ^ 2) * s0 ^ 2 ≤ -(-d) := by
    nlinarith [hs0sq, hk2]
  have hprefix : ContMDiff 𝓘(ℝ, ℝ) I 1 prefixCurve :=
    halpha.comp (contDiff_const.mul contDiff_id).contMDiff
  have htail : ContMDiffOn 𝓘(ℝ, ℝ) I 1 tail (Icc s0 s1) :=
    contMDiffOn_comp_sqrt_sub_sq hd ha halpha
  have hnode : prefixCurve s0 = tail s0 := by
    dsimp only [prefixCurve, tail]
    rw [hks0, show s0 ^ 2 - d = a ^ 2 by rw [hs0sq]; ring, Real.sqrt_sq ha.le]
  have htailEnd : tail s1 = alpha c := by
    dsimp only [tail]
    rw [show s1 ^ 2 - d = c ^ 2 by rw [hs1sq]; ring, Real.sqrt_sq hc.le]
  have hjoin := DifferentialGeometry.PDE.RicciFlow.lCost_le_join_on_carrier_of_bounded_rm
    S hS 0 s1 hs0 hs01 prefixCurve tail hprefix.contMDiffOn htail hnode
    (by intro s _; rw [hcarrier]; exact sub_nonpos.mpr (sq_nonneg s))
    (by
      obtain ⟨K, hK⟩ := hRm
      exact ⟨K, fun t ht x => hK t ht.2 x⟩)
  have hjoin' : lCost S 0 (alpha 0) (alpha c) (c ^ 2 + d) ≤
      lRegularizedAction S 0 prefixCurve 0 s0 + lRegularizedAction S 0 tail s0 s1 := by
    simpa only [prefixCurve, mul_zero, htailEnd, hs1sq] using hjoin
  have hpre := lRegularizedAction_mul_le_add_of_metric_antitone S hS hs0.le hkpos hk
    hshift hcarrier hmetric hscalar alpha halpha
  rw [hks0] at hpre
  have htailBound := lRegularizedAction_sqrt_sub_sq_le S hS hd ha hac.le
    (by intro r _; rw [hcarrier]; change -d - r ^ 2 ≤ 0; linarith [sq_nonneg r])
    (fun r _ x => (hscalar (-d - r ^ 2) (by linarith [sq_nonneg r]) x).1)
    alpha halpha
  have hcont : ContinuousOn (lRegularizedLagrangian S (-d) alpha) (Icc 0 c) := by
    apply (lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha).comp
      (continuous_const.prodMk continuous_id).continuousOn
    intro r _
    change -d - r ^ 2 ∈ D.carrier
    rw [hcarrier]
    change -d - r ^ 2 ≤ 0
    linarith [sq_nonneg r]
  have hInt0a : IntervalIntegrable (lRegularizedLagrangian S (-d) alpha) volume 0 a :=
    (hcont.mono (Icc_subset_Icc le_rfl hac.le)).intervalIntegrable_of_Icc ha.le
  have hIntac : IntervalIntegrable (lRegularizedLagrangian S (-d) alpha) volume a c :=
    (hcont.mono (Icc_subset_Icc ha.le le_rfl)).intervalIntegrable_of_Icc hac.le
  have hsplit := lRegularizedAction_add S (-d) alpha 0 a c hInt0a hIntac
  have hnonneg : 0 ≤ lRegularizedAction S (-d) alpha 0 a := by
    apply intervalIntegral.integral_nonneg ha.le
    intro r _
    unfold lRegularizedLagrangian
    exact add_nonneg
      (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))
      (mul_nonneg (by positivity)
        (hscalar (-d - r ^ 2) (by linarith [sq_nonneg r]) (alpha r)).1)
  have hfactor : 1 ≤ s0 / a := (le_div_iff₀ ha).mpr (by simpa only [one_mul] using has0)
  have hpreScale := mul_le_mul_of_nonneg_right (hk.trans hfactor) hnonneg
  have hsum := add_le_add hpre htailBound
  have hsum' : lRegularizedAction S 0 prefixCurve 0 s0 + lRegularizedAction S 0 tail s0 s1 ≤
      k * lRegularizedAction S (-d) alpha 0 a + 2 * R * s0 ^ 3 +
        (s0 / a) * lRegularizedAction S (-d) alpha a c := hsum
  change lCost S 0 (alpha 0) (alpha c) (c ^ 2 + d) ≤
    (s0 / a) * lRegularizedAction S (-d) alpha 0 c + 2 * R * s0 ^ 3
  refine hjoin'.trans (hsum'.trans ?_)
  rw [← hsplit]
  calc
    k * lRegularizedAction S (-d) alpha 0 a + 2 * R * s0 ^ 3 +
        (s0 / a) * lRegularizedAction S (-d) alpha a c ≤
      (s0 / a) * lRegularizedAction S (-d) alpha 0 a + 2 * R * s0 ^ 3 +
        (s0 / a) * lRegularizedAction S (-d) alpha a c :=
      add_le_add_left (add_le_add_left hpreScale _) _
    _ = _ := by ring

theorem lCost_le_sqrt_mul_lCost_add_of_metric_antitone
    [PreconnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Iic 0)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (Iic 0))
    {R : ℝ} (hscalar : ∀ t ≤ 0, ∀ x : M, 0 ≤ S.scalar t x ∧ S.scalar t x ≤ R)
    (hRm : ∃ K : ℝ, ∀ t ≤ 0, ∀ x : M,
      Tensor0SBundle.normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K)
    {d a tau : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (htau : a ^ 2 + d < tau)
    (p q : M) :
    lCost S 0 p q tau ≤
      (Real.sqrt (a ^ 2 + d) / a) * lCost S (-d) p q (tau - d) +
        2 * R * (Real.sqrt (a ^ 2 + d)) ^ 3 := by
  let c : ℝ := Real.sqrt (tau - d)
  have hsigma : 0 < tau - d := by nlinarith [sq_pos_of_pos ha]
  have hcsq : c ^ 2 = tau - d := Real.sq_sqrt hsigma.le
  have hac : a < c := Real.lt_sqrt_of_sq_lt (by linarith)
  have hfactor : 0 < Real.sqrt (a ^ 2 + d) / a :=
    div_pos (Real.sqrt_pos.mpr (by positivity)) ha
  by_contra! hnot
  have hthreshold : lCost S (-d) p q (tau - d) <
      (lCost S 0 p q tau - 2 * R * (Real.sqrt (a ^ 2 + d)) ^ 3) /
        (Real.sqrt (a ^ 2 + d) / a) := by
    apply (lt_div_iff₀ hfactor).mpr
    nlinarith
  obtain ⟨alpha, halpha, hstart, hend, hsmall⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S (-d) p q
      (tau - d) hsigma _ hthreshold
  have hupper := lCost_le_sqrt_mul_lRegularizedAction_add S hS hcarrier hmetric
    hscalar hRm hd ha hac alpha halpha
  have htime : c ^ 2 + d = tau := by rw [hcsq]; ring
  have hend' : alpha c = q := hend
  rw [hstart, hend', htime] at hupper
  have hstrict := (lt_div_iff₀ hfactor).mp hsmall
  nlinarith [hupper, hstrict]

end DifferentialGeometry.PDE.RicciFlow.Perelman

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set CanonicalNeighborhood
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : T2Space F.M := F.t2
private local instance : SigmaCompactSpace F.M := F.sigmaCompact

theorem exists_ancientKappa_lCost_terminal_le_sqrt_mul_add
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ d a tau : ℝ, 0 ≤ d → 0 < a → a ^ 2 + d < tau →
      ∀ p q : F.M, lCost F.S 0 p q tau ≤
        (Real.sqrt (a ^ 2 + d) / a) * lCost F.S (-d) p q (tau - d) +
          2 * R * (Real.sqrt (a ^ 2 + d)) ^ 3 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : ConnectedSpace F.M := hF.connected
  let _ : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let _ : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨R, hR⟩ := hF.globalScalarBound
  have hRnonneg : 0 ≤ R :=
    (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).1.trans
      (hR 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl]) F.basepoint).2
  have hmetric (x : F.M) (v : TangentSpace I x) :
      AntitoneOn (fun t => (F.S.base.metric t).inner x v v) (Iic 0) := by
    intro s hs t ht hst
    have hRic : ∀ r ∈ Ioo s t, ∀ y : F.M, ∀ w : TangentSpace I y,
        0 ≤ F.S.ricciAt r y (vec2 w w) := by
      intro r hr y w
      apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric r) y).mpr
      intro n c a b
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator r (hr.2.le.trans ht) y n c a b
    exact CanonicalNeighborhood.metric_inner_antitoneOn_of_ricci_nonnegative_interior
      F.S F.isSolution (fun _ hr => hr.2.trans ht) (fun _ hr => hr.2.trans_le ht)
      hRic x v ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  refine ⟨R, hRnonneg, ?_⟩
  intro d a tau hd ha htau p q
  exact lCost_le_sqrt_mul_lCost_add_of_metric_antitone F.S F.isSolution hF.carrier_eq
    hmetric hR ⟨K, hK⟩ hd ha htau p q

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
