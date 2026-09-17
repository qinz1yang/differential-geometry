import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.Range
import DifferentialGeometry.Geometry.Metric.Comparison.CurveCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Bundle Filter Function MeasureTheory Set
open DifferentialGeometry.CheegerGromovCompactness CanonicalNeighborhood
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff Topology


universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
local instance terminalEnergyTopology : TopologicalSpace F.M := F.topology
local instance terminalEnergyCharted : ChartedSpace H F.M := F.charted
local instance terminalEnergySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalEnergyC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance terminalEnergyT2 : T2Space F.M := F.t2
local instance terminalEnergySigma : SigmaCompactSpace F.M := F.sigmaCompact

private theorem lagrangian_continuousOn_terminal_interval
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) (a b : ℝ) :
    ContinuousOn (lRegularizedLagrangian F.S 0 alpha) (Icc a b) := by
  apply (lRegularizedLagrangian_continuousOn_carrier F.S F.isSolution alpha halpha).comp
    (continuous_const.prodMk continuous_id).continuousOn
  intro r hr
  change (0 : ℝ) - r ^ 2 ∈ ancientTimeInterval.carrier
  simpa only [ancientTimeInterval_carrier, mem_Iic, zero_sub] using neg_nonpos.mpr (sq_nonneg r)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem curveEnergy_terminal_le_two_mul_action_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a b : ℝ} (hab : a ≤ b) :
    curveEnergy (F.S.base.metric 0) alpha a b ≤ 2 * lRegularizedAction F.S 0 alpha a b := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric 0) alpha halpha a b
  have hEint : IntervalIntegrable (fun s => (F.S.base.metric 0).inner (alpha s)
      (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hE
  have hLag : IntervalIntegrable (lRegularizedLagrangian F.S 0 alpha) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact lagrangian_continuousOn_terminal_interval F alpha halpha a b
  have hpoint : ∀ s ∈ Icc a b,
      (F.S.base.metric 0).inner (alpha s) (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) ≤
        2 * lRegularizedLagrangian F.S 0 alpha s := by
    intro s hs
    have hcomp := ancientModel_metric_zero_le F hF (neg_nonpos.mpr (sq_nonneg s))
      (alpha s) (lVelocity (I := I) alpha s)
    have hscalar : 0 ≤ F.S.scalar (-s ^ 2) (alpha s) := by
      obtain ⟨C, hC⟩ := hF.globalScalarBound
      exact (hC (-s^2) (by simpa only [ancientTimeInterval_carrier, mem_Iic] using neg_nonpos.mpr (sq_nonneg s)) (alpha s)).1
    dsimp only [lRegularizedLagrangian]
    rw [zero_sub]
    nlinarith [mul_nonneg (sq_nonneg s) hscalar]
  have hint := intervalIntegral.integral_mono_on hab hEint (hLag.const_mul 2) hpoint
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianEDist_terminal_le_of_action_le
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℝ → F.M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    {a s t b A : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hA : lRegularizedAction F.S 0 alpha a b ≤ A) :
    riemannianEDistOf (F.S.base.metric 0) (alpha s) (alpha t) ≤
      ENNReal.ofReal (Real.sqrt (t-s) * Real.sqrt (2*A)) := by
  have hE := integrableOn_riemannianMetric_inner_lVelocity_self_of_contMDiff_one
    (F.S.base.metric 0) alpha halpha a b
  have henergy := (curveEnergy_terminal_le_two_mul_action_of_ancient F hF alpha halpha
    (has.trans (hst.trans htb))).trans (mul_le_mul_of_nonneg_left hA (by norm_num))
  exact edistOf_le_budget (F.S.base.metric 0) hst halpha.contMDiffOn
    (hE.mono_set (Icc_subset_Icc has htb))
    ((curveEnergy_mono (F.S.base.metric 0) has hst htb hE).trans henergy)

theorem exists_compact_range_of_ancient_action_le
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x : F.M) {a b A : ℝ}
    (hstart : ∀ n, alpha n a = x) (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    ∃ K : Set F.M, IsCompact K ∧ ∀ n, alpha n '' Icc a b ⊆ K := by
  let _ : T2Space (TangentBundle I F.M) := F.t2TangentBundle
  let _ : NeZero (Module.finrank ℝ E) := by
    obtain ⟨t, ht, x, hx⟩ := hF.notFlat
    exact ⟨Tensor0SBundle.finrank_ne_zero_of_normSq0S_ne_zero
      (F.S.base.metric t) x (by norm_num : 0 < 4) _ hx⟩
  have hg : RiemannianMetricComplete (F.S.base.metric 0) :=
    ⟨hF.complete 0 (by simp only [ancientTimeInterval_carrier, mem_Iic, le_refl])⟩
  refine ⟨{y | riemannianEDistOf (F.S.base.metric 0) x y ≤
      ENNReal.ofReal (Real.sqrt (b-a) * Real.sqrt (2*A))},
    hg.closedEBall_isCompact x (Real.sqrt (b-a) * Real.sqrt (2*A)), ?_⟩
  intro n y hy
  obtain ⟨r, hr, rfl⟩ := hy
  have hdist := riemannianEDist_terminal_le_of_action_le F hF (alpha n) (halpha n)
    le_rfl hr.1 hr.2 (hA n)
  rw [hstart n] at hdist
  exact hdist.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hr.2])) (Real.sqrt_nonneg _)))


theorem exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x y : F.M) {a b A : ℝ} (hab : a ≤ b)
    (hstart : ∀ n, alpha n a = x)
    (hend : Tendsto (fun n => alpha n b) atTop (𝓝 y))
    (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    letI : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
    letI : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
    ∃ K : Set F.M, ∃ phi : ℕ → ℕ, ∃ g : C(Icc a b, F.M),
      IsCompact K ∧ StrictMono phi ∧
      (∀ n, alpha (phi n) '' Icc a b ⊆ K) ∧
      TendstoUniformly (fun n (s : Icc a b) => alpha (phi n) s.1) g atTop ∧
      (∀ s, g s ∈ K) ∧
      g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  let : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
  let : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
  obtain ⟨K, hK, hKrange⟩ :=
    exists_compact_range_of_ancient_action_le F hF alpha halpha x hstart hA
  let B : ℝ := 2 * A
  have henergy : ∀ n, curveEnergy (F.S.base.metric 0) (alpha n) a b ≤ B := by
    intro n
    exact (curveEnergy_terminal_le_two_mul_action_of_ancient F hF (alpha n) (halpha n) hab).trans
      (mul_le_mul_of_nonneg_left (hA n) (by norm_num))
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Geometry.Riemannian.exists_strictMono_tendstoUniformly_of_curveEnergy_le
      (I := I) (F.S.base.metric 0) a b B alpha
      (fun n => (halpha n).contMDiffOn) henergy K hK
      (fun n s => hKrange n ⟨s.1, s.2, rfl⟩)
  have hga : g ⟨a, le_rfl, hab⟩ = x := by
    have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Icc a b)
    have hlim' : Tendsto (fun _ : ℕ => x) atTop (𝓝 (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hstart] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  have hgb : g ⟨b, hab, le_rfl⟩ = y :=
    tendsto_nhds_unique (hconv.tendsto_at ⟨b, hab, le_rfl⟩)
      (hend.comp hphi.tendsto_atTop)
  refine ⟨K, phi, g, hK, hphi, (fun n => hKrange (phi n)), hconv, ?_, hga, hgb⟩
  intro s
  exact hK.isClosed.mem_of_tendsto (hconv.tendsto_at s)
    (Filter.Eventually.of_forall (fun n => hKrange (phi n) ⟨s.1, s.2, rfl⟩))

theorem exists_uniform_subseq_of_ancient_action_le
    [I.Boundaryless]
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (alpha : ℕ → ℝ → F.M) (halpha : ∀ n, ContMDiff 𝓘(ℝ, ℝ) I 1 (alpha n))
    (x y : F.M) {a b A : ℝ} (hab : a ≤ b)
    (hstart : ∀ n, alpha n a = x) (hend : ∀ n, alpha n b = y)
    (hA : ∀ n, lRegularizedAction F.S 0 (alpha n) a b ≤ A) :
    letI : TopologicalSpace.MetrizableSpace F.M := Manifold.metrizableSpace I F.M
    letI : PseudoMetricSpace F.M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric F.M
    ∃ K : Set F.M, ∃ phi : ℕ → ℕ, ∃ g : C(Icc a b, F.M),
      IsCompact K ∧ StrictMono phi ∧
      (∀ n, alpha (phi n) '' Icc a b ⊆ K) ∧
      TendstoUniformly (fun n (s : Icc a b) => alpha (phi n) s.1) g atTop ∧
      (∀ s, g s ∈ K) ∧
      g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  apply exists_uniform_subseq_of_ancient_action_le_of_tendsto_endpoint F hF alpha halpha x y hab hstart
    (by simpa only [hend] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))) hA

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
