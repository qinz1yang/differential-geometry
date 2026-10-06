import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyLog_CX3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyJets_CX3

set_option autoImplicit false

/-! # CH12-CX3: chartwise smooth cutoff logarithms -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def logPair_CX3 (c : M) (z : E × E) : M × M :=
  ((extChartAt I c).symm z.1, (extChartAt I c).symm (z.1 + z.2))

def logChartDom_CX3 (c : M) (N : Set (M × M)) : Set (E × E) :=
  {z | z.1 ∈ (extChartAt I c).target ∧ z.1 + z.2 ∈ (extChartAt I c).target} ∩
    logPair_CX3 (I := I) c ⁻¹' N

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem logPair_smooth_CX3 (c : M) :
    ContMDiffOn 𝓘(ℝ, E × E) (I.prod I) ∞ (logPair_CX3 (I := I) c)
      {z | z.1 ∈ (extChartAt I c).target ∧ z.1 + z.2 ∈ (extChartAt I c).target} := by
  have hfst : ContMDiffOn 𝓘(ℝ, E × E) I ∞ (fun z : E × E => (extChartAt I c).symm z.1)
      {z | z.1 ∈ (extChartAt I c).target ∧ z.1 + z.2 ∈ (extChartAt I c).target} :=
    (contMDiffOn_extChartAt_symm c).comp
      (contMDiffOn_iff_contDiffOn.mpr contDiff_fst.contDiffOn) (fun _ hz => hz.1)
  have hadd : ContMDiff 𝓘(ℝ, E × E) 𝓘(ℝ, E) ∞ (fun z : E × E => z.1 + z.2) :=
    contMDiff_iff_contDiff.mpr (contDiff_fst.add contDiff_snd)
  exact hfst.prodMk ((contMDiffOn_extChartAt_symm c).comp hadd.contMDiffOn (fun _ hz => hz.2))

omit [FiniteDimensional ℝ E] in
theorem logChartDom_open_CX3 (c : M) {N : Set (M × M)} (hN : IsOpen N) :
    IsOpen (logChartDom_CX3 (I := I) c N) := by
  apply (logPair_smooth_CX3 c).continuousOn.isOpen_inter_preimage
  · exact ((isOpen_extChartAt_target c).preimage continuous_fst).inter
      ((isOpen_extChartAt_target c).preimage (continuous_fst.add continuous_snd))
  · exact hN

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
theorem logChartDom_zero_CX3 (c : M) {N : Set (M × M)} (hN : ∀ p : M, (p, p) ∈ N)
    {x : E} (hx : x ∈ (extChartAt I c).target) :
    (x, (0 : E)) ∈ logChartDom_CX3 (I := I) c N := by
  exact ⟨⟨hx, by simpa using hx⟩, by simpa [logPair_CX3] using hN ((extChartAt I c).symm x)⟩

variable [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)

def cutoffLogBundle_CX3 (c : M) (χ : M → ℝ) (z : E × E) : TangentBundle I M :=
  ⟨(extChartAt I c).symm z.1,
    χ ((extChartAt I c).symm z.1) • (transferLog_CX3 g hEnorm (logPair_CX3 (I := I) c z)).snd⟩

def cutoffLogCoord_CX3 (c : M) (χ : M → ℝ) (z : E × E) : E :=
  ((trivializationAt E (TangentSpace I) c) (cutoffLogBundle_CX3 g hEnorm c χ z)).2

theorem cutoffLogBundle_smooth_CX3 (c : M) {N : Set (M × M)} (hN : IsOpen N)
    (hlog : ContMDiffOn (I.prod I) I.tangent ∞ (transferLog_CX3 g hEnorm) N)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) :
    ContMDiffOn 𝓘(ℝ, E × E) I.tangent ∞ (cutoffLogBundle_CX3 g hEnorm c χ)
      (logChartDom_CX3 (I := I) c N) := by
  have hpair : ContMDiffOn 𝓘(ℝ, E × E) (I.prod I) ∞ (logPair_CX3 (I := I) c)
      (logChartDom_CX3 (I := I) c N) :=
    (logPair_smooth_CX3 c).mono inter_subset_left
  have hL : ContMDiffOn 𝓘(ℝ, E × E) I.tangent ∞
      (fun z => transferLog_CX3 g hEnorm (logPair_CX3 (I := I) c z))
      (logChartDom_CX3 (I := I) c N) := hlog.comp hpair (fun _ hz => hz.2)
  have hscalar : ContMDiffOn 𝓘(ℝ, E × E) 𝓘(ℝ, ℝ) ∞
      (fun z : E × E => χ ((extChartAt I c).symm z.1)) (logChartDom_CX3 (I := I) c N) :=
    hχ.comp_contMDiffOn ((contMDiffOn_extChartAt_symm c).comp
      (contMDiffOn_iff_contDiffOn.mpr contDiff_fst.contDiffOn) (fun _ hz => hz.1.1))
  intro z hz
  exact (contMDiffAt_smul_tangent_S15
    (fun z => transferLog_CX3 g hEnorm (logPair_CX3 (I := I) c z))
    (fun z : E × E => χ ((extChartAt I c).symm z.1))
    (hL.contMDiffAt ((logChartDom_open_CX3 c hN).mem_nhds hz))
    (hscalar.contMDiffAt ((logChartDom_open_CX3 c hN).mem_nhds hz))).contMDiffWithinAt

theorem cutoffLogCoord_smooth_CX3 (c : M) {N : Set (M × M)} (hN : IsOpen N)
    (hlog : ContMDiffOn (I.prod I) I.tangent ∞ (transferLog_CX3 g hEnorm) N)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) :
    ContDiffOn ℝ ∞ (cutoffLogCoord_CX3 g hEnorm c χ) (logChartDom_CX3 (I := I) c N) := by
  have hb := cutoffLogBundle_smooth_CX3 g hEnorm c hN hlog χ hχ
  have he : ContMDiffOn I.tangent (I.prod 𝓘(ℝ, E)) ∞ (trivializationAt E (TangentSpace I) c)
      (trivializationAt E (TangentSpace I) c).source :=
    (trivializationAt E (TangentSpace I) c).contMDiffOn
  have hm : MapsTo (cutoffLogBundle_CX3 g hEnorm c χ) (logChartDom_CX3 (I := I) c N)
      (trivializationAt E (TangentSpace I) c).source := by
    intro z hz
    apply (trivializationAt E (TangentSpace I) c).mem_source.mpr
    rw [baseSet_eq_source_S15]
    exact (extChartAt I c).map_target hz.1.1
  exact contMDiffOn_iff_contDiffOn.mp (contMDiff_snd.comp_contMDiffOn (he.comp hb hm))

theorem cutoffLogBundle_zero_CX3 (c : M) (χ : M → ℝ) (x : E) :
    cutoffLogBundle_CX3 g hEnorm c χ (x, 0) =
      (⟨(extChartAt I c).symm x,
        (0 : TangentSpace I ((extChartAt I c).symm x))⟩ : TangentBundle I M) := by
  unfold cutoffLogBundle_CX3
  have heq : logPair_CX3 (I := I) c (x, 0) =
      ((extChartAt I c).symm x, (extChartAt I c).symm x) := by simp [logPair_CX3]
  rw [heq, transferLog_zero_CX3]
  simp only [smul_zero]

theorem cutoffLogCoord_zero_CX3 (c : M) (χ : M → ℝ) {x : E}
    (hx : x ∈ (extChartAt I c).target) : cutoffLogCoord_CX3 g hEnorm c χ (x, 0) = 0 := by
  have hp : (extChartAt I c).symm x ∈ (trivializationAt E (TangentSpace I) c).baseSet := by
    rw [baseSet_eq_source_S15]; exact (extChartAt I c).map_target hx
  unfold cutoffLogCoord_CX3
  rw [cutoffLogBundle_zero_CX3]
  change ((trivializationAt E (TangentSpace I) c)
    (zeroSection E (TangentSpace I) ((extChartAt I c).symm x))).2 = 0
  rw [(trivializationAt E (TangentSpace I) c).zeroSection (R := ℝ) hp]

/-- Uniform control of the metric length follows from continuity of the bundle
map, separately from its coordinate derivatives. -/
theorem exists_cutoffLog_length_bound_CX3 (c : M) {N : Set (M × M)} (hN : IsOpen N)
    (hdiag : ∀ p : M, (p, p) ∈ N)
    (hlog : ContMDiffOn (I.prod I) I.tangent ∞ (transferLog_CX3 g hEnorm) N)
    (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    {K : Set E} (hK : IsCompact K) (hKT : K ⊆ (extChartAt I c).target)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ K, ∀ w : E, ‖w‖ ≤ δ →
      (x, w) ∈ logChartDom_CX3 (I := I) c N ∧
        tanLen_S15 g (cutoffLogBundle_CX3 g hEnorm c χ (x, w)) < ε := by
  let U := logChartDom_CX3 (I := I) c N
  have hcont : ContinuousOn (fun z => tanLen_S15 g (cutoffLogBundle_CX3 g hEnorm c χ z)) U :=
    (continuous_tanLen_S15 g).comp_continuousOn
      (cutoffLogBundle_smooth_CX3 g hEnorm c hN hlog χ hχ).continuousOn
  have hopen : IsOpen (U ∩ {z | tanLen_S15 g (cutoffLogBundle_CX3 g hEnorm c χ z) < ε}) :=
    hcont.isOpen_inter_preimage (logChartDom_open_CX3 c hN) isOpen_Iio
  obtain ⟨δ, hδ, hsub⟩ := exists_graph_tube_CX3 hK hopen (fun x hx =>
    ⟨logChartDom_zero_CX3 c hdiag (hKT hx), by
      change tanLen_S15 g (cutoffLogBundle_CX3 g hEnorm c χ (x, 0)) < ε
      rw [cutoffLogBundle_zero_CX3]
      change Real.sqrt (g.inner ((extChartAt I c).symm x)
        (0 : TangentSpace I ((extChartAt I c).symm x))
        (0 : TangentSpace I ((extChartAt I c).symm x))) < ε
      rw [map_zero, Real.sqrt_zero]
      exact hε⟩)
  exact ⟨δ, hδ, fun x hx w hw => hsub ⟨hx, by simpa only [mem_closedBall, dist_zero_right] using hw⟩⟩

end GC.LongTime.Ch12
