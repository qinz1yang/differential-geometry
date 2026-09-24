import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Parameter
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem metricDerivNormSupOn_pullback_continuousOn [I.Boundaryless]
    (g : P → SmoothRiemannianMetric I M) (A : Set P)
    (hg : ContMDiffOn (𝓘(ℝ, P).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : P × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (Set.univ : Set M)))
    (Y : P → M ≃ₘ⟮I, I⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M => Y p.1 p.2))
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (r : ℕ) :
    ContinuousOn (fun q => metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetricCross (g q) (Y q)) (g q) R) A := by
  apply metricDerivNormSupOn_continuousOn
    (fun q => Diffeomorph.pullbackMetricCross (g q) (Y q)) g (fun _ => R)
    (U := univ) _ hK (subset_univ K) r
  intro x _
  refine ⟨(extChartAt I x).target, isOpen_extChartAt_target x,
    (extChartAt I x).map_source (mem_extChartAt_source x), Subset.rfl, ?_⟩
  intro i j
  refine ⟨?_, chartGramOnE_joint_contDiffOn g A hg x i j, ?_⟩
  · exact chartGramOnE_pullback_joint_contDiffOn g A hg Y (by simpa using hY) x i j
  · exact (chartGramOnE_contDiffOn R x i j).comp contDiffOn_snd (fun q hq => hq.2)

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

theorem metricDerivNormSupOn_pullback_tendstoUniformlyOn [I.Boundaryless]
    (g : Q → SmoothRiemannianMetric I M) {J : Set Q} (hJ : IsCompact J)
    (hg : ContMDiffOn (𝓘(ℝ, Q).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : Q × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    (Y : P → M ≃ₘ⟮I, I⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I) I ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I M ∞)
    (R : SmoothRiemannianMetric I M) {K : Set M} (hK : IsCompact K) (r : ℕ) :
    TendstoUniformlyOn (fun p t => metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetricCross (g t) (Y p)) (g t) R)
      (fun _ => 0) (𝓝 p₀) J := by
  have htime : ContMDiff (𝓘(ℝ, P × Q).prod I) (𝓘(ℝ, Q).prod I) ∞
      (fun p : (P × Q) × M => (p.1.2, p.2)) :=
    ((contDiff_snd.contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
  have hparam : ContMDiff (𝓘(ℝ, P × Q).prod I) (𝓘(ℝ, P).prod I) ∞
      (fun p : (P × Q) × M => (p.1.1, p.2)) :=
    ((contDiff_fst.contMDiff).comp contMDiff_fst).prodMk contMDiff_snd
  have hg' : ContMDiffOn (𝓘(ℝ, P × Q).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : (P × Q) × M => (⟨p.2, (g p.1.2).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      ((univ ×ˢ J) ×ˢ (univ : Set M)) :=
    hg.comp htime.contMDiffOn (fun p hp => ⟨hp.1.2, mem_univ _⟩)
  have hc := metricDerivNormSupOn_pullback_continuousOn
    (fun q : P × Q => g q.2) (univ ×ˢ J) hg'
    (fun q : P × Q => Y q.1) (hY.comp hparam) R hK r
  have hzero (t : Q) : metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetricCross (g t) (Y p₀)) (g t) R = 0 := by
    rw [hY₀, Diffeomorph.pullbackMetricCross_refl, metricDerivNormSupOn_self]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨W, hW, hsmall⟩ := hJ.mem_uniformity_of_prod
    (f := fun p t => metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetricCross (g t) (Y p)) (g t) R)
    hc (mem_univ p₀) (Metric.dist_mem_uniformity hε)
  rw [nhdsWithin_univ] at hW
  filter_upwards [hW] with p hp
  intro t ht
  have hh : dist (metricDerivNormSupOn K r
      (Diffeomorph.pullbackMetricCross (g t) (Y p)) (g t) R)
      (metricDerivNormSupOn K r (Diffeomorph.pullbackMetricCross (g t) (Y p₀)) (g t) R) < ε :=
    hsmall p hp t ht
  rw [hzero] at hh
  simpa only [dist_comm] using hh

end DifferentialGeometry.CheegerGromovCompactness
