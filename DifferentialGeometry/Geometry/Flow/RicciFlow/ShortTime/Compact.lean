import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.NoncompactRicciFlat
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.UniformBounds
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow
open Bundle Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

private theorem exists_compact_ricci_flow_at_zero
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ (d : ℝ) (hd : 0 < d),
      ∃ Q : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen 0 d hd),
        Q.solution.base.metric 0 = g₀ ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 d, ∀ x : M,
          normSq0S (Q.solution.base.metric t) x 4
            (metricRm04At (Q.solution.base.metric t) x) ≤ C) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun p : ℝ × M => (⟨p.2, (Q.solution.base.metric p.1).inner p.2⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
          (Ico 0 d ×ˢ (Set.univ : Set M)) ∧
        (∀ t ∈ Ico 0 d, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun r => (Q.solution.base.metric r).inner x v w)
            (-2 * ricciTensor (Q.solution.base.metric t) x v w) (Ici 0) t) := by
  obtain ⟨T, hT, g, hinit, hjoint, hpde⟩ := ricci_flow_short_time_existence g₀
  obtain ⟨d, hd, hdT⟩ := exists_between hT
  have hgram (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :=
    (hjoint x₀ i j).mono (show Icc 0 d ×ˢ
      (trivializationAt E (TangentSpace I) x₀).baseSet ⊆
        Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet from
      fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt hdT⟩, hp.2⟩)
  obtain ⟨C, hC, hbound⟩ := rm04SlabSup g g g hgram hgram hgram
  have hbound' : ∀ t ∈ Ico 0 d, ∀ x : M,
      normSq0S (g t) x 4 (metricRm04At (g t) x) ≤ C := by
    intro t ht x
    exact hbound t ⟨ht.1, ht.2.le⟩ x
  let Q := completeBoundedCurvatureSolutionOfJointRicciFlow hd g
    (fun x₀ i j => (hjoint x₀ i j).mono (fun _ hp =>
      ⟨⟨hp.1.1, hp.1.2.trans hdT⟩, hp.2⟩))
    (fun t ht => hpde t ⟨ht.1, ht.2.trans hdT⟩)
    (fun t _ => RiemannianMetricComplete.of_compact (g t))
    (fun t ht => ⟨C, hC, hbound' t ht⟩)
  refine ⟨d, hd, Q, hinit, ⟨C, hC, hbound'⟩, ?_, ?_⟩
  · apply metricCLMSection_jointContMDiffOn_of_chartGram_on g (Ico 0 d)
    exact fun x₀ i j => (hjoint x₀ i j).mono (fun _ hp =>
      ⟨⟨hp.1.1, hp.1.2.trans hdT⟩, hp.2⟩)
  · exact fun t ht => hpde t ⟨ht.1, ht.2.trans hdT⟩

private theorem exists_compact_ricci_flow_from_time
    (g₀ : SmoothRiemannianMetric I M) (s : ℝ) :
    ∃ (d : ℝ) (hsd : s < d),
      ∃ Q : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen s d hsd),
        Q.solution.base.metric s = g₀ ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico s d, ∀ x : M,
          normSq0S (Q.solution.base.metric t) x 4
            (metricRm04At (Q.solution.base.metric t) x) ≤ C) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun p : ℝ × M => (⟨p.2, (Q.solution.base.metric p.1).inner p.2⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
          (Ico s d ×ˢ (Set.univ : Set M)) ∧
        (∀ t ∈ Ico s d, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun r => (Q.solution.base.metric r).inner x v w)
            (-2 * ricciTensor (Q.solution.base.metric t) x v w) (Ici s) t) := by
  obtain ⟨d, hd, P, hinit, ⟨C, hC, hbound⟩, hjoint, hpde⟩ :=
    exists_compact_ricci_flow_at_zero g₀
  have hsd : s < s + d := by linarith
  let D := RealTimeInterval.closedOpen s (s + d) hsd
  let S : SolutionOn (I := I) (M := M) D := (P.solution.timeShift (-s)).timeRestrict D
  have hcar : D.carrier ⊆ ((RealTimeInterval.closedOpen 0 d hd).timeShift (-s)).carrier := by
    intro t ht
    change 0 ≤ t + -s ∧ t + -s < d
    change s ≤ t ∧ t < s + d at ht
    constructor <;> linarith [ht.1, ht.2]
  have hreg : D.regular ⊆ ((RealTimeInterval.closedOpen 0 d hd).timeShift (-s)).regular := by
    intro t ht
    change 0 < t + -s ∧ t + -s < d
    change s < t ∧ t < s + d at ht
    constructor <;> linarith [ht.1, ht.2]
  have htranslate (t : ℝ) (ht : t ∈ Ico s (s + d)) : t + -s ∈ Ico 0 d := by
    constructor <;> linarith [ht.1, ht.2]
  let Q : CompleteBoundedCurvatureSolutionOn (I := I) (M := M) (D := D) := {
    solution := S
    isSolution := isSoln_timeRestrict (isSolutionOn_timeShift P.isSolution (-s)) hcar hreg
    complete := fun t ht => P.complete (t + -s) (htranslate t ht)
    curvatureBound := fun t ht => ⟨C, hC, hbound (t + -s) (htranslate t ht)⟩ }
  refine ⟨s + d, hsd, Q, ?_, ⟨C, hC, ?_⟩, ?_, ?_⟩
  · change P.solution.base.metric (s + -s) = g₀
    simpa only [add_neg_cancel] using hinit
  · intro t ht x
    exact hbound (t + -s) (htranslate t ht) x
  · have hmap : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun p : ℝ × M => (p.1 + -s, p.2)) :=
      (contMDiff_fst.add contMDiff_const).prodMk contMDiff_snd
    exact hjoint.comp hmap.contMDiffOn (fun p hp => ⟨htranslate p.1 hp.1, hp.2⟩)
  · intro t ht x v w
    have h := (hpde (t + -s) (htranslate t ht) x v w).comp t
      ((hasDerivAt_id t).add_const (-s)).hasDerivWithinAt
      (show Set.MapsTo (fun r : ℝ => r + -s) (Ici s) (Ici 0) from
        fun r hr => by change 0 ≤ r + -s; change s ≤ r at hr; linarith)
    change HasDerivWithinAt
      (fun r => (P.solution.base.metric (r + -s)).inner x v w)
      (-2 * ricciTensor (P.solution.base.metric (t + -s)) x v w) (Ici s) t
    dsimp only [Function.comp_def, id_eq] at h
    rw [mul_one] at h
    exact h


end InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]

theorem exists_completeBoundedCurvatureSolutionOn_from_time_of_compact
    (g₀ : SmoothRiemannianMetric I M) (s : ℝ) :
    ∃ (d : ℝ) (hsd : s < d),
      ∃ Q : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen s d hsd),
        Q.solution.base.metric s = g₀ ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico s d, ∀ x : M,
          normSq0S (Q.solution.base.metric t) x 4
            (metricRm04At (Q.solution.base.metric t) x) ≤ C) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun p : ℝ × M => (⟨p.2, (Q.solution.base.metric p.1).inner p.2⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
          (Ico s d ×ˢ (Set.univ : Set M)) ∧
        (∀ t ∈ Ico s d, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun r => (Q.solution.base.metric r).inner x v w)
            (-2 * ricciTensor (Q.solution.base.metric t) x v w) (Ici s) t) := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let k : SmoothRiemannianMetric J M := g₀.transContinuousLinearEquiv e
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  obtain ⟨d, hsd, P, hinit, ⟨C, hC, hbound⟩, hjoint, hpde⟩ := exists_compact_ricci_flow_from_time k s
  let Q := P.pullback Φ
  refine ⟨d, hsd, Q, ?_, ⟨C, hC, ?_⟩, ?_, ?_⟩
  · change Diffeomorph.pullbackMetricCross (P.solution.base.metric s) Φ = g₀
    rw [hinit]
    exact SmoothRiemannianMetric.pullback_transContinuousLinearEquiv g₀ e
  · intro t ht x
    change normSq0S (Diffeomorph.pullbackMetricCross (P.solution.base.metric t) Φ) x 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (P.solution.base.metric t) Φ) x) ≤ C
    rw [DifferentialGeometry.HCGCompactness.riemannNormSq_cross]
    exact hbound t ht (Φ x)
  · apply metricCLMSection_jointContMDiffOn_of_chartGram_on
      Q.solution.base.metric (Ico s d)
    exact chartGramMatrix_joint_contMDiffOn_of_pullback P.solution.base.metric (Ico s d)
      hjoint Q.solution.base.metric Φ Φ.contMDiff
      (fun t _ x v w => Diffeomorph.pullbackMetricCross_inner (P.solution.base.metric t) Φ x v w)
  · intro t ht x v w
    change HasDerivWithinAt
      (fun r => (Diffeomorph.pullbackMetricCross (P.solution.base.metric r) Φ).inner x v w)
      (-2 * ricciTensor (Diffeomorph.pullbackMetricCross (P.solution.base.metric t) Φ) x v w)
      (Ici s) t
    simpa only [Diffeomorph.pullbackMetricCross_inner,
      DifferentialGeometry.HCGCompactness.ricciTensor_cross] using
      hpde t ht (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w)


theorem exists_completeBoundedCurvatureSolutionOn_of_compact
    (g₀ : SmoothRiemannianMetric I M) :
    ∃ (d : ℝ) (hd : 0 < d),
      ∃ Q : CompleteBoundedCurvatureSolutionOn (I := I) (M := M)
        (D := RealTimeInterval.closedOpen 0 d hd),
        Q.solution.base.metric 0 = g₀ ∧
        (∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 d, ∀ x : M,
          normSq0S (Q.solution.base.metric t) x 4
            (metricRm04At (Q.solution.base.metric t) x) ≤ C) ∧
        ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
          (fun p : ℝ × M => (⟨p.2, (Q.solution.base.metric p.1).inner p.2⟩ :
            TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
              (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
          (Ico 0 d ×ˢ (Set.univ : Set M)) ∧
        (∀ t ∈ Ico 0 d, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun r => (Q.solution.base.metric r).inner x v w)
            (-2 * ricciTensor (Q.solution.base.metric t) x v w) (Ici 0) t) :=
  exists_completeBoundedCurvatureSolutionOn_from_time_of_compact g₀ 0

end DifferentialGeometry.PDE.RicciFlow
