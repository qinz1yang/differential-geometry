import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.InitialDistanceSupWeight
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm

set_option autoImplicit false
noncomputable section
open Set Bundle Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

variable [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem closed_slab_curvature_norm_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) (k : ℕ) :
    ContinuousOn (fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2)
      (Icc 0 T ×ˢ univ) := by
  have hh := (covariantRiemannNormSq_contMDiffOn S.base.metric (Icc 0 T)
    (uniqueDiffOn_Icc hT) hgram k).continuousOn
  apply hh.congr
  intro q _
  dsimp only
  unfold nablaKRm04NormSqIntrinsic
  rw [nablaKRm_eq_iterCov]
  rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem closed_slab_bernstein_continuous
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) (a : ℝ) :
    ContinuousOn (fun q : ℝ × M => shiFirstBernsteinTimeQuantity S a q.1 q.2)
      (spacetimeSlab (M := M) T) := by
  exact continuous_fst.continuousOn.mul
    ((continuousOn_const.add (closed_slab_curvature_norm_continuous S hT hgram 0)).mul
      (closed_slab_curvature_norm_continuous S hT hgram 1))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem closed_slab_weight_attained
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    {T : ℝ} (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) :
    ∀ t ∈ Ioc 0 T, ∀ x : M, ∃ s ∈ Icc 0 t,
      nablaRmSupWeight S t x ≤
        2 * Real.sqrt T * Real.sqrt (s * nablaKRm04NormSqIntrinsic S 1 s x) := by
  have hc (x : M) : ContinuousOn
      (fun s : ℝ => nablaKRm04NormSqIntrinsic S 1 s x) (Icc 0 T) := by
    have hj := closed_slab_curvature_norm_continuous (I := I) S hT hgram 1
    have hm : MapsTo (fun t : ℝ => (t,x)) (Icc 0 T) (Icc 0 T ×ˢ (univ : Set M)) :=
      fun t ht => ⟨ht,mem_univ x⟩
    have hp : ContinuousOn (fun t : ℝ => (t,x)) (Icc 0 T) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact ContinuousOn.comp
      (g := fun q : ℝ × M => nablaKRm04NormSqIntrinsic S 1 q.1 q.2)
      (f := fun t : ℝ => (t,x)) hj hp hm
  intro t ht x
  have hct : ContinuousOn (fun s : ℝ => nablaKRm04NormSqIntrinsic S 1 s x) (Icc 0 t) :=
    (hc x).mono (Icc_subset_Icc le_rfl ht.2)
  exact exists_mem_Icc_nablaRmSupWeight_le (I := I) (M := M) S (t := t) (T := T) ht.1.le ht.2 x hct


theorem shiFirstDerivative_local_nablaRmSupWeight_of_closed_slab
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T a Ksec R r₁ r₂ Clap Cconn : ℝ} (p : M)
    (hT : 0 < T) (ha : 32 ≤ a)
    (hslab : Icc 0 T ⊆ D.carrier) (hreg : Ioc 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (S.base.metric q.1) x₀ q.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hball : IsCompact {y : M |
      riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R})
    (hKsec : Ksec ≤ 0)
    (hsec : ∀ y : M, riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R →
      Geometry.Riemannian.SectionalBoundedBelowAt (S.base.metric 0) y Ksec)
    (hu : ∀ s ∈ Icc 0 T, ∀ y : M,
      riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R →
        nablaKRm04NormSqIntrinsic S 0 s y ≤ 1)
    (hr₁ : 0 < r₁) (hr₁₂ : r₁ < r₂) (hr₂R : r₂ ≤ R)
    (hClap : 0 ≤ Clap) (hCconn : 0 ≤ Cconn)
    (hlap : InitialDistanceFlowLaplacianBound S T p
      {y : M | riemannianEDistOf (S.base.metric 0) p y ≤ ENNReal.ofReal R}
      r₁ Ksec Clap Cconn (nablaRmSupWeight S)) :
    ∀ t ∈ Ioc 0 T, ∀ x : M,
      riemannianEDistOf (S.base.metric 0) p x ≤ ENNReal.ofReal r₁ →
        Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) ≤
          shiFirstDerivativeLocalConst (Module.finrank ℝ E) a T r₁ r₂ Clap Cconn
            (2 * Real.sqrt T) / Real.sqrt t := by
  obtain ⟨cut⟩ := nonempty_shiInitialDistanceCutoff_of_solution S hS (K := 1) p hT
    hslab hreg hball hKsec hsec hu hr₁ hr₁₂ hr₂R hClap hCconn
    (fun t y => nablaRmSupWeight_nonneg S t y) hlap
  refine shiFirstDerivative_local_of_cutoff_of_positive_time_regular S hS cut hT ha
    (shiInitialCutoffA_nonneg _ _ _ _ _)
    (shiInitialCutoffB_nonneg _ hr₁₂.le hClap)
    (shiInitialCutoffD_nonneg hr₁₂.le hCconn) (by positivity) hreg
    ?_ (closed_slab_bernstein_continuous S hT hgram a)
    (fun t ht x _ => closed_slab_weight_attained S hT hgram t ht x)
  · intro s hs y hy
    apply hu s hs y
    have hmem : y ∈ cut.support := by
      by_contra hn
      rw [cut.support_zero y hn] at hy
      exact lt_irrefl 0 hy
    exact (cut.support_subset_ball hmem).le.trans (ENNReal.ofReal_le_ofReal hr₂R)

end DifferentialGeometry.PDE.RicciFlow
