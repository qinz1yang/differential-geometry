import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointCurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointTimeExpressions
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow

private theorem compact_tower_mono_time (c K t T : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (ht : 0 ≤ t) (htT : t ≤ T) (N : ℕ) :
    DifferentialGeometry.Analysis.endpointTowerBound c K t A N ≤
      DifferentialGeometry.Analysis.endpointTowerBound c K T A N := by
  have hT : 0 ≤ T := ht.trans htT
  induction N with
  | zero => exact le_rfl
  | succ n ih =>
      have hl := DifferentialGeometry.Analysis.endpointTowerBound_nonneg c K t A hc hK ht n
      have hr := DifferentialGeometry.Analysis.endpointTowerBound_nonneg c K T A hc hK hT n
      simp only [DifferentialGeometry.Analysis.endpointTowerBound]
      gcongr

private theorem complete_tower_mono_time (c K t T : ℝ) (A : ℕ → ℝ)
    (hc : 0 ≤ c) (hK : 0 ≤ K) (ht : 0 ≤ t) (htT : t ≤ T) (N : ℕ) :
    DifferentialGeometry.Analysis.completeEndpointTowerBound c K t A N ≤
      DifferentialGeometry.Analysis.completeEndpointTowerBound c K T A N := by
  have hT : 0 ≤ T := ht.trans htT
  induction N with
  | zero => exact le_rfl
  | succ n ih =>
      have hl := DifferentialGeometry.Analysis.completeEndpointTowerBound_nonneg c K t A hc hK ht n
      have hr := DifferentialGeometry.Analysis.completeEndpointTowerBound_nonneg c K T A hc hK hT n
      simp only [DifferentialGeometry.Analysis.completeEndpointTowerBound]
      gcongr

theorem compactCurvatureEndpointBound_mono_time (n N : ℕ) (t T K : ℝ) (A : ℕ → ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (htT : t ≤ T) :
    compactCurvatureEndpointBound n N t K A ≤ compactCurvatureEndpointBound n N T K A := by
  apply Real.sqrt_le_sqrt
  exact compact_tower_mono_time _ K t T A
    (Finset.sum_nonneg fun k _ => rmTowerCost_nonneg n k) hK ht htT N

theorem completeCurvatureEndpointBound_mono_time (n N : ℕ) (t T K : ℝ) (A : ℕ → ℝ)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (htT : t ≤ T) :
    completeCurvatureEndpointBound n N t K A ≤ completeCurvatureEndpointBound n N T K A := by
  unfold completeCurvatureEndpointBound
  exact add_le_add (Real.sqrt_le_sqrt (complete_tower_mono_time _ K t T A
    (Finset.sum_nonneg fun k _ => rmTowerCost_nonneg n k) hK ht htT N)) le_rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem spatial_norm_continuous {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (hT : 0 < T)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet)) (k : ℕ) (x : M) :
    ContinuousOn (fun t => Real.sqrt (nablaKRm04NormSqIntrinsic S k t x)) (Icc 0 T) := by
  exact ((CurvatureExpression.curvature k).time_jet_contDiffOn S (Icc 0 T)
    (uniqueDiffOn_Icc hT) hgram 0 x).2.continuousOn.sqrt

section Complete
variable [SigmaCompactSpace M]

theorem curvature_endpoint_bound_complete_terminal (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K) (A : ℕ → ℝ)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcomplete : RiemannianMetricComplete (I := I) (S.base.metric 0)) (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K)
    (hinit : ∀ k ≤ N, ∀ x : M, Real.sqrt (nablaKRm04NormSqIntrinsic S k 0 x) ≤ A k) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤
        completeCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
  by_cases hp : 0 < T
  · intro k hk t ht x
    have hb : ∀ r ∈ Ico 0 T, Real.sqrt (nablaKRm04NormSqIntrinsic S k r x) ≤
        completeCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
      intro r hr
      let τ := (r + T) / 2
      have hτ : 0 < τ := by dsimp only [τ]; linarith [hr.1]
      have hτT : τ < T := by dsimp only [τ]; linarith [hr.2]
      have hrτ : r ≤ τ := by dsimp only [τ]; linarith [hr.2]
      have hsub : Icc 0 τ ⊆ Icc 0 T := fun z hz => ⟨hz.1, hz.2.trans hτT.le⟩
      have hg (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :=
        (hgram x₀ i j).mono (prod_mono hsub subset_rfl)
      have hh := curvature_endpoint_bound_complete τ hτ.le N K hK A D S hS hcomplete
        (hsub.trans hslab) (fun z hz hzpos => hregular ⟨hzpos, hz.2.trans_lt hτT⟩)
        hg (fun z hz => hcurv z (hsub hz)) hinit k hk r ⟨hr.1, hrτ⟩ x
      exact hh.trans (completeCurvatureEndpointBound_mono_time _ N τ T K A hK hτ.le hτT.le)
    have hcl : closure (Ico 0 T) = Icc 0 T := closure_Ico hp.ne
    have hc := spatial_norm_continuous S T hp hgram k x
    rw [← hcl] at hc
    exact le_on_closure hb hc continuousOn_const (by rw [hcl]; exact ht)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro k hk t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    have hsum : |A k| ≤ ∑ j ∈ Finset.range (N + 1), |A j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_range.mpr (by omega))
    exact ((hinit k hk x).trans (le_abs_self _)).trans
      (hsum.trans (le_add_of_nonneg_left (Real.sqrt_nonneg _)))
end Complete

section Compact
variable [CompactSpace M]

theorem curvature_endpoint_bound_compact_terminal (T : ℝ) (hT : 0 ≤ T)
    (N : ℕ) (K : ℝ) (hK : 0 ≤ K) (A : ℕ → ℝ)
    (D : RealTimeInterval) (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hslab : Icc 0 T ⊆ D.carrier) (hregular : Ioo 0 T ⊆ D.regular)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ K)
    (hinit : ∀ k ≤ N, ∀ x : M, Real.sqrt (nablaKRm04NormSqIntrinsic S k 0 x) ≤ A k) :
    ∀ k ≤ N, ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤
        compactCurvatureEndpointBound (Module.finrank ℝ E) N T K A +
          ∑ j ∈ Finset.range (N + 1), |A j| := by
  by_cases hp : 0 < T
  · intro k hk t ht x
    have hb : ∀ r ∈ Ico 0 T, Real.sqrt (nablaKRm04NormSqIntrinsic S k r x) ≤
        compactCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
      intro r hr
      let τ := (r + T) / 2
      have hτ : 0 < τ := by dsimp only [τ]; linarith [hr.1]
      have hτT : τ < T := by dsimp only [τ]; linarith [hr.2]
      have hrτ : r ≤ τ := by dsimp only [τ]; linarith [hr.2]
      have hsub : Icc 0 τ ⊆ Icc 0 T := fun z hz => ⟨hz.1, hz.2.trans hτT.le⟩
      have hg (x₀ : M) (i j : Fin (Module.finrank ℝ E)) :=
        (hgram x₀ i j).mono (prod_mono hsub subset_rfl)
      have hh := curvature_endpoint_bound_compact τ hτ N K hK A D S hS (hsub.trans hslab)
        (fun z hz hzpos => hregular ⟨hzpos, hz.2.trans_lt hτT⟩)
        hg (fun z hz => hcurv z (hsub hz)) hinit k hk r ⟨hr.1, hrτ⟩ x
      exact hh.trans (compactCurvatureEndpointBound_mono_time _ N τ T K A hK hτ.le hτT.le)
    have hcl : closure (Ico 0 T) = Icc 0 T := closure_Ico hp.ne
    have he : Real.sqrt (nablaKRm04NormSqIntrinsic S k t x) ≤
        compactCurvatureEndpointBound (Module.finrank ℝ E) N T K A := by
      have hc := spatial_norm_continuous S T hp hgram k x
      rw [← hcl] at hc
      exact le_on_closure hb hc continuousOn_const (by rw [hcl]; exact ht)
    exact he.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => abs_nonneg (A j)))
  · have hz : T = 0 := le_antisymm (le_of_not_gt hp) hT
    subst T
    intro k hk t ht x
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    have hsum : |A k| ≤ ∑ j ∈ Finset.range (N + 1), |A j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (A j)) (Finset.mem_range.mpr (by omega))
    exact ((hinit k hk x).trans (le_abs_self _)).trans
      (hsum.trans (le_add_of_nonneg_left (compactCurvatureEndpointBound_nonneg _ _ _ _ _)))
end Compact
end DifferentialGeometry.PDE.RicciFlow
