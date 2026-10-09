import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardClosedLimitCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderClosedLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.BufferedReference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Scaling
import DifferentialGeometry.Geometry.Metric.Tensor.CompactBounds

noncomputable section
open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

section

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem solutionOn_closed_of_joint_gram
    {a b : ℝ} (hab : a < b) (g : ℝ → SmoothRiemannianMetric I M)
    (hgram : ∀ (q : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (g p.1) q p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) q).baseSet))
    (hpde : ∀ t ∈ Ioo a b, ∀ (q : M) (v w : TangentSpace I q),
      HasDerivAt (fun s => (g s).inner q v w) (-2 * ricciTensor (g t) q v w) t) :
    IsSolutionOn ({ base := { metric := g } } :
      SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le)) := by
  apply isSolutionOn_of_joint_metric (RealTimeInterval.closed a b hab.le)
    (uniqueDiffOn_Icc hab) g
    (metricCLMSection_jointContMDiffOn_of_chartGram_on g (Icc a b) hgram)
  intro t ht q v w
  exact (hpde t ht q v w).hasDerivWithinAt


end

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Q := cylinderReferenceCopy.Q
private abbrev C := Metric.sphere (0 : E3) 1 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : ConnectedSpace (Metric.sphere (0 : E3) 1) :=
  Subtype.connectedSpace (isConnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by simp [E3])) (0 : E3) zero_le_one)
private local instance : ConnectedSpace Q :=
  cylinderReferenceCopy.equiv.toHomeomorph.connectedSpace_iff.mp inferInstance

private theorem shrinkingCylinder_curvature_bound {b : ℝ} (hb : b < 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, t ≤ b → ∀ x : C,
      normSq0S (shrinkingCylinderMetric (E := E3) t) x 4
        (metricRm04At (shrinkingCylinderMetric (E := E3) t) x) ≤ K := by
  let g := roundMetric (E := E3) (n := 2)
  obtain ⟨B, hB, hbound⟩ := Geometry.Tensor.exists_pos_bound_norm_on_compact g
    (metricRm04 g) (isCompact_univ)
  let A := 2 * (1 - b)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨(A⁻¹) ^ 2 * B ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro t ht x
  have ht1 : t < 1 := ht.trans_lt hb
  let c := 2 * (1 - t)
  have hc : 0 < c := by dsimp [c]; positivity
  have hAc : A ≤ c := by dsimp [A, c]; linarith
  have hmetric : shrinkingCylinderMetric (E := E3) t = cylinderMetric (scaleMetric c hc g) := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [shrinkingCylinderMetric_inner ht1, cylinderMetric_inner]
    exact congrArg (fun z : ℝ => z + v.2 * w.2)
      (scaleMetric_inner c hc g y.1
        (v.1 : TangentSpace (𝓡 2) y.1) (w.1 : TangentSpace (𝓡 2) y.1)).symm
  rw [hmetric]
  change normSq0S ((scaleMetric c hc g).prod (euclideanMetric (E := ℝ))) x 4
    (metricRm04At ((scaleMetric c hc g).prod (euclideanMetric (E := ℝ))) x) ≤ _
  rw [normSq0S_metricRm04At_productReal]
  have hscale : normSq0S (scaleMetric c hc g) x.1 4 (metricRm04At (scaleMetric c hc g) x.1) =
      (c⁻¹) ^ 2 * normSq0S g x.1 4 (metricRm04At g x.1) := by
    simp only [← metricRm04_apply]
    rw [metricRm_scale, normSq0S_smul, normSq0S_scale]
    field_simp
  rw [hscale]
  have hrm : normSq0S g x.1 4 (metricRm04At g x.1) ≤ B ^ 2 := by
    have h := hbound x.1 (mem_univ _)
    have hn := normSq0S_nonneg g x.1 4 (metricRm04At g x.1)
    rw [metricRm04_apply] at h
    exact (Real.sqrt_le_iff.mp h).2
  have hi : c⁻¹ ≤ A⁻¹ := inv_anti₀ hA hAc
  have hisq : (c⁻¹) ^ 2 ≤ (A⁻¹) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hc.le) hi 2
  exact mul_le_mul hisq hrm (normSq0S_nonneg _ _ _ _) (sq_nonneg _)


private theorem cylinder_limit_eq_shrinking_of_closed_solution
    {τ : ℝ} (hτ : 0 < τ) (g : ℝ → SmoothRiemannianMetric (𝓡 3) Q)
    (hgram : ∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) q p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (g s).inner q v w) (-2 * ricciTensor (g t) q v w) t)
    (hzero : g 0 = cylinderReferenceMetric)
    (hcurv : ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 τ, ∀ q : Q,
      normSq0S (g t) q 4 (metricRm04 (g t) q) ≤ K) :
    ∀ t ∈ Icc 0 τ, t < 1 →
      Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv =
        shrinkingCylinderMetric (E := E3) t := by
  let S₁ : SolutionOn (I := 𝓡 3) (M := Q) (RealTimeInterval.closed 0 τ hτ.le) :=
    { base := { metric := g } }
  have hS₁ : IsSolutionOn S₁ := solutionOn_closed_of_joint_gram hτ g hgram hpde
  let S₂c : SolutionOn (I := IC) (M := C)
      (RealTimeInterval.closedOpen (-1) 1 (by norm_num)) :=
    { base := { metric := shrinkingCylinderMetric (E := E3) } }
  have hS₂c : IsSolutionOn S₂c := shrinkingCylinderMetric_isSolutionOn_interval
    (E := E3) (by norm_num : (-1 : ℝ) < 1) le_rfl
  let S₂ := S₂c.pullback cylinderReferenceCopy.equiv.symm
  have hS₂ : IsSolutionOn S₂ := hS₂c.pullback S₂c cylinderReferenceCopy.equiv.symm
  obtain ⟨R₁, hR₁, hRm₁⟩ := hcurv
  intro t ht ht1
  by_cases ht0 : t = 0
  · subst t
    rw [hzero, pullback_cylinderReferenceMetric, shrinkingCylinderMetric_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  obtain ⟨R₂, hR₂, hRm₂⟩ := shrinkingCylinder_curvature_bound ht1
  have hcomplete₂ : RiemannianMetricComplete (S₂.base.metric (-1)) :=
    RiemannianMetricComplete.pullbackCross _ cylinderReferenceCopy.equiv.symm
      (shrinkingCylinderMetric_complete (E := E3) (-1))
  have heq := forward_unique_on_closed_slab_of_complete_bounded_curvature_of_buffered_reference
    S₁ S₂ hS₁ hS₂ (a₀ := -1) (a := 0) (b := t) (by norm_num) htpos
    (fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
    (fun s hs => ⟨hs.1, hs.2.trans_lt ht1⟩)
    (fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩)
    (fun s hs => ⟨hs.1, hs.2.trans ht1⟩)
    hcomplete₂ hR₁ hR₂
    (fun s hs q => hRm₁ s ⟨hs.1, hs.2.trans ht.2⟩ q)
    (by
      intro s hs q
      change normSq0S (Diffeomorph.pullbackMetricCross
        (shrinkingCylinderMetric (E := E3) s) cylinderReferenceCopy.equiv.symm) q 4
        (metricRm04At (Diffeomorph.pullbackMetricCross
          (shrinkingCylinderMetric (E := E3) s) cylinderReferenceCopy.equiv.symm) q) ≤ R₂
      rw [riemannNormSq_cross]
      exact hRm₂ s hs.2 _)
    (by change g 0 = Diffeomorph.pullbackMetricCross (shrinkingCylinderMetric (E := E3) 0)
          cylinderReferenceCopy.equiv.symm
        rw [hzero, shrinkingCylinderMetric_zero]
        rfl)
  have h := congrArg (fun G => Diffeomorph.pullbackMetricCross G cylinderReferenceCopy.equiv)
    (heq t ⟨htpos.le, le_rfl⟩)
  change Diffeomorph.pullbackMetricCross (g t) cylinderReferenceCopy.equiv =
    Diffeomorph.pullbackMetricCross (Diffeomorph.pullbackMetricCross
      (shrinkingCylinderMetric (E := E3) t) cylinderReferenceCopy.equiv.symm)
      cylinderReferenceCopy.equiv at h
  simpa only [Diffeomorph.pullbackMetricCross_trans, Diffeomorph.self_trans_symm,
    Diffeomorph.pullbackMetricCross_refl] using h

private local instance : TopologicalSpace cylinderPointedReference.M := cylinderPointedReference.topology
private local instance : ChartedSpace E3 cylinderPointedReference.M := cylinderPointedReference.charted
private local instance : T2Space cylinderPointedReference.M := cylinderPointedReference.t2
private local instance : IsManifold (𝓡 3) ∞ cylinderPointedReference.M := cylinderPointedReference.smooth
private local instance : SigmaCompactSpace cylinderPointedReference.M := cylinderPointedReference.sigmaCompact

theorem standard_cylinder_closed_limit_eq_shrinking
    {τ : ℝ} {hτ : 0 < τ} {hlt : ENNReal.ofReal τ < uniformStandardLifetime}
    {S : ℕ → StandardSolution} {x : ℕ → E3} {φ : ℕ → ℕ}
    (Φ : PointedCGHMaps (standardClosedPointedFlowSequence τ hτ hlt S x)
      cylinderPointedReference φ)
    (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (hinit : ∀ j, sourceMetric Φ hsrc htgt j 0 =
      sourceMetricRestriction Φ cylinderReferenceMetric j)
    (bf : BumpFamily Φ)
    (co : FlowMetricConvergenceData Φ cylinderReferenceMetric bf hsrc htgt 0 τ)
    (hzero : co.gInf 0 = cylinderReferenceMetric)
    (hgram : ∀ (q : Q) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × Q => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix
          (co.gInf p.1) q p.2 i j)
        (Icc 0 τ ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) q).baseSet))
    (hpde : ∀ t ∈ Ioo 0 τ, ∀ (q : Q) (v w : TangentSpace (𝓡 3) q),
      HasDerivAt (fun s => (co.gInf s).inner q v w)
        (-2 * ricciTensor (co.gInf t) q v w) t) :
    ∀ t ∈ Icc 0 τ, t < 1 →
      Diffeomorph.pullbackMetricCross (co.gInf t) cylinderReferenceCopy.equiv =
        shrinkingCylinderMetric (E := E3) t := by
  apply cylinder_limit_eq_shrinking_of_closed_solution hτ co.gInf hgram hpde hzero
  exact standard_closed_limit_curvature_bound Φ hsrc htgt hinit bf co


end DifferentialGeometry.PDE.RicciFlow
