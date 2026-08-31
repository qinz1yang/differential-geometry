import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.DimensionBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerBound.Slice
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.DomainContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.UniformBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metric_complete
    (g : SmoothRiemannianMetric I M) :
    RiemannianMetricComplete (I := I) g := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      (WithTop.coe_le_coe.2 (le_top : (1 : ℕ∞) ≤ (⊤ : ℕ∞)))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  refine ⟨?_⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  infer_instance

omit [NeZero (Module.finrank Real E)] in
private theorem exists_rm_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {a T : Real} (hslab : Icc a T ⊆ D.regular) :
    ∃ K : Real, ∀ q ∈ Icc a T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
  classical
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) x₀ p.2 i j)
        (Icc a T ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    let e := trivializationAt E (TangentSpace I) x₀
    have hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞)
        (e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) e.baseSet :=
      e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
        (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)
    have hbridge : ∀ {x : M}, x ∈ e.baseSet →
        ∀ k : Fin (Module.finrank Real E),
          e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k x =
            DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k x := by
      intro x hx k
      rw [e.localFrame_apply_of_mem_baseSet (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) hx]
      unfold Bundle.Trivialization.basisAt DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber
      rw [Module.Basis.map_apply]
      exact congrFun (e.symm_continuousLinearEquivAt_eq hx) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
    have h := hS.smoothMetric.frameCompSmooth
      (e.localFrame (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) hframe i j
    refine (h.mono (prod_mono hslab (Subset.refl _))).congr ?_
    intro p hp
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, hbridge hp.2 i, hbridge hp.2 j,
      SolutionOn.family]
  obtain ⟨K, _hK, hbound⟩ :=
    rm04SlabSup (I := I) S.base.metric S.base.metric S.base.metric
      hgram hgram hgram
  refine ⟨K, ?_⟩
  intro q hq z
  simpa only [SolutionOn.family, SolutionFamily.rm04, metricRm04_apply,
    metricRm04At]
    using hbound q hq z

theorem redVolume_late_low [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {a₀ a omega : Real} (ha₀a : a₀ < a) (haomega : a < omega)
    (hreg : Ico a₀ omega ⊆ D.regular) (x₀ : M) :
    ∃ v₀ : ENNReal, 0 < v₀ ∧
      ∀ {T : Real}, a ≤ T → T < omega →
        ∀ (x : M) {tau : Real}, 0 < tau → tau ≤ T - a₀ →
          v₀ ≤ redVolume S T x tau := by
  classical
  let a₁ : Real := (a₀ + a) / 2
  have ha₀a₁ : a₀ < a₁ := by
    dsimp only [a₁]
    linarith
  have ha₁a : a₁ < a := by
    dsimp only [a₁]
    linarith
  have hregFwd : Icc a₀ a₁ ⊆ D.regular := by
    intro q hq
    apply hreg
    exact ⟨hq.1, hq.2.trans_lt (ha₁a.trans haomega)⟩
  obtain ⟨v₀, hv₀, hfloor⟩ :=
    redVolume_slice_low (I := I) S hS
      (l₀ := (Module.finrank Real E : Real) / 2)
      ha₀a₁ ha₁a haomega hregFwd x₀
  refine ⟨v₀, hv₀, ?_⟩
  intro T haT hTomega x tau htau htau_le
  have hslab : Icc a₀ T ⊆ D.regular := by
    intro q hq
    exact hreg ⟨hq.1, hq.2.trans_lt hTomega⟩
  have hTa₀ : 0 < T - a₀ := by linarith
  have hTa₁ : 0 < T - a₁ := by linarith
  obtain ⟨K, hRm⟩ := exists_rm_bound (I := I) S hS hslab
  have hg : RiemannianMetricComplete (I := I) (S.base.metric T) :=
    metric_complete (I := I) (S.base.metric T)
  obtain ⟨y₀, hy₀⟩ :=
    exists_redLen_le (I := I) S hS K T (T - a₀) (T - a₁) hg
      hTa₁ (by linarith) (by simpa only [sub_sub_cancel] using hslab)
      (by simpa only [sub_sub_cancel] using hRm) x
  have hslab₁ : Icc (T - (T - a₁)) T ⊆ D.regular := by
    intro q hq
    exact hslab ⟨by linarith [hq.1], hq.2⟩
  have hRm₁ : ∀ q ∈ Icc (T - (T - a₁)) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    intro q hq z
    exact hRm q ⟨by linarith [hq.1], hq.2⟩ z
  obtain ⟨y, W, hWmin, hWend, _hval, hmin⟩ :=
    exists_redMin_vec (I := I) S hS K T hg (T - a₁) hTa₁
      hslab₁ hRm₁ x
  have hWend' : lRegCurve S T x W (Real.sqrt (T - a₁)) = y := by
    simpa only [lExp] using hWend
  have hWred : redLength S T x
      (lRegCurve S T x W (Real.sqrt (T - a₁))) (T - a₁) ≤
        (Module.finrank Real E : Real) / 2 := by
    rw [hWend']
    exact (hmin y₀).trans hy₀
  have hWdom : Real.sqrt (T - a₀) ∈ lRegDomain S T x W := by
    apply mem_lRegDomain_of_time_slab (I := I) S hS T x W
      (Real.sqrt (T - a₀)) (Real.sqrt_nonneg _)
    simpa only [Real.sq_sqrt hTa₀.le, sub_sub_cancel] using hslab
  have hlate : v₀ ≤ redVolume S T x (T - a₀) :=
    hfloor haT hTomega hslab hWdom hWmin hWred
  have hslab₀ : Icc (T - (T - a₀)) T ⊆ D.regular := by
    simpa only [sub_sub_cancel] using hslab
  exact hlate.trans
    (redVolume_anti (I := I) S hS T x htau htau_le hslab₀)

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
