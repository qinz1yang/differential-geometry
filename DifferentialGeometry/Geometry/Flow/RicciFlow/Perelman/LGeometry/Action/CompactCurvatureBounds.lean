import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Operator.NormGradSqTime
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.TimeSlab

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lGrad_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t0 t1 : Real} (hK : Set.Icc t0 t1 ⊆ D.regular) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 → ∀ x (v : TangentSpace I x),
        |(S.base.metric t).inner x
            (gradientFun (I := I) (S.base.metric t) (S.scalar t) x) v| ≤
          C * Real.sqrt ((S.base.metric t).inner x v v) := by
  let q : Real × M → Real := fun p ↦
    (S.base.metric p.1).inner p.2
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
      (gradientFun (I := I) (S.base.metric p.1) (S.scalar p.1) p.2)
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
        (modelWithCornersSelf Real Real) ∞
        (fun p : Real × M ↦
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (S.base.metric p.1) x₀ p.2 i j)
        (D.regular ×ˢ
          (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    let e := trivializationAt E (TangentSpace I : M → Type _) x₀
    let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
    let frame : Fin (Module.finrank Real E) →
        (x : M) → TangentSpace I x := e.localFrame b
    have hframe : IsLocalFrameOn I E ∞ frame e.baseSet := by
      simpa only [frame] using e.isLocalFrameOn_localFrame_baseSet I ∞ b
    have hcomp := hS.smoothMetric.frameCompSmooth frame hframe i j
    refine hcomp.congr ?_
    intro p hp
    have hframe_eq (k : Fin (Module.finrank Real E)) :
        frame k p.2 = DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ k p.2 := by
      dsimp only [frame]
      rw [e.localFrame_apply_of_mem_baseSet b hp.2]
      change (e.linearEquivAt Real p.2 hp.2).symm (b k) =
        e.symmL Real p.2 ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)
      dsimp only [b]
      rw [e.linearEquivAt_symm_apply, e.symmL_apply hp.2]
    simp only [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, SolutionOn.family_metric]
    rw [hframe_eq i, hframe_eq j]
  have hq : ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      q (D.regular ×ˢ (Set.univ : Set M)) := by
    simpa only [q, SolutionOn.family_metric] using
      gradSq_joint (I := I) S.family.metric D.regular_isOpen hgram
        S.scalar (scalar_joint (I := I) S hS)
  let f : Real × M → Real := fun p ↦ Real.sqrt (q p)
  let K : Set (Real × M) := Set.Icc t0 t1 ×ˢ (Set.univ : Set M)
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_univ
  have hfcont : ContinuousOn f K := by
    have hcomp := Real.continuous_sqrt.continuousOn.comp
      (hq.continuousOn.mono (Set.prod_mono hK Set.Subset.rfl))
      (fun _ _ ↦ Set.mem_univ _)
    have hfun : Real.sqrt ∘ q = fun p ↦ Real.sqrt (q p) := by
      rfl
    rw [hfun] at hcomp
    exact hcomp
  obtain ⟨C₀, hC₀⟩ := bddAbove_def.mp (hKcompact.bddAbove_image hfcont)
  refine ⟨max 0 C₀, le_max_left _ _, ?_⟩
  intro t ht x v
  have hgrad : Real.sqrt (q (t, x)) ≤ max 0 C₀ := by
    apply (hC₀ (f (t, x)) ⟨(t, x), ⟨ht, Set.mem_univ x⟩, rfl⟩).trans
    exact le_max_right _ _
  have hcs :=
    DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
      (I := I) (M := M) (S.base.metric t) x
        (gradientFun (I := I) (S.base.metric t) (S.scalar t) x) v
  exact hcs.trans (mul_le_mul_of_nonneg_right (by simpa only [q] using hgrad)
    (Real.sqrt_nonneg _))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRicci_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {t0 t1 : Real} (hK : Set.Icc t0 t1 ⊆ D.regular) :
    ∃ C : Real, 0 ≤ C ∧
      ∀ t, t ∈ Set.Icc t0 t1 → ∀ x (v : TangentSpace I x),
        |S.ricciAt t x (vec2 v v)| ≤
          C * (S.base.metric t).inner x v v := by
  let G : Real → SmoothRiemannianMetric I M := fun t ↦ S.base.metric t
  let A : (t : Real) → (x : M) → Tensor0SSpace 2 I x :=
    fun t x ↦ S.ricciAt t x
  have hcarrier : Set.Icc t0 t1 ⊆ D.carrier :=
    hK.trans D.regular_subset
  have hGcont : Continuous
      (metricTimeBundleQuad (I := I) (M := M) G (Set.Icc t0 t1)) := by
    simpa only [G, SolutionOn.family_metric] using
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := I) (M := M)
        S.family.metric hS.smoothMetric hcarrier
  have hcompact : IsCompact
      (Set.univ : Set (MetricUnitTangentTimeSlab (I := I) (M := M) G
        (Set.Icc t0 t1))) :=
    metricUnitTimeSlab_icc_compact_of_bundle (I := I) (M := M)
      G t0 t1 (S.base.metric t0) hGcont
  have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2
      (Set.Icc t0 t1) A := by
    simpa only [A, SolutionOn.ricciAt, SolutionOn.ricci,
      SolutionFamily.ricci_apply] using
      tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
        hS.ricciCont hcarrier
  have hcont := timeSlabAbsQuadCont (I := I) (M := M) G A
    (Set.Icc t0 t1)
    (tensor0SFamilyContinuousOnSet.tangentBundle (I := I) (M := M) hA)
  obtain ⟨C, hC, hbound⟩ :=
    compactUnitTimeSlab_absBound (I := I) (M := M) G A
      (Set.Icc t0 t1) hcompact hcont
  refine ⟨C, hC, ?_⟩
  intro t ht x v
  have hv : vec2 (I := I) v v = fun _ : Fin 2 ↦ v := by
    funext i
    simp only [DifferentialGeometry.Geometry.Curvature.vec2]
    split <;> rfl
  rw [hv]
  simpa only [G, A, quad02] using hbound t ht x v

end DifferentialGeometry.PDE.RicciFlow.Perelman
