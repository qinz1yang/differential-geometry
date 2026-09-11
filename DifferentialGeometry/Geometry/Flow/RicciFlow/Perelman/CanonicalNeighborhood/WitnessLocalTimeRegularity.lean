import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenChartTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.LocalPullback


set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [SigmaCompactSpace N]

private local instance localTimeAmbientC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance localTimeTargetC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem local_time_tower_chart_contDiffOn_closed
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    {D : RealTimeInterval} (T : SolutionOn (I := I) (M := U) D) (hT : IsSolutionOn T)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hzero : ∀ t, ∀ x : U, ∀ v : Fin 2 → TangentSpace I x,
      A 0 t (x : M) v = (T.base.metric t).inner x (v 0) (v 1))
    (hA : ∀ q t, t ∈ Icc c b → ∀ x ∈ U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t)
    (p : U) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I (p : M) (p : M) ∈ V ∧
      V ⊆ (extChartAt I (p : M)).target ∧
      ∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun z : ℝ × E => A q z.1 ((extChartAt I (p : M)).symm z.2)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j)
            ((extChartAt I (p : M)).symm z.2))) (Icc c b ×ˢ V) := by
  obtain ⟨V, hV, hpV, hVt, hjet⟩ :=
    solution_chartGram_timeJets_contDiffOn_closed T hT hac hcb hslab hreg p
  refine ⟨V, hV, hpV, hVt.trans (extChartAt_opens_target_subset U p), ?_⟩
  intro q slots
  apply (hjet q (slots 0) (slots 1)).congr
  rintro ⟨t, z⟩ ⟨ht, hz⟩
  let x : U := (extChartAt I p).symm z
  have hxchart : (x : M) ∈ (chartAt H (p : M)).source := by
    have hxlocal := (extChartAt I p).map_target (hVt hz)
    rw [extChartAt_source_eq_chartAt_source, TopologicalSpace.Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hxlocal
    exact hxlocal
  have hxcoe : (x : M) = (extChartAt I (p : M)).symm z :=
    extChartAt_opens_symm_coe U p (hVt hz)
  let v : Fin 2 → TangentSpace I (x : M) :=
    fun j => chartBasisVecFiber (I := I) (p : M) (slots j) (x : M)
  have hbase (s : ℝ) (_hs : s ∈ Icc c b) :
      iteratedDerivWithin 0
        (fun r => chartGramOnE (I := I) (T.base.metric r) p (slots 0) (slots 1) z)
        (Icc c b) s = A 0 s (x : M) v := by
    rw [iteratedDerivWithin_zero, hzero s x v]
    change (T.base.metric s).inner x
      (chartBasisVecFiber (I := I) p (slots 0) x)
      (chartBasisVecFiber (I := I) p (slots 1) x) = _
    rw [chartBasisVecFiber_restrictOpen U p x hxchart,
      chartBasisVecFiber_restrictOpen U p x hxchart]
  have heq := derivWithin_tower_eq_of_genuine (uniqueDiffOn_Icc hcb)
    (fun k s => iteratedDerivWithin k
      (fun r => chartGramOnE (I := I) (T.base.metric r) p (slots 0) (slots 1) z) (Icc c b) s)
    (fun k s => A k s (x : M) v)
    (fun _ _ _ => by rw [iteratedDerivWithin_succ])
    (fun k s hs => (tensor0SEvalCLM (I := I) (M := M) (x := (x : M)) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hA k s hs x x.property)) hbase q t ht
  dsimp only [v] at heq
  rw [hxcoe] at heq
  exact heq.symm


theorem partial_pullback_time_tower_contDiffOn_closed
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ D.carrier) (hreg : Ioo a b ⊆ D.regular)
    (Phi : PartialDiffeomorph I I M N ∞)
    (U : TopologicalSpace.Opens M) [SigmaCompactSpace U]
    (hU : (U : Set M) ⊆ Phi.source)
    (A : ℕ → ℝ → Tensor0SField (I := I) (M := M) (n := ∞) 2)
    (hzero : ∀ t, ∀ x ∈ U, ∀ v : Fin 2 → TangentSpace I x,
      A 0 t x v = (S.base.metric t).inner (Phi x)
        (mfderiv I I Phi x (v 0)) (mfderiv I I Phi x (v 1)))
    (hA : ∀ q t, t ∈ Icc c b → ∀ x ∈ U,
      HasDerivWithinAt (fun s => A q s x) (A (q + 1) t x) (Icc c b) t)
    (p : U) :
    ∃ V : Set E, IsOpen V ∧ extChartAt I (p : M) (p : M) ∈ V ∧
      V ⊆ (extChartAt I (p : M)).target ∧
      ∀ q : ℕ, ∀ slots : Fin 2 → Fin (Module.finrank ℝ E),
        ContDiffOn ℝ ∞ (fun z : ℝ × E => A q z.1 ((extChartAt I (p : M)).symm z.2)
          (fun j => chartBasisVecFiber (I := I) (p : M) (slots j)
            ((extChartAt I (p : M)).symm z.2))) (Icc c b ×ˢ V) := by
  let W : TopologicalSpace.Opens N := ⟨Phi '' (U : Set M), image_opens_isOpen Phi hU⟩
  let : SigmaCompactSpace W := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen I W.isOpen)
  let e : U ≃ₘ⟮I, I⟯ W := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Phi hU
  let T := solutionOnPullback (solutionOnRestrictOpen S W) e
  have hT : IsSolutionOn T := isSolutionOn_pullback _ (isSolutionOn_restrictOpen S hS W) e
  apply local_time_tower_chart_contDiffOn_closed U T hT hac hcb hslab hreg A ?_ hA p
  intro t x v
  rw [hzero t x x.property v]
  change _ = (Diffeomorph.pullbackMetric ((S.base.metric t).restrictOpen W) e).inner x (v 0) (v 1)
  rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
  exact (congrArg₂ (fun v' w' => (S.base.metric t).inner (Phi (x : M)) v' w')
    (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x (v 0))
    (DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Phi hU x (v 1))).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
