import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCylinderTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductBackground
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Continuation

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] [I.Boundaryless]
  {D : RealTimeInterval} {a b : ℝ}

theorem continuous_product_solution_family_of_initial_agreement
    (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda) {d : ℝ} (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P]
    (seed : P → ProductCurve M)
    (hseed : @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a d)) seed)
    (hseedsol : ∀ p, (seed p).IsSolutionOn B.family.metric lambda (Icc a d))
    (solutions : P → ProductCurve M)
    (hsol : ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b))
    (htrace : ∀ p z, (solutions p).map z a = (seed p).map z a) :
    @Continuous P (ProductCurve M) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) solutions := by
  let A : QuotientProductAtlas I M := quotientProductAtlas
  let _ := A.charts
  let _ := A.smoothManifold
  obtain ⟨D', _, _, hB⟩ := exists_quotientProduct_ricciBackground_on_regular A B
  obtain ⟨Bhat, hf, _, _, _, _⟩ := hB lambda hlambda
  have hm : Bhat.family.metric =
      fun τ => quotientProductMetric A (B.family.metric τ) lambda hlambda :=
    congrArg (fun F => F.metric) hf
  let eP := A.smoothLoopEmbedding e
  have hseedmap := continuous_map_of_continuous_productCurve A e (uniqueDiffOn_Icc had) seed hseed
  have hseedmapSol (p : P) : (seed p).map.IsSolutionOn Bhat.family.metric (Icc a d) := by
    rw [hm]
    exact (seed p).isSolutionOn_map A B.family.metric lambda hlambda
      (uniqueDiffOn_Icc had) (hseedsol p)
  have hmapSol (p : P) : (solutions p).map.IsSolutionOn Bhat.family.metric (Icc a b) := by
    rw [hm]
    exact (solutions p).isSolutionOn_map A B.family.metric lambda hlambda
      (uniqueDiffOn_Icc B.lt) (hsol p)
  let initial : P → SmoothImmersion (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle) := fun p =>
    SmoothImmersion.slice (seed p).map (hseedmapSol p).smooth (hseedmapSol p).immersed
      a ⟨le_rfl, had.le⟩
  let : TopologicalSpace (SmoothImmersion (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle)) := smoothImmersionTopology eP
  have hslices : @Continuous (P × Icc a d) _ inferInstance (smoothImmersionTopology eP)
      (fun q => SmoothImmersion.slice (seed q.1).map (hseedmapSol q.1).smooth
        (hseedmapSol q.1).immersed q.2 q.2.2) :=
    continuous_iff_continuousAt.mpr fun q => continuousAt_slice_smoothImmersion eP had hseedmap
      (fun p => (hseedmapSol p).smooth) (fun p => (hseedmapSol p).immersed) q
  have hinit : @Continuous P _ inferInstance (smoothImmersionTopology eP) initial :=
    hslices.comp (continuous_id.prodMk (continuous_const (y := (⟨a, le_rfl, had.le⟩ : Icc a d))))
  have hmap : @Continuous P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
      (smoothCylinderTopology eP (Icc a b)) (fun p => (solutions p).map) :=
    compact_family_solution_continuous Bhat.toSmoothMetricWindow B.lt le_rfl eP initial hinit
      (fun p => (solutions p).map) hmapSol htrace
      (curveShorteningLocalUniqueness_of_compact Bhat.toSmoothMetricWindow)
  exact continuous_productCurve_of_continuous_map A e (uniqueDiffOn_Icc B.lt) solutions hmap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
