import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductCylinderTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductSolutionCorrespondence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.CompactFamilyExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ImmersionTopology
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ProductWindowSmoothness

section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_continuous_product_solution_lifts
    (A : QuotientProductAtlas I M) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (g : ℝ → SmoothRiemannianMetric I M) (lambda : ℝ) (hlambda : 0 < lambda)
    {s u : ℝ} (hsu : s < u) {P : Type*} [TopologicalSpace P]
    (c : P → CurveMap (M × Surgery.Topology.Circle))
    (hc : letI := A.charts
      letI := A.smoothManifold
      ∀ p, (c p).IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
        (fun t => quotientProductMetric A (g t) lambda hlambda) (Icc s u))
    (hcontinuous : letI := A.charts
      @Continuous P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
        (smoothCylinderTopology (A.smoothLoopEmbedding e) (Icc s u)) c) :
    ∃ lifts : P → ProductCurve M,
      @Continuous P (ProductCurve M) inferInstance
        (smoothProductCylinderTopology e (Icc s u)) lifts ∧
      ∀ p, (lifts p).IsSolutionOn g lambda (Icc s u) ∧
        ∀ z t, t ∈ Icc s u → (lifts p).map z t = c p z t := by
  classical
  let := A.charts
  let := A.smoothManifold
  have hexists := fun p => product_solution_lift A g lambda hlambda (c p) hsu
    (Icc s u) (Or.inr rfl) (hc p)
  choose lifts hlifts hmap using hexists
  have hmapcont : @Continuous P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
      (smoothCylinderTopology (A.smoothLoopEmbedding e) (Icc s u))
      (fun p => (lifts p).map) := by
    apply (@continuous_iff_continuousAt P (CurveMap (M × Surgery.Topology.Circle))
      inferInstance (smoothCylinderTopology (A.smoothLoopEmbedding e) (Icc s u))).mpr
    intro p
    exact smoothCylinderTopology_continuousAt_congr (A.smoothLoopEmbedding e)
      (fun p z t ht => (hmap p z t ht).symm)
      (@Continuous.continuousAt P (CurveMap (M × Surgery.Topology.Circle)) inferInstance
        (smoothCylinderTopology (A.smoothLoopEmbedding e) (Icc s u)) c p hcontinuous)
  exact ⟨lifts, continuous_productCurve_of_continuous_map A e
    (uniqueDiffOn_Icc hsu) lifts hmapcont, fun p => ⟨hlifts p, hmap p⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end

section

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M] {D : RealTimeInterval} {a b : ℝ}

theorem exists_continuous_product_solution_family_of_compact
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (lambda : ℝ) (hlambda : 0 < lambda)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → ProductCurve M)
    (hs : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hi : ∀ p, (initial p).ImmersedOn (I := I) {a})
    (hjets : ∀ m : ℕ, Continuous (fun q : P × ℝ => iteratedDeriv m
      (fun x => productEmbeddedCoordinates e (initial q.1) x a) q.2)) :
    ∃ d : ℝ, a < d ∧ d ≤ b ∧ ∃ solutions : P → ProductCurve M,
      @Continuous P (ProductCurve M) inferInstance
        (smoothProductCylinderTopology e (Icc a d)) solutions ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a d) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a := by
  let A : QuotientProductAtlas I M := quotientProductAtlas (I := I) (M := M)
  let := A.charts
  let := A.smoothManifold
  let eP := A.smoothLoopEmbedding e
  let L : (EuclideanSpace ℝ (Fin N) × ℂ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (N + 2)) :=
    ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin N))).prodCongr
      Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv).trans
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := N) (m := 2)).symm
  let initialImmersion : P → SmoothImmersion (I := I.prod 𝓘(ℝ, ℝ))
      (M := M × Surgery.Topology.Circle) := fun p =>
    SmoothImmersion.slice (initial p).map ((initial p).smoothOn_map A (hs p))
      (((initial p).map_immersedOn_iff A (hs p)).mpr (hi p)) a (mem_singleton a)
  have hjetsP : ∀ m : ℕ, Continuous (fun q : P × ℝ => iteratedDeriv m
      (fun x : ℝ => eP.map ((initialImmersion q.1).map x)) q.2) := by
    intro m
    have hjet (p : P) (x : ℝ) :
        iteratedDeriv m (fun y : ℝ => eP.map ((initialImmersion p).map y)) x =
          L (iteratedDeriv m (fun y => productEmbeddedCoordinates e (initial p) y a) x) := by
      have hfun : (fun y : ℝ => eP.map ((initialImmersion p).map y)) =
          L ∘ (fun y => productEmbeddedCoordinates e (initial p) y a) := rfl
      rw [hfun]
      simp only [iteratedDeriv, L.iteratedFDeriv_comp_left]
      rfl
    exact (L.continuous.comp (hjets m)).congr fun q => (hjet q.1 q.2).symm
  have hinit := continuous_smoothImmersion_of_continuous_jets eP initialImmersion hjetsP
  obtain ⟨Bhat, _, hmetric, _⟩ :=
    exists_smoothMetricWindow_quotientProduct A B lambda hlambda
  obtain ⟨d, had, hdb, curves, hcontinuous, hcurves⟩ :=
    exists_continuous_solution_family_of_compact Bhat eP initialImmersion hinit
  have hsol : ∀ p, (curves p).IsSolutionOn (I := I.prod 𝓘(ℝ, ℝ))
      (fun t => quotientProductMetric A (B.family.metric t) lambda hlambda) (Icc a d) := by
    rw [← hmetric]
    exact fun p => (hcurves p).1
  obtain ⟨lifts, hlifts, hmaps⟩ := exists_continuous_product_solution_lifts A e B.family.metric
    lambda hlambda had curves hsol hcontinuous
  exact ⟨d, had, hdb, lifts, hlifts, fun p => ⟨(hmaps p).1,
    fun z => ((hmaps p).2 z a ⟨le_rfl, had.le⟩).trans ((hcurves p).2 z)⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
end
