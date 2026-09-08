import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneSplitting
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ProductCover

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature
open Curvature.DimensionThree
open Riemannian.Topology.UniversalCover

variable {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners Real (DifferentialGeometry.Topology.Morse.MorseModel 3) H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

theorem exists_roundThreeCylinder_solitonModelCovering_of_rank_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀
      (by change Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3
          simp [DifferentialGeometry.Topology.Morse.MorseModel]) = 1) :
    ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric
        roundThreeCylinderShrinkerPotential g f cover := by
  have hsplit := gradientRicciSoliton_hasCurvatureSurfaceProductSplitting_of_rank_one
    g f (show (0 : Real) ≤ 1 by norm_num) h.1 h.2.1 hrank
  let _ : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨_, P, -, -, -, hpositive⟩ := hsplit
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) ∞ P.N :=
    P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  let _ : SimplyConnectedSpace P.N := P.simplyConnectedN
  let k : SmoothRiemannianMetric
      (𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) P.N := P.metricN
  let Phi := P.F
  have hdim : Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 2) = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hpull : Diffeomorph.pullbackMetricCross (liftedMetric (I := I) g) Phi =
      k.prod (euclideanMetric (E := Real)) := by
    simpa only [k, Phi, flatModelMetric] using P.pullbackMetric_eq_prod g
  have hpos : ∃ x : P.N, 0 < metricScalarAt
      (I := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2)) k x := by
    exact ⟨Classical.choice (inferInstance : Nonempty P.N), by simpa [k] using hpositive _⟩
  apply exists_roundThreeCylinder_solitonModelCovering_of_product_diffeomorph
    (E₂ := DifferentialGeometry.Topology.Morse.MorseModel 2)
    (J := 𝓘(Real, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (N := P.N) (g := g) (f := f) (k := k) (Phi := Phi)
    (h := h) (hk := P.completeN) (hpull := hpull) hdim hpos

end DifferentialGeometry.Geometry
