import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRankModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCurvatureRank

set_option autoImplicit false

noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry
open Curvature Curvature.DimensionThree
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_solitonModelCovering_trichotomy
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) :
    (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ∨
    (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ∨
    (∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  rcases gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy g f
    (show (0 : ℝ) ≤ 1 by norm_num) h.1 h.2.1 hdim x with hzero | hone | hthree
  · exact Or.inl (exists_gaussian_solitonModelCovering_of_rank_zero h hdim hzero)
  · exact Or.inr (Or.inr (exists_roundThreeCylinder_solitonModelCovering_of_rank_one h hdim hone))
  · exact Or.inr (Or.inl (exists_roundThreeSphere_solitonModelCovering_of_rank_three h hdim hthree))

theorem normalizedGradientRicciSoliton_solitonModelCovering_classification
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3) :
    let gaussian := ∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover
    let sphere := ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgs : ¬ (gaussian ∧ sphere) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hs⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeSphere hg hs
  have hgc : ¬ (gaussian ∧ cylinder) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeCylinder hg hc
  have hsc : ¬ (sphere ∧ cylinder) := by
    rintro ⟨⟨_, hs⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_roundThreeSphere_and_roundThreeCylinder hs hc
  rcases normalizedGradientRicciSoliton_solitonModelCovering_trichotomy h hdim with hg | hs | hc
  · exact Or.inl ⟨hg, fun hs => hgs ⟨hg, hs⟩, fun hc => hgc ⟨hg, hc⟩⟩
  · exact Or.inr (Or.inl ⟨hs, fun hg => hgs ⟨hg, hs⟩, fun hc => hsc ⟨hs, hc⟩⟩)
  · exact Or.inr (Or.inr ⟨hc, fun hg => hgc ⟨hg, hc⟩, fun hs => hsc ⟨hs, hc⟩⟩)

end DifferentialGeometry.Geometry
