import DifferentialGeometry.Geometry.Curvature.AmbientNeckChartLeastRicci

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Neck

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] (J : ModelWithCorners ℝ F H)
  [TopologicalSpace M] [ChartedSpace H M]

structure cylindricalChart where
  domain : TopologicalSpace.Opens (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
  target : TopologicalSpace.Opens M
  chart : domain ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ target
  scale : ℝ
  scale_pos : 0 < scale

variable {J}

def cylindricalChart.region (C : cylindricalChart J (M := M)) (U : Set C.domain) : Set M :=
  Subtype.val '' (C.chart '' U)

theorem cylindricalChart.isOpen_region (C : cylindricalChart J (M := M))
    {U : Set C.domain} (hU : IsOpen U) : IsOpen (C.region U) :=
  C.target.isOpenEmbedding'.isOpenMap _ (C.chart.toHomeomorph.isOpenMap _ hU)

def cylindricalChart.axial (C : cylindricalChart J (M := M)) : M → ℝ :=
  Subtype.val.extend
    (fun y : C.target ↦ (Real.sqrt C.scale)⁻¹ *
      (C.chart.symm y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ).2)
    (fun _ ↦ 0)

variable [FiniteDimensional ℝ F] [IsManifold J ∞ M] [T2Space M]

def cylindricalChart.metricCloseOn (C : cylindricalChart J (M := M))
    (g : SmoothRiemannianMetric J M) (ε : ℝ) (U : Set C.domain) : Prop :=
  ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
    metricDerivNorm k
      (Diffeomorph.pullbackMetricCross (scaleMetric C.scale C.scale_pos (g.restrictOpen C.target)) C.chart)
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain)
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen C.domain) x ≤ ε

theorem cylindricalChart.exists_least_ricci_field [BoundarylessManifold J M]
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (hU : IsOpen U) (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : C.metricCloseOn g ε U) :
    ∃ (ν : M → ℝ) (Y : ∀ y : M, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ C.axial C.target ∧
      ContMDiffOn J 𝓘(ℝ) ∞ ν (C.region U) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J M)) (C.region U) ∧
      ∀ y ∈ C.region U, g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * C.scale * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J C.axial y (Y y) ∧ |mvfderiv J C.axial y (Y y) - 1| ≤ 92354 * ε :=
  DifferentialGeometry.Geometry.Curvature.exists_ambient_least_ricci_field_from_neck_chart
    C.domain C.target g C.chart C.scale C.scale_pos hU ε hε hsmall

end DifferentialGeometry.Geometry.Neck
