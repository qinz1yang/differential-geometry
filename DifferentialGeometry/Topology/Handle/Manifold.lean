import DifferentialGeometry.Topology.Handle.Defs
import DifferentialGeometry.Topology.Manifold.ClosedBall.Charts
import DifferentialGeometry.Topology.Manifold.Sphere.CellBoundary
import DifferentialGeometry.Topology.Manifold.ProductGroupoid

open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Handle

noncomputable section

universe u v w

@[reducible]
noncomputable def standardHandleChartedSpaceSucc (m n : ℕ) :
    ChartedSpace (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1)))
      (ClosedCell (m + 1) × ClosedCell (n + 1)) := by
  letI : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpaceSucc m
  letI : ChartedSpace (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1)) :=
    closedCellChartedSpaceSucc n
  exact prodChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1))
    (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1))

theorem standardHandleHasGroupoid (m n : ℕ) :
    @HasGroupoid (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1))) _
      (ClosedCell (m + 1) × ClosedCell (n + 1)) _ (standardHandleChartedSpaceSucc m n)
      (contDiffGroupoid (⊤ : ℕ∞)
        ((modelWithCornersEuclideanHalfSpace (m + 1)).prod
          (modelWithCornersEuclideanHalfSpace (n + 1)))) := by
  let : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
    closedCellChartedSpaceSucc m
  let : ChartedSpace (EuclideanHalfSpace (n + 1)) (ClosedCell (n + 1)) :=
    closedCellChartedSpaceSucc n
  let : HasGroupoid (ClosedCell (m + 1)) (contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersEuclideanHalfSpace (m + 1))) := closedCellHasGroupoid m
  let : HasGroupoid (ClosedCell (n + 1)) (contDiffGroupoid (⊤ : ℕ∞)
      (modelWithCornersEuclideanHalfSpace (n + 1))) := closedCellHasGroupoid n
  exact hasGroupoid_prod

theorem standardHandleIsManifold (m n : ℕ) :
    @IsManifold ℝ _ (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (n + 1))) _ _
      (ModelProd (EuclideanHalfSpace (m + 1)) (EuclideanHalfSpace (n + 1))) _
      ((modelWithCornersEuclideanHalfSpace (m + 1)).prod
        (modelWithCornersEuclideanHalfSpace (n + 1))) (⊤ : ℕ∞)
      (ClosedCell (m + 1) × ClosedCell (n + 1)) _ (standardHandleChartedSpaceSucc m n) := by
  let := standardHandleChartedSpaceSucc m n
  exact { toHasGroupoid := standardHandleHasGroupoid m n }

@[reducible]
noncomputable def standardHandleChartedSpace (k l : ℕ)
    [Fact (k = (k - 1) + 1)] [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle k l) := by
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  exact prodChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k)
    (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l)

@[reducible]
noncomputable def standardHandleZeroChartedSpace (l : ℕ) [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanHalfSpace ((l - 1) + 1)))
      (StandardHandle 0 l) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  exact prodChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0)
    (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l)

@[reducible]
noncomputable def standardHandleTopChartedSpace (k : ℕ) [Fact (k = (k - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((k - 1) + 1)) (EuclideanSpace ℝ (Fin 0)))
      (StandardHandle k 0) := by
  letI : ChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k) :=
    closedCellChartedSpace k
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0) :=
    closedCellZeroChartedSpace
  exact prodChartedSpace (EuclideanHalfSpace ((k - 1) + 1)) (ClosedCell k)
    (EuclideanSpace ℝ (Fin 0)) (ClosedCell 0)

@[reducible]
noncomputable def standardHandleTopSubChartedSpace (n : ℕ) [Fact (n = (n - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanHalfSpace ((n - 1) + 1)) (EuclideanSpace ℝ (Fin 0)))
      (StandardHandle n (n - n)) := by
  letI : ChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n) :=
    closedCellChartedSpace n
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n)) :=
    closedCellSubSelfChartedSpace n
  exact prodChartedSpace (EuclideanHalfSpace ((n - 1) + 1)) (ClosedCell n)
    (EuclideanSpace ℝ (Fin 0)) (ClosedCell (n - n))

@[reducible]
noncomputable def attachingRegionChartedSpace (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1)))
      (AttachingRegion k l) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  letI : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  infer_instance

instance attachingRegionChartedSpaceInst (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1)))
      (AttachingRegion k l) :=
  attachingRegionChartedSpace k l

theorem attachingRegionIsManifold (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    @IsManifold ℝ _
      (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((l - 1) + 1))) _
      _ (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1))) _
      ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
      (AttachingRegion k l) _ (attachingRegionChartedSpace k l) := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin (k - 1))) (CellBoundary k) :=
    cellBoundaryChartedSpace k
  let : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell l) :=
    closedCellChartedSpace l
  let : ChartedSpace (EuclideanHalfSpace ((l - 1) + 1)) (ClosedCell ((l - 1) + 1)) :=
    closedCellChartedSpaceSucc (l - 1)
  let : IsManifold (𝓡 (k - 1)) (⊤ : ℕ∞) (CellBoundary k) := cellBoundaryIsManifold k
  let : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell ((l - 1) + 1)) := closedCellIsManifold (l - 1)
  let : IsManifold (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (⊤ : ℕ∞)
      (ClosedCell l) := isManifoldOfHomeomorph
        (modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (closedCellReindexHomeo l)
  change @IsManifold ℝ _
    (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin ((l - 1) + 1))) _
    _ (ModelProd (EuclideanSpace ℝ (Fin (k - 1))) (EuclideanHalfSpace ((l - 1) + 1))) _
    ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
    (CellBoundary k × ClosedCell l) _ (attachingRegionChartedSpace k l)
  exact IsManifold.prod (I := 𝓡 (k - 1))
    (I' := modelWithCornersEuclideanHalfSpace ((l - 1) + 1)) (n := (⊤ : ℕ∞))
    (CellBoundary k) (ClosedCell l)

instance attachingRegionIsManifoldInst (k l : ℕ)
    [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) = (k - 1) + 1)]
    [Fact (l = (l - 1) + 1)] :
    IsManifold ((𝓡 (k - 1)).prod (modelWithCornersEuclideanHalfSpace ((l - 1) + 1))) (⊤ : ℕ∞)
      (AttachingRegion k l) :=
  attachingRegionIsManifold k l

end

end DifferentialGeometry.Topology.Handle
