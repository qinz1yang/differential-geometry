import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSeamFacesParams
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource

/-!
# Draft 74, package S0 (torus): the `T² × [0, 1]` piece of a smooth injective full-rank map

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G29 (torus builder), the analogue of
`sphereIntervalPiece` (`AssemblyNormRP3Pieces`): the product atlas of `Torus × [0, 1]` (model
`torusModel.prod (𝓡∂ 1)`) transported to the half-space model `𝓡∂ 3`, through the model change
`(E¹ × E¹) × H¹ ≃ E² × H¹ ≃ H³` (`torusModelLinearEquiv_GSF`, then
`euclideanHalfSpaceProdHomeomorph`).

Universe: the piece type is `Torus × [0, 1] : Type 0` (the tree's `Torus` is not universe
polymorphic), so `W : CompactCarrier.{0}` (the closed route's universe).

* `torusIccChartedSpace74`, `torusIccIsManifold74`, `torusIccProdDiffeomorph74`;
* `torusIntervalPiece F hF hFb hFi : PieceEmbedding W` and `torusIntervalPieceDiffeo`
  (`map ∘ diffeo = F`), `range_torusIntervalPiece`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open DifferentialGeometry.Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- The model of `Torus × [0, 1]`. -/
abbrev TorusIccModel74 : Type :=
  ModelProd (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
    (EuclideanHalfSpace 1)

/-- The coordinate change `(E¹ × E¹) × E¹ ≃ E³` of the torus-interval model. -/
def torusIccCoordinates74 :
    ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
  (FC39P0.torusModelLinearEquiv_GSF.prodCongr (ContinuousLinearEquiv.refl ℝ _)).trans
    euclideanHalfSpaceProdCoordinates

/-- The model homeomorphism `(E¹ × E¹) × H¹ ≃ H³`. -/
def torusIccHomeomorph74 : TorusIccModel74 ≃ₜ EuclideanHalfSpace 3 :=
  (FC39P0.torusModelHomeomorph_GSF.prodCongr (Homeomorph.refl (EuclideanHalfSpace 1))).trans
    euclideanHalfSpaceProdHomeomorph

theorem torusIccHomeomorph74_compat (x : TorusIccModel74) :
    (𝓡∂ 3) (torusIccHomeomorph74 x) = torusIccCoordinates74 ((torusModel.prod (𝓡∂ 1)) x) :=
  rfl

/-- The half-space chart structure on `Torus × [0, 1]`. -/
@[instance_reducible]
def torusIccChartedSpace74 : ChartedSpace (EuclideanHalfSpace 3) (Torus × Icc (0 : ℝ) 1) :=
  chartedSpaceTransHomeomorph (M := Torus × Icc (0 : ℝ) 1) torusIccHomeomorph74

theorem torusIcc_isManifold74 :
    letI := torusIccChartedSpace74
    IsManifold (𝓡∂ 3) ∞ (Torus × Icc (0 : ℝ) 1) :=
  isManifold_transHomeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) torusIccHomeomorph74
    torusIccCoordinates74 torusIccHomeomorph74_compat

/-- The identity as a diffeomorphism from the half-space atlas to the product atlas. -/
def torusIccProdDiffeomorph74 :
    letI := torusIccChartedSpace74
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮𝓡∂ 3, torusModel.prod (𝓡∂ 1)⟯ (Torus × Icc (0 : ℝ) 1) := by
  letI := torusIccChartedSpace74
  exact
    { toEquiv := Equiv.refl _
      contMDiff_toFun :=
        (contMDiff_chartedSpaceTransHomeomorph_source_iff (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3)
          torusIccHomeomorph74 torusIccCoordinates74 torusIccHomeomorph74_compat
          (torusModel.prod (𝓡∂ 1))).mpr contMDiff_id
      contMDiff_invFun :=
        (contMDiff_chartedSpaceTransHomeomorph_iff (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3)
          torusIccHomeomorph74 torusIccCoordinates74 torusIccHomeomorph74_compat
          (torusModel.prod (𝓡∂ 1))).mpr contMDiff_id }

section TorusIntervalPiece

local instance torusIccCharts_R74 :
    ChartedSpace (EuclideanHalfSpace 3) (Torus × Icc (0 : ℝ) 1) :=
  torusIccChartedSpace74

local instance torusIccSmooth_R74 : IsManifold (𝓡∂ 3) ∞ (Torus × Icc (0 : ℝ) 1) :=
  torusIcc_isManifold74

variable {W : CompactCarrier.{0}} (F : Torus × Icc (0 : ℝ) 1 → W.Carrier)
  (hF : ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ F)
  (hFb : ∀ p, Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model F p)) (hFi : Injective F)

/-- **The `T² × [0, 1]` piece of a smooth injective full-rank map `F`**: the piece type
`Torus × [0, 1]` with the product atlas transported to the half-space model. -/
def torusIntervalPiece : PieceEmbedding W where
  Piece := Torus × Icc (0 : ℝ) 1
  map := F
  smooth := hF.comp torusIccProdDiffeomorph74.contMDiff
  mfderiv_bijective q := by
    let d := torusIccProdDiffeomorph74
    change Bijective (mfderiv (𝓡∂ 3) W.model (F ∘ d) q)
    rw [mfderiv_comp q (hF.mdifferentiableAt (by simp)) (d.contMDiff.mdifferentiableAt (by simp))]
    exact (hFb (d q)).comp (d.mfderivToContinuousLinearEquiv (by simp) q).bijective
  injective := hFi

/-- The model diffeomorphism of `torusIntervalPiece`. -/
def torusIntervalPieceDiffeo :
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯
      (torusIntervalPiece F hF hFb hFi).Piece :=
  torusIccProdDiffeomorph74.symm

theorem torusIntervalPiece_map_diffeo (p : Torus × Icc (0 : ℝ) 1) :
    (torusIntervalPiece F hF hFb hFi).map (torusIntervalPieceDiffeo F hF hFb hFi p) = F p :=
  rfl

theorem range_torusIntervalPiece : range (torusIntervalPiece F hF hFb hFi).map = range F :=
  rfl

end TorusIntervalPiece

end GC.GraphManifold.Assembly
