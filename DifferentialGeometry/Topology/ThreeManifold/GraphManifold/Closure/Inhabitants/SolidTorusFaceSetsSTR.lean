import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.SolidTorusRowsSTR
import DifferentialGeometry.Topology.Manifold.ClosedBall

/-!
# S-SOLIDTORUS4 (suffix `_STR`), G6 part 1: the faces of `∂M₂`

The model boundary of the ball piece is one component (the sphere), so the ball has exactly one
`ModelBoundaryFace` (`ballFace_STR`), whose image is `{u = κ}`; the cusp has the one internal face
with image `{h = -1/4}`. The residual faces of the (empty) slim family are therefore these two
(`res_cases_STR`) and `∂M₂ = {u = κ} ∪ {h = -1/4}` (`boundaryM2_eq_STR`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR

open GC.GraphManifold.Assembly.FC39P0.SolidTorusSTI GC.GraphManifold.Assembly.FC39P0

local instance carrierCharts_FaceSetsSTR : ChartedSpace (EuclideanHalfSpace 3) Wc.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) solidTorusSet.{0}
  exact inferInstance

local instance carrierSmooth_FaceSetsSTR : IsManifold (𝓡∂ 3) ∞ Wc.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ solidTorusSet.{0}
  exact inferInstance

local instance ballCharts_FaceSetsSTR : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_FaceSetsSTR : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-! ## The ball face -/

/-- A boundary point of the closed 3-cell. -/
def ballPoint_STR : ClosedCell 3 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp⟩

theorem ballPoint_boundary_STR : ballPoint_STR ∈ (𝓡∂ 3).boundary (ClosedCell 3) := by
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  change ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1
  simp

theorem ballBoundary_preconnected_STR : IsPreconnected ((𝓡∂ 3).boundary (ClosedCell 3)) := by
  rw [DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  have himg : (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ''
      {x : ClosedCell 3 | ‖x.val‖ = 1} = Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      have hy' : ‖y‖ = 1 := by simpa using hy
      exact ⟨⟨y, hy'.le⟩, hy', rfl⟩
  have hs := isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank
    (show 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) by simp)) 0 1
  rw [← himg] at hs
  exact (Topology.IsInducing.subtypeVal.isPreconnected_image).1 hs

/-- **The model boundary face of the ball**: the whole model boundary (one component). -/
def ballFace_STR : ModelBoundaryFace capPiece_STI :=
  ⟨(𝓡∂ 3).boundary (ClosedCell 3), ballPoint_STR, ballPoint_boundary_STR,
    (ballBoundary_preconnected_STR.connectedComponentIn ballPoint_boundary_STR).symm⟩

theorem ballFace_unique_STR (F : ModelBoundaryFace capPiece_STI) : F = ballFace_STR := by
  obtain ⟨K, x, hx, hK⟩ := F
  apply Subtype.ext
  change K = (𝓡∂ 3).boundary (ClosedCell 3)
  rw [hK]
  exact ballBoundary_preconnected_STR.connectedComponentIn hx

theorem ballFace_image_STR :
    capPiece_STI.map '' ballFace_STR.1 = {p | uW_STR p = 4 / 5} := by
  have h := pieceBoundary_capPiece_STI
  ext p
  have h1 : p ∈ pieceBoundary capPiece_STI ↔ ratioBall_STI p = 0 := by
    rw [h]
    exact Iff.rfl
  rw [ratioBall_eq_zero_iff_STI] at h1
  exact h1

/-! ## The cusp face -/

theorem cuspFace_image_STR :
    X135Radial.cuspPiece.map '' (X135Radial.radialCuspCores.internalModelFace 0).1 =
      {p | X135Radial.height p = -(1 / 4 : ℝ)} := by
  change X135Radial.cuspToCarrier '' range (X135Radial.cuspEnd true) = _
  rw [← range_comp]
  change range (fun t => X135Radial.cuspPiece.map (X135Radial.cuspEnd true t)) = _
  rw [X135Radial.cuspEnd_map_range true]
  rfl

/-! ## The residual faces -/

/-- The only index of the ball zero domains. -/
def ball0_STR : Fin ballZeroDomainsL_STR.count := ⟨0, Nat.one_pos⟩

local instance ballCountSubsingleton_STR : Subsingleton (Fin ballZeroDomainsL_STR.count) :=
  inferInstanceAs (Subsingleton (Fin 1))

/-- The neighbour face given by the ball. -/
def ballNb_STR : NeighbourFace ballZeroDomainsL_STR X135Radial.radialCuspCores :=
  .inl ⟨ball0_STR, ballFace_STR⟩

/-- The neighbour face given by the internal face of the cusp. -/
def cuspNb_STR : NeighbourFace ballZeroDomainsL_STR X135Radial.radialCuspCores :=
  .inr ⟨0, ⟨X135Radial.radialCuspCores.internalModelFace 0, rfl⟩⟩

theorem neighbour_cases_STR (F : NeighbourFace ballZeroDomainsL_STR X135Radial.radialCuspCores) :
    F = ballNb_STR ∨ F = cuspNb_STR := by
  cases F with
  | inl F =>
    obtain ⟨i, face⟩ := F
    have hi : i = ball0_STR := Subsingleton.elim _ _
    subst hi
    left
    rw [ballFace_unique_STR face]
    rfl
  | inr F =>
    obtain ⟨b, face, hface⟩ := F
    have hb : b = (0 : Fin 1) := Subsingleton.elim _ _
    subst hb
    subst hface
    right
    rfl

theorem neighbourSet_ball_STR : neighbourSet ballNb_STR = {p | uW_STR p = 4 / 5} :=
  ballFace_image_STR

theorem neighbourSet_cusp_STR :
    neighbourSet cuspNb_STR = {p | X135Radial.height p = -(1 / 4 : ℝ)} :=
  cuspFace_image_STR

theorem end_false_STR (e : slimPieces_STR.End) : False := e.1.1.elim0

/-- The residual face given by the ball. -/
def ballRes_STR : slimPieces_STR.ResidualFace :=
  .inl ⟨ballNb_STR, fun e => (end_false_STR e).elim⟩

/-- The residual face given by the internal face of the cusp. -/
def cuspRes_STR : slimPieces_STR.ResidualFace :=
  .inl ⟨cuspNb_STR, fun e => (end_false_STR e).elim⟩

theorem res_cases_STR (F : slimPieces_STR.ResidualFace) : F = ballRes_STR ∨ F = cuspRes_STR := by
  cases F with
  | inl F =>
    obtain ⟨G, hG⟩ := F
    rcases neighbour_cases_STR G with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  | inr e => exact (end_false_STR e.1).elim

theorem ballRes_ne_cuspRes_STR : ballRes_STR ≠ cuspRes_STR := by
  intro h
  have h1 : ballNb_STR = cuspNb_STR := by
    injection h with h2
    injection h2
  cases h1

theorem residualSet_ball_STR : slimPieces_STR.residualSet ballRes_STR = {p | uW_STR p = 4 / 5} :=
  neighbourSet_ball_STR

theorem residualSet_cusp_STR : slimPieces_STR.residualSet cuspRes_STR =
    {p | X135Radial.height p = -(1 / 4 : ℝ)} :=
  neighbourSet_cusp_STR

/-- **`∂M₂ = {u = κ} ∪ {h = -1/4}`**. -/
theorem boundaryM2_eq_STR : slimPieces_STR.boundaryM2 =
    {p | uW_STR p = 4 / 5} ∪ {p | X135Radial.height p = -(1 / 4 : ℝ)} := by
  unfold SlimPiecesV2.boundaryM2
  ext p
  constructor
  · intro hp
    obtain ⟨F, hF⟩ := mem_iUnion.1 hp
    rcases res_cases_STR F with rfl | rfl
    · rw [residualSet_ball_STR] at hF
      exact Or.inl hF
    · rw [residualSet_cusp_STR] at hF
      exact Or.inr hF
  · rintro (hp | hp)
    · exact mem_iUnion.2 ⟨ballRes_STR, by rw [residualSet_ball_STR]; exact hp⟩
    · exact mem_iUnion.2 ⟨cuspRes_STR, by rw [residualSet_cusp_STR]; exact hp⟩

end GC.GraphManifold.Assembly.FC39P0.SolidTorusSTR
