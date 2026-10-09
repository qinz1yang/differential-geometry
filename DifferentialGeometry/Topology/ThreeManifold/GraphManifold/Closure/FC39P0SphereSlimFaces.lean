import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlim
import DifferentialGeometry.Topology.Manifold.ScaledClosedBall
import DifferentialGeometry.Topology.PiecewiseLinear.BoundarySurfaceEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportTarget
import DifferentialGeometry.Topology.Manifold.HalfSpaceCenteredChart

/-!
# FC39 producer, packet P0 (gate 1): the faces of the S³ slim kind

Slim side of the seam–face data (task-47 draft §2, §7.6) for the S³ inhabitant
`sphereSlimPieces` (`FC39P0SphereSlim.lean`), stereographic convention (`r = ‖y‖`,
`q₀ = (r² − 4)/(r² + 4)`):

* the two actual ends (`sphereSlimEndEquiv : Bool ≃ End`); the ONE actual shared face
  `sphereSharedFace` (the end `0`, the sphere `r = 1/2`, `q₀ = −15/17`) and the ONE new end
  `sphereNewEnd` (the end `1`, `r = 1`, `q₀ = −3/5`); the seam index equivalences
  `sphereSharedSphereEquiv : Fin 1 ≃ {σ // shape σ = sphere}`, `sphereSharedTorusEquiv` (empty);
* the actual model faces: `slimEndFaceEquiv : Bool ≃ ModelBoundaryFace sphereSlimPiece`, the unique
  model face `innerBallFace` of `Z₋` and `outerBallFace` of `Z₊`;
* the residual faces of `∂M₂` (`sphereResidualEquiv : Bool ≃ ResidualFace`): `false` = the new slim
  end (`q₀ = −3/5`, function `q₀ + 3/5`, owner the slim piece), `true` = the unshared model face of
  `Z₊` (`q₀ = 3/5`, function `3/5 − q₀`, owner the zero index `1`); `∂M₂ = {q₀ = ±3/5}`;
* the two side parametrizations of the shared sphere, smooth embeddings of the standard sphere
  onto the two actual model faces with the SAME ambient map `z ↦ ambient(z/2)`:
  `slimSideParam z = (z, 0)` (slim piece) and `ballSideParam z = z` (model ball of `Z₋`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance ballChartsFaces_FC39P0c : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothFaces_FC39P0c : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

local instance boundaryNonempty_FC39P0c :
    Nonempty (Integral.DivergenceTheorem.WithBoundary.HasSmoothBoundary.boundaryH (𝓡∂ 3)) :=
  show Nonempty (EuclideanSpace ℝ (Fin 2)) from inferInstance

local instance boundaryCharts_FC39P0c {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :
    ChartedSpace (EuclideanSpace ℝ (Fin 2))
      (Integral.DivergenceTheorem.WithBoundary.BoundaryManifold (𝓡∂ 3) M) :=
  Integral.DivergenceTheorem.WithBoundary.BoundaryManifold.chartedSpace (I := 𝓡∂ 3)

local instance boundarySmooth_FC39P0c {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] :
    IsManifold (𝓡 2) ∞ (Integral.DivergenceTheorem.WithBoundary.BoundaryManifold (𝓡∂ 3) M) :=
  Integral.DivergenceTheorem.WithBoundary.BoundaryManifold.isManifold (I := 𝓡∂ 3)

/-! ## The two ends, the shared face and the new end -/

/-- The end `b` of the slim piece (`false = 0`: `r = 1/2`; `true = 1`: `r = 1`). -/
def sphereSlimEnd (b : Bool) : sphereSlimPieces.End :=
  ⟨((0 : Fin 1), b), trivial⟩

theorem sphereSlimEnd_surjective (e : sphereSlimPieces.End) : ∃ b, sphereSlimEnd b = e := by
  obtain ⟨⟨j, b⟩, hj⟩ := e
  exact ⟨b, Subtype.ext (Prod.ext (Subsingleton.elim (α := Fin 1) _ _) rfl)⟩

/-- **The actual ends of the S³ slim kind**: `Bool`. -/
def sphereSlimEndEquiv : Bool ≃ sphereSlimPieces.End :=
  Equiv.ofBijective sphereSlimEnd ⟨fun _ _ h => congrArg (fun e => e.1.2) h,
    sphereSlimEnd_surjective⟩

theorem sphereSlimPieces_endKind_false :
    sphereSlimPieces.endKind (sphereSlimEnd false) = some slimSharedNeighbour :=
  rfl

theorem sphereSlimPieces_endKind_true : sphereSlimPieces.endKind (sphereSlimEnd true) = none :=
  rfl

theorem sphereSlimEnd_set (b : Bool) :
    sphereSlimPieces.endSet (sphereSlimEnd b) = {x | sphereHeight x = slimEndHeight b} :=
  image_slimMap_end b

/-- **The actual shared face** of the S³ slim kind: the end `0` (the sphere `r = 1/2`). -/
def sphereSharedFace : ActualSharedFace sphereSlimPieces :=
  ⟨sphereSlimEnd false, rfl⟩

theorem eq_sphereSharedFace (σ : ActualSharedFace sphereSlimPieces) : σ = sphereSharedFace := by
  obtain ⟨e, he⟩ := σ
  obtain ⟨b, rfl⟩ := sphereSlimEnd_surjective e
  cases b
  · rfl
  · exact absurd he (by decide)

theorem sphereSharedFace_set :
    sphereSlimPieces.endSet sphereSharedFace.1 = {x | sphereHeight x = -15 / 17} :=
  sphereSlimEnd_set false

theorem sphereSharedFace_shape : sphereSlimPieces.endShape sphereSharedFace.1 = .sphere :=
  rfl

theorem sphereSharedFace_neighbour :
    sphereSlimPieces.endKind sphereSharedFace.1 = some slimSharedNeighbour :=
  rfl

/-- **The sphere-seam index of the S³ data**: one shared sphere. -/
def sphereSharedSphereEquiv :
    Fin 1 ≃ {σ : ActualSharedFace sphereSlimPieces // sphereSlimPieces.endShape σ.1 = .sphere} where
  toFun _ := ⟨sphereSharedFace, sphereSharedFace_shape⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv σ := Subtype.ext (eq_sphereSharedFace σ.1).symm

/-- **The torus-seam index of the S³ data**: no shared torus. -/
def sphereSharedTorusEquiv :
    Fin 0 ≃ {σ : ActualSharedFace sphereSlimPieces // sphereSlimPieces.endShape σ.1 = .torus} where
  toFun i := i.elim0
  invFun σ := absurd σ.2 (by rw [eq_sphereSharedFace σ.1]; exact fun h => FaceShape.noConfusion h)
  left_inv i := i.elim0
  right_inv σ := absurd σ.2 (by
    rw [eq_sphereSharedFace σ.1]
    exact fun h => FaceShape.noConfusion h)

/-- **The new end** of the S³ slim kind: the end `1` (the sphere `r = 1`, a face of `M₂`). -/
def sphereNewEnd : sphereSlimPieces.NewEnd :=
  ⟨sphereSlimEnd true, rfl⟩

theorem eq_sphereNewEnd (e : sphereSlimPieces.NewEnd) : e = sphereNewEnd := by
  obtain ⟨e, he⟩ := e
  obtain ⟨b, rfl⟩ := sphereSlimEnd_surjective e
  cases b
  · exact absurd he (Option.some_ne_none _)
  · rfl

theorem sphereNewEnd_set :
    sphereSlimPieces.endSet sphereNewEnd.1 = {x | sphereHeight x = -3 / 5} :=
  sphereSlimEnd_set true

/-! ## The actual model faces -/

theorem slimEndFace_injective : Injective slimEndFace := by
  intro b b' h
  have hm : (slimSpherePoint, iccEnd b) ∈ (slimEndFace b').1 := by
    rw [← h]
    exact ⟨slimSpherePoint, rfl⟩
  have h2 := mem_slimEndSet.1 hm
  cases b <;> cases b'
  · rfl
  · have h3 := congrArg Subtype.val h2
    norm_num [iccEnd] at h3
  · have h3 := congrArg Subtype.val h2
    norm_num [iccEnd] at h3
  · rfl

/-- **The two actual model faces of the slim piece**, numbered by the ends. -/
def slimEndFaceEquiv : Bool ≃ ModelBoundaryFace sphereSlimPiece :=
  Equiv.ofBijective slimEndFace ⟨slimEndFace_injective, slimEndFace_exhausted⟩

/-- A piece with preconnected model boundary has at most one actual model face. -/
theorem modelBoundaryFace_eq_of_isPreconnected {P : PieceEmbedding sphereW}
    (h : IsPreconnected ((𝓡∂ 3).boundary P.Piece)) (F G : ModelBoundaryFace P) : F = G := by
  obtain ⟨C, x, hx, rfl⟩ := F
  obtain ⟨D, y, hy, rfl⟩ := G
  apply Subtype.ext
  change connectedComponentIn _ x = connectedComponentIn _ y
  rw [h.connectedComponentIn hx, h.connectedComponentIn hy]

theorem eq_innerBallFace (F : ModelBoundaryFace sphereInnerBall) : F = innerBallFace :=
  modelBoundaryFace_eq_of_isPreconnected isPreconnected_innerBall_boundary F innerBallFace

theorem innerBallFace_set : innerBallFace.1 = (𝓡∂ 3).boundary sphereInnerBall.Piece :=
  rfl

theorem isPreconnected_outerBall_boundary :
    IsPreconnected ((𝓡∂ 3).boundary (cycleBallPiece true).Piece) := by
  have hS : PreconnectedSpace (Metric.sphere (0 : E3) 1) :=
    (isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)).toPreconnectedSpace
  have hR : IsPreconnected (range fun v : Metric.sphere (0 : E3) 1 =>
      (⟨v.val, (norm_eq_of_mem_sphere v).le⟩ : ClosedCell 3)) :=
    isPreconnected_range (continuous_subtype_val.subtype_mk _)
  have heq : (range fun v : Metric.sphere (0 : E3) 1 =>
      (⟨v.val, (norm_eq_of_mem_sphere v).le⟩ : ClosedCell 3)) =
      (𝓡∂ 3).boundary (cycleBallPiece true).Piece := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact closedCell_isBoundaryPoint_iff.2 (norm_eq_of_mem_sphere v)
    · intro hx
      exact ⟨⟨x.val, mem_sphere_zero_iff_norm.2 (closedCell_isBoundaryPoint_iff.1 hx)⟩, rfl⟩
  exact heq ▸ hR

theorem ballBoundaryPoint_mem_outer :
    ballBoundaryPoint ∈ (𝓡∂ 3).boundary (cycleBallPiece true).Piece :=
  closedCell_isBoundaryPoint_iff.2 (by simp [ballBoundaryPoint])

/-- **The model face of `Z₊`** (its whole boundary sphere). -/
def outerBallFace : ModelBoundaryFace (cycleBallPiece true) :=
  ⟨(𝓡∂ 3).boundary (cycleBallPiece true).Piece, ballBoundaryPoint, ballBoundaryPoint_mem_outer,
    (isPreconnected_outerBall_boundary.connectedComponentIn ballBoundaryPoint_mem_outer).symm⟩

theorem eq_outerBallFace (F : ModelBoundaryFace (cycleBallPiece true)) : F = outerBallFace :=
  modelBoundaryFace_eq_of_isPreconnected isPreconnected_outerBall_boundary F outerBallFace

theorem image_outerBallFace :
    (cycleBallPiece true).map '' outerBallFace.1 = {x | sphereHeight x = 3 / 5} := by
  change pieceBoundary (cycleBallPiece true) = _
  rw [pieceBoundary_outerBall]
  ext x
  simp only [mem_ofPred_eq]
  constructor <;> intro h <;> linarith

theorem image_innerBallFace :
    sphereInnerBall.map '' innerBallFace.1 = {x | sphereHeight x = -15 / 17} := by
  change pieceBoundary sphereInnerBall = _
  rw [pieceBoundary_innerBall]
  ext x
  simp only [mem_ofPred_eq]
  constructor <;> intro h <;> linarith

/-! ## The residual faces of `∂M₂` -/

/-- The unshared neighbour face: the model face of `Z₊` (zero index `1`). -/
def sphereZplusNeighbour : NeighbourFace sphereZeroDomains sphereCuspCores :=
  .inl ⟨(1 : Fin 2), outerBallFace⟩

theorem sphereZplus_unshared (e : sphereSlimPieces.End) :
    sphereSlimPieces.endKind e ≠ some sphereZplusNeighbour := by
  obtain ⟨b, rfl⟩ := sphereSlimEnd_surjective e
  cases b
  · intro h
    have h1 := Sum.inl_injective (Option.some_injective _ h)
    exact absurd (congrArg Sigma.fst h1) (by decide)
  · exact fun h => Option.some_ne_none _ h.symm

/-- **The residual faces of the S³ data**: `false` = the new slim end (`q₀ = −3/5`), `true` = the
model face of `Z₊` (`q₀ = 3/5`). -/
def sphereResidual : Bool → sphereSlimPieces.ResidualFace
  | false => .inr sphereNewEnd
  | true => .inl ⟨sphereZplusNeighbour, sphereZplus_unshared⟩

theorem sphereResidual_surjective (F : sphereSlimPieces.ResidualFace) :
    ∃ b, sphereResidual b = F := by
  rcases F with ⟨F, hF⟩ | e
  · rcases F with ⟨i, G⟩ | ⟨c, -⟩
    · fin_cases i
      · have hG : G = innerBallFace := eq_innerBallFace G
        rw [hG] at hF
        exact absurd rfl (hF (sphereSlimEnd false))
      · have hG : G = outerBallFace := eq_outerBallFace G
        subst hG
        exact ⟨true, rfl⟩
    · exact c.elim0
  · exact ⟨false, by rw [eq_sphereNewEnd e]; rfl⟩

theorem sphereResidual_injective : Injective sphereResidual := by
  intro b b' h
  cases b <;> cases b'
  · rfl
  · exact absurd h Sum.inr_ne_inl
  · exact absurd h Sum.inl_ne_inr
  · rfl

/-- **The residual faces of `∂M₂` of the S³ data**, numbered by `Bool`. -/
def sphereResidualEquiv : Bool ≃ sphereSlimPieces.ResidualFace :=
  Equiv.ofBijective sphereResidual ⟨sphereResidual_injective, sphereResidual_surjective⟩

/-- The height level of the residual face `b` (`−3/5` new slim end, `3/5` face of `Z₊`). -/
def sphereResidualHeight (b : Bool) : ℝ :=
  bif b then 3 / 5 else -3 / 5

theorem residualSet_sphereResidual (b : Bool) :
    sphereSlimPieces.residualSet (sphereResidual b) =
      {x | sphereHeight x = sphereResidualHeight b} := by
  cases b
  · exact sphereNewEnd_set
  · exact image_outerBallFace

theorem residualFn_sphereResidual_false :
    sphereSlimPieces.residualFn (sphereResidual false) = fun x => sphereHeight x + 3 / 5 :=
  rfl

theorem residualFn_sphereResidual_true :
    sphereSlimPieces.residualFn (sphereResidual true) = fun x => 3 / 5 - sphereHeight x :=
  rfl

theorem residualNear_sphereResidual_false :
    sphereSlimPieces.residualNear (sphereResidual false) = slimNear :=
  rfl

theorem residualNear_sphereResidual_true :
    sphereSlimPieces.residualNear (sphereResidual true) = ⊤ :=
  rfl

theorem residualOwner_sphereResidual_false :
    sphereSlimPieces.residualOwner (sphereResidual false) = .inr (.inr (0 : Fin 1)) :=
  rfl

theorem residualOwner_sphereResidual_true :
    sphereSlimPieces.residualOwner (sphereResidual true) = .inl (1 : Fin 2) :=
  rfl

/-- **`∂M₂` of the S³ data** is the union of the two levels `q₀ = ±3/5`. -/
theorem sphere_boundaryM2 :
    sphereSlimPieces.boundaryM2 = {x | sphereHeight x = -3 / 5} ∪ {x | sphereHeight x = 3 / 5} := by
  ext x
  simp only [SlimPiecesV2.boundaryM2, mem_iUnion, mem_union]
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨b, rfl⟩ := sphereResidual_surjective F
    rw [residualSet_sphereResidual] at hF
    cases b
    exacts [Or.inl hF, Or.inr hF]
  · rintro (h | h)
    · exact ⟨sphereResidual false, by rw [residualSet_sphereResidual]; exact h⟩
    · exact ⟨sphereResidual true, by rw [residualSet_sphereResidual]; exact h⟩

/-! ## The two side parametrizations of the shared sphere -/

/-- The boundary sphere of the closed unit ball. -/
def ballSphereMap (z : Metric.sphere (0 : E3) 1) : ClosedCell 3 :=
  ⟨z.val, (norm_eq_of_mem_sphere z).le⟩

/-- The boundary sphere of the closed unit ball is a smooth embedding (through the boundary
manifold of the ball of radius `1/2`, `closedBallBoundaryDiffeomorph`). -/
theorem isSmoothEmbedding_ballSphereMap :
    IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ ballSphereMap := by
  have hL : (0 : ℝ) < 1 / 2 := by norm_num
  let _ := closedBallChartedSpace hL
  let _ := closedBall_isManifold hL
  let D := (closedBallBoundaryDiffeomorph hL).symm
  have h1 := PiecewiseLinear.isSmoothEmbedding_coe_of_boundary_surface_openPartialHomeomorph
    (M := {x : E3 // ‖x‖ ≤ 1 / 2}) D.toHomeomorph.toOpenPartialHomeomorph rfl
    D.contMDiff.contMDiffOn D.symm.contMDiff.contMDiffOn
  have h2 := h1.diffeomorph_comp (closedBallUnitDiffeomorph hL)
  convert h2 using 1
  funext z
  apply Subtype.ext
  change z.val = (1 / 2 : ℝ)⁻¹ • ((1 / 2 : ℝ) • z.val)
  rw [smul_smul]
  norm_num

/-- **The `Z₋` side**: `z ↦ z` onto the boundary sphere of the model ball of `Z₋`. -/
def ballSideParam (z : ClosureSphere.{0}) : sphereInnerBall.Piece :=
  ballSphereMap z.down

theorem isSmoothEmbedding_ballSideParam : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ ballSideParam :=
  isSmoothEmbedding_ballSphereMap.comp_diffeomorph
    (uliftDiffeomorph (𝓡 2) (Metric.sphere (0 : E3) 1)).symm

theorem range_ballSideParam : range ballSideParam = innerBallFace.1 := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact closedCell_isBoundaryPoint_iff.2 (norm_eq_of_mem_sphere z.down)
  · intro hx
    have h1 : ‖x.val‖ = 1 := closedCell_isBoundaryPoint_iff.1 hx
    exact ⟨ULift.up ⟨x.val, mem_sphere_zero_iff_norm.2 h1⟩, rfl⟩

theorem ballSideParam_map (z : ClosureSphere.{0}) :
    sphereInnerBall.map (ballSideParam z) = cycleBallAmbient false ((1 / 2 : ℝ) • (z.down : E3)) :=
  sphereInnerBall_apply _

/-- **The slim side**: `z ↦ (z, 0)` onto the end sphere `S² × {0}` of the slim piece. -/
def slimSideParam (z : ClosureSphere.{0}) : sphereSlimPiece.Piece :=
  (z, iccEnd false)

theorem isSmoothEmbedding_slimSideParam : IsSmoothEmbedding (𝓡 2) (𝓡∂ 3) ∞ slimSideParam := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hb : (𝓡∂ 1).IsBoundaryPoint (iccEnd false : Icc (0 : ℝ) 1) := by
    change (iccEnd false : Icc (0 : ℝ) 1) ∈ (𝓡∂ 1).boundary (Icc (0 : ℝ) 1)
    rw [boundary_Icc]
    left
    exact Subtype.ext (by simp [iccEnd])
  have h : IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (fun z : ClosureSphere.{0} => (z, (iccEnd false : Icc (0 : ℝ) 1))) :=
    @isSmoothEmbedding_prodMk_boundary_point 0 (Icc (0 : ℝ) 1) _
      (inferInstance : ChartedSpace (EuclideanHalfSpace 1) (Icc (0 : ℝ) 1))
      (inferInstance : IsManifold (𝓡∂ 1) ∞ (Icc (0 : ℝ) 1)) _ _ ClosureSphere.{0} _ _ _ _ _
      (𝓡 2) _ (iccEnd false) hb
  exact DifferentialGeometry.Manifold.isSmoothEmbedding_chartedSpaceTransHomeomorph_target
    (N := ClosureSphere.{0} × Icc (0 : ℝ) 1) (f := fun z => (z, iccEnd false))
    ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
    DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model (𝓡 2) h

theorem range_slimSideParam : range slimSideParam = (slimEndFace false).1 :=
  rfl

theorem slimSideParam_map (z : ClosureSphere.{0}) :
    sphereSlimPiece.map (slimSideParam z) =
      cycleBallAmbient false ((1 / 2 : ℝ) • (z.down : E3)) := by
  change cycleBallAmbient false (slimRadial (z, iccEnd false)) = _
  rw [slimRadial_apply]
  norm_num [iccEnd]

/-- **The common inclusion of the shared sphere**: the two side parametrizations have the same
ambient map. -/
theorem slimSideParam_map_eq_ballSideParam_map (z : ClosureSphere.{0}) :
    sphereSlimPiece.map (slimSideParam z) = sphereInnerBall.map (ballSideParam z) := by
  rw [slimSideParam_map, ballSideParam_map]

/-- The common ambient image of the two side parametrizations is the shared face. -/
theorem range_sideParam_map :
    (range fun z => sphereSlimPiece.map (slimSideParam z)) =
      sphereSlimPieces.endSet sphereSharedFace.1 := by
  change _ = sphereSlimPiece.map '' slimEndSet false
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(z, iccEnd false), ⟨z, rfl⟩, rfl⟩
  · rintro ⟨p, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, rfl⟩

end GC.GraphManifold.Assembly.FC39P0
