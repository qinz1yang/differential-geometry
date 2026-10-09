import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimLabels
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Faces

/-!
# FC39 producer, packet P0 (gate 1): the shared sphere seam of the S³ data

The ONE sphere seam of the common S³ configuration (lead decision T49-1), at the shared face
`r = 1/2` of the slim piece and `Z₋` (stereographic convention, `r = ‖y‖`):

* `sphereSharedSeam : SphereSeam sphereW`, collar `(z, s) ↦ ambient((1/2 + s/40) z)` on
  `S² × (−1, 1)` (`sharedCollarMap`; a partial diffeomorphism by
  `exists_partialDiffeomorph_of_injOn`);
* its zero slice is the common image of the two side parametrizations of
  `FC39P0SphereSlimFaces.lean` (`sphereSharedSeam_zero_slim`, `sphereSharedSeam_zero_ball`), hence
  the actual shared face and the neighbour face (`range_sphereSharedSeam_zero`,
  `range_sphereSharedSeam_zero_neighbour`);
* the sides: `s ≤ 0` lies in `Z₋`, `s ≥ 0` in the slim piece (`sphereSharedSeam_neg_mem`,
  `sphereSharedSeam_pos_mem`): side `true` = `Z₋`, side `false` = the slim piece;
* the prescribed safe neighbourhood `sphereSharedNear = {q₀ < −4/5}` of the shared face: it
  contains the face and the closed collar, and its closure stays in `{q₀ ≤ −4/5}`, hence off the
  edge piece (`sphereSharedNear_off_edge`, the edge piece lies in `{|q₀| ≤ 3/5}`) and off the
  external collars (no ports); the safe-neighbourhood family of the shared faces
  (`sphereSharedSafeFamily`) with the slim-side clauses of `SharedSafe`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-! ## The collar map -/

/-- The collar radius `1/2 + s/40` (in `(19/40, 21/40)` on `(−1, 1)`). -/
def sharedCollarRadius (s : ℝ) : ℝ :=
  1 / 2 + 1 / 40 * s

/-- The seam collar `(z, s) ↦ ambient((1/2 + s/40) z)`. -/
def sharedCollarMap (p : ClosureSphere.{0} × ℝ) : sphereW.Carrier :=
  cycleBallAmbient false (sharedCollarRadius p.2 • (p.1.down : E3))

theorem sharedCollarRadius_pos {s : ℝ} (hs : -1 < s) : 0 < sharedCollarRadius s := by
  unfold sharedCollarRadius
  linarith

theorem norm_sharedCollar {z : S2} {s : ℝ} (hs : -1 < s) :
    ‖sharedCollarRadius s • (z : E3)‖ = sharedCollarRadius s := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sharedCollarRadius_pos hs),
    norm_eq_of_mem_sphere, mul_one]

theorem sphereHeight_sharedCollarMap {p : ClosureSphere.{0} × ℝ} (hp : -1 < p.2) :
    sphereHeight (sharedCollarMap p) =
      (sharedCollarRadius p.2 ^ 2 - 4) / (sharedCollarRadius p.2 ^ 2 + 4) := by
  rw [sharedCollarMap, sphereHeight_ambient_false, norm_sharedCollar hp]

theorem isLocalDiffeomorphOn_sharedCollarMap :
    IsLocalDiffeomorphOn sphereSignedCollarModel sphereW.model ∞ sharedCollarMap
      sphereSignedCollarSource := by
  rintro ⟨p, hp⟩
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (S2 × ℝ) (S2 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) S2 ∞).prodCongr (pushAffine (1 / 2) (1 / 40) (by norm_num))
  have hD : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      PieceEmbedding.sphereRealDown p :=
    PieceEmbedding.sphereRealDown.isLocalDiffeomorph p
  have hR := R.isLocalDiffeomorph (PieceEmbedding.sphereRealDown p)
  have hpos : 0 < (R (PieceEmbedding.sphereRealDown p)).2 := sharedCollarRadius_pos hs.1
  have hg := isLocalDiffeomorphAt_chart_sphere_smul (n := 2) (cycleBallAmbient false)
    (R (PieceEmbedding.sphereRealDown p)) hpos (by rw [cycleBallAmbient_source]; exact mem_univ _)
  exact (hD.comp _ _ hR).comp _ _ hg

theorem injOn_sharedCollarMap : InjOn sharedCollarMap sphereSignedCollarSource := by
  rintro p hp p' hp' h
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  have hs' : p'.2 ∈ Ioo (-1 : ℝ) 1 := hp'.2
  have hv := (cycleBallAmbient false).injOn (by rw [cycleBallAmbient_source]; exact mem_univ _)
    (by rw [cycleBallAmbient_source]; exact mem_univ _) h
  have hn := congrArg norm hv
  rw [norm_sharedCollar hs.1, norm_sharedCollar hs'.1] at hn
  have h22 : p.2 = p'.2 := by
    unfold sharedCollarRadius at hn
    linarith
  have hz : (p.1.down : E3) = p'.1.down := by
    rw [← hn] at hv
    exact smul_right_injective _ (sharedCollarRadius_pos hs.1).ne' hv
  exact Prod.ext (ULift.ext (Subtype.ext hz)) h22

theorem exists_sharedCollar :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel sphereW.model (ClosureSphere.{0} × ℝ)
      sphereW.Carrier ∞,
      d.source = sphereSignedCollarSource ∧ d.target = sharedCollarMap '' sphereSignedCollarSource ∧
        (d : ClosureSphere.{0} × ℝ → sphereW.Carrier) = sharedCollarMap := by
  have : Nonempty (ClosureSphere.{0} × ℝ) := ⟨(slimSpherePoint, 0)⟩
  exact exists_partialDiffeomorph_of_injOn (isOpen_univ.prod isOpen_Ioo)
    isLocalDiffeomorphOn_sharedCollarMap injOn_sharedCollarMap

/-- **The shared sphere seam of the S³ data**: the collar `(z, s) ↦ ambient((1/2 + s/40) z)`. -/
def sphereSharedSeam : SphereSeam sphereW where
  collar := exists_sharedCollar.choose
  source_eq := exists_sharedCollar.choose_spec.1
  target_interior _ _ := BoundarylessManifold.isInteriorPoint

theorem sphereSharedSeam_apply (p : ClosureSphere.{0} × ℝ) :
    sphereSharedSeam.collar p = sharedCollarMap p :=
  congrFun exists_sharedCollar.choose_spec.2.2 p

theorem sphereSharedSeam_target :
    sphereSharedSeam.collar.target = sharedCollarMap '' sphereSignedCollarSource :=
  exists_sharedCollar.choose_spec.2.1

/-! ## The zero slice is the shared face -/

theorem sphereSharedSeam_zero_slim (z : ClosureSphere.{0}) :
    sphereSharedSeam.collar (z, 0) = sphereSlimPiece.map (slimSideParam z) := by
  rw [sphereSharedSeam_apply, slimSideParam_map, sharedCollarMap, sharedCollarRadius]
  norm_num

theorem sphereSharedSeam_zero_ball (z : ClosureSphere.{0}) :
    sphereSharedSeam.collar (z, 0) = sphereInnerBall.map (ballSideParam z) := by
  rw [sphereSharedSeam_zero_slim, slimSideParam_map_eq_ballSideParam_map]

/-- **The zero slice of the seam is the actual shared face** (`sphere_slim` for the S³ data). -/
theorem range_sphereSharedSeam_zero :
    (range fun z => sphereSharedSeam.collar (z, 0)) =
      sphereSlimPieces.endSet sphereSharedFace.1 := by
  rw [← range_sideParam_map]
  simp only [sphereSharedSeam_zero_slim]

/-- **The zero slice of the seam is the neighbour face** (`sphere_neighbour` for the S³ data). -/
theorem range_sphereSharedSeam_zero_neighbour :
    (range fun z => sphereSharedSeam.collar (z, 0)) = neighbourSet slimSharedNeighbour := by
  rw [range_sphereSharedSeam_zero]
  exact sphereSlim_shared_eq _ _ rfl

/-! ## The two sides -/

/-- **Side `true` (`s ≤ 0`) lies in `Z₋`.** -/
theorem sphereSharedSeam_neg_mem (z : ClosureSphere.{0}) {s : ℝ} (hs : s ≤ 0) (hs' : -1 < s) :
    sphereSharedSeam.collar (z, s) ∈ range sphereInnerBall.map := by
  rw [range_innerBall, sphereSharedSeam_apply, mem_ofPred_eq,
    sphereHeight_sharedCollarMap (p := (z, s)) hs']
  have hr := sharedCollarRadius_pos hs'
  have hle : sharedCollarRadius s ^ 2 ≤ 1 / 4 := by
    unfold sharedCollarRadius at hr ⊢
    nlinarith
  have := (stereoHeight_le_iff (sq_nonneg (sharedCollarRadius s)) (by norm_num :
    (-15 / 17 : ℝ) < 1)).2 (by norm_num; linarith)
  linarith

/-- **Side `false` (`s ≥ 0`) lies in the slim piece.** -/
theorem sphereSharedSeam_pos_mem (z : ClosureSphere.{0}) {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1) :
    sphereSharedSeam.collar (z, s) ∈ range sphereSlimPiece.map := by
  change _ ∈ range slimMap
  rw [range_slimMap, sphereSharedSeam_apply, mem_ofPred_eq, sharedCollarMap,
    sphereHeight_ambient_false, half_le_norm_iff_height, norm_le_one_iff_height,
    norm_sharedCollar (by linarith : (-1 : ℝ) < s)]
  unfold sharedCollarRadius
  constructor <;> linarith

/-! ## The safe neighbourhood of the shared face -/

/-- **The prescribed safe neighbourhood** `{q₀ < −4/5}` of the shared face. -/
def sphereSharedNear : TopologicalSpace.Opens sphereW.Carrier :=
  ⟨{x | sphereHeight x < -4 / 5}, isOpen_lt contMDiff_sphereHeight.continuous continuous_const⟩

theorem sphereSharedFace_subset_near :
    sphereSlimPieces.endSet sphereSharedFace.1 ⊆ sphereSharedNear := by
  rw [sphereSharedFace_set]
  intro x hx
  change sphereHeight x = -15 / 17 at hx
  change sphereHeight x < -4 / 5
  rw [hx]
  norm_num

theorem closure_sphereSharedNear :
    closure (sphereSharedNear : Set sphereW.Carrier) ⊆ {x | sphereHeight x ≤ -4 / 5} :=
  closure_minimal (fun x hx => show sphereHeight x ≤ -4 / 5 from le_of_lt hx)
    (isClosed_le contMDiff_sphereHeight.continuous continuous_const)

theorem sphereHeight_le_of_mem_sharedSeam {x : sphereW.Carrier}
    (hx : x ∈ sphereSharedSeam.collar.target) : sphereHeight x ≤ -6 / 7 := by
  rw [sphereSharedSeam_target] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  rw [sphereHeight_sharedCollarMap hs.1]
  have hr := sharedCollarRadius_pos hs.1
  have hle : sharedCollarRadius p.2 ^ 2 ≤ 4 / 13 := by
    unfold sharedCollarRadius at hr ⊢
    nlinarith [hs.2]
  exact (stereoHeight_le_iff (sq_nonneg _) (by norm_num)).2 (by norm_num; linarith)

/-- **The closed seam collar lies in the safe neighbourhood** (`sphere_closure` for the S³
data). -/
theorem closure_sphereSharedSeam_target :
    closure sphereSharedSeam.collar.target ⊆ (sphereSharedNear : Set sphereW.Carrier) := by
  have hcl : closure sphereSharedSeam.collar.target ⊆ {x | sphereHeight x ≤ -6 / 7} :=
    closure_minimal (fun _ hx => sphereHeight_le_of_mem_sharedSeam hx)
      (isClosed_le contMDiff_sphereHeight.continuous continuous_const)
  intro x hx
  have h := hcl hx
  change sphereHeight x ≤ -6 / 7 at h
  change sphereHeight x < -4 / 5
  linarith

/-- The edge piece lies in the band `−3/5 ≤ q₀ ≤ 3/5` (`1 ≤ r ≤ 4`). -/
theorem sphereHeight_edgePiece {x : sphereW.Carrier} (hx : x ∈ sphereEdgeBundle.edgePiece) :
    -3 / 5 ≤ sphereHeight x ∧ sphereHeight x ≤ 3 / 5 := by
  rw [sphere_edgePiece_eq] at hx
  obtain ⟨b, ⟨w, t⟩, rfl⟩ := mem_iUnion.1 hx
  have hp := handle_box w t
  rw [cycleS3Handle_map, sphereHeight_handleChart b hp]
  dsimp only
  have hs := handleRadiusParam_mem_Icc b t.2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hlo := cycleHandleRadius_strictMono.monotoneOn h0 hs hs.1
  have hhi := cycleHandleRadius_strictMono.monotoneOn hs h1' hs.2
  have e0 : cycleHandleRadius 0 = 1 := by
    rw [cycleHandleRadius_inner (by norm_num)]
    norm_num
  have e1 : cycleHandleRadius 1 = 4 := by
    rw [cycleHandleRadius_outer (by norm_num)]
    norm_num
  rw [e0] at hlo
  rw [e1] at hhi
  constructor
  · rw [le_stereoHeight_iff (sq_nonneg _) (by norm_num),
      show (4 * (1 + -3 / 5) / (1 - -3 / 5) : ℝ) = 1 by norm_num]
    nlinarith
  · rw [stereoHeight_le_iff (sq_nonneg _) (by norm_num),
      show (4 * (1 + 3 / 5) / (1 - 3 / 5) : ℝ) = 16 by norm_num]
    nlinarith

/-- **The closed safe neighbourhood avoids the edge piece** (`off_edge` for the S³ data). -/
theorem sphereSharedNear_off_edge :
    Disjoint (closure (sphereSharedNear : Set sphereW.Carrier)) sphereEdgeBundle.edgePiece := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 := closure_sphereSharedNear hx
  have h2 := (sphereHeight_edgePiece hx').1
  change sphereHeight x ≤ -4 / 5 at h1
  linarith

/-- The safe neighbourhoods of the actual shared faces of the S³ data (one face). -/
def sphereSharedSafeFamily (_ : ActualSharedFace sphereSlimPieces) :
    TopologicalSpace.Opens sphereW.Carrier :=
  sphereSharedNear

/-- `face_subset` of `SharedSafe` for the S³ data. -/
theorem sphereSharedSafe_face_subset (σ : ActualSharedFace sphereSlimPieces) :
    sphereSlimPieces.endSet σ.1 ⊆ sphereSharedSafeFamily σ := by
  rw [eq_sphereSharedFace σ]
  exact sphereSharedFace_subset_near

/-- `closure_disjoint` of `SharedSafe` for the S³ data (vacuous: one shared face). -/
theorem sphereSharedSafe_closure_disjoint :
    Pairwise fun σ τ : ActualSharedFace sphereSlimPieces =>
      Disjoint (closure (sphereSharedSafeFamily σ : Set sphereW.Carrier))
        (closure (sphereSharedSafeFamily τ : Set sphereW.Carrier)) := by
  intro σ τ h
  exact absurd ((eq_sphereSharedFace σ).trans (eq_sphereSharedFace τ).symm) h

/-- `off_edge` of `SharedSafe` for the S³ data. -/
theorem sphereSharedSafe_off_edge (σ : ActualSharedFace sphereSlimPieces) :
    Disjoint (closure (sphereSharedSafeFamily σ : Set sphereW.Carrier))
      sphereEdgeBundle.edgePiece :=
  sphereSharedNear_off_edge

end GC.GraphManifold.Assembly.FC39P0
