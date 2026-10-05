import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointJunctions

/-!
# FC39 producer, packet P0 (gate 1): the layers of the one S³ configuration

The certificate layers (`FC39P0Layers.lean`) that the joint links of §2 (`FC39P0Faces.lean`) are
stated against, for the S³ data:

* `sphereVertexLayer` — three vertices in the order `Z₋, S, Z₊` (vertex `k` is the row vertex of
  `sphereRowIndex k`: `0 ↦ Z₋ = .inl 0`, `1 ↦ S = .inr (.inr 0)`, `2 ↦ Z₊ = .inl 1`);
* `spherePortLayer` — no ports (closed `S³`);
* `sphereSeamLayer` — one sphere seam, the shared sphere `r = 1/2` (`sphereSharedSeam`), side
  `true` (`s ≤ 0`) the vertex `Z₋`, side `false` (`s ≥ 0`) the vertex `S`; no torus seam;
* `sphereFaceEquiv : Fin 4 ≃ Σ v, ModelBoundaryFace (vertex v).piece` — the face catalogue:
  `0 ↦ (Z₋, its boundary sphere)`, `1 ↦ (S, end r = 1/2)`, `2 ↦ (S, end r = 1)`,
  `3 ↦ (Z₊, its boundary sphere)`;
* `sphereFaceLayer` — the four faces (the images of the catalogue), kinds `sphereSeam 0 true`,
  `sphereSeam 0 false`, `partitioned`, `partitioned`, models: the level spheres
  `{q₀ = −15/17, −15/17, −3/5, 3/5}` are homeomorphic to `S²` (`sphereLevelHomeomorphJ`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## Vertices -/

/-- The row index of the vertex `k` (order `Z₋, S, Z₊`). -/
def sphereRowIndexFun : Fin 3 → sphereSlimPieces.RowIndex :=
  ![.inl (0 : Fin 2), .inr (.inr (0 : Fin 1)), .inl (1 : Fin 2)]

/-- The vertex number of a row index. -/
def sphereRowIndexInv : sphereSlimPieces.RowIndex → Fin 3
  | .inl i => if (i : ℕ) = 0 then 0 else 2
  | .inr (.inl b) => b.elim0
  | .inr (.inr _) => 1

/-- **The vertex numbering of the S³ data**: `Fin 3 ≃` the row indices (`Z₋, S, Z₊`). -/
def sphereRowIndex : Fin 3 ≃ sphereSlimPieces.RowIndex where
  toFun := sphereRowIndexFun
  invFun := sphereRowIndexInv
  left_inv k := by fin_cases k <;> rfl
  right_inv a := by
    rcases a with ⟨i, hi⟩ | b | ⟨j, hj⟩
    · change i < 2 at hi
      interval_cases i <;> rfl
    · exact b.elim0
    · change j < 1 at hj
      interval_cases j
      rfl

/-- The row vertex of the S³ rows (the same rule as `FC39RowsV2.rowVertex`). -/
def sphereRowVertex : sphereSlimPieces.RowIndex → Vertex sphereW
  | .inl i =>
    match sphereZeroDomains.model i with
    | .inl m => .zero (sphereZeroDomains.piece i) m
    | .inr Cz => .closedZero Cz.1
  | .inr (.inl b) => .cuspCore (sphereCuspCores.piece b) (sphereCuspCores.product b)
  | .inr (.inr j) => .slim (sphereSlimPieces.piece j) (sphereSlimPieces.model j)

/-- **The vertex layer of the S³ data** (order `Z₋, S, Z₊`). -/
def sphereVertexLayer : VertexLayer sphereW where
  vertexCount := 3
  vertex k := sphereRowVertex (sphereRowIndex k)

theorem sphereVertexLayer_piece_zero :
    (sphereVertexLayer.vertex (0 : Fin 3)).piece = sphereInnerBall :=
  rfl

theorem sphereVertexLayer_piece_one :
    (sphereVertexLayer.vertex (1 : Fin 3)).piece = sphereSlimPiece :=
  rfl

theorem sphereVertexLayer_piece_two :
    (sphereVertexLayer.vertex (2 : Fin 3)).piece = cycleBallPiece true :=
  rfl

/-! ## Ports and seams -/

/-- **The port layer of the S³ data** (no ports). -/
def spherePortLayer : PortLayer sphereW (BoundaryTori.empty sphereW) sphereVertexLayer where
  external_exhausted := sphereCuspCores.ports
  externalOwner i := i.elim0
  external_owned i := i.elim0

/-- **The seam layer of the S³ data**: one sphere seam `r = 1/2` between `Z₋` (side `true`) and `S`
(side `false`); no torus seam. -/
def sphereSeamLayer : SeamLayer sphereW sphereVertexLayer sphereCircleRegion where
  torusSeamCount := 0
  torusSeam c := c.elim0
  torusSide c := c.elim0
  torusSide_neg c := c.elim0
  torusSide_pos c := c.elim0
  torusSeam_disjoint c := c.elim0
  sphereSeamCount := 1
  sphereSeam _ := sphereSharedSeam
  sphereSide _ b := (bif b then (0 : Fin 3) else (1 : Fin 3) : Fin 3)
  sphereSide_neg _ z _ hs hs' := sphereSharedSeam_neg_mem z hs hs'
  sphereSide_pos _ z _ hs hs' := sphereSharedSeam_pos_mem z hs hs'
  sphereSeam_disjoint c d h := absurd (Subsingleton.elim c d) h
  sphere_torus_seam_disjoint _ d := d.elim0

/-! ## The face catalogue -/

/-- The face catalogue: `0 ↦ (Z₋, ∂)`, `1 ↦ (S, r = 1/2)`, `2 ↦ (S, r = 1)`, `3 ↦ (Z₊, ∂)`. -/
def sphereFaceFun : Fin 4 → Σ v : Fin 3, ModelBoundaryFace (sphereVertexLayer.vertex v).piece :=
  ![⟨0, innerBallFace⟩, ⟨1, slimEndFace false⟩, ⟨1, slimEndFace true⟩, ⟨2, outerBallFace⟩]

theorem sphereFaceFun_bijective : Bijective sphereFaceFun := by
  constructor
  · intro f f' h
    fin_cases f <;> fin_cases f'
    all_goals first
      | rfl
      | exact absurd (congrArg Sigma.fst h) (by decide)
      | (exfalso
         have h2 := eq_of_heq (Sigma.mk.inj_iff.1 h).2
         exact absurd (slimEndFace_injective h2) (by decide))
  · rintro ⟨v, F⟩
    fin_cases v
    · have hF : F = innerBallFace := eq_innerBallFace F
      subst hF
      exact ⟨0, rfl⟩
    · obtain ⟨b, hb⟩ := slimEndFace_exhausted F
      subst hb
      cases b
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · have hF : F = outerBallFace := eq_outerBallFace F
      subst hF
      exact ⟨3, rfl⟩

/-- **The face catalogue of the S³ data** `Fin 4 ≃ Σ v, ModelBoundaryFace (vertex v).piece`. -/
def sphereFaceEquiv : Fin 4 ≃ Σ v : Fin 3, ModelBoundaryFace (sphereVertexLayer.vertex v).piece :=
  Equiv.ofBijective sphereFaceFun sphereFaceFun_bijective

theorem sphereFaceEquiv_apply (f : Fin 4) : sphereFaceEquiv f = sphereFaceFun f :=
  rfl

/-! ## The face sets -/

/-- The ambient face of a catalogue entry. -/
def sphereFaceSet (f : Fin 4) : Set sphereW.Carrier :=
  (sphereVertexLayer.vertex (sphereFaceFun f).1).piece.map '' (sphereFaceFun f).2.1

/-- The height level of a face. -/
def sphereFaceHeight : Fin 4 → ℝ
  | 0 => -15 / 17
  | 1 => -15 / 17
  | 2 => -3 / 5
  | 3 => 3 / 5

/-- The stereographic radius of a face. -/
def sphereFaceRadius : Fin 4 → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | 2 => 1
  | 3 => 4

theorem slimEndFace_image (b : Bool) :
    sphereSlimPiece.map '' (slimEndFace b).1 = {x | sphereHeight x = slimEndHeight b} := by
  have h := sphereSlimEnd_set b
  rw [← h]
  change sphereSlimPiece.map '' slimEndSet b = sphereSlimPiece.map '' slimModelEnd sphereSlimModel b
  rw [slimModelEnd_eq]

theorem sphereFaceSet_eq (f : Fin 4) :
    sphereFaceSet f = {x | sphereHeight x = sphereFaceHeight f} := by
  fin_cases f
  · exact image_innerBallFace
  · refine (slimEndFace_image false).trans ?_
    simp [slimEndHeight, sphereFaceHeight]
  · refine (slimEndFace_image true).trans ?_
    simp [slimEndHeight, sphereFaceHeight]
  · exact image_outerBallFace

theorem sphereFaceRadius_pos (f : Fin 4) : 0 < sphereFaceRadius f := by
  fin_cases f <;> simp [sphereFaceRadius]

theorem circHeight_sphereFaceRadius (f : Fin 4) :
    circHeight (sphereFaceRadius f) = sphereFaceHeight f := by
  fin_cases f <;> simp [sphereFaceRadius, sphereFaceHeight, circHeight] <;> norm_num

/-! ## The level spheres are spheres -/

/-- The level sphere of radius `R` in the stereographic chart. -/
def sphereLevelMapJ (R : ℝ) (θ : Metric.sphere (0 : E3) 1) : sphereW.Carrier :=
  cycleBallAmbient false (R • (θ : E3))

theorem continuous_sphereLevelMapJ (R : ℝ) : Continuous (sphereLevelMapJ R) :=
  continuous_ambient_false.comp (continuous_subtype_val.const_smul R)

theorem injective_sphereLevelMapJ {R : ℝ} (hR : 0 < R) : Injective (sphereLevelMapJ R) := by
  intro θ θ' h
  exact Subtype.ext (smul_right_injective E3 hR.ne' (ambient_injective_JOINT h))

theorem stereoHeight_injective_JOINT {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : (a - 4) / (a + 4) = (b - 4) / (b + 4)) : a = b := by
  rw [div_eq_div_iff (by linarith) (by linarith)] at h
  linarith

theorem range_sphereLevelMapJ {R : ℝ} (hR : 0 < R) :
    range (sphereLevelMapJ R) = {x | sphereHeight x = circHeight R} := by
  ext x
  constructor
  · rintro ⟨θ, rfl⟩
    change sphereHeight (cycleBallAmbient false (R • (θ : E3))) = circHeight R
    rw [sphereHeight_ambient_false, norm_smul, norm_eq_of_mem_sphere, mul_one,
      Real.norm_of_nonneg hR.le]
    rfl
  · intro hx
    change sphereHeight x = circHeight R at hx
    have hlt : sphereHeight x < 1 := by
      rw [hx, circHeight, div_lt_one (by positivity)]
      linarith
    obtain ⟨y, rfl, hy⟩ := exists_ambient_of_height_lt hlt
    rw [hx] at hy
    have h2 : ‖y‖ ^ 2 = R ^ 2 :=
      (stereoHeight_injective_JOINT (sq_nonneg _) (sq_nonneg _) hy).symm
    have hn : ‖y‖ = R := (pow_left_inj₀ (norm_nonneg y) hR.le two_ne_zero).1 h2
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hn
      exact hR.ne' hn.symm
    refine ⟨sphereDirection southPole y, ?_⟩
    change cycleBallAmbient false (R • (sphereDirection southPole y : E3)) = _
    rw [← hn, norm_smul_sphereDirection southPole hy0]

/-- **A level sphere `{q₀ = circHeight R}` is homeomorphic to `S²`.** -/
def sphereLevelHomeomorphJ {R : ℝ} (hR : 0 < R) {A : Set sphereW.Carrier}
    (hA : A = {x | sphereHeight x = circHeight R}) :
    A ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  (Homeomorph.setCongr (hA.trans (range_sphereLevelMapJ hR).symm)).trans
    ((continuous_sphereLevelMapJ R).isClosedEmbedding
      (injective_sphereLevelMapJ hR)).isEmbedding.toHomeomorph.symm

/-! ## The face layer -/

/-- The kinds of the four faces. -/
def sphereFaceKind : Fin 4 → FaceKind 0 0 1
  | 0 => .sphereSeam 0 true
  | 1 => .sphereSeam 0 false
  | 2 => .partitioned
  | 3 => .partitioned

/-- Generic: the faces of a catalogue owned by a vertex exhaust its model boundary image. -/
theorem faceEquiv_exhausted_JOINT {V : VertexLayer sphereW} {m : ℕ}
    (e : Fin m ≃ Σ v : Fin V.vertexCount, ModelBoundaryFace (V.vertex v).piece)
    (k : Fin V.vertexCount) :
    (⋃ (f : Fin m) (_ : (e f).1 = k), (V.vertex (e f).1).piece.map '' (e f).2.1) =
      (V.vertex k).boundaryImage := by
  apply Subset.antisymm
  · refine iUnion₂_subset fun f hf => ?_
    have key : ∀ p : Σ v : Fin V.vertexCount, ModelBoundaryFace (V.vertex v).piece, p.1 = k →
        (V.vertex p.1).piece.map '' p.2.1 ⊆ (V.vertex k).boundaryImage := by
      rintro ⟨v, F⟩ hv
      dsimp only at hv
      subst hv
      exact image_mono F.subset
    exact key (e f) hf
  · rintro _ ⟨q, hq, rfl⟩
    refine mem_iUnion₂.2 ⟨e.symm ⟨k, ActualComponent.of hq⟩, by rw [Equiv.apply_symm_apply], ?_⟩
    rw [Equiv.apply_symm_apply]
    exact ⟨q, mem_connectedComponentIn hq, rfl⟩

theorem disjoint_sphereFaceSet {f f' : Fin 4} (h : sphereFaceHeight f ≠ sphereFaceHeight f') :
    Disjoint (sphereFaceSet f) (sphereFaceSet f') := by
  rw [sphereFaceSet_eq, sphereFaceSet_eq, Set.disjoint_left]
  intro x hx hx'
  exact h ((show sphereHeight x = sphereFaceHeight f from hx).symm.trans hx')

/-- **The face layer of the S³ data**: the four faces of the catalogue. -/
def sphereFaceLayer :
    FaceLayer sphereW (BoundaryTori.empty sphereW) sphereVertexLayer sphereSeamLayer
      spherePortLayer where
  faceCount := 4
  face := sphereFaceSet
  faceOwner f := (sphereFaceFun f).1
  faceModel f := .inl (sphereLevelHomeomorphJ (sphereFaceRadius_pos f)
    ((sphereFaceSet_eq f).trans (by rw [circHeight_sphereFaceRadius])))
  face_exhausted k := faceEquiv_exhausted_JOINT sphereFaceEquiv k
  faceKind := sphereFaceKind
  face_disjoint f f' hne hs _ := by
    fin_cases f <;> fin_cases f'
    all_goals first
      | exact absurd rfl hne
      | exact absurd ⟨rfl, rfl⟩ (hs (0 : Fin 1) true)
      | exact absurd ⟨rfl, rfl⟩ (hs (0 : Fin 1) false)
      | exact disjoint_sphereFaceSet (by simp [sphereFaceHeight]; norm_num)
  face_external _ i := i.elim0
  external_face i := i.elim0
  face_torusSeam _ c := c.elim0
  torusSeam_face c := c.elim0
  face_sphereSeam f c b h := by
    fin_cases f
    · cases h
      refine ⟨?_, rfl⟩
      change sphereFaceSet 0 = range fun z => sphereSharedSeam.collar (z, 0)
      rw [range_sphereSharedSeam_zero_neighbour]
      rfl
    · cases h
      refine ⟨?_, rfl⟩
      change sphereFaceSet 1 = range fun z => sphereSharedSeam.collar (z, 0)
      rw [range_sphereSharedSeam_zero, sphereSharedFace_set]
      exact (slimEndFace_image false).trans (by simp [slimEndHeight])
    · cases h
    · cases h
  sphereSeam_face c b := by
    have hc : c = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) c _
    subst hc
    cases b
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩

theorem sphereFaceLayer_face (f : Fin 4) : sphereFaceLayer.face f = sphereFaceSet f :=
  rfl

theorem sphereFaceLayer_faceOwner (f : Fin 4) :
    sphereFaceLayer.faceOwner f = (sphereFaceEquiv f).1 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
