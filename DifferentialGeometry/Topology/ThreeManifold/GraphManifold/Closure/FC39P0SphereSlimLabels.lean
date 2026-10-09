import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereSlimFaces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereEdge
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.CycleIncidence

/-!
# FC39 producer, packet P0 (gate 1): the horizontal labels of the S³ edge endpoints

The common S³ configuration (lead decision T49-1): the four endpoints of the accepted edge kind
`sphereEdgeBundle` (`FC39P0SphereEdge*.lean`, handles `cycleS3Handle b`, radius `1 → 4`, reversed
on the north side) against the residual faces of the slim kind (`FC39P0SphereSlimFaces.lean`):

* the endpoint `(i, e)` (handle `b = finTwoEquiv i`, interval end `e`) has the label
  `edgeEndLabel (i, e) = (b != e)`: `true` = the model face of `Z₊` (`r = 4`, `q₀ = 3/5`), `false`
  = the new slim end (`r = 1`, `q₀ = −3/5`); `sphereHorizontal : EdgeEnd → ResidualFace`;
* `sphere_horizontal_disk`: the WHOLE end disk lies in its labelled face (`horizontal_disk` of
  `JunctionsV2` for these data);
* `sphere_edge_faces`: `P ∩ F` is the union of the end disks labelled `F`, face by face
  (`edge_faces` of `JunctionsV2` for these data).

Key computation: on the handle chart `χ_b(w, t)` the height is the stereographic height of the
radius `cycleHandleRadius s`, `s = t` (south) or `1 − t` (north) (`sphereHeight_handleChart`), and
on the handle (`t ∈ [0, 1]`) the level `q₀ = ±3/5` is exactly the end `t = iccEnd (b != c)`
(`sphereHeight_handle_eq_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

local instance diskChartsLabels_FC39P0c : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The height on the handle charts -/

/-- The radius parameter of the handle chart `χ_b(w, t)`: `t` on the south side, `1 − t` on the
north side. -/
def handleRadiusParam (b : Bool) (t : ℝ) : ℝ :=
  bif b then 1 - t else t

theorem handleRadiusParam_mem_Ioo (b : Bool) {t : ℝ} (ht : t ∈ Ioo (-1 / 2 : ℝ) (3 / 2)) :
    handleRadiusParam b t ∈ Ioo (-1 / 2 : ℝ) (3 / 2) := by
  cases b
  · exact ht
  · exact ⟨by simp only [handleRadiusParam, Bool.cond_true]; linarith [ht.2],
      by simp only [handleRadiusParam, Bool.cond_true]; linarith [ht.1]⟩

theorem handleRadiusParam_mem_Icc (b : Bool) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    handleRadiusParam b t ∈ Icc (0 : ℝ) 1 := by
  cases b
  · exact ht
  · exact ⟨by simp only [handleRadiusParam, Bool.cond_true]; linarith [ht.2],
      by simp only [handleRadiusParam, Bool.cond_true]; linarith [ht.1]⟩

/-- **The height on the handle chart** is the stereographic height of the handle radius. -/
theorem sphereHeight_handleChart (b : Bool) {p : E2 × ℝ} (hp : p ∈ edgeBox) :
    sphereHeight (cycleHandleChart b p) =
      (cycleHandleRadius (handleRadiusParam b p.2) ^ 2 - 4) /
        (cycleHandleRadius (handleRadiusParam b p.2) ^ 2 + 4) := by
  have hpos := cycleHandleRadius_pos_FC39P0 (handleRadiusParam_mem_Ioo b hp.2)
  have hθ : ‖((Handle.stereoChart northPole).symm p.1 : E3)‖ = 1 := norm_eq_of_mem_sphere _
  rw [cycleHandleChart_eq_FC39P0, sphereHeight_ambient_false]
  cases b
  · simp only [handleRadiusParam, Bool.cond_false] at hpos ⊢
    simp only [Bool.false_eq_true, ite_false]
    rw [norm_smul, hθ, Real.norm_eq_abs, abs_of_pos hpos, mul_one]
  · simp only [handleRadiusParam, Bool.cond_true] at hpos ⊢
    simp only [ite_true]
    rw [norm_smul, norm_neg, hθ, Real.norm_eq_abs, abs_of_pos hpos, mul_one]

theorem stereoHeight_eq_neg_three_fifths_iff {R : ℝ} (hR : 0 < R) :
    (R ^ 2 - 4) / (R ^ 2 + 4) = -3 / 5 ↔ R = 1 := by
  rw [stereoHeight_eq_iff (sq_nonneg R) (by norm_num)]
  constructor
  · intro h
    have h2 : R ^ 2 = 1 ^ 2 := by rw [h]; norm_num
    exact (pow_left_inj₀ hR.le zero_le_one two_ne_zero).1 h2
  · rintro rfl
    norm_num

theorem stereoHeight_eq_three_fifths_iff {R : ℝ} (hR : 0 < R) :
    (R ^ 2 - 4) / (R ^ 2 + 4) = 3 / 5 ↔ R = 4 := by
  rw [stereoHeight_eq_iff (sq_nonneg R) (by norm_num)]
  constructor
  · intro h
    have h2 : R ^ 2 = 4 ^ 2 := by rw [h]; norm_num
    exact (pow_left_inj₀ hR.le (by norm_num) two_ne_zero).1 h2
  · rintro rfl
    norm_num

/-- **On a handle the residual levels are exactly the two ends**: `q₀ = −3/5` (the new slim end)
at `s = 0`, `q₀ = 3/5` (the face of `Z₊`) at `s = 1`, i.e. at `t = iccEnd (b != c)`. -/
theorem sphereHeight_handle_eq_iff {b c : Bool} (w : ClosedCell 2) {t : Icc (0 : ℝ) 1} :
    sphereHeight ((cycleS3Handle b).map (w, t)) = sphereResidualHeight c ↔
      t = iccEnd (b != c) := by
  have hp := handle_box w t
  have hs := handleRadiusParam_mem_Icc b t.2
  have hpos := cycleHandleRadius_pos_FC39P0 (handleRadiusParam_mem_Ioo b hp.2)
  rw [cycleS3Handle_map, sphereHeight_handleChart b hp]
  change _ = _ ↔ _
  cases c
  · change _ = -3 / 5 ↔ _
    rw [stereoHeight_eq_neg_three_fifths_iff hpos, cycleHandleRadius_eq_one hs]
    cases b
    · simp only [handleRadiusParam, Bool.cond_false, bne_self_eq_false]
      exact ⟨fun h => Subtype.ext (by simp [iccEnd, h]), fun h => by simp [h, iccEnd]⟩
    · simp only [handleRadiusParam, Bool.cond_true]
      constructor
      · intro h
        exact Subtype.ext (show (t : ℝ) = 1 by linarith)
      · intro h
        rw [h]
        simp [iccEnd]
  · change _ = 3 / 5 ↔ _
    rw [stereoHeight_eq_three_fifths_iff hpos, cycleHandleRadius_eq_four hs]
    cases b
    · simp only [handleRadiusParam, Bool.cond_false]
      exact ⟨fun h => Subtype.ext (by simp [iccEnd, h]), fun h => by simp [h, iccEnd]⟩
    · simp only [handleRadiusParam, Bool.cond_true, bne_self_eq_false]
      constructor
      · intro h
        exact Subtype.ext (show (t : ℝ) = 0 by linarith)
      · intro h
        rw [h]
        simp [iccEnd]

/-! ## The labels -/

/-- The four endpoints of the S³ edge bundle, numbered by (handle, interval end). -/
def sphereEdgeEndEquiv : Fin 2 × Bool ≃ sphereEdgeBundle.EdgeEnd :=
  Equiv.ofBijective edgeEndFun edgeEndFun_bijective

/-- The label of the endpoint `(i, e)`: `true` (the face of `Z₊`) iff the handle side differs
from the interval end. -/
def edgeEndLabel (a : Fin 2 × Bool) : Bool :=
  finTwoEquiv a.1 != a.2

/-- **The horizontal labels of the S³ data**: the residual face of every edge endpoint. -/
def sphereHorizontal (e : sphereEdgeBundle.EdgeEnd) : sphereSlimPieces.ResidualFace :=
  sphereResidual (edgeEndLabel (sphereEdgeEndEquiv.symm e))

theorem sphereHorizontal_apply (a : Fin 2 × Bool) :
    sphereHorizontal (sphereEdgeEndEquiv a) = sphereResidual (edgeEndLabel a) := by
  rw [sphereHorizontal, Equiv.symm_apply_apply]

theorem sphereEdgeEndEquiv_apply (a : Fin 2 × Bool) :
    (sphereEdgeEndEquiv a).1 = edgeInterval (finTwoEquiv a.1) (iccEnd a.2) :=
  rfl

/-- The end disk of the endpoint `(i, e)` is the end slice of the handle `finTwoEquiv i`. -/
theorem sphereEdge_disk_eq (a : Fin 2 × Bool) :
    sphereEdgeBundle.disk (sphereEdgeEndEquiv a).1 =
      range fun w => (cycleS3Handle (finTwoEquiv a.1)).map (w, iccEnd a.2) :=
  (cycleS3Handle_disk (finTwoEquiv a.1) (iccEnd a.2)).symm

theorem bne_bne_self (b e : Bool) : (b != (b != e)) = e := by
  cases b <;> cases e <;> rfl

/-- **`horizontal_disk` for the S³ data**: the whole end disk lies in its labelled face. -/
theorem sphere_horizontal_disk (e : sphereEdgeBundle.EdgeEnd) :
    sphereEdgeBundle.disk e.1 ⊆ sphereSlimPieces.residualSet (sphereHorizontal e) := by
  obtain ⟨a, rfl⟩ := sphereEdgeEndEquiv.surjective e
  rw [sphereHorizontal_apply, residualSet_sphereResidual, sphereEdge_disk_eq]
  rintro _ ⟨w, rfl⟩
  refine (sphereHeight_handle_eq_iff (b := finTwoEquiv a.1) (c := edgeEndLabel a) w
    (t := iccEnd a.2)).2 ?_
  rw [edgeEndLabel, bne_bne_self]

/-- **The edge piece of the S³ data is the union of the two handles.** -/
theorem sphere_edgePiece_eq :
    sphereEdgeBundle.edgePiece = ⋃ b, range (cycleS3Handle b).map := by
  have h : (⋃ b, range (cycleS3Handle b).map) =
      range (cycleS3Handle false).map ∪ range (cycleS3Handle true).map := by
    ext y
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      exacts [Or.inl hb, Or.inr hb]
    · rintro (hb | hb)
      exacts [⟨false, hb⟩, ⟨true, hb⟩]
  rw [h, range_cycleS3Handle_eq, range_cycleS3Handle_eq, ← image_union]
  change Subtype.val '' {x : edgeSource | edgeProj x ∈ edgeCbase ∧ edgeHeight x ≤ 1} = _
  congr 1
  ext x
  simp only [edgeCbase_eq, mem_ofPred_eq, mem_union]
  tauto

/-- **`edge_faces` for the S³ data**: `P ∩ F` is the union of the end disks labelled `F`. -/
theorem sphere_edge_faces (F : sphereSlimPieces.ResidualFace) :
    sphereEdgeBundle.edgePiece ∩ sphereSlimPieces.residualSet F =
      ⋃ (e : sphereEdgeBundle.EdgeEnd) (_ : sphereHorizontal e = F), sphereEdgeBundle.disk e.1 := by
  obtain ⟨c, rfl⟩ := sphereResidual_surjective F
  ext y
  constructor
  · rintro ⟨hy, hF⟩
    rw [sphere_edgePiece_eq] at hy
    obtain ⟨b, ⟨w, t⟩, rfl⟩ := mem_iUnion.1 hy
    rw [residualSet_sphereResidual] at hF
    have ht := (sphereHeight_handle_eq_iff w).1 hF
    refine mem_iUnion₂.2 ⟨sphereEdgeEndEquiv (finTwoEquiv.symm b, b != c), ?_, ?_⟩
    · rw [sphereHorizontal_apply, edgeEndLabel, Equiv.apply_symm_apply, bne_bne_self]
    · rw [sphereEdge_disk_eq]
      refine ⟨w, ?_⟩
      change (cycleS3Handle (finTwoEquiv (finTwoEquiv.symm b))).map (w, iccEnd (b != c)) = _
      rw [Equiv.apply_symm_apply, ← ht]
  · intro hy
    obtain ⟨e, he, hy⟩ := mem_iUnion₂.1 hy
    refine ⟨?_, he ▸ sphere_horizontal_disk e hy⟩
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hy
    refine ⟨x, ⟨?_, hx2⟩, rfl⟩
    rw [hx1]
    exact sphereEdgeBundle.frontier_cbase_subset e.2

end GC.GraphManifold.Assembly.FC39P0
