import DifferentialGeometry.Topology.Simplex.TriangleSphere
import DifferentialGeometry.Topology.Simplex.TriangleGenLoop
import DifferentialGeometry.Topology.Simplex.TriangleCubeSphere
import DifferentialGeometry.Topology.Homotopy.SpherePrecomposition
import DifferentialGeometry.Topology.Simplex.VertexContraction
import DifferentialGeometry.Topology.Simplex.HomotopyExtension
import DifferentialGeometry.Topology.Homotopy.SphereFamilyDescent
import Mathlib.Topology.Homotopy.Equiv

noncomputable section

open ContinuousMap

namespace DifferentialGeometry.Simplex

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem triangleSphereMap_natural (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) (f : C(X, Y)) :
    triangleSphereMap (f.comp g) (f x) (fun p hp => congrArg f (hg p hp)) =
      f.comp (triangleSphereMap g x hg) := by
  ext z
  obtain ⟨p, rfl⟩ := (stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 3) ℝ).symm).surjective z
  obtain ⟨i, hi⟩ := p.property
  let q := faceDelete i ⟨p.val, hi⟩
  have he : p = ⟨stdSimplex.map i.succAbove q,
      ⟨i, map_succAbove_apply_pivot i q⟩⟩ := by
    apply Subtype.ext
    exact (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
  rw [he]
  change boundarySphereDesc _ _ _ = f (boundarySphereDesc _ _ _)
  rw [boundarySphereDesc_face, boundarySphereDesc_face]
  fin_cases i <;> rfl


theorem genLoopSphereHomeomorph_triangleGenLoop_comp (g : C(stdSimplex ℝ (Fin 3), X))
    (x : X) (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    (Topology.genLoopSphereHomeomorph 1 x (triangleGenLoop g x hg)).val.comp
      triangleCubeSphereMap = g := by
  ext p
  obtain ⟨q, rfl⟩ := triangleJoin_surjective p
  rw [ContinuousMap.comp_apply, triangleCubeSphereMap_triangleJoin,
    Topology.genLoopSphereHomeomorph_projection]
  rfl

def triangleSphereCollapse :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  triangleSphereMap triangleCubeSphereMap (Topology.cubeSphereBasepoint 1)
    triangleCubeSphereMap_boundary

theorem triangleSphereMap_eq_comp_triangleSphereCollapse
    (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    triangleSphereMap g x hg =
      (Topology.genLoopSphereHomeomorph 1 x (triangleGenLoop g x hg)).val.comp
        triangleSphereCollapse := by
  let f := (Topology.genLoopSphereHomeomorph 1 x (triangleGenLoop g x hg)).val
  have hfg : f.comp triangleCubeSphereMap = g :=
    genLoopSphereHomeomorph_triangleGenLoop_comp g x hg
  have hfx : f (Topology.cubeSphereBasepoint 1) = x :=
    (Topology.genLoopSphereHomeomorph 1 x (triangleGenLoop g x hg)).property
  have h := triangleSphereMap_natural triangleCubeSphereMap (Topology.cubeSphereBasepoint 1)
    triangleCubeSphereMap_boundary f
  simpa only [hfg, hfx, triangleSphereCollapse] using h

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

private def inactiveDisk : Set (boundary (Fin 4)) :=
  {p | ∃ j : Fin 4, j ≠ 0 ∧ p.val.val j = 0}

private theorem vertexContraction_mem_inactiveDisk (t : unitInterval) (q : inactiveDisk) :
    ∃ j : Fin 4, j ≠ 0 ∧ (vertexContraction (0 : Fin 4) (t, q.1.1)).val j = 0 := by
  obtain ⟨j, hj, hz⟩ := q.2
  refine ⟨j, hj, ?_⟩
  rw [vertexContraction_apply]
  simp [hz, Ne.symm hj]

private def inactiveDiskContraction :
    C(unitInterval × inactiveDisk, inactiveDisk) where
  toFun z :=
    ⟨⟨vertexContraction (0 : Fin 4) (z.1, z.2.1.1), by
      obtain ⟨j, hj, hz⟩ := vertexContraction_mem_inactiveDisk z.1 z.2
      exact ⟨j, hz⟩⟩, vertexContraction_mem_inactiveDisk z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (vertexContraction (I := Fin 4) (0 : Fin 4)).continuous.comp
      (continuous_fst.prodMk
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)))

private theorem inactiveDiskContraction_apply (t : unitInterval) (q : inactiveDisk) :
    (inactiveDiskContraction (t, q)).val.val = vertexContraction (0 : Fin 4) (t, q.1.1) :=
  rfl

private def inactiveVertex0 : inactiveDisk :=
  ⟨⟨stdSimplex.vertex (S := ℝ) (0 : Fin 4), by
    exact ⟨1, by simp⟩⟩, by
    exact ⟨1, by decide, by simp⟩⟩

private theorem inactiveDiskContraction_zero (q : inactiveDisk) :
    inactiveDiskContraction (0, q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  exact vertexContraction_zero (0 : Fin 4) q.1.1

private theorem inactiveDiskContraction_one (q : inactiveDisk) :
    inactiveDiskContraction (1, q) = inactiveVertex0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact vertexContraction_one (0 : Fin 4) q.1.1

private theorem inactiveDiskContraction_vertex (t : unitInterval) :
    inactiveDiskContraction (t, inactiveVertex0) = inactiveVertex0 := by
  apply Subtype.ext
  apply Subtype.ext
  exact vertexContraction_vertex (0 : Fin 4) t

private def boundaryTriangleToInactive :
    C(boundary (Fin 3), inactiveDisk) where
  toFun q :=
    ⟨⟨stdSimplex.map (0 : Fin 4).succAbove q.1,
      ⟨0, map_succAbove_apply_pivot (0 : Fin 4) q.1⟩⟩, by
      obtain ⟨j, hz⟩ := q.2
      refine ⟨(0 : Fin 4).succAbove j, Fin.succAbove_ne _ _, ?_⟩
      rw [map_succAbove_apply_image]
      exact hz⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (stdSimplex.continuous_map (0 : Fin 4).succAbove).comp continuous_subtype_val

private def inactiveDiskBoundaryInclusion :
    C(inactiveDisk, boundary (Fin 4)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def boundaryTriangleContraction :
    C(unitInterval × boundary (Fin 3), boundary (Fin 4)) :=
  inactiveDiskBoundaryInclusion.comp
    (inactiveDiskContraction.comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) boundaryTriangleToInactive))

private theorem boundaryTriangleContraction_apply (t : unitInterval) (q : boundary (Fin 3)) :
    (boundaryTriangleContraction (t, q)).val =
      vertexContraction (0 : Fin 4) (t, stdSimplex.map (0 : Fin 4).succAbove q.val) :=
  rfl

private theorem boundaryTriangleContraction_mem_inactiveDisk
    (t : unitInterval) (q : boundary (Fin 3)) :
    boundaryTriangleContraction (t, q) ∈ inactiveDisk :=
  (inactiveDiskContraction (t, boundaryTriangleToInactive q)).property

private theorem boundaryTriangleContraction_zero (q : boundary (Fin 3)) :
    boundaryTriangleContraction (0, q) =
      ⟨stdSimplex.map (0 : Fin 4).succAbove q.1,
        ⟨0, map_succAbove_apply_pivot (0 : Fin 4) q.1⟩⟩ := by
  apply Subtype.ext
  exact vertexContraction_zero (0 : Fin 4) _

private theorem boundaryTriangleContraction_one (q : boundary (Fin 3)) :
    boundaryTriangleContraction (1, q) = inactiveVertex0.val := by
  apply Subtype.ext
  exact vertexContraction_one (0 : Fin 4) _

private def tetrahedronFaceInclusion (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), boundary (Fin 4)) where
  toFun p := ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (stdSimplex.continuous_map i.succAbove).subtype_mk _

private def inactiveFaceInclusion (i : Fin 4) (hi : i ≠ 0) :
    C(stdSimplex ℝ (Fin 3), inactiveDisk) where
  toFun p := ⟨tetrahedronFaceInclusion i p, ⟨i, hi, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (tetrahedronFaceInclusion i).continuous.subtype_mk _

private def inactiveFaceContraction (i : Fin 4) (hi : i ≠ 0) :
    C(unitInterval × stdSimplex ℝ (Fin 3), boundary (Fin 4)) :=
  inactiveDiskBoundaryInclusion.comp
    (inactiveDiskContraction.comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) (inactiveFaceInclusion i hi)))

private theorem exists_boundaryHomotopy_contraction_inactiveDisk :
    ∃ K : C(unitInterval × boundary (Fin 4), boundary (Fin 4)),
      (∀ p, K (0, p) = p) ∧
      (∀ (t : unitInterval) (p : boundary (Fin 4)), p ∈ inactiveDisk →
        (K (t, p)).val = vertexContraction (0 : Fin 4) (t, p.val)) := by
  classical
  obtain ⟨F, hF, hside⟩ := exists_continuous_homotopy_extension 2
    (tetrahedronFaceInclusion 0) boundaryTriangleContraction boundaryTriangleContraction_zero
  let L (i : Fin 4) : C(unitInterval × stdSimplex ℝ (Fin 3), boundary (Fin 4)) :=
    if hi : i = 0 then F else inactiveFaceContraction i hi
  have hL (i : Fin 4) (j : Fin 3) (t : unitInterval)
      (p : stdSimplex ℝ (Fin 2)) :
      (L i (t, stdSimplex.map j.succAbove p)).val =
        vertexContraction (0 : Fin 4)
          (t, stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p)) := by
    by_cases hi : i = 0
    · subst i
      simp only [L, dif_pos rfl]
      exact congrArg Subtype.val (hside t
        ⟨stdSimplex.map j.succAbove p, ⟨j, map_succAbove_apply_pivot j p⟩⟩)
    · simp only [L, dif_neg hi]
      rfl
  have hfaces (i : Fin 4) (j : Fin 3) (t : unitInterval)
      (p : stdSimplex ℝ (Fin 2)) :
      L i (t, stdSimplex.map j.succAbove p) =
        L (i.succAbove j) (t, stdSimplex.map (j.predAbove i).succAbove p) := by
    apply Subtype.ext
    rw [hL, hL]
    congr 2
    rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
    congr 1
    funext k
    exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  let G (i : Fin 4) : C(stdSimplex ℝ (Fin 3), C(unitInterval, boundary (Fin 4))) :=
    ((L i).comp ContinuousMap.prodSwap).curry
  have hG (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
      G i (stdSimplex.map j.succAbove p) =
        G (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p) := by
    apply ContinuousMap.ext
    intro t
    exact hfaces i j t p
  let K : C(unitInterval × boundary (Fin 4), boundary (Fin 4)) :=
    (boundaryDesc G hG).uncurry.comp ContinuousMap.prodSwap
  have hK (i : Fin 4) (t : unitInterval) (p : stdSimplex ℝ (Fin 3)) :
      K (t, tetrahedronFaceInclusion i p) = L i (t, p) := by
    change boundaryDesc G hG ⟨stdSimplex.map i.succAbove p,
      ⟨i, map_succAbove_apply_pivot i p⟩⟩ t = L i (t, p)
    rw [boundaryDesc_face]
    rfl
  refine ⟨K, ?_, ?_⟩
  · intro p
    obtain ⟨i, hi⟩ := p.property
    let q := faceDelete i ⟨p.val, hi⟩
    have hq : tetrahedronFaceInclusion i q = p := by
      apply Subtype.ext
      change stdSimplex.map i.succAbove q = p.val
      exact congrArg (fun r : face i => r.val) (faceInsert_faceDelete i ⟨p.val, hi⟩)
    rw [← hq, hK]
    by_cases hi0 : i = 0
    · subst i
      exact hF q
    · simp only [L, dif_neg hi0]
      apply Subtype.ext
      exact vertexContraction_zero (0 : Fin 4) _
  · intro t p hp
    obtain ⟨i, hi0, hi⟩ := hp
    let q := faceDelete i ⟨p.val, hi⟩
    have hq : tetrahedronFaceInclusion i q = p := by
      apply Subtype.ext
      change stdSimplex.map i.succAbove q = p.val
      exact congrArg (fun r : face i => r.val) (faceInsert_faceDelete i ⟨p.val, hi⟩)
    rw [← hq, hK]
    simp only [L, dif_neg hi0]
    rfl

private theorem exists_boundaryHomotopy_preserves_inactiveDisk :
    ∃ K : C(unitInterval × boundary (Fin 4), boundary (Fin 4)),
      (∀ p, K (0, p) = p) ∧
      (∀ p ∈ inactiveDisk, K (1, p) = inactiveVertex0.val) ∧
      ∀ (t : unitInterval) p, p ∈ inactiveDisk → K (t, p) ∈ inactiveDisk := by
  obtain ⟨K, hK0, hKA⟩ := exists_boundaryHomotopy_contraction_inactiveDisk
  refine ⟨K, hK0, ?_, ?_⟩
  · intro p hp
    apply Subtype.ext
    exact (hKA 1 p hp).trans (vertexContraction_one (0 : Fin 4) p.val)
  · intro t p hp
    obtain ⟨j, hj, hz⟩ := vertexContraction_mem_inactiveDisk t ⟨p, hp⟩
    refine ⟨j, hj, ?_⟩
    rw [hKA t p hp]
    exact hz


private abbrev B := boundary (Fin 4)
private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def vertexZero : B := ⟨stdSimplex.vertex (S := ℝ) 0, ⟨1, by simp⟩⟩

private def inactive : Set B := {p : B | ∃ j : Fin 4, j ≠ 0 ∧ p.val.val j = 0}

private def faceB (i : Fin 4) : C(stdSimplex ℝ (Fin 3), B) where
  toFun p := ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩
  continuous_toFun := (stdSimplex.continuous_map i.succAbove).subtype_mk _

private theorem face_zero_boundary (p : stdSimplex ℝ (Fin 3))
    (hp : p ∈ boundary (Fin 3)) : faceB 0 p ∈ inactive := by
  obtain ⟨j, hj⟩ := hp
  exact ⟨(0 : Fin 4).succAbove j, Fin.succAbove_ne _ _, by
    simpa only [faceB, ContinuousMap.coe_mk, map_succAbove_apply_image] using hj⟩

private theorem face_inactive (i : Fin 4) (hi : i ≠ 0) (p : stdSimplex ℝ (Fin 3)) :
    faceB i p ∈ inactive := ⟨i, hi, map_succAbove_apply_pivot i p⟩

private def collapseBoundary : C(B, S) :=
  boundaryDesc (triangleSphereFaces triangleCubeSphereMap (Topology.cubeSphereBasepoint 1))
    (triangleSphereFaces_compatible triangleCubeSphereMap (Topology.cubeSphereBasepoint 1)
      triangleCubeSphereMap_boundary)

private theorem collapseBoundary_face (i : Fin 4) (p : stdSimplex ℝ (Fin 3)) :
    collapseBoundary (faceB i p) =
      triangleSphereFaces triangleCubeSphereMap (Topology.cubeSphereBasepoint 1) i p :=
  boundaryDesc_face _ _ i p

private theorem collapseBoundary_inactive (p : B) (hp : p ∈ inactive) :
    collapseBoundary p = Topology.cubeSphereBasepoint 1 := by
  obtain ⟨i, hi, hpi⟩ := hp
  let q := faceDelete i ⟨p.val, hpi⟩
  have he : p = faceB i q :=
    Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hpi⟩)).symm
  rw [he, collapseBoundary_face]
  fin_cases i <;> first | contradiction | rfl

private theorem collapseBoundary_zero (p : stdSimplex ℝ (Fin 3)) :
    collapseBoundary (faceB 0 p) = triangleCubeSphereMap p :=
  collapseBoundary_face 0 p

private theorem exists_collapseBoundary_homotopyEquiv
    (K : C(unitInterval × B, B))
    (hzero : ∀ p, K (0, p) = p)
    (hone : ∀ p ∈ inactive, K (1, p) = vertexZero)
    (hpres : ∀ t p, p ∈ inactive → K (t, p) ∈ inactive) :
    ∃ e : HomotopyEquiv B S, e.toFun = collapseBoundary := by
  let g : C(stdSimplex ℝ (Fin 3), B) :=
    K.comp ⟨fun p => (1, faceB 0 p), continuous_const.prodMk (faceB 0).continuous⟩
  have hg : ∀ p ∈ boundary (Fin 3), g p = vertexZero :=
    fun p hp => hone (faceB 0 p) (face_zero_boundary p hp)
  let R : C(S, B) :=
    (Topology.genLoopSphereHomeomorph 1 vertexZero (triangleGenLoop g vertexZero hg)).val
  have hRg : R.comp triangleCubeSphereMap = g :=
    genLoopSphereHomeomorph_triangleGenLoop_comp g vertexZero hg
  have hRb : R (Topology.cubeSphereBasepoint 1) = vertexZero :=
    (Topology.genLoopSphereHomeomorph 1 vertexZero (triangleGenLoop g vertexZero hg)).property
  have hRK (p : B) : R (collapseBoundary p) = K (1, p) := by
    obtain ⟨i, hi⟩ := p.property
    let q := faceDelete i ⟨p.val, hi⟩
    have he : p = faceB i q :=
      Subtype.ext (congrArg Subtype.val (faceInsert_faceDelete i ⟨p.val, hi⟩)).symm
    rw [he]
    by_cases h : i = 0
    · subst i
      rw [collapseBoundary_zero]
      exact congrArg (fun F : C(stdSimplex ℝ (Fin 3), B) => F q) hRg
    · rw [collapseBoundary_inactive _ (face_inactive i h q), hRb]
      exact (hone _ (face_inactive i h q)).symm
  have hleft : (R.comp collapseBoundary).Homotopic (ContinuousMap.id B) := by
    refine ⟨(show (ContinuousMap.id B).Homotopy (R.comp collapseBoundary) from ?_).symm⟩
    exact ⟨K, hzero, fun p => (hRK p).symm⟩
  let F : C(unitInterval × (Fin 2 → unitInterval), S) :=
    collapseBoundary.comp (K.comp ⟨fun z =>
      (z.1, faceB 0 (triangleJoin (z.2 0, z.2 1))),
      continuous_fst.prodMk ((faceB 0).continuous.comp
        (triangleJoin.continuous.comp
          (((continuous_apply 0).comp continuous_snd).prodMk
            ((continuous_apply 1).comp continuous_snd))))⟩)
  have hF : ∀ t v, v ∈ Cube.boundary (Fin 2) →
      F (t, v) = Topology.cubeSphereBasepoint 1 := by
    intro t v hv
    apply collapseBoundary_inactive
    apply hpres
    apply face_zero_boundary
    apply (triangleJoin_mem_boundary_iff (v 0, v 1)).mpr
    have he : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rwa [he]
  let Z : C(unitInterval, S) := ContinuousMap.const _ (Topology.cubeSphereBasepoint 1)
  have hright : (collapseBoundary.comp R).Homotopic (ContinuousMap.id S) := by
    refine ⟨(show (ContinuousMap.id S).Homotopy (collapseBoundary.comp R) from ?_).symm⟩
    refine {
      toFun := Topology.sphereFamilyDescendValue 1 F Z
      continuous_toFun := Topology.continuous_sphereFamilyDescendValue 1 F Z hF
      map_zero_left := ?_
      map_one_left := ?_ }
    · intro z
      obtain ⟨v, rfl⟩ := Topology.cubeSphereProjection_surjective 1 z
      rw [Topology.sphereFamilyDescendValue_projection 1 F Z hF]
      change collapseBoundary (K (0, faceB 0 (triangleJoin (v 0, v 1)))) = _
      rw [hzero, collapseBoundary_zero, triangleCubeSphereMap_triangleJoin]
      have he : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
      exact congrArg (Topology.cubeSphereProjection 1) he
    · intro z
      obtain ⟨v, rfl⟩ := Topology.cubeSphereProjection_surjective 1 z
      rw [Topology.sphereFamilyDescendValue_projection 1 F Z hF]
      change collapseBoundary (K (1, faceB 0 (triangleJoin (v 0, v 1)))) = _
      rw [← hRK, collapseBoundary_zero, triangleCubeSphereMap_triangleJoin]
      have he : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
      exact congrArg (fun w => collapseBoundary (R (Topology.cubeSphereProjection 1 w))) he
  exact ⟨⟨collapseBoundary, R, hleft, hright⟩, rfl⟩


private theorem exists_triangleSphereCollapse_homotopyEquiv_of_contraction
    (K : C(unitInterval × B, B))
    (hzero : ∀ p, K (0, p) = p)
    (hone : ∀ p ∈ inactive, K (1, p) = vertexZero)
    (hpres : ∀ t p, p ∈ inactive → K (t, p) ∈ inactive) :
    ∃ e : HomotopyEquiv S S, e.toFun = triangleSphereCollapse := by
  obtain ⟨e, he⟩ := exists_collapseBoundary_homotopyEquiv K hzero hone hpres
  let b := stdSimplexNormedBoundarySphereHomeomorph
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  refine ⟨b.symm.toHomotopyEquiv.trans e, ?_⟩
  change e.toFun.comp (⟨b.symm, b.symm.continuous⟩ : C(S, B)) = triangleSphereCollapse
  rw [he]
  rfl


theorem triangleSphereCollapse_homotopyEquiv :
    ∃ e : ContinuousMap.HomotopyEquiv
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      e.toFun = triangleSphereCollapse := by
  obtain ⟨K, hK0, hKA, hKpres⟩ := exists_boundaryHomotopy_preserves_inactiveDisk
  exact exists_triangleSphereCollapse_homotopyEquiv_of_contraction K hK0 hKA hKpres

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem triangleSphereMap_class_eq_precompose
    (g : C(stdSimplex ℝ (Fin 3), X)) (x : X)
    (hg : ∀ p ∈ boundary (Fin 3), g p = x) :
    (Topology.homotopyGroupFreeSphereEquiv 1 x).symm
      (ZerothHomotopy.mk (triangleSphereMap g x hg)) =
      Topology.homotopyGroupSpherePrecompose 1 x triangleSphereCollapse
        (⟦triangleGenLoop g x hg⟧ : HomotopyGroup (Fin 2) X x) := by
  unfold Topology.homotopyGroupSpherePrecompose
  rw [Topology.homotopyGroupToFreeSphere_mk, Topology.freeSpherePrecompose_mk,
    triangleSphereMap_eq_comp_triangleSphereCollapse]

end DifferentialGeometry.Simplex

namespace DifferentialGeometry.Simplex

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

theorem homotopyGroupSpherePrecompose_triangleSphereCollapse_bijective (x : X) :
    Function.Bijective (Topology.homotopyGroupSpherePrecompose 1 x triangleSphereCollapse) := by
  obtain ⟨e, he⟩ := triangleSphereCollapse_homotopyEquiv
  rw [← he]
  exact Topology.homotopyGroupSpherePrecompose_homotopyEquiv 1 x e

end DifferentialGeometry.Simplex
