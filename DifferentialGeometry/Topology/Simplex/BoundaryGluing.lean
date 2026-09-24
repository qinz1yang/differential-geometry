import DifferentialGeometry.Topology.Simplex.Face
import DifferentialGeometry.Topology.Simplex.BoundaryRetraction
import DifferentialGeometry.Topology.Simplex.NormedBall
import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace DifferentialGeometry.Simplex

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

private theorem face_delete_map (i : Fin (n + 2))
    (p : stdSimplex ℝ (Fin (n + 2))) (hi : p.val i = 0) :
    stdSimplex.map i.succAbove (faceDelete i ⟨p, hi⟩) = p :=
  congrArg Subtype.val (faceInsert_faceDelete i ⟨p, hi⟩)

private theorem face_values_eq
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (i j : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 3)))
    (hi : p.val i = 0) (hj : p.val j = 0) :
    f i (faceDelete i ⟨p, hi⟩) = f j (faceDelete j ⟨p, hj⟩) := by
  by_cases hji : j = i
  · subst j
    rfl
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hji
  let q := faceDelete i ⟨p, hi⟩
  have hq : q.val j = 0 := hj
  let z := faceDelete j ⟨q, hq⟩
  have hz : stdSimplex.map j.succAbove z = q := face_delete_map j q hq
  have hother : faceDelete (i.succAbove j) ⟨p, hj⟩ =
      stdSimplex.map (j.predAbove i).succAbove z := by
    apply (faceHomeomorph (i.succAbove j)).injective
    apply Subtype.ext
    change stdSimplex.map (i.succAbove j).succAbove
      (faceDelete (i.succAbove j) ⟨p, hj⟩) =
        stdSimplex.map (i.succAbove j).succAbove (stdSimplex.map (j.predAbove i).succAbove z)
    rw [face_delete_map]
    calc
      p = stdSimplex.map i.succAbove q := (face_delete_map i p hi).symm
      _ = stdSimplex.map i.succAbove (stdSimplex.map j.succAbove z) := congrArg _ hz.symm
      _ = _ := by
        rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
        congr 1
        funext k
        exact (Fin.succAbove_succAbove_succAbove_predAbove i j k).symm
  rw [hother]
  change f i q = _
  rw [← hz]
  exact h i j z

private def boundaryDescFun
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (p : boundary (Fin (n + 3))) : X :=
  f p.property.choose (faceDelete p.property.choose ⟨p.val, p.property.choose_spec⟩)

private theorem boundaryDescFun_face
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (p : boundary (Fin (n + 3))) (i : Fin (n + 3)) (hi : p.val.val i = 0) :
    boundaryDescFun f p = f i (faceDelete i ⟨p.val, hi⟩) :=
  face_values_eq f h _ _ _ _ _

def boundaryDesc
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p)) :
    C(boundary (Fin (n + 3)), X) where
  toFun := boundaryDescFun f
  continuous_toFun := by
    let F (i : Fin (n + 3)) : Set (boundary (Fin (n + 3))) :=
      {p | p.val.val i = 0}
    have hcover : ⋃ i, F i = Set.univ := by
      apply Set.eq_univ_of_forall
      intro p
      exact Set.mem_iUnion.mpr p.property
    have hclosed (i : Fin (n + 3)) : IsClosed (F i) :=
      isClosed_eq ((continuous_apply i).comp
        (continuous_subtype_val.comp continuous_subtype_val)) continuous_const
    apply (locallyFinite_of_finite F).continuous hcover hclosed
    intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (fun p : F i ↦ boundaryDescFun f p.val) =
        fun p : F i ↦ f i (faceDelete i ⟨p.val.val, p.property⟩) := by
      funext p
      exact boundaryDescFun_face f h p.val i p.property
    change Continuous (fun p : F i ↦ boundaryDescFun f p.val)
    rw [he]
    exact (f i).continuous.comp ((faceDelete i).continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))

theorem boundaryDesc_face
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))) :
    boundaryDesc f h ⟨stdSimplex.map i.succAbove p,
      ⟨i, map_succAbove_apply_pivot i p⟩⟩ = f i p := by
  change boundaryDescFun f _ = f i p
  rw [boundaryDescFun_face f h _ i (map_succAbove_apply_pivot i p)]
  exact congrArg (f i) (faceDelete_faceInsert i p)


theorem boundaryDesc_unique
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (g : C(boundary (Fin (n + 3)), X))
    (hg : ∀ (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))),
      g ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩ = f i p) :
    g = boundaryDesc f h := by
  ext p
  obtain ⟨i, hi⟩ := p.property
  let q := faceDelete i ⟨p.val, hi⟩
  have he : p = ⟨stdSimplex.map i.succAbove q, ⟨i, map_succAbove_apply_pivot i q⟩⟩ :=
    Subtype.ext (face_delete_map i p.val hi).symm
  rw [he, hg, boundaryDesc_face]

def boundarySphereDesc
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p)) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X) :=
  (boundaryDesc f h).comp
    ⟨(stdSimplexNormedBoundarySphereHomeomorph
      (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm,
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm).symm.continuous⟩

theorem boundarySphereDesc_face
    (f : Fin (n + 3) → C(stdSimplex ℝ (Fin (n + 2)), X))
    (h : ∀ (i : Fin (n + 3)) (j : Fin (n + 2))
      (p : stdSimplex ℝ (Fin (n + 1))),
      f i (stdSimplex.map j.succAbove p) =
        f (i.succAbove j) (stdSimplex.map (j.predAbove i).succAbove p))
    (i : Fin (n + 3)) (p : stdSimplex ℝ (Fin (n + 2))) :
    boundarySphereDesc f h
      (stdSimplexNormedBoundarySphereHomeomorph
        (EuclideanSpace.equiv (Fin (n + 2)) ℝ).symm
        ⟨stdSimplex.map i.succAbove p, ⟨i, map_succAbove_apply_pivot i p⟩⟩) = f i p := by
  simp only [boundarySphereDesc, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Homeomorph.symm_apply_apply]
  exact boundaryDesc_face f h i p

end DifferentialGeometry.Simplex
