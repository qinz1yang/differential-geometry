import DifferentialGeometry.Topology.Simplex.TetrahedronOneSkeleton
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.CompactOpen

noncomputable section

namespace DifferentialGeometry.Simplex

def edgeIntoTetrahedronOneSkeleton (i : Fin 4) (j : Fin 3) :
    C(stdSimplex ℝ (Fin 2), tetrahedronOneSkeleton) :=
  (faceBoundaryIntoTetrahedronOneSkeleton i).comp
    ⟨fun p => ⟨stdSimplex.map j.succAbove p, ⟨j, map_succAbove_apply_pivot j p⟩⟩,
      (stdSimplex.continuous_map j.succAbove).subtype_mk _⟩

@[simp] theorem edgeIntoTetrahedronOneSkeleton_val (i : Fin 4) (j : Fin 3)
    (p : stdSimplex ℝ (Fin 2)) :
    (edgeIntoTetrahedronOneSkeleton i j p).val =
      stdSimplex.map i.succAbove (stdSimplex.map j.succAbove p) := rfl

theorem exists_edgeIntoTetrahedronOneSkeleton_eq (p : tetrahedronOneSkeleton) :
    ∃ (i : Fin 4) (j : Fin 3) (q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j q = p := by
  obtain ⟨i, q, rfl⟩ := exists_faceBoundaryIntoTetrahedronOneSkeleton_eq p
  obtain ⟨j, hj⟩ := q.property
  let r := faceDelete j ⟨q.val, hj⟩
  refine ⟨i, j, r, ?_⟩
  apply congrArg (faceBoundaryIntoTetrahedronOneSkeleton i)
  apply Subtype.ext
  exact congrArg (fun z : face j => z.val) (faceInsert_faceDelete j ⟨q.val, hj⟩)

private def tetrahedronEdgeQuotientMap :
    C((Fin 4 × Fin 3) × stdSimplex ℝ (Fin 2), tetrahedronOneSkeleton) :=
  ⟨fun z => edgeIntoTetrahedronOneSkeleton z.1.1 z.1.2 z.2,
    continuous_prod_of_discrete_left.mpr fun i =>
      (edgeIntoTetrahedronOneSkeleton i.1 i.2).continuous⟩

private theorem tetrahedronEdgeQuotientMap_surjective :
    Function.Surjective tetrahedronEdgeQuotientMap := by
  intro p
  obtain ⟨i, j, q, hq⟩ := exists_edgeIntoTetrahedronOneSkeleton_eq p
  exact ⟨((i, j), q), hq⟩

private theorem tetrahedronEdgeQuotientMap_isQuotientMap :
    Topology.IsQuotientMap tetrahedronEdgeQuotientMap :=
  Topology.IsQuotientMap.of_surjective_continuous tetrahedronEdgeQuotientMap_surjective
    tetrahedronEdgeQuotientMap.continuous

variable {X : Type*} [TopologicalSpace X]

def tetrahedronOneSkeletonDesc
    (f : Fin 4 → Fin 3 → C(stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j p = f k l q) : C(tetrahedronOneSkeleton, X) := by
  let F : C((Fin 4 × Fin 3) × stdSimplex ℝ (Fin 2), X) :=
    ⟨fun z => f z.1.1 z.1.2 z.2,
      continuous_prod_of_discrete_left.mpr fun i => (f i.1 i.2).continuous⟩
  have hF : Function.FactorsThrough F tetrahedronEdgeQuotientMap := by
    intro a b hab
    exact h a.1.1 b.1.1 a.1.2 b.1.2 a.2 b.2 hab
  exact tetrahedronEdgeQuotientMap_isQuotientMap.lift F hF

@[simp] theorem tetrahedronOneSkeletonDesc_edge
    (f : Fin 4 → Fin 3 → C(stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j p = f k l q)
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) :
    tetrahedronOneSkeletonDesc f h (edgeIntoTetrahedronOneSkeleton i j p) = f i j p := by
  let F : C((Fin 4 × Fin 3) × stdSimplex ℝ (Fin 2), X) :=
    ⟨fun z => f z.1.1 z.1.2 z.2,
      continuous_prod_of_discrete_left.mpr fun i => (f i.1 i.2).continuous⟩
  have hF : Function.FactorsThrough F tetrahedronEdgeQuotientMap := by
    intro a b hab
    exact h a.1.1 b.1.1 a.1.2 b.1.2 a.2 b.2 hab
  have he := tetrahedronEdgeQuotientMap_isQuotientMap.lift_comp F hF
  exact congrArg (fun k => k ((i, j), p)) he

theorem tetrahedronOneSkeletonDesc_unique
    (f : Fin 4 → Fin 3 → C(stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j p = f k l q)
    (g : C(tetrahedronOneSkeleton, X))
    (hg : ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      g (edgeIntoTetrahedronOneSkeleton i j p) = f i j p) :
    g = tetrahedronOneSkeletonDesc f h := by
  ext p
  obtain ⟨i, j, q, rfl⟩ := exists_edgeIntoTetrahedronOneSkeleton_eq p
  rw [hg, tetrahedronOneSkeletonDesc_edge]

private def tetrahedronEdgePathMap
    (f : Fin 4 → Fin 3 → C(unitInterval × stdSimplex ℝ (Fin 2), X)) :
    Fin 4 → Fin 3 → C(stdSimplex ℝ (Fin 2), C(unitInterval, X)) := fun i j =>
  ((f i j).comp ⟨fun z => (z.2, z.1), continuous_snd.prodMk continuous_fst⟩).curry

def tetrahedronOneSkeletonHomotopyDesc
    (f : Fin 4 → Fin 3 → C(unitInterval × stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)) (t : unitInterval),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j (t, p) = f k l (t, q)) :
    C(unitInterval × tetrahedronOneSkeleton, X) := by
  let F := tetrahedronEdgePathMap f
  have hF : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        F i j p = F k l q := by
    intro i k j l p q hpq
    apply ContinuousMap.ext
    intro t
    exact h i k j l p q t hpq
  exact (tetrahedronOneSkeletonDesc F hF).uncurry.comp
    ⟨fun z => (z.2, z.1), continuous_snd.prodMk continuous_fst⟩

@[simp] theorem tetrahedronOneSkeletonHomotopyDesc_edge
    (f : Fin 4 → Fin 3 → C(unitInterval × stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)) (t : unitInterval),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j (t, p) = f k l (t, q))
    (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)) (t : unitInterval) :
    tetrahedronOneSkeletonHomotopyDesc f h (t, edgeIntoTetrahedronOneSkeleton i j p) =
      f i j (t, p) := by
  let F := tetrahedronEdgePathMap f
  have hF : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        F i j p = F k l q := by
    intro i k j l p q hpq
    apply ContinuousMap.ext
    intro t
    exact h i k j l p q t hpq
  change tetrahedronOneSkeletonDesc F hF (edgeIntoTetrahedronOneSkeleton i j p) t = _
  rw [tetrahedronOneSkeletonDesc_edge F hF]
  rfl

theorem tetrahedronOneSkeletonHomotopyDesc_eq
    (f : Fin 4 → Fin 3 → C(unitInterval × stdSimplex ℝ (Fin 2), X))
    (h : ∀ (i k : Fin 4) (j l : Fin 3) (p q : stdSimplex ℝ (Fin 2)) (t : unitInterval),
      edgeIntoTetrahedronOneSkeleton i j p = edgeIntoTetrahedronOneSkeleton k l q →
        f i j (t, p) = f k l (t, q))
    (t : unitInterval) (g : tetrahedronOneSkeleton → X)
    (hg : ∀ (i : Fin 4) (j : Fin 3) (p : stdSimplex ℝ (Fin 2)),
      f i j (t, p) = g (edgeIntoTetrahedronOneSkeleton i j p))
    (p : tetrahedronOneSkeleton) :
    tetrahedronOneSkeletonHomotopyDesc f h (t, p) = g p := by
  obtain ⟨i, j, q, rfl⟩ := exists_edgeIntoTetrahedronOneSkeleton_eq p
  rw [tetrahedronOneSkeletonHomotopyDesc_edge, hg]

end DifferentialGeometry.Simplex
