import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Analysis.Normed.Module.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Simplicial

universe u

namespace Poincare.Homology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]


def affineSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    C(stdSimplex ℝ (Fin (n + 1)), E) where
  toFun x := ∑ i, x i • v i
  continuous_toFun := continuous_finsetSum _ (fun i _ ↦
    ((continuous_apply i).comp continuous_subtype_val).smul continuous_const)


theorem affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → E)
    (x : stdSimplex ℝ (Fin (n + 1))) : affineSimplex v x = ∑ i, x i • v i := rfl


@[simp]
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    affineSimplex v (stdSimplex.vertex i) = v i := by
  simp [affineSimplex, Pi.single_apply]

theorem affineSimplex_comp_map {n m : ℕ} (v : Fin (n + 1) → E)
    (f : Fin (m + 1) → Fin (n + 1)) :
    (affineSimplex v).comp ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ =
      affineSimplex (v ∘ f) := by
  ext x
  change ∑ j, (FunOnFinite.linearMap ℝ ℝ f x.val) j • v j = ∑ i, x i • v (f i)
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_smul]
  calc
    _ = ∑ j, ∑ i ∈ Finset.univ with f i = j, x i • v (f i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      rfl
    _ = _ := Finset.sum_fiberwise Finset.univ f _


theorem range_affineSimplex_subset {n : ℕ} (v : Fin (n + 1) → E) {s : Set E}
    (hs : Convex ℝ s) (hv : ∀ i, v i ∈ s) : Set.range (affineSimplex v) ⊆ s := by
  rintro _ ⟨x, rfl⟩
  exact hs.sum_mem (fun i _ ↦ x.property.1 i) x.property.2 (fun i _ ↦ hv i)


def affineSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ} (v : Fin (n + 1) → s) :
    C(stdSimplex ℝ (Fin (n + 1)), s) :=
  ⟨fun x ↦ ⟨affineSimplex (fun i ↦ (v i : E)) x,
      range_affineSimplex_subset _ hs (fun i ↦ (v i).property) ⟨x, rfl⟩⟩,
    (affineSimplex (fun i ↦ (v i : E))).continuous.subtype_mk _⟩


def affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    TopCat.toSSet.obj (TopCat.of E) _⦋n⦌ :=
  ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).symm (affineSimplex v)


def singularSimplexVertices {n : ℕ} (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    Fin (n + 1) → E :=
  fun i ↦ (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ (stdSimplex.vertex i)


@[simp]
theorem singularSimplexVertices_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    singularSimplexVertices (affineSingularSimplex v) = v := by
  funext i
  exact affineSimplex_vertex v i

omit [NormedSpace ℝ E] in
theorem singularSimplexVertices_map {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n⦌) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).map f.op σ) =
      singularSimplexVertices σ ∘ f := by
  funext i
  change (TopCat.of E).toSSetObjEquiv (op ⦋n⦌) σ
      (stdSimplex.map f (stdSimplex.vertex i)) = _
  rw [stdSimplex.map_vertex]
  rfl

omit [NormedSpace ℝ E] in
@[simp]
theorem singularSimplexVertices_δ {n : ℕ}
    (σ : TopCat.toSSet.obj (TopCat.of E) _⦋n + 1⦌) (i : Fin (n + 2)) :
    singularSimplexVertices ((TopCat.toSSet.obj (TopCat.of E)).δ i σ) =
      singularSimplexVertices σ ∘ i.succAbove :=
  singularSimplexVertices_map (SimplexCategory.δ i) σ


theorem map_affineSingularSimplex {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (v : Fin (n + 1) → E) :
    (TopCat.toSSet.obj (TopCat.of E)).map f.op (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ f) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋m⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map f, stdSimplex.continuous_map f⟩ = affineSimplex (v ∘ f)
  exact affineSimplex_comp_map v f

def affineStraightening : TopCat.toSSet.obj (TopCat.of E) ⟶ TopCat.toSSet.obj (TopCat.of E) where
  app n := ↾fun σ ↦ affineSingularSimplex (n := n.unop.len) (singularSimplexVertices σ)
  naturality n m f := by
    ext σ
    change affineSingularSimplex (singularSimplexVertices
      ((TopCat.toSSet.obj (TopCat.of E)).map f σ)) =
        (TopCat.toSSet.obj (TopCat.of E)).map f
          (affineSingularSimplex (singularSimplexVertices σ))
    exact (congrArg affineSingularSimplex (singularSimplexVertices_map f.unop σ)).trans
      (map_affineSingularSimplex f.unop (singularSimplexVertices σ)).symm


@[simp]
theorem affineStraightening_affineSingularSimplex {n : ℕ} (v : Fin (n + 1) → E) :
    (affineStraightening (E := E)).app (op ⦋n⦌) (affineSingularSimplex v) =
      affineSingularSimplex v := by
  change affineSingularSimplex (singularSimplexVertices (affineSingularSimplex v)) = _
  rw [singularSimplexVertices_affineSingularSimplex]


theorem affineSingularSimplex_vertices_zero (σ : TopCat.toSSet.obj (TopCat.of E) _⦋0⦌) :
    affineSingularSimplex (singularSimplexVertices σ) = σ := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋0⦌)).injective
  ext x
  obtain rfl := Subsingleton.elim x (stdSimplex.vertex (0 : Fin 1))
  exact affineSimplex_vertex _ 0


@[simp]
theorem δ_affineSingularSimplex {n : ℕ} (v : Fin (n + 2) → E) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of E)).δ i (affineSingularSimplex v) =
      affineSingularSimplex (v ∘ i.succAbove) := by
  apply ((TopCat.of E).toSSetObjEquiv (op ⦋n⦌)).injective
  change (affineSimplex v).comp
    ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩ =
      affineSimplex (v ∘ i.succAbove)
  exact affineSimplex_comp_map v i.succAbove


def affineSingularSimplexIn {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) : TopCat.toSSet.obj (TopCat.of s) _⦋n⦌ :=
  ((TopCat.of s).toSSetObjEquiv (op ⦋n⦌)).symm (affineSimplexIn hs v)


theorem affineSingularSimplexIn_inclusion {s : Set E} (hs : Convex ℝ s) {n : ℕ}
    (v : Fin (n + 1) → s) :
    (TopCat.toSSet.map (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(s, E)))).app
      (op ⦋n⦌) (affineSingularSimplexIn hs v) =
        affineSingularSimplex (fun i ↦ (v i : E)) := rfl

end Poincare.Homology
