import DifferentialGeometry.Topology.Homology.ConeTriangleHomotopy
import DifferentialGeometry.Topology.Simplex.MapInjectivity

noncomputable section

namespace DifferentialGeometry.Topology

open CategoryTheory AlgebraicTopology
open Convexity.StdSimplex (coordinateSet coordinateMap continuous_coordinateMap
  coordinateHomeomorph coordinateHomeomorphI coordinateEquiv coordinateEquiv_map
  coordinateMap_comp_apply)
open scoped Simplicial

universe u

variable {ι : Type*} [Fintype ι] [Preorder ι]
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

private def simplexRestriction (n : ℕ) (τ : C(coordinateSet ℝ ι, X))
    (f : Fin (n + 1) → ι) : integralSingularSimplex n X :=
  (integralSingularSimplexEquiv n X).symm
    ((τ.comp ⟨coordinateMap f, continuous_coordinateMap f⟩).comp
      ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩)

omit [Preorder ι] [SimplyConnectedSpace X] in
private theorem simplexRestriction_apply (n : ℕ) (τ : C(coordinateSet ℝ ι, X))
    (f : Fin (n + 1) → ι) (p : coordinateSet ℝ (Fin (n + 1))) :
    integralSingularSimplexEquiv n X (simplexRestriction n τ f)
        ((coordinateHomeomorph ℝ (Fin (n + 1))).symm p) =
      τ (coordinateMap f p) := by
  change ((integralSingularSimplexEquiv n X)
    ((integralSingularSimplexEquiv n X).symm _)) _ = _
  rw [Equiv.apply_symm_apply]
  change τ (coordinateMap f ((coordinateEquiv ℝ _)
    ((coordinateEquiv ℝ _).symm p))) = _
  rw [Equiv.apply_symm_apply]

omit [Preorder ι] [SimplyConnectedSpace X] in
private theorem simplexRestriction_face (n : ℕ) (τ : C(coordinateSet ℝ ι, X))
    (f : Fin (n + 2) → ι) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplexRestriction (n + 1) τ f) =
      simplexRestriction n τ (f ∘ i.succAbove) := by
  apply (integralSingularSimplexEquiv n X).injective
  apply ContinuousMap.ext
  intro p
  change (TopCat.of X).toSSetObjEquiv _
    ((TopCat.toSSet.obj (TopCat.of X)).δ i (simplexRestriction (n + 1) τ f)) p = _
  rw [TopCat.toSSetObjEquiv_δ_apply]
  change integralSingularSimplexEquiv (n + 1) X (simplexRestriction (n + 1) τ f)
    (Convexity.StdSimplex.map i.succAbove p) = _
  simp only [simplexRestriction, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  change τ (coordinateMap f
      (coordinateEquiv ℝ _ (Convexity.StdSimplex.map i.succAbove p))) =
    τ (coordinateMap (f ∘ i.succAbove) (coordinateEquiv ℝ _ p))
  rw [coordinateEquiv_map, coordinateMap_comp_apply]

private theorem eq_or_boundary_of_map_eq {n : ℕ} {f g : Fin (n + 1) → ι}
    (hf : StrictMono f) (hg : StrictMono g)
    {p q : coordinateSet ℝ (Fin (n + 1))} (h : coordinateMap f p = coordinateMap g q) :
    (f = g ∧ p = q) ∨ (p ∈ Simplex.boundary (Fin (n + 1)) ∧
      q ∈ Simplex.boundary (Fin (n + 1))) := by
  classical
  by_cases hp : p ∈ Simplex.boundary (Fin (n + 1))
  · by_cases hq : q ∈ Simplex.boundary (Fin (n + 1))
    · exact Or.inr ⟨hp, hq⟩
    · obtain ⟨hgf, hqp⟩ := stdSimplex.eq_and_eq_of_map_eq_of_strictMono hg hf
        (fun j hj => hq ⟨j, hj⟩) h.symm
      exact Or.inl ⟨hgf.symm, hqp.symm⟩
  · exact Or.inl (stdSimplex.eq_and_eq_of_map_eq_of_strictMono hf hg
      (fun j hj => hp ⟨j, hj⟩) h)

private theorem edge_overlap (x : X) (τ : C(coordinateSet ℝ ι, X))
    {f g : Fin 2 → ι} (hf : StrictMono f) (hg : StrictMono g)
    (t : unitInterval) (p q : coordinateSet ℝ (Fin 2))
    (h : coordinateMap f p = coordinateMap g q) :
    integralSingularConeEdgeHomotopy x (simplexRestriction 1 τ f)
        (t, coordinateHomeomorphI p) =
      integralSingularConeEdgeHomotopy x (simplexRestriction 1 τ g)
        (t, coordinateHomeomorphI q) := by
  obtain ⟨rfl, rfl⟩ | ⟨hp, hq⟩ := eq_or_boundary_of_map_eq hf hg h
  · rfl
  · rw [integralSingularConeEdgeHomotopy_boundary x _ p hp,
      integralSingularConeEdgeHomotopy_boundary x _ q hq,
      simplexRestriction_apply, simplexRestriction_apply, h]

theorem integralSingularConeTriangleHomotopy_comp_map_eq (x : X)
    [Subsingleton (HomotopyGroup (Fin 2) X x)] (τ : C(coordinateSet ℝ ι, X))
    {f g : Fin 3 → ι} (hf : StrictMono f) (hg : StrictMono g)
    (t : unitInterval) (p q : coordinateSet ℝ (Fin 3))
    (h : coordinateMap f p = coordinateMap g q) :
    integralSingularConeTriangleHomotopy x
        ((integralSingularSimplexEquiv 2 X).symm
          ((τ.comp ⟨coordinateMap f, continuous_coordinateMap f⟩).comp
      ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩)) (t, p) =
      integralSingularConeTriangleHomotopy x
        ((integralSingularSimplexEquiv 2 X).symm
          ((τ.comp ⟨coordinateMap g, continuous_coordinateMap g⟩).comp
            ⟨coordinateEquiv ℝ _, (coordinateHomeomorph ℝ _).continuous⟩)) (t, q) := by
  change integralSingularConeTriangleHomotopy x (simplexRestriction 2 τ f) (t, p) =
    integralSingularConeTriangleHomotopy x (simplexRestriction 2 τ g) (t, q)
  obtain ⟨rfl, rfl⟩ | ⟨hp, hq⟩ := eq_or_boundary_of_map_eq hf hg h
  · rfl
  · obtain ⟨i, hi⟩ := hp
    obtain ⟨j, hj⟩ := hq
    let p' := Simplex.faceDelete i ⟨p, hi⟩
    let q' := Simplex.faceDelete j ⟨q, hj⟩
    have hp' : coordinateMap i.succAbove p' = p :=
      congrArg Subtype.val (Simplex.faceInsert_faceDelete i ⟨p, hi⟩)
    have hq' : coordinateMap j.succAbove q' = q :=
      congrArg Subtype.val (Simplex.faceInsert_faceDelete j ⟨q, hj⟩)
    rw [← hp', ← hq', integralSingularConeTriangleHomotopy_face,
      integralSingularConeTriangleHomotopy_face, simplexRestriction_face, simplexRestriction_face]
    apply edge_overlap x τ (hf.comp (Fin.strictMono_succAbove i))
      (hg.comp (Fin.strictMono_succAbove j)) t p' q'
    rw [← coordinateMap_comp_apply, ← coordinateMap_comp_apply, hp', hq']
    exact h

end DifferentialGeometry.Topology
