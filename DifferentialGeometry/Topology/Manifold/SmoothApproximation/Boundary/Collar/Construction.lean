import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Helpers
import DifferentialGeometry.Topology.VectorField.CollarExtension
import Mathlib.Geometry.Manifold.Instances.Icc

/-!
# The collar straightening map and its regularity

`collarPush cB ret X h rA δ' x` is `cB (ret (X x).1, projIcc (X x).2)` on the collar `{rA < δ'}`
and `h x` elsewhere: `X : A → F × ℝ` is a map in "collar coordinates of `B`" (a point of an
ambient vector space `F ⊇ ∂B` and a height), pushed into `B` by the retraction `ret : F → ∂B` and
the collar `cB` of `B`.

* `contMDiff_collarPush`: if `X` is `C¹` on the collar, smooth on a smaller collar, stays where
  `ret` is smooth and in `[0, aB]`, and reproduces `h` on an outer annulus, then the pushed map is
  `C¹`, smooth on the smaller collar, and equal to `h` off a neighbourhood of `∂A`.
* `straightenModel`, `straightenBlend`: the first-order model `(e (Φ (πA x)), 0) + rA x • w (πA x)`
  and its blend with `g` by `collarTransition (rA / δ)`; `straightenBlend_eq_model`,
  `straightenBlend_eq_target`, `contMDiffOn_straightenBlend`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.VectorField

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

variable {n : ℕ}
  {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
  {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
  [IsManifold (𝓡∂ (n + 1)) ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Push a map in collar coordinates of `B` into `B` on the collar `{rA < δ'}`, `h` elsewhere. -/
def collarPush {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    (cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B)
    (ret : F → BoundaryManifold (𝓡∂ (n + 1)) B) (X : A → F × ℝ) (h : A → B) (rA : A → ℝ)
    (δ' : ℝ) (x : A) : B :=
  if rA x < δ' then cB (ret (X x).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (X x).2) else h x

theorem contMDiffOn_collarPush_aux {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B}
    (hcB : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ cB)
    {ret : F → BoundaryManifold (𝓡∂ (n + 1)) B} {U : Set F}
    (hret : ContMDiffOn 𝓘(ℝ, F) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ ret U)
    {X : A → F × ℝ} {m : ℕ∞} {s : Set A} (hX : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) m X s)
    (hXU : ∀ x ∈ s, (X x).1 ∈ U) (hX2 : ∀ x ∈ s, (X x).2 ∈ Icc 0 aB) :
    ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) m
      (fun x => cB (ret (X x).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (X x).2)) s := by
  have h1 : ContMDiffOn (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) m
      (fun x => ret (X x).1) s :=
    (hret.of_le (by exact_mod_cast le_top)).comp (contDiff_fst.contMDiff.comp_contMDiffOn hX) hXU
  have h2 : ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ 1) m
      (fun x => projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (X x).2) s :=
    contMDiffOn_projIcc.comp (contDiff_snd.contMDiff.comp_contMDiffOn hX) hX2
  exact (hcB.of_le (by exact_mod_cast le_top)).comp_contMDiffOn (h1.prodMk h2)

/-- **Regularity of the pushed map.** -/
theorem contMDiff_collarPush {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B}
    (hcB : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ cB)
    {ret : F → BoundaryManifold (𝓡∂ (n + 1)) B} {U : Set F}
    (hret : ContMDiffOn 𝓘(ℝ, F) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ ret U)
    {X : A → F × ℝ} {h : A → B} (hh : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) 1 h)
    {rA : A → ℝ} (hrA : Continuous rA) {δ₀ δ₁ δ' : ℝ} (hδ₁ : δ₁ < δ')
    (hX1 : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) 1 X {x | rA x < δ'})
    (hXinf : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) ∞ X {x | rA x < δ₀})
    (hXU : ∀ x, rA x < δ' → (X x).1 ∈ U) (hX2 : ∀ x, rA x < δ' → (X x).2 ∈ Icc 0 aB)
    (hXh : ∀ x, δ₁ < rA x → rA x < δ' →
      cB (ret (X x).1, projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (X x).2) = h x) :
    ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) 1 (collarPush cB ret X h rA δ') ∧
      ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) ∞ (collarPush cB ret X h rA δ')
        {x | rA x < min δ₀ δ'} ∧
      ∀ x, δ₁ < rA x → collarPush cB ret X h rA δ' x = h x := by
  have heq : ∀ x, δ₁ < rA x → collarPush cB ret X h rA δ' x = h x := by
    intro x hx
    unfold collarPush
    split_ifs with h'
    · exact hXh x hx h'
    · rfl
  have hopen1 : IsOpen {x | rA x < δ'} := isOpen_lt hrA continuous_const
  have hopen2 : IsOpen {x | δ₁ < rA x} := isOpen_lt continuous_const hrA
  have hon : ∀ (m : ℕ∞) (s : Set A), s ⊆ {x | rA x < δ'} →
      ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) m X s →
      ContMDiffOn (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) m (collarPush cB ret X h rA δ') s := by
    intro m s hs hXs
    refine (contMDiffOn_collarPush_aux hcB hret hXs (fun x hx => hXU x (hs hx))
      (fun x hx => hX2 x (hs hx))).congr fun x hx => ?_
    unfold collarPush
    simp only [show rA x < δ' from hs hx, ite_true]
  refine ⟨fun x => ?_, ?_, heq⟩
  · by_cases hx : rA x < δ'
    · exact (hon 1 _ subset_rfl hX1).contMDiffAt (hopen1.mem_nhds hx)
    · have hx' : δ₁ < rA x := lt_of_lt_of_le hδ₁ (not_lt.mp hx)
      exact (hh.contMDiffAt).congr_of_eventuallyEq
        (Filter.mem_of_superset (hopen2.mem_nhds hx') fun y hy => heq y hy)
  · exact hon (⊤ : ℕ∞) _ (fun x (hx : rA x < min δ₀ δ') => lt_of_lt_of_le hx (min_le_right _ _))
      (hXinf.mono fun x (hx : rA x < min δ₀ δ') => (lt_of_lt_of_le hx (min_le_left _ _) :
        rA x < δ₀))

/-- The blend `M + collarTransition (rA / δ) • (g - M)` of a model `M` with a target `g`. -/
def straightenBlend (rA : A → ℝ) (δ : ℝ) (M g : A → F × ℝ) (x : A) : F × ℝ :=
  M x + collarTransition (rA x / δ) • (g x - M x)

omit [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A] in
theorem straightenBlend_eq_model {rA : A → ℝ} {δ : ℝ} (hδ : 0 < δ) {M g : A → F × ℝ} {x : A}
    (hx : rA x ≤ δ / 3) : straightenBlend rA δ M g x = M x := by
  have h : rA x / δ ≤ 1 / 3 := by rw [div_le_iff₀ hδ]; linarith
  simp [straightenBlend, collarTransition_eq_zero h]

omit [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A] in
theorem straightenBlend_eq_target {rA : A → ℝ} {δ : ℝ} (hδ : 0 < δ) {M g : A → F × ℝ} {x : A}
    (hx : 2 * δ / 3 ≤ rA x) : straightenBlend rA δ M g x = g x := by
  have h : 2 / 3 ≤ rA x / δ := by rw [le_div_iff₀ hδ]; linarith
  simp [straightenBlend, collarTransition_eq_one h]

theorem contMDiffOn_straightenBlend {rA : A → ℝ} (hrA : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ rA)
    (δ : ℝ) {M g : A → F × ℝ} {m : ℕ∞} {s : Set A}
    (hM : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) m M s)
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) m g s) :
    ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, F × ℝ) m (straightenBlend rA δ M g) s := by
  have hρ : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) m (fun x => collarTransition (rA x / δ)) :=
    ((contDiff_collarTransition.of_le (by exact_mod_cast le_top)).contMDiff.comp
      ((hrA.of_le (by exact_mod_cast le_top)).div_const δ))
  exact hM.add (hρ.contMDiffOn.smul (hg.sub hM))

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
