import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Orientation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationOpen

set_option autoImplicit false

noncomputable section

open Manifold
open TopologicalSpace (Opens)
open scoped Manifold ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

open DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem tangentOrientationEquiv_eq_iff_of_isPreconnected
    (Φ : _root_.PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    (oM : SmoothOrientation I M) (oN : SmoothOrientation J N)
    {s : Set M} (hs : IsPreconnected s) (hsource : s ⊆ Φ.source)
    {x y : M} (hx : x ∈ s) (hy : y ∈ s) :
    (tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt I J ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (oM.val x) = oN.val (Φ x)) ↔
    (tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt I J ∞ (hsource hy)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (oM.val y) = oN.val (Φ y)) := by
  let U : Opens M := ⟨Φ.source, Φ.open_source⟩
  let hU : (U : Set M) ⊆ Φ.source := fun _ hz => hz
  let a : s → U := fun z => ⟨z.val, hsource z.property⟩
  have ha : Continuous a := continuous_subtype_val.subtype_mk _
  let o₁ := restrictSmoothOrientation I U oM
  let o₂ := pullbackSmoothOrientation Φ hU oN
  have hconstant := (smoothOrientation_agreement_locallyConstant I o₁ o₂).comp_continuous ha
  let : PreconnectedSpace s := Subtype.preconnectedSpace hs
  have heq := hconstant.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨y, hy⟩
  have hpoint (z : s) : (o₁.val (a z) = o₂.val (a z)) ↔
      (tangentOrientationEquiv
        ((Φ.isLocalDiffeomorphAt I J ∞ (hsource z.property)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv (oM.val z.val) = oN.val (Φ z.val)) := by
    rw [← pullbackSmoothOrientation_pushforward Φ hU oN (a z)]
    exact (tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt I J ∞ (hsource z.property)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv).injective.eq_iff.symm
  exact (hpoint ⟨x, hx⟩).symm.trans ((Iff.of_eq heq).trans (hpoint ⟨y, hy⟩))

end DifferentialGeometry.PartialDiffeomorph

namespace DifferentialGeometry.PartialDiffeomorph

open DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
variable {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem tangentOrientationEquiv_eq_or_eq_neg_of_isPreconnected
    (Φ : _root_.PartialDiffeomorph I J M N (∞ : WithTop ℕ∞))
    (oM : SmoothOrientation I M) (oN : SmoothOrientation J N)
    {s : Set M} (hs : IsPreconnected s) (hsource : s ⊆ Φ.source) :
    (∀ (x : M) (hx : x ∈ s), tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt I J ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (oM.val x) = oN.val (Φ x)) ∨
    (∀ (x : M) (hx : x ∈ s), tangentOrientationEquiv
      ((Φ.isLocalDiffeomorphAt I J ∞ (hsource hx)).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv (oM.val x) = -oN.val (Φ x)) := by
  rcases s.eq_empty_or_nonempty with hempty | ⟨p, hp⟩
  · left
    intro x hx
    simp only [hempty, Set.mem_empty_iff_false] at hx
  · let : FiniteDimensional ℝ (TangentSpace J (Φ p)) :=
      inferInstanceAs (FiniteDimensional ℝ F)
    rcases Orientation.eq_or_eq_neg
      (tangentOrientationEquiv
        ((Φ.isLocalDiffeomorphAt I J ∞ (hsource hp)).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv (oM.val p)) (oN.val (Φ p)) (by simp) with hpos | hneg
    · left
      intro x hx
      exact (tangentOrientationEquiv_eq_iff_of_isPreconnected Φ oM oN hs hsource hp hx).mp hpos
    · right
      intro x hx
      exact (tangentOrientationEquiv_eq_iff_of_isPreconnected Φ oM (negSmoothOrientation J oN)
        hs hsource hp hx).mp hneg

end DifferentialGeometry.PartialDiffeomorph
