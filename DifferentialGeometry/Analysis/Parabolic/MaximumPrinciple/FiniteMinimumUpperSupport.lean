import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Weak

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Analysis.Parabolic

open Bundle Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [CompleteSpace E] in
theorem finite_minimum_barrier_nonneg_of_negative_supersolution
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (X : Real -> (x : M) -> TangentSpace I x)
    (u : ι -> Real -> M -> Real)
    (hu_cont : ∀ i : ι,
      ContinuousOn (fun p : Real × M => u i p.1 p.2) (spacetimeSlab (M := M) T))
    (hu_time : ∀ i : ι, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M,
        DifferentiableWithinAt Real (fun s : Real => u i s x) (Set.Icc 0 T) t)
    (hu_space_nhds : ∀ i : ι, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M,
        ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) (u i t) y)
    (hu_grad : ∀ i : ι, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M,
        MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u i t) y) x)
    (hu_super : ∀ i : ι, ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M, u i t x ≤ 0 ->
        0 ≤ parabolicOperatorWithDrift (I := I) G T X (u i) t x)
    (hinit : ∀ x : M,
      0 ≤ (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i : ι => u i 0 x)) :
    ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      0 ≤ (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i : ι => u i t x) := by
  classical
  let w : Real -> M -> Real := fun t x =>
    (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i : ι => u i t x)
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hcont0 :=
      ContinuousOn.finset_inf'_apply (s := (Finset.univ : Finset ι))
        (hne := Finset.univ_nonempty)
        (f := fun i : ι => fun p : Real × M => u i p.1 p.2)
        (t := spacetimeSlab (M := M) T) (by
          intro i hi
          exact hu_cont i)
    simpa [w, Function.comp_def] using hcont0
  have hw_out : ∀ t : Real, t ∈ Set.Icc 0 T -> ∀ x : M,
      x ∉ (Set.univ : Set M) -> 0 ≤ w t x := by
    intro t ht x hx
    simp at hx
  have hsupport : ∀ t : Real, t ∈ Set.Icc 0 T -> 0 < t ->
      ∀ x : M, w t x < 0 ->
        ParabolicUpperSupportAt (I := I) G T X w t x := by
    intro t ht htpos x hneg
    let exist : ∃ i, i ∈ (Finset.univ : Finset ι) ∧
        (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun i : ι => u i t x) = u i t x :=
      Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset ι))
        (H := Finset.univ_nonempty) (f := fun i : ι => u i t x)
    let i : ι := Classical.choose exist
    have hi_mem : i ∈ (Finset.univ : Finset ι) := (Classical.choose_spec exist).1
    have hi_eq : (Finset.univ : Finset ι).inf' Finset.univ_nonempty (fun j : ι => u j t x) =
        u i t x := (Classical.choose_spec exist).2
    have hi_neg : u i t x < 0 := by
      rw [← hi_eq]
      exact hneg
    refine ⟨u i, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · dsimp [w]
      rw [hi_eq]
    · refine Filter.Eventually.of_forall ?_
      intro p
      dsimp [w]
      exact Finset.inf'_le (s := (Finset.univ : Finset ι))
        (f := fun j : ι => u j p.1 p.2) (Finset.mem_univ i)
    · exact hu_time i t ht htpos x
    · exact hu_space_nhds i t ht htpos x
    · exact hu_grad i t ht htpos x
    · exact hu_super i t ht htpos x (le_of_lt hi_neg)
  have hmain := strict_barrier_cpt_of_upperSupport (I := I)
    (G := G) (T := T) (X := X) (w := w) (K := (Set.univ : Set M))
    isCompact_univ hw_out hw_cont (by
      intro x
      simpa [w] using hinit x) hsupport
  intro t ht x
  simpa [w] using hmain t ht x

end DifferentialGeometry.Analysis.Parabolic
