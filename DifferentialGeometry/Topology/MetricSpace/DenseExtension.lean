import Mathlib.Topology.Instances.ENNReal.Lemmas

open Set
open scoped NNReal ENNReal

theorem DenseRange.exists_lipschitz_extension
    {A X Y : Type*} [PseudoEMetricSpace X] [EMetricSpace Y] [CompleteSpace Y]
    {i : A → X} (hi : DenseRange i) (f : A → Y) {K : ℝ≥0}
    (hf : ∀ a b, edist (f a) (f b) ≤ K * edist (i a) (i b)) :
    ∃ g : X → Y, LipschitzWith K g ∧ ∀ a, g (i a) = f a := by
  let : PseudoEMetricSpace A := PseudoEMetricSpace.induced i inferInstance
  have hiso : Isometry i := fun _ _ => rfl
  have hfl : LipschitzWith K f := hf
  let g := (hiso.isUniformInducing.isDenseInducing hi).extend f
  have hg : Continuous g :=
    (uniformContinuous_uniformly_extend hiso.isUniformInducing hi
      hfl.uniformContinuous).continuous
  have heq : ∀ a, g (i a) = f a :=
    uniformly_extend_of_ind hiso.isUniformInducing hi hfl.uniformContinuous
  refine ⟨g, ?_, heq⟩
  intro x y
  apply hi.induction_on₂ (p := fun x y => edist (g x) (g y) ≤ K * edist x y) ?_ ?_ x y
  · exact isClosed_le (by fun_prop)
      ((ENNReal.continuous_const_mul (by simp)).comp (by fun_prop))
  · intro a b
    rw [heq, heq]
    exact hf a b

theorem DenseRange.restrictPreimage_of_isOpen
    {A X : Type*} [TopologicalSpace X] {i : A → X} (hi : DenseRange i)
    {U : Set X} (hU : IsOpen U) : DenseRange (U.restrictPreimage i) := by
  rw [denseRange_iff_closure_range, Set.range_restrictPreimage,
    ← hU.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val, hi.closure_range]
  exact Set.preimage_univ
