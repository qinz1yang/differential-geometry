import Poincare.Topology.Homology.LocalCharts
import Poincare.Topology.Manifold.SphereOrientation

noncomputable section

open Bundle ContinuousMap Metric Module Set
open scoped Manifold

universe u

namespace Poincare.Topology

private theorem normalized_local_zero_vertex
    {X E : Type u} [TopologicalSpace X] [T1Space X] [NormedAddCommGroup E]
    (e : OpenPartialHomeomorph X E) (x : X) (hx : x ∈ e.source) :
    integralRelativeHomologyMap 0 (toContinuousMap (Homeomorph.subRight (e x)))
      (show MapsTo (Homeomorph.subRight (e x)) ({e x}ᶜ : Set E) ({0}ᶜ : Set E) from
        fun _ hz => sub_ne_zero.mpr hz)
      ((integralLocalHomologyOpenPartialHomeomorphIso 0 e x hx).hom.hom
        (integralAbsoluteToRelative 0 ({x}ᶜ : Set X)
          (integralZeroChainClass (integralVertexChain x)))) =
      integralAbsoluteToRelative 0 ({0}ᶜ : Set E)
        (integralZeroChainClass (integralVertexChain (0 : E))) := by
  rw [integralLocalHomologyOpenPartialHomeomorphIso_zero_vertex]
  have h := integralRelativeHomologyMap_zero_vertex
    (toContinuousMap (Homeomorph.subRight (e x)))
    (show MapsTo (Homeomorph.subRight (e x)) ({e x}ᶜ : Set E) ({0}ᶜ : Set E) from
      fun _ hz => sub_ne_zero.mpr hz) (e x)
  change _ = integralAbsoluteToRelative 0 ({0}ᶜ : Set E)
    (integralZeroChainClass (integralVertexChain (e x - e x))) at h
  simpa only [sub_self] using h

local instance : Fact (finrank ℝ ℝ = 0 + 1) := ⟨by simp⟩

private theorem real_unit_sphere_eq_positive_or_negative (x : sphere (0 : ℝ) 1) :
    x = (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1) ∨
      x = (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1) := by
  have h : |(x : ℝ)| = 1 := by
    simpa only [mem_sphere, dist_zero_right, Real.norm_eq_abs] using x.property
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

open Classical in
theorem zero_sphere_boundary_class_outward_chart_maps
    (p x : sphere (0 : ℝ) 1)
    (hx : x ∈ (chartAt (EuclideanSpace ℝ (Fin 0)) p).source) :
    integralRelativeHomologyMap 0
      (toContinuousMap (Homeomorph.subRight (chartAt (EuclideanSpace ℝ (Fin 0)) p x)))
      (show MapsTo (Homeomorph.subRight (chartAt (EuclideanSpace ℝ (Fin 0)) p x))
        ({chartAt (EuclideanSpace ℝ (Fin 0)) p x}ᶜ : Set (EuclideanSpace ℝ (Fin 0)))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) from fun _ hz => sub_ne_zero.mpr hz)
      ((integralLocalHomologyOpenPartialHomeomorphIso 0
        (chartAt (EuclideanSpace ℝ (Fin 0)) p) x hx).hom.hom
        (integralAbsoluteToRelative 0 ({x}ᶜ : Set (sphere (0 : ℝ) 1))
          (integralZeroChainClass (integralVertexChain
            (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)) -
          integralZeroChainClass (integralVertexChain
            (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))))) =
    if Orientation.map (Fin 0)
      ((trivializationAt (EuclideanSpace ℝ (Fin 0)) (TangentSpace (𝓡 0)) p).continuousLinearEquivAt ℝ x
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)).toLinearEquiv
      (sphereOutwardOrientation 0 (Basis.singleton (Fin 1) ℝ).orientation x) =
        positiveOrientation then
      integralAbsoluteToRelative 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0)))
        (integralZeroChainClass (integralVertexChain (0 : EuclideanSpace ℝ (Fin 0))))
    else -integralAbsoluteToRelative 0 ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0)))
      (integralZeroChainClass (integralVertexChain (0 : EuclideanSpace ℝ (Fin 0)))) := by
  let N : integralLocalHomology 0 x →ₗ[ℤ]
      integralLocalHomology 0 (0 : EuclideanSpace ℝ (Fin 0)) :=
    (integralRelativeHomologyMap 0
      (toContinuousMap (Homeomorph.subRight (chartAt (EuclideanSpace ℝ (Fin 0)) p x)))
      (show MapsTo (Homeomorph.subRight (chartAt (EuclideanSpace ℝ (Fin 0)) p x))
        ({chartAt (EuclideanSpace ℝ (Fin 0)) p x}ᶜ : Set (EuclideanSpace ℝ (Fin 0)))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 0))) from fun _ hz => sub_ne_zero.mpr hz)).comp
      (integralLocalHomologyOpenPartialHomeomorphIso 0
        (chartAt (EuclideanSpace ℝ (Fin 0)) p) x hx).hom.hom
  change N (integralAbsoluteToRelative 0 ({x}ᶜ : Set (sphere (0 : ℝ) 1))
    (integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)) -
      integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)))) = _
  rcases real_unit_sphere_eq_positive_or_negative x with rfl | rfl
  · rw [sphereOutwardOrientation_real_positive,
      Orientation.map_positiveOrientation_of_isEmpty, if_pos rfl]
    have hother : (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1) ∈
        ({(⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1)) := by
      intro h
      have hval := congrArg (fun y : sphere (0 : ℝ) 1 => (y : ℝ)) h
      norm_num at hval
    have hclass : integralAbsoluteToRelative 0
        ({(⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
        (integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)) -
          integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))) =
      integralAbsoluteToRelative 0
        ({(⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
        (integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1))) := by
      let F : integralSingularHomology 0 (sphere (0 : ℝ) 1) →ₗ[ℤ]
          integralLocalHomology 0 (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1) :=
        integralAbsoluteToRelative 0
          ({(⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
      let a : integralSingularHomology 0 (sphere (0 : ℝ) 1) :=
        integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1))
      let b : integralSingularHomology 0 (sphere (0 : ℝ) 1) :=
        integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))
      have hb : F b = 0 := integralAbsoluteToRelative_zero_vertex_of_mem _ _ hother
      exact (map_sub F a b).trans ((congrArg
        (fun z => F a - z)
        hb).trans (sub_zero (F a)))
    exact (congrArg N hclass).trans (normalized_local_zero_vertex _ _ hx)
  · have hneg : (-positiveOrientation : Orientation ℝ (EuclideanSpace ℝ (Fin 0)) (Fin 0)) ≠
        positiveOrientation :=
      Ne.symm (Module.Ray.ne_neg_self
        (positiveOrientation : Orientation ℝ (EuclideanSpace ℝ (Fin 0)) (Fin 0)))
    rw [sphereOutwardOrientation_real_negative, Orientation.map_neg,
      Orientation.map_positiveOrientation_of_isEmpty, if_neg hneg]
    have hother : (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1) ∈
        ({(⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1)) := by
      intro h
      have hval := congrArg (fun y : sphere (0 : ℝ) 1 => (y : ℝ)) h
      norm_num at hval
    have hclass : integralAbsoluteToRelative 0
        ({(⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
        (integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1)) -
          integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))) =
      -integralAbsoluteToRelative 0
        ({(⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
        (integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))) := by
      let F : integralSingularHomology 0 (sphere (0 : ℝ) 1) →ₗ[ℤ]
          integralLocalHomology 0 (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1) :=
        integralAbsoluteToRelative 0
          ({(⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1)}ᶜ : Set (sphere (0 : ℝ) 1))
      let a : integralSingularHomology 0 (sphere (0 : ℝ) 1) :=
        integralZeroChainClass (integralVertexChain (⟨1, by norm_num⟩ : sphere (0 : ℝ) 1))
      let b : integralSingularHomology 0 (sphere (0 : ℝ) 1) :=
        integralZeroChainClass (integralVertexChain (⟨-1, by norm_num⟩ : sphere (0 : ℝ) 1))
      have ha : F a = 0 := integralAbsoluteToRelative_zero_vertex_of_mem _ _ hother
      exact (map_sub F a b).trans ((congrArg
        (fun z => z - F b)
        ha).trans (zero_sub (F b)))
    exact (congrArg N hclass).trans ((map_neg N _).trans
      (congrArg Neg.neg (normalized_local_zero_vertex _ _ hx)))

end Poincare.Topology

end
