import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation

open Set Topology

namespace DifferentialGeometry.Topology

universe u

theorem continuous_affineInterpolate (F : ℝ → ℝ) (hc : Continuous F) (s : ℝ) :
    Continuous (fun t : ℝ => (1 - s) * F t + s * t) :=
  (continuous_const.mul hc).add (continuous_const.mul continuous_id)

theorem affineInterpolate_periodic (F : ℝ → ℝ) (hp : ∀ t, F (t + 1) = F t + 1) (s : ℝ) :
    ∀ t, (1 - s) * F (t + 1) + s * (t + 1) = (1 - s) * F t + s * t + 1 := by
  intro t
  rw [hp]
  ring

theorem freeLoop_comp_affineCircleMap_homotopic {X : Type u} [TopologicalSpace X]
    (γ : freeLoop X) (F : ℝ → ℝ) (hc : Continuous F) (hp : ∀ t, F (t + 1) = F t + 1) :
    (γ.comp (affineCircleMap F hc hp)).Homotopic γ := by
  refine ⟨⟨⟨fun z : unitInterval × loopCircle =>
      γ (affineCircleMap (fun t => (1 - (z.1 : ℝ)) * F t + (z.1 : ℝ) * t)
        (continuous_affineInterpolate F hc _) (affineInterpolate_periodic F hp _) z.2), ?_⟩,
    ?_, ?_⟩⟩
  · apply (unitInterval_to_loopCircle_prod_quotient unitInterval).continuous_iff.mpr
    exact γ.continuous.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (hc.comp (continuous_subtype_val.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd))))
  · intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change γ (((1 - ((0 : unitInterval) : ℝ)) * F t + ((0 : unitInterval) : ℝ) * t : ℝ) :
      loopCircle) = γ ((F t : ℝ) : loopCircle)
    norm_num
  · intro θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    change γ (((1 - ((1 : unitInterval) : ℝ)) * F t + ((1 : unitInterval) : ℝ) * t : ℝ) :
      loopCircle) = γ ((t : ℝ) : loopCircle)
    norm_num

def negLoopCircle : C(loopCircle, loopCircle) := ⟨fun θ => -θ, continuous_neg⟩

theorem comp_negLoopCircle_zero {X : Type u} [TopologicalSpace X] (γ : freeLoop X) :
    (γ.comp negLoopCircle) 0 = γ 0 := by
  change γ (-(0 : loopCircle)) = γ 0
  rw [neg_zero]

theorem circleToPath_comp_negLoopCircle {X : Type u} [TopologicalSpace X] (γ : freeLoop X) :
    circleToPath (⟨γ.comp negLoopCircle, comp_negLoopCircle_zero γ⟩ :
        basedCircleLoop (γ 0)) =
      (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0))).symm := by
  ext t
  change γ (-((t : ℝ) : loopCircle)) = γ (((1 - (t : ℝ) : ℝ)) : loopCircle)
  have harith : (1 : ℝ) - (t : ℝ) = -(t : ℝ) + 1 := by ring
  rw [harith, AddCircle.coe_add, AddCircle.coe_period, add_zero, QuotientAddGroup.mk_neg]

theorem conjugacyClass_comp_negLoopCircle {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (γ : freeLoop X) {x : X} (q : Path x (γ 0)) :
    FreeLoop.conjugacyClass (γ.comp negLoopCircle) x =
      ConjClasses.mk (loopRepresentativeAlong q (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))⁻¹ := by
  have hmk := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q
    (⟨γ.comp negLoopCircle, comp_negLoopCircle_zero γ⟩ : basedCircleLoop (γ 0))
  rw [hmk]
  congr 1
  unfold loopRepresentativeAlong basedCircleFundamentalGroupClass
  rw [circleToPath_comp_negLoopCircle γ, ← map_inv]
  rfl

theorem conjugacyClassMeets_mk_inv_of {G : Type*} [Group G] {g : G} {N : Subgroup G}
    (h : conjugacyClassMeets (ConjClasses.mk g) N) :
    conjugacyClassMeets (ConjClasses.mk g⁻¹) N := by
  obtain ⟨r, hr, hrN⟩ := h
  have hconj : IsConj g r :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp hr).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine ⟨r⁻¹, ConjClasses.mem_carrier_iff_mk_eq.mpr ?_, N.inv_mem hrN⟩
  refine ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨c⁻¹, ?_⟩)
  rw [← hc]
  group

theorem conjugacyClassMeets_mk_inv_iff {G : Type*} [Group G] (g : G) (N : Subgroup G) :
    conjugacyClassMeets (ConjClasses.mk g⁻¹) N ↔ conjugacyClassMeets (ConjClasses.mk g) N := by
  refine ⟨fun h => ?_, conjugacyClassMeets_mk_inv_of⟩
  have := conjugacyClassMeets_mk_inv_of h
  rwa [inv_inv] at this

theorem loopClassMeets_comp_negLoopCircle_iff {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (γ : freeLoop X) (x : X) (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets (γ.comp negLoopCircle) x N ↔ loopClassMeets γ x N := by
  have hq : Path x (γ 0) := PathConnectedSpace.somePath x (γ 0)
  have hneg := conjugacyClass_comp_negLoopCircle γ hq
  have hpos := FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong hq
    (⟨γ, rfl⟩ : basedCircleLoop (γ 0))
  unfold loopClassMeets
  rw [hneg, hpos]
  exact conjugacyClassMeets_mk_inv_iff _ N

theorem loopClassMeets_comp_circleHomeomorph_iff {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (γ : freeLoop X) (ψ : loopCircle ≃ₜ loopCircle) (x : X)
    (N : Subgroup (FundamentalGroup X x)) :
    loopClassMeets (γ.comp ⟨ψ, ψ.continuous⟩) x N ↔ loopClassMeets γ x N := by
  rcases circleHomeomorph_affineLift_or_neg ψ with ⟨F, hp, -, hψ⟩ | ⟨F, hp, -, hψ⟩
  · have heq : γ.comp ⟨ψ, ψ.continuous⟩ = γ.comp (affineCircleMap F F.continuous hp) := by
      ext θ
      exact congrArg γ (hψ θ)
    unfold loopClassMeets
    rw [heq, FreeLoop.conjugacyClass_eq_of_homotopic
      (freeLoop_comp_affineCircleMap_homotopic γ F F.continuous hp) x]
  · have heq : γ.comp ⟨ψ, ψ.continuous⟩ =
        (γ.comp negLoopCircle).comp (affineCircleMap F F.continuous hp) := by
      ext θ
      exact congrArg γ (hψ θ)
    rw [heq]
    rw [show loopClassMeets ((γ.comp negLoopCircle).comp (affineCircleMap F F.continuous hp))
        x N = loopClassMeets (γ.comp negLoopCircle) x N from by
      unfold loopClassMeets
      rw [FreeLoop.conjugacyClass_eq_of_homotopic
        (freeLoop_comp_affineCircleMap_homotopic (γ.comp negLoopCircle) F F.continuous hp) x]]
    exact loopClassMeets_comp_negLoopCircle_iff γ x N

end DifferentialGeometry.Topology
