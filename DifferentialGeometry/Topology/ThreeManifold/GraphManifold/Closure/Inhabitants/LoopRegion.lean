import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopCornerBase

/-!
The true circle region lifts the actual compact cornered base through the native orbit projection.
It retains the same original rim quadrants and is exactly the shell with its two corner fills.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

def loopCircleLift (A : Set loopCircleBase) : Set SphereCarrier.{0} :=
  Subtype.val '' (loopCircleProjection ⁻¹' A)

def loopCircleRegion : Set SphereCarrier.{0} := loopCircleLift loopCircleCornerBase

theorem loopCircleLift_orbits (A : Set loopCircleBase) :
    loopCircleLift A = loopCircleCoordinates '' ((Subtype.val '' A) ×ˢ Set.univ) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨((loopCircleProjection q).val, (loopCircleBundle q).2),
      ⟨⟨loopCircleProjection q, hq, rfl⟩, trivial⟩, ?_⟩
    exact congrArg Subtype.val (loopCircleBundle.symm_apply_apply q)
  · rintro ⟨⟨w, θ⟩, hw, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hw.1
    refine ⟨loopCircleBundle.symm (z, θ), ?_, rfl⟩
    change (loopCircleBundle (loopCircleBundle.symm (z, θ))).1 ∈ A
    rw [loopCircleBundle.apply_symm_apply]
    exact hz

theorem loopCircleLift_rounded :
    loopCircleLift {z | loopCircleBaseRounding z ≤ 0} = loopRoundedShell := by
  rw [loopCircleLift_orbits]
  have he : Subtype.val '' {z : loopCircleBase | loopCircleBaseRounding z ≤ 0} =
      loopShellBase := by
    rw [← loopShellRounding_sublevel]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, loopShellRounding_source hz⟩, hz, rfl⟩
  rw [he, loopRoundedShell_orbits]

theorem loopCircleRegion_compact : IsCompact loopCircleRegion := by
  have hc : IsCompact (loopCircleCornerBase ×ˢ (Set.univ : Set Circle)) :=
    loopCircleCornerBase_compact.prod isCompact_univ
  have he : loopCircleRegion =
      (fun q : loopCircleBase × Circle => (loopCircleBundle.symm q).val) ''
        (loopCircleCornerBase ×ˢ Set.univ) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨loopCircleBundle q, ⟨hq, trivial⟩,
        congrArg Subtype.val (loopCircleBundle.symm_apply_apply q)⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨loopCircleBundle.symm q, ?_, rfl⟩
      change (loopCircleBundle (loopCircleBundle.symm q)).1 ∈ loopCircleCornerBase
      rw [loopCircleBundle.apply_symm_apply]
      exact hq.1
  rw [he]
  exact hc.image (continuous_subtype_val.comp loopCircleBundle.symm.continuous)

theorem loopRegionRim_domain (b : Bool) (θ : Circle) (v : ℝ × ℝ) (hv : v ∈ rimBox 2) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)
      ∈ loopCircleDomain := by
  have he := congrArg Prod.fst (loopRimOrbit_inverse b θ v hv)
  rw [loopCircleCoordinates_inverse] at he
  have hb := (loopBaseCorner b v).property
  change ‖(loopBaseCorner b v).val‖ < 1 at hb
  rw [loopBaseCorner_val b v hv, loopCornerChart_apply] at hb
  dsimp only [Prod.fst] at he
  rw [← he, modelPlaneComplex.symm.norm_map] at hb
  change sphereFirst _ ≠ 0
  intro hz
  have hh := norm_sphereFirst_sq_add
    (standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v))
  rw [hz, norm_zero, zero_pow (by decide), zero_add] at hh
  nlinarith [norm_nonneg (sphereSecond
    (standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)))]

theorem loopRegionRim_projection (b : Bool) (θ : Circle) (v : ℝ × ℝ)
    (hv : v ∈ rimBox 2) :
    loopCircleProjection ⟨standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v), loopRegionRim_domain b θ v hv⟩ =
    loopBaseCorner b v := by
  apply Subtype.ext
  rw [loopCircleProjection_val, loopBaseCorner_val b v hv, loopCornerChart_apply]
  have he := congrArg Prod.fst (loopRimOrbit_inverse b θ v hv)
  rw [loopCircleCoordinates_inverse] at he
  exact he

theorem loopCircleRegion_rim (b : Bool) (θ : Circle) {v : ℝ × ℝ} (hv : v ∈ rimBox 2) :
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v)
      ∈ loopCircleRegion ↔ 0 ≤ v.1 ∧ 0 ≤ v.2 := by
  rw [← loopCircleCornerBase_chart b hv]
  constructor
  · rintro ⟨q, hq, he⟩
    have hqeq : q = ⟨standardLoopBallHandleCycle.rimChart
        ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v),
        loopRegionRim_domain b θ v hv⟩ := Subtype.ext he
    rw [hqeq] at hq
    change loopCircleProjection _ ∈ loopCircleCornerBase at hq
    rw [loopRegionRim_projection b θ v hv] at hq
    exact hq
  · intro hz
    refine ⟨⟨standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b (θ, v),
      loopRegionRim_domain b θ v hv⟩, ?_, rfl⟩
    change loopCircleProjection _ ∈ loopCircleCornerBase
    rw [loopRegionRim_projection b θ v hv]
    exact hz

theorem loopCircleLift_fill (b : Bool) :
    loopCircleLift (loopBaseCorner b '' loopCornerFill) =
    standardLoopBallHandleCycle.rimChart ⟨0, standardLoopBallHandleCycle.len_pos⟩ b ''
      (Set.univ ×ˢ loopCornerFill) := by
  rw [loopCircleLift_orbits]
  ext p
  constructor
  · rintro ⟨⟨w, θ⟩, hw, rfl⟩
    obtain ⟨z, ⟨v, hv, rfl⟩, rfl⟩ := hw.1
    refine ⟨(θ, v), ⟨trivial, hv⟩, ?_⟩
    have hs := loopCornerFill_source hv
    have hi := loopRimOrbit_inverse b θ v hs
    rw [← loopCornerChart_apply, ← loopBaseCorner_val b v hs] at hi
    exact (loopCircleCoordinates.right_inv (loopRegionRim_domain b θ v hs)).symm.trans
      (congrArg loopCircleCoordinates hi)
  · rintro ⟨⟨θ, v⟩, hv, rfl⟩
    have hs := loopCornerFill_source hv.2
    refine ⟨((loopBaseCorner b v).val, θ),
      ⟨⟨loopBaseCorner b v, ⟨v, hv.2, rfl⟩, rfl⟩, trivial⟩, ?_⟩
    have hi := loopRimOrbit_inverse b θ v hs
    rw [← loopCornerChart_apply, ← loopBaseCorner_val b v hs] at hi
    exact (congrArg loopCircleCoordinates hi).symm.trans
      (loopCircleCoordinates.right_inv (loopRegionRim_domain b θ v hs))

theorem loopCircleRegion_shell_fills : loopCircleRegion = loopRoundedShell ∪
    ⋃ b : Bool, standardLoopBallHandleCycle.rimChart
      ⟨0, standardLoopBallHandleCycle.len_pos⟩ b '' (Set.univ ×ˢ loopCornerFill) := by
  have hu (A B : Set loopCircleBase) :
      loopCircleLift (A ∪ B) = loopCircleLift A ∪ loopCircleLift B := by
    simp only [loopCircleLift, preimage_union, image_union]
  have hi (A : Bool → Set loopCircleBase) :
      loopCircleLift (⋃ b, A b) = ⋃ b, loopCircleLift (A b) := by
    simp only [loopCircleLift, preimage_iUnion, image_iUnion]
  rw [loopCircleRegion, loopCircleCornerBase, hu, loopCircleLift_rounded, hi]
  simp_rw [loopCircleLift_fill]


theorem loopCircleRegion_cover :
    (((⋃ k, Set.range (standardLoopBallHandleCycle.ball k).map) ∪
      ⋃ k, Set.range (standardLoopBallHandleCycle.handle k).map) ∪
      Set.range loopComplementVertex.map) ∪ loopCircleRegion = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  have hc : p ∈ solidTorusSet.{0} ∪ loopRoundedShell ∪
      Set.range loopComplementVertex.map := by rw [loopRoundedShell_cover]; trivial
  rcases hc with (ht | hs) | hk
  · rw [← standardLoopBallHandleCycle_union,
      standardLoopBallHandleCycle.range_union_eq] at ht
    rcases ht with hr | hf
    · exact Or.inl (Or.inl hr)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hf
      obtain ⟨b, q, hq, rfl⟩ := mem_iUnion.mp hk
      have hk0 : k = ⟨0, standardLoopBallHandleCycle.len_pos⟩ := by
        apply Fin.ext
        change k.val = 0
        have h := k.isLt
        change k.val < 1 at h
        omega
      subst k
      right
      rw [loopCircleRegion_shell_fills]
      right
      refine mem_iUnion.mpr ⟨b, ⟨q, ⟨trivial, ?_⟩, rfl⟩⟩
      exact ⟨⟨⟨hq.1.le, (abs_lt.mp hq.2.2.1.1).2.le⟩,
        ⟨hq.2.1.le, (abs_lt.mp hq.2.2.1.2).2.le⟩⟩, hq.2.2.2⟩
  · right
    rw [loopCircleRegion_shell_fills]
    exact Or.inl hs
  · exact Or.inl (Or.inr hk)

end GC.GraphManifold.Assembly
