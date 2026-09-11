import DifferentialGeometry.Topology.ProjectiveSpace.SphereQuotient

set_option autoImplicit false

noncomputable section

open Metric Topology

namespace DifferentialGeometry.ProjectiveSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


def coordinateInclusion : Projectivization ℝ E → Projectivization ℝ (E × ℝ) :=
  Projectivization.map (LinearMap.inl ℝ E ℝ) (fun _ _ h ↦ congrArg Prod.fst h)


@[simp]
theorem coordinateInclusion_mk (v : E) (hv : v ≠ 0) :
    coordinateInclusion (Projectivization.mk ℝ v hv) =
      Projectivization.mk ℝ (v, (0 : ℝ)) (fun h ↦ hv (congrArg Prod.fst h)) := rfl


@[fun_prop]
theorem continuous_coordinateInclusion : Continuous (coordinateInclusion (E := E)) :=
  continuous_map _ _ (ContinuousLinearMap.inl ℝ E ℝ).continuous


theorem coordinateInclusion_injective : Function.Injective (coordinateInclusion (E := E)) :=
  Projectivization.map_injective _ _


theorem isClosedEmbedding_coordinateInclusion [FiniteDimensional ℝ E] :
    IsClosedEmbedding (coordinateInclusion (E := E)) :=
  continuous_coordinateInclusion.isClosedEmbedding coordinateInclusion_injective

omit [NormedSpace ℝ E] in
private theorem diskVector_ne_zero (v : E) : (v, 1 - ‖v‖) ≠ (0 : E × ℝ) := by
  intro h
  have hv : v = 0 := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  simp [hv] at ht


def diskCharacteristicMap (v : closedBall (0 : E) 1) : Projectivization ℝ (E × ℝ) :=
  Projectivization.mk ℝ (v.val, 1 - ‖v.val‖) (diskVector_ne_zero v.val)


@[fun_prop]
theorem continuous_diskCharacteristicMap : Continuous (diskCharacteristicMap (E := E)) :=
  (continuous_mk' ℝ (E × ℝ)).comp
    ((continuous_subtype_val.prodMk (continuous_const.sub continuous_subtype_val.norm)).subtype_mk _)

theorem diskCharacteristicMap_sphere (v : sphere (0 : E) 1) :
    diskCharacteristicMap ⟨v.val, sphere_subset_closedBall v.prop⟩ =
      coordinateInclusion (sphereProjection v) := by
  change Projectivization.mk ℝ ((v : E), 1 - ‖(v : E)‖) _ =
    Projectivization.mk ℝ ((v : E), (0 : ℝ)) _
  congr 1
  exact Prod.ext rfl (by simp [mem_sphere_zero_iff_norm.mp v.prop])


theorem diskCharacteristicMap_eq_iff (x y : closedBall (0 : E) 1) :
    diskCharacteristicMap x = diskCharacteristicMap y ↔
      x = y ∨ ‖(x : E)‖ = 1 ∧ (x : E) = -(y : E) := by
  rw [diskCharacteristicMap, diskCharacteristicMap, Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩
    have hv : a • (y : E) = (x : E) := congrArg Prod.fst ha
    have ht : a * (1 - ‖(y : E)‖) = 1 - ‖(x : E)‖ := congrArg Prod.snd ha
    have hn := congrArg norm hv
    rw [norm_smul, Real.norm_eq_abs] at hn
    have hx := mem_closedBall_zero_iff.mp x.prop
    have hy := mem_closedBall_zero_iff.mp y.prop
    by_cases ha0 : 0 ≤ a
    · rw [abs_of_nonneg ha0] at hn
      have ha1 : a = 1 := by nlinarith
      exact Or.inl (Subtype.ext (by simpa [ha1] using hv.symm))
    · have ha0' : a < 0 := lt_of_not_ge ha0
      rw [abs_of_neg ha0'] at hn
      have hnx : ‖(x : E)‖ = 1 := by nlinarith
      have hny : ‖(y : E)‖ = 1 := by nlinarith
      have ha1 : a = -1 := by nlinarith
      exact Or.inr ⟨hnx, by simpa [ha1] using hv.symm⟩
  · rintro (rfl | ⟨hx, hxy⟩)
    · exact ⟨1, by simp⟩
    · have hy : ‖(y : E)‖ = 1 := by simpa [hxy] using hx
      exact ⟨-1, Prod.ext (by simpa using hxy.symm) (by simp [hx, hy])⟩

private theorem exists_diskRepresentative (v : E × ℝ) (hv : v ≠ 0) (ht : 0 ≤ v.2) :
    ∃ x, diskCharacteristicMap x = Projectivization.mk ℝ v hv := by
  have hd : 0 < ‖v.1‖ + v.2 := by
    by_contra h
    have h' : ‖v.1‖ + v.2 ≤ 0 := le_of_not_gt h
    have hw : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1])
    have ht' : v.2 = 0 := by nlinarith [norm_nonneg v.1]
    exact hv (Prod.ext hw ht')
  have hn : ‖(‖v.1‖ + v.2)⁻¹ • v.1‖ = (‖v.1‖ + v.2)⁻¹ * ‖v.1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  have hi : (‖v.1‖ + v.2)⁻¹ * (‖v.1‖ + v.2) = 1 := inv_mul_cancel₀ hd.ne'
  have hx : (‖v.1‖ + v.2)⁻¹ • v.1 ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, hn]
    calc
      _ ≤ (‖v.1‖ + v.2)⁻¹ * (‖v.1‖ + v.2) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ht) (inv_nonneg.mpr hd.le)
      _ = 1 := hi
  refine ⟨⟨_, hx⟩, (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ?_⟩
  refine ⟨(‖v.1‖ + v.2)⁻¹, Prod.ext rfl ?_⟩
  change (‖v.1‖ + v.2)⁻¹ * v.2 = 1 - ‖(‖v.1‖ + v.2)⁻¹ • v.1‖
  rw [hn]
  nlinarith [hi]

theorem diskCharacteristicMap_surjective :
    Function.Surjective (diskCharacteristicMap (E := E)) := by
  intro p
  induction p using Projectivization.ind with
  | h v hv =>
    by_cases ht : 0 ≤ v.2
    · exact exists_diskRepresentative v hv ht
    · have hv' : -v ≠ 0 := neg_ne_zero.mpr hv
      obtain ⟨x, hx⟩ := exists_diskRepresentative (-v) hv' (by simpa using (le_of_not_ge ht))
      refine ⟨x, hx.trans ((Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr ?_)⟩
      exact ⟨-1, by simp⟩


theorem isQuotientMap_diskCharacteristicMap [FiniteDimensional ℝ E] :
    IsQuotientMap (diskCharacteristicMap (E := E)) :=
  continuous_diskCharacteristicMap.isClosedMap.isQuotientMap
    continuous_diskCharacteristicMap diskCharacteristicMap_surjective

theorem diskCharacteristicMap_mem_range_coordinateInclusion_iff
    (x : closedBall (0 : E) 1) :
    diskCharacteristicMap x ∈ Set.range coordinateInclusion ↔ ‖(x : E)‖ = 1 := by
  constructor
  · rintro ⟨p, hp⟩
    induction p using Projectivization.ind with
    | h v hv =>
      have hp' : Projectivization.mk ℝ ((x : E), 1 - ‖(x : E)‖) _ =
          Projectivization.mk ℝ (v, (0 : ℝ)) _ := hp.symm
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mp hp'
      have ht : a * 0 = 1 - ‖(x : E)‖ := congrArg Prod.snd ha
      linarith
  · intro hx
    refine ⟨sphereProjection ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩, ?_⟩
    exact (diskCharacteristicMap_sphere ⟨x.val, mem_sphere_zero_iff_norm.mpr hx⟩).symm

end DifferentialGeometry.ProjectiveSpace
