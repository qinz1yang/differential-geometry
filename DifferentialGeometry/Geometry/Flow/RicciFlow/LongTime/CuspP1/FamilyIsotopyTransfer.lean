import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Maps.OpenQuotient

/-!
# CP1-D5: transfer of a compactly supported homeomorphism through an open embedding
-/

set_option autoImplicit false
open Set Function Topology
noncomputable section
namespace GC.LongTime.CuspP1

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- extension of a map of `X` to `Y` along `ι`, identity off the range -/
def extendAlong_CPD5 (ι : X → Y) (e : X → X) : Y → Y := Function.extend ι (ι ∘ e) id

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem extendAlong_apply_CPD5 {ι : X → Y} (hι : Function.Injective ι) (e : X → X) (x : X) :
    extendAlong_CPD5 ι e (ι x) = ι (e x) := by
  unfold extendAlong_CPD5
  rw [hι.extend_apply]; rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem extendAlong_apply_of_notMem_CPD5 (ι : X → Y) (e : X → X) {y : Y} (hy : y ∉ range ι) :
    extendAlong_CPD5 ι e y = y := by
  unfold extendAlong_CPD5
  rw [Function.extend_apply' _ _ _ (by simpa using hy)]; rfl

omit [TopologicalSpace X] [TopologicalSpace Y] in
theorem extendAlong_eq_self_CPD5 {ι : X → Y} (hι : Function.Injective ι) {C : Set X} {e : X → X}
    (hsupp : ∀ x, x ∉ C → e x = x) {y : Y} (hy : y ∉ ι '' C) : extendAlong_CPD5 ι e y = y := by
  by_cases hr : y ∈ range ι
  · obtain ⟨x, rfl⟩ := hr
    rw [extendAlong_apply_CPD5 hι, hsupp x (fun hx => hy ⟨x, hx, rfl⟩)]
  · exact extendAlong_apply_of_notMem_CPD5 ι e hr

theorem continuous_extendAlong_CPD5 [T2Space Y] {ι : X → Y} (hι : IsOpenEmbedding ι) {C : Set X}
    (hC : IsCompact C) {e : X → X} (he : Continuous e) (hsupp : ∀ x, x ∉ C → e x = x) :
    Continuous (extendAlong_CPD5 ι e) := by
  have hCι : IsClosed (ι '' C) := (hC.image hι.continuous).isClosed
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ range ι
  · obtain ⟨x, rfl⟩ := hy
    rw [← hι.continuousAt_iff]
    have : extendAlong_CPD5 ι e ∘ ι = ι ∘ e := funext fun x => extendAlong_apply_CPD5 hι.injective e x
    rw [this]
    exact (hι.continuous.comp he).continuousAt
  · have hyC : y ∉ ι '' C := fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩
    refine continuousAt_id.congr ?_
    filter_upwards [hCι.isOpen_compl.mem_nhds hyC] with z hz
    exact (extendAlong_eq_self_CPD5 hι.injective hsupp hz).symm

/-- A compactly supported homeomorphism of `X` extends along an open embedding `ι : X → Y`
(`Y` Hausdorff) to a homeomorphism of `Y`, the identity off `ι '' C`. -/
theorem exists_homeo_extension_CPD5 [T2Space Y] {ι : X → Y} (hι : IsOpenEmbedding ι) {C : Set X}
    (hC : IsCompact C) (e : X ≃ₜ X) (hsupp : ∀ x, x ∉ C → e x = x) :
    ∃ e' : Y ≃ₜ Y, (∀ x, e' (ι x) = ι (e x)) ∧ ∀ y, y ∉ ι '' C → e' y = y := by
  have hsupp' : ∀ x, x ∉ C → e.symm x = x := fun x hx => by
    rw [e.symm_apply_eq]; exact (hsupp x hx).symm
  refine ⟨{ toFun := extendAlong_CPD5 ι e
            invFun := extendAlong_CPD5 ι e.symm
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := continuous_extendAlong_CPD5 hι hC e.continuous hsupp
            continuous_invFun := continuous_extendAlong_CPD5 hι hC e.symm.continuous hsupp' },
    fun x => extendAlong_apply_CPD5 hι.injective e x,
    fun y hy => extendAlong_eq_self_CPD5 hι.injective hsupp hy⟩
  · intro y
    by_cases hr : y ∈ range ι
    · obtain ⟨x, rfl⟩ := hr
      simp only [extendAlong_apply_CPD5 hι.injective, Homeomorph.symm_apply_apply]
    · simp only [extendAlong_apply_of_notMem_CPD5 ι _ hr]
  · intro y
    by_cases hr : y ∈ range ι
    · obtain ⟨x, rfl⟩ := hr
      simp only [extendAlong_apply_CPD5 hι.injective, Homeomorph.apply_symm_apply]
    · simp only [extendAlong_apply_of_notMem_CPD5 ι _ hr]

end GC.LongTime.CuspP1
