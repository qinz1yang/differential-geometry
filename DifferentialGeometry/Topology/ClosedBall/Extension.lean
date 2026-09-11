import DifferentialGeometry.Topology.ClosedBall.Retraction

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace DifferentialGeometry.Topology.ClosedBall
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [TopologicalSpace F]
  (a : E) {r : ℝ} (hr : 0 ≤ r)


def extension (f : C(closedBall a r, F)) : C(E, F) := f.comp (retraction a hr)


theorem extension_apply (f : C(closedBall a r, F)) (x : E) :
    extension a hr f x = f (retraction a hr x) := rfl

@[simp]
theorem extension_coe (f : C(closedBall a r, F)) (x : closedBall a r) :
    extension a hr f (x : E) = f x := by
  rw [extension_apply, retraction_coe]

@[simp]
theorem extension_restrict (f : C(closedBall a r, F)) :
    (extension a hr f).restrict (closedBall a r) = f := by
  ext x
  exact extension_coe a hr f x

theorem extension_eventuallyEq_of_eventuallyEq (f : C(closedBall a r, F))
    {x : E} (hx : x ∈ ball a r) {g : E → F}
    (hg : (f : closedBall a r → F) =ᶠ[𝓝 (⟨x, ball_subset_closedBall hx⟩ : closedBall a r)]
      (fun y => g y.val)) :
    (extension a hr f : E → F) =ᶠ[𝓝 x] g := by
  have hρ : Tendsto (retraction a hr) (𝓝 x)
      (𝓝 (⟨x, ball_subset_closedBall hx⟩ : closedBall a r)) := by
    have h := (retraction a hr).continuous.continuousAt (x := x)
    have he := retraction_coe a hr (⟨x, ball_subset_closedBall hx⟩ : closedBall a r)
    exact he ▸ h
  have hh := hg.comp_tendsto hρ
  exact hh.trans ((retraction_eventuallyEq_id a hr hx).fun_comp g)

theorem extension_restrict_eventuallyEq (g : C(E, F)) {x : E} (hx : x ∈ ball a r) :
    (extension a hr (g.restrict (closedBall a r)) : E → F) =ᶠ[𝓝 x] g :=
  extension_eventuallyEq_of_eventuallyEq a hr _ hx (Filter.EventuallyEq.rfl)

theorem extension_ne_of_le (f : C(closedBall a r, F)) {z : F}
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ z)
    {x : E} (hx : r ≤ dist x a) : extension a hr f x ≠ z :=
  hb (retraction a hr x) (retraction_mem_sphere a hr hx)

theorem extension_eq_iff (f : C(closedBall a r, F)) {z : F}
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ z) (x : E) :
    extension a hr f x = z ↔ ∃ hx : x ∈ closedBall a r, f ⟨x, hx⟩ = z := by
  constructor
  · intro hz
    have hx : x ∈ closedBall a r := by
      by_contra hx
      exact extension_ne_of_le a hr f hb (le_of_lt (lt_of_not_ge hx)) hz
    exact ⟨hx, (extension_coe a hr f ⟨x, hx⟩).symm.trans hz⟩
  · rintro ⟨hx, hz⟩
    exact (extension_coe a hr f ⟨x, hx⟩).trans hz

theorem extension_preimage_singleton (f : C(closedBall a r, F)) {z : F}
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ z) :
    (extension a hr f) ⁻¹' {z} = Subtype.val '' (f ⁻¹' {z}) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hmem, hz⟩ := (extension_eq_iff a hr f hb x).mp hx
    exact ⟨⟨x, hmem⟩, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact (extension_coe a hr f y).trans hy


theorem extension_preimage_singleton_subset_ball (f : C(closedBall a r, F)) {z : F}
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ z) :
    (extension a hr f) ⁻¹' {z} ⊆ ball a r := by
  intro x hx
  exact lt_of_not_ge (fun hle => extension_ne_of_le a hr f hb hle hx)

variable [Zero F]


theorem extension_ne_zero_of_not_mem (f : C(closedBall a r, F))
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ 0)
    {x : E} (hx : x ∉ closedBall a r) : extension a hr f x ≠ 0 :=
  extension_ne_of_le a hr f hb (le_of_lt (lt_of_not_ge hx))

theorem extension_zeroSet (f : C(closedBall a r, F))
    (hb : ∀ y : closedBall a r, (y : E) ∈ sphere a r → f y ≠ 0) :
    {x : E | extension a hr f x = 0} =
      Subtype.val '' {y : closedBall a r | f y = 0} :=
  extension_preimage_singleton a hr f hb

end DifferentialGeometry.Topology.ClosedBall
