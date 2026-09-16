import DifferentialGeometry.Topology.PiecewiseLinear.HeightIndex
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem HasPLCrossingAt.image_homeomorph [FiniteDimensional ℝ E]
    {A B : Set E} {x : E} (hAB : HasPLCrossingAt A B x) (h : E ≃ₜ E)
    (hh : IsPLHomeomorphOn h univ univ) : HasPLCrossingAt (h '' A) (h '' B) (h x) := by
  have himage := hAB.image_openPartialHomeomorph h.toOpenPartialHomeomorph
    hh.isPiecewiseAffineOn (mem_univ x)
  change HasPLCrossingAt (h '' (univ ∩ A)) (h '' (univ ∩ B)) (h x) at himage
  simpa only [univ_inter] using himage

theorem hasPLCrossingAt_image_homeomorph_iff [FiniteDimensional ℝ E]
    {A B : Set E} {x : E} (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ) :
    HasPLCrossingAt (h '' A) (h '' B) (h x) ↔ HasPLCrossingAt A B x := by
  constructor
  · intro himage
    have horiginal := himage.image_homeomorph h.symm hh.homeomorph_symm
    simpa only [image_image, h.symm_apply_apply, image_id'] using horiginal
  · exact fun hAB => hAB.image_homeomorph h hh

private theorem singleton_mem_nhdsWithin_image_iff {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) (S : Set X) (x : X) :
    {h x} ∈ 𝓝[h '' S] (h x) ↔ {x} ∈ 𝓝[S] x := by
  rw [← h.isEmbedding.map_nhdsWithin_eq]
  change h ⁻¹' {h x} ∈ 𝓝[S] x ↔ {x} ∈ 𝓝[S] x
  have hpre : h ⁻¹' {h x} = {x} := by
    ext y
    exact h.injective.eq_iff
  rw [hpre]

theorem mem_heightSingularPoints_image_iff [FiniteDimensional ℝ E]
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    {S : Set E} {ℓ ℓ' : E → ℝ} (hℓ : ∀ x, ℓ' (h x) = ℓ x) (x : E) :
    h x ∈ heightSingularPoints (h '' S) ℓ' ↔ x ∈ heightSingularPoints S ℓ := by
  have hplane : h '' {y | ℓ y = ℓ x} = {y | ℓ' y = ℓ' (h x)} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change ℓ' (h z) = ℓ' (h x)
      rw [hℓ z, hℓ x]
      exact hz
    · intro hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      change ℓ (h.symm y) = ℓ x
      rw [← hℓ (h.symm y), h.apply_symm_apply, ← hℓ x]
      exact hy
  have hlevel : h '' (S ∩ {y | ℓ y = ℓ x}) =
      (h '' S) ∩ {y | ℓ' y = ℓ' (h x)} := by
    rw [image_inter h.injective, hplane]
  change (h x ∈ h '' S ∧ ¬ HasPLCrossingAt (h '' S) {y | ℓ' y = ℓ' (h x)} (h x) ∧
      ¬ {h x} ∈ 𝓝[(h '' S) ∩ {y | ℓ' y = ℓ' (h x)}] (h x)) ↔
    (x ∈ S ∧ ¬ HasPLCrossingAt S {y | ℓ y = ℓ x} x ∧
      ¬ {x} ∈ 𝓝[S ∩ {y | ℓ y = ℓ x}] x)
  rw [← hlevel, ← hplane, hasPLCrossingAt_image_homeomorph_iff h hh,
    singleton_mem_nhdsWithin_image_iff, h.injective.mem_set_image]

theorem heightSingularPoints_image [FiniteDimensional ℝ E]
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    {S : Set E} {ℓ ℓ' : E → ℝ} (hℓ : ∀ x, ℓ' (h x) = ℓ x) :
    heightSingularPoints (h '' S) ℓ' = h '' heightSingularPoints S ℓ := by
  ext y
  obtain ⟨x, rfl⟩ := h.surjective y
  rw [mem_heightSingularPoints_image_iff h hh hℓ, h.injective.mem_set_image]

theorem heightIndex_image [FiniteDimensional ℝ E]
    (h : E ≃ₜ E) (hh : IsPLHomeomorphOn h univ univ)
    {S : Set E} {ℓ ℓ' : E → ℝ} (hℓ : ∀ x, ℓ' (h x) = ℓ x) :
    heightIndex (h '' S) ℓ' = heightIndex S ℓ := by
  let e : heightSingularPoints S ℓ ≃ heightSingularPoints (h '' S) ℓ' :=
    { toFun := fun x => ⟨h x, (mem_heightSingularPoints_image_iff h hh hℓ x).mpr x.property⟩
      invFun := fun y => ⟨h.symm y, (mem_heightSingularPoints_image_iff h hh hℓ (h.symm y)).mp
        (by simpa only [h.apply_symm_apply] using y.property)⟩
      left_inv := fun x => Subtype.ext (h.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (h.apply_symm_apply y) }
  unfold heightIndex
  rw [← e.tsum_eq]
  apply tsum_congr
  intro p
  change (levelPolygons (h '' S) ℓ' (ℓ' (h p))).encard - 1 =
    (levelPolygons S ℓ (ℓ p)).encard - 1
  rw [hℓ p, encard_levelPolygons_image h hh (fun x _ => hℓ x)]

end DifferentialGeometry.Topology.PiecewiseLinear
