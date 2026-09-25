import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Topology.Homotopy.Contractible

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.nullhomotopic_inclusion_of_image
    {P J : Set E} {Q K : Set F} {f : E → F} (hf : IsPLHomeomorphOn f P Q)
    (hJP : J ⊆ P) (hKQ : K ⊆ Q) (himage : f '' J = K)
    (hnull : (⟨inclusion hJP, continuous_inclusion hJP⟩ : C(J, P)).Nullhomotopic) :
    (⟨inclusion hKQ, continuous_inclusion hKQ⟩ : C(K, Q)).Nullhomotopic := by
  let φ : C(P, Q) := ⟨fun x => ⟨f x, hf.bijOn.mapsTo x.2⟩,
    (hf.isPiecewiseAffineOn.continuousOn.comp_continuous continuous_subtype_val
      fun x => x.2).subtype_mk _⟩
  let g := Function.invFunOn f P
  have hgJ : MapsTo g K J := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := himage.symm.subset hy
    change Function.invFunOn f P (f x) ∈ J
    rw [hf.bijOn.invOn_invFunOn.1 (hJP hx)]
    exact hx
  let ψ : C(K, J) := ⟨fun y => ⟨g y, hgJ y.2⟩,
    (hf.symm.isPiecewiseAffineOn.continuousOn.comp_continuous continuous_subtype_val
      fun y => hKQ y.2).subtype_mk _⟩
  have heq : (φ.comp (⟨inclusion hJP, continuous_inclusion hJP⟩ : C(J, P))).comp ψ =
      (⟨inclusion hKQ, continuous_inclusion hKQ⟩ : C(K, Q)) := by
    ext y
    exact hf.bijOn.invOn_invFunOn.2 (hKQ y.2)
  exact heq ▸ (hnull.comp_right φ).comp_left ψ

theorem IsPLHomeomorphOn.nullhomotopic_inclusion_iff_of_image
    {P J : Set E} {Q K : Set F} {f : E → F} (hf : IsPLHomeomorphOn f P Q)
    (hJP : J ⊆ P) (hKQ : K ⊆ Q) (himage : f '' J = K) :
    (⟨inclusion hJP, continuous_inclusion hJP⟩ : C(J, P)).Nullhomotopic ↔
      (⟨inclusion hKQ, continuous_inclusion hKQ⟩ : C(K, Q)).Nullhomotopic := by
  have hinverse : Function.invFunOn f P '' K = J := by
    rw [← himage, ← image_comp]
    exact (show EqOn (Function.invFunOn f P ∘ f) id J from fun _ hx =>
      hf.bijOn.invOn_invFunOn.1 (hJP hx)).image_eq.trans (image_id J)
  exact ⟨hf.nullhomotopic_inclusion_of_image hJP hKQ himage,
    hf.symm.nullhomotopic_inclusion_of_image hKQ hJP hinverse⟩

end DifferentialGeometry.Topology.PiecewiseLinear
