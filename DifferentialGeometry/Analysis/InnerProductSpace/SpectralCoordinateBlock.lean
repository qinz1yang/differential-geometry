import DifferentialGeometry.Analysis.InnerProductSpace.LocalizedNormalSpectralSection

/-!
# A coordinate block killed by every contributing plane passes through the spectral section (CGP04)

Blueprint 207B, CGP04 (`lem:fibration-smoothed-locus-marker-exclusion`, B:4057–4082). On the larger
reference ball `B(y, 30 b r(y))` every contributing center `u` and plane `L_u` has zero `i` block
(CFS28 gives `R_i < R_{a_u}/2` — `small_radius_lt_half_reference_of_contributing_support` — and
CFS27's pruning rule deletes such blocks). The spectral calculation of CFS24 is pointwise on that
ball: `J_i Q = J_i`, `J_i μ = 0` and `J_i η(z) = J_i z`. At a zero of the section, `J_i z = 0`.

Here `J` is any continuous linear map (the coordinate block), and `hrule` is the plane rule on the
contributing indices: every index whose weight is somewhere nonzero on `U` has plane in `ker J`
and center in `ker J`. The proof is CFS24's localized identity
`Submodule.localized_weighted_normal_spectral_section` with base point `0`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Metric

namespace Submodule

variable {H G ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- CGP04/CFS24: a coordinate block vanishing on every contributing plane and center is preserved
by the weighted spectral section: `J (Q z (z - μ z)) = J z` on `U`. -/
theorem coordinateBlock_weighted_section_eq (S : Finset ι) (U : Set H) (w : ι → H → ℝ)
    (hw : ∀ z ∈ U, ∑ i ∈ S, w i z = 1) (L : ι → Submodule ℝ H) (c : ι → H) (J : H →L[ℝ] G)
    (hrule : ∀ i ∈ S, (∃ y ∈ U, w i y ≠ 0) → (∀ v ∈ L i, J v = 0) ∧ J (c i) = 0) :
    ∀ z ∈ U, J ((⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i z • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
          (z - ∑ i ∈ S, w i z • c i)) = J z := by
  classical
  intro z hz
  obtain ⟨-, hloc⟩ := localized_weighted_normal_spectral_section S U w hw L c 0
  set A : Finset ι := S.filter (fun i => ∃ y ∈ U, w i y ≠ 0) with hA
  set V : Submodule ℝ H := A.sup (fun i => (ℝ ∙ (c i - 0)) ⊔ L i) with hV
  have hVker : V ≤ LinearMap.ker (J : H →ₗ[ℝ] G) := by
    refine Finset.sup_le (fun i hi => ?_)
    obtain ⟨hiS, hact⟩ := Finset.mem_filter.mp hi
    obtain ⟨hL, hc⟩ := hrule i hiS hact
    refine sup_le ?_ (fun v hv => hL v hv)
    rw [Submodule.span_singleton_le_iff_mem, sub_zero]
    exact hc
  have hJ (y : H) : J y = J (Vᗮ.starProjection y) := by
    have hdecomp := Submodule.starProjection_add_starProjection_orthogonal (K := V) y
    have h0 : J (V.starProjection y) = 0 := hVker (V.starProjection_apply_mem y)
    conv_lhs => rw [← hdecomp]
    rw [map_add, h0, zero_add]
  have hz' := (hloc z hz).2
  rw [hJ, hz', sub_zero, ← hJ]

/-- CGP04 (WE): at a zero of the weighted spectral section the coordinate block vanishes. -/
theorem coordinateBlock_eq_zero_of_weighted_section_eq_zero (S : Finset ι) (U : Set H)
    (w : ι → H → ℝ) (hw : ∀ z ∈ U, ∑ i ∈ S, w i z = 1) (L : ι → Submodule ℝ H) (c : ι → H)
    (J : H →L[ℝ] G)
    (hrule : ∀ i ∈ S, (∃ y ∈ U, w i y ≠ 0) → (∀ v ∈ L i, J v = 0) ∧ J (c i) = 0)
    {z : H} (hz : z ∈ U)
    (hzero : (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ S, w i z • (L i)ᗮ.starProjection).toLinearMap μ).starProjection
          (z - ∑ i ∈ S, w i z • c i) = 0) : J z = 0 := by
  rw [← coordinateBlock_weighted_section_eq S U w hw L c J hrule z hz, hzero, map_zero]

end Submodule
