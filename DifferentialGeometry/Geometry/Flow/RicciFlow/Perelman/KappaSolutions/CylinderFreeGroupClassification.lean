import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SphereOrthogonalFixedPoint
import Mathlib.Analysis.Normed.Affine.Isometry

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "SphereAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : SphereAmbient) 1
local notation "OrthogonalThree" => SphereAmbient ≃ₗᵢ[ℝ] SphereAmbient
local notation "LineIsometry" => ℝ ≃ᵃⁱ[ℝ] ℝ
local notation "CylinderIsometry" => OrthogonalThree × LineIsometry

private theorem cylinderFree_line_translation_or_reflection (b : LineIsometry) :
    (∃ c : ℝ, b = AffineIsometryEquiv.vaddConst ℝ c) ∨
      ∃ c : ℝ, b = AffineIsometryEquiv.pointReflection ℝ c := by
  let epsilon : ℝ := b.linearIsometryEquiv 1
  have hformula (s : ℝ) : b s = epsilon * s + b 0 := by
    have hv := b.map_vadd (0 : ℝ) s
    change b (s + 0) = b.linearIsometryEquiv s + b 0 at hv
    rw [add_zero] at hv
    have hlin : b.linearIsometryEquiv s = s * epsilon := by
      have h := LinearIsometryEquiv.map_smul (e := b.linearIsometryEquiv) s (1 : ℝ)
      simpa only [smul_eq_mul, mul_one] using h
    rw [hv, hlin, mul_comm s epsilon]
  have hsquare : epsilon ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (b.linearIsometryEquiv.norm_map (1 : ℝ))
    simpa only [Real.norm_eq_abs, abs_one, one_pow, sq_abs] using h
  rcases sq_eq_one_iff.mp hsquare with hplus | hminus
  · left
    refine ⟨b 0, ?_⟩
    apply AffineIsometryEquiv.ext
    intro s
    change b s = s + b 0
    rw [hformula, hplus, one_mul]
  · right
    refine ⟨b 0 / 2, ?_⟩
    apply AffineIsometryEquiv.ext
    intro s
    change b s = (b 0 / 2 - s) + b 0 / 2
    rw [hformula, hminus]
    ring

private theorem cylinderFree_line_square_and_fixed (b : LineIsometry)
    (hb : b = 1 ∨ ∃ c : ℝ, b = AffineIsometryEquiv.pointReflection ℝ c) :
    b * b = 1 ∧ ∃ s : ℝ, b s = s := by
  rcases hb with h | ⟨c, h⟩
  · subst b
    exact ⟨one_mul 1, 0, rfl⟩
  · subst b
    constructor
    · apply AffineIsometryEquiv.ext
      intro s
      change AffineIsometryEquiv.pointReflection ℝ c
        (AffineIsometryEquiv.pointReflection ℝ c s) = s
      exact AffineIsometryEquiv.pointReflection_involutive c s
    · exact ⟨c, AffineIsometryEquiv.pointReflection_self c⟩

variable (G : Subgroup CylinderIsometry)
  (hfree : ∀ gamma : CylinderIsometry, gamma ∈ G → gamma ≠ 1 →
    ∀ p : SphereTwo × ℝ,
      (gamma.1 (p.1 : SphereAmbient), gamma.2 p.2) ≠ ((p.1 : SphereAmbient), p.2))
  (hnoTranslation : ∀ gamma : CylinderIsometry, gamma ∈ G → ∀ c : ℝ,
    gamma.2 = AffineIsometryEquiv.vaddConst ℝ c → c = 0)

include hnoTranslation

theorem cylinderFreeGroup_line_eq_one_or_reflection
    (gamma : CylinderIsometry) (hgamma : gamma ∈ G) :
    gamma.2 = 1 ∨ ∃ c : ℝ, gamma.2 = AffineIsometryEquiv.pointReflection ℝ c := by
  rcases cylinderFree_line_translation_or_reflection gamma.2 with ⟨c, hc⟩ | hreflection
  · left
    have hz := hnoTranslation gamma hgamma c hc
    rw [hc, hz]
    apply AffineIsometryEquiv.ext
    intro s
    change s + 0 = s
    exact add_zero s
  · exact Or.inr hreflection

include hfree

theorem cylinderFreeGroup_square_eq_one (gamma : CylinderIsometry) (hgamma : gamma ∈ G) :
    gamma * gamma = 1 := by
  by_contra hne
  have hline := (cylinderFree_line_square_and_fixed gamma.2
    (cylinderFreeGroup_line_eq_one_or_reflection G hnoTranslation gamma hgamma)).1
  obtain ⟨y, hy⟩ := sphereOrthogonal_square_has_fixed_point gamma.1
  apply hfree (gamma * gamma) (G.mul_mem hgamma hgamma) hne (y, 0)
  refine Prod.ext hy ?_
  exact congrArg (fun b : LineIsometry => b 0) hline

theorem cylinderFreeGroup_sphere_eq_antipodal
    (gamma : CylinderIsometry) (hgamma : gamma ∈ G) (hne : gamma ≠ 1) :
    gamma.1 = LinearIsometryEquiv.neg ℝ := by
  have hsquare := cylinderFreeGroup_square_eq_one G hfree hnoTranslation gamma hgamma
  obtain ⟨s, hs⟩ := (cylinderFree_line_square_and_fixed gamma.2
    (cylinderFreeGroup_line_eq_one_or_reflection G hnoTranslation gamma hgamma)).2
  apply cylinderDeck_involution_eq_neg_of_sphere_free gamma.1
  · intro v
    exact congrArg (fun delta : CylinderIsometry => delta.1 v) hsquare
  · intro y hy
    apply hfree gamma hgamma hne (y, s)
    exact Prod.ext hy hs

theorem cylinderFreeGroup_nonidentity_unique
    (gamma delta : CylinderIsometry) (hgamma : gamma ∈ G) (hdelta : delta ∈ G)
    (hgamma_ne : gamma ≠ 1) (hdelta_ne : delta ≠ 1) : gamma = delta := by
  have hg := cylinderFreeGroup_sphere_eq_antipodal G hfree hnoTranslation
    gamma hgamma hgamma_ne
  have hd := cylinderFreeGroup_sphere_eq_antipodal G hfree hnoTranslation
    delta hdelta hdelta_ne
  have hproduct : gamma * delta = 1 := by
    by_contra hne
    obtain ⟨s, hs⟩ := (cylinderFree_line_square_and_fixed (gamma * delta).2
      (cylinderFreeGroup_line_eq_one_or_reflection G hnoTranslation
        (gamma * delta) (G.mul_mem hgamma hdelta))).2
    obtain ⟨y, -⟩ := sphereOrthogonal_square_has_fixed_point (1 : OrthogonalThree)
    apply hfree (gamma * delta) (G.mul_mem hgamma hdelta) hne (y, s)
    refine Prod.ext ?_ hs
    change gamma.1 (delta.1 (y : SphereAmbient)) = (y : SphereAmbient)
    rw [hg, hd]
    simp only [LinearIsometryEquiv.coe_neg, neg_neg]
  have hdSquare := cylinderFreeGroup_square_eq_one G hfree hnoTranslation delta hdelta
  calc
    gamma = gamma * (delta * delta) := by rw [hdSquare, mul_one]
    _ = (gamma * delta) * delta := (mul_assoc gamma delta delta).symm
    _ = delta := by rw [hproduct, one_mul]

theorem cylinderFreeGroup_eq_zpowers_and_two_elements
    (gamma : CylinderIsometry) (hgamma : gamma ∈ G) (hne : gamma ≠ 1) :
    G = Subgroup.zpowers gamma ∧ gamma * gamma = 1 ∧
      ∀ delta : CylinderIsometry, delta ∈ G ↔ delta = 1 ∨ delta = gamma := by
  classical
  have hmembers (delta : CylinderIsometry) : delta ∈ G ↔ delta = 1 ∨ delta = gamma := by
    constructor
    · intro hdelta
      by_cases hd : delta = 1
      · exact Or.inl hd
      · exact Or.inr (cylinderFreeGroup_nonidentity_unique G hfree hnoTranslation
          delta gamma hdelta hgamma hd hne)
    · rintro (rfl | rfl)
      · exact G.one_mem
      · exact hgamma
  refine ⟨?_, cylinderFreeGroup_square_eq_one G hfree hnoTranslation gamma hgamma, hmembers⟩
  apply le_antisymm
  · intro delta hdelta
    rcases (hmembers delta).mp hdelta with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers gamma
  · exact Subgroup.zpowers_le.mpr hgamma

theorem cylinderFreeGroup_classification :
    G = ⊥ ∨
      G = Subgroup.zpowers
        ((LinearIsometryEquiv.neg ℝ : OrthogonalThree), (1 : LineIsometry)) ∨
      ∃ c : ℝ, G = Subgroup.zpowers
        ((LinearIsometryEquiv.neg ℝ : OrthogonalThree),
          AffineIsometryEquiv.pointReflection ℝ c) := by
  classical
  by_cases hexists : ∃ gamma : CylinderIsometry, gamma ∈ G ∧ gamma ≠ 1
  · obtain ⟨gamma, hgamma, hne⟩ := hexists
    have hcyclic := (cylinderFreeGroup_eq_zpowers_and_two_elements
      G hfree hnoTranslation gamma hgamma hne).1
    have hsphere := cylinderFreeGroup_sphere_eq_antipodal
      G hfree hnoTranslation gamma hgamma hne
    rcases cylinderFreeGroup_line_eq_one_or_reflection G hnoTranslation gamma hgamma with
      hline | ⟨c, hline⟩
    · right
      left
      have hgammaEq : gamma =
          ((LinearIsometryEquiv.neg ℝ : OrthogonalThree), (1 : LineIsometry)) :=
        Prod.ext hsphere hline
      rw [hgammaEq] at hcyclic
      exact hcyclic
    · right
      right
      refine ⟨c, ?_⟩
      have hgammaEq : gamma =
          ((LinearIsometryEquiv.neg ℝ : OrthogonalThree),
            AffineIsometryEquiv.pointReflection ℝ c) := Prod.ext hsphere hline
      rw [hgammaEq] at hcyclic
      exact hcyclic
  · left
    apply (Subgroup.eq_bot_iff_forall G).mpr
    intro gamma hgamma
    by_contra hne
    exact hexists ⟨gamma, hgamma, hne⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
