import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Topology.ProjectiveSpace.Real

set_option autoImplicit false

noncomputable section

open Bundle Metric

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable [Fact (Module.finrank ℝ E = 2 + 1)]

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private theorem RoundQuotientData.proj_injective_or_antipodal_fibers
    (D : RoundQuotientData E 2) :
    Function.Injective D.proj ∨
      ∀ x y : sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y := by
  classical
  by_cases hneg : ∃ gamma : D.Γ,
      D.ρ gamma = LinearIsometryEquiv.neg ℝ
  · right
    intro x y
    constructor
    · intro hxy
      obtain ⟨gamma, hgamma⟩ := D.proj_eq_imp x y hxy
      rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action
          D.ρ D.action_free gamma with hone | hminus
      · left
        apply Subtype.ext
        have h := congrArg Subtype.val hgamma
        simpa [hone] using h
      · right
        apply Subtype.ext
        have h := congrArg Subtype.val hgamma
        have h' := congrArg Neg.neg h
        simpa [hminus] using h'
    · rintro (hxy | hxy)
      · exact congrArg D.proj hxy
      · obtain ⟨gamma, hgamma⟩ := hneg
        have hsmul := D.proj_smul gamma y
        rw [hgamma] at hsmul
        have hnegY :
            sphereDiffeo (n := 2) (LinearIsometryEquiv.neg ℝ) y = -y := by
          apply Subtype.ext
          rfl
        rw [hnegY] at hsmul
        rw [hxy]
        exact hsmul
  · left
    intro x y hxy
    obtain ⟨gamma, hgamma⟩ := D.proj_eq_imp x y hxy
    rcases orth_rep_apply_eq_one_or_neg_of_free_sphere_action
        D.ρ D.action_free gamma with hone | hminus
    · apply Subtype.ext
      have h := congrArg Subtype.val hgamma
      simpa [hone] using h
    · exact (hneg ⟨gamma, hminus⟩).elim

theorem RoundQuotientData.proj_fiber_dichotomy
    (D : RoundQuotientData E 2) :
    (Function.Injective D.proj ∧
      ¬ ∀ x y : sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y) ∨
    (¬ Function.Injective D.proj ∧
      ∀ x y : sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y) := by
  classical
  have hinjNot : Function.Injective D.proj →
      ¬ ∀ x y : sphere (0 : E) 1,
        D.proj x = D.proj y ↔ x = y ∨ x = -y := by
    intro hinj hanti
    have hfinrank : 0 < Module.finrank ℝ E := by
      rw [show Module.finrank ℝ E = 2 + 1 from Fact.out]
      norm_num
    let : Nontrivial E := Module.nontrivial_of_finrank_pos hfinrank
    let x : sphere (0 : E) 1 :=
      Classical.choice
        (NormedSpace.sphere_nonempty_rclike ℝ
          (E := E) (r := (1 : ℝ)) zero_le_one)
    have hproj : D.proj x = D.proj (-x) :=
      (hanti x (-x)).mpr (Or.inr (by simp))
    exact ne_neg_of_mem_unit_sphere ℝ x (hinj hproj)
  rcases D.proj_injective_or_antipodal_fibers with hinj | hanti
  · exact Or.inl ⟨hinj, hinjNot hinj⟩
  · exact Or.inr ⟨fun hinj => hinjNot hinj hanti, hanti⟩

noncomputable def RoundQuotientData.sphereHomeomorph
    (D : RoundQuotientData E 2)
    (hinj : Function.Injective D.proj) :
    sphere (0 : E) 1 ≃ₜ D.Q :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective D.proj ⟨hinj, D.proj_surjective⟩)
    D.proj_smooth.continuous

theorem RoundQuotientData.sphereHomeomorph_apply
    (D : RoundQuotientData E 2)
    (hinj : Function.Injective D.proj) (x : sphere (0 : E) 1) :
    D.sphereHomeomorph hinj x = D.proj x :=
  rfl

private theorem RoundQuotientData.proj_respects_antipodal
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x y : sphere (0 : E) 1)
    (hxy : MulAction.orbitRel
      (realProjectiveSpaceAntipodalGroup E) _ x y) :
    D.proj x = D.proj y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases realProjectiveSpaceAntipodalGroup_smul_eq_self_or_neg psi y with
    hself | hneg
  · exact (hanti (psi • y) y).mpr (Or.inl hself)
  · exact (hanti (psi • y) y).mpr (Or.inr hneg)

private def RoundQuotientData.realProjectiveSpaceToQuotient
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    RealProjectiveSpace E → D.Q :=
  Quotient.lift D.proj (D.proj_respects_antipodal hanti)

private theorem RoundQuotientData.realProjectiveSpaceToQuotient_apply
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x : sphere (0 : E) 1) :
    D.realProjectiveSpaceToQuotient hanti
        (realProjectiveSpaceQuotientMap x) = D.proj x :=
  rfl

private theorem RoundQuotientData.realProjectiveSpaceToQuotient_continuous
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    Continuous (D.realProjectiveSpaceToQuotient hanti) :=
  D.proj_smooth.continuous.quotient_lift
    (D.proj_respects_antipodal hanti)

noncomputable def RoundQuotientData.realProjectiveSpaceHomeomorph
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y) :
    RealProjectiveSpace E ≃ₜ D.Q := by
  let F := D.realProjectiveSpaceToQuotient hanti
  have hsurj : Function.Surjective F := by
    intro q
    obtain ⟨x, hx⟩ := D.proj_surjective q
    exact ⟨realProjectiveSpaceQuotientMap x, hx⟩
  have hinj : Function.Injective F := by
    intro q r hqr
    induction q using Quotient.inductionOn with
    | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
        change D.proj x = D.proj y at hqr
        change realProjectiveSpaceQuotientMap x =
          realProjectiveSpaceQuotientMap y
        apply realProjectiveSpaceQuotientMap_eq_iff.mpr
        rcases (hanti x y).mp hqr with hxy | hxy
        · exact Or.inl hxy
        · exact Or.inr (congrArg Subtype.val hxy)
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F ⟨hinj, hsurj⟩)
    (D.realProjectiveSpaceToQuotient_continuous hanti)

theorem RoundQuotientData.realProjectiveSpaceHomeomorph_apply
    (D : RoundQuotientData E 2)
    (hanti : ∀ x y : sphere (0 : E) 1,
      D.proj x = D.proj y ↔ x = y ∨ x = -y)
    (x : sphere (0 : E) 1) :
    D.realProjectiveSpaceHomeomorph hanti
        (realProjectiveSpaceQuotientMap x) = D.proj x :=
  rfl

theorem RoundQuotientData.homeomorphic_sphere_or_real_projective_space
    (D : RoundQuotientData E 2) :
    (∃ e : sphere (0 : E) 1 ≃ₜ D.Q,
      ∀ x, e x = D.proj x) ∨
    (∃ e : RealProjectiveSpace E ≃ₜ D.Q,
      ∀ x, e (realProjectiveSpaceQuotientMap x) = D.proj x) := by
  rcases D.proj_fiber_dichotomy with htriv | hanti
  · exact Or.inl ⟨D.sphereHomeomorph htriv.1,
      D.sphereHomeomorph_apply htriv.1⟩
  · exact Or.inr ⟨D.realProjectiveSpaceHomeomorph hanti.2,
      D.realProjectiveSpaceHomeomorph_apply hanti.2⟩

theorem RoundQuotientData.homeomorphic_two_sphere_or_real_projective_plane
    (D : RoundQuotientData
      (EuclideanSpace ℝ (Fin 3)) 2) :
    (∃ e : sphere
        (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ D.Q,
      ∀ x, e x = D.proj x) ∨
    (∃ e : RealProjectivePlane ≃ₜ D.Q,
      ∀ x, e (realProjectivePlaneQuotientMap x) = D.proj x) := by
  rcases D.homeomorphic_sphere_or_real_projective_space with hsphere | hprojective
  · exact Or.inl hsphere
  · right
    obtain ⟨e, he⟩ := hprojective
    exact ⟨e, fun x => by
      simpa only [realProjectivePlaneQuotientMap] using he x⟩

end DifferentialGeometry.Geometry
