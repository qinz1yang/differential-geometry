import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderIsometry
import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.OrthogonalAction
import DifferentialGeometry.Topology.ProperlyDiscontinuousAction
import DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotient
import DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThree

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open private roundTwoSphereAntipodalDiffeomorph
  cylinderAntipodalDiffeomorph_toEquiv_ne_one cylinderDiagonalDiffeomorph_toEquiv_ne_one
  from DifferentialGeometry.Topology.ProjectiveSpace.CylinderQuotient

theorem cylinderAntipodal_potential (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential (cylinderAntipodal x) =
      roundThreeCylinderShrinkerPotential x := by
  simp [cylinderAntipodal, roundThreeCylinderShrinkerPotential_apply]

theorem cylinderDiagonal_potential (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    roundThreeCylinderShrinkerPotential (cylinderDiagonal x) =
      roundThreeCylinderShrinkerPotential x := by
  simp [cylinderDiagonal, roundThreeCylinderShrinkerPotential_apply]

theorem gaussianPotential_affine_preserving_shift_eq_zero
    (epsilon shift : Real)
    (hpreserve : ∀ s : Real,
      gaussianPotential (E := Real) (epsilon * s + shift) =
        gaussianPotential (E := Real) s) :
    shift = 0 := by
  have hzero := hpreserve 0
  simp only [gaussianPotential_apply, Real.norm_eq_abs] at hzero
  have hsq : shift ^ 2 = 0 := by
    simpa using hzero
  nlinarith

theorem roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (epsilon shift : Real)
    (hpreserve : ∀ s : Real,
      roundThreeCylinderShrinkerPotential (y, epsilon * s + shift) =
        roundThreeCylinderShrinkerPotential (y, s)) :
    shift = 0 := by
  have hzero := hpreserve 0
  simp only [mul_zero, zero_add, roundThreeCylinderShrinkerPotential_apply] at hzero
  nlinarith

theorem roundThreeCylinderShrinkerPotential_affine_line_preserving_iff
    (y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (epsilon shift : Real) :
    (∀ s : Real,
      roundThreeCylinderShrinkerPotential (y, epsilon * s + shift) =
        roundThreeCylinderShrinkerPotential (y, s)) ↔
      (epsilon = 1 ∨ epsilon = -1) ∧ shift = 0 := by
  constructor
  · intro hpreserve
    have hshift :=
      roundThreeCylinderShrinkerPotential_affine_line_preserving_shift_eq_zero
        y epsilon shift hpreserve
    subst shift
    have hone := hpreserve 1
    simp only [mul_one, add_zero, roundThreeCylinderShrinkerPotential_apply,
      one_pow] at hone
    refine ⟨sq_eq_one_iff.mp ?_, rfl⟩
    nlinarith
  · rintro ⟨hepsilon, rfl⟩ s
    rcases hepsilon with rfl | rfl <;>
      simp [roundThreeCylinderShrinkerPotential_apply]

variable {Γ : Type*}

theorem finite_of_properlyDiscontinuousSMul_of_roundThreeCylinderShrinkerPotential_invariant
    [SMul Γ (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    [ProperlyDiscontinuousSMul Γ
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    (hpotential : ∀ (γ : Γ) x,
      roundThreeCylinderShrinkerPotential (γ • x) =
        roundThreeCylinderShrinkerPotential x) :
    Finite Γ := by
  apply ProperlyDiscontinuousSMul.finite_of_isCompact_mapsTo
    (Γ := Γ)
    (T := Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (K := roundThreeCylinderCentralSlice)
    isCompact_roundThreeCylinderCentralSlice
  · refine ⟨(⟨EuclideanSpace.single 0 1, ?_⟩, (0 : Real)), rfl⟩
    simp [PiLp.norm_single]
  · intro γ x hx
    rw [← roundThreeCylinderShrinkerPotential_eq_one_iff] at hx ⊢
    rw [hpotential γ x]
    exact hx

private theorem roundTwoSphereAntipodalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric
        roundTwoSphereAntipodalDiffeomorph =
      roundTwoSphereShrinkerMetric := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner]
  change (roundSphereShrinkerMetric
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)).inner
      (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real) x)
        (mfderiv (𝓡 2) (𝓡 2)
          (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)) x v)
        (mfderiv (𝓡 2) (𝓡 2)
          (sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)) x w) =
      (roundSphereShrinkerMetric
        (A := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)).inner x v w
  rw [roundSphereShrinkerMetric, scaleMetric_inner, scaleMetric_inner]
  exact congrArg
    (fun z : Real => roundSphereShrinkerRadius 2 ^ 2 * z)
    (roundInner_sphereDiffeo (n := 2)
      (LinearIsometryEquiv.neg Real) x v w)

theorem cylinderAntipodalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderAntipodalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  rw [roundThreeCylinderShrinkerMetric,
    cylinderAntipodalDiffeomorph,
    Diffeomorph.pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    Diffeomorph.pullbackMetric_refl]

theorem cylinderDiagonalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderDiagonalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  have hneg :
      Diffeomorph.pullbackMetric (euclideanMetric (E := Real))
          (ContinuousLinearEquiv.neg Real).toDiffeomorph =
        euclideanMetric := by
    have hdiffeo :
        (ContinuousLinearEquiv.neg Real).toDiffeomorph =
          (LinearIsometryEquiv.neg Real :
            Real ≃ₗᵢ[Real] Real).toContinuousLinearEquiv.toDiffeomorph := by
      apply Diffeomorph.ext
      intro x
      rfl
    rw [hdiffeo]
    exact
      LinearIsometryEquiv.pullbackMetric_euclidean
        (E := Real) (LinearIsometryEquiv.neg Real)
  rw [roundThreeCylinderShrinkerMetric,
    cylinderDiagonalDiffeomorph,
    Diffeomorph.pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    hneg]

theorem cylinderAntipodalDiffeomorph_potential :
    roundThreeCylinderShrinkerPotential.comp
        cylinderAntipodalDiffeomorph.toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  apply ContMDiffMap.ext
  intro x
  change roundThreeCylinderShrinkerPotential
      (cylinderAntipodalDiffeomorph x) =
    roundThreeCylinderShrinkerPotential x
  rw [cylinderAntipodalDiffeomorph_apply]
  exact cylinderAntipodal_potential x

theorem cylinderDiagonalDiffeomorph_potential :
    roundThreeCylinderShrinkerPotential.comp
        cylinderDiagonalDiffeomorph.toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  apply ContMDiffMap.ext
  intro x
  change roundThreeCylinderShrinkerPotential
      (cylinderDiagonalDiffeomorph x) =
    roundThreeCylinderShrinkerPotential x
  rw [cylinderDiagonalDiffeomorph_apply]
  exact cylinderDiagonal_potential x

theorem cylinderAntipodalGroupDiffeomorph_pullbackMetric
    (psi : cylinderAntipodalGroup) :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        (cylinderAntipodalGroupDiffeomorph psi) =
      roundThreeCylinderShrinkerMetric := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderAntipodalGroupDiffeomorph, h,
      Diffeomorph.pullbackMetric_refl]
  · simpa [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one] using
        cylinderAntipodalDiffeomorph_pullbackMetric

theorem cylinderDiagonalGroupDiffeomorph_pullbackMetric
    (psi : cylinderDiagonalGroup) :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        (cylinderDiagonalGroupDiffeomorph psi) =
      roundThreeCylinderShrinkerMetric := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderDiagonalGroupDiffeomorph, h,
      Diffeomorph.pullbackMetric_refl]
  · simpa [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one] using
        cylinderDiagonalDiffeomorph_pullbackMetric

theorem cylinderAntipodalGroupDiffeomorph_potential
    (psi : cylinderAntipodalGroup) :
    roundThreeCylinderShrinkerPotential.comp
        (cylinderAntipodalGroupDiffeomorph psi).toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · rw [show cylinderAntipodalGroupDiffeomorph psi =
        Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞ by
      simp [cylinderAntipodalGroupDiffeomorph, h]]
    apply ContMDiffMap.ext
    intro x
    rfl
  · simpa [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one] using
        cylinderAntipodalDiffeomorph_potential

theorem cylinderDiagonalGroupDiffeomorph_potential
    (psi : cylinderDiagonalGroup) :
    roundThreeCylinderShrinkerPotential.comp
        (cylinderDiagonalGroupDiffeomorph psi).toContMDiffMap =
      roundThreeCylinderShrinkerPotential := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · rw [show cylinderDiagonalGroupDiffeomorph psi =
        Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
          (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞ by
      simp [cylinderDiagonalGroupDiffeomorph, h]]
    apply ContMDiffMap.ext
    intro x
    rfl
  · simpa [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one] using
        cylinderDiagonalDiffeomorph_potential

theorem cylinderAntipodalQuotientMap_metricFiberCompatible :
    metricFiberCompatible roundThreeCylinderShrinkerMetric
      cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph := by
  intro x y hxy
  rcases cylinderAntipodalQuotientMap_eq_iff.mp hxy with h | h
  · subst x
    cases hxy
    rfl
  · subst x
    let Phi := cylinderAntipodalDiffeomorph
    have hcomp : cylinderAntipodalQuotientMap ∘
        (Phi : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _) =
      cylinderAntipodalQuotientMap := by
      funext z
      exact cylinderAntipodalQuotientMap_eq_iff.mpr (Or.inr rfl)
    exact localPushInner_eq_of_fiber_preserving_isometry
      roundThreeCylinderShrinkerMetric cylinderAntipodalQuotientMap
      cylinderAntipodalQuotientMap_isLocalDiffeomorph Phi hcomp
      cylinderAntipodalDiffeomorph_pullbackMetric y

theorem cylinderDiagonalQuotientMap_metricFiberCompatible :
    metricFiberCompatible roundThreeCylinderShrinkerMetric
      cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph := by
  intro x y hxy
  rcases cylinderDiagonalQuotientMap_eq_iff.mp hxy with h | h
  · subst x
    cases hxy
    rfl
  · subst x
    let Phi := cylinderDiagonalDiffeomorph
    have hcomp : cylinderDiagonalQuotientMap ∘
        (Phi : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _) =
      cylinderDiagonalQuotientMap := by
      funext z
      exact cylinderDiagonalQuotientMap_eq_iff.mpr (Or.inr rfl)
    exact localPushInner_eq_of_fiber_preserving_isometry
      roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMap
      cylinderDiagonalQuotientMap_isLocalDiffeomorph Phi hcomp
      cylinderDiagonalDiffeomorph_pullbackMetric y

noncomputable def cylinderAntipodalQuotientMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      CylinderAntipodalQuotient :=
  descendedMetric roundThreeCylinderShrinkerMetric
    cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    cylinderAntipodalQuotientMap_metricFiberCompatible

noncomputable def cylinderDiagonalQuotientMetric :
    SmoothRiemannianMetric ((𝓡 2).prod 𝓘(Real, Real))
      CylinderDiagonalQuotient :=
  descendedMetric roundThreeCylinderShrinkerMetric
    cylinderDiagonalQuotientMap
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    cylinderDiagonalQuotientMap_metricFiberCompatible

theorem localPullMetric_cylinderAntipodalQuotientMetric :
    localPullMetric cylinderAntipodalQuotientMetric
        cylinderAntipodalQuotientMap
        cylinderAntipodalQuotientMap_isLocalDiffeomorph =
      roundThreeCylinderShrinkerMetric :=
  localPullMetric_descendedMetric roundThreeCylinderShrinkerMetric
    cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    cylinderAntipodalQuotientMap_metricFiberCompatible

theorem localPullMetric_cylinderDiagonalQuotientMetric :
    localPullMetric cylinderDiagonalQuotientMetric
        cylinderDiagonalQuotientMap
        cylinderDiagonalQuotientMap_isLocalDiffeomorph =
      roundThreeCylinderShrinkerMetric :=
  localPullMetric_descendedMetric roundThreeCylinderShrinkerMetric
    cylinderDiagonalQuotientMap
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    cylinderDiagonalQuotientMap_metricFiberCompatible

theorem cylinderAntipodalQuotientMetric_complete :
    RiemannianMetricComplete cylinderAntipodalQuotientMetric :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric
    roundThreeCylinderShrinkerMetric cylinderAntipodalQuotientMetric
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_isCoveringMap
    cylinderAntipodalQuotientMap_surjective
    localPullMetric_cylinderAntipodalQuotientMetric
    roundThreeCylinderShrinkerMetric_complete

theorem cylinderDiagonalQuotientMetric_complete :
    RiemannianMetricComplete cylinderDiagonalQuotientMetric :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric
    roundThreeCylinderShrinkerMetric cylinderDiagonalQuotientMetric
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_isCoveringMap
    cylinderDiagonalQuotientMap_surjective
    localPullMetric_cylinderDiagonalQuotientMetric
    roundThreeCylinderShrinkerMetric_complete

private theorem cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel
    (x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    MulAction.orbitRel cylinderDiagonalGroup _ x y ↔
      MulAction.orbitRel
        (realProjectiveSpaceAntipodalGroup
          (EuclideanSpace Real (Fin 4)))
        threeSphereAwayFromRealProjectivePuncture
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x)
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y) := by
  have hsource : MulAction.orbitRel cylinderDiagonalGroup _ x y ↔
      cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y :=
    ⟨Quotient.sound, Quotient.exact⟩
  have htarget :
      MulAction.orbitRel
          (realProjectiveSpaceAntipodalGroup
            (EuclideanSpace Real (Fin 4)))
          threeSphereAwayFromRealProjectivePuncture
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x)
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y) ↔
        realProjectiveSpaceQuotientMap
            ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
              threeSphereAwayFromRealProjectivePuncture) :
                Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) =
          realProjectiveSpaceQuotientMap
            ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y :
              threeSphereAwayFromRealProjectivePuncture) :
                Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) := by
    rw [SubMulAction.orbitRel_of_subMul]
    change MulAction.orbitRel
        (realProjectiveSpaceAntipodalGroup
          (EuclideanSpace Real (Fin 4)))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
        ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
          threeSphereAwayFromRealProjectivePuncture) :
            Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1)
        ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture y :
          threeSphereAwayFromRealProjectivePuncture) :
            Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1) ↔ _
    exact ⟨Quotient.sound, Quotient.exact⟩
  rw [hsource, htarget, cylinderDiagonalQuotientMap_eq_iff,
    realProjectiveSpaceQuotientMap_eq_iff]
  constructor
  · rintro (rfl | hxy)
    · exact Or.inl rfl
    · right
      rw [hxy, cylinderDiagonalDiffeomorph_apply]
      exact congrArg Subtype.val
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture_diagonal y)
  · rintro (hxy | hxy)
    · left
      apply twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.injective
      exact Subtype.ext hxy
    · right
      apply twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [cylinderDiagonalDiffeomorph_apply, cylinderDiagonal_apply,
        twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture_diagonal]
      exact hxy

private noncomputable def
    cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient :
    CylinderDiagonalQuotient ≃ₜ
      ThreeSphereAwayFromRealProjectivePunctureQuotient :=
  Homeomorph.Quotient.congr
    twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture
    cylinderDiagonalOrbitRel_iff_threeSphereAwayFromRealProjectivePunctureOrbitRel

noncomputable def cylinderDiagonalQuotientHomeomorph :
    CylinderDiagonalQuotient ≃ₜ PuncturedRealProjectiveThreeSpace :=
  cylinderDiagonalQuotientHomeomorphThreeSphereAwayFromRealProjectivePunctureQuotient.trans
    threeSphereAwayFromRealProjectivePunctureQuotientHomeomorph

theorem cylinderDiagonalQuotientHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientHomeomorph (cylinderDiagonalQuotientMap x) =
      ⟨realProjectiveSpaceQuotientMap
          ((twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x :
            threeSphereAwayFromRealProjectivePuncture) :
              Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1),
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture x).2⟩ :=
  rfl

theorem cylinderDiagonalQuotientHomeomorph_symm_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientHomeomorph.symm
        ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩ =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm z) := by
  apply cylinderDiagonalQuotientHomeomorph.injective
  rw [Homeomorph.apply_symm_apply,
    cylinderDiagonalQuotientHomeomorph_apply,
    Homeomorph.apply_symm_apply]

private theorem cylinderAntipodalPotential_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderAntipodalGroup _ x y) :
    roundThreeCylinderShrinkerPotential x =
      roundThreeCylinderShrinkerPotential y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    rfl
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    exact cylinderAntipodal_potential y

private theorem cylinderDiagonalPotential_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderDiagonalGroup _ x y) :
    roundThreeCylinderShrinkerPotential x =
      roundThreeCylinderShrinkerPotential y := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    rfl
  · change roundThreeCylinderShrinkerPotential (psi.1 y) = _
    rw [h]
    exact cylinderDiagonal_potential y

private noncomputable def cylinderAntipodalQuotientPotentialFn :
    CylinderAntipodalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderAntipodalPotential_respects h)

private noncomputable def cylinderDiagonalQuotientPotentialFn :
    CylinderDiagonalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderDiagonalPotential_respects h)

noncomputable def cylinderAntipodalQuotientPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real), CylinderAntipodalQuotient; Real⟯ :=
  ⟨cylinderAntipodalQuotientPotentialFn,
    cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderAntipodalQuotientMap_surjective (by
        have heq : cylinderAntipodalQuotientPotentialFn ∘
            cylinderAntipodalQuotientMap = roundThreeCylinderShrinkerPotential := by
          funext x
          rfl
        rw [heq]
        exact roundThreeCylinderShrinkerPotential.contMDiff)⟩

noncomputable def cylinderDiagonalQuotientPotential :
    C^∞⟮(𝓡 2).prod 𝓘(Real, Real), CylinderDiagonalQuotient; Real⟯ :=
  ⟨cylinderDiagonalQuotientPotentialFn,
    cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderDiagonalQuotientMap_surjective (by
        have heq : cylinderDiagonalQuotientPotentialFn ∘
            cylinderDiagonalQuotientMap = roundThreeCylinderShrinkerPotential := by
          funext x
          rfl
        rw [heq]
        exact roundThreeCylinderShrinkerPotential.contMDiff)⟩

theorem cylinderAntipodalQuotientPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientPotential (cylinderAntipodalQuotientMap x) =
      roundThreeCylinderShrinkerPotential x :=
  rfl

theorem cylinderDiagonalQuotientPotential_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientPotential (cylinderDiagonalQuotientMap x) =
      roundThreeCylinderShrinkerPotential x :=
  rfl

theorem cylinderAntipodalQuotientPotential_continuous :
    Continuous cylinderAntipodalQuotientPotential := by
  exact cylinderAntipodalQuotientPotential.contMDiff.continuous

theorem cylinderDiagonalQuotientPotential_continuous :
    Continuous cylinderDiagonalQuotientPotential := by
  exact cylinderDiagonalQuotientPotential.contMDiff.continuous

theorem normalizedGradientRicciSoliton_cylinderAntipodalQuotient :
    normalizedGradientRicciSoliton cylinderAntipodalQuotientMetric
      cylinderAntipodalQuotientPotential :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric
    normalizedGradientRicciSoliton_roundThreeCylinder
    cylinderAntipodalQuotientMetric_complete
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
    localPullMetric_cylinderAntipodalQuotientMetric
    (fun x ↦ (cylinderAntipodalQuotientPotential_apply x).symm)

theorem normalizedGradientRicciSoliton_cylinderDiagonalQuotient :
    normalizedGradientRicciSoliton cylinderDiagonalQuotientMetric
      cylinderDiagonalQuotientPotential :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric
    normalizedGradientRicciSoliton_roundThreeCylinder
    cylinderDiagonalQuotientMetric_complete
    cylinderDiagonalQuotientMap_isLocalDiffeomorph
    cylinderDiagonalQuotientMap_surjective
    localPullMetric_cylinderDiagonalQuotientMetric
    (fun x ↦ (cylinderDiagonalQuotientPotential_apply x).symm)

private theorem cylinderAntipodalToRealProjectivePlaneProduct_respects
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real}
    (hxy : MulAction.orbitRel cylinderAntipodalGroup _ x y) :
    (realProjectivePlaneQuotientMap x.1, x.2) =
      (realProjectivePlaneQuotientMap y.1, y.2) := by
  rcases hxy with ⟨psi, rfl⟩
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
  · change (realProjectivePlaneQuotientMap (psi.1 y).1, (psi.1 y).2) = _
    rw [hpsi]
    rfl
  · change (realProjectivePlaneQuotientMap (psi.1 y).1, (psi.1 y).2) = _
    rw [hpsi]
    rw [Diffeomorph.coe_toEquiv, cylinderAntipodalDiffeomorph_apply]
    apply Prod.ext
    · rw [realProjectivePlaneQuotientMap_eq_iff]
      right
      exact realProjectivePlaneAntipodalHomeomorph_coe y.1
    · rfl

private def cylinderAntipodalToRealProjectivePlaneProduct :
    CylinderAntipodalQuotient → RealProjectivePlane × Real :=
  Quotient.lift
    (fun x => (realProjectivePlaneQuotientMap x.1, x.2))
    (fun _ _ hxy =>
      cylinderAntipodalToRealProjectivePlaneProduct_respects hxy)

private theorem realProjectivePlaneProductToCylinderAntipodal_respects
    (s : Real) {x y : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1}
    (hxy : MulAction.orbitRel realProjectivePlaneAntipodalGroup _ x y) :
    cylinderAntipodalQuotientMap (x, s) =
      cylinderAntipodalQuotientMap (y, s) := by
  have hquotient : realProjectivePlaneQuotientMap x =
      realProjectivePlaneQuotientMap y :=
    Quotient.sound hxy
  rw [realProjectivePlaneQuotientMap_eq_iff] at hquotient
  rcases hquotient with rfl | hxy
  · rfl
  · rw [cylinderAntipodalQuotientMap_eq_iff]
    right
    rw [cylinderAntipodalDiffeomorph_apply]
    apply Prod.ext
    · exact Subtype.ext hxy
    · rfl

private def realProjectivePlaneProductToCylinderAntipodal :
    RealProjectivePlane × Real → CylinderAntipodalQuotient :=
  fun q => Quotient.lift
    (fun x => cylinderAntipodalQuotientMap (x, q.2))
    (fun _ _ hxy =>
      realProjectivePlaneProductToCylinderAntipodal_respects q.2 hxy) q.1

private noncomputable def cylinderAntipodalQuotientEquivRealProjectivePlaneProd :
    CylinderAntipodalQuotient ≃ RealProjectivePlane × Real where
  toFun := cylinderAntipodalToRealProjectivePlaneProduct
  invFun := realProjectivePlaneProductToCylinderAntipodal
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ x => rfl
  right_inv q := by
    rcases q with ⟨q, s⟩
    induction q using Quotient.inductionOn with
    | _ x => rfl

private theorem cylinderAntipodalToRealProjectivePlaneProduct_continuous :
    Continuous cylinderAntipodalToRealProjectivePlaneProduct := by
  exact ((continuous_quotient_mk'.comp continuous_fst).prodMk
    continuous_snd).quotient_lift
      (fun x y hxy =>
        cylinderAntipodalToRealProjectivePlaneProduct_respects hxy)

private theorem realProjectivePlaneProductToCylinderAntipodal_continuous :
    Continuous realProjectivePlaneProductToCylinderAntipodal := by
  let qmap : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      RealProjectivePlane × Real :=
    Prod.map realProjectivePlaneQuotientMap id
  have hqmap : IsOpenQuotientMap qmap :=
    realProjectivePlaneQuotientMap_isOpenQuotientMap.prodMap
      IsOpenQuotientMap.id
  rw [hqmap.isQuotientMap.continuous_iff]
  convert continuous_quotient_mk' using 1
  ext x
  rfl

noncomputable def cylinderAntipodalQuotientHomeomorph :
    CylinderAntipodalQuotient ≃ₜ RealProjectivePlane × Real where
  toEquiv := cylinderAntipodalQuotientEquivRealProjectivePlaneProd
  continuous_toFun :=
    cylinderAntipodalToRealProjectivePlaneProduct_continuous
  continuous_invFun :=
    realProjectivePlaneProductToCylinderAntipodal_continuous

theorem cylinderAntipodalQuotientHomeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientHomeomorph
        (cylinderAntipodalQuotientMap x) =
      (realProjectivePlaneQuotientMap x.1, x.2) :=
  rfl

theorem cylinderAntipodalQuotientHomeomorph_symm_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real) :
    cylinderAntipodalQuotientHomeomorph.symm
        (realProjectivePlaneQuotientMap x, s) =
      cylinderAntipodalQuotientMap (x, s) :=
  rfl

theorem noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant
    {Gamma : Type*} [Group Gamma]
    [MulAction Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)]
    (hpotential : ∀ (gamma : Gamma) x,
      roundThreeCylinderShrinkerPotential (gamma • x) =
        roundThreeCylinderShrinkerPotential x) :
    NoncompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := by
  let Fbar : MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → Real :=
    Quotient.lift roundThreeCylinderShrinkerPotential (by
      intro x y hxy
      rcases hxy with ⟨gamma, rfl⟩
      exact hpotential gamma y)
  have hFbar : Continuous Fbar :=
    roundThreeCylinderShrinkerPotential.contMDiff.continuous.quotient_lift
      (by
        intro x y hxy
        rcases hxy with ⟨gamma, rfl⟩
        exact hpotential gamma y)
  refine not_compactSpace_iff.mp ?_
  intro hcompact
  let _ : CompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := hcompact
  obtain ⟨C, hC⟩ := (isCompact_range hFbar).bddAbove
  let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
  have hle : Fbar (Quotient.mk'' (y, 2 * (|C| + 1))) ≤ C :=
    hC ⟨_, rfl⟩
  change roundThreeCylinderShrinkerPotential (y, 2 * (|C| + 1)) ≤ C at hle
  rw [roundThreeCylinderShrinkerPotential_apply] at hle
  nlinarith [abs_nonneg C, le_abs_self C]

def roundThreeCylinderSolitonAutomorphism
    (psi : Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) : Prop :=
  ∃ Phi :
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
          Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real,
    Phi.toEquiv = psi ∧
      Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric Phi =
        roundThreeCylinderShrinkerMetric ∧
      ∀ x, roundThreeCylinderShrinkerPotential (Phi x) =
        roundThreeCylinderShrinkerPotential x

theorem noncompactSpace_orbitRelQuotient_of_roundThreeCylinderSolitonAutomorphism
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1) :
    NoncompactSpace (MulAction.orbitRel.Quotient Gamma
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) := by
  apply noncompactSpace_orbitRelQuotient_of_roundThreeCylinderShrinkerPotential_invariant
  intro gamma x
  obtain ⟨Phi, hPhi, _, hpotential⟩ := hsoliton gamma
  change roundThreeCylinderShrinkerPotential (gamma.1 x) = _
  rw [← hPhi]
  exact hpotential x

private theorem roundThreeCylinderSolitonAutomorphism_mem_cases
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1)
    (gamma : Gamma) :
    gamma.1 = 1 ∨
      gamma.1 = cylinderAntipodalDiffeomorph.toEquiv ∨
      gamma.1 = cylinderDiagonalDiffeomorph.toEquiv := by
  classical
  let : Fact
      (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  choose Phi hPhiEquiv hPhiMetric hPhiPotential using hsoliton
  have hPhiApply (gamma : Gamma) (x : Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
      Phi gamma x = gamma.1 x := by
    change (Phi gamma).toEquiv x = gamma.1 x
    exact congrArg (fun e : Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) => e x)
      (hPhiEquiv gamma)
  let phi (gamma : Gamma) :=
    roundThreeCylinderCentralSliceDiffeomorph (Phi gamma) (hPhiPotential gamma)
  have hphiMetric (gamma : Gamma) :
      Diffeomorph.pullbackMetric roundTwoSphereShrinkerMetric (phi gamma) =
        roundTwoSphereShrinkerMetric :=
    roundThreeCylinderCentralSliceDiffeomorph_pullbackMetric
      (Phi gamma) (hPhiPotential gamma) (hPhiMetric gamma)
  have hphiOne (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi 1 x = x := by
    have h := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi 1) (hPhiPotential 1) x
    rw [hPhiApply] at h
    have h' := congrArg Prod.fst h
    simpa using h'.symm
  have hphiMul (gamma delta : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
      phi (gamma * delta) x = phi gamma (phi delta x) := by
    have hprod := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi (gamma * delta)) (hPhiPotential (gamma * delta)) x
    have hdelta := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi delta) (hPhiPotential delta) x
    have hgamma := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi gamma) (hPhiPotential gamma) (phi delta x)
    rw [hPhiApply] at hprod hdelta hgamma
    change gamma.1 (delta.1 (x, 0)) = _ at hprod
    rw [hdelta, hgamma] at hprod
    exact (congrArg Prod.fst hprod).symm
  have hphiIso (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
      (v w : TangentSpace (𝓡 2) x) :
      roundTwoSphereShrinkerMetric.inner x v w =
        roundTwoSphereShrinkerMetric.inner (phi gamma x)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x v)
          (mfderiv (𝓡 2) (𝓡 2) (phi gamma) x w) := by
    have h := Diffeomorph.pullbackMetric_inner
      roundTwoSphereShrinkerMetric (phi gamma) x v w
    rw [hphiMetric gamma] at h
    exact h
  have hphiFree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      phi gamma x = x → gamma = 1 := by
    intro gamma x hx
    have h := roundThreeCylinderCentralSliceDiffeomorph_apply
      (Phi gamma) (hPhiPotential gamma) x
    rw [hPhiApply] at h
    have hfix : gamma.1 (x, 0) = (x, 0) := by
      rw [h]
      exact Prod.ext hx rfl
    exact hfree gamma (x, 0) hfix
  obtain ⟨rho, hrho⟩ := orth_rep_of_iso
    (E := EuclideanSpace Real (Fin 3)) (n := 2)
    phi (by norm_num) hphiOne hphiMul (by
      intro gamma x v w
      have h := hphiIso gamma x v w
      have hscaled := h
      simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric,
        scaleMetric_inner] at hscaled
      exact mul_left_cancel₀
        (ne_of_gt (sq_pos_of_pos (roundSphereShrinkerRadius_pos (n := 2) (by decide))))
        hscaled)
  have hphiFree' : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1),
      sphereDiffeo (n := 2) (rho gamma) x = x → gamma = 1 := by
    intro gamma x hx
    apply hphiFree gamma x
    rw [← hrho gamma]
    exact hx
  have hcase (gamma : Gamma) :
      rho gamma = 1 ∨ rho gamma = LinearIsometryEquiv.neg Real := by
    exact orth_rep_apply_eq_one_or_neg_of_free_sphere_action rho hphiFree' gamma
  have hphiRep (gamma : Gamma) :
      sphereDiffeo (n := 2) (rho gamma) = phi gamma := hrho gamma
  have hcases (gamma : Gamma) :
      gamma.1 = 1 ∨ gamma.1 = cylinderAntipodalDiffeomorph.toEquiv ∨
        gamma.1 = cylinderDiagonalDiffeomorph.toEquiv := by
    by_cases hgamma : gamma = 1
    · left
      subst gamma
      rfl
    · have hnormal := roundThreeCylinderDiffeomorph_eq_prodCongr_refl_or_neg
        (Phi gamma) (hPhiPotential gamma) (hPhiMetric gamma)
      rcases hnormal with hnormal | hnormal
      · rcases hcase gamma with hρ | hρ
        · have hφ : ∀ x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
              phi gamma x = x := by
            intro x
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          have hmap : gamma.1 = 1 := by
            apply Equiv.ext
            intro x
            rw [← hPhiEquiv gamma, hnormal]
            change (phi gamma x.1, x.2) = x
            exact Prod.ext (hφ x.1) (by rfl)
          exact (hgamma (Subtype.ext hmap)).elim
        · right; left
          apply Equiv.ext
          intro x
          rw [← hPhiEquiv gamma, hnormal]
          rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
          change (phi gamma x.1, x.2) = _
          have hφ : phi gamma x.1 = -x.1 := by
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          change (phi gamma x.1, x.2) = cylinderAntipodalDiffeomorph x
          rw [cylinderAntipodalDiffeomorph_apply]
          exact Prod.ext hφ (by rfl)
      · rcases hcase gamma with hρ | hρ
        · have hφ : ∀ x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
              phi gamma x = x := by
            intro x
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          have hfix : gamma.1 (⟨EuclideanSpace.single 0 1, by
              simp [PiLp.norm_single]⟩, 0) =
              (⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩, 0) := by
            rw [← hPhiEquiv gamma, hnormal]
            rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
            change (phi gamma _, (ContinuousLinearEquiv.neg Real) 0) = _
            exact Prod.ext (hφ _) (by simp only [map_zero])
          exact (hgamma (hfree gamma _ hfix)).elim
        · right; right
          apply Equiv.ext
          intro x
          rw [← hPhiEquiv gamma, hnormal]
          rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_prodCongr]
          change (phi gamma x.1, (ContinuousLinearEquiv.neg Real) x.2) = _
          have hφ : phi gamma x.1 = -x.1 := by
            rw [← hphiRep gamma, hρ]
            apply Subtype.ext
            rfl
          rw [Diffeomorph.coe_toEquiv]
          change (phi gamma x.1, (ContinuousLinearEquiv.neg Real) x.2) =
            cylinderDiagonalDiffeomorph x
          rw [cylinderDiagonalDiffeomorph_apply]
          exact Prod.ext hφ (by simp [cylinderDiagonal])
  exact hcases gamma

theorem roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1) :
    Gamma = ⊥ ∨ Gamma = cylinderAntipodalGroup ∨
      Gamma = cylinderDiagonalGroup := by
  classical
  have hnotBoth : ∀ (ha : cylinderAntipodalDiffeomorph.toEquiv ∈ Gamma)
      (hd : cylinderDiagonalDiffeomorph.toEquiv ∈ Gamma), False := by
    intro ha hd
    let ga : Gamma := ⟨cylinderAntipodalDiffeomorph.toEquiv, ha⟩
    let gd : Gamma := ⟨cylinderDiagonalDiffeomorph.toEquiv, hd⟩
    let y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    have hfix : (ga * gd).1 (y, 0) = (y, 0) := by
      change ga.1 (gd.1 (y, 0)) = (y, 0)
      change cylinderAntipodalDiffeomorph.toEquiv
          (cylinderDiagonalDiffeomorph.toEquiv (y, 0)) = (y, 0)
      rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_toEquiv,
        cylinderDiagonalDiffeomorph_apply, cylinderAntipodalDiffeomorph_apply]
      simp [cylinderAntipodal, cylinderDiagonal]
    have hprod : ga * gd = 1 := hfree (ga * gd) (y, 0) hfix
    have hact := congrArg (fun gamma : Gamma => gamma.1 (y, 1)) hprod
    change ga.1 (gd.1 (y, 1)) = (y, 1) at hact
    change cylinderAntipodalDiffeomorph.toEquiv
        (cylinderDiagonalDiffeomorph.toEquiv (y, 1)) = (y, 1) at hact
    rw [Diffeomorph.coe_toEquiv, Diffeomorph.coe_toEquiv,
      cylinderDiagonalDiffeomorph_apply, cylinderAntipodalDiffeomorph_apply] at hact
    have hsnd := congrArg Prod.snd hact
    simp [cylinderAntipodal, cylinderDiagonal] at hsnd
    norm_num at hsnd
  by_cases ha : ∃ gamma : Gamma,
      gamma.1 = cylinderAntipodalDiffeomorph.toEquiv
  · obtain ⟨gammaA, hgammaA⟩ := ha
    have ha_mem : cylinderAntipodalDiffeomorph.toEquiv ∈ Gamma := by
      simpa [hgammaA] using gammaA.property
    have hnotD : ∀ gamma : Gamma,
        gamma.1 ≠ cylinderDiagonalDiffeomorph.toEquiv := by
      intro gamma hgamma
      apply hnotBoth ha_mem
      simpa [hgamma] using gamma.property
    right; left
    apply le_antisymm
    · intro gamma hgamma
      change gamma ∈ Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv
      rcases roundThreeCylinderSolitonAutomorphism_mem_cases
        Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
      · change gamma = 1 at h1
        rw [h1]
        exact Subgroup.one_mem _
      · change gamma = cylinderAntipodalDiffeomorph.toEquiv at ha'
        rw [ha']
        exact Subgroup.mem_zpowers _
      · exact (hnotD ⟨gamma, hgamma⟩ hd').elim
    · change Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv ≤ Gamma
      exact Subgroup.zpowers_le.mpr ha_mem
  · by_cases hd : ∃ gamma : Gamma,
        gamma.1 = cylinderDiagonalDiffeomorph.toEquiv
    · obtain ⟨gammaD, hgammaD⟩ := hd
      have hd_mem : cylinderDiagonalDiffeomorph.toEquiv ∈ Gamma := by
        simpa [hgammaD] using gammaD.property
      have hnotA : ∀ gamma : Gamma,
          gamma.1 ≠ cylinderAntipodalDiffeomorph.toEquiv := by
        intro gamma hgamma
        exact ha ⟨gamma, hgamma⟩
      right; right
      apply le_antisymm
      · intro gamma hgamma
        change gamma ∈ Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv
        rcases roundThreeCylinderSolitonAutomorphism_mem_cases
          Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
        · change gamma = 1 at h1
          rw [h1]
          exact Subgroup.one_mem _
        · exact (hnotA ⟨gamma, hgamma⟩ ha').elim
        · change gamma = cylinderDiagonalDiffeomorph.toEquiv at hd'
          rw [hd']
          exact Subgroup.mem_zpowers _
      · change Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv ≤ Gamma
        exact Subgroup.zpowers_le.mpr hd_mem
    · left
      apply (Subgroup.eq_bot_iff_forall Gamma).mpr
      intro gamma hgamma
      rcases roundThreeCylinderSolitonAutomorphism_mem_cases
        Gamma hsoliton hfree ⟨gamma, hgamma⟩ with h1 | ha' | hd'
      · change gamma = 1 at h1
        exact h1
      · exact (ha ⟨⟨gamma, hgamma⟩, ha'⟩).elim
      · exact (hd ⟨⟨gamma, hgamma⟩, hd'⟩).elim

theorem roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy
    (Gamma : Subgroup (Equiv.Perm
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)))
    (hsoliton : ∀ gamma : Gamma,
      roundThreeCylinderSolitonAutomorphism gamma.1)
    (hfree : ∀ (gamma : Gamma)
      (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real),
      gamma.1 x = x → gamma = 1) :
    (Gamma = ⊥ ∧ Gamma ≠ cylinderAntipodalGroup ∧
      Gamma ≠ cylinderDiagonalGroup) ∨
    (Gamma = cylinderAntipodalGroup ∧ Gamma ≠ ⊥ ∧
      Gamma ≠ cylinderDiagonalGroup) ∨
    (Gamma = cylinderDiagonalGroup ∧ Gamma ≠ ⊥ ∧
      Gamma ≠ cylinderAntipodalGroup) := by
  rcases
      roundThreeCylinderSolitonAutomorphism_subgroup_eq_bot_or_antipodal_or_diagonal
        Gamma hsoliton hfree with hGamma | hGamma | hGamma
  · subst Gamma
    exact Or.inl ⟨rfl, cylinderAntipodalGroup_ne_bot.symm,
      cylinderDiagonalGroup_ne_bot.symm⟩
  · subst Gamma
    exact Or.inr (Or.inl ⟨rfl, cylinderAntipodalGroup_ne_bot,
      cylinderAntipodalGroup_ne_cylinderDiagonalGroup⟩)
  · subst Gamma
    exact Or.inr (Or.inr ⟨rfl, cylinderDiagonalGroup_ne_bot,
      cylinderAntipodalGroup_ne_cylinderDiagonalGroup.symm⟩)

end DifferentialGeometry.Geometry
