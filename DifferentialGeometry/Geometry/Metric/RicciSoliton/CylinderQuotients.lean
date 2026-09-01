import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderIsometry
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Metric.Sphere.FreeOrthogonalAction
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryRepresentation
import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
import DifferentialGeometry.Topology.ProperlyDiscontinuousAction
import Mathlib.Geometry.Manifold.Instances.Quotient
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

def cylinderAntipodal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, x.2)

def cylinderDiagonal :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real →
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  fun x => (-x.1, -x.2)

private noncomputable def roundTwoSphereAntipodalDiffeomorph :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
      Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := by
  let : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact sphereDiffeo (n := 2) (LinearIsometryEquiv.neg Real)

noncomputable def cylinderAntipodalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (Diffeomorph.refl 𝓘(Real, Real) Real ∞)

noncomputable def cylinderDiagonalDiffeomorph :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real :=
  roundTwoSphereAntipodalDiffeomorph.prodCongr
    (ContinuousLinearEquiv.neg Real).toDiffeomorph

theorem cylinderAntipodal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x = (-x.1, x.2) := rfl

theorem cylinderDiagonal_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x = (-x.1, -x.2) := rfl

private theorem roundTwoSphereAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) :
    roundTwoSphereAntipodalDiffeomorph x = -x := by
  apply Subtype.ext
  simp [roundTwoSphereAntipodalDiffeomorph]

theorem cylinderAntipodalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x = cylinderAntipodal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

theorem cylinderDiagonalDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x = cylinderDiagonal x := by
  apply Prod.ext
  · exact roundTwoSphereAntipodalDiffeomorph_apply x.1
  · rfl

theorem cylinderAntipodal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal (cylinderAntipodal x) = x := by
  apply Prod.ext
  · simp [cylinderAntipodal]
  · simp [cylinderAntipodal]

theorem cylinderDiagonal_involutive (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal (cylinderDiagonal x) = x := by
  apply Prod.ext
  · simp [cylinderDiagonal]
  · simp [cylinderDiagonal]

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

theorem cylinderAntipodal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

theorem cylinderDiagonal_fixed_point_free (x :
    Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonal x ≠ x := by
  intro h
  have hsphere : -x.1 = x.1 := congrArg Prod.fst h
  have hzero : (x.1 : EuclideanSpace Real (Fin 3)) = 0 := by
    apply_fun (fun z : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 =>
      (z : EuclideanSpace Real (Fin 3))) at hsphere
    have hamb : -(x.1 : EuclideanSpace Real (Fin 3)) = x.1 := by
      simpa using hsphere
    ext i
    have hi := congrArg (fun z : EuclideanSpace Real (Fin 3) => z i) hamb
    simp only [PiLp.neg_apply, PiLp.zero_apply] at hi ⊢
    linarith
  have hnorm := x.1.2
  rw [hzero] at hnorm
  norm_num at hnorm

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
          (LinearIsometryEquiv.neg Real : Real ≃ₗᵢ[Real] Real).toContinuousLinearEquiv.toDiffeomorph := by
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

theorem cylinderAntipodalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalDiffeomorph x ≠ x := by
  rw [cylinderAntipodalDiffeomorph_apply]
  exact cylinderAntipodal_fixed_point_free x

theorem cylinderDiagonalDiffeomorph_fixed_point_free
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalDiffeomorph x ≠ x := by
  rw [cylinderDiagonalDiffeomorph_apply]
  exact cylinderDiagonal_fixed_point_free x

private theorem perm_orderOf_eq_two {X : Type*} [Nonempty X]
    (phi : Equiv.Perm X) (hinvolutive : Function.Involutive phi)
    (hfree : ∀ x, phi x ≠ x) :
    orderOf phi = 2 := by
  apply orderOf_eq_prime
  · ext x
    exact hinvolutive x
  · intro h
    obtain ⟨x⟩ := ‹Nonempty X›
    exact hfree x (by rw [h]; rfl)

private theorem mem_zpowers_perm_order_two_iff {X : Type*}
    (phi : Equiv.Perm X) (horder : orderOf phi = 2) (psi : Equiv.Perm X) :
    psi ∈ Subgroup.zpowers phi ↔ psi = 1 ∨ psi = phi := by
  classical
  have hfinite : IsOfFinOrder phi :=
    orderOf_pos_iff.mp (by rw [horder]; exact Nat.zero_lt_two)
  constructor
  · intro hpsi
    have hrange := hfinite.mem_zpowers_iff_mem_range_orderOf.mp hpsi
    rw [horder] at hrange
    rcases Finset.mem_image.mp hrange with ⟨n, hn, rfl⟩
    simp only [Finset.mem_range] at hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

noncomputable def cylinderAntipodalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderAntipodalDiffeomorph.toEquiv

noncomputable def cylinderDiagonalGroup : Subgroup (Equiv.Perm
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)) :=
  Subgroup.zpowers cylinderDiagonalDiffeomorph.toEquiv

instance cylinderAntipodalGroupMulAction :
    MulAction cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  MulAction.instMulAction cylinderAntipodalGroup

instance cylinderDiagonalGroupMulAction :
    MulAction cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
  MulAction.instMulAction cylinderDiagonalGroup

theorem cylinderAntipodalGroup_orderOf :
    orderOf cylinderAntipodalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderAntipodalDiffeomorph
        (cylinderAntipodalDiffeomorph x) = x
    rw [cylinderAntipodalDiffeomorph_apply,
      cylinderAntipodalDiffeomorph_apply]
    exact cylinderAntipodal_involutive x
  · exact cylinderAntipodalDiffeomorph_fixed_point_free

theorem cylinderDiagonalGroup_orderOf :
    orderOf cylinderDiagonalDiffeomorph.toEquiv = 2 := by
  let : Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :=
    ⟨⟨Classical.choice
      (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype, 0⟩⟩
  apply perm_orderOf_eq_two
  · intro x
    change cylinderDiagonalDiffeomorph
        (cylinderDiagonalDiffeomorph x) = x
    rw [cylinderDiagonalDiffeomorph_apply,
      cylinderDiagonalDiffeomorph_apply]
    exact cylinderDiagonal_involutive x
  · exact cylinderDiagonalDiffeomorph_fixed_point_free

theorem cylinderAntipodalGroup_eq_one_or_generator
    (psi : cylinderAntipodalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderAntipodalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderAntipodalGroup_orderOf psi.1).mp psi.2

theorem cylinderDiagonalGroup_eq_one_or_generator
    (psi : cylinderDiagonalGroup) :
    psi.1 = 1 ∨ psi.1 = cylinderDiagonalDiffeomorph.toEquiv := by
  exact (mem_zpowers_perm_order_two_iff _
    cylinderDiagonalGroup_orderOf psi.1).mp psi.2

noncomputable instance cylinderAntipodalGroupFinite :
    Finite cylinderAntipodalGroup := by
  have hfinite : IsOfFinOrder cylinderAntipodalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderAntipodalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderAntipodalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

noncomputable instance cylinderDiagonalGroupFinite :
    Finite cylinderDiagonalGroup := by
  have hfinite : IsOfFinOrder cylinderDiagonalDiffeomorph.toEquiv :=
    orderOf_pos_iff.mp (by
      rw [cylinderDiagonalGroup_orderOf]
      exact Nat.zero_lt_two)
  exact Finite.of_equiv
    (Fin (orderOf cylinderDiagonalDiffeomorph.toEquiv))
    (finEquivZPowers hfinite)

noncomputable def cylinderAntipodalGroupGenerator : cylinderAntipodalGroup :=
  ⟨cylinderAntipodalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

noncomputable def cylinderDiagonalGroupGenerator : cylinderDiagonalGroup :=
  ⟨cylinderDiagonalDiffeomorph.toEquiv, Subgroup.mem_zpowers _⟩

theorem cylinderAntipodalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderAntipodalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderAntipodalGroupMulAction.toSMul
        cylinderAntipodalGroupGenerator x =
      cylinderAntipodalDiffeomorph x :=
  rfl

theorem cylinderDiagonalGroupGenerator_smul
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    @SMul.smul cylinderDiagonalGroup
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
        cylinderDiagonalGroupMulAction.toSMul
        cylinderDiagonalGroupGenerator x =
      cylinderDiagonalDiffeomorph x :=
  rfl

instance cylinderAntipodalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderAntipodalDiffeomorph.continuous

instance cylinderDiagonalGroupContinuousConstSMul :
    ContinuousConstSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) where
  continuous_const_smul psi := by
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with hpsi | hpsi
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact continuous_id
    · change Continuous (psi.1 :
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → _)
      rw [hpsi]
      exact cylinderDiagonalDiffeomorph.continuous

instance cylinderAntipodalGroupIsCancelSMul :
    IsCancelSMul cylinderAntipodalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderAntipodalDiffeomorph_fixed_point_free x hpsi

instance cylinderDiagonalGroupIsCancelSMul :
    IsCancelSMul cylinderDiagonalGroup
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro psi x hpsi
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · exact Subtype.ext h
  · exfalso
    change psi.1 x = x at hpsi
    rw [h] at hpsi
    exact cylinderDiagonalDiffeomorph_fixed_point_free x hpsi

private theorem cylinderAntipodalDiffeomorph_toEquiv_ne_one :
    cylinderAntipodalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderAntipodalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

private theorem cylinderDiagonalDiffeomorph_toEquiv_ne_one :
    cylinderDiagonalDiffeomorph.toEquiv ≠ 1 := by
  intro h
  have horder := cylinderDiagonalGroup_orderOf
  rw [h, orderOf_one] at horder
  omega

noncomputable def cylinderAntipodalGroupDiffeomorph
    (psi : cylinderAntipodalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderAntipodalDiffeomorph

noncomputable def cylinderDiagonalGroupDiffeomorph
    (psi : cylinderDiagonalGroup) :
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
      ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), (𝓡 2).prod 𝓘(Real, Real)⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real := by
  classical
  exact if psi.1 = 1 then
      Diffeomorph.refl ((𝓡 2).prod 𝓘(Real, Real))
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ∞
    else cylinderDiagonalDiffeomorph

theorem cylinderAntipodalGroupDiffeomorph_apply
    (psi : cylinderAntipodalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderAntipodalGroupDiffeomorph, h]
  · simp [cylinderAntipodalGroupDiffeomorph, h,
      cylinderAntipodalDiffeomorph_toEquiv_ne_one]

theorem cylinderDiagonalGroupDiffeomorph_apply
    (psi : cylinderDiagonalGroup)
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalGroupDiffeomorph psi x = psi.1 x := by
  rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
  · simp [cylinderDiagonalGroupDiffeomorph, h]
  · simp [cylinderDiagonalGroupDiffeomorph, h,
      cylinderDiagonalDiffeomorph_toEquiv_ne_one]

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

abbrev CylinderAntipodalQuotient := MulAction.orbitRel.Quotient
  cylinderAntipodalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

abbrev CylinderDiagonalQuotient := MulAction.orbitRel.Quotient
  cylinderDiagonalGroup
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)

def cylinderAntipodalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderAntipodalQuotient := Quotient.mk'' x

def cylinderDiagonalQuotientMap
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    CylinderDiagonalQuotient := Quotient.mk'' x

theorem cylinderAntipodalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderAntipodalQuotientMap
      cylinderAntipodalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem cylinderDiagonalQuotientMap_isQuotientCoveringMap :
    IsQuotientCoveringMap cylinderDiagonalQuotientMap
      cylinderDiagonalGroup := by
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem cylinderAntipodalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.isCoveringMap

theorem cylinderDiagonalQuotientMap_isCoveringMap :
    IsCoveringMap cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.isCoveringMap

theorem cylinderAntipodalQuotientMap_surjective :
    Function.Surjective cylinderAntipodalQuotientMap :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.surjective

theorem cylinderDiagonalQuotientMap_surjective :
    Function.Surjective cylinderDiagonalQuotientMap :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.surjective

theorem cylinderAntipodalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderAntipodalGroup y :=
  cylinderAntipodalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

theorem cylinderDiagonalQuotientMap_eq_iff_mem_orbit
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x ∈ MulAction.orbit cylinderDiagonalGroup y :=
  cylinderDiagonalQuotientMap_isQuotientCoveringMap.apply_eq_iff_mem_orbit

theorem cylinderAntipodalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderAntipodalQuotientMap x = cylinderAntipodalQuotientMap y ↔
      x = y ∨ x = cylinderAntipodalDiffeomorph y := by
  rw [cylinderAntipodalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderAntipodalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderAntipodalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderAntipodalGroupGenerator, ?_⟩
      exact cylinderAntipodalGroupGenerator_smul y

theorem cylinderDiagonalQuotientMap_eq_iff
    {x y : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real} :
    cylinderDiagonalQuotientMap x = cylinderDiagonalQuotientMap y ↔
      x = y ∨ x = cylinderDiagonalDiffeomorph y := by
  rw [cylinderDiagonalQuotientMap_eq_iff_mem_orbit]
  constructor
  · rintro ⟨psi, rfl⟩
    rcases cylinderDiagonalGroup_eq_one_or_generator psi with h | h
    · left
      change psi.1 y = y
      rw [h]
      rfl
    · right
      change psi.1 y = cylinderDiagonalDiffeomorph y
      rw [h]
      rfl
  · rintro (rfl | h)
    · exact MulAction.mem_orbit_self _
    · rw [h]
      refine ⟨cylinderDiagonalGroupGenerator, ?_⟩
      exact cylinderDiagonalGroupGenerator_smul y

theorem cylinderAntipodalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderAntipodalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderAntipodalQuotient → Y,
      Fbar ∘ cylinderAntipodalQuotientMap = F := by
  let Fbar : CylinderAntipodalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

theorem cylinderDiagonalQuotientMap_lift_unique {Y : Type*}
    (F : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real → Y)
    (hinvariant : ∀ psi : cylinderDiagonalGroup, ∀ x, F (psi.1 x) = F x) :
    ∃! Fbar : CylinderDiagonalQuotient → Y,
      Fbar ∘ cylinderDiagonalQuotientMap = F := by
  let Fbar : CylinderDiagonalQuotient → Y :=
    Quotient.lift F (by
      intro x y hxy
      rcases hxy with ⟨psi, rfl⟩
      exact hinvariant psi y)
  refine ⟨Fbar, ?_, ?_⟩
  · funext x
    rfl
  · intro G hG
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun hG x

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

noncomputable def cylinderAntipodalQuotientPotential :
    CylinderAntipodalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderAntipodalPotential_respects h)

noncomputable def cylinderDiagonalQuotientPotential :
    CylinderDiagonalQuotient → Real :=
  Quotient.lift roundThreeCylinderShrinkerPotential
    (fun _ _ h => cylinderDiagonalPotential_respects h)

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
  exact roundThreeCylinderShrinkerPotential.contMDiff.continuous.quotient_lift
    (fun _ _ hxy => cylinderAntipodalPotential_respects hxy)

theorem cylinderDiagonalQuotientPotential_continuous :
    Continuous cylinderDiagonalQuotientPotential := by
  exact roundThreeCylinderShrinkerPotential.contMDiff.continuous.quotient_lift
    (fun _ _ hxy => cylinderDiagonalPotential_respects hxy)

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
    (Classical.choice (show Nonempty (Metric.sphere
      (0 : EuclideanSpace Real (Fin 3)) 1) from ⟨⟨EuclideanSpace.single 0 1, by
        simp [PiLp.norm_single]⟩⟩))
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

theorem roundThreeCylinderSolitonAutomorphism_subgroup_eq_trichotomy
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

end DifferentialGeometry.Geometry
