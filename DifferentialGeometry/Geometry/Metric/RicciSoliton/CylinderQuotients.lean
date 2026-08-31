import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem realNegDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric (euclideanMetric (E := Real))
        (ContinuousLinearEquiv.neg Real).toDiffeomorph =
      euclideanMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner,
    DifferentialGeometry.euclideanMetric_inner,
    DifferentialGeometry.euclideanMetric_inner]
  change inner Real
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun q : Real => -q) x v)
      (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun q : Real => -q) x w) =
    inner Real v w
  have hmf (z a : Real) :
      mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun q : Real => -q) z a = -a := by
    rw [mfderiv_eq_fderiv]
    change (fderiv Real (fun q : Real => -q) z) a = -a
    rw [show (fun q : Real => -q) = -(id : Real → Real) by rfl,
      fderiv_neg, fderiv_id]
    rfl
  calc
    inner Real
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun q : Real => -q) x v)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) (fun q : Real => -q) x w) =
      inner Real (-v) (-w) :=
        congrArg₂ (inner Real) (hmf x v) (hmf x w)
    _ = inner Real v w := by
      exact inner_neg_neg v w

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
  [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {G : Type*} [TopologicalSpace G]
variable {J : ModelWithCorners Real F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
variable [T2Space M] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem pullbackMetric_prodCongr
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Phi : M ≃ₘ⟮I, I⟯ M) (Psi : N ≃ₘ⟮J, J⟯ N) :
    Diffeomorph.pullbackMetric (g.prod h) (Phi.prodCongr Psi) =
      (Diffeomorph.pullbackMetric g Phi).prod
        (Diffeomorph.pullbackMetric h Psi) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetric_inner,
    SmoothRiemannianMetric.prod_inner,
    SmoothRiemannianMetric.prod_inner,
    Diffeomorph.pullbackMetric_inner,
    Diffeomorph.pullbackMetric_inner]
  have hPhi : MDiffAt (Phi : M → M) x.1 :=
    Phi.contMDiff.mdifferentiableAt (by simp)
  have hPsi : MDiffAt (Psi : N → N) x.2 :=
    Psi.contMDiff.mdifferentiableAt (by simp)
  rw [Diffeomorph.coe_prodCongr]
  rw [mfderiv_prodMap hPhi hPsi]
  simp [ContinuousLinearMap.prodMap]
  rfl

theorem cylinderAntipodalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderAntipodalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  rw [roundThreeCylinderShrinkerMetric,
    cylinderAntipodalDiffeomorph,
    pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    Diffeomorph.pullbackMetric_refl]

theorem cylinderDiagonalDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetric roundThreeCylinderShrinkerMetric
        cylinderDiagonalDiffeomorph =
      roundThreeCylinderShrinkerMetric := by
  rw [roundThreeCylinderShrinkerMetric,
    cylinderDiagonalDiffeomorph,
    pullbackMetric_prodCongr,
    roundTwoSphereAntipodalDiffeomorph_pullbackMetric,
    realNegDiffeomorph_pullbackMetric]

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

end DifferentialGeometry.Geometry
