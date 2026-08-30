import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.Sphere.OrthogonalAction

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

end DifferentialGeometry.Geometry
