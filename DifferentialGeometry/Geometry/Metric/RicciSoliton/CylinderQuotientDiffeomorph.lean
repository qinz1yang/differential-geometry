import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotients
import DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThreeManifold
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Geometry.Metric.ProjectiveSpace

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open Filter Topology

namespace DifferentialGeometry.Geometry

local instance : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

noncomputable def cylinderAntipodalQuotientDiffeomorph :
    CylinderAntipodalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real),
      (𝓡 2).prod 𝓘(Real, Real)⟯ RealProjectivePlane × Real where
  toEquiv := cylinderAntipodalQuotientHomeomorph.toEquiv
  contMDiff_toFun := by
    apply cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderAntipodalQuotientMap_surjective
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real))
      ((𝓡 2).prod 𝓘(Real, Real)) ∞
      (fun x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real =>
        (realProjectivePlaneQuotientMap x.1, x.2))
    exact ((realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2)).contMDiff.comp
      contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := by
    rintro ⟨y, s⟩
    obtain ⟨x, rfl⟩ := realProjectivePlaneQuotientMap_surjective y
    let hlocal := realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2) x
    have hinv : ContMDiffAt ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 2) ∞
        (fun z : RealProjectivePlane × Real => hlocal.localInverse z.1)
        (realProjectivePlaneQuotientMap x, s) :=
      hlocal.localInverse_contMDiffAt.comp
        (f := fun z : RealProjectivePlane × Real => z.1)
        (realProjectivePlaneQuotientMap x, s) contMDiffAt_fst
    have hsmooth := cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff.contMDiffAt.comp
      (realProjectivePlaneQuotientMap x, s) (hinv.prodMk contMDiffAt_snd)
    apply hsmooth.congr_of_eventuallyEq
    have hevent := hlocal.localInverse_eventuallyEq_right.comp_tendsto
      (continuous_fst.tendsto (realProjectivePlaneQuotientMap x, s))
    filter_upwards [hevent] with z hz
    change cylinderAntipodalQuotientHomeomorph.symm z =
      cylinderAntipodalQuotientMap (hlocal.localInverse z.1, z.2)
    apply cylinderAntipodalQuotientHomeomorph.injective
    rw [Homeomorph.apply_symm_apply, cylinderAntipodalQuotientHomeomorph_apply]
    exact Prod.ext hz.symm rfl

@[simp] theorem cylinderAntipodalQuotientDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderAntipodalQuotientDiffeomorph (cylinderAntipodalQuotientMap x) =
      (realProjectivePlaneQuotientMap x.1, x.2) := rfl

@[simp] theorem cylinderAntipodalQuotientDiffeomorph_symm_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) (s : Real) :
    cylinderAntipodalQuotientDiffeomorph.symm (realProjectivePlaneQuotientMap x, s) =
      cylinderAntipodalQuotientMap (x, s) := rfl

noncomputable def cylinderDiagonalQuotientDiffeomorph :
    CylinderDiagonalQuotient ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), 𝓡 3⟯
      PuncturedRealProjectiveThreeSpace where
  toEquiv := cylinderDiagonalQuotientHomeomorph.toEquiv
  contMDiff_toFun := by
    apply cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff_of_comp_of_surjective
      cylinderDiagonalQuotientMap_surjective
    apply (ContMDiff.subtypeVal_comp_iff
      (⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
        isOpen_compl_singleton⟩ : TopologicalSpace.Opens RealProjectiveThreeSpace) _).mp
    change ContMDiff ((𝓡 2).prod 𝓘(Real, Real)) (𝓡 3) ∞
      (fun x => realProjectiveSpaceQuotientMap
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).1)
    let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩
    exact (realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 4)) (n := 3)).contMDiff.comp
      ((contMDiff_subtype_val (U := ⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩)).comp
        twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.contMDiff)
  contMDiff_invFun := by
    intro y
    let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩
    obtain ⟨z, hz⟩ := realProjectiveSpaceQuotientMap_surjective y.1
    let z' : threeSphereAwayFromRealProjectivePuncture := ⟨z, by
      change realProjectiveSpaceQuotientMap z ≠ realProjectiveThreeSpacePuncture
      rw [hz]
      exact y.2⟩
    have hp : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
        (fun z : threeSphereAwayFromRealProjectivePuncture => realProjectiveSpaceQuotientMap z.1) :=
      isLocalDiffeomorph_restrict_open
        (⟨_, isOpen_threeSphereAwayFromRealProjectivePuncture⟩ :
          TopologicalSpace.Opens (Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1))
        (realProjectiveSpaceQuotientMap_isLocalDiffeomorph.isLocalDiffeomorphOn _)
    let hlocal := hp z'
    have hv : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (Subtype.val : PuncturedRealProjectiveThreeSpace → RealProjectiveThreeSpace) y :=
      (contMDiff_subtype_val (U :=
        ⟨{q : RealProjectiveThreeSpace | q ≠ realProjectiveThreeSpacePuncture},
          isOpen_compl_singleton⟩)).contMDiffAt
    have hi : ContMDiffAt (𝓡 3) (𝓡 3) ∞
        (fun q : PuncturedRealProjectiveThreeSpace => hlocal.localInverse q.1) y := by
      have hl := hlocal.localInverse_contMDiffAt
      change ContMDiffAt (𝓡 3) (𝓡 3) ∞ hlocal.localInverse
        (realProjectiveSpaceQuotientMap z) at hl
      rw [hz] at hl
      exact hl.comp y hv
    have hsmooth := cylinderDiagonalQuotientMap_isLocalDiffeomorph.contMDiff.contMDiffAt.comp y
      (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm.contMDiff.contMDiffAt.comp y hi)
    apply hsmooth.congr_of_eventuallyEq
    have hevent := hlocal.localInverse_eventuallyEq_right
    change (fun q => realProjectiveSpaceQuotientMap (hlocal.localInverse q).1) =ᶠ[
      𝓝 (realProjectiveSpaceQuotientMap z)] id at hevent
    rw [hz] at hevent
    have hevent' := hevent.comp_tendsto (continuous_subtype_val.tendsto y)
    filter_upwards [hevent'] with q hq
    change cylinderDiagonalQuotientHomeomorph.symm q =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture.symm
          (hlocal.localInverse q.1))
    rw [← cylinderDiagonalQuotientHomeomorph_symm_apply]
    congr 1
    exact Subtype.ext hq.symm

@[simp] theorem cylinderDiagonalQuotientDiffeomorph_apply
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) :
    cylinderDiagonalQuotientDiffeomorph (cylinderDiagonalQuotientMap x) =
      ⟨realProjectiveSpaceQuotientMap
          (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).1,
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture x).2⟩ := rfl

@[simp] theorem cylinderDiagonalQuotientDiffeomorph_symm_apply
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientDiffeomorph.symm
        ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩ =
      cylinderDiagonalQuotientMap
        (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm z) :=
  cylinderDiagonalQuotientHomeomorph_symm_apply z

theorem cylinderAntipodalQuotientDiffeomorph_potential
    (x : RealProjectivePlane × Real) :
    cylinderAntipodalQuotientPotential (cylinderAntipodalQuotientDiffeomorph.symm x) =
      1 + x.2 ^ 2 / 4 := by
  obtain ⟨y, hy⟩ := realProjectivePlaneQuotientMap_surjective x.1
  have heq : x = (realProjectivePlaneQuotientMap y, x.2) := Prod.ext hy.symm rfl
  rw [heq, cylinderAntipodalQuotientDiffeomorph_symm_apply,
    cylinderAntipodalQuotientPotential_apply, roundThreeCylinderShrinkerPotential_apply]

theorem cylinderDiagonalQuotientDiffeomorph_potential
    (z : threeSphereAwayFromRealProjectivePuncture) :
    cylinderDiagonalQuotientPotential
        (cylinderDiagonalQuotientDiffeomorph.symm
          ⟨realProjectiveSpaceQuotientMap z.1, z.2⟩) =
      1 + (twoSphereProdRealDiffeomorphThreeSphereAwayFromRealProjectivePuncture.symm z).2 ^ 2 / 4 := by
  rw [cylinderDiagonalQuotientDiffeomorph_symm_apply,
    cylinderDiagonalQuotientPotential_apply, roundThreeCylinderShrinkerPotential_apply]

private theorem roundProjectiveQuotientMap_inner
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) x) :
    (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner
      (realProjectivePlaneQuotientMap x)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x v)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x w) =
      (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)).inner x v w := by
  have hround := congrArg
    (fun k : SmoothRiemannianMetric (𝓡 2) (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) =>
      k.inner x v w)
    (localPullMetric_roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  exact hround

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem sphereRealProduct_inner
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace Real (Fin 2)) M]
    [T2Space M]
    [IsManifold (𝓡 2) ∞ M]
    (g : SmoothRiemannianMetric (𝓡 2) M) (h : SmoothRiemannianMetric 𝓘(Real, Real) Real)
    (x : M × Real) (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    (g.prod h).inner x v w = g.inner x.1 v.1 w.1 + h.inner x.2 v.2 w.2 := by
  exact SmoothRiemannianMetric.prod_inner g h x v w

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cylinderProjectiveQuotientMap_inner
    (x : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(Real, Real)) x) :
    ((scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real))).inner
      (realProjectivePlaneQuotientMap x.1, x.2)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x v)
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x w) =
      roundThreeCylinderShrinkerMetric.inner x v w := by
  change EuclideanSpace Real (Fin 2) × Real at v w
  have hp : MDifferentiable (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap :=
    (realProjectiveSpaceQuotientMap_isLocalDiffeomorph
      (E := EuclideanSpace Real (Fin 3)) (n := 2)).mdifferentiable (by simp)
  erw [mfderiv_prodMap hp.mdifferentiableAt mdifferentiable_id.mdifferentiableAt,
    sphereRealProduct_inner, roundThreeCylinderShrinkerMetric, sphereRealProduct_inner]
  change (scaleMetric 2 (by norm_num)
      (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).inner
      (realProjectivePlaneQuotientMap x.1)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x.1 v.1)
      (mfderiv (𝓡 2) (𝓡 2) realProjectivePlaneQuotientMap x.1 w.1) +
      (euclideanMetric (E := Real)).inner x.2
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) id x.2 v.2)
        (mfderiv 𝓘(Real, Real) 𝓘(Real, Real) id x.2 w.2) =
    roundTwoSphereShrinkerMetric.inner x.1 v.1 w.1 +
      (euclideanMetric (E := Real)).inner x.2 v.2 w.2
  erw [scaleMetric_inner]
  erw [roundProjectiveQuotientMap_inner]
  erw [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2), mfderiv_id]
  norm_num
  rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem cylinderAntipodalQuotientDiffeomorph_pullbackMetric :
    Diffeomorph.pullbackMetricCross
      ((scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := Real))) cylinderAntipodalQuotientDiffeomorph =
      cylinderAntipodalQuotientMetric := by
  apply localPullMetric_injective_of_surjective cylinderAntipodalQuotientMap
    cylinderAntipodalQuotientMap_isLocalDiffeomorph
    cylinderAntipodalQuotientMap_surjective
  rw [localPullMetric_cylinderAntipodalQuotientMetric]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hchain :
      mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        (Prod.map realProjectivePlaneQuotientMap id) x =
      (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
        cylinderAntipodalQuotientDiffeomorph (cylinderAntipodalQuotientMap x)).comp
        (mfderiv ((𝓡 2).prod 𝓘(Real, Real)) ((𝓡 2).prod 𝓘(Real, Real))
          cylinderAntipodalQuotientMap x) :=
    mfderiv_comp x
      (cylinderAntipodalQuotientDiffeomorph.contMDiff.mdifferentiableAt (by simp))
      (cylinderAntipodalQuotientMap_isLocalDiffeomorph.contMDiff.mdifferentiableAt (by simp))
  have hv := DFunLike.congr_fun hchain v
  have hw := DFunLike.congr_fun hchain w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner]
  have h := cylinderProjectiveQuotientMap_inner x v w
  rw [hv, hw] at h
  exact h

end DifferentialGeometry.Geometry
