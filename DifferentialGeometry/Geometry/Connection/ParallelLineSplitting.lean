import DifferentialGeometry.Geometry.Connection.ParallelLine
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
import DifferentialGeometry.Geometry.Metric.LieDerivative.Flow

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M]

attribute [local instance] DifferentialGeometry.seminormedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedAddCommGroupTangentSpace
attribute [local instance] DifferentialGeometry.normedSpaceTangentSpace

def perpModelSubmodule (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : ClosedSubmodule ℝ E :=
  (⊥ : ClosedSubmodule ℝ ℝ).comap
    ((g.inner x e).comp
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap)

abbrev perpSpace (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : Type _ := (perpModelSubmodule g x e).toSubmodule

def perpModel (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : ModelWithCorners ℝ (perpSpace g x e) (perpSpace g x e) :=
  ModelWithCorners.ofTargetUniv ℝ (PartialEquiv.refl (perpSpace g x e)) rfl rfl
    (by exact continuous_id) (by exact continuous_id)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem perpModel_apply (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (k : perpSpace g x e) : perpModel g x e k = k := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem perpModel_symm_apply (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (k : perpSpace g x e) : (perpModel g x e).symm k = k := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem extChartAt_perpModel_symm_apply (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (k z : perpSpace g x e) :
    (extChartAt (perpModel g x e) k).symm z = z := rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem perpModel_range (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : Set.range (perpModel g x e) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro k
  exact ⟨k, perpModel_apply g x e k⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private instance perpModelBoundaryless (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : (perpModel g x e).Boundaryless :=
  ⟨perpModel_range g x e⟩

private def perpProdLinearMap (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) :
    perpSpace g x e × ℝ →ₗ[ℝ] TangentSpace I x where
  toFun q :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1 + q.2 • e
  map_add' p q := by simp [add_smul]; abel
  map_smul' r q := by simp [mul_smul]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem perpProdLinearMap_bijective (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (he : g.inner x e e = 1) :
    Function.Bijective (perpProdLinearMap g x e) := by
  constructor
  · rintro ⟨v, r⟩ ⟨w, q⟩ h
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v.1 + r • e =
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w.1 + q • e at h
    have hv : g.inner x e
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v.1) = 0 := by
      have hv' := v.2
      change g.inner x e
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v.1) ∈
          (⊥ : ClosedSubmodule ℝ ℝ) at hv'
      exact ClosedSubmodule.mem_bot.mp hv'
    have hw : g.inner x e
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w.1) = 0 := by
      have hw' := w.2
      change g.inner x e
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w.1) ∈
          (⊥ : ClosedSubmodule ℝ ℝ) at hw'
      exact ClosedSubmodule.mem_bot.mp hw'
    have hs : r = q := by
      have hinner := congrArg (fun z => g.inner x e z) h
      rw [map_add, map_add, hv, hw, map_smul, map_smul, he] at hinner
      simpa only [smul_eq_mul, mul_one, zero_add] using hinner
    subst q
    have hvw : v.1 = w.1 := by
      apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.injective
      exact add_right_cancel h
    exact Prod.ext (Subtype.ext hvw) rfl
  · intro v
    let r : ℝ := g.inner x e v
    let w : E := tangentSpaceModelContinuousLinearEquiv (I := I) x (v - r • e)
    have hw : w ∈ perpModelSubmodule g x e := by
      change g.inner x e
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w) ∈
          (⊥ : ClosedSubmodule ℝ ℝ)
      rw [ClosedSubmodule.mem_bot]
      simp only [w, ContinuousLinearEquiv.symm_apply_apply, map_sub, map_smul, r, he,
        smul_eq_mul, mul_one, sub_self]
    refine ⟨(⟨w, hw⟩, r), ?_⟩
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm w + r • e = v
    simp only [w]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    abel

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private def perpProdLinearEquiv (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (he : g.inner x e e = 1) :
    (perpSpace g x e × ℝ) ≃ₗ[ℝ] TangentSpace I x where
  toFun q :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1 + q.2 • e
  invFun v :=
    (⟨tangentSpaceModelContinuousLinearEquiv (I := I) x
        (v - (g.inner x e v) • e), by
      change g.inner x e ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (v - (g.inner x e v) • e))) ∈
        (⊥ : ClosedSubmodule ℝ ℝ)
      rw [ClosedSubmodule.mem_bot]
      simp only [ContinuousLinearEquiv.symm_apply_apply, map_sub, map_smul, he,
        smul_eq_mul, mul_one, sub_self]⟩,
      g.inner x e v)
  left_inv q := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add, map_smul, he, smul_eq_mul, mul_one]
      have hq : g.inner x e
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1) = 0 := by
        have hq' := q.1.2
        change g.inner x e
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1) ∈
            (⊥ : ClosedSubmodule ℝ ℝ) at hq'
        exact ClosedSubmodule.mem_bot.mp hq'
      rw [hq, zero_add]
      have hcancel :
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1 +
              q.2 • e - q.2 • e =
            (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1 := by
        abel
      rw [hcancel, ContinuousLinearEquiv.apply_symm_apply]
    · simp only [map_add, map_smul, he, smul_eq_mul, mul_one]
      have hq : g.inner x e
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1) = 0 := by
        have hq' := q.1.2
        change g.inner x e
          ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1) ∈
            (⊥ : ClosedSubmodule ℝ ℝ) at hq'
        exact ClosedSubmodule.mem_bot.mp hq'
      rw [hq, zero_add]
  right_inv v := by
    dsimp
    rw [ContinuousLinearEquiv.symm_apply_apply]
    abel
  map_add' p q := by simp [add_smul]; abel
  map_smul' r q := by simp [mul_smul]

private def perpProdContinuousLinearEquiv (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (he : g.inner x e e = 1) :
    (perpSpace g x e × ℝ) ≃L[ℝ] TangentSpace I x where
  toLinearEquiv := perpProdLinearEquiv g x e he
  continuous_toFun := by
    change Continuous (fun q : perpSpace g x e × ℝ =>
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm q.1.1 + q.2 • e)
    fun_prop
  continuous_invFun := by
    dsimp [perpProdLinearEquiv]
    fun_prop

private def adaptedBaseMap (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) (k : perpSpace g x e) : M :=
  (extChartAt I x).symm (extChartAt I x x + k.1)

private def adaptedBaseDomain (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : Set (perpSpace g x e) :=
  (fun k => extChartAt I x x + k.1) ⁻¹' (extChartAt I x).target

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem isOpen_adaptedBaseDomain (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : IsOpen (adaptedBaseDomain g x e) := by
  apply (isOpen_extChartAt_target x).preimage
  fun_prop

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem zero_mem_adaptedBaseDomain (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : (0 : perpSpace g x e) ∈ adaptedBaseDomain g x e := by
  change extChartAt I x x + (0 : perpSpace g x e).1 ∈ (extChartAt I x).target
  simpa only [Submodule.coe_zero, add_zero] using mem_extChartAt_target x

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem adaptedBaseMap_zero (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) : adaptedBaseMap g x e 0 = x := by
  change (extChartAt I x).symm (extChartAt I x x + (0 : E)) = x
  rw [add_zero]
  exact (extChartAt I x).left_inv (mem_extChartAt_source x)

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem contMDiffAt_adaptedBaseMap (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) :
    ContMDiffAt (perpModel g x e) I ∞ (adaptedBaseMap g x e) 0 := by
  have hsub : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
      (perpModelSubmodule g x e).toSubmodule.subtypeL 0 := by
    rw [contMDiffAt_iff]
    constructor
    · fun_prop
    · convert
        (perpModelSubmodule g x e).toSubmodule.subtypeL.contDiff.contDiffAt.contDiffWithinAt
          using 1
      · funext z
        simp only [Function.comp_apply, ext_chart_model_space_apply,
          extChartAt_perpModel_symm_apply]
  have haff : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
      (fun k : perpSpace g x e => extChartAt I x x + k.1) 0 := by
    convert (contMDiffAt_const (c := extChartAt I x x)).add hsub using 1
    all_goals rfl
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
  have hsymm' : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (extChartAt I x x + (0 : perpSpace g x e).1) := by
    simpa only [Submodule.coe_zero, add_zero] using hsymm
  change ContMDiffAt (perpModel g x e) I ∞
    (fun k : perpSpace g x e =>
      (extChartAt I x).symm (extChartAt I x x + k.1)) 0
  exact hsymm'.comp (I := perpModel g x e)
    (f := fun k : perpSpace g x e => extChartAt I x x + k.1) 0 haff

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem contMDiffAt_adaptedBaseMap_of_mem
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    (k : perpSpace g x e) (hk : k ∈ adaptedBaseDomain g x e) :
    ContMDiffAt (perpModel g x e) I ∞ (adaptedBaseMap g x e) k := by
  have hsub : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
      (perpModelSubmodule g x e).toSubmodule.subtypeL k := by
    rw [contMDiffAt_iff]
    constructor
    · fun_prop
    · convert
        (perpModelSubmodule g x e).toSubmodule.subtypeL.contDiff.contDiffAt.contDiffWithinAt
          using 1
      · funext z
        simp only [Function.comp_apply, ext_chart_model_space_apply,
          extChartAt_perpModel_symm_apply]
  have haff : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
      (fun z : perpSpace g x e => extChartAt I x x + z.1) k := by
    convert (contMDiffAt_const (c := extChartAt I x x)).add hsub using 1
    all_goals rfl
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
      (extChartAt I x x + k.1) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hk)
  exact hsymm.comp (I := perpModel g x e)
    (f := fun z : perpSpace g x e => extChartAt I x x + z.1) k haff

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem contMDiffOn_adaptedBaseMap
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x) :
    ContMDiffOn (perpModel g x e) I ∞ (adaptedBaseMap g x e)
      (adaptedBaseDomain g x e) := by
  intro k hk
  exact (contMDiffAt_adaptedBaseMap_of_mem g x e k hk).contMDiffWithinAt

omit [FiniteDimensional ℝ E] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
private theorem mfderiv_adaptedBaseMap_zero (g : SmoothRiemannianMetric I M) (x : M)
    (e : TangentSpace I x) :
    mfderiv (perpModel g x e) I (adaptedBaseMap g x e) 0 =
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm.toContinuousLinearMap.comp
        (perpModelSubmodule g x e).toSubmodule.subtypeL := by
  have haff : MDifferentiableAt (perpModel g x e) 𝓘(ℝ, E)
      (fun k : perpSpace g x e => extChartAt I x x + k.1) 0 := by
    have hsub : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
        (perpModelSubmodule g x e).toSubmodule.subtypeL 0 := by
      rw [contMDiffAt_iff]
      constructor
      · fun_prop
      · convert
          (perpModelSubmodule g x e).toSubmodule.subtypeL.contDiff.contDiffAt.contDiffWithinAt
            using 1
        · funext z
          simp only [Function.comp_apply, ext_chart_model_space_apply,
            extChartAt_perpModel_symm_apply]
    have hcont : ContMDiffAt (perpModel g x e) 𝓘(ℝ, E) ∞
        (fun k : perpSpace g x e => extChartAt I x x + k.1) 0 := by
      convert (contMDiffAt_const (c := extChartAt I x x)).add hsub using 1
      all_goals rfl
    exact hcont.mdifferentiableAt (by
      intro h
      change ((↑(⊤ : ℕ∞) : WithTop ℕ∞) = (↑(0 : ℕ∞) : WithTop ℕ∞)) at h
      exact ENat.top_ne_zero (WithTop.coe_injective h))
  have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x) :=
    have hcont : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm
        (extChartAt I x x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))
    hcont.mdifferentiableAt (by
      intro h
      change ((↑(⊤ : ℕ∞) : WithTop ℕ∞) = (↑(0 : ℕ∞) : WithTop ℕ∞)) at h
      exact ENat.top_ne_zero (WithTop.coe_injective h))
  have hsymm' : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm
      (extChartAt I x x + (0 : perpSpace g x e).1) := by
    simpa only [Submodule.coe_zero, add_zero] using hsymm
  rw [show adaptedBaseMap g x e =
      (extChartAt I x).symm ∘
        (fun k : perpSpace g x e => extChartAt I x x + k.1) by rfl]
  have hcomp := mfderiv_comp (I := perpModel g x e) (I' := 𝓘(ℝ, E))
    (I'' := I) (f := fun k : perpSpace g x e => extChartAt I x x + k.1)
    (g := (extChartAt I x).symm) 0 hsymm' haff
  have hzero : extChartAt I x x + (0 : perpSpace g x e).1 = extChartAt I x x := by
    simp only [Submodule.coe_zero, add_zero]
  rw [hzero, extChartAt_to_inv] at hcomp
  rw [hcomp]
  have hsymm_deriv :
      mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm (extChartAt I x x) =
        ContinuousLinearMap.id ℝ
          (TangentSpace 𝓘(ℝ, E) (extChartAt I x x)) := by
    rw [← mfderivWithin_univ]
    simpa only [I.range_eq_univ] using
      (mfderivWithin_range_extChartAt_symm (I := I) (x := x))
  rw [hsymm_deriv]
  have haff_deriv :
      mfderiv (perpModel g x e) 𝓘(ℝ, E)
        (fun k : perpSpace g x e => extChartAt I x x + k.1) 0 =
        (perpModelSubmodule g x e).toSubmodule.subtypeL := by
    apply HasMFDerivAt.mfderiv
    constructor
    · exact haff.continuousAt
    · convert ((hasFDerivAt_const (x := (0 : perpSpace g x e))
        (c := extChartAt I x x)).add
          (perpModelSubmodule g x e).toSubmodule.subtypeL.hasFDerivAt).hasFDerivWithinAt
        using 1
      all_goals try rfl
      · simp only [zero_add]
  rw [haff_deriv]
  apply ContinuousLinearMap.ext
  intro v
  change v.1 = (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm v.1
  exact (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm_apply_apply v.1 |>.symm

omit [I.Boundaryless] in
private theorem exists_compactlySupported_extension_eq_eventually
    {U : Set M} (hUopen : IsOpen U) {x : M} (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) :
    ∃ X : (y : M) → TangentSpace I y,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) ∧
      IsCompact (tsupport X) ∧ X =ᶠ[𝓝 x] fun y => s y := by
  obtain ⟨chi, hchi⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x)
      (hUopen.mem_nhds hxU)).ex_mem
  let X : (y : M) → TangentSpace I y := fun y => chi y • s y
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) := by
    exact chi.contMDiff.smul_section s.contMDiff
  have hchiCompact : IsCompact (tsupport (chi : M → ℝ)) := by
    exact chi.isCompact_symm_image_closedBall.of_isClosed_subset
      (isClosed_tsupport _) chi.tsupport_subset_symm_image_closedBall
  have hXsupport : tsupport X ⊆ tsupport (chi : M → ℝ) := by
    change tsupport ((chi : M → ℝ) • fun y => s y) ⊆ tsupport (chi : M → ℝ)
    exact tsupport_smul_subset_left (chi : M → ℝ) (fun y => s y)
  have hXCompact : IsCompact (tsupport X) :=
    hchiCompact.of_isClosed_subset (isClosed_tsupport _) hXsupport
  refine ⟨X, hX, hXCompact, ?_⟩
  filter_upwards [chi.eventuallyEq_one] with y hy
  simp only [X, hy, Pi.one_apply, one_smul]
  rfl

private theorem mfderiv_globalFlow_zero_apply
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) (x : M) (r : ℝ)
    (v : TangentSpace I x) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun p : ℝ × M =>
        DifferentialGeometry.Analysis.ODE.curveAt X
          (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
            X hX hXcompact) p.2 p.1) (0, x))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (0, x) from (r, v)) =
        r • X x + v := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Phi : ℝ × M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi := by
    exact DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  have hPhiMD : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (0, x) :=
    (hPhi (0, x)).mdifferentiableAt (by simp)
  have htime :
      (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => Phi (t, x)) 0) r = r • X x := by
    have hcurve :=
      DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete x 0
    rw [hcurve.mfderiv]
    change r • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete x 0) = r • X x
    rw [DifferentialGeometry.Analysis.ODE.curveAt_zero]
  have hspace :
      (mfderiv I I (fun y : M => Phi (0, y)) x) v = v := by
    have hfun : (fun y : M => Phi (0, y)) = id := by
      funext y
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y
    rw [hfun, mfderiv_id]
    rfl
  change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (0, x))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (0, x) from (r, v)) = _
  rw [mfderiv_prod_eq_add_apply hPhiMD]
  rw [htime, hspace]
  rfl

private def correctedFlowMap
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    (f : M → ℝ) (q : perpSpace g x e × ℝ) : M :=
  DifferentialGeometry.Analysis.ODE.curveAt X
    (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
      X hX hXcompact) (adaptedBaseMap g x e q.1)
      (q.2 - f (adaptedBaseMap g x e q.1))

private def correctedFlowBaseDomain
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    (U : Set M) : Set (perpSpace g x e) :=
  adaptedBaseDomain g x e ∩ adaptedBaseMap g x e ⁻¹' U

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem isOpen_correctedFlowBaseDomain
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    {U : Set M} (hUopen : IsOpen U) : IsOpen (correctedFlowBaseDomain g x e U) := by
  exact (contMDiffOn_adaptedBaseMap g x e).continuousOn.isOpen_inter_preimage
    (isOpen_adaptedBaseDomain g x e) hUopen

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem zero_mem_correctedFlowBaseDomain
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    {U : Set M} (hxU : x ∈ U) :
    (0 : perpSpace g x e) ∈ correctedFlowBaseDomain g x e U := by
  exact ⟨zero_mem_adaptedBaseDomain g x e, by
    change adaptedBaseMap g x e 0 ∈ U
    rw [adaptedBaseMap_zero]
    exact hxU⟩

private theorem correctedFlowMap_contMDiffOn
    (g : SmoothRiemannianMetric I M) (x : M) (e : TangentSpace I x)
    {U : Set M} (hUopen : IsOpen U) (f : M → ℝ)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) :
    ContMDiffOn ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I ∞
      (correctedFlowMap X hX hXcompact g x e f)
      (correctedFlowBaseDomain g x e U ×ˢ Set.univ) := by
  let b : perpSpace g x e → M := adaptedBaseMap g x e
  let tau : perpSpace g x e × ℝ → ℝ := fun q => q.2 - f (b q.1)
  let input : perpSpace g x e × ℝ → ℝ × M := fun q => (tau q, b q.1)
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Phi : ℝ × M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  intro q hq
  have hbq : ContMDiffAt (perpModel g x e) I ∞ b q.1 :=
    contMDiffAt_adaptedBaseMap_of_mem g x e q.1 hq.1.1
  have hfq : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f (b q.1) :=
    (hf (b q.1) hq.1.2).contMDiffAt (hUopen.mem_nhds hq.1.2)
  have hfbq : ContMDiffAt (perpModel g x e) 𝓘(ℝ, ℝ) ∞
      (fun k => f (b k)) q.1 := hfq.comp q.1 hbq
  have hbProdq : ContMDiffAt ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p : perpSpace g x e × ℝ => b p.1) q :=
    hbq.comp (f := fun p : perpSpace g x e × ℝ => p.1) q contMDiffAt_fst
  have hfbProdq :
      ContMDiffAt ((perpModel g x e).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : perpSpace g x e × ℝ => f (b p.1)) q :=
    hfbq.comp (f := fun p : perpSpace g x e × ℝ => p.1) q contMDiffAt_fst
  have htauq : ContMDiffAt ((perpModel g x e).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ tau q :=
    contMDiffAt_snd.sub hfbProdq
  have hinputq : ContMDiffAt ((perpModel g x e).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) ∞ input q := htauq.prodMk hbProdq
  have hFq : ContMDiffAt ((perpModel g x e).prod 𝓘(ℝ, ℝ)) I ∞
      (fun p => Phi (input p)) q := (hPhi (input q)).comp q hinputq
  exact hFq.contMDiffWithinAt

private theorem correctedFlowMap_isLocalDiffeomorphAt_one
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (hfx : f x = 0) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (hXeq : X =ᶠ[𝓝 x] fun y => s y) :
    IsLocalDiffeomorphAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I 1
      (correctedFlowMap X hX hXcompact g x (s x) f) (0, 0) := by
  let b : perpSpace g x (s x) → M := adaptedBaseMap g x (s x)
  let tau : perpSpace g x (s x) × ℝ → ℝ := fun q => q.2 - f (b q.1)
  let input : perpSpace g x (s x) × ℝ → ℝ × M := fun q => (tau q, b q.1)
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Phi : ℝ × M → M := fun p =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete p.2 p.1
  let F : perpSpace g x (s x) × ℝ → M := fun q => Phi (input q)
  have hb0 : b 0 = x := adaptedBaseMap_zero g x (s x)
  have hbSmooth : ContMDiffAt (perpModel g x (s x)) I ∞ b 0 :=
    contMDiffAt_adaptedBaseMap g x (s x)
  have hbMD : MDifferentiableAt (perpModel g x (s x)) I b 0 :=
    hbSmooth.mdifferentiableAt (by simp)
  have hfAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f x :=
    (hf x hxU).contMDiffAt (hUopen.mem_nhds hxU)
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
    hfAt.mdifferentiableAt (by simp)
  have hfbSmooth : ContMDiffAt (perpModel g x (s x)) 𝓘(ℝ, ℝ) ∞
      (fun k => f (b k)) 0 := by
    have hfAt' : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f (b 0) := by
      simpa only [hb0] using hfAt
    exact hfAt'.comp (I := perpModel g x (s x)) 0 hbSmooth
  have hfbMD : MDifferentiableAt (perpModel g x (s x)) 𝓘(ℝ, ℝ)
      (fun k => f (b k)) 0 := hfbSmooth.mdifferentiableAt (by simp)
  have hfbDeriv :
      mfderiv (perpModel g x (s x)) 𝓘(ℝ, ℝ) (fun k => f (b k)) 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro k
    change mvfderiv (I := perpModel g x (s x)) (fun k => f (b k)) 0 k = 0
    rw [show (fun k => f (b k)) = f ∘ b by rfl]
    have hfMD' : MDifferentiableAt I 𝓘(ℝ, ℝ) f (b 0) := by
      simpa only [hb0] using hfMD
    rw [mvfderiv_comp_apply 0 hfMD' hbMD k]
    rw [hb0, mfderiv_adaptedBaseMap_zero]
    rw [hdf x hxU]
    have hk := k.2
    change g.inner x (s x)
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm k.1) ∈
        (⊥ : ClosedSubmodule ℝ ℝ) at hk
    exact ClosedSubmodule.mem_bot.mp hk
  have hbProdSmooth : ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : perpSpace g x (s x) × ℝ => b q.1) (0, 0) :=
    hbSmooth.comp (f := fun q : perpSpace g x (s x) × ℝ => q.1)
      (0, 0) contMDiffAt_fst
  have hfbProdSmooth :
      ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun q : perpSpace g x (s x) × ℝ => f (b q.1)) (0, 0) :=
    hfbSmooth.comp (f := fun q : perpSpace g x (s x) × ℝ => q.1)
      (0, 0) contMDiffAt_fst
  have htauSmooth :
      ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ tau (0, 0) := by
    exact contMDiffAt_snd.sub hfbProdSmooth
  have hinputSmooth :
      ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod I) ∞ input (0, 0) :=
    htauSmooth.prodMk hbProdSmooth
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi := by
    exact DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  have hinput0 : input (0, 0) = (0, x) := by
    apply Prod.ext
    · simp only [input, tau, hb0, hfx, zero_sub, neg_zero]
    · exact hb0
  have hFSmooth :
      ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞ F (0, 0) := by
    have hPhiAt : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞ Phi (input (0, 0)) := by
      simpa only [hinput0] using hPhi (0, x)
    exact hPhiAt.comp (0, 0) hinputSmooth
  have htauMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
      𝓘(ℝ, ℝ) tau (0, 0) := htauSmooth.mdifferentiableAt (by simp)
  have hbProdMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
      (fun q : perpSpace g x (s x) × ℝ => b q.1) (0, 0) :=
    hbProdSmooth.mdifferentiableAt (by simp)
  have hinputMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) input (0, 0) := hinputSmooth.mdifferentiableAt (by simp)
  have hFMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
      F (0, 0) := hFSmooth.mdifferentiableAt (by simp)
  have htauDeriv (k : perpSpace g x (s x)) (r : ℝ) :
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        tau (0, 0))
        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (0, 0) from (k, r)) = r := by
    rw [mfderiv_prod_eq_add_apply htauMD]
    have hk : (mfderiv (perpModel g x (s x)) 𝓘(ℝ, ℝ)
        (fun z : perpSpace g x (s x) => tau (z, 0)) 0) k = 0 := by
      have hfun : (fun z : perpSpace g x (s x) => tau (z, 0)) =
          -(fun z => f (b z)) := by
        funext z
        simp only [tau, Pi.neg_apply, zero_sub]
      rw [hfun, mfderiv_neg, hfbDeriv]
      change -(0 : ℝ) = 0
      exact neg_zero
    have hr : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
        (fun z : ℝ => tau (0, z)) 0) r = r := by
      have hfun : (fun z : ℝ => tau (0, z)) = fun z => z - f (b 0) := by rfl
      have hfun' : (fun z : ℝ => z - f (b 0)) = id - fun _ : ℝ => f (b 0) := by
        rfl
      rw [hfun, hfun']
      rw [mfderiv_sub mdifferentiableAt_id mdifferentiableAt_const,
        mfderiv_id, mfderiv_const]
      change r - 0 = r
      exact sub_zero r
    rw [hk, hr]
    change (0 : ℝ) + r = r
    exact zero_add r
  have hbProdDeriv (k : perpSpace g x (s x)) (r : ℝ) :
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
        (fun q : perpSpace g x (s x) × ℝ => b q.1) (0, 0))
        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (0, 0) from (k, r)) =
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm k.1 := by
    rw [mfderiv_prod_eq_add_apply hbProdMD]
    rw [show (fun z : perpSpace g x (s x) => b z) = b by rfl,
      mfderiv_adaptedBaseMap_zero]
    have hr : (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => b 0) 0) r = 0 := by
      rw [mfderiv_const]
      rfl
    rw [hr, add_zero]
    rfl
  have hinputDeriv (k : perpSpace g x (s x)) (r : ℝ) :
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I)
        input (0, 0))
        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (0, 0) from (k, r)) =
          (show TangentSpace (𝓘(ℝ, ℝ).prod I) ((0 : ℝ), x) from
            (r, (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm k.1)) := by
    rw [mfderiv_prodMk htauMD hbProdMD]
    apply Prod.ext
    · exact htauDeriv k r
    · exact hbProdDeriv k r
  have hXx : X x = s x := hXeq.eq_of_nhds
  have he : g.inner x (s x) (s x) = 1 := hunit x hxU
  have hmf :
      mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F (0, 0) =
        (perpProdContinuousLinearEquiv g x (s x) he :
          (perpSpace g x (s x) × ℝ) →L[ℝ] TangentSpace I x) := by
    apply ContinuousLinearMap.ext
    rintro ⟨k, r⟩
    have hPhiMD' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (input (0, 0)) := by
      simpa only [hinput0] using (hPhi (0, x)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (I := (perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, ℝ).prod I) (I'' := I) (f := input) (g := Phi)
      (0, 0) hPhiMD' hinputMD
    rw [hinput0] at hcomp
    change (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F (0, 0))
      (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (0, 0) from (k, r)) = _
    rw [show F = Phi ∘ input by rfl]
    rw [hcomp]
    change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (0, x))
        ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I)
          input (0, 0)) (k, r)) = _
    rw [hinputDeriv k r]
    rw [mfderiv_globalFlow_zero_apply X hX hXcompact x r
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm k.1)]
    rw [hXx]
    rw [add_comm]
    rfl
  have hinv : (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F (0, 0)).IsInvertible := by
    rw [hmf]
    exact ContinuousLinearMap.isInvertible_equiv
  have hlocal := DifferentialGeometry.Coordinates.contMDiffAt_isLocalDiffeomorphAt_of_mfderiv
    (n := (1 : WithTop ℕ∞)) le_rfl (by exact_mod_cast WithTop.one_ne_top)
    (hFSmooth.of_le (by exact_mod_cast le_top)) hinv
  change IsLocalDiffeomorphAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I 1
    (correctedFlowMap X hX hXcompact g x (s x) f) (0, 0)
  exact hlocal

private theorem correctedFlowMap_isLocalDiffeomorphAt_infty
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (hfx : f x = 0) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (hXeq : X =ᶠ[𝓝 x] fun y => s y) :
    IsLocalDiffeomorphAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞
      (correctedFlowMap X hX hXcompact g x (s x) f) (0, 0) := by
  let F : perpSpace g x (s x) × ℝ → M :=
    correctedFlowMap X hX hXcompact g x (s x) f
  let W : Set (perpSpace g x (s x) × ℝ) :=
    correctedFlowBaseDomain g x (s x) U ×ˢ Set.univ
  have hWopen : IsOpen W :=
    (isOpen_correctedFlowBaseDomain g x (s x) hUopen).prod isOpen_univ
  have hzeroW : (0, 0) ∈ W :=
    ⟨zero_mem_correctedFlowBaseDomain g x (s x) hxU, Set.mem_univ 0⟩
  have hFOn : ContMDiffOn ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞ F W :=
    correctedFlowMap_contMDiffOn g x (s x) hUopen f hf X hX hXcompact
  have hlocalOne :
      IsLocalDiffeomorphAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I 1 F (0, 0) :=
    correctedFlowMap_isLocalDiffeomorphAt_one g x hUopen hxU s f hunit hfx hf hdf
      X hX hXcompact hXeq
  obtain ⟨phi, hzeroPhi, hEqPhi⟩ := hlocalOne
  let V : Set (perpSpace g x (s x) × ℝ) := phi.source ∩ W
  have hVopen : IsOpen V := phi.open_source.inter hWopen
  have hzeroV : (0, 0) ∈ V := ⟨hzeroPhi, hzeroW⟩
  have hFOnV : ContMDiffOn ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞ F V :=
    hFOn.mono inter_subset_right
  have hcoordInv : ∀ q ∈ V,
      (fderiv ℝ
        (writtenInExtChartAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I q F)
        (extChartAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) q q)).IsInvertible := by
    intro q hq
    have hlocalq :
        IsLocalDiffeomorphAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I 1 F q :=
      ⟨phi, hq.1, hEqPhi⟩
    have hmfInv :
        (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F q).IsInvertible := by
      refine ⟨hlocalq.mfderivToContinuousLinearEquiv (by norm_num), ?_⟩
      exact hlocalq.mfderivToContinuousLinearEquiv_coe (by norm_num)
    have hFAt : ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞ F q :=
      (hFOnV q hq).contMDiffAt (hVopen.mem_nhds hq)
    have hFMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F q :=
      hFAt.mdifferentiableAt (by simp)
    have hderiv :
        fderiv ℝ
          (writtenInExtChartAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I q F)
          (extChartAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) q q) =
        mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I F q := by
      rw [hFMD.mfderiv,
        ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
    exact hderiv ▸ hmfInv
  obtain ⟨psi, hzeroPsi, -, hEqPsi⟩ :=
    DifferentialGeometry.Coordinates.exists_partialDiffeomorph_of_contMDiffOn_infty
      hVopen hzeroV hFOnV hcoordInv
  exact ⟨psi, hzeroPsi, hEqPsi⟩

private def restrictPartialDiffeomorphOpen
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (phi : PartialDiffeomorph I' I M' M ∞)
    (R : Set M') (hRopen : IsOpen R) :
    PartialDiffeomorph I' I M' M ∞ := by
  let e := phi.toOpenPartialHomeomorph.restrOpen R hRopen
  exact
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn I' I ∞ (phi : M' → M) e.source
        exact phi.contMDiffOn_toFun.mono (by
          intro z hz
          exact hz.1)
      contMDiffOn_invFun := by
        change ContMDiffOn I I' ∞ phi.invFun e.target
        exact phi.contMDiffOn_invFun.mono (by
          intro z hz
          change z ∈ phi.target ∩ phi.symm ⁻¹' R at hz
          exact hz.1) }

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem restrictPartialDiffeomorphOpen_source_eq
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    (phi : PartialDiffeomorph I' I M' M ∞)
    (R : Set M') (hRopen : IsOpen R) (hRsub : R ⊆ phi.source) :
    (restrictPartialDiffeomorphOpen phi R hRopen).source = R := by
  change phi.source ∩ R = R
  exact inter_eq_right.mpr hRsub

private def globalFlowDiffeomorph
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) (t : ℝ) : M ≃ₘ⟮I, I⟯ M := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let flow : ℝ → M → M := fun r y =>
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y r
  have hXone : CMDiff 1 (fun y : M => (⟨y, X y⟩ : TangentBundle I M)) :=
    hX.of_le (by norm_num)
  have hflowSmooth : ∀ r : ℝ, ContMDiff I I ∞ (flow r) := by
    intro r y
    exact DifferentialGeometry.Analysis.ODE.contMDiffAt_globalFlow_of_compactSupport
      X hX hXcompact r y
  exact
    { toEquiv :=
        { toFun := flow t
          invFun := flow (-t)
          left_inv := by
            intro y
            have h := DifferentialGeometry.Analysis.ODE.curveAt_add
              X hXone hcomplete y t (-t)
            dsimp only [flow]
            rw [← h]
            simpa only [add_neg_cancel] using
              DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y
          right_inv := by
            intro y
            have h := DifferentialGeometry.Analysis.ODE.curveAt_add
              X hXone hcomplete y (-t) t
            dsimp only [flow]
            rw [← h]
            simpa only [neg_add_cancel] using
              DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y }
      contMDiff_toFun := hflowSmooth t
      contMDiff_invFun := hflowSmooth (-t) }

private theorem globalFlowDiffeomorph_apply
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) (t : ℝ) (y : M) :
    globalFlowDiffeomorph X hX hXcompact t y =
      DifferentialGeometry.Analysis.ODE.curveAt X
        (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
          X hX hXcompact) y t := rfl

private theorem mfderiv_globalFlow_apply
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) (t : ℝ) (y : M)
    (r : TangentSpace 𝓘(ℝ, ℝ) t)
    (v : TangentSpace I y) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) I
      (fun p : ℝ × M => globalFlowDiffeomorph X hX hXcompact p.1 p.2) (t, y))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (t, y) from (r, v)) =
        (NormedSpace.fromTangentSpace t r) •
            X (globalFlowDiffeomorph X hX hXcompact t y) +
          (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y) v := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Phi : ℝ × M → M := fun p => globalFlowDiffeomorph X hX hXcompact p.1 p.2
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi := by
    exact DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  have hPhiMD : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (t, y) :=
    (hPhi (t, y)).mdifferentiableAt (by simp)
  have htime :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ => Phi (u, y)) t)
          r =
        (NormedSpace.fromTangentSpace t r) •
          X (globalFlowDiffeomorph X hX hXcompact t y) := by
    have hcurve :=
      DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete y t
    have hfun : (fun u : ℝ => Phi (u, y)) =
        DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y := rfl
    rw [hfun]
    rw [hcurve.mfderiv]
    change (NormedSpace.fromTangentSpace t r) •
      X (globalFlowDiffeomorph X hX hXcompact t y) = _
    rfl
  change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (t, y))
      (show TangentSpace (𝓘(ℝ, ℝ).prod I) (t, y) from (r, v)) = _
  rw [mfderiv_prod_eq_add_apply hPhiMD]
  rw [htime]

private theorem globalFlow_potential_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {U : Set M} (hUopen : IsOpen U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ z ∈ U, g.inner z (s z) (s z) = 1)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ z ∈ U, ∀ v : TangentSpace I z,
      mvfderiv (I := I) f z v = g.inner z (s z) v)
    (t : ℝ) (y : M)
    (htU : globalFlowDiffeomorph X hX hXcompact t y ∈ U)
    (htEq : X (globalFlowDiffeomorph X hX hXcompact t y) =
      s (globalFlowDiffeomorph X hX hXcompact t y)) :
    HasDerivAt (fun r : ℝ => f (globalFlowDiffeomorph X hX hXcompact r y)) 1 t := by
  let gamma : ℝ → M := fun r => globalFlowDiffeomorph X hX hXcompact r y
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  have hgamma : IsMIntegralCurve gamma X :=
    DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete y
  have hgammaMD : MDifferentiableAt 𝓘(ℝ, ℝ) I gamma t :=
    (hgamma t).mdifferentiableAt
  have hfAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f (gamma t) :=
    (hf _ htU).contMDiffAt (hUopen.mem_nhds htU)
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f (gamma t) :=
    hfAt.mdifferentiableAt (by simp)
  have hcomp := DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
    I f gamma t hfMD hgammaMD
  have hvel :
      mfderiv 𝓘(ℝ, ℝ) I gamma t
          (DifferentialGeometry.Analysis.Calculus.realTangentOne t) = X (gamma t) := by
    rw [(hgamma t).mfderiv]
    change (1 : ℝ) • X (gamma t) = X (gamma t)
    exact one_smul ℝ (X (gamma t))
  have hrate :
      (NormedSpace.fromTangentSpace (f (gamma t)))
        ((mfderiv I 𝓘(ℝ, ℝ) f (gamma t))
          (mfderiv 𝓘(ℝ, ℝ) I gamma t
            (DifferentialGeometry.Analysis.Calculus.realTangentOne t))) = 1 := by
    rw [hvel]
    change mvfderiv (I := I) f (gamma t) (X (gamma t)) = 1
    rw [hdf _ htU, htEq, hunit _ htU]
  simpa only [gamma] using hcomp.congr_deriv hrate

private theorem globalFlow_potential_eq_add_of_path
    (g : SmoothRiemannianMetric I M)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {U : Set M} (hUopen : IsOpen U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ z ∈ U, g.inner z (s z) (s z) = 1)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ z ∈ U, ∀ v : TangentSpace I z,
      mvfderiv (I := I) f z v = g.inner z (s z) v)
    (t : ℝ) (y : M)
    (hpathU : ∀ r ∈ Set.uIcc 0 t, globalFlowDiffeomorph X hX hXcompact r y ∈ U)
    (hpathEq : ∀ r ∈ Set.uIcc 0 t,
      X (globalFlowDiffeomorph X hX hXcompact r y) =
        s (globalFlowDiffeomorph X hX hXcompact r y)) :
    f (globalFlowDiffeomorph X hX hXcompact t y) = f y + t := by
  let P : ℝ → ℝ := fun r => f (globalFlowDiffeomorph X hX hXcompact r y)
  let Q : ℝ → ℝ := fun r => P r - r
  have hzero : globalFlowDiffeomorph X hX hXcompact 0 y = y := by
    rw [globalFlowDiffeomorph_apply]
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact) y
  have hhas : ∀ r ∈ Set.uIcc 0 t, HasDerivAt P 1 r := by
    intro r hr
    exact globalFlow_potential_hasDerivAt g X hX hXcompact hUopen s f hunit hf hdf r y
      (hpathU r hr) (hpathEq r hr)
  have hQhas : ∀ r ∈ Set.uIcc 0 t, HasDerivAt Q 0 r := by
    intro r hr
    change HasDerivAt (P - id) 0 r
    simpa only [sub_self] using (hhas r hr).sub (hasDerivAt_id r)
  by_cases ht : 0 ≤ t
  · rcases ht.eq_or_lt with rfl | htpos
    · simp only [add_zero, hzero]
    · have hsub : Set.Icc 0 t ⊆ Set.uIcc 0 t := by
        rw [Set.uIcc_of_le (le_of_lt htpos)]
      have hdiff : DifferentiableOn ℝ Q (Set.Icc 0 t) := by
        intro r hr
        exact (hQhas r (hsub hr)).differentiableAt.differentiableWithinAt
      have hderiv : ∀ r ∈ Set.Ico 0 t, derivWithin Q (Set.Icc 0 t) r = 0 := by
        intro r hr
        have hrIcc : r ∈ Set.Icc 0 t := ⟨hr.1, le_of_lt hr.2⟩
        exact (hQhas r (hsub hrIcc)).hasDerivWithinAt.derivWithin
          ((uniqueDiffOn_Icc htpos) r hrIcc)
      have hconst := constant_of_derivWithin_zero hdiff hderiv t (right_mem_Icc.mpr ht)
      change P t - t = P 0 - 0 at hconst
      dsimp only [P] at hconst
      rw [sub_zero, hzero] at hconst
      linarith
  · have htneg : t < 0 := lt_of_not_ge ht
    have hsub : Set.Icc t 0 ⊆ Set.uIcc 0 t := by
      rw [Set.uIcc_of_ge (le_of_lt htneg)]
    have hdiff : DifferentiableOn ℝ Q (Set.Icc t 0) := by
      intro r hr
      exact (hQhas r (hsub hr)).differentiableAt.differentiableWithinAt
    have hderiv : ∀ r ∈ Set.Ico t 0, derivWithin Q (Set.Icc t 0) r = 0 := by
      intro r hr
      have hrIcc : r ∈ Set.Icc t 0 := ⟨hr.1, le_of_lt hr.2⟩
      exact (hQhas r (hsub hrIcc)).hasDerivWithinAt.derivWithin
        ((uniqueDiffOn_Icc htneg) r hrIcc)
    have hconst := constant_of_derivWithin_zero hdiff hderiv 0
      (right_mem_Icc.mpr (le_of_lt htneg))
    change P 0 - 0 = P t - t at hconst
    dsimp only [P] at hconst
    rw [sub_zero, hzero] at hconst
    linarith

private theorem globalFlow_pairing_hasDerivAt
    (g : SmoothRiemannianMetric I M)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (t : ℝ) (y : M) (v w : TangentSpace I y) :
    HasDerivAt
      (fun r : ℝ => g.inner (globalFlowDiffeomorph X hX hXcompact r y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g
        (⟨fun z => X z, hX⟩ : Cₛ^∞⟮I; E, TangentSpace I⟯)
        (globalFlowDiffeomorph X hX hXcompact t y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y w)) t := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Y : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨fun z => X z, hX⟩
  let fam : ℝ → M ≃ₘ⟮I, I⟯ M := fun u =>
    globalFlowDiffeomorph X hX hXcompact (u + t - 1)
  have hfamOde : ∀ z : M, ∀ u ∈ Set.Ioo (0 : ℝ) 2,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun a : ℝ => (fam a : M → M) z)
        (Set.Ici (0 : ℝ)) u
        ((1 : ℝ →L[ℝ] ℝ).smulRight (Y ((fam u : M → M) z))) := by
    intro z u hu
    have hcurve : IsMIntegralCurve
        (fun a : ℝ => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete z (a + t - 1)) X := by
      have h :=
        (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete z).comp_add (t - 1)
      convert h using 1
      funext a
      simp only [Function.comp_apply]
      congr 1
      ring
    exact (hcurve u).hasMFDerivWithinAt
  have hfamJoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) 2 ×ˢ Set.univ) := by
    have hflow :=
      DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
        X hX hXcompact
    have hinput : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
        (fun q : ℝ × M => (q.1 + t - 1, q.2)) := by
      exact ((contMDiff_fst.add contMDiff_const).sub contMDiff_const).prodMk contMDiff_snd
    exact (hflow.comp hinput).contMDiffOn
  have hshift :=
    DifferentialGeometry.Geometry.Riemannian.Variation.flow_metric_pairing_hasDerivWithinAt
    (I := I) g (fun _ => Y) 2 fam hfamOde hfamJoint 1 (by norm_num) y v w
  have hshiftAt : HasDerivAt
      (fun u : ℝ => g.inner ((fam u : M → M) y)
        (mfderiv I I (fam u : M → M) y v)
        (mfderiv I I (fam u : M → M) y w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g Y
        ((fam 1 : M → M) y)
        (mfderiv I I (fam 1 : M → M) y v)
        (mfderiv I I (fam 1 : M → M) y w)) 1 :=
    hshift.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hback : HasDerivAt (fun r : ℝ => r - t + 1) 1 t := by
    simpa only [id_eq] using ((hasDerivAt_id t).sub_const t).add_const 1
  have hbase : t - t + 1 = (1 : ℝ) := by ring
  have hshiftAt' : HasDerivAt
      (fun u : ℝ => g.inner ((fam u : M → M) y)
        (mfderiv I I (fam u : M → M) y v)
        (mfderiv I I (fam u : M → M) y w))
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g Y
        ((fam 1 : M → M) y)
        (mfderiv I I (fam 1 : M → M) y v)
        (mfderiv I I (fam 1 : M → M) y w)) (t - t + 1) := by
    rw [hbase]
    exact hshiftAt
  have hcomp := hshiftAt'.comp t hback
  have hfamOne : fam 1 = globalFlowDiffeomorph X hX hXcompact t := by
    dsimp only [fam]
    congr 1
    ring
  have hfamBack : ∀ r : ℝ,
      fam (r - t + 1) = globalFlowDiffeomorph X hX hXcompact r := by
    intro r
    dsimp only [fam]
    congr 1
    ring
  rw [hfamOne] at hcomp
  have hfun :
      ((fun u : ℝ => g.inner ((fam u : M → M) y)
        (mfderiv I I (fam u : M → M) y v)
        (mfderiv I I (fam u : M → M) y w)) ∘ fun r : ℝ => r - t + 1) =
      (fun r : ℝ => g.inner (globalFlowDiffeomorph X hX hXcompact r y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y w)) := by
    funext r
    rw [Function.comp_apply, hfamBack r]
  rw [hfun] at hcomp
  simpa only [Y, mul_one] using hcomp

private theorem globalFlow_pairing_eq_of_parallel_on_Icc
    (g : SmoothRiemannianMetric I M)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {U : Set M}
    (hparallel : ∀ z ∈ U, ∀ q : TangentSpace I z,
      (LeviCivita (I := I) g) X z q = 0)
    {a b : ℝ} (hab : a ≤ b) (y : M) (v w : TangentSpace I y)
    (hpath : ∀ r ∈ Set.Icc a b, globalFlowDiffeomorph X hX hXcompact r y ∈ U) :
    g.inner (globalFlowDiffeomorph X hX hXcompact b y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact b : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact b : M → M) y w) =
      g.inner (globalFlowDiffeomorph X hX hXcompact a y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact a : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact a : M → M) y w) := by
  rcases hab.eq_or_lt with rfl | hablt
  · rfl
  let P : ℝ → ℝ := fun r =>
    g.inner (globalFlowDiffeomorph X hX hXcompact r y)
      (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y v)
      (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y w)
  have hhas : ∀ r : ℝ, HasDerivAt P
      (DifferentialGeometry.PDE.DeTurck.lieDerivMetric (I := I) g
        (⟨fun z => X z, hX⟩ : Cₛ^∞⟮I; E, TangentSpace I⟯)
        (globalFlowDiffeomorph X hX hXcompact r y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact r : M → M) y w)) r := by
    intro r
    exact globalFlow_pairing_hasDerivAt g X hX hXcompact r y v w
  have hdiff : DifferentiableOn ℝ P (Set.Icc a b) := by
    intro r hr
    exact (hhas r).differentiableAt.differentiableWithinAt
  have hderiv : ∀ r ∈ Set.Ico a b, derivWithin P (Set.Icc a b) r = 0 := by
    intro r hr
    have hrIcc : r ∈ Set.Icc a b := ⟨hr.1, le_of_lt hr.2⟩
    rw [(hhas r).hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Icc hablt) r hrIcc)]
    rw [DifferentialGeometry.PDE.RicciFlow.Pullback.cartan_formula_for_lie_deriv_metric]
    change
      g.inner _ ((LeviCivita (I := I) g) X _ _) _ +
        g.inner _ _ ((LeviCivita (I := I) g) X _ _) = 0
    rw [hparallel _ (hpath r hrIcc), hparallel _ (hpath r hrIcc)]
    simp
  exact constant_of_derivWithin_zero hdiff hderiv b (right_mem_Icc.mpr hab)

private theorem globalFlow_pairing_eq_zero_of_parallel_on_uIcc
    (g : SmoothRiemannianMetric I M)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {U : Set M}
    (hparallel : ∀ z ∈ U, ∀ q : TangentSpace I z,
      (LeviCivita (I := I) g) X z q = 0)
    (t : ℝ) (y : M) (v w : TangentSpace I y)
    (hpath : ∀ r ∈ Set.uIcc 0 t, globalFlowDiffeomorph X hX hXcompact r y ∈ U) :
    g.inner (globalFlowDiffeomorph X hX hXcompact t y)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y v)
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y w) =
      g.inner y v w := by
  have hzero : globalFlowDiffeomorph X hX hXcompact 0 y = y := by
    rw [globalFlowDiffeomorph_apply]
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact) y
  have hzeroDeriv :
      mfderiv I I (globalFlowDiffeomorph X hX hXcompact 0 : M → M) y =
        ContinuousLinearMap.id ℝ (TangentSpace I y) := by
    have hfun : (globalFlowDiffeomorph X hX hXcompact 0 : M → M) = id := by
      funext z
      rw [globalFlowDiffeomorph_apply]
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
        (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
          X hX hXcompact) z
    rw [hfun, mfderiv_id]
  by_cases ht : 0 ≤ t
  · have hsub : Set.Icc 0 t ⊆ Set.uIcc 0 t := by
      rw [Set.uIcc_of_le ht]
    have h := globalFlow_pairing_eq_of_parallel_on_Icc g X hX hXcompact hparallel ht
      y v w (fun r hr => hpath r (hsub hr))
    rw [hzero, hzeroDeriv] at h
    simpa only [ContinuousLinearMap.id_apply] using h
  · have ht' : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    have hsub : Set.Icc t 0 ⊆ Set.uIcc 0 t := by
      rw [Set.uIcc_of_ge ht']
    have h := globalFlow_pairing_eq_of_parallel_on_Icc g X hX hXcompact hparallel ht'
      y v w (fun r hr => hpath r (hsub hr))
    rw [hzero, hzeroDeriv] at h
    simpa only [ContinuousLinearMap.id_apply] using h.symm

private def RectangularCorrectedFlowMapData
    (g : SmoothRiemannianMetric I M) (x : M) (U : Set M)
    (s : (y : M) → TangentSpace I y) (f : M → ℝ)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) : Prop :=
  ∃ (W : Set M) (A : Set ℝ) (B : Set M) (delta : ℝ)
    (K : Set (perpSpace g x (s x))) (J : Set ℝ)
    (phi : PartialDiffeomorph
      ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
      (perpSpace g x (s x) × ℝ) M ∞),
    And (IsOpen W) <|
    And (x ∈ W) <|
    And (W ⊆ U) <|
    And (Set.EqOn X (fun y => s y) W) <|
    And (IsOpen A) <|
    And ((0 : ℝ) ∈ A) <|
    And (IsOpen B) <|
    And (x ∈ B) <|
    And (0 < delta) <|
    And (Metric.ball (0 : ℝ) delta ⊆ A) <|
    And (A ×ˢ B ⊆ (fun p : ℝ × M => globalFlowDiffeomorph X hX hXcompact p.1 p.2) ⁻¹' W) <|
    And (IsOpen K) <|
    And ((0 : perpSpace g x (s x)) ∈ K) <|
    And (IsOpen J) <|
    And ((0 : ℝ) ∈ J) <|
    And (phi.source = K ×ˢ J) <|
    And
      (Set.EqOn (correctedFlowMap X hX hXcompact g x (s x) f)
        phi (K ×ˢ J)) <|
    And (∀ k ∈ K, adaptedBaseMap g x (s x) k ∈ B) <|
    And (∀ k ∈ K, -f (adaptedBaseMap g x (s x) k) ∈ Metric.ball (0 : ℝ) delta) <|
    And (∀ k ∈ K, ∀ r ∈ Set.uIcc 0 (-f (adaptedBaseMap g x (s x) k)),
      globalFlowDiffeomorph X hX hXcompact r (adaptedBaseMap g x (s x) k) ∈ W) <|
    ∀ k ∈ K, ∀ t ∈ J, ∀ r ∈ Set.uIcc 0 t,
      globalFlowDiffeomorph X hX hXcompact r (phi (k, 0)) ∈ W

private theorem exists_rectangular_correctedFlowMap
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (hfx : f x = 0) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (hXeq : X =ᶠ[𝓝 x] fun y => s y) :
    RectangularCorrectedFlowMapData g x U (fun y => s y) f X hX hXcompact := by
  let F : perpSpace g x (s x) × ℝ → M :=
    correctedFlowMap X hX hXcompact g x (s x) f
  have hEqNhds : {y : M | X y = s y} ∈ 𝓝 x := hXeq
  obtain ⟨W, hWsub, hWopen, hxW⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hUopen.mem_nhds hxU) hEqNhds)
  have hWU : W ⊆ U := fun y hy => (hWsub hy).1
  have hWEq : Set.EqOn X (fun y => s y) W := fun y hy => (hWsub hy).2
  let Phi : ℝ × M → M := fun p =>
    globalFlowDiffeomorph X hX hXcompact p.1 p.2
  have hPhiSmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  have hPhiZero : Phi (0, x) = x := by
    rw [show Phi (0, x) = globalFlowDiffeomorph X hX hXcompact 0 x by rfl,
      globalFlowDiffeomorph_apply]
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact) x
  have hpre : Phi ⁻¹' W ∈ 𝓝 ((0 : ℝ), x) := by
    apply hPhiSmooth.continuous.continuousAt.preimage_mem_nhds
    rw [hPhiZero]
    exact hWopen.mem_nhds hxW
  obtain ⟨A, B, hAopen, hzeroA, hBopen, hxB, hABsub⟩ :=
    mem_nhds_prod_iff'.mp hpre
  obtain ⟨delta, hdelta, hballA⟩ :=
    Metric.mem_nhds_iff.mp (hAopen.mem_nhds hzeroA)
  have hlocal :=
    correctedFlowMap_isLocalDiffeomorphAt_infty g x hUopen hxU s f hunit hfx hf hdf
      X hX hXcompact hXeq
  obtain ⟨psi, hzeroPsi, hEqPsi⟩ := hlocal
  have hFzero : F (0, 0) = x := by
    change DifferentialGeometry.Analysis.ODE.curveAt X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact)
      (adaptedBaseMap g x (s x) 0)
      (0 - f (adaptedBaseMap g x (s x) 0)) = x
    rw [adaptedBaseMap_zero, hfx, sub_zero]
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact) x
  have hpsiZero : psi (0, 0) = x := by
    calc
      psi (0, 0) = F (0, 0) := (hEqPsi hzeroPsi).symm
      _ = x := hFzero
  let D : Set (perpSpace g x (s x) × ℝ) :=
    correctedFlowBaseDomain g x (s x) U ×ˢ Set.univ
  have hDopen : IsOpen D :=
    (isOpen_correctedFlowBaseDomain g x (s x) hUopen).prod isOpen_univ
  have hDzero : ((0 : perpSpace g x (s x)), (0 : ℝ)) ∈ D :=
    ⟨zero_mem_correctedFlowBaseDomain g x (s x) hxU, Set.mem_univ 0⟩
  let b : perpSpace g x (s x) → M := adaptedBaseMap g x (s x)
  have hbOnBase : ContinuousOn b (correctedFlowBaseDomain g x (s x) U) := by
    exact (contMDiffOn_adaptedBaseMap g x (s x)).continuousOn.mono inter_subset_left
  have hbOn : ContinuousOn (fun q : perpSpace g x (s x) × ℝ => b q.1) D := by
    exact hbOnBase.comp continuousOn_fst (by intro q hq; exact hq.1)
  have hbMapsToU : Set.MapsTo (fun q : perpSpace g x (s x) × ℝ => b q.1) D U := by
    intro q hq
    exact hq.1.2
  have hfbOn : ContinuousOn (fun q : perpSpace g x (s x) × ℝ => f (b q.1)) D := by
    exact hf.continuousOn.comp hbOn hbMapsToU
  have hnegfbOn : ContinuousOn (fun q : perpSpace g x (s x) × ℝ => -f (b q.1)) D := by
    exact ContinuousOn.neg hfbOn
  have hBpreOpen : IsOpen (D ∩ (fun q : perpSpace g x (s x) × ℝ => b q.1) ⁻¹' B) :=
    hbOn.isOpen_inter_preimage hDopen hBopen
  have hnegfbPreOpen : IsOpen
      (D ∩ (fun q : perpSpace g x (s x) × ℝ => -f (b q.1)) ⁻¹'
        Metric.ball (0 : ℝ) delta) :=
    hnegfbOn.isOpen_inter_preimage hDopen Metric.isOpen_ball
  let psiBaseSource : Set (perpSpace g x (s x) × ℝ) :=
    psi.source ∩ psi ⁻¹' B
  have hpsiBaseSourceOpen : IsOpen psiBaseSource := by
    exact psi.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      psi.open_source hBopen
  let baseAtZero : perpSpace g x (s x) × ℝ → perpSpace g x (s x) × ℝ :=
    fun q => (q.1, 0)
  have hbaseAtZeroContinuous : Continuous baseAtZero := by
    exact continuous_fst.prodMk continuous_const
  let G : Set (perpSpace g x (s x) × ℝ) :=
    (psi.source ∩ D ∩ baseAtZero ⁻¹' psiBaseSource ∩
      (fun q : perpSpace g x (s x) × ℝ => q.2) ⁻¹' Metric.ball 0 delta) ∩
      (D ∩ (fun q : perpSpace g x (s x) × ℝ => b q.1) ⁻¹' B) ∩
      (D ∩ (fun q : perpSpace g x (s x) × ℝ => -f (b q.1)) ⁻¹'
        Metric.ball (0 : ℝ) delta)
  have hGopen : IsOpen G := by
    exact (((psi.open_source.inter hDopen).inter
      (hpsiBaseSourceOpen.preimage hbaseAtZeroContinuous)).inter
        (Metric.isOpen_ball.preimage continuous_snd)).inter hBpreOpen |>.inter hnegfbPreOpen
  have hzeroG : ((0 : perpSpace g x (s x)), (0 : ℝ)) ∈ G := by
    refine ⟨⟨⟨⟨⟨hzeroPsi, hDzero⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · change ((0 : perpSpace g x (s x)), (0 : ℝ)) ∈ psiBaseSource
      refine ⟨hzeroPsi, ?_⟩
      change psi (0, 0) ∈ B
      rw [hpsiZero]
      exact hxB
    · change dist (0 : ℝ) 0 < delta
      simpa only [dist_self] using hdelta
    · exact ⟨hDzero, by change b 0 ∈ B; rw [show b 0 = x by exact adaptedBaseMap_zero g x (s x)]; exact hxB⟩
    · exact ⟨hDzero, by
        change -f (b 0) ∈ Metric.ball (0 : ℝ) delta
        rw [show b 0 = x by exact adaptedBaseMap_zero g x (s x), hfx]
        simpa only [Metric.mem_ball, neg_zero, dist_self] using hdelta⟩
  obtain ⟨K, J, hKopen, hzeroK, hJopen, hzeroJ, hKJsub⟩ :=
    mem_nhds_prod_iff'.mp (hGopen.mem_nhds hzeroG)
  let phi := restrictPartialDiffeomorphOpen psi (K ×ˢ J) (hKopen.prod hJopen)
  have hKJpsi : K ×ˢ J ⊆ psi.source :=
    fun q hq => (hKJsub hq).1.1.1.1.1
  have hphiSource : phi.source = K ×ˢ J :=
    restrictPartialDiffeomorphOpen_source_eq psi (K ×ˢ J)
      (hKopen.prod hJopen) hKJpsi
  have hEqPhi : Set.EqOn F phi (K ×ˢ J) := by
    intro q hq
    change F q = psi q
    exact hEqPsi (hKJpsi hq)
  refine ⟨W, A, B, delta, K, J, phi, hWopen, hxW, hWU, hWEq,
    hAopen, hzeroA, hBopen, hxB, hdelta, hballA, hABsub,
    hKopen, hzeroK, hJopen, hzeroJ, hphiSource, hEqPhi, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkzero : (k, (0 : ℝ)) ∈ K ×ˢ J := ⟨hk, hzeroJ⟩
    have hkG := hKJsub hkzero
    exact hkG.1.2.2
  · intro k hk
    have hkzero : (k, (0 : ℝ)) ∈ K ×ˢ J := ⟨hk, hzeroJ⟩
    have hkG := hKJsub hkzero
    exact hkG.2.2
  · intro k hk r hr
    have hkzero : (k, (0 : ℝ)) ∈ K ×ˢ J := ⟨hk, hzeroJ⟩
    have hkG := hKJsub hkzero
    have hB : b k ∈ B := hkG.1.2.2
    have hsmall : -f (b k) ∈ Metric.ball (0 : ℝ) delta := hkG.2.2
    have hrball : r ∈ Metric.ball (0 : ℝ) delta := by
      change dist r 0 < delta
      have hle : dist r 0 ≤ dist (-f (b k)) 0 := by
        simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hr
      exact lt_of_le_of_lt hle (by simpa only [Metric.mem_ball] using hsmall)
    have hrA : r ∈ A := hballA hrball
    have hpair : (r, b k) ∈ A ×ˢ B := by exact ⟨hrA, hB⟩
    have hpreW := hABsub hpair
    change Phi (r, b k) ∈ W at hpreW
    exact hpreW
  · intro k hk t ht r hr
    have hkt : (k, t) ∈ K ×ˢ J := ⟨hk, ht⟩
    have hkzero : (k, (0 : ℝ)) ∈ K ×ˢ J := ⟨hk, hzeroJ⟩
    have hkzeroG := hKJsub hkzero
    have hphiBase : phi (k, 0) ∈ B := by
      have hpsiBase : psi (k, 0) ∈ B := by
        have hbase : (k, 0) ∈ psiBaseSource := by
          have hbase' := hkzeroG.1.1.1.2
          change (k, 0) ∈ psiBaseSource at hbase'
          exact hbase'
        exact hbase.2
      have hFphi := hEqPhi hkzero
      have hFpsi : F (k, 0) = psi (k, 0) := by
        simpa only [F] using hEqPsi (hKJpsi hkzero)
      rw [← hFphi, hFpsi]
      exact hpsiBase
    have htball : t ∈ Metric.ball (0 : ℝ) delta := (hKJsub hkt).1.1.2
    have hrball : r ∈ Metric.ball (0 : ℝ) delta := by
      change dist r 0 < delta
      have hle : dist r 0 ≤ dist t 0 := by
        simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hr
      exact hle.trans_lt (by simpa only [Metric.mem_ball] using htball)
    have hrA : r ∈ A := hballA hrball
    have hpair : (r, (phi (k, 0) : M)) ∈ A ×ˢ B := ⟨hrA, hphiBase⟩
    have hpreW := hABsub hpair
    change Phi (r, phi (k, 0)) ∈ W at hpreW
    exact hpreW

private theorem correctedFlowMap_eq_flow_of_base
    (g : SmoothRiemannianMetric I M) (x : M)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (k : perpSpace g x (s x)) (t : ℝ) :
    correctedFlowMap X hX hXcompact g x (s x) f (k, t) =
      globalFlowDiffeomorph X hX hXcompact t
        (correctedFlowMap X hX hXcompact g x (s x) f (k, 0)) := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
      X hX hXcompact
  let b : M := adaptedBaseMap g x (s x) k
  have h := DifferentialGeometry.Analysis.ODE.curveAt_add X
    (hX.of_le (by norm_num))
    hcomplete b (-f b) t
  have harg : -f b + t = t - f b := by ring
  rw [harg] at h
  change DifferentialGeometry.Analysis.ODE.curveAt X hcomplete b (t - f b) =
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
      (correctedFlowMap X hX hXcompact g x (s x) f (k, 0)) t
  have hbase : correctedFlowMap X hX hXcompact g x (s x) f (k, 0) =
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete b (-f b) := by
    simp [correctedFlowMap, b]
  rw [hbase]
  change DifferentialGeometry.Analysis.ODE.curveAt X hcomplete b (t - f b) =
    DifferentialGeometry.Analysis.ODE.curveAt X hcomplete
      (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete b (-f b)) t at h
  exact h

private theorem correctedFlowMap_zero_level_of_basePath
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {W : Set M} (hWU : W ⊆ U)
    (hWEq : Set.EqOn X (fun y => s y) W)
    {K : Set (perpSpace g x (s x))}
    (hbasePath : ∀ k ∈ K, ∀ r ∈ Set.uIcc 0 (-f (adaptedBaseMap g x (s x) k)),
      globalFlowDiffeomorph X hX hXcompact r (adaptedBaseMap g x (s x) k) ∈ W)
    (k : perpSpace g x (s x)) (hk : k ∈ K) :
    f (correctedFlowMap X hX hXcompact g x (s x) f (k, 0)) = 0 := by
  let b : M := adaptedBaseMap g x (s x) k
  have hpathU : ∀ r ∈ Set.uIcc 0 (-f b),
      globalFlowDiffeomorph X hX hXcompact r b ∈ U := by
    intro r hr
    exact hWU (hbasePath k hk r hr)
  have hpathEq : ∀ r ∈ Set.uIcc 0 (-f b),
      X (globalFlowDiffeomorph X hX hXcompact r b) =
        s (globalFlowDiffeomorph X hX hXcompact r b) := by
    intro r hr
    exact hWEq (hbasePath k hk r hr)
  have hpot := globalFlow_potential_eq_add_of_path g X hX hXcompact hUopen s f hunit hf hdf
    (-f b) b hpathU hpathEq
  have hbaseFlow : correctedFlowMap X hX hXcompact g x (s x) f (k, 0) =
      globalFlowDiffeomorph X hX hXcompact (-f b) b := by
    change DifferentialGeometry.Analysis.ODE.curveAt X
      (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
        X hX hXcompact) (adaptedBaseMap g x (s x) k)
      (0 - f (adaptedBaseMap g x (s x) k)) = _
    simp only [b, zero_sub, globalFlowDiffeomorph_apply]
  rw [hbaseFlow]
  rw [hpot]
  ring

private theorem globalFlow_mfderiv_product_decomposition
    (g : SmoothRiemannianMetric I M) (x : M)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {K : Set (perpSpace g x (s x))}
    (hKopen : IsOpen K)
    (Y : perpSpace g x (s x) → M)
    (hY : ContMDiffOn (perpModel g x (s x)) I ∞ Y K)
    (k : perpSpace g x (s x)) (hk : k ∈ K) (t : ℝ)
    (u : TangentSpace (perpModel g x (s x)) k) (r : ℝ) :
    (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
      (fun z : perpSpace g x (s x) × ℝ =>
        globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1)) (k, t))
      (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (u, r)) =
      r • X (globalFlowDiffeomorph X hX hXcompact t (Y k)) +
        (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
          ((mfderiv (perpModel g x (s x)) I Y k) u) := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport X hX hXcompact
  let Phi : ℝ × M → M := fun p => globalFlowDiffeomorph X hX hXcompact p.1 p.2
  let Fflow : perpSpace g x (s x) × ℝ → M := fun z => Phi (z.2, Y z.1)
  have hPhi : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ Phi :=
    DifferentialGeometry.Analysis.ODE.contMDiff_globalFlow_joint_of_compactSupport
      X hX hXcompact
  have hYAt : ContMDiffAt (perpModel g x (s x)) I ∞ Y k :=
    (hY k hk).contMDiffAt (hKopen.mem_nhds hk)
  have hYMD : MDifferentiableAt (perpModel g x (s x)) I Y k :=
    hYAt.mdifferentiableAt (by simp)
  have hYProdAt : ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : perpSpace g x (s x) × ℝ => Y z.1) (k, t) :=
    hYAt.comp (f := fun z : perpSpace g x (s x) × ℝ => z.1) (k, t)
      contMDiffAt_fst
  have hYProdMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
      (fun z : perpSpace g x (s x) × ℝ => Y z.1) (k, t) :=
    hYProdAt.mdifferentiableAt (by simp)
  have hinputMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
      (𝓘(ℝ, ℝ).prod I) (fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1)) (k, t) := by
    apply mdifferentiableAt_snd.prodMk hYProdMD
  have hFflowAt : ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞ Fflow (k, t) := by
    exact (hPhi (t, Y k)).comp (k, t) (contMDiffAt_snd.prodMk hYProdAt)
  have hFflowMD : MDifferentiableAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I Fflow (k, t) :=
    hFflowAt.mdifferentiableAt (by simp)
  have hinputDeriv :
      mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I)
          (fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1)) (k, t) =
        (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
          (fun z : perpSpace g x (s x) × ℝ => z.2) (k, t)).prod
          (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
            (fun z : perpSpace g x (s x) × ℝ => Y z.1) (k, t)) := by
    exact mfderiv_prodMk mdifferentiableAt_snd hYProdMD
  have hinputApply (a : TangentSpace (perpModel g x (s x)) k) (c : ℝ) :
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I)
          (fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1)) (k, t))
        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (a, c)) =
        (c, (mfderiv (perpModel g x (s x)) I Y k) a) := by
    rw [hinputDeriv]
    change
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (fun z : perpSpace g x (s x) × ℝ => z.2) (k, t) (a, c),
       mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
        (fun z : perpSpace g x (s x) × ℝ => Y z.1) (k, t) (a, c)) =
      (c, (mfderiv (perpModel g x (s x)) I Y k) a)
    apply Prod.ext
    · rw [mfderiv_snd]
      rfl
    · have hYProdDeriv :
          mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
              (fun z : perpSpace g x (s x) × ℝ => Y z.1) (k, t) =
            (mfderiv (perpModel g x (s x)) I Y k).comp
              (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
                (perpModel g x (s x)) (fun z : perpSpace g x (s x) × ℝ => z.1) (k, t)) := by
        exact mfderiv_comp (k, t) hYMD mdifferentiableAt_fst
      rw [hYProdDeriv]
      rw [mfderiv_fst]
      rfl
  have hflowDeriv (a : TangentSpace (perpModel g x (s x)) k) (c : ℝ) :
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I Fflow (k, t))
          (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (a, c)) =
        c • X (Fflow (k, t)) +
          (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
            ((mfderiv (perpModel g x (s x)) I Y k) a) := by
    change
      (mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
        (Phi ∘ (fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1))) (k, t))
          (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (a, c)) = _
    have hPhiMD : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I Phi (t, Y k) :=
      (hPhi (t, Y k)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp (I := (perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, ℝ).prod I) (I'' := I) (f := fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1))
      (g := Phi) (k, t) hPhiMD hinputMD
    rw [hcomp]
    change (mfderiv (𝓘(ℝ, ℝ).prod I) I Phi (t, Y k))
      ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod I) (fun z : perpSpace g x (s x) × ℝ => (z.2, Y z.1)) (k, t))
        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (a, c))) = _
    rw [hinputApply a c]
    exact mfderiv_globalFlow_apply X hX hXcompact t (Y k) c
      ((mfderiv (perpModel g x (s x)) I Y k) a)
  exact hflowDeriv u r

private theorem globalFlow_mfderiv_pushforward
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X)) (t : ℝ) (y : M) :
    (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) y)
        (X y) = X (globalFlowDiffeomorph X hX hXcompact t y) := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
      X hX hXcompact
  let phi : ℝ → M → M := fun r z =>
    globalFlowDiffeomorph X hX hXcompact r z
  have hphiMD : MDifferentiableAt I I (phi t) y := by
    exact (globalFlowDiffeomorph X hX hXcompact t).contMDiff_toFun.mdifferentiableAt (by simp)
  have hcurveMD : MDifferentiableAt 𝓘(ℝ, ℝ) I
      (fun r : ℝ => phi r y) 0 := by
    exact (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete y 0).mdifferentiableAt
  have hcurveAt : (fun r : ℝ => phi r y) =
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y := by
    funext r
    rfl
  have hflowEq : (fun r : ℝ => phi t (phi r y)) =
      (fun r : ℝ => phi r (phi t y)) := by
    funext r
    have h₁ := DifferentialGeometry.Analysis.ODE.curveAt_add X (hX.of_le (by norm_num))
      hcomplete y r t
    have h₂ := DifferentialGeometry.Analysis.ODE.curveAt_add X (hX.of_le (by norm_num))
      hcomplete y t r
    dsimp [phi] at ⊢
    simp only [globalFlowDiffeomorph_apply]
    exact h₁.symm.trans (by simpa [add_comm] using h₂)
  have hflowEq' : (fun r : ℝ => phi t (phi r y)) =
      DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y) := by
    funext r
    have hEq := congrFun hflowEq r
    rw [hEq]
    have h := DifferentialGeometry.Analysis.ODE.curveAt_add X (hX.of_le (by norm_num))
      hcomplete y t r
    dsimp [phi] at ⊢
    rw [globalFlowDiffeomorph_apply]
  have hphi0 : phi 0 y = y := by
    dsimp [phi]
    rw [globalFlowDiffeomorph_apply]
    exact DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete y
  have hphiMD0 : MDifferentiableAt I I (phi t) (phi 0 y) := by
    simpa [hphi0] using hphiMD
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := I)
    (f := fun r : ℝ => phi r y) (g := fun z : M => phi t z) 0 hphiMD0 hcurveMD
  rw [hphi0] at hcomp
  have hcurveDeriv :=
    (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete (phi t y) 0).mfderiv
  have hcurveYDeriv :=
    (DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete y 0).mfderiv
  have hchain :
      mfderiv 𝓘(ℝ, ℝ) I
          (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y)) 0 =
        (mfderiv I I (phi t) y).comp
          (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => phi r y) 0) := by
    rw [← mfderiv_congr hflowEq']
    exact hcomp
  have hleft_eval :
      (mfderiv 𝓘(ℝ, ℝ) I
        (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y)) 0) (1 : ℝ) =
        X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y) 0) := by
    rw [hcurveDeriv]
    change (1 : ℝ) • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y) 0) = _
    simp
  have hright_eval :
      (mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => phi r y) 0) (1 : ℝ) = X y := by
    rw [hcurveAt, hcurveYDeriv]
    change (1 : ℝ) • X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y 0) = _
    rw [DifferentialGeometry.Analysis.ODE.curveAt_zero]
    simp
  have hchainApply := congrArg (fun L => L (1 : ℝ)) hchain
  rw [hleft_eval] at hchainApply
  change X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete (phi t y) 0) =
    (mfderiv I I (phi t) y)
      ((mfderiv 𝓘(ℝ, ℝ) I (fun r : ℝ => phi r y) 0) (1 : ℝ)) at hchainApply
  rw [hright_eval] at hchainApply
  have hzt := DifferentialGeometry.Analysis.ODE.curveAt_zero X hcomplete (phi t y)
  rw [hzt] at hchainApply
  simpa [phi] using hchainApply.symm

private theorem globalFlow_inner_product_product_formula
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (f : M → ℝ)
    (hunit : ∀ y ∈ U, g.inner y (s y) (s y) = 1)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    {W : Set M} (hWU : W ⊆ U)
    (hWEq : Set.EqOn X (fun y => s y) W)
    (hXparallel : ∀ y ∈ W, ∀ q : TangentSpace I y,
      (LeviCivita (I := I) g) X y q = 0)
    {K : Set (perpSpace g x (s x))} {J : Set ℝ}
    (hKopen : IsOpen K)
    (Y : perpSpace g x (s x) → M)
    (hY : ContMDiffOn (perpModel g x (s x)) I ∞ Y K)
    (hYlevel : ∀ k ∈ K, f (Y k) = 0)
    (hflowPath : ∀ k ∈ K, ∀ t ∈ J, ∀ r ∈ Set.uIcc 0 t,
      globalFlowDiffeomorph X hX hXcompact r (Y k) ∈ W)
    (k : perpSpace g x (s x)) (hk : k ∈ K) (t : ℝ)
    (ht : t ∈ J)
    (u v : TangentSpace (perpModel g x (s x)) k) (r q : ℝ) :
    g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k))
        ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
          (fun z : perpSpace g x (s x) × ℝ =>
            globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1)) (k, t))
          (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (u, r)))
        ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
          (fun z : perpSpace g x (s x) × ℝ =>
            globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1)) (k, t))
          (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (v, q))) =
      g.inner (Y k) (mfderiv (perpModel g x (s x)) I Y k u)
        (mfderiv (perpModel g x (s x)) I Y k v) + r * q := by
  have hYkW : Y k ∈ W := by
    have hz : (0 : ℝ) ∈ Set.uIcc 0 t := by simp
    have hzero : globalFlowDiffeomorph X hX hXcompact 0 (Y k) = Y k := by
      rw [globalFlowDiffeomorph_apply]
      exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
        (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
          X hX hXcompact) (Y k)
    rw [← hzero]
    exact hflowPath k hk t ht 0 hz
  have hYkU : Y k ∈ U := hWU hYkW
  have hYAt : ContMDiffAt (perpModel g x (s x)) I ∞ Y k :=
    (hY k hk).contMDiffAt (hKopen.mem_nhds hk)
  have hYMD : MDifferentiableAt (perpModel g x (s x)) I Y k :=
    hYAt.mdifferentiableAt (by simp)
  have hfAt : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f (Y k) :=
    (hf (Y k) hYkU).contMDiffAt (hUopen.mem_nhds hYkU)
  have hfMD : MDifferentiableAt I 𝓘(ℝ, ℝ) f (Y k) :=
    hfAt.mdifferentiableAt (by simp)
  have hlevelEq : (fun z : perpSpace g x (s x) => f (Y z)) =ᶠ[𝓝 k]
      (fun _ => 0) := by
    filter_upwards [hKopen.mem_nhds hk] with z hz
    exact hYlevel z hz
  have hlevelDeriv : mfderiv (perpModel g x (s x)) 𝓘(ℝ, ℝ)
      (fun z : perpSpace g x (s x) => f (Y z)) k = 0 := by
    rw [hlevelEq.mfderiv_eq]
    rw [mfderiv_const]
    rfl
  have hlevelApply (a : TangentSpace (perpModel g x (s x)) k) :
      (mfderiv (perpModel g x (s x)) 𝓘(ℝ, ℝ)
        (fun z : perpSpace g x (s x) => f (Y z)) k) a = 0 := by
    rw [hlevelDeriv]
    rfl
  have horth : ∀ a : TangentSpace (perpModel g x (s x)) k,
      g.inner (Y k) ((mfderiv (perpModel g x (s x)) I Y k) a)
        (X (Y k)) = 0 := by
    intro a
    have hchain := mfderiv_comp k hfMD hYMD
    have hchainApply := congrArg (fun L => L a) hchain
    have hzero := hlevelApply a
    change (mfderiv (perpModel g x (s x)) 𝓘(ℝ, ℝ) (f ∘ Y) k) a = 0 at hzero
    rw [hchain] at hzero
    change (mfderiv I 𝓘(ℝ, ℝ) f (Y k))
      ((mfderiv (perpModel g x (s x)) I Y k) a) = 0 at hzero
    change mvfderiv (I := I) f (Y k)
      ((mfderiv (perpModel g x (s x)) I Y k) a) = 0 at hzero
    have hXs : X (Y k) = s (Y k) := hWEq hYkW
    rw [hdf (Y k) hYkU, ← hXs] at hzero
    rw [g.symm]
    exact hzero
  have hpair (a b : TangentSpace (perpModel g x (s x)) k) :
      g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k))
          ((mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
            ((mfderiv (perpModel g x (s x)) I Y k) a))
          ((mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
            ((mfderiv (perpModel g x (s x)) I Y k) b)) =
        g.inner (Y k) ((mfderiv (perpModel g x (s x)) I Y k) a)
          ((mfderiv (perpModel g x (s x)) I Y k) b) := by
    exact globalFlow_pairing_eq_zero_of_parallel_on_uIcc g X hX hXcompact
      hXparallel t (Y k)
      ((mfderiv (perpModel g x (s x)) I Y k) a)
      ((mfderiv (perpModel g x (s x)) I Y k) b)
      (hflowPath k hk t ht)
  have hpairLeft (a : TangentSpace (perpModel g x (s x)) k) :
      g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k))
          ((mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
            ((mfderiv (perpModel g x (s x)) I Y k) a))
          (X (globalFlowDiffeomorph X hX hXcompact t (Y k))) = 0 := by
    have hp := globalFlow_pairing_eq_zero_of_parallel_on_uIcc g X hX hXcompact
      hXparallel t (Y k)
      ((mfderiv (perpModel g x (s x)) I Y k) a) (X (Y k))
      (hflowPath k hk t ht)
    rw [globalFlow_mfderiv_pushforward X hX hXcompact t (Y k)] at hp
    rw [horth a] at hp
    exact hp
  have hpairRight (a : TangentSpace (perpModel g x (s x)) k) :
      g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k))
          (X (globalFlowDiffeomorph X hX hXcompact t (Y k)))
          ((mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
            ((mfderiv (perpModel g x (s x)) I Y k) a)) = 0 := by
    rw [g.symm]
    exact hpairLeft a
  have hunitFlow :
      g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k))
        (X (globalFlowDiffeomorph X hX hXcompact t (Y k)))
        (X (globalFlowDiffeomorph X hX hXcompact t (Y k))) = 1 := by
    have htW := hflowPath k hk t ht t (by simp)
    have htU := hWU htW
    rw [hWEq htW]
    exact hunit _ htU
  have hdu := globalFlow_mfderiv_product_decomposition g x s X hX hXcompact
    hKopen Y hY k hk t u r
  have hdv := globalFlow_mfderiv_product_decomposition g x s X hX hXcompact
    hKopen Y hY k hk t v q
  rw [hdu, hdv]
  let z : TangentSpace I (globalFlowDiffeomorph X hX hXcompact t (Y k)) :=
    X (globalFlowDiffeomorph X hX hXcompact t (Y k))
  let A : TangentSpace I (globalFlowDiffeomorph X hX hXcompact t (Y k)) :=
    (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
      ((mfderiv (perpModel g x (s x)) I Y k) u)
  let B : TangentSpace I (globalFlowDiffeomorph X hX hXcompact t (Y k)) :=
    (mfderiv I I (globalFlowDiffeomorph X hX hXcompact t : M → M) (Y k))
      ((mfderiv (perpModel g x (s x)) I Y k) v)
  change g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) (r • z + A) (q • z + B) = _
  have hexpand :
      g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) (r • z + A) (q • z + B) =
        r * q * g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) z z +
          r * g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) z B +
          q * g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) A z +
          g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) A B := by
    simp [smul_eq_mul]
    ring
  rw [hexpand, hunitFlow]
  have hAB : g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) A B =
      g.inner (Y k) ((mfderiv (perpModel g x (s x)) I Y k) u)
        ((mfderiv (perpModel g x (s x)) I Y k) v) := by
    simpa [A, B] using hpair u v
  have hAz : g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) A z = 0 := by
    simpa [A, z] using hpairLeft u
  have hzB : g.inner (globalFlowDiffeomorph X hX hXcompact t (Y k)) z B = 0 := by
    simpa [B, z] using hpairRight v
  rw [hAB, hAz, hzB]
  ring

omit [I.Boundaryless] [T2Space M] in
private theorem leviCivita_parallel_of_eqOn
    (g : SmoothRiemannianMetric I M)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯)
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    {W : Set M} (hWopen : IsOpen W)
    (hXeq : Set.EqOn X (fun y => s y) W)
    (hSparallel : ∀ y ∈ W, ∀ q : TangentSpace I y,
      (LeviCivita (I := I) g) s y q = 0) :
    ∀ y ∈ W, ∀ q : TangentSpace I y,
      (LeviCivita (I := I) g) X y q = 0 := by
  intro y hy q
  let Xs : Cₛ^∞⟮I; E, TangentSpace I⟯ := ⟨X, hX⟩
  have hevent : ∀ᶠ z in 𝓝 y, X z = s z := by
    filter_upwards [hWopen.mem_nhds hy] with z hz
    exact hXeq hz
  have hc := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      Xs.mdifferentiableAt s.mdifferentiableAt
      (Filter.univ_mem : (Set.univ : Set M) ∈ 𝓝 y) hevent
  have hc' : (LeviCivita (I := I) g) X y =
      (LeviCivita (I := I) g) s y := by
    simpa [Xs] using hc
  rw [hc']
  exact hSparallel y hy q

private theorem globalFlow_mfderiv_time_apply
    (X : (y : M) → TangentSpace I y)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => (⟨y, X y⟩ : TangentBundle I M)))
    (hXcompact : IsCompact (tsupport X))
    (t : ℝ) (y : M) (r : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I
      (fun z : ℝ => globalFlowDiffeomorph X hX hXcompact z y) t) r =
      r • X (globalFlowDiffeomorph X hX hXcompact t y) := by
  let hcomplete :=
    DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
      X hX hXcompact
  have hcurve := DifferentialGeometry.Analysis.ODE.curveAt_integralCurve X hcomplete y t
  have hmf := hcurve.mfderiv
  have hglobal :
      (fun z : ℝ => globalFlowDiffeomorph X hX hXcompact z y) =
        (fun z : ℝ => DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y z) := by
    funext z
    rfl
  rw [hglobal, hmf]
  change ((1 : ℝ →L[ℝ] ℝ).smulRight
      (X (DifferentialGeometry.Analysis.ODE.curveAt X hcomplete y t))) r = _
  rw [globalFlowDiffeomorph_apply]
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]

theorem exists_local_product_from_parallel_unit_section_of_gradient_potential
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (hunit : ∀ y ∈ U,
      g.inner y (s y) (s y) = 1)
    (hparallel : ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) s y v = 0)
    (f : M → ℝ) (hfx : f x = 0)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = g.inner y (s y) v) :
    ∃ (K : Set (perpSpace g x (s x))) (J : Set ℝ)
      (phi : PartialDiffeomorph
        ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
        (perpSpace g x (s x) × ℝ) M ∞),
      And (IsOpen K)
        (And ((0 : perpSpace g x (s x)) ∈ K)
          (And (IsOpen J)
            (And ((0 : ℝ) ∈ J)
              (And (phi.source = K ×ˢ J)
                (And (phi (0, 0) = x)
                  (∀ (k : perpSpace g x (s x)), k ∈ K → ∀ (t : ℝ), t ∈ J →
                    ∀ (u v : TangentSpace (perpModel g x (s x)) k), ∀ (r q : ℝ),
                    g.inner (phi (k, t))
                      ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                        (fun z : perpSpace g x (s x) × ℝ => phi z) (k, t))
                        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (u, r)))
                      ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                        (fun z : perpSpace g x (s x) × ℝ => phi z) (k, t))
                        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (v, q))) =
                      g.inner (phi (k, 0))
                        ((mfderiv (perpModel g x (s x)) I
                          (fun z : perpSpace g x (s x) => phi (z, 0)) k) u)
                        ((mfderiv (perpModel g x (s x)) I
                          (fun z : perpSpace g x (s x) => phi (z, 0)) k) v) +
                      r * q)))))) := by
  obtain ⟨X, hX, hXcompact, hXeq⟩ :=
    exists_compactlySupported_extension_eq_eventually hUopen hxU s
  obtain ⟨W, A, B, delta, K, J, phi, hWopen, hxW, hWU, hWEq,
      hAopen, hzeroA, hBopen, hxB, hdelta, hballA, hABsub,
      hKopen, hzeroK, hJopen, hzeroJ, hphiSource, hEqPhi,
      hbaseB, hbaseSmall, hbasePath, hflowPath⟩ :=
    exists_rectangular_correctedFlowMap g x hUopen hxU s f hunit hfx hf hdf
      X hX hXcompact hXeq
  let Y : perpSpace g x (s x) → M := fun k => phi (k, 0)
  have hY : ContMDiffOn (perpModel g x (s x)) I ∞ Y K := by
    intro k hk
    have hsource : (k, (0 : ℝ)) ∈ phi.source := by
      rw [hphiSource]
      exact ⟨hk, hzeroJ⟩
    have hphiAt : ContMDiffAt ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I ∞
        (fun z : perpSpace g x (s x) × ℝ => phi z) (k, 0) :=
      (phi.contMDiffOn_toFun (k, 0) hsource).contMDiffAt
        (phi.open_source.mem_nhds hsource)
    exact (hphiAt.comp k (contMDiffAt_id.prodMk contMDiffAt_const)).contMDiffWithinAt
  have hYlevel : ∀ k ∈ K, f (Y k) = 0 := by
    intro k hk
    have hlevel := correctedFlowMap_zero_level_of_basePath g x hUopen s f hunit hf hdf
      X hX hXcompact hWU hWEq hbasePath k hk
    change f (phi (k, (0 : ℝ))) = 0
    rw [← hEqPhi ⟨hk, hzeroJ⟩]
    exact hlevel
  have hXparallel : ∀ y ∈ W, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) X y v = 0 := by
    exact leviCivita_parallel_of_eqOn g s X hX hWopen hWEq
      (fun y hy v => hparallel y (hWU hy) v)
  have hflowPath' : ∀ k ∈ K, ∀ t ∈ J, ∀ r ∈ Set.uIcc 0 t,
      globalFlowDiffeomorph X hX hXcompact r (Y k) ∈ W := by
    intro k hk t ht r hr
    exact hflowPath k hk t ht r hr
  have hflowEq : ∀ k ∈ K, ∀ t ∈ J,
      globalFlowDiffeomorph X hX hXcompact t (Y k) = phi (k, t) := by
    intro k hk t ht
    calc
      globalFlowDiffeomorph X hX hXcompact t (Y k) =
          globalFlowDiffeomorph X hX hXcompact t
            (correctedFlowMap X hX hXcompact g x (s x) f (k, 0)) := by
        rw [show Y k = phi (k, 0) by rfl, ← hEqPhi ⟨hk, hzeroJ⟩]
      _ = correctedFlowMap X hX hXcompact g x (s x) f (k, t) := by
        exact (correctedFlowMap_eq_flow_of_base g x s f X hX hXcompact k t).symm
      _ = phi (k, t) := hEqPhi ⟨hk, ht⟩
  have hphiZero : phi (0, 0) = x := by
    calc
      phi (0, 0) = correctedFlowMap X hX hXcompact g x (s x) f (0, 0) :=
        (hEqPhi ⟨hzeroK, hzeroJ⟩).symm
      _ = x := by
        change DifferentialGeometry.Analysis.ODE.curveAt X
          (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
            X hX hXcompact)
          (adaptedBaseMap g x (s x) 0)
          (0 - f (adaptedBaseMap g x (s x) 0)) = x
        rw [adaptedBaseMap_zero, hfx, sub_zero]
        exact DifferentialGeometry.Analysis.ODE.curveAt_zero X
          (DifferentialGeometry.Analysis.ODE.exists_globalIntegralCurve_of_compactSupport
            X hX hXcompact) x
  have hformula := globalFlow_inner_product_product_formula g x hUopen s f hunit hf hdf
    X hX hXcompact hWU hWEq hXparallel hKopen Y hY hYlevel hflowPath'
  refine ⟨K, J, phi, hKopen, hzeroK, hJopen, hzeroJ, hphiSource, hphiZero, ?_⟩
  intro k hk t ht u v r q
  let _ := hk
  let _ := ht
  have hEqFlow :
      (fun z : perpSpace g x (s x) × ℝ =>
        globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1)) =ᶠ[
          𝓝 (k, t)]
        (fun z : perpSpace g x (s x) × ℝ => phi z) := by
    have hprod : K ×ˢ J ∈ 𝓝 (k, t) :=
      prod_mem_nhds (hKopen.mem_nhds hk) (hJopen.mem_nhds ht)
    filter_upwards [hprod] with z hz
    calc
      globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1) =
          globalFlowDiffeomorph X hX hXcompact z.2
            (correctedFlowMap X hX hXcompact g x (s x) f (z.1, 0)) := by
        have hEqPhi0 : correctedFlowMap X hX hXcompact g x (s x) f (z.1, 0) =
            phi (z.1, 0) := hEqPhi (show (z.1, (0 : ℝ)) ∈ K ×ˢ J from
              ⟨hz.1, hzeroJ⟩)
        simpa [Y] using congrArg (globalFlowDiffeomorph X hX hXcompact z.2)
          hEqPhi0.symm
      _ = correctedFlowMap X hX hXcompact g x (s x) f (z.1, z.2) := by
        exact (correctedFlowMap_eq_flow_of_base g x s f X hX hXcompact z.1 z.2).symm
      _ = phi z := hEqPhi ⟨hz.1, hz.2⟩
  have hderivEq :
      mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
          (fun z : perpSpace g x (s x) × ℝ =>
            globalFlowDiffeomorph X hX hXcompact z.2 (Y z.1)) (k, t) =
        mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
          (fun z : perpSpace g x (s x) × ℝ => phi z) (k, t) :=
    hEqFlow.mfderiv_eq
  have hformula' := hformula k hk t ht u v r q
  rw [hflowEq k hk t ht, hderivEq] at hformula'
  simpa [Y, Function.comp_def] using hformula'

theorem exists_local_product_from_parallel_unit_section
    (g : SmoothRiemannianMetric I M) (x : M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U)
    (s : Cₛ^∞⟮I; E, TangentSpace I⟯) (hunit : ∀ y ∈ U,
      g.inner y (s y) (s y) = 1)
    (hparallel : ∀ y ∈ U, ∀ v : TangentSpace I y,
      (LeviCivita (I := I) g) s y v = 0) :
    ∃ (K : Set (perpSpace g x (s x))) (J : Set ℝ)
      (phi : PartialDiffeomorph
        ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
        (perpSpace g x (s x) × ℝ) M ∞),
      And (IsOpen K)
        (And ((0 : perpSpace g x (s x)) ∈ K)
          (And (IsOpen J)
            (And ((0 : ℝ) ∈ J)
              (And (phi.source = K ×ˢ J)
                (And (phi (0, 0) = x)
                  (∀ (k : perpSpace g x (s x)), k ∈ K → ∀ (t : ℝ), t ∈ J →
                    ∀ (u v : TangentSpace (perpModel g x (s x)) k), ∀ (r q : ℝ),
                    g.inner (phi (k, t))
                      ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                        (fun z : perpSpace g x (s x) × ℝ => phi z) (k, t))
                        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (u, r)))
                      ((mfderiv ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                        (fun z : perpSpace g x (s x) × ℝ => phi z) (k, t))
                        (show TangentSpace ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) (k, t) from (v, q))) =
                      g.inner (phi (k, 0))
                        ((mfderiv (perpModel g x (s x)) I
                          (fun z : perpSpace g x (s x) => phi (z, 0)) k) u)
                        ((mfderiv (perpModel g x (s x)) I
                          (fun z : perpSpace g x (s x) => phi (z, 0)) k) v) +
                      r * q)))))) := by
  obtain ⟨V, f, hVopen, hxV, hVU, hfx, hf, hdf⟩ :=
    exists_local_gradient_potential_of_parallel_section g hUopen hxU s hparallel
  exact exists_local_product_from_parallel_unit_section_of_gradient_potential
    g x hVopen hxV s
    (fun y hy => hunit y (hVU hy))
    (fun y hy v => hparallel y (hVU hy) v)
    f hfx hf hdf

theorem ContMDiffVectorSubbundle.exists_local_product_of_rank_eq_one
    (g : SmoothRiemannianMetric I M)
    (S : ContMDiffVectorSubbundle
      (I := I) (F := E) (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (hSrank : S.rank = 1)
    (hS : IsCovariantlyInvariantSubmoduleFamily (LeviCivita (I := I) g) S.fiber)
    (x : M) :
    ∃ (U : Set M) (s : Cₛ^∞⟮I; E, TangentSpace I⟯),
      And (IsOpen U) <| And (x ∈ U) <|
      And (∀ y ∈ U, s y ∈ S.fiber y) <|
      And (∀ y ∈ U, g.inner y (s y) (s y) = 1) <|
      And (∀ y ∈ U, ∀ v : TangentSpace I y,
        (LeviCivita (I := I) g) s y v = 0) <|
      ∃ (K : Set (perpSpace g x (s x))) (J : Set ℝ)
                (phi : PartialDiffeomorph
                  ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                  (perpSpace g x (s x) × ℝ) M ∞),
                And (IsOpen K)
                  (And ((0 : perpSpace g x (s x)) ∈ K)
                    (And (IsOpen J)
                      (And ((0 : ℝ) ∈ J)
                        (And (phi.source = K ×ˢ J)
                          (And (phi (0, 0) = x)
                            (∀ (k : perpSpace g x (s x)), k ∈ K →
                              ∀ (t : ℝ), t ∈ J →
                              ∀ (u v : TangentSpace (perpModel g x (s x)) k),
                              ∀ (r q : ℝ),
                              g.inner (phi (k, t))
                                ((mfderiv
                                  ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                                  (fun z : perpSpace g x (s x) × ℝ => phi z)
                                  (k, t))
                                  (show TangentSpace
                                    ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
                                    (k, t) from (u, r)))
                                ((mfderiv
                                  ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ)) I
                                  (fun z : perpSpace g x (s x) × ℝ => phi z)
                                  (k, t))
                                  (show TangentSpace
                                    ((perpModel g x (s x)).prod 𝓘(ℝ, ℝ))
                                    (k, t) from (v, q))) =
                                g.inner (phi (k, 0))
                                  ((mfderiv (perpModel g x (s x)) I
                                    (fun z : perpSpace g x (s x) => phi (z, 0)) k) u)
                                  ((mfderiv (perpModel g x (s x)) I
                                    (fun z : perpSpace g x (s x) => phi (z, 0)) k) v) +
                                r * q)))))) := by
  obtain ⟨U, s, hUopen, hxU, hs_mem, hs_unit, hs_parallel⟩ :=
    ContMDiffVectorSubbundle.exists_local_parallel_unit_section_of_rank_eq_one
      g S hSrank hS x
  refine ⟨U, s, hUopen, hxU, hs_mem, hs_unit, hs_parallel, ?_⟩
  exact exists_local_product_from_parallel_unit_section
    g x hUopen hxU s hs_unit hs_parallel

end DifferentialGeometry.Geometry.Connection
