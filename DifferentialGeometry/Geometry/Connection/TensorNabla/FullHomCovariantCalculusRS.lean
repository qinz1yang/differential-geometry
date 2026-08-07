import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSApplication
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Curvature


noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] private def fullHomTangentSpaceFiniteDimensional {x : M} :
    FiniteDimensional ℝ (TangentSpace I x) :=
  Tensor0SBundle.tangentSpace_finiteDimensional x

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceFiniteDimensional {r t : ℕ} {x : M} :
    FiniteDimensional ℝ (TensorRSSpace r t I x) :=
  Tensor0SBundle.tensorRSSpace_finiteDimensional r t x

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
@[reducible] private def fullHomTensorRSSpaceT2 {r t : ℕ} {x : M} :
    T2Space (TensorRSSpace r t I x) := by
  unfold TensorRSSpace
  exact ContinuousLinearMap.instT2Space

set_option backward.isDefEq.respectTransparency false in

def homTensorRSDirCovDeriv (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
      (v : TangentSpace I x) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x :=
  homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_continuous (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    Continuous (fun v : TangentSpace I x => homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x
      v) :=
  (homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x).continuous

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_add (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
      (v v' : TangentSpace I x) :
    homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (v + v') =
      homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v +
        homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v' := by
  exact (homTensorRSCovariantDerivative I M r a c
    (LeviCivita (I := I) g) Ψ x).map_add v v'

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovDirHom_smul (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) (k : ℝ)
    (v : TangentSpace I x) :
    homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (k • v) =
      k • homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v := by
  exact (homTensorRSCovariantDerivative I M r a c
    (LeviCivita (I := I) g) Ψ x).map_smul k v

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradDirCLM (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace r c I x :=
  haveI : FiniteDimensional ℝ (TangentSpace I x) :=
    fullHomTangentSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r c I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun v : TangentSpace I x => homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v d
      map_add' := fun v v' => by rw [homTensorRSCovDirHom_add, ContinuousLinearMap.add_apply]
      map_smul' := fun k v => by rw [homTensorRSCovDirHom_smul, ContinuousLinearMap.smul_apply]; rfl
                                   }

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma homTensorRSCovGradDirCLM_apply (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (v : TangentSpace I x) :
    homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d v =
      homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v d := by
  rw [homTensorRSCovGradDirCLM, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

noncomputable def homTensorRSCovGradFib (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M) :
    TensorRSSpace r a I x →L[ℝ] TensorRSSpace r (c + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun d =>
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)
      map_add' := fun d₁ d₂ => by
        rw [← map_add (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.add_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, homTensorRSCovGradDirCLM_apply, map_add]
      map_smul' := fun k d => by
        rw [RingHom.id_apply, ← map_smul (covGradBundleEquiv (I := I) (M := M) r c x)]
        refine congrArg (covGradBundleEquiv (I := I) (M := M) r c x) ?_
        refine ContinuousLinearMap.ext (fun v => ?_)
        rw [ContinuousLinearMap.smul_apply, homTensorRSCovGradDirCLM_apply,
          homTensorRSCovGradDirCLM_apply, map_smul] }

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma homTensorRSCovGradFieldFib_apply_eval (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x) (x : M)
    (d : TensorRSSpace r a I x) (Dlow : Tensor0SSpace r I x)
    (v0 : TangentSpace I x) (vs : Fin c → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x d) Dlow) (Fin.cons v0 vs) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x v0 d) Dlow) vs := by
  letI : FiniteDimensional ℝ (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceFiniteDimensional (I := I) (M := M)
  letI : T2Space (TensorRSSpace r a I x) :=
    fullHomTensorRSSpaceT2 (I := I) (M := M)
  have hval : (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
        covGradBundleEquiv (I := I) (M := M) r c x
          (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d)) := by
    rw [homTensorRSCovGradFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
      AddHom.coe_mk]
  rw [hval]
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) r c x
    (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x d) Dlow (Fin.cons v0 vs)]
  have htail : Matrix.vecTail (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) = vs := by
    funext j; simp [Matrix.vecTail, Fin.cons_succ]
  have hhead : (Fin.cons v0 vs : Fin (c + 1) → TangentSpace I x) 0 = v0 := by simp [Fin.cons_zero]
  rw [htail, hhead, homTensorRSCovGradDirCLM_apply]

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem fullHomRSCovGradDirCLM_apply_apply_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r a ℝ E,
        (fun z : M => TensorRSSpace r a I z)⟯)
      (Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r c I z) x
        ((show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
          ((homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g)).toFun
            (fun y : M => (Ψ y : HomTensorRSSpace r a c I y)) x) (Y x)) (Z x))) := by
  intro Z Y
  have hgrad := homTensorRSCovariantDerivative_section_contMDiffOn I M r a c
    (LeviCivita (I := I) g) Ψ hΨ
  have hstep1 := ContMDiffOn.clm_bundle_apply (b := id) hgrad Y.contMDiff.contMDiffOn
  have hstep2 := ContMDiffOn.clm_bundle_apply (b := id) hstep1 Z.contMDiff.contMDiffOn
  rw [← contMDiffOn_univ]
  refine hstep2.congr ?_
  intro x _
  congr 1

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem fullHomRSCovGradDirCLM_apply_contMDiff
    (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ∀ (Z : Cₛ^∞⟮I; TensorRSModel r a ℝ E,
      (fun z : M => TensorRSSpace r a I z)⟯),
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace r c I z) x
        (homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))) := by
  intro Z
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := TangentSpace I) (V₂ := fun z : M => TensorRSSpace r c I z)
    (φ := fun x => homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x))
  intro Y
  exact fullHomRSCovGradDirCLM_apply_apply_contMDiff (I := I) (M := M) g r a c Ψ hΨ Z Y

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
theorem homTensorRSCovGradField_contMDiff (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r (c + 1) ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r (c + 1) I z) x
        (homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r a I z) (V₂ := fun z : M => TensorRSSpace r (c + 1) I z)
    (φ := fun x => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
  intro Z
  have hG := fullHomRSCovGradDirCLM_apply_contMDiff (I := I) (M := M) g r a c Ψ hΨ Z
  have hcov := covGradBundleEquiv_section_contMDiff (I := I) (M := M) r c
    (fun x => homTensorRSCovGradDirCLM (I := I) (M := M) g r a c Ψ x (Z x)) hG
  refine hcov.congr ?_
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem tensorCovDerivAt_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) (x : M) (v : E) :
    (show TensorRSSpace r c I x from
        tensorCovDerivAt (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W)
          x v) =
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
          homTensorRSCovariantDerivative I M r a c (LeviCivita (I := I) g) Ψ x v) (W.toSection x) +
        (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
          (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v) := by
  have hval : (fun y : M => (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W).toSection y) =
      (fun y : M => (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y)
        (W.toSection y)) := by
    funext y; rw [appFullRS_toSection (I := I) (M := M) g r a c Ψ hΨ W y]
  have hΨ_diff : MDifferentiableAt I
    (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x :=
    hΨ.contMDiffAt.mdifferentiableAt (by simp)
  have hW_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W.toSection y)) x :=
    W.toSection.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  obtain ⟨Vsec, hVx⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x v
  have hV_diff : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E (E := fun z : M => TangentSpace I z) y (Vsec y)) x :=
    Vsec.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [tensorCovDerivAt_def (I := I) (M := M) g r c
    (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) x v,
    hval]
  rw [show v = (Vsec : Π z : M, TangentSpace I z) x from hVx.symm]
  have hprod := homTensorRSCovariantDerivative_apply_of_mdifferentiableAt I M r a c
    (LeviCivita (I := I) g) Ψ (fun y : M => W.toSection y) (fun y : M => Vsec y)
    hΨ_diff hW_diff hV_diff
  rw [eq_sub_iff_add_eq] at hprod
  rw [tensorCovDerivAt_def (I := I) (M := M) g r a W x ((Vsec : Π z : M, TangentSpace I z) x)]
  rw [← hprod]

set_option backward.isDefEq.respectTransparency false in

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem covGradBundleEquiv_symm_covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a : ℕ)
    (W : SmoothCcTensor g r a) (x : M) (v0 : TangentSpace I x) :
    (covGradBundleEquiv (I := I) (M := M) r a x).symm
        ((covGrad (I := I) (M := M) g r a W).toSection x) v0 =
      (show TensorRSSpace r a I x from tensorCovDerivAt (I := I) (M := M) g r a W x v0) := by
  rw [covGrad_toSection_apply (I := I) (M := M) g r a W x, ContinuousLinearEquiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] in
theorem covGrad_appFullRS_eq (g : SmoothRiemannianMetric I M) (r a c : ℕ)
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) x (Ψ x)))
    (W : SmoothCcTensor g r a) :
    covGrad (I := I) (M := M) g r c (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) =
      homTensorRSApply (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
        homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [show ((homTensorRSApply (I := I) (M := M) g r a (c + 1)
        (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W +
      homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
        (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W)).toSection x) =
      (homTensorRSApply (I := I) (M := M) g r a (c + 1)
          (fun x : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ x)
          (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x +
        (homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
          (fun x : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c x (Ψ x))
          (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
          (covGrad (I := I) (M := M) g r a W)).toSection x from rfl]
  apply ContinuousLinearMap.ext
  intro d
  rw [ContinuousLinearMap.add_apply]
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun v => ?_)
  beta_reduce
  rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
  rw [covGrad_toSection_apply_eval (I := I) (M := M) g r c
    (homTensorRSApply (I := I) (M := M) g r a c Ψ hΨ W) x
    d v]
  have hT1val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (homTensorRSApply (I := I) (M := M) g r a (c + 1)
            (fun y : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ y)
            (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W).toSection x) d) v
              =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          homTensorRSDirCovDeriv (I := I) (M := M) g r a c Ψ x (v 0) (W.toSection x)) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r a (c + 1)
        (fun y : M => homTensorRSCovGradFib (I := I) (M := M) g r a c Ψ y)
        (homTensorRSCovGradField_contMDiff (I := I) (M := M) g r a c Ψ hΨ) W x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [homTensorRSCovGradFieldFib_apply_eval (I := I) (M := M) g r a c Ψ x (W.toSection x) d (v 0)
      (Matrix.vecTail v)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT1val]
  have hT2val : Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (c + 1) I x from
          (homTensorRSApply (I := I) (M := M) g r (a + 1) (c + 1)
            (fun y : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c y (Ψ y))
            (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
            (covGrad (I := I) (M := M) g r a W)).toSection x) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace c I x from
          (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
            (show TensorRSSpace r a I x from
              tensorCovDerivAt (I := I) (M := M) g r a W x (v 0))) d)
        (Matrix.vecTail v) := by
    rw [appFullRS_toSection (I := I) (M := M) g r (a + 1) (c + 1)
        (fun y : M => slotInsertHomTensorRSFib (I := I) (M := M) g r a c y (Ψ y))
        (slotExtendFullFib_contMDiff (I := I) (M := M) g r a c Ψ hΨ)
        (covGrad (I := I) (M := M) g r a W) x]
    rw [show v = Fin.cons (v 0) (Matrix.vecTail v) from (Fin.cons_self_tail v).symm]
    rw [slotExtendFullFib_apply_eval (I := I) (M := M) g r a c x (Ψ x)
      ((covGrad (I := I) (M := M) g r a W).toSection x) d (v 0) (Matrix.vecTail v)]
    rw [covGradBundleEquiv_symm_covGrad_appFullRS_eq (I := I) (M := M) g r a W x (v 0)]
    simp only [Fin.cons_zero, Matrix.vecTail]
    rw [show (Fin.cons (v 0) (v ∘ Fin.succ) ∘ Fin.succ) = v ∘ Fin.succ from
      funext (fun j => by simp [Fin.cons_succ])]
  rw [hT2val]
  rw [tensorCovDerivAt_appFullRS_eq (I := I) (M := M) g r a c Ψ hΨ W x (v 0)]
  rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply,
    homTensorRSDirCovDeriv]

end Connection
end Geometry
end DifferentialGeometry

end
