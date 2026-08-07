import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.MetricArmCoeffCovariantDerivative
open DifferentialGeometry.Geometry.Connection.Realization DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.TensorRSNabla
open DifferentialGeometry.TensorMultilinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (metricCauchySchwarzBound ccTensorBilinSymm)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
section NormedDomReindexing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem rsDomDomCongrFib_contMDiff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r s ℝ E)
        (E := fun z : M => TensorRSSpace r s I z) x
        (tensorRS_domDomCongr σ (R.toSection x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel r ℝ E) (V₁ := fun x : M => Tensor0SSpace r I x)
    (F₂ := Tensor0SModel s ℝ E) (V₂ := fun x : M => Tensor0SSpace s I x)
    (φ := fun x : M => tensorRS_domDomCongr σ (R.toSection x))
  intro Y
  have hZ := ContMDiff.clm_bundle_apply (b := id) R.toSection.contMDiff Y.contMDiff
  have hperm : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel s ℝ E)
        (E := fun z : M => Tensor0SSpace s I z) x
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x)
              (Y x)))))) := by
    refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (Tensor0SSpace.ofModel (𝕜 := ℝ) (I := I) (x := x)
          (ContinuousMultilinearMap.domDomCongr σ
            (Tensor0SSpace.toModel
              ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))) :
            Tensor0SSpace s I x))).mpr ?_
    have hZcoord := (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x => (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))).mp
        hZ
    intro τ x₀
    refine (hZcoord (τ ∘ σ) x₀).congr_of_eventuallyEq ?_
    filter_upwards [Filter.univ_mem] with x _
    rw [continuousMultilinearMap_basis_repr, continuousMultilinearMap_basis_repr]
    change (ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x))))
        (fun j => (Bundle.Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x)
          ((Module.finBasis ℝ E) (τ j))) = _
    rw [ContinuousMultilinearMap.domDomCongr_apply]
    rfl
  refine hperm.congr (fun x => ?_)
  refine congrArg (fun t => TotalSpace.mk' (Tensor0SModel s ℝ E)
    (E := fun z : M => Tensor0SSpace s I z) x t) ?_
  apply Tensor0SSpace.toModel_injective
  change Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        tensorRS_domDomCongr σ (R.toSection x)) (Y x))
    = Tensor0SSpace.toModel
        (Tensor0SSpace.ofModel (ContinuousMultilinearMap.domDomCongr σ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from R.toSection x) (Y x)))))
  rw [toModel_rsDomDomCongr_apply, Tensor0SSpace.toModel_ofModel]

set_option backward.isDefEq.respectTransparency false in
def rsDomDomCongrSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) : SmoothCcTensor g r s where
  toSection :=
    { toFun := fun x : M => tensorRS_domDomCongr σ (R.toSection x)
      contMDiff_toFun := rsDomDomCongrFib_contMDiff (I := I) (M := M) g r s σ R }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma rsDomDomCongrSection_toSection (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : Equiv.Perm (Fin s)) (R : SmoothCcTensor g r s) (x : M) :
    (rsDomDomCongrSection (I := I) (M := M) g r s σ R).toSection x =
      tensorRS_domDomCongr σ (R.toSection x) := rfl

end NormedDomReindexing

def armSlotEndoPassZeroCc (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x))) :
    SmoothCcTensor g 2 3 :=
  rsDomDomCongrSection (I := I) (M := M) g 2 3 (finRotate 3)
    (armSlotEndoCc (I := I) (M := M) g 1 Arm)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
@[simp] lemma armSlotEndoPassZeroCc_toSection (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (x : M) :
    (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x =
      tensorRS_domDomCongr (finRotate 3)
        ((armSlotEndoCc (I := I) (M := M) g 1 Arm).toSection x) := rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem toModel_appCcRS_armSlotEndoPassZeroCc_eval (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (W : SmoothCcTensor g 1 2) (x : M) (om : Tensor0SSpace 1 I x)
    (v : Fin 3 → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
          (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om)
        (fun j : Fin 2 => if j = 0 then Arm x (v 1) (v 2) else v 0) := by
  classical
  have hcomp : (show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 3 I x from
        (ccOperatorFieldComp (I := I) (M := M) g 1 2 3
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm) W).toSection x) om =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm).toSection x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) := by
    rw [appCcRS_toSection]
    rfl
  rw [hcomp, armSlotEndoPassZeroCc_toSection]
  rw [toModel_rsDomDomCongr_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [armSlotEndoCc_toSection]
  rw [show (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace 3 I x from
        TensorRSSpace.ofCLM (bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)))
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) =
      bilinearSlotInsertCLM (I := I) (M := M) 1 x (Arm x)
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from W.toSection x) om) from rfl]
  rw [armSlotFib_apply_eval, slotInsertEndoFib_apply_eval]
  have hr0 : finRotate 3 (0 : Fin 3) = 1 := by decide
  have hr1 : finRotate 3 (1 : Fin 3) = 2 := by decide
  have hr2 : finRotate 3 (2 : Fin 3) = 0 := by decide
  congr 1
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, if_pos rfl]
    change Arm x (v (finRotate 3 0)) (v (finRotate 3 1)) = Arm x (v 1) (v 2)
    rw [hr0, hr1]
  · intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rw [Function.update_of_ne (Fin.succ_ne_zero 0), if_neg (Fin.succ_ne_zero 0)]
    change v (finRotate 3 2) = v 0
    rw [hr2]

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) :
    ∃ τ : Equiv.Perm (Fin (3 + j)), ∀ (x : M) (d : Tensor0SSpace 2 I x),
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
            (iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
        ContinuousMultilinearMap.domDomCongr τ
          (Tensor0SSpace.toModel
            ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
              (iteratedCovGrad (I := I) g 2 3 j
                (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) d)) := by
  induction j with
  | zero =>
    refine ⟨finRotate 3, fun x d => ?_⟩
    rw [iteratedCovGrad_zero, iteratedCovGrad_zero, armSlotEndoPassZeroCc_toSection,
      toModel_rsDomDomCongr_apply]
  | succ j ih =>
    obtain ⟨τ, hτ⟩ := ih
    refine ⟨Equiv.Perm.decomposeFin.symm (0, τ), fun x d => ?_⟩
    rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
    apply ContinuousMultilinearMap.ext
    intro v
    exact covGrad_rs_toModel_domDomCongr (I := I) (M := M) g 2 (3 + j) τ
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoCc (I := I) (M := M) g 1 Arm))
      (iteratedCovGrad (I := I) g 2 3 j (armSlotEndoPassZeroCc (I := I) (M := M) g Arm))
      hτ x d v

theorem riemannianFiberNormSq_iteratedCovGrad_armSlotEndoPassZeroCc_eq
    (g : SmoothRiemannianMetric I M)
    (Arm : ContMDiffSection I (E →L[ℝ] (E →L[ℝ] E)) ∞
      (fun x : M => TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)))
    (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g 2 (3 + j) x
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
  classical
  obtain ⟨τ, hτ⟩ := exists_iteratedCovGrad_armSlotEndoPassZeroCc_toSection_eq
    (I := I) (M := M) g Arm j
  have hsec : (iteratedCovGrad (I := I) g 2 3 j
        (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x =
      tensorRS_domDomCongr τ
        ((iteratedCovGrad (I := I) g 2 3 j
          (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x) := by
    apply ContinuousLinearMap.ext
    intro d
    apply Tensor0SSpace.toModel_injective
    change Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          (iteratedCovGrad (I := I) g 2 3 j
            (armSlotEndoPassZeroCc (I := I) (M := M) g Arm)).toSection x) d) =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (3 + j) I x from
          tensorRS_domDomCongr τ
            ((iteratedCovGrad (I := I) g 2 3 j
              (armSlotEndoCc (I := I) (M := M) g 1 Arm)).toSection x)) d)
    rw [toModel_rsDomDomCongr_apply]
    exact hτ x d
  rw [hsec]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g 2 (3 + j) x τ _

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] in
private lemma metricCovDeriv_symm_right
    (g : SmoothRiemannianMetric I M)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricCovDeriv (I := I) g cov X Y Z x = metricCovDeriv (I := I) g cov X Z Y x := by
  unfold metricCovDeriv
  rw [show (fun b : M => g.inner b (Z b) (Y b)) = (fun b : M => g.inner b (Y b) (Z b)) from by
    funext b; rw [g.symm b (Z b) (Y b)]]
  rw [g.symm x (cov.toFun Y x (X x)) (Z x), g.symm x (Y x) (cov.toFun Z x (X x))]
  ring

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma metricDiffCovDeriv_symm_right
    (g₁ g₀ : SmoothRiemannianMetric I M)
    (X Y Z : Π b : M, TangentSpace I b) (x : M) :
    metricDiffCovDeriv (I := I) g₁ g₀ X Y Z x =
      metricDiffCovDeriv (I := I) g₁ g₀ X Z Y x := by
  unfold metricDiffCovDeriv
  rw [metricCovDeriv_symm_right (I := I) g₁ (LeviCivita (I := I) g₀) X Y Z x,
    metricCovDeriv_symm_right (I := I) g₀ (LeviCivita (I := I) g₀) X Y Z x]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem endoCovariantDerivative_gInvDiffRaisedEndoField_resolvent
    (g₀ g₁ : SmoothRiemannianMetric I M)
    (V W Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (x : M) :
    g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - metricDiffCovDeriv (I := I) g₁ g₀
          (fun y : M => V y)
          (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
          (fun y : M => Z y) x := by
  classical
  have hg1gir : ∀ u : TangentSpace I x,
      g₁.inner x (metricComparisonEndo (I := I) g₀ g₁ x (W x)) u = g₀.inner x (W x) u := by
    intro u
    rw [gInvRaisedEndo_apply, inverseMetricSharpFib_inner, cotangentToDualLinear_apply,
      cotangentToDual_g0FlatCLM]
  have hpair : g₁.inner x
        (((endoCovariantDerivative (I := I) (M := M) g₀)
          (gInvDiffRaisedEndoField (I := I) g₀ g₁) x (V x)) (W x)) (Z x) =
      - g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x
          (metricComparisonEndo (I := I) g₀ g₁ x (W x)) (V x)) (Z x)
        - g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) := by
    rw [endoCov_gInvDiffRaisedField_fibrewise (I := I) g₀ g₁ x (V x) (W x)]
    rw [map_add, ContinuousLinearMap.add_apply, map_neg, ContinuousLinearMap.neg_apply,
      inverseMetricSharpFib_inner, cotangentToDualLinear_apply, cotangentToDual_dualToCotangent]
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [show (cotangentToCLM (I := I) (g0FlatCLM (I := I) g₀ x (W x)))
            (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
          g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) from
      cotangentToDual_g0FlatCLM (I := I) g₀ x (W x)
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
    ring
  have hk1 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y))
    (Z := fun y : M => Z y) V.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
    Z.mdifferentiableAt
  have hk2 := connDiff_koszul_metricDiff (I := I) g₁ g₀
    (X := fun y : M => V y) (Y := fun y : M => Z y)
    (Z := fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) V.mdifferentiableAt
    Z.mdifferentiableAt
    ((gInvRaisedEndo_section_contMDiff (I := I) g₀ g₁ W x).mdifferentiableAt (by norm_num))
  have hsym := metricDiffCovDeriv_symm_right (I := I) g₁ g₀
    (fun y : M => V y) (fun y : M => Z y)
    (fun y : M => metricComparisonEndo (I := I) g₀ g₁ y (W y)) x
  have hconv : g₀.inner x (W x) (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)) =
      g₁.inner x (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))
        (metricComparisonEndo (I := I) g₀ g₁ x (W x)) := by
    rw [← hg1gir (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x)),
      g₁.symm x (metricComparisonEndo (I := I) g₀ g₁ x (W x))
        (PDE.DeTurck.connDiff (I := I) g₁ g₀ x (Z x) (V x))]
  rw [hpair, hconv]
  simp only [] at hk1 hk2
  linarith [hk1, hk2, hsym]

end Sobolev
end Analysis
end DifferentialGeometry

end
