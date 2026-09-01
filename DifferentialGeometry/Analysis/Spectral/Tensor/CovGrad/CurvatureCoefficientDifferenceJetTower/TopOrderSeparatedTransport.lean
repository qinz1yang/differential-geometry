import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Grid
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Lowered
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.CurvatureCoefficientDifferenceJetTower.Palatini
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.IteratedCovGradSectionPermutationInvariance
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.CovariantJet.Naturality

open DifferentialGeometry.Tensor.Multilinear
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Geometry.Operator

noncomputable section


open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Analysis.Spectral.MetricRealization
  (gFibreOpBound ccTensorBilinSymm ccTensorBilin ccTensorBilin_apply ccTensorModel
    ccTensorMultilinear ccTensorBilinSymm_contMDiff ccTensorBilinSymm_apply ccTensorBilinSymm_symm)
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

namespace CurvatureCoefficientDifferenceJetTower
end CurvatureCoefficientDifferenceJetTower

open CurvatureCoefficientDifferenceJetTower

section TopOrderSeparatedTransportMirrors


namespace CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma castCcTensorRank_refl (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a : ℕ} (h : a = a)
    (W : SmoothCcTensor g₀ r a) : castCcTensorRank g₀ r h W = W := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
lemma covGrad_castCcTensorRank (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) :
    covGrad (I := I) (M := M) g₀ r b (castCcTensorRank g₀ r h W) =
      castCcTensorRank g₀ r (by omega : a + 1 = b + 1)
        (covGrad (I := I) (M := M) g₀ r a W) := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma castCcTensorRank_trans (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b c : ℕ}
    (h₁ : a = b) (h₂ : b = c) (W : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h₂ (castCcTensorRank g₀ r h₁ W) =
      castCcTensorRank g₀ r (h₁.trans h₂) W := by
  subst h₁; subst h₂; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma castCcTensorRank_sub (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h (W - W') = castCcTensorRank g₀ r h W - castCcTensorRank g₀ r h W' := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma castCcTensorRank_add (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W W' : SmoothCcTensor g₀ r a) :
    castCcTensorRank g₀ r h (W + W') = castCcTensorRank g₀ r h W + castCcTensorRank g₀ r h W' := by
  subst h; rfl

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_iteratedCovGrad_domDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      iteratedCovGrad (I := I) g₀ 0 s i (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (iteratedCovGrad (I := I) g₀ 0 s i S) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_unit_toModel_domDomCongr (I := I) (M := M)
    g₀ s σ S (domDomCongrSection (I := I) g₀ σ S)
    (fun y => domDomCongrSection_unitModel (I := I) g₀ σ S y) i
  refine ⟨σ', ?_⟩
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [hσ' x, domDomCongrSection_unitModel]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_covGrad_domDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M)
    {s : ℕ} (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    ∃ σ' : Equiv.Perm (Fin (s + 1)),
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) =
        domDomCongrSection (I := I) g₀ σ' (covGrad (I := I) (M := M) g₀ 0 s S) := by
  obtain ⟨σ', hσ'⟩ := exists_iteratedCovGrad_domDomCongrSection_eq (I := I) (M := M) g₀ σ S 1
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 (domDomCongrSection (I := I) g₀ σ S) =
      covGrad (I := I) (M := M) g₀ 0 s (domDomCongrSection (I := I) g₀ σ S) from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  rw [show iteratedCovGrad (I := I) g₀ 0 s 1 S =
      covGrad (I := I) (M := M) g₀ 0 s S from by
    rw [iteratedCovGrad_succ, iteratedCovGrad_zero]; rfl] at hσ'
  exact ⟨σ', hσ'⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma domDomCongrSection_refl (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ (Equiv.refl (Fin s)) S = S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma domDomCongrSection_comp (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ τ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ τ (domDomCongrSection (I := I) g₀ σ S) =
      domDomCongrSection (I := I) g₀ (σ.trans τ) S := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  rw [domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [ContinuousMultilinearMap.domDomCongr_apply, Equiv.trans_apply]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma domDomCongrSection_add (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S S' : SmoothCcTensor g₀ 0 s) :
    domDomCongrSection (I := I) g₀ σ (S + S') =
      domDomCongrSection (I := I) g₀ σ S + domDomCongrSection (I := I) g₀ σ S' := by
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  have hadd : ∀ (A B : SmoothCcTensor g₀ 0 s) (y : M),
      unitModel (I := I) (M := M) g₀ s (A + B) y =
        unitModel (I := I) (M := M) g₀ s A y + unitModel (I := I) (M := M) g₀ s B y := by
    intro A B y
    simp only [unitModel]
    rw [show ((A + B).toSection y) = A.toSection y + B.toSection y from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    rw [add_apply, Tensor0SSpace.toModel_add]
  rw [hadd, domDomCongrSection_unitModel, domDomCongrSection_unitModel,
    domDomCongrSection_unitModel, hadd S S' x]
  apply ContinuousMultilinearMap.ext
  intro v
  simp only [add_apply, ContinuousMultilinearMap.domDomCongr_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
lemma iteratedCovGrad_covGrad_eq_castCcTensorRank (g₀ : SmoothRiemannianMetric I M) (r s : ℕ)
    (W : SmoothCcTensor g₀ r s) (i : ℕ) :
    iteratedCovGrad (I := I) g₀ r (s + 1) i (covGrad (I := I) (M := M) g₀ r s W) =
      castCcTensorRank g₀ r (by omega : s + (i + 1) = (s + 1) + i)
        (iteratedCovGrad (I := I) g₀ r s (i + 1) W) := by
  induction i with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      rw [iteratedCovGrad_succ, ih]
      rw [covGrad_castCcTensorRank (I := I) (M := M) g₀ r
        (by omega : s + (i + 1) = (s + 1) + i)]
      rw [show iteratedCovGrad (I := I) g₀ r s (i + 1 + 1) W =
          covGrad (I := I) (M := M) g₀ r (s + (i + 1))
            (iteratedCovGrad (I := I) g₀ r s (i + 1) W) from by
        rw [iteratedCovGrad_succ]]

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_iteratedCovGrad_rsDomDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (i : ℕ) :
    ∃ σ' : Equiv.Perm (Fin (s + i)),
      ∀ x : M,
        ((iteratedCovGrad (I := I) g₀ r s i
            (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z)).toSection x :
          Tensor0SSpace r I x →L[ℝ] Tensor0SSpace (s + i) I x) =
        rsDomDomCongr (I := I) (M := M) σ'
          ((iteratedCovGrad (I := I) g₀ r s i Z).toSection x) := by
  induction i with
  | zero =>
      refine ⟨σ, fun x => ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rfl
  | succ i ih =>
      obtain ⟨σ', hσ'⟩ := ih
      refine ⟨Equiv.Perm.decomposeFin.symm (0, σ'), fun x => ?_⟩
      rw [iteratedCovGrad_succ, iteratedCovGrad_succ]
      apply ContinuousLinearMap.ext
      intro d
      apply Tensor0SSpace.toModel_injective
      apply ContinuousMultilinearMap.ext
      intro v
      have hL := covGrad_rs_toModel_domDomCongr (I := I) (M := M) g₀ r (s + i) σ'
        (iteratedCovGrad (I := I) g₀ r s i Z)
        (iteratedCovGrad (I := I) g₀ r s i
          (rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z))
        (fun y d' => by
          rw [hσ' y]
          exact toModel_rsDomDomCongr_apply (I := I) (M := M) σ' _ d') x d v
      refine hL.trans ?_
      exact (congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M)
        (Equiv.Perm.decomposeFin.symm (0, σ'))
        ((covGrad (I := I) (M := M) g₀ r (s + i)
          (iteratedCovGrad (I := I) g₀ r s i Z)).toSection x) d)).symm

end CurvatureCoefficientDifferenceJetTower

section MetricLowering



namespace CurvatureCoefficientDifferenceJetTower

def riemannianMetricCovariantTensor (g₀ : SmoothRiemannianMetric I M) (x : M) : Tensor0SSpace 2 I x :=
  (show ContinuousMultilinearMap ℝ (fun _ : Fin 2 => TangentSpace I x) ℝ from
    { toFun := fun m => g₀.inner x (m 0) (m 1)
      map_update_add' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i a a'
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_add,
            add_apply]
      map_update_smul' := by
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        have h10 : (1 : Fin 2) ≠ 0 := by decide
        intro _ m i c a
        fin_cases i <;>
          simp only [Fin.reduceFinMk, Fin.isValue, Function.update_self, ne_eq,
            Function.update_of_ne, h01, h10, not_false_eq_true, map_smul,
            smul_apply]
      cont := ((g₀.inner x).continuous.comp (continuous_apply 0)).clm_apply
        (continuous_apply 1) }
    : Tensor0SSpace 2 I x)

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] lemma riemannianMetricCovariantTensor_apply (g₀ : SmoothRiemannianMetric I M) (x : M)
    (m : Fin 2 → TangentSpace I x) :
    riemannianMetricCovariantTensor (I := I) g₀ x m = g₀.inner x (m 0) (m 1) := rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem riemannianMetricCovariantTensor_contMDiff (g₀ : SmoothRiemannianMetric I M) :
    ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun z : M => Tensor0SSpace 2 I z) x (riemannianMetricCovariantTensor (I := I) g₀ x)) := by
  classical
  refine (contMDiff_multilinearSection_iff_coord (𝕜 := ℝ) (F := E)
      (E := (TangentSpace I : M → Type _)) (IB := I) (n := (∞ : WithTop ℕ∞)) (Module.finBasis ℝ E)
      (fun x : M => (riemannianMetricCovariantTensor (I := I) g₀ x :
        Bundle.continuousMultilinearMap ℝ 2 E (TangentSpace I) x))).mpr ?_
  intro σ x₀
  set b := Module.finBasis ℝ E with hb
  set e₁ := trivializationAt E (TangentSpace I : M → Type _) x₀ with he₁def
  have he₁ : x₀ ∈ e₁.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hframe := e₁.isLocalFrameOn_localFrame_baseSet I (⊤ : ℕ∞) b
  obtain ⟨Y, hY⟩ := hframe.exists_contMDiffSection_eqOn_nhd e₁.open_baseSet he₁
  have hscalar : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun x : M => g₀.inner x (Y (σ 0) x) (Y (σ 1) x)) x₀ :=
    (contMDiff_g_inner_of_smooth_sections (I := I) g₀ (Y (σ 0)) (Y (σ 1))).contMDiffAt
  refine hscalar.congr_of_eventuallyEq ?_
  have h_base₁ : ∀ᶠ x in 𝓝 x₀, x ∈ e₁.baseSet := e₁.open_baseSet.mem_nhds he₁
  filter_upwards [h_base₁, hY] with x hx₁ hYx
  rw [continuousMultilinearMap_basis_repr]
  have hframeEq : ∀ k : Fin 2, e₁.symmL ℝ x (b (σ k)) = (Y (σ k)) x := by
    intro k
    rw [hYx (σ k), Trivialization.localFrame_apply_of_mem_baseSet (hx := hx₁)]
    exact e₁.symmL_apply hx₁ (b (σ k))
  change g₀.inner x (e₁.symmL ℝ x (b (σ 0))) (e₁.symmL ℝ x (b (σ 1))) = _
  rw [hframeEq 0, hframeEq 1]

def riemannianMetricCovariantTensorField (g₀ : SmoothRiemannianMetric I M) :
    Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ 2 :=
  letI := Tensor0SBundle.tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2
  ⟨fun x => riemannianMetricCovariantTensor (I := I) g₀ x, riemannianMetricCovariantTensor_contMDiff (I := I) g₀⟩

def riemannianMetricCcTensor (g₀ : SmoothRiemannianMetric I M) : SmoothCcTensor g₀ 0 2 where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ (riemannianMetricCovariantTensorField (I := I) g₀)
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma riemannianMetricCcTensor_unitModel (g₀ : SmoothRiemannianMetric I M) (x : M) :
    unitModel (I := I) (M := M) g₀ 2 (riemannianMetricCcTensor (I := I) (M := M) g₀) x =
      Tensor0SSpace.toModel (riemannianMetricCovariantTensor (I := I) g₀ x) := by
  rw [unitModel]
  rw [show (riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x
        (unitTensor (I := I) (M := M) x) =
      (MixedSection.eval₀ (F := E) (E := (TangentSpace I : M → Type _)) x).smulRight
          (riemannianMetricCovariantTensorField (I := I) g₀ x)
          (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => TangentSpace I x) (1 : ℝ))
      from rfl]
  rw [ContinuousLinearMap.smulRight_apply, MixedSection.eval₀_apply,
    ContinuousMultilinearMap.constOfIsEmpty_apply, one_smul]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma toModel_covector_apply (x : M) (om : Tensor0SSpace 1 I x)
    (m : Fin 1 → E) :
    Tensor0SSpace.toModel om m =
      cotangentToDual (I := I) (x := x) om
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)) := by
  rw [show m = (fun _ : Fin 1 => m 0) from by
    funext k; fin_cases k; rfl]
  rw [cotangentToDual_apply]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianMetricCovariantTensor_curry_eq_flat (g₀ : SmoothRiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x) (riemannianMetricCovariantTensor (I := I) g₀ x) v =
      g0FlatCLM (I := I) g₀ x v := by
  apply tensor0SSpace_ext (𝕜 := ℝ) 1 x
  intro w
  rfl

noncomputable def lowerContravariantSlot (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) : SmoothCcTensor g₀ 0 (s + 2) :=
  operatorFieldApply (I := I) (M := M) g₀ 2 (s + 2)
    (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z) (riemannianMetricCcTensor (I := I) (M := M) g₀)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma riemannianMetricCcTensor_toSection_unitTensor (g₀ : SmoothRiemannianMetric I M) (x : M) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
        (riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x)
      (unitTensor (I := I) (M := M) x) = riemannianMetricCovariantTensor (I := I) g₀ x := by
  apply Tensor0SSpace.toModel_injective
  have h := riemannianMetricCcTensor_unitModel (I := I) (M := M) g₀ x
  rw [unitModel] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma lowerContravariantSlot_unitModel_apply (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (Z : SmoothCcTensor g₀ 1 (s + 1)) (x : M) (m : Fin (s + 2) → E) :
    unitModel (I := I) (M := M) g₀ (s + 2) (lowerContravariantSlot (I := I) (M := M) g₀ s Z) x m =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x)
          (g0FlatCLM (I := I) g₀ x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))))
        (Matrix.vecTail m) := by
  classical
  rw [unitModel]
  rw [show ((lowerContravariantSlot (I := I) (M := M) g₀ s Z).toSection x
        (unitTensor (I := I) (M := M) x)) =
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from
          (riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x)
          (unitTensor (I := I) (M := M) x)) from rfl]
  rw [riemannianMetricCcTensor_toSection_unitTensor (I := I) (M := M) g₀ x]
  rw [show ((show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace (s + 2) I x from
        (slotExtend (I := I) (M := M) g₀ 1 (s + 1) Z).toSection x)
        (riemannianMetricCovariantTensor (I := I) g₀ x)) =
      (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
        ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
          ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x)
            (riemannianMetricCovariantTensor (I := I) g₀ x))) from rfl]
  rw [show m = Fin.cons (m 0) (Matrix.vecTail m) from by
    funext k
    refine Fin.cases rfl (fun j => rfl) k]
  rw [← TensorMultilinear.tensor0S_curry_toModel_apply (I := I) (M := M) (n := s + 1)
    (T := (tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) (s + 1) x).symm
      ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Z.toSection x).comp
        ((tensor0SCurry (I := I) (M := M) (𝕜 := ℝ) 1 x)
          (riemannianMetricCovariantTensor (I := I) g₀ x))))]
  simp only [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  rw [riemannianMetricCovariantTensor_curry_eq_flat (I := I) (M := M) g₀ x
    ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))]
  simp only [Fin.cons_zero, Matrix.vecTail]
  rw [show Fin.cons (m 0) (m ∘ Fin.succ) ∘ Fin.succ = m ∘ Fin.succ from by
    funext k
    simp only [Function.comp_apply, Fin.cons_succ]]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma interiorProduct_toModel_apply (s : ℕ) (x : M) (vv : TangentSpace I x)
    (D : Tensor0SSpace (s + 1) I x) (w : Fin s → E) :
    Tensor0SSpace.toModel
        (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x vv D) w =
      Tensor0SSpace.toModel D
        (Fin.cons (tangentSpaceModelContinuousLinearEquiv (I := I) x vv) w) := by
  have h1 : Tensor0SSpace.toModel
      (Tensor0SBundle.interiorProduct (𝕜 := ℝ) (I := I) s x vv D) =
      Tensor0SBundle.modelInteriorProduct (𝕜 := ℝ) (E := E) s
        (tangentSpaceModelContinuousLinearEquiv (I := I) x vv) (Tensor0SSpace.toModel D) := rfl
  rw [h1]
  rfl

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lowerContravariantSlot_cometricRaiseSlot0Field (g₀ : SmoothRiemannianMetric I M) (s : ℕ)
    (W : SmoothCcTensor g₀ 0 (s + 2)) :
    lowerContravariantSlot (I := I) (M := M) g₀ s
        (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) = W := by
  classical
  apply smoothCcTensor_ext_of_unitModel (I := I) (M := M) g₀
  intro x
  apply ContinuousMultilinearMap.ext
  intro m
  rw [lowerContravariantSlot_unitModel_apply (I := I) (M := M) g₀ s
    (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) x m]
  rw [cometricRaiseSlot0Field_toSection (I := I) (M := M) g₀ s W x]
  rw [cometricRaiseSlot0Fib_clm_apply (I := I) g₀ s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x))
    (g0FlatCLM (I := I) g₀ x
      ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0)))]
  rw [interiorProduct_toModel_apply (I := I) (M := M) (s + 1) x
    (inverseMetricSharpFib (I := I) g₀ x
      (g0FlatCLM (I := I) g₀ x
        ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (m 0))))
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 2) I x from W.toSection x)
      (unitTensor (I := I) (M := M) x)) (Matrix.vecTail m)]
  rw [inverseMetricSharpFib_g0FlatCLM]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [unitModel]
  refine congrArg _ ?_
  funext k
  refine Fin.cases rfl (fun j => rfl) k

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma exists_iteratedCovGrad_cometricRaiseSlot0Field_eq (g₀ : SmoothRiemannianMetric I M)
    (s : ℕ) (W : SmoothCcTensor g₀ 0 (s + 2)) (i : ℕ) :
    ∃ σ : Equiv.Perm (Fin ((s + i) + 2)),
      iteratedCovGrad (I := I) g₀ 1 (s + 1) i
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ s W) =
        castCcTensorRank g₀ 1 (by omega : (s + i) + 1 = (s + 1) + i)
          (cometricRaiseSlot0Field (I := I) (M := M) g₀ (s + i)
            (domDomCongrSection (I := I) g₀ σ
              (castCcTensorRank g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
                (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W)))) := by
  induction i with
  | zero =>
      refine ⟨Equiv.refl _, ?_⟩
      rw [iteratedCovGrad_zero, iteratedCovGrad_zero]
      rw [show (castCcTensorRank g₀ 0 (by omega : (s + 2) + 0 = (s + 0) + 2) W) = W from rfl]
      rw [domDomCongrSection_refl (I := I) (M := M) g₀ W]
      rfl
  | succ i ih =>
      obtain ⟨σ, hσ⟩ := ih
      obtain ⟨σ', hσ'⟩ := exists_covGrad_domDomCongrSection_eq (I := I) (M := M) g₀ σ
        (castCcTensorRank g₀ 0 (by omega : (s + 2) + i = (s + i) + 2)
          (iteratedCovGrad (I := I) g₀ 0 (s + 2) i W))
      refine ⟨σ'.trans (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1), ?_⟩
      rw [iteratedCovGrad_succ, hσ]
      rw [covGrad_castCcTensorRank (I := I) (M := M) g₀ 1
        (by omega : (s + i) + 1 = (s + 1) + i)]
      rw [covGrad_cometricRaiseSlot0Field_eq (I := I) (M := M) g₀ (s + i)]
      rw [hσ']
      rw [domDomCongrSection_comp (I := I) (M := M) g₀ σ'
        (Equiv.swap (0 : Fin ((s + i) + 2 + 1)) 1)]
      rw [covGrad_castCcTensorRank (I := I) (M := M) g₀ 0
        (by omega : (s + 2) + i = (s + i) + 2)]
      rw [← iteratedCovGrad_succ]
      rfl

end CurvatureCoefficientDifferenceJetTower

end MetricLowering

section HeadTransport



namespace CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_domDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M) {s : ℕ}
    (σ : Equiv.Perm (Fin s)) (S : SmoothCcTensor g₀ 0 s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x
        ((domDomCongrSection (I := I) g₀ σ S).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 s x (S.toSection x) := by
  have h := riemannianFiberNormSq_iteratedCovGrad_domDomCongrSection (I := I) (M := M)
    g₀ σ S 0 x
  rw [iteratedCovGrad_zero, iteratedCovGrad_zero] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_castCcTensorRank_eq (g₀ : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) (W : SmoothCcTensor g₀ r a) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r b x
        ((castCcTensorRank g₀ r h W).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r a x (W.toSection x) := by
  subst h; rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
    [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
lemma tensorRS_domDomCongr_sub {r s : ℕ} {x : M} (σ : Equiv.Perm (Fin s))
    (T T' : TensorRSSpace r s I x) :
    rsDomDomCongr (I := I) (M := M) σ (T - T') =
      rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T' := by
  apply ContinuousLinearMap.ext
  intro d
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro v
  have hL := congrArg (fun f => f v)
    (toModel_rsDomDomCongr_apply (I := I) (M := M) σ (T - T') d)
  refine hL.trans ?_
  have e1 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d := rfl
  have e2 : ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T - rsDomDomCongr (I := I) (M := M) σ T') d) =
      (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T) d -
        (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
          rsDomDomCongr (I := I) (M := M) σ T') d := rfl
  have h1 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T) d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  have h2 : Tensor0SSpace.toModel
      ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
        rsDomDomCongr (I := I) (M := M) σ T') d) v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
        (fun k => v (σ k)) := by
    have := congrArg (fun f => f v) (toModel_rsDomDomCongr_apply (I := I) (M := M) σ T' d)
    refine this.trans ?_
    simp only [ContinuousMultilinearMap.domDomCongr_apply]
  calc ContinuousMultilinearMap.domDomCongr σ
        (Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)) v
      = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T - T') d)
          (fun k => v (σ k)) := by
        simp only [ContinuousMultilinearMap.domDomCongr_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d -
            (show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by rw [e1]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T) d)
          (fun k => v (σ k)) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from T') d)
          (fun k => v (σ k)) := by
        rw [Tensor0SSpace.toModel_sub]
        simp only [sub_apply]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T) d) v -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T') d) v := by rw [h1, h2]
    _ = Tensor0SSpace.toModel
          ((show Tensor0SSpace r I x →L[ℝ] Tensor0SSpace s I x from
            rsDomDomCongr (I := I) (M := M) σ T -
              rsDomDomCongr (I := I) (M := M) σ T') d) v := by
        rw [e2, Tensor0SSpace.toModel_sub]
        simp only [sub_apply]

omit [SigmaCompactSpace M] in
lemma exists_lowerContravariantSlot_head_transport (g₀ : SmoothRiemannianMetric I M)
    (σ₀ : Equiv.Perm (Fin (2 + 2)))
    (Y : SmoothCcTensor g₀ 1 (2 + 1)) (i : ℕ) (HY : SmoothCcTensor g₀ 1 ((2 + 1) + i)) :
    ∃ Hd : SmoothCcTensor g₀ 0 ((2 + 2) + i), ∀ x : M,
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x (Hd.toSection x) ≤
        (Module.finrank ℝ E : ℝ) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (HY.toSection x)) ∧
      (riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
              (domDomCongrSection (I := I) g₀ σ₀
                (lowerContravariantSlot (I := I) (M := M) g₀ 2 Y)) - Hd).toSection x) ≤
        2 * ((Module.finrank ℝ E : ℝ) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
        2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ∑ k ∈ Finset.range i,
              ((Module.finrank ℝ E : ℝ) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                  (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x))) := by
  classical
  obtain ⟨σ₂, hσ₂⟩ := exists_iteratedCovGrad_slotExtend_rsDomDomCongr (I := I) (M := M)
    g₀ 1 (2 + 1) Y i
  obtain ⟨σ₁, hσ₁⟩ := exists_iteratedCovGrad_domDomCongrSection_eq (I := I) (M := M) g₀
    σ₀ (lowerContravariantSlot (I := I) (M := M) g₀ 2 Y) i
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  set gW : SmoothCcTensor g₀ 0 2 := riemannianMetricCcTensor (I := I) (M := M) g₀ with hgW_def
  set TransHead : SmoothCcTensor g₀ (1 + 1) (((2 + 1) + 1) + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
      (castCcTensorRank g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
        (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)) with hTransHead_def
  refine ⟨domDomCongrSection (I := I) g₀ σ₁
    (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW), fun x => ?_⟩
  have hgW_nn : 0 ≤ riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) :=
    riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x _
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hTransHead_riemannianFiberNormSq : ∀ (V : SmoothCcTensor g₀ 1 ((2 + 1) + i)),
      riemannianFiberNormSq (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ (1 + 1) (((2 + 1) + 1) + i) σ₂
          (castCcTensorRank g₀ (1 + 1) (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
            (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V))).toSection x) =
      n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x (V.toSection x) := by
    intro V
    rw [rsDomDomCongrSection_toSection]
    rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
      (((2 + 1) + 1) + i) x σ₂ _]
    rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ (1 + 1)
      (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
      (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) V) x]
    rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) V x]
  constructor
  · rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σ₁ _ x]
    rw [operatorFieldApplication_toSection]
    refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
      ((2 + 2) + i) x
      (show Tensor0SSpace 2 I x →L[ℝ] Tensor0SSpace ((2 + 2) + i) I x from
        TransHead.toSection x)
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 2 I x from gW.toSection x)) ?_
    rw [hTransHead_def, hTransHead_riemannianFiberNormSq HY]
    exact le_of_eq (by ring)
  · have hcorner := iteratedCovGrad_operatorFieldApplication_eq_coeffCorner_add_lower (I := I) (M := M) g₀ 2
      (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW i
    have hlow : lowerContravariantSlot (I := I) (M := M) g₀ 2 Y =
        operatorFieldApply (I := I) (M := M) g₀ 2 (2 + 2)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) gW := rfl
    have hsplit : iteratedCovGrad (I := I) g₀ 0 (2 + 2) i
          (domDomCongrSection (I := I) g₀ σ₀
            (lowerContravariantSlot (I := I) (M := M) g₀ 2 Y)) -
          domDomCongrSection (I := I) g₀ σ₁
            (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i) TransHead gW) =
        domDomCongrSection (I := I) g₀ σ₁
          (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
            ∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)) := by
      rw [hσ₁, hlow, hcorner]
      rw [← domDomCongrSection_sub (I := I) (M := M) g₀ σ₁]
      refine congrArg (fun Z => domDomCongrSection (I := I) g₀ σ₁ Z) ?_
      rw [operatorFieldApplication_sub_left (I := I) (M := M) g₀ 2 ((2 + 2) + i) _ TransHead gW]
      rw [add_sub_right_comm]
    rw [hsplit]
    rw [riemannianFiberNormSq_domDomCongrSection_eq (I := I) (M := M) g₀ σ₁ _ x]
    rw [show (((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW +
        ∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)) =
        (operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x +
        (∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 0 ((2 + 2) + i) x _ _) ?_
    have hA : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
          (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) ≤
        n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
      rw [operatorFieldApplication_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0 2
        ((2 + 2) + i) x _ _) ?_
      have hD : riemannianFiberNormSq (I := I) (M := M) g₀ 2 ((2 + 2) + i) x
          ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
          n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x) := by
        rw [show ((iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead).toSection x) =
            (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y)).toSection x -
              TransHead.toSection x from by
          rw [SmoothCcTensor.toSection_sub]; rfl]
        rw [hσ₂ x]
        rw [hTransHead_def, rsDomDomCongrSection_toSection]
        rw [← tensorRS_domDomCongr_sub (I := I) (M := M) σ₂]
        rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ (1 + 1)
          (((2 + 1) + 1) + i) x σ₂ _]
        rw [show ((castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y))).toSection x -
            (castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) =
            ((castCcTensorRank g₀ (1 + 1)
              (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i)
              (slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i)
                  (iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y) -
                slotExtend (I := I) (M := M) g₀ 1 ((2 + 1) + i) HY)).toSection x) from by
          rw [castCcTensorRank_sub, SmoothCcTensor.toSection_sub]; rfl]
        rw [← slotExtend_sub (I := I) (M := M) g₀ 1 ((2 + 1) + i)]
        rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ (1 + 1)
          (by omega : (((2 + 1) + i) + 1) = ((2 + 1) + 1) + i) _ x]
        rw [riemannianFiberNormSq_slotExtend_eq (I := I) (M := M) g₀ 1 ((2 + 1) + i) _ x]
      rw [hD]
      have hgWx := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x (gW.toSection x)
      have hYd := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)
      exact le_of_eq (by ring)
    have hcorrectionTerm : ∀ k ∈ Finset.range i,
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
          ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        operatorFieldApplicationGdiag (E := E) i *
          ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
      intro k hk
      have hk_le : k + 1 ≤ i := by
        rw [Finset.mem_range] at hk; omega
      rw [operatorFieldComposition_toSection]
      refine le_trans (riemannianFiberNormSq_compRS_le_mul (I := I) (M := M) g₀ 0
        (2 + (k + 1)) ((2 + 2) + i) x _ _) ?_
      have hΨ : riemannianFiberNormSq (I := I) (M := M) g₀ (2 + (k + 1)) ((2 + 2) + i) x
          ((operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
            (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1)).toSection x) ≤
          operatorFieldApplicationGdiag (E := E) i *
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
              ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) := by
        have hw := riemannianFiberNormSq_iteratedCovGrad_operatorFieldApplicationLeibnizPsi_window_le (I := I) (M := M) g₀ 2
          (2 + 2) (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1) 0 hk_le x
        rw [iteratedCovGrad_zero] at hw
        rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g₀ 2 (2 + 2)
          (show (i - (k + 1)) + 0 = i - (k + 1) from by omega)
          (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) x] at hw
        refine le_trans hw ?_
        exact mul_le_mul_of_nonneg_left
          (riemannianFiberNormSq_iteratedCovGrad_slotExtend_le (I := I) (M := M) g₀ 1 (2 + 1)
            Y (i - (k + 1)) x)
          (operatorFieldApplicationGdiag_nonneg (E := E) i)
      refine le_trans (mul_le_mul_of_nonneg_right hΨ
        (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x _)) ?_
      exact le_of_eq (by ring)
    have hB : riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
        ((∑ k ∈ Finset.range i,
          ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
              (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
            (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x) ≤
        (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
      rw [SmoothCcTensor.toSection_sum_apply]
      refine le_trans (riemannianFiberNormSq_sum_le_card_mul (I := I) (M := M) g₀ 0
        ((2 + 2) + i) x (Finset.range i) _) ?_
      rw [Finset.card_range]
      calc ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
              ((ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
          ≤ ((i : ℕ) : ℝ) * ∑ k ∈ Finset.range i,
              operatorFieldApplicationGdiag (E := E) i *
                ((n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                    ((2 + 1) + (i - (k + 1))) x
                    ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                  riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                    ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k hk => ?_))
              (Nat.cast_nonneg i)
            exact hcorrectionTerm k hk
        _ = (i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => by ring)
    calc 2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((operatorFieldApply (I := I) (M := M) g₀ 2 ((2 + 2) + i)
              (iteratedCovGrad (I := I) g₀ 2 (2 + 2) i
                (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) - TransHead) gW).toSection x) +
          2 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 ((2 + 2) + i) x
            ((∑ k ∈ Finset.range i,
              ccOperatorFieldComp (I := I) (M := M) g₀ 0 (2 + (k + 1)) ((2 + 2) + i)
                (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 2 (2 + 2)
                  (slotExtend (I := I) (M := M) g₀ 1 (2 + 1) Y) i (k + 1))
                (iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW)).toSection x)
        ≤ 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x (gW.toSection x) *
              riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
                ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i Y - HY).toSection x)) +
            2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
              ∑ k ∈ Finset.range i,
                (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1
                  ((2 + 1) + (i - (k + 1))) x
                  ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) Y).toSection x)) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1) gW).toSection x)) := by
          have h2 : (0 : ℝ) ≤ 2 := by norm_num
          exact add_le_add (mul_le_mul_of_nonneg_left hA h2)
            (mul_le_mul_of_nonneg_left hB h2)
      _ = _ := by rw [hgW_def, hn_def]

end CurvatureCoefficientDifferenceJetTower

end HeadTransport

section ConnectionDifferenceCarrierSplit


namespace CurvatureCoefficientDifferenceJetTower

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
lemma iteratedCovGrad_connectionDifferenceSection_eq_head_add_tail (g₀ g₁ : SmoothRiemannianMetric I M) (j : ℕ) :
    iteratedCovGrad (I := I) g₀ 1 2 j (connectionDifferenceSection (I := I) g₁ g₀) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
          (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
          (sharpFlatEndoCc (I := I) g₀ g₁) +
        ∑ k ∈ Finset.range j,
          ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + (k + 1)) (2 + j)
            (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j (k + 1))
            (iteratedCovGrad (I := I) g₀ 1 1 (k + 1) (sharpFlatEndoCc (I := I) g₀ g₁)) := by
  rw [connectionDifferenceSection_eq_operatorFieldComposition_raisedKoszul_sharpFlatEndoCc (I := I) (M := M) g₀ g₁]
  rw [iteratedCovGrad_operatorFieldComposition_eq (I := I) (M := M) g₀ 1 1 2
    (raisedKoszul (I := I) g₀ g₁) (sharpFlatEndoCc (I := I) g₀ g₁) j]
  rw [Finset.sum_range_succ' (fun k =>
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + k) (2 + j)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j k)
      (iteratedCovGrad (I := I) g₀ 1 1 k (sharpFlatEndoCc (I := I) g₀ g₁))) j]
  have hf0 : ccOperatorFieldComp (I := I) (M := M) g₀ 1 (1 + 0) (2 + j)
      (operatorFieldApplicationLeibnizPsi (I := I) (M := M) g₀ 1 2 (raisedKoszul (I := I) g₀ g₁) j 0)
      (iteratedCovGrad (I := I) g₀ 1 1 0 (sharpFlatEndoCc (I := I) g₀ g₁)) =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j)
        (iteratedCovGrad (I := I) g₀ 1 2 j (raisedKoszul (I := I) g₀ g₁))
        (sharpFlatEndoCc (I := I) g₀ g₁) :=
    congrArg (fun Z : SmoothCcTensor g₀ 1 (2 + j) =>
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + j) Z (sharpFlatEndoCc (I := I) g₀ g₁))
      (operatorFieldApplicationLeibnizPsi_zero_right_eq (I := I) (M := M) g₀ 1 2
        (raisedKoszul (I := I) g₀ g₁) j)
  rw [hf0]
  exact add_comm _ _

omit [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
lemma riemannianFiberNormSq_rsDomDomCongrSection_eq (g₀ : SmoothRiemannianMetric I M)
    (r s : ℕ) (σ : Equiv.Perm (Fin s)) (Z : SmoothCcTensor g₀ r s) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g₀ r s x
        ((rsDomDomCongrSection (I := I) (M := M) g₀ r s σ Z).toSection x) =
      riemannianFiberNormSq (I := I) (M := M) g₀ r s x (Z.toSection x) := by
  rw [rsDomDomCongrSection_toSection]
  exact riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ r s x σ _

end CurvatureCoefficientDifferenceJetTower

end ConnectionDifferenceCarrierSplit

end TopOrderSeparatedTransportMirrors

section TopOrderSeparatedRungRLD



namespace CurvatureCoefficientDifferenceJetTower

lemma sum_antidiagonalTupleGrid_le_boundedFactorGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    {W₀ K W : ℕ} (hK : W₀ ≤ K + 1) (hW : W₀ ≤ W) :
    ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k ≤
      Combinatorics.boundedFactorGridWindow b K W := by
  calc ∑ k ∈ Finset.range W₀, Combinatorics.antidiagonalTupleGrid b k
      = ∑ k ∈ Finset.range W₀, Combinatorics.boundedFactorGrid b K k :=
        Finset.sum_congr rfl (fun k hk =>
          Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
            (by rw [Finset.mem_range] at hk; omega))
    _ ≤ Combinatorics.boundedFactorGridWindow b K W := by
        rw [Combinatorics.boundedFactorGridWindow]
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.mpr hW) ?_
        intro k _ _
        exact Combinatorics.boundedFactorGrid_nonneg b hb K k

lemma connectionDifferenceResidualGridSum_le_boundedFactorGridWindow (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (j : ℕ) :
    ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1) ≤
      (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
  calc ∑ k ∈ Finset.range j, b (j - k) * Combinatorics.antidiagonalTupleGrid b (k + 1)
      ≤ ∑ _k ∈ Finset.range j, Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [Finset.mem_range] at hk
        rw [Combinatorics.antidiagonalTupleGrid_eq_boundedFactorGrid b
          (show k + 1 ≤ j from by omega)]
        refine le_trans (Combinatorics.single_factor_mul_boundedFactorGrid_le b hb
          (k + 1) (j - k) (by omega) (by omega)) ?_
        rw [show (k + 1) + (j - k) = j + 1 from by omega]
        exact Combinatorics.boundedFactorGrid_le_boundedFactorGridWindow b hb (by omega)
    _ = (j : ℝ) * Combinatorics.boundedFactorGridWindow b j (j + 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [SigmaCompactSpace M] in
theorem exists_quadraticConnectionDifferenceCc_iteratedCovGrad_riemannianFiberNormSq_le (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KQ : ℕ → ℝ, (∀ m, 0 ≤ KQ m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
          KQ m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 1) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => operatorFieldApplicationGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2)),
    fun m => mul_nonneg (operatorFieldApplicationGdiag_nonneg (E := E) m)
      (Finset.sum_nonneg (fun a _ => mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
        (mul_nonneg (Finset.sum_nonneg (fun l _ => hCA_nn l))
          (Combinatorics.windowPairCellCount_nonneg _ _)))), ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 1) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin := Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 1) (m + 3)
  have hquad : quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁ =
      ccOperatorFieldComp (I := I) (M := M) g₀ 1 2 3
        (armSlotEndoPassZeroCc (I := I) (M := M) g₀
          (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))
        (connectionDifferenceSection (I := I) g₁ g₀) := rfl
  rw [hquad]
  refine le_trans (riemannianFiberNormSq_iteratedCovGrad_operatorFieldComposition_diagonalProductGrid_rankLeft_le
    (I := I) (M := M) g₀ m 1 2 3
    (armSlotEndoPassZeroCc (I := I) (M := M) g₀
      (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))
    (connectionDifferenceSection (I := I) g₁ g₀) x) ?_
  have hterm : ∀ a ∈ Finset.range (m + 1),
      riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
          ((iteratedCovGrad (I := I) g₀ 2 3 a
            (armSlotEndoPassZeroCc (I := I) (M := M) g₀
              (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
        (∑ l ∈ Finset.range (m + 1 - a),
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
            ((iteratedCovGrad (I := I) g₀ 1 2 l
              (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)) ≤
      (((Module.finrank ℝ E : ℝ) * CA a) *
        ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by
    intro a ha
    rw [Finset.mem_range] at ha
    have hΦ : riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
        ((iteratedCovGrad (I := I) g₀ 2 3 a
          (armSlotEndoPassZeroCc (I := I) (M := M) g₀
            (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) ≤
        ((Module.finrank ℝ E : ℝ) * CA a) *
          Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) := by
      refine le_trans (riemannianFiberNormSq_iteratedCovGrad_armSlotPass_connectionDifferenceArm_le (I := I) (M := M)
        g₀ g₁ a x) ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound a x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn a)
      exact sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (by omega)
    have hW : (∑ l ∈ Finset.range (m + 1 - a),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
          ((iteratedCovGrad (I := I) g₀ 1 2 l
            (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)) ≤
        (∑ l ∈ Finset.range (m + 1 - a), CA l) *
          Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun l hl => ?_)
      rw [Finset.mem_range] at hl
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound l x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn l)
      exact sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (by omega)
    have hpair : Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
        Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2) ≤
        Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin := by
      refine le_trans (Combinatorics.boundedFactorGridWindow_mul_le b hb (m + 1)
        (a + 2) ((m - a) + 2) (by omega) (by omega)) ?_
      refine mul_le_mul_of_nonneg_left ?_ (Combinatorics.windowPairCellCount_nonneg _ _)
      rw [hWfin_def]
      refine Combinatorics.boundedFactorGridWindow_mono b hb (le_refl _) ?_
      omega
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          (∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connectionDifferenceSection (I := I) g₁ g₀)).toSection x))
        ≤ (((Module.finrank ℝ E : ℝ) * CA a) *
            Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2)) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by
          refine mul_le_mul hΦ hW (Finset.sum_nonneg (fun l _ =>
            riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + l) x _)) ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Combinatorics.boundedFactorGridWindow_nonneg b hb _ _)
      _ = (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.boundedFactorGridWindow b (m + 1) (a + 2) *
              Combinatorics.boundedFactorGridWindow b (m + 1) ((m - a) + 2)) := by ring
      _ ≤ (((Module.finrank ℝ E : ℝ) * CA a) * (∑ l ∈ Finset.range (m + 1 - a), CA l)) *
            (Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2) * Wfin) := by
          refine mul_le_mul_of_nonneg_left hpair ?_
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCA_nn a))
            (Finset.sum_nonneg (fun l _ => hCA_nn l))
      _ = (((Module.finrank ℝ E : ℝ) * CA a) *
            ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
              Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin := by ring
  change operatorFieldApplicationGdiag (E := E) m *
      (∑ a ∈ Finset.range (m + 1),
        riemannianFiberNormSq (I := I) (M := M) g₀ 2 (3 + a) x
            ((iteratedCovGrad (I := I) g₀ 2 3 a
              (armSlotEndoPassZeroCc (I := I) (M := M) g₀
                (connectionDifferenceArmFieldPt (I := I) (M := M) g₀ g₁))).toSection x) *
          ∑ l ∈ Finset.range (m + 1 - a),
            riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 1 2 l
                (connectionDifferenceSection (I := I) g₁ g₀)).toSection x)) ≤
    (operatorFieldApplicationGdiag (E := E) m *
      ∑ a ∈ Finset.range (m + 1),
        ((Module.finrank ℝ E : ℝ) * CA a) *
          ((∑ l ∈ Finset.range (m + 1 - a), CA l) *
            Combinatorics.windowPairCellCount (a + 2) ((m - a) + 2))) * Wfin
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left ?_ (operatorFieldApplicationGdiag_nonneg (E := E) m)
  exact Finset.sum_le_sum hterm

omit [SigmaCompactSpace M] in
theorem exists_palatiniConnectionDifferencePair_iteratedCovGrad_riemannianFiberNormSq_le (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ}
    (hδ₀ : δ₀ < 1) :
    ∃ KP : ℕ → ℝ, (∀ m, 0 ≤ KP m) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (m : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
            ((iteratedCovGrad (I := I) g₀ 1 3 m
              (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
                    quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) -
                rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3)
                  (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
                    quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁))).toSection x) ≤
          KP m * Combinatorics.boundedFactorGridWindow
            (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
              ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (m + 2) (m + 3) := by
  classical
  obtain ⟨CA, hCA_nn, hCA⟩ := exists_riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_tgrid
    (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := exists_quadraticConnectionDifferenceCc_iteratedCovGrad_riemannianFiberNormSq_le (I := I) (M := M) g₀ hδ₀
  refine ⟨fun m => 8 * (CA (m + 1) + KQ m),
    fun m => by have := hCA_nn (m + 1); have := hKQ_nn m; linarith, ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound m x
  set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
    ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
  have hb : ∀ l, 0 ≤ b l :=
    fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
      quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁ with hA_def
  set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (m + 2) (m + 3) with hWfin_def
  have hWfin_nn : 0 ≤ Wfin :=
    Combinatorics.boundedFactorGridWindow_nonneg b hb (m + 2) (m + 3)
  have hAjets : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
      ((iteratedCovGrad (I := I) g₀ 1 3 m A).toSection x) ≤
      (2 * CA (m + 1) + 2 * KQ m) * Wfin := by
    rw [hA_def, iteratedCovGrad_add]
    rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀)) +
        iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) =
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x +
        (iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x from by
      rw [SmoothCcTensor.toSection_add]; rfl]
    refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
    have hcd : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))).toSection x) ≤
        CA (m + 1) * Wfin := by
      rw [iteratedCovGrad_covGrad_eq_castCcTensorRank (I := I) (M := M) g₀ 1 2
        (connectionDifferenceSection (I := I) g₁ g₀) m]
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 1
        (by omega : 2 + (m + 1) = (2 + 1) + m)
        (iteratedCovGrad (I := I) g₀ 1 2 (m + 1) (connectionDifferenceSection (I := I) g₁ g₀)) x]
      refine le_trans (hCA g₁ T htie hδ_le hδ0 hbound (m + 1) x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hCA_nn (m + 1))
      exact sum_antidiagonalTupleGrid_le_boundedFactorGridWindow b hb (by omega) (by omega)
    have hq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + m) x
        ((iteratedCovGrad (I := I) g₀ 1 3 m
          (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) ≤
        KQ m * Wfin := by
      refine le_trans (hKQ g₁ T htie hδ_le hδ0 hbound m x) ?_
      refine mul_le_mul_of_nonneg_left ?_ (hKQ_nn m)
      rw [hWfin_def]
      exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (le_refl _)
    linarith [hcd, hq]
  rw [show ((iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
          rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
          (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
      (iteratedCovGrad (I := I) g₀ 1 3 m
        (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x from by
    rw [iteratedCovGrad_sub, SmoothCcTensor.toSection_sub]; rfl]
  refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + m) x _ _) ?_
  rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (Equiv.swap (1 : Fin 3) 2) A m x]
  rw [riemannianFiberNormSq_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 3
    (finRotate 3) A m x]
  linarith [hAjets]

end CurvatureCoefficientDifferenceJetTower

theorem riemannianFiberNormSq_iteratedCovGrad_riemannLoweredBackgroundDifference_topOrderSeparated_le
    (g₀ : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ Ktop : ℝ, 0 ≤ Ktop ∧ ∃ Kc : ℕ → ℝ, (∀ i, 0 ≤ Kc i) ∧
      ∀ (g₁ : SmoothRiemannianMetric I M) (T : SmoothCcTensor g₀ 0 2)
        (_htie : ∀ (y : M) (v w : TangentSpace I y),
          g₁.inner y v w = g₀.inner y v w + ccTensorBilinSymm (I := I) g₀ T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : gFibreOpBound (I := I) (M := M) g₀ (ccTensorBilinSymm (I := I) g₀ T) δ)
        (i : ℕ),
        ∃ Hd : SmoothCcTensor g₀ 0 (4 + i),
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x) ≤
              Ktop * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) ∧
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x
                ((iteratedCovGrad (I := I) g₀ 0 4 i
                    (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) -
                  Hd).toSection x) ≤
              Kc i * Combinatorics.boundedFactorGridWindow
                (fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x)) (i + 1) (i + 3)) := by
  classical
  obtain ⟨Kt0, hKt0_nn, Kc0, hKc0_nn, hbot⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_connectionDifferenceSection_topOrderSeparated_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KP, hKP_nn, hKP⟩ := exists_palatiniConnectionDifferencePair_iteratedCovGrad_riemannianFiberNormSq_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨KQ, hKQ_nn, hKQ⟩ := exists_quadraticConnectionDifferenceCc_iteratedCovGrad_riemannianFiberNormSq_le (I := I) (M := M) g₀ hδ₀
  obtain ⟨cg, hcg_nn, hcg⟩ := exists_backgroundJet_riemannianFiberNormSq_bound (I := I) (M := M) g₀ 0 2
    (riemannianMetricCcTensor (I := I) (M := M) g₀)
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  refine ⟨n * cg 0 * (4 * Kt0),
    mul_nonneg (mul_nonneg hn_nn (hcg_nn 0)) (mul_nonneg (by norm_num) hKt0_nn), ?_⟩
  refine ⟨fun i => 2 * (n * cg 0 *
      (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
      2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
        ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)),
    fun i => by
      have h1 : (0 : ℝ) ≤ Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ) :=
        mul_nonneg (hKc0_nn (i + 1)) (Nat.cast_nonneg _)
      have h2 : (0 : ℝ) ≤ KQ i := hKQ_nn i
      have h3 : (0 : ℝ) ≤ ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1) :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (mul_nonneg hn_nn (hKP_nn _)) (hcg_nn _))
      have h4 : (0 : ℝ) ≤ (i : ℝ) * operatorFieldApplicationGdiag (E := E) i :=
        mul_nonneg (Nat.cast_nonneg _) (operatorFieldApplicationGdiag_nonneg (E := E) i)
      have h5 : (0 : ℝ) ≤ n * cg 0 := mul_nonneg hn_nn (hcg_nn 0)
      linarith [mul_nonneg h4 h3, mul_nonneg h5 (by linarith : (0:ℝ) ≤ 4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))], ?_⟩
  intro g₁ T htie δ hδ_le hδ0 hbound i
  have hpal := riemannLoweredBackgroundDifference_palatini_repr (I := I) (M := M) g₀ g₁
  set A : SmoothCcTensor g₀ 1 3 :=
    covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀) +
      quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁ with hA_def
  set PA : SmoothCcTensor g₀ 1 3 :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A with hPA_def
  have hswap : lowerContravariantSlot (I := I) (M := M) g₀ 2 PA =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁) := by
    rw [← hpal]
    exact lowerContravariantSlot_cometricRaiseSlot0Field (I := I) (M := M) g₀ 2 _
  have hCD4 : riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁ =
      domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
        (lowerContravariantSlot (I := I) (M := M) g₀ 2 PA) := by
    rw [hswap, domDomCongrSection_comp, Equiv.swap_swap, domDomCongrSection_refl]
  set HeadCore : SmoothCcTensor g₀ 1 (2 + (i + 1)) :=
    ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
      (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
      (sharpFlatEndoCc (I := I) g₀ g₁) with hHeadCore_def
  set HA : SmoothCcTensor g₀ 1 (3 + i) :=
    castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i) HeadCore with hHA_def
  obtain ⟨τ₁, hτ₁⟩ := exists_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M)
    g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A i
  obtain ⟨τ₂, hτ₂⟩ := exists_iteratedCovGrad_rsDomDomCongrSection_eq (I := I) (M := M)
    g₀ 1 3 (finRotate 3) A i
  set HPA : SmoothCcTensor g₀ 1 (3 + i) :=
    rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
      rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA with hHPA_def
  obtain ⟨Hd, hHd⟩ := exists_lowerContravariantSlot_head_transport (I := I) (M := M) g₀
    (Equiv.swap (0 : Fin 4) 1) PA i HPA
  refine ⟨Hd, ?_, ?_⟩
  · intro x
    have h1 := (hHd x).1
    have hHPA_riemannianFiberNormSq : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        (HPA.toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          (HeadCore.toSection x) := by
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA x,
        riemannianFiberNormSq_rsDomDomCongrSection_eq (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA x]
      rw [hHA_def, riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) HeadCore x]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
        (HeadCore.toSection x)]
    have hHC := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).1
    rw [riemannianFiberNormSq_iteratedCovGrad_order_congr (I := I) (M := M) g₀ 0 2
      (show (i + 1) + 1 = i + 2 from by omega) T x] at hHC
    have hgW := hcg 0 x
    rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (riemannianMetricCcTensor (I := I) (M := M) g₀)) =
        riemannianMetricCcTensor (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
    have hb_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
      ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)
    have hHC_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
      (HeadCore.toSection x)
    have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
      ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x)
    have hHPA_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
      (HPA.toSection x)
    calc riemannianFiberNormSq (I := I) (M := M) g₀ 0 (4 + i) x (Hd.toSection x)
        ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x) := h1
      _ ≤ n * cg 0 *
          (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
          have hstep1 : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
              (HPA.toSection x) ≤
              4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x)) := by
            refine le_trans hHPA_riemannianFiberNormSq ?_
            linarith [hHC]
          have hng : 0 ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) :=
            mul_nonneg hn_nn hgW_nn
          calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
                riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x (HPA.toSection x)
              ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
                  ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) :=
                mul_le_mul_of_nonneg_left hstep1 hng
            _ ≤ n * cg 0 *
                (4 * (Kt0 * riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
                  ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x))) := by
                refine mul_le_mul_of_nonneg_right ?_ ?_
                · exact mul_le_mul_of_nonneg_left hgW hn_nn
                · exact mul_nonneg (by norm_num) (mul_nonneg hKt0_nn hb_nn)
      _ = n * cg 0 * (4 * Kt0) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (i + 2)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (i + 2) T).toSection x) := by ring
  · intro x
    have h2 := (hHd x).2
    set b : ℕ → ℝ := fun l => riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + l) x
      ((iteratedCovGrad (I := I) g₀ 0 2 l T).toSection x) with hb_def
    have hb : ∀ l, 0 ≤ b l :=
      fun l => riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + l) x _
    set Wfin : ℝ := Combinatorics.boundedFactorGridWindow b (i + 1) (i + 3) with hWfin_def
    have hWfin_nn : 0 ≤ Wfin :=
      Combinatorics.boundedFactorGridWindow_nonneg b hb (i + 1) (i + 3)
    rw [show (iteratedCovGrad (I := I) g₀ 0 4 i
          (riemannLoweredBackgroundDifference (I := I) (M := M) g₀ g₁)) =
        iteratedCovGrad (I := I) g₀ 0 4 i
          (domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 4) 1)
            (lowerContravariantSlot (I := I) (M := M) g₀ 2 PA)) from by rw [← hCD4]]
    refine le_trans h2 ?_
    have hAdiff : iteratedCovGrad (I := I) g₀ 1 3 i A - HA =
        castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
          (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connectionDifferenceSection (I := I) g₁ g₀) -
            HeadCore) +
        iteratedCovGrad (I := I) g₀ 1 3 i (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁) := by
      rw [hA_def, iteratedCovGrad_add]
      rw [show (iteratedCovGrad (I := I) g₀ 1 3 i
            (covGrad (I := I) (M := M) g₀ 1 2 (connectionDifferenceSection (I := I) g₁ g₀))) =
          castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connectionDifferenceSection (I := I) g₁ g₀))
          from iteratedCovGrad_covGrad_eq_castCcTensorRank (I := I) (M := M) g₀ 1 2
            (connectionDifferenceSection (I := I) g₁ g₀) i]
      rw [hHA_def]
      rw [castCcTensorRank_sub (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i)]
      exact add_sub_right_comm _ _ _
    have hdiff_pt : ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x :
        Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace (3 + i) I x) =
        rsDomDomCongr (I := I) (M := M) τ₁
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) -
          rsDomDomCongr (I := I) (M := M) τ₂
            ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i PA).toSection x - HPA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hPA_def, iteratedCovGrad_sub]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (Equiv.swap (1 : Fin 3) 2) A) -
          iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3
              (Equiv.swap (1 : Fin 3) 2) A)).toSection x -
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 3 (finRotate 3) A)).toSection x
          from by rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [hτ₁ x, hτ₂ x]
      rw [hHPA_def]
      rw [show ((rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA -
            rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x) =
          (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₁ HA).toSection x -
            (rsDomDomCongrSection (I := I) (M := M) g₀ 1 (3 + i) τ₂ HA).toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [rsDomDomCongrSection_toSection, rsDomDomCongrSection_toSection]
      rw [show ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) =
          (iteratedCovGrad (I := I) g₀ 1 3 i A).toSection x - HA.toSection x from by
        rw [SmoothCcTensor.toSection_sub]; rfl]
      rw [tensorRS_domDomCongr_sub (I := I) (M := M) τ₁, tensorRS_domDomCongr_sub (I := I) (M := M) τ₂]
      abel
    have hPAHPA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i PA - HPA).toSection x) ≤
        4 * riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) := by
      rw [hdiff_pt]
      refine le_trans (riemannianFiberNormSq_sub_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₁ _,
        riemannianFiberNormSq_domDomCongr_covariant (I := I) (M := M) g₀ 1 (3 + i) x τ₂ _]
      linarith [riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
    have hAHA : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + i) x
        ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x) ≤
        2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin := by
      rw [hAdiff]
      rw [show ((castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connectionDifferenceSection (I := I) g₁ g₀) -
              HeadCore) +
          iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x) =
          (castCcTensorRank g₀ 1 (by omega : 2 + (i + 1) = 3 + i)
            (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connectionDifferenceSection (I := I) g₁ g₀) -
              HeadCore)).toSection x +
          (iteratedCovGrad (I := I) g₀ 1 3 i
            (quadraticConnectionDifferenceCc (I := I) (M := M) g₀ g₁)).toSection x from by
        rw [SmoothCcTensor.toSection_add]; rfl]
      refine le_trans (riemannianFiberNormSq_add_le (I := I) (M := M) g₀ 1 (3 + i) x _ _) ?_
      rw [riemannianFiberNormSq_castCcTensorRank_eq (I := I) (M := M) g₀ 1
        (by omega : 2 + (i + 1) = 3 + i) _ x]
      have hres := (hbot g₁ T htie hδ_le hδ0 hbound (i + 1) x).2
      rw [hHeadCore_def]
      have hresW : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (2 + (i + 1)) x
          ((iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (connectionDifferenceSection (I := I) g₁ g₀) -
            ccOperatorFieldComp (I := I) (M := M) g₀ 1 1 (2 + (i + 1))
              (iteratedCovGrad (I := I) g₀ 1 2 (i + 1) (raisedKoszul (I := I) g₀ g₁))
              (sharpFlatEndoCc (I := I) g₀ g₁)).toSection x) ≤
          Kc0 (i + 1) * (((i + 1 : ℕ) : ℝ) * Wfin) := by
        refine le_trans hres ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKc0_nn (i + 1))
        refine le_trans (connectionDifferenceResidualGridSum_le_boundedFactorGridWindow b hb (i + 1)) ?_
        rw [show (i + 1) + 2 = i + 3 from by omega]
      have hqW := hKQ g₁ T htie hδ_le hδ0 hbound i x
      linarith [hresW, hqW, hWfin_nn, hKc0_nn (i + 1), hKQ_nn i]
    have hcorr : ∀ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x) ≤
        ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hPAj : riemannianFiberNormSq (I := I) (M := M) g₀ 1 (3 + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x) ≤
          KP (i - (k + 1)) * Wfin := by
        rw [hPA_def, hA_def]
        refine le_trans (hKP g₁ T htie hδ_le hδ0 hbound (i - (k + 1)) x) ?_
        refine mul_le_mul_of_nonneg_left ?_ (hKP_nn (i - (k + 1)))
        rw [hWfin_def]
        exact Combinatorics.boundedFactorGridWindow_mono b hb (by omega) (by omega)
      have hgj := hcg (k + 1) x
      have hPAj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1
        (3 + (i - (k + 1))) x
        ((iteratedCovGrad (I := I) g₀ 1 3 (i - (k + 1)) PA).toSection x)
      have hgj_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
        ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
          (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x)
      calc (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
            ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
              (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x)
          ≤ (n * (KP (i - (k + 1)) * Wfin)) * cg (k + 1) := by
            refine mul_le_mul ?_ hgj hgj_nn ?_
            · exact mul_le_mul_of_nonneg_left hPAj hn_nn
            · exact mul_nonneg hn_nn (mul_nonneg (hKP_nn _) hWfin_nn)
        _ = ((n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by ring
    have hterm2 : (∑ k ∈ Finset.range i,
        (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
          ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
            (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x)) ≤
        (∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum hcorr
    have hterm1 : n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
          ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
        n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
          2 * KQ i * Wfin)) := by
      have hgW := hcg 0 x
      rw [show (iteratedCovGrad (I := I) g₀ 0 2 0 (riemannianMetricCcTensor (I := I) (M := M) g₀)) =
          riemannianMetricCcTensor (I := I) (M := M) g₀ from iteratedCovGrad_zero (I := I) g₀ 0 2 _] at hgW
      have hd_le : riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
          ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x) ≤
          4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin) := by
        refine le_trans hPAHPA ?_
        linarith [hAHA, riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 (3 + i) x
          ((iteratedCovGrad (I := I) g₀ 1 3 i A - HA).toSection x)]
      have hgW_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 2 x
        ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x)
      have hd_nn := riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
        ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
      calc n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)
          ≤ n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
              ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin + 2 * KQ i * Wfin)) :=
            mul_le_mul_of_nonneg_left hd_le (mul_nonneg hn_nn hgW_nn)
        _ ≤ n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin)) := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hgW hn_nn) ?_
            have h1 : (0 : ℝ) ≤ 2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num)
                (mul_nonneg (hKc0_nn _) (Nat.cast_nonneg _))) hWfin_nn
            have h2 : (0 : ℝ) ≤ 2 * KQ i * Wfin :=
              mul_nonneg (mul_nonneg (by norm_num) (hKQ_nn i)) hWfin_nn
            linarith
    calc 2 * (n * riemannianFiberNormSq (I := I) (M := M) g₀ 0 2 x
            ((riemannianMetricCcTensor (I := I) (M := M) g₀).toSection x) *
          riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + i) x
            ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) i PA - HPA).toSection x)) +
        2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
          ∑ k ∈ Finset.range i,
            (n * riemannianFiberNormSq (I := I) (M := M) g₀ 1 ((2 + 1) + (i - (k + 1))) x
              ((iteratedCovGrad (I := I) g₀ 1 (2 + 1) (i - (k + 1)) PA).toSection x)) *
            riemannianFiberNormSq (I := I) (M := M) g₀ 0 (2 + (k + 1)) x
              ((iteratedCovGrad (I := I) g₀ 0 2 (k + 1)
                (riemannianMetricCcTensor (I := I) (M := M) g₀)).toSection x))
        ≤ 2 * (n * cg 0 * (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) * Wfin +
            2 * KQ i * Wfin))) +
          2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ((∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1)) * Wfin)) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num)) ?_
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hterm2
            (mul_nonneg (Nat.cast_nonneg _) (operatorFieldApplicationGdiag_nonneg (E := E) i))
      _ = (2 * (n * cg 0 *
            (4 * (2 * (Kc0 (i + 1) * ((i + 1 : ℕ) : ℝ)) + 2 * KQ i))) +
          2 * ((i : ℝ) * operatorFieldApplicationGdiag (E := E) i *
            ∑ k ∈ Finset.range i, (n * KP (i - (k + 1))) * cg (k + 1))) * Wfin := by
          ring

end TopOrderSeparatedRungRLD

end Spectral
end Analysis
end DifferentialGeometry

end
