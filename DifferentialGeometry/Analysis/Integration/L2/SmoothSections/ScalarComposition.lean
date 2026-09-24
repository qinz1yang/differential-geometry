import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.Defs
import DifferentialGeometry.Tensor.RSTensor.RankZero
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {g : SmoothRiemannianMetric I M}
variable {ι : Type*} [Fintype ι]

private theorem contMDiff_scalar_compOn
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun x => F (fun i => TensorRSField.scalar0 (u i).toSection x)) := by
  exact hF.contMDiffOn.comp_contMDiff
    (contMDiff_pi_space.mpr (fun i => TensorRSField.scalar0_smooth (u i).toSection)) hu

noncomputable def scalarCompOn [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    SmoothCcTensor g 0 0 where
  toSection := (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞)
    (fun x => F (fun i => TensorRSField.scalar0 (u i).toSection x))
    (contMDiff_scalar_compOn u F hF hu)).toTensorRSField ∞
  hasCompactSupport :=
    IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)

@[simp] theorem scalar0_scalarCompOn [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    TensorRSField.scalar0 (scalarCompOn u F hF hu).toSection =
      fun x => F (fun i => TensorRSField.scalar0 (u i).toSection x) := by
  unfold scalarCompOn TensorRSField.scalar0
  rw [TensorRSField.rs0_toRS0]
  exact Tensor0SField.toScalarField_fromScalarField _ _ _

noncomputable def scalarComp [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) : SmoothCcTensor g 0 0 :=
  scalarCompOn u F hF.contDiffOn (fun _ => Set.mem_univ _)

@[simp] theorem scalar0_scalarComp [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) :
    TensorRSField.scalar0 (scalarComp u F hF).toSection =
      fun x => F (fun i => TensorRSField.scalar0 (u i).toSection x) :=
  scalar0_scalarCompOn u F hF.contDiffOn (fun _ => Set.mem_univ _)

theorem ext_scalar0 {S T : SmoothCcTensor g 0 0}
    (h : TensorRSField.scalar0 S.toSection = TensorRSField.scalar0 T.toSection) : S = T := by
  apply SmoothCcTensor.ext
  calc
    S.toSection = (Tensor0SField.fromScalarField ∞
        (TensorRSField.scalar0 S.toSection)
        (TensorRSField.scalar0_smooth S.toSection)).toTensorRSField ∞ :=
      (TensorRSField.lift_scalar0 S.toSection).symm
    _ = (Tensor0SField.fromScalarField ∞
        (TensorRSField.scalar0 T.toSection)
        (TensorRSField.scalar0_smooth T.toSection)).toTensorRSField ∞ := by simp only [h]
    _ = T.toSection := TensorRSField.lift_scalar0 T.toSection

theorem scalarCompOn_add [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    scalarCompOn u (F + G) (hF.add hG) hu =
      scalarCompOn u F hF hu + scalarCompOn u G hG hu := by
  apply ext_scalar0
  rw [scalar0_scalarCompOn, toSection_add, TensorRSField.scalar0_add,
    scalar0_scalarCompOn, scalar0_scalarCompOn]
  rfl

theorem scalarCompOn_sub [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    scalarCompOn u (F - G) (hF.sub hG) hu =
      scalarCompOn u F hF hu - scalarCompOn u G hG hu := by
  apply ext_scalar0
  rw [scalar0_scalarCompOn, toSection_sub, TensorRSField.scalar0_sub,
    scalar0_scalarCompOn, scalar0_scalarCompOn]
  rfl

theorem scalarComp_add [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    scalarComp u (F + G) (hF.add hG) = scalarComp u F hF + scalarComp u G hG :=
  scalarCompOn_add u F G hF.contDiffOn hG.contDiffOn (fun _ => Set.mem_univ _)

theorem scalarComp_sub [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : (ι → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    scalarComp u (F - G) (hF.sub hG) = scalarComp u F hF - scalarComp u G hG :=
  scalarCompOn_sub u F G hF.contDiffOn hG.contDiffOn (fun _ => Set.mem_univ _)

@[simp] theorem scalarComp_apply [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (i : ι) :
    scalarComp u (fun v => v i) (contDiff_apply ℝ ℝ i) = u i := by
  apply ext_scalar0
  rw [scalar0_scalarComp]

@[simp] theorem scalarComp_zero [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) :
    scalarComp u (fun _ => 0) contDiff_const = 0 := by
  apply ext_scalar0
  rw [scalar0_scalarComp, toSection_zero, TensorRSField.scalar0_zero]
  rfl

theorem scalarCompOn_congr [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : (ι → ℝ) → ℝ)
    {U V : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G V)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U)
    (hv : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ V)
    (hFG : ∀ x, F (fun i => TensorRSField.scalar0 (u i).toSection x) =
      G (fun i => TensorRSField.scalar0 (u i).toSection x)) :
    scalarCompOn u F hF hu = scalarCompOn u G hG hv := by
  apply ext_scalar0
  rw [scalar0_scalarCompOn, scalar0_scalarCompOn]
  exact funext hFG

private theorem contMDiff_scalar_compParamOn
    (u : ι → SmoothCcTensor g 0 0) (F : M × (ι → ℝ) → ℝ)
    {U : Set (M × (ι → ℝ))}
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F U)
    (hu : ∀ x, (x, fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    ContMDiff I 𝓘(ℝ) ∞
      (fun x => F (x, fun i => TensorRSField.scalar0 (u i).toSection x)) := by
  exact hF.comp_contMDiff
    (contMDiff_id.prodMk
      (contMDiff_pi_space.mpr (fun i => TensorRSField.scalar0_smooth (u i).toSection))) hu

noncomputable def scalarCompParamOn [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : M × (ι → ℝ) → ℝ)
    {U : Set (M × (ι → ℝ))}
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F U)
    (hu : ∀ x, (x, fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    SmoothCcTensor g 0 0 where
  toSection := (Tensor0SField.fromScalarField (∞ : WithTop ℕ∞)
    (fun x => F (x, fun i => TensorRSField.scalar0 (u i).toSection x))
    (contMDiff_scalar_compParamOn u F hF hu)).toTensorRSField ∞
  hasCompactSupport :=
    IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _)

@[simp] theorem scalar0_scalarCompParamOn [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : M × (ι → ℝ) → ℝ)
    {U : Set (M × (ι → ℝ))}
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F U)
    (hu : ∀ x, (x, fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    TensorRSField.scalar0 (scalarCompParamOn u F hF hu).toSection =
      fun x => F (x, fun i => TensorRSField.scalar0 (u i).toSection x) := by
  unfold scalarCompParamOn TensorRSField.scalar0
  rw [TensorRSField.rs0_toRS0]
  exact Tensor0SField.toScalarField_fromScalarField _ _ _

noncomputable def scalarCompParam [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : M × (ι → ℝ) → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F) : SmoothCcTensor g 0 0 :=
  scalarCompParamOn u F hF.contMDiffOn (fun _ => Set.mem_univ _)

@[simp] theorem scalar0_scalarCompParam [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : M × (ι → ℝ) → ℝ)
    (hF : ContMDiff (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F) :
    TensorRSField.scalar0 (scalarCompParam u F hF).toSection =
      fun x => F (x, fun i => TensorRSField.scalar0 (u i).toSection x) :=
  scalar0_scalarCompParamOn u F hF.contMDiffOn (fun _ => Set.mem_univ _)

theorem scalarCompParamOn_sub [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : M × (ι → ℝ) → ℝ)
    {U : Set (M × (ι → ℝ))}
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F U)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ G U)
    (hu : ∀ x, (x, fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    scalarCompParamOn u (F - G) (hF.sub hG) hu =
      scalarCompParamOn u F hF hu - scalarCompParamOn u G hG hu := by
  apply ext_scalar0
  rw [scalar0_scalarCompParamOn, toSection_sub, TensorRSField.scalar0_sub,
    scalar0_scalarCompParamOn, scalar0_scalarCompParamOn]
  rfl

theorem scalarCompParamOn_add [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F G : M × (ι → ℝ) → ℝ)
    {U : Set (M × (ι → ℝ))}
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ F U)
    (hG : ContMDiffOn (I.prod 𝓘(ℝ, ι → ℝ)) 𝓘(ℝ) ∞ G U)
    (hu : ∀ x, (x, fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    scalarCompParamOn u (F + G) (hF.add hG) hu =
      scalarCompParamOn u F hF hu + scalarCompParamOn u G hG hu := by
  apply ext_scalar0
  rw [scalar0_scalarCompParamOn, toSection_add, TensorRSField.scalar0_add,
    scalar0_scalarCompParamOn, scalar0_scalarCompParamOn]
  rfl

@[simp] theorem scalarCompParamOn_snd [CompactSpace M]
    (u : ι → SmoothCcTensor g 0 0) (F : (ι → ℝ) → ℝ)
    {U : Set (ι → ℝ)} (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ x, (fun i => TensorRSField.scalar0 (u i).toSection x) ∈ U) :
    scalarCompParamOn u (F ∘ Prod.snd)
      (hF.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hp => hp)) hu =
      scalarCompOn u F hF hu := by
  apply ext_scalar0
  rw [scalar0_scalarCompParamOn, scalar0_scalarCompOn]
  rfl

end DifferentialGeometry.Integral.L2.SmoothCcTensor
