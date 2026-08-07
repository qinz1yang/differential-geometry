import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartReprDerivativeBounds.ChartPulledCovDerivChartCompBound
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance intrinsicPieceTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance intrinsicPieceTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma norm_fderiv_fderiv_eq_iteratedFDeriv_two
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (F : E → N) (x : E) :
    ‖fderiv ℝ (fderiv ℝ F) x‖ = ‖iteratedFDeriv ℝ 2 F x‖ := by
  have h1 : ‖fderiv ℝ (fderiv ℝ F) x‖
      = ‖iteratedFDeriv ℝ 1 (fderiv ℝ F) x‖ :=
    (norm_iteratedFDeriv_one (𝕜 := ℝ) (fderiv ℝ F) (x := x)).symm
  have h2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ F) x‖
      = ‖iteratedFDeriv ℝ 2 F x‖ :=
    norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 1)
  rw [h1, h2]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma fderiv_fderiv_apply_norm_le
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (F : E → N) (u : E → E) (x : E)
    (hF : DifferentiableAt ℝ (fderiv ℝ F) x)
    (hu : DifferentiableAt ℝ u x) :
    ‖fderiv ℝ (fun y : E => (fderiv ℝ F y) (u y)) x‖ ≤
      ‖fderiv ℝ F x‖ * ‖fderiv ℝ u x‖ +
        ‖iteratedFDeriv ℝ 2 F x‖ * ‖u x‖ := by
  rw [fderiv_clm_apply hF hu]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(fderiv ℝ F x).comp (fderiv ℝ u x)‖ ≤
      ‖fderiv ℝ F x‖ * ‖fderiv ℝ u x‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have h2 : ‖(fderiv ℝ (fderiv ℝ F) x).flip (u x)‖ ≤
      ‖iteratedFDeriv ℝ 2 F x‖ * ‖u x‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ (u x)) ?_
    rw [ContinuousLinearMap.opNorm_flip,
      norm_fderiv_fderiv_eq_iteratedFDeriv_two (F := F) (x := x)]
  exact add_le_add h1 h2

private lemma two_product_sum_le
    {C a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : p ≤ C) (hq : q ≤ C) :
    b * p + a * q ≤ C * (a + b) := by
  calc
    b * p + a * q ≤ b * C + a * C :=
      add_le_add (mul_le_mul_of_nonneg_left hp hb)
        (mul_le_mul_of_nonneg_left hq ha)
    _ = C * (a + b) := by ring

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma u_contDiffOn_goodSet
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hB_total : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x : M => TotalSpace.mk' E
        (E := fun y : M => TangentSpace I y) x (B.toFun x)) := B.contMDiff
  have hB_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (B.toFun : Π x : M, TangentSpace I x))
      (chartLeviCivitaGoodSet (I := I) α) := hB_total.contMDiffOn
  exact chartE_pullback_contDiffOn_goodSet (I := I) α hB_on

omit [NeZero (Module.finrank ℝ E)] in
private lemma pouTsupport_subset_goodSet [SigmaCompactSpace M] (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have h_eq :=
    DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
    (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M) α hb

omit [NeZero (Module.finrank ℝ E)] in
private lemma u_and_fderiv_u_bound
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖fderiv ℝ
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C ∧
        ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    u_contDiffOn_goodSet (I := I) α B
  have hfd_cd : ContDiffOn ℝ ∞
      (fderiv ℝ (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
    have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
    exact hu_cd.fderiv_of_isOpen hU_open h_le
  have hcont_u : ContinuousOn (fun y : E =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    continuous_norm.comp_continuousOn hu_cd.continuousOn
  have hcont_fd : ContinuousOn (fun y : E =>
      ‖fderiv ℝ (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    continuous_norm.comp_continuousOn hfd_cd.continuousOn
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have hcont_u_M : ContinuousOn (fun b : M =>
      ‖(chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖) K_set :=
    hcont_u.comp hφ_cont hmaps
  have hcont_fd_M : ContinuousOn (fun b : M =>
      ‖fderiv ℝ
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
        (extChartAt I α b)‖) K_set :=
    hcont_fd.comp hφ_cont hmaps
  obtain ⟨Cu, hCu_mem⟩ := hK_compact.bddAbove_image hcont_u_M
  obtain ⟨Cfd, hCfd_mem⟩ := hK_compact.bddAbove_image hcont_fd_M
  refine ⟨max (max Cu Cfd) 0, le_max_right _ _, ?_⟩
  intro b hb
  refine ⟨?_, ?_⟩
  · have h1 := hCfd_mem ⟨b, hb, rfl⟩
    exact le_trans (le_trans h1 (le_max_right _ _)) (le_max_left _ _)
  · have h1 := hCu_mem ⟨b, hb, rfl⟩
    exact le_trans (le_trans h1 (le_max_left _ _)) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] in
theorem intrinsic_piece_fderiv_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
        DifferentiableAt ℝ
          (fderiv ℝ
            (tensorRSChartE_section_repr (I := I) r s α
              (fun y : M => T.toSection y)
              ∘ (extChartAt I α).symm))
          (extChartAt I α b) →
        ‖fderiv ℝ
          (fun y : E =>
            fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y')
                ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)‖ ≤
        K * (‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖) := by
  classical
  letI _h_top : TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x)) :=
    tensorRSBundle_topology r s
  letI _h_fib : FiberBundle (TensorRSModel r s ℝ E)
      (fun x : M => TensorRSSpace r s I x) :=
    tensorRSBundle_fiber r s
  obtain ⟨C, hC_nn, hC_bound⟩ := u_and_fderiv_u_bound (I := I) (M := M) α B
  refine ⟨C, hC_nn, ?_⟩
  intro T b hb hF2_diff
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def
  set u : E → E :=
    chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm with hu_def
  set x : E := extChartAt I α b with hx_def
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  have hx_mem :
      x ∈ (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α :=
    ⟨b, hb_good, rfl⟩
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hu_cd : ContDiffOn ℝ ∞ u
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    u_contDiffOn_goodSet (I := I) α B
  have hu_diff : DifferentiableAt ℝ u x := by
    have hne : (∞ : WithTop ℕ∞) ≠ 0 := by
      intro h
      exact absurd h (by simp)
    exact ((hu_cd.differentiableOn hne) x hx_mem).differentiableAt
      (hU_open.mem_nhds hx_mem)
  have h_goalLHS_fn : (fun y : E =>
        fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y)))) =
      (fun y : E => (fderiv ℝ F y) (u y)) := by
    funext y; rfl
  rw [h_goalLHS_fn]
  have h_norm_le :
      ‖fderiv ℝ (fun y : E => (fderiv ℝ F y) (u y)) x‖ ≤
        ‖fderiv ℝ F x‖ * ‖fderiv ℝ u x‖ +
          ‖iteratedFDeriv ℝ 2 F x‖ * ‖u x‖ :=
    fderiv_fderiv_apply_norm_le F u x hF2_diff hu_diff
  obtain ⟨hfd_le, hu_le⟩ := hC_bound b hb.1
  have h_final :
      ‖fderiv ℝ F x‖ * ‖fderiv ℝ u x‖ +
        ‖iteratedFDeriv ℝ 2 F x‖ * ‖u x‖ ≤
        C * (‖iteratedFDeriv ℝ 2 F x‖ + ‖fderiv ℝ F x‖) :=
    two_product_sum_le (norm_nonneg _) (norm_nonneg _) hfd_le hu_le
  exact le_trans h_norm_le h_final

end Elliptic
end Analysis
end DifferentialGeometry

end
