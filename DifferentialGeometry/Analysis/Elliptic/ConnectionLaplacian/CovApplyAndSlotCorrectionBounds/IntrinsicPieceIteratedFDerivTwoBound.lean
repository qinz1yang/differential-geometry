import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.IntrinsicPieceFderivBound
import DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.CovApplyAndSlotCorrectionBounds.SlotCorrectionChartFderivBound
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

private local instance intrinsicPieceTwoTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance intrinsicPieceTwoTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

private lemma choose_two_product_sum (p q : ℕ → ℝ) :
    ∑ i ∈ Finset.range (2 + 1),
        ↑((2 : ℕ).choose i) * p i * q (2 - i) =
      p 0 * q 2 + 2 * p 1 * q 1 + p 2 * q 0 := by
  norm_num [Finset.sum_range_succ]

private lemma three_product_sum_le
    {C A1 A2 A3 B0 B1 B2 : ℝ}
    (hC : 0 ≤ C) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3)
    (hB0 : B0 ≤ C) (hB1 : B1 ≤ C) (hB2 : B2 ≤ C) :
    A1 * B2 + 2 * A2 * B1 + A3 * B0 ≤
      2 * C * (A3 + A2 + A1) := by
  have h1 := mul_le_mul_of_nonneg_left hB2 hA1
  have h2 := mul_le_mul_of_nonneg_left hB1 hA2
  have h3 := mul_le_mul_of_nonneg_left hB0 hA3
  have hA1C : 0 ≤ A1 * C := mul_nonneg hA1 hC
  have hA3C : 0 ≤ A3 * C := mul_nonneg hA3 hC
  nlinarith

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_two_fderiv_apply_norm_le
    {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (F : E → N) (u : E → E) (U : Set E) (x : E)
    (hF : ContDiffOn ℝ ∞ F U) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ 2 (fun y : E => (fderiv ℝ F y) (u y)) x‖ ≤
      ‖fderiv ℝ F x‖ * ‖iteratedFDeriv ℝ 2 u x‖ +
        2 * ‖iteratedFDeriv ℝ 2 F x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
        ‖iteratedFDeriv ℝ 3 F x‖ * ‖iteratedFDeriv ℝ 0 u x‖ := by
  have h_top : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by
    rw [ENat.coe_top_add_one]
  have hc : ContDiffOn ℝ ∞ (fderiv ℝ F) U :=
    hF.fderiv_of_isOpen hU h_top
  have h_leibniz_within :
      ‖iteratedFDerivWithin ℝ 2 (fun y : E => (fderiv ℝ F y) (u y)) U x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDerivWithin ℝ i (fderiv ℝ F) U x‖ *
            ‖iteratedFDerivWithin ℝ (2 - i) u U x‖ :=
    norm_iteratedFDerivWithin_clm_apply hc hu hU.uniqueDiffOn hx
      (by
        show ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)
  have h_leibniz_global :
      ‖iteratedFDeriv ℝ 2 (fun y : E => (fderiv ℝ F y) (u y)) x‖ ≤
        ∑ i ∈ Finset.range (2 + 1),
          ↑((2 : ℕ).choose i) *
            ‖iteratedFDeriv ℝ i (fderiv ℝ F) x‖ *
            ‖iteratedFDeriv ℝ (2 - i) u x‖ := by
    rw [← iteratedFDerivWithin_of_isOpen 2 hU hx]
    refine le_trans h_leibniz_within ?_
    apply Finset.sum_le_sum
    intro i _
    rw [iteratedFDerivWithin_of_isOpen i hU hx,
      iteratedFDerivWithin_of_isOpen (2 - i) hU hx]
  rw [choose_two_product_sum
    (fun i => ‖iteratedFDeriv ℝ i (fderiv ℝ F) x‖)
    (fun i => ‖iteratedFDeriv ℝ i u x‖)] at h_leibniz_global
  rw [norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 0),
    norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 1),
    norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := x) (n := 2),
    norm_iteratedFDeriv_one (𝕜 := ℝ) F (x := x)] at h_leibniz_global
  exact h_leibniz_global

omit [CompactSpace M] [T2Space M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma c_contDiffOn_goodSet
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : SmoothCcTensor g r s) :
    ContDiffOn ℝ ∞
      (fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm))
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  have hF_cd : ContDiffOn ℝ ∞
      (tensorRSChartE_section_repr (I := I) r s α
          (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hU_open : IsOpen
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) :=
    chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have h_le : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by rw [ENat.coe_top_add_one]
  exact hF_cd.fderiv_of_isOpen hU_open h_le

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma u_contDiffOn_goodSet'
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
private lemma pouTsupport_subset_goodSet' [SigmaCompactSpace M] (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      chartLeviCivitaGoodSet (I := I) α := by
  intro b hb
  have h_eq :=
    DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source
    (I := I) α
  rw [h_eq, extChartAt_source_eq_chartAt_source (I := I)]
  exact (chartAtlasPOU_isSubordinate I M) α hb

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_u_continuousOn
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (k : ℕ) :
    ContinuousOn
      (fun y : E => ‖iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) y‖)
      ((extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hu_cd : ContDiffOn ℝ ∞
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    u_contDiffOn_goodSet' (I := I) α B
  have hk_le : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by
    show ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    have h1 : ((k : ℕ) : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
    exact (WithTop.coe_le_coe.mpr h1 : _)
  have hcd_k : ContDiffOn ℝ k
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U :=
    hu_cd.of_le hk_le
  have h_within_cont : ContinuousOn
      (iteratedFDerivWithin ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U) U :=
    hcd_k.continuousOn_iteratedFDerivWithin (m := k) (le_refl _)
      (hU_open.uniqueDiffOn)
  have h_eq : EqOn
      (iteratedFDerivWithin ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm) U)
      (iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)) U :=
    iteratedFDerivWithin_of_isOpen k hU_open
  have h_iter_cont : ContinuousOn
      (iteratedFDeriv ℝ k
        (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)) U := by
    refine h_within_cont.congr ?_
    intro y hy
    exact (h_eq hy).symm
  exact continuous_norm.comp_continuousOn h_iter_cont

omit [NeZero (Module.finrank ℝ E)] in
private lemma iteratedFDeriv_u_bound_012
    (α : M) (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x),
        ‖iteratedFDeriv ℝ 0
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 1
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C ∧
        ‖iteratedFDeriv ℝ 2
          (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
          (extChartAt I α b)‖ ≤ C := by
  classical
  set K_set : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hK_set_def
  have hK_compact : IsCompact K_set :=
    pouTsupport_isCompact (I := I) (M := M) α
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hφ_cm : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I α) (chartAt H α).source :=
    contMDiffOn_extChartAt (I := I) (n := ∞) (x := α)
  have hK_sub : K_set ⊆ (chartAt H α).source :=
    (chartAtlasPOU_isSubordinate I M) α
  have hK_sub_good : K_set ⊆ chartLeviCivitaGoodSet (I := I) α :=
    pouTsupport_subset_goodSet' (I := I) α
  have hmaps : Set.MapsTo (extChartAt I α) K_set U :=
    fun b hb => ⟨b, hK_sub_good hb, rfl⟩
  have hφ_cont : ContinuousOn (extChartAt I α) K_set :=
    (hφ_cm.continuousOn).mono hK_sub
  have h_cont_0 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 0
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 0).comp
      hφ_cont hmaps
  have h_cont_1 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 1
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 1).comp
      hφ_cont hmaps
  have h_cont_2 : ContinuousOn (fun b : M => ‖iteratedFDeriv ℝ 2
      (chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm)
      (extChartAt I α b)‖) K_set :=
    (iteratedFDeriv_u_continuousOn (I := I) α B 2).comp
      hφ_cont hmaps
  obtain ⟨C0, hC0_mem⟩ := hK_compact.bddAbove_image h_cont_0
  obtain ⟨C1, hC1_mem⟩ := hK_compact.bddAbove_image h_cont_1
  obtain ⟨C2, hC2_mem⟩ := hK_compact.bddAbove_image h_cont_2
  refine ⟨max (max (max C0 C1) C2) 0, le_max_right _ _, ?_⟩
  intro b hb
  refine ⟨?_, ?_, ?_⟩
  · have h := hC0_mem ⟨b, hb, rfl⟩
    calc _ ≤ C0 := h
      _ ≤ max C0 C1 := le_max_left _ _
      _ ≤ max (max C0 C1) C2 := le_max_left _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _
  · have h := hC1_mem ⟨b, hb, rfl⟩
    calc _ ≤ C1 := h
      _ ≤ max C0 C1 := le_max_right _ _
      _ ≤ max (max C0 C1) C2 := le_max_left _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _
  · have h := hC2_mem ⟨b, hb, rfl⟩
    calc _ ≤ C2 := h
      _ ≤ max (max C0 C1) C2 := le_max_right _ _
      _ ≤ max (max (max C0 C1) C2) 0 := le_max_left _ _

omit [NeZero (Module.finrank ℝ E)] in
theorem intrinsic_piece_iteratedFDeriv_two_bound
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (B : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (T : SmoothCcTensor g r s),
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α →
        ‖iteratedFDeriv ℝ 2
          (fun y : E =>
            fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
                (fun y' : M => T.toSection y')
                ∘ (extChartAt I α).symm) y
              (trivToE (I := I) α ((extChartAt I α).symm y)
                (B.toFun ((extChartAt I α).symm y))))
          (extChartAt I α b)‖ ≤
        K * (‖iteratedFDeriv ℝ 3 (tensorRSChartE_section_repr (I := I) r s α
                (fun y : M => T.toSection y) ∘ (extChartAt I α).symm)
                (extChartAt I α b)‖ +
             ‖iteratedFDeriv ℝ 2 (tensorRSChartE_section_repr (I := I) r s α
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
  obtain ⟨C, hC_nn, hC_bound⟩ := iteratedFDeriv_u_bound_012 (I := I) (M := M) α B
  refine ⟨2 * C, by positivity, ?_⟩
  intro T b hb
  set F : E → TensorRSModel r s ℝ E :=
    tensorRSChartE_section_repr (I := I) r s α
      (fun y : M => T.toSection y) ∘ (extChartAt I α).symm with hF_def
  set u : E → E :=
    chartE_section_repr (I := I) α B.toFun ∘ (extChartAt I α).symm with hu_def
  set x : E := extChartAt I α b with hx_def
  set U : Set E := (extChartAt I α) '' chartLeviCivitaGoodSet (I := I) α
    with hU_def
  have hU_open : IsOpen U := chartLeviCivitaGoodSet_image_isOpen (I := I) α
  have hF_cd : ContDiffOn ℝ ∞ F U :=
    R_contDiffOn_goodSet (I := I) (M := M) g r s α T
  have hu_cd : ContDiffOn ℝ ∞ u U := u_contDiffOn_goodSet' (I := I) α B
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := hb.2
  have hx_mem : x ∈ U := ⟨b, hb_good, rfl⟩
  have h_leibniz_global :
      ‖iteratedFDeriv ℝ 2
          (fun y : E => (fderiv ℝ F y) (u y)) x‖ ≤
        ‖fderiv ℝ F x‖ * ‖iteratedFDeriv ℝ 2 u x‖ +
          2 * ‖iteratedFDeriv ℝ 2 F x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
          ‖iteratedFDeriv ℝ 3 F x‖ * ‖iteratedFDeriv ℝ 0 u x‖ :=
    iteratedFDeriv_two_fderiv_apply_norm_le F u U x hF_cd hu_cd hU_open hx_mem
  have h_goalLHS_fn : (fun y : E =>
        fderiv ℝ (tensorRSChartE_section_repr (I := I) r s α
            (fun y' : M => T.toSection y') ∘ (extChartAt I α).symm) y
          (trivToE (I := I) α ((extChartAt I α).symm y)
            (B.toFun ((extChartAt I α).symm y)))) =
      (fun y : E => (fderiv ℝ F y) (u y)) := by
    funext y
    rfl
  rw [h_goalLHS_fn]
  obtain ⟨hu0_le, hu1_le, hu2_le⟩ := hC_bound b hb.1
  have h_final_le :
      ‖fderiv ℝ F x‖ * ‖iteratedFDeriv ℝ 2 u x‖ +
          2 * ‖iteratedFDeriv ℝ 2 F x‖ * ‖iteratedFDeriv ℝ 1 u x‖ +
          ‖iteratedFDeriv ℝ 3 F x‖ * ‖iteratedFDeriv ℝ 0 u x‖ ≤
        2 * C * (‖iteratedFDeriv ℝ 3 F x‖ +
          ‖iteratedFDeriv ℝ 2 F x‖ + ‖fderiv ℝ F x‖) :=
    three_product_sum_le hC_nn (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hu0_le hu1_le hu2_le
  exact le_trans h_leibniz_global h_final_le

end Elliptic
end Analysis
end DifferentialGeometry

end
