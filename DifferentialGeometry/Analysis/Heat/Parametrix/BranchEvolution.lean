import DifferentialGeometry.Analysis.Heat.Parametrix.BranchCutoff
import DifferentialGeometry.Analysis.Parabolic.ScalarTimeDependent
import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Operator.LaplacianRegularity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem contMDiffOn_heatParametrix_joint
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => B.heatParametrix N z.1 z.2)
      (Ioi 0 ×ˢ (B.dom ∩ B.inv ⁻¹' U)) := by
  intro z hz
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_inf.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have he := (contMDiffOn_branchEnergy B).contMDiffAt (B.hom.open_target.mem_nhds hz.2.1)
  have ha (k : ℕ) := (B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k).contMDiffAt
    (hV.mem_nhds hz.2)
  have harg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × M => 4 * Real.pi * w.1) z := contMDiffAt_const.mul contMDiffAt_fst
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × M => (4 * Real.pi * w.1) ^ (-(Module.finrank ℝ E : ℝ) / 2)) z := by
    have hn : 4 * Real.pi * z.1 ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hz.1.ne'
    exact (Real.contDiffAt_rpow_const_of_ne (n := ∞)
      (p := -(Module.finrank ℝ E : ℝ) / 2) hn).contMDiffAt.comp z harg
  have hden : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × M => 2 * w.1) z := contMDiffAt_const.mul contMDiffAt_fst
  have hneg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun w : ℝ × M => -branchEnergy g B w.2) z := (he.comp z contMDiffAt_snd).neg
  have hfrac := hneg.div₀ hden (mul_ne_zero (by norm_num) hz.1.ne')
  have hexp := Real.contDiff_exp.contMDiff.contMDiffAt.comp z hfrac
  apply ContMDiffAt.contMDiffWithinAt
  exact (hbase.mul hexp).mul (ContMDiffAt.sum fun k _ =>
    (contMDiffAt_fst.pow k).mul ((ha k).comp z contMDiffAt_snd))

theorem contMDiffOn_cutoffHeatParametrix_joint
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => B.cutoffHeatParametrix χ N z.1 z.2) (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  by_cases hq : z.2 ∈ tsupport χ
  · obtain ⟨U, hU, hstar, hsub, hqU⟩ := hs z.2 hq
    have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
      B.inv_inf.continuousOn.isOpen_inter_preimage B.hom.open_target hU
    exact (hχ.contMDiffAt.comp z contMDiffAt_snd).mul
      ((B.contMDiffOn_heatParametrix_joint hU hstar hsub N).contMDiffAt
        ((isOpen_Ioi.prod hV).mem_nhds ⟨hz.1, hqU⟩))
  · have he : χ =ᶠ[nhds z.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hz0 : (fun w : ℝ × M => B.cutoffHeatParametrix χ N w.1 w.2) =ᶠ[nhds z]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [he.comp_tendsto continuousAt_snd] with w hw
      change χ w.2 * B.heatParametrix N w.1 w.2 = 0
      rw [show χ w.2 = 0 from hw, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hz0

theorem cutoffHeatParametrix_isHeatForcedOnStationary
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U)
    (N : ℕ) (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (hD : D.carrier ⊆ Ioi 0) :
    DifferentialGeometry.Analysis.Parabolic.IsHeatForcedOnStationary D g
      (B.cutoffHeatParametrixResidual χ N) (B.cutoffHeatParametrix χ N) where
  jointSmooth := (B.contMDiffOn_cutoffHeatParametrix_joint hχ hs N).mono
    (prod_mono (D.regular_subset.trans hD) Subset.rfl)
  jointCont := (B.contMDiffOn_cutoffHeatParametrix_joint hχ hs N).continuousOn.mono
    (prod_mono hD Subset.rfl)
  sliceSmooth t _ := B.contMDiff_cutoffHeatParametrix hχ hs N t
  equation t ht q := by
    have htpos := hD (D.regular_subset ht)
    have hd := (B.hasDerivAt_heatParametrix N q htpos).const_mul (χ q)
    have hder : HasDerivAt (fun s => B.cutoffHeatParametrix χ N s q)
        (deriv (fun s => B.cutoffHeatParametrix χ N s q) t) t :=
      hd.differentiableAt.hasDerivAt
    apply hder.congr_deriv
    have hres := B.cutoffHeatParametrix_residual (hχ.of_le ENat.LEInfty.out) hs N htpos q
    exact sub_eq_iff_eq_add'.mp hres

theorem contMDiffOn_cutoffHeatParametrixResidual_joint
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => B.cutoffHeatParametrixResidual χ N z.1 z.2) (Ioi 0 ×ˢ univ) := by
  have h := B.contMDiffOn_cutoffHeatParametrix_joint hχ hs N
  have hD : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set M)) := isOpen_Ioi.prod isOpen_univ
  have ht : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => deriv (fun t => B.cutoffHeatParametrix χ N t z.2) z.1)
      (Ioi 0 ×ˢ univ) := by
    intro z hz
    exact (DifferentialGeometry.timeDeriv_smoothAt (h.contMDiffAt (hD.mem_nhds hz))
      (show ∞ + 1 ≤ (∞ : WithTop ℕ∞) by simp)).contMDiffWithinAt
  have hl := contMDiffOn_laplacian_leviCivita_prod_of_isOpen
    (IP := 𝓘(ℝ, ℝ)) (f := B.cutoffHeatParametrix χ N) g hD h
  apply (ht.sub hl).congr
  intro z hz
  exact (B.cutoffHeatParametrix_residual (hχ.of_le ENat.LEInfty.out) hs N hz.1 z.2).symm

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExpInvBranch
