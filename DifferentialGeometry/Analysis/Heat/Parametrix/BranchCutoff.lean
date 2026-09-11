import DifferentialGeometry.Analysis.Heat.Parametrix.BranchFinite
import DifferentialGeometry.Geometry.Operator.CutoffSupport

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch

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

def cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (χ : M → ℝ) (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  χ q * B.heatParametrix N t q

def cutoffHeatParametrixResidual
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (χ : M → ℝ) (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  -χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
    laplacian (LeviCivita g) g
      (heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) N) q -
    B.heatParametrix N t q * laplacian (LeviCivita g) g χ q -
    2 * g.inner q (gradientFun g χ q) (gradientFun g (B.heatParametrix N t) q)

theorem cutoffHeatParametrix_residual_on_domain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    {χ : M → ℝ} {q : M} (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) 2 χ q)
    (hq : q ∈ B.dom ∩ B.inv ⁻¹' U) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => B.cutoffHeatParametrix χ N s q) t -
      laplacian (LeviCivita g) g (B.cutoffHeatParametrix χ N t) q =
        B.cutoffHeatParametrixResidual χ N t q := by
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have hv : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (B.heatParametrix N t) q :=
    ((B.contMDiffOn_heatParametrix hU hstar hsub N t q hq).contMDiffAt
      (hV.mem_nhds hq)).of_le ENat.LEInfty.out
  have hn {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f q) :
      ∀ᶠ y in nhds q, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hl := laplacian_mul_at (LeviCivita g) g (hn hχ) (hn hv)
    ((gradientFun_contMDiffAt_one g hχ).mdifferentiableAt one_ne_zero)
    ((gradientFun_contMDiffAt_one g hv).mdifferentiableAt one_ne_zero)
  have hd := (B.hasDerivAt_heatParametrix N q ht).const_mul (χ q)
  have hres := B.heatParametrix_residual hU hstar hsub N hq ht
  change deriv (fun s => χ q * B.heatParametrix N s q) t -
    laplacian (LeviCivita g) g (fun y => χ y * B.heatParametrix N t y) q = _
  rw [hd.deriv, hl]
  rw [(B.hasDerivAt_heatParametrix N q ht).deriv] at hres
  dsimp only [cutoffHeatParametrixResidual]
  linear_combination χ q * hres

theorem cutoffHeatParametrixResidual_eq_zero_of_notMem_tsupport
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ} {q : M} (hq : q ∉ tsupport χ)
    (N : ℕ) (t : ℝ) : B.cutoffHeatParametrixResidual χ N t q = 0 := by
  have he : χ =ᶠ[nhds q] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hq
  obtain ⟨hl, hg⟩ := laplacian_gradient_eq_zero_of_eventuallyEq_const (LeviCivita g) g he
  simp only [cutoffHeatParametrixResidual, he.eq_of_nhds, hl, hg, neg_zero, zero_mul,
    mul_zero, map_zero, zero_apply, sub_self]

theorem cutoffHeatParametrix_residual
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) 2 χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U)
    (N : ℕ) {t : ℝ} (ht : 0 < t) (q : M) :
    deriv (fun s => B.cutoffHeatParametrix χ N s q) t -
      laplacian (LeviCivita g) g (B.cutoffHeatParametrix χ N t) q =
        B.cutoffHeatParametrixResidual χ N t q := by
  by_cases hq : q ∈ tsupport χ
  · obtain ⟨U, hU, hstar, hsub, hqU⟩ := hs q hq
    exact B.cutoffHeatParametrix_residual_on_domain hU hstar hsub hχ.contMDiffAt hqU N ht
  · have he : χ =ᶠ[nhds q] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hf : B.cutoffHeatParametrix χ N t =ᶠ[nhds q] fun _ => 0 := by
      filter_upwards [he] with y hy
      simp only [cutoffHeatParametrix, hy, zero_mul]
    have htime : (fun s => B.cutoffHeatParametrix χ N s q) = fun _ => 0 := by
      funext s
      simp only [cutoffHeatParametrix, he.eq_of_nhds, zero_mul]
    rw [htime, (laplacian_gradient_eq_zero_of_eventuallyEq_const (LeviCivita g) g hf).1,
      B.cutoffHeatParametrixResidual_eq_zero_of_notMem_tsupport hq N t, deriv_const, sub_zero]

theorem hasCompactSupport_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ} (hc : HasCompactSupport χ)
    (N : ℕ) (t : ℝ) : HasCompactSupport (B.cutoffHeatParametrix χ N t) :=
  hc.mul_right

theorem contMDiff_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : ∀ q ∈ tsupport χ, ∃ U : Set E, IsOpen U ∧ StarConvex ℝ 0 U ∧
      U ⊆ B.hom.source ∧ q ∈ B.dom ∩ B.inv ⁻¹' U) (N : ℕ) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (B.cutoffHeatParametrix χ N t) := by
  apply contMDiff_of_tsupport
  intro q hq
  have hqχ : q ∈ tsupport χ := tsupport_mul_subset_left hq
  obtain ⟨U, hU, hstar, hsub, hqU⟩ := hs q hqχ
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  exact hχ.contMDiffAt.mul ((B.contMDiffOn_heatParametrix hU hstar hsub N t q hqU).contMDiffAt
    (hV.mem_nhds hqU))

theorem inner_gradient_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    {q : M} (hq : q ∈ B.dom ∩ B.inv ⁻¹' U) (X : TangentSpace I q) (N : ℕ) (t : ℝ) :
    g.inner q X (gradientFun g (B.heatParametrix N t) q) =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) *
        ((∑ k ∈ Finset.range (N + 1), t ^ k * g.inner q X
          (gradientFun g (heatParametrixCoefficientInCoordinates g B.hom B.inv
            (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k) q)) -
          (∑ k ∈ Finset.range (N + 1), t ^ k *
            heatParametrixCoefficientInCoordinates g B.hom B.inv
              (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k q) /
            (2 * t) * g.inner q X (gradientFun g (branchEnergy g B) q)) := by
  let a := heatParametrixCoefficientInCoordinates g B.hom B.inv
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0)
  let e := branchEnergy g B
  let c := (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  let β := -(2 * t)⁻¹
  let S : M → ℝ := ∑ k ∈ Finset.range (N + 1), (t ^ k) • a k
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have ha (k : ℕ) : MDifferentiableAt I 𝓘(ℝ, ℝ) (a k) q :=
    ((B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k q hq).contMDiffAt
      (hV.mem_nhds hq)).mdifferentiableAt (by simp)
  have he : MDifferentiableAt I 𝓘(ℝ, ℝ) e q :=
    ((contMDiffOn_branchEnergy B q hq.1).contMDiffAt
      (B.hom.open_target.mem_nhds hq.1)).mdifferentiableAt (by simp)
  have hb : MDifferentiableAt I 𝓘(ℝ, ℝ) (β • e) q := he.const_smul β
  have hexp : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.exp ((β • e) y)) q :=
    Real.differentiable_exp.differentiableAt.mdifferentiableAt.comp q hb
  have hS : MDifferentiableAt I 𝓘(ℝ, ℝ) S q :=
    MDifferentiableAt.sum fun k _ => (ha k).const_smul (t ^ k)
  have hP : B.heatParametrix N t = c • (fun y => Real.exp ((β • e) y) * S y) := by
    funext y
    simp only [heatParametrix, S, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    dsimp only [c, β, e, a]
    rw [show -(2 * t)⁻¹ * branchEnergy g B y = -branchEnergy g B y / (2 * t) by ring]
    ring
  have hprod : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.exp ((β • e) y) * S y) q :=
    hexp.mul hS
  rw [hP, gradientFun_const_smul g c hprod, gradientFun_mul g hexp hS,
    gradientFun_sum_smul g (Finset.range (N + 1)) (fun k => t ^ k) (fun k _ => ha k),
    gradientFun_comp g Real.differentiable_exp.differentiableAt hb,
    gradientFun_const_smul g β he]
  simp only [Real.deriv_exp, Pi.smul_apply, smul_eq_mul, map_smul, map_add, map_sum]
  dsimp only [c, β, e, a, S]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [show -(2 * t)⁻¹ * branchEnergy g B q = -branchEnergy g B q / (2 * t) by ring]
  ring

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch
