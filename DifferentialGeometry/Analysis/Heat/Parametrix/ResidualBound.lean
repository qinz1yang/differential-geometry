import DifferentialGeometry.Analysis.Calculus.ExponentialAsymptotics
import DifferentialGeometry.Analysis.Heat.Parametrix.Cutoff
import DifferentialGeometry.Geometry.Exponential.BranchEnergyBounds
import DifferentialGeometry.Geometry.Operator.CutoffSupport
import DifferentialGeometry.Geometry.Operator.LaplacianRegularity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators

private theorem exists_gaussian_cutoff_commutator_bound (n T A : ℝ) {c : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ e a₀ a₁ b₀ b₁ d l : ℝ,
      c ≤ e → |a₀| ≤ A → |a₁| ≤ A → |b₀| ≤ A → |b₁| ≤ A → |d| ≤ A → |l| ≤ A →
      |(4 * Real.pi * t) ^ (-n / 2) * Real.exp (-e / (2 * t)) *
          (a₀ + t * a₁) * l +
        2 * ((4 * Real.pi * t) ^ (-n / 2) * Real.exp (-e / (2 * t)) *
          (b₀ + t * b₁ - (a₀ + t * a₁) / (2 * t) * d))| ≤ C := by
  let B := A + |T| * A
  have hB : 0 ≤ B := add_nonneg hA (mul_nonneg (abs_nonneg T) hA)
  obtain ⟨C₀, hC₀, h₀⟩ := Real.exists_rpow_mul_exp_neg_div_le_rpow (-n / 2) 0 T (half_pos hc)
  obtain ⟨C₁, hC₁, h₁⟩ := Real.exists_rpow_mul_exp_neg_div_le_rpow (-n / 2 - 1) 0 T (half_pos hc)
  let S := (4 * Real.pi) ^ (-n / 2)
  have hS : 0 ≤ S := Real.rpow_nonneg (by positivity) _
  refine ⟨S * C₀ * B * A + 2 * (S * C₀ * B + S * C₁ * B * A / 2), by positivity, ?_⟩
  intro t ht e a₀ a₁ b₀ b₁ d l he ha₀ ha₁ hb₀ hb₁ hd hl
  have hat : |t| ≤ |T| := by rw [abs_of_pos ht.1]; exact ht.2.trans (le_abs_self T)
  have ha : |a₀ + t * a₁| ≤ B := by
    calc
      _ ≤ |a₀| + |t| * |a₁| := by simpa only [abs_mul] using abs_add_le a₀ (t * a₁)
      _ ≤ A + |T| * A := by gcongr
  have hb : |b₀ + t * b₁| ≤ B := by
    calc
      _ ≤ |b₀| + |t| * |b₁| := by simpa only [abs_mul] using abs_add_le b₀ (t * b₁)
      _ ≤ A + |T| * A := by gcongr
  let G := (4 * Real.pi * t) ^ (-n / 2) * Real.exp (-e / (2 * t))
  have hG : 0 ≤ G := mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) ht.1.le) _) (Real.exp_pos _).le
  have hG₀ : G ≤ S * C₀ := by
    have hbound := h₀ t ht (e / 2) (by linarith)
    simp only [Real.rpow_zero, mul_one] at hbound
    dsimp only [G, S]
    rw [Real.mul_rpow (by positivity) ht.1.le]
    rw [show -e / (2 * t) = -(e / 2) / t by ring]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbound hS
  have hG₁ : G / t ≤ S * C₁ := by
    have hbound := h₁ t ht (e / 2) (by linarith)
    simp only [Real.rpow_zero, mul_one] at hbound
    dsimp only [G, S]
    rw [Real.mul_rpow (by positivity) ht.1.le]
    rw [show -e / (2 * t) = -(e / 2) / t by ring]
    have heq : ((4 * Real.pi) ^ (-n / 2) * t ^ (-n / 2) * Real.exp (-(e / 2) / t)) / t =
        (4 * Real.pi) ^ (-n / 2) * (t ^ (-n / 2 - 1) * Real.exp (-(e / 2) / t)) := by
      rw [Real.rpow_sub_one ht.1.ne']
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hbound hS
  change |G * (a₀ + t * a₁) * l + 2 * (G * (b₀ + t * b₁ - (a₀ + t * a₁) / (2 * t) * d))| ≤ _
  calc
    _ ≤ G * |a₀ + t * a₁| * |l| + 2 *
        (G * |b₀ + t * b₁| + G / t * |a₀ + t * a₁| * |d| / 2) := by
      have htri := abs_add_le (G * (a₀ + t * a₁) * l)
        (2 * (G * (b₀ + t * b₁ - (a₀ + t * a₁) / (2 * t) * d)))
      have hin := abs_sub (b₀ + t * b₁) ((a₀ + t * a₁) / (2 * t) * d)
      simp only [abs_mul, abs_of_nonneg hG, abs_of_pos ht.1,
        abs_div, abs_two] at htri hin
      calc
        _ ≤ G * |a₀ + t * a₁| * |l| + 2 * (G *
          (|b₀ + t * b₁| + |a₀ + t * a₁| / (2 * t) * |d|)) :=
          htri.trans (add_le_add_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hin hG) (show (0 : ℝ) ≤ 2 by norm_num)) _)
        _ = _ := by ring
    _ ≤ S * C₀ * B * A + 2 * (S * C₀ * B + S * C₁ * B * A / 2) := by gcongr

namespace DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_pos_le_branchEnergy_on_laplacian_gradient_support
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ B.dom) {a : ℝ} (hp : χ =ᶠ[nhds p] fun _ => a) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tsupport χ ∧ p ∉ K ∧
      ∃ c : ℝ, 0 < c ∧ (∀ q ∈ K, c ≤ branchEnergy g B q) ∧
        ∀ q ∉ K, Operator.laplacian (Connection.LeviCivita g) g χ q = 0 ∧
          Operator.gradientFun g χ q = 0 := by
  obtain ⟨K, hK, hKs, hpK, hv⟩ :=
    Operator.exists_isCompact_laplacian_gradient_support_of_eventuallyEq_const
      (Connection.LeviCivita g) g hc hp
  obtain ⟨c, hc, hb⟩ := exists_pos_le_branchEnergy_of_isCompact B hK (hKs.trans hs) hpK
  exact ⟨K, hK, hKs, hpK, c, hc, hb, hv⟩

end DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius)
open Geometry.Riemannian.Exponential Geometry.Riemannian.NormalCoordinates
open Geometry.Connection Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem continuousOn_inner_gradient
    (g : SmoothRiemannianMetric I M) {u v : M → ℝ} {U : Set M}
    (hU : IsOpen U) (hu : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u U)
    (hv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ v U) :
    ContinuousOn (fun q => g.inner q (gradientFun g u q) (gradientFun g v q)) U := by
  intro q hq
  have hgu := gradientFun_contMDiffAt g ((hu q hq).contMDiffAt (hU.mem_nhds hq))
  have hgv := gradientFun_contMDiffAt g ((hv q hq).contMDiffAt (hU.mem_nhds hq))
  have happ : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ ℝ)) ∞
      (fun z : M => (⟨z, g.inner z (gradientFun g u z) (gradientFun g v z)⟩ :
        TotalSpace ℝ (Bundle.Trivial M ℝ))) q :=
    ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) g.contMDiff.contMDiffAt hgu hgv
  rw [Bundle.contMDiffAt_totalSpace] at happ
  exact happ.2.continuousAt.continuousWithinAt

private theorem exists_cutoffHeatParametrix_coefficient_bound
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    {K : Set M} (hK : IsCompact K)
    (hKU : K ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ K,
      |χ q| ≤ C ∧ |heatParametrixCoefficient g p 0 q| ≤ C ∧
      |heatParametrixCoefficient g p 1 q| ≤ C ∧
      |laplacian (LeviCivita g) g (heatParametrixCoefficient g p 1) q| ≤ C ∧
      |laplacian (LeviCivita g) g χ q| ≤ C ∧
      |g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g B) q)| ≤ C ∧
      |g.inner q (gradientFun g χ q) (gradientFun g (heatParametrixCoefficient g p 0) q)| ≤ C ∧
      |g.inner q (gradientFun g χ q) (gradientFun g (heatParametrixCoefficient g p 1) q)| ≤ C := by
  let U := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  have hU : IsOpen U := (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
    (normalChartAt g p).open_source Metric.isOpen_ball
  have hKU' : K ⊆ U := fun _ hq => (hKU hq).2
  have hKB : K ⊆ B.dom := fun _ hq => (hKU hq).1
  let a₀ := heatParametrixCoefficient g p 0
  let a₁ := heatParametrixCoefficient g p 1
  let l₁ := laplacian (LeviCivita g) g a₁
  let lχ := laplacian (LeviCivita g) g χ
  let d := fun q => g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g B) q)
  let b₀ := fun q => g.inner q (gradientFun g χ q) (gradientFun g a₀ q)
  let b₁ := fun q => g.inner q (gradientFun g χ q) (gradientFun g a₁ q)
  have hχc : ContinuousOn χ K := hχ.continuous.continuousOn
  have ha₀ : ContinuousOn a₀ K := (contMDiffOn_heatParametrixCoefficient g p 0).continuousOn.mono hKU'
  have ha₁ : ContinuousOn a₁ K := (contMDiffOn_heatParametrixCoefficient g p 1).continuousOn.mono hKU'
  have hl₁ : ContinuousOn l₁ K := (contMDiffOn_laplacian_leviCivita g hU
    (contMDiffOn_heatParametrixCoefficient g p 1)).continuousOn.mono hKU'
  have hlχ : ContinuousOn lχ K := (contMDiff_laplacian_leviCivita g hχ).continuous.continuousOn
  have hd : ContinuousOn d K := (continuousOn_inner_gradient g B.hom.open_target
    hχ.contMDiffOn (contMDiffOn_branchEnergy B)).mono hKB
  have hb₀ : ContinuousOn b₀ K := (continuousOn_inner_gradient g hU
    hχ.contMDiffOn (contMDiffOn_heatParametrixCoefficient g p 0)).mono hKU'
  have hb₁ : ContinuousOn b₁ K := (continuousOn_inner_gradient g hU
    hχ.contMDiffOn (contMDiffOn_heatParametrixCoefficient g p 1)).mono hKU'
  let F := fun q => |χ q| + |a₀ q| + |a₁ q| + |l₁ q| + |lχ q| + |d q| + |b₀ q| + |b₁ q|
  have hF : ContinuousOn F K :=
    ((((((hχc.abs.add ha₀.abs).add ha₁.abs).add hl₁.abs).add hlχ.abs).add hd.abs).add hb₀.abs).add hb₁.abs
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q hq
  have hCF : |F q| ≤ C := by simpa only [Real.norm_eq_abs] using hC q hq
  have hb : F q ≤ max C 0 := (le_abs_self (F q)).trans
    (hCF.trans (le_max_left C 0))
  change |χ q| ≤ _ ∧ |a₀ q| ≤ _ ∧ |a₁ q| ≤ _ ∧ |l₁ q| ≤ _ ∧ |lχ q| ≤ _ ∧
    |d q| ≤ _ ∧ |b₀ q| ≤ _ ∧ |b₁ q| ≤ _
  dsimp only [F] at hb
  have h0 := abs_nonneg (χ q)
  have h1 := abs_nonneg (a₀ q)
  have h2 := abs_nonneg (a₁ q)
  have h3 := abs_nonneg (l₁ q)
  have h4 := abs_nonneg (lχ q)
  have h5 := abs_nonneg (d q)
  have h6 := abs_nonneg (b₀ q)
  have h7 := abs_nonneg (b₁ q)
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith⟩

end DifferentialGeometry.Analysis.HeatEquation

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius)
open Geometry.Riemannian.Exponential Geometry.Riemannian.NormalCoordinates
open Geometry.Connection Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

theorem inner_gradient_heatParametrix_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {q : M}
    (hq : q ∈ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    (X : TangentSpace I q) (t : ℝ) :
    g.inner q X (gradientFun g (heatParametrix g B 1 t) q) =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) *
        (g.inner q X (gradientFun g (heatParametrixCoefficient g p 0) q) +
          t * g.inner q X (gradientFun g (heatParametrixCoefficient g p 1) q) -
          (heatParametrixCoefficient g p 0 q + t * heatParametrixCoefficient g p 1 q) /
            (2 * t) * g.inner q X (gradientFun g (branchEnergy g B) q)) := by
  let a₀ := heatParametrixCoefficient g p 0
  let a₁ := heatParametrixCoefficient g p 1
  let e := branchEnergy g B
  let c := (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  let β := -(2 * t)⁻¹
  have hU : IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have ha₀ : MDifferentiableAt I 𝓘(ℝ, ℝ) a₀ q :=
    ((contMDiffOn_heatParametrixCoefficient g p 0 q hq.2).contMDiffAt
      (hU.mem_nhds hq.2)).mdifferentiableAt (by simp)
  have ha₁ : MDifferentiableAt I 𝓘(ℝ, ℝ) a₁ q :=
    ((contMDiffOn_heatParametrixCoefficient g p 1 q hq.2).contMDiffAt
      (hU.mem_nhds hq.2)).mdifferentiableAt (by simp)
  have he : MDifferentiableAt I 𝓘(ℝ, ℝ) e q :=
    ((contMDiffOn_branchEnergy B q hq.1).contMDiffAt
      (B.hom.open_target.mem_nhds hq.1)).mdifferentiableAt (by simp)
  have hb : MDifferentiableAt I 𝓘(ℝ, ℝ) (β • e) q := he.const_smul β
  have hexp : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => Real.exp ((β • e) y)) q :=
    Real.differentiable_exp.differentiableAt.mdifferentiableAt.comp q hb
  have hsum : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => a₀ y + t * a₁ y) q :=
    ha₀.add (ha₁.const_smul t)
  have hP : heatParametrix g B 1 t = c •
      (fun y => Real.exp ((β • e) y) * (a₀ y + t * a₁ y)) := by
    funext y
    simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, one_mul, Pi.smul_apply, smul_eq_mul]
    dsimp only [c, β, e, a₀, a₁]
    rw [show -(2 * t)⁻¹ * branchEnergy g B y = -branchEnergy g B y / (2 * t) by ring]
    ring
  have hprod : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y => Real.exp ((β • e) y) * (a₀ y + t * a₁ y)) q := hexp.mul hsum
  have hcgrad := gradientFun_const_smul g c hprod
  have hmulgrad := gradientFun_mul g hexp hsum
  rw [hP, hcgrad, hmulgrad]
  have htfun : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => t * a₁ y) q := ha₁.const_smul t
  have hsumgrad := gradientFun_add g ha₀ htfun
  have htg : gradientFun g (fun y => t * a₁ y) q = t • gradientFun g a₁ q :=
    gradientFun_const_smul g t ha₁
  have heg := gradientFun_comp g Real.differentiable_exp.differentiableAt hb
  have hbg := gradientFun_const_smul g β he
  rw [hsumgrad, htg, heg, hbg]
  simp only [Real.deriv_exp, Pi.smul_apply, smul_eq_mul, map_smul, map_add]
  dsimp only [c, β, e, a₀, a₁]
  rw [show -(2 * t)⁻¹ * branchEnergy g B q = -branchEnergy g B q / (2 * t) by ring]
  ring

theorem exists_cutoffHeatParametrix_residual_bound_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (hn : Module.finrank ℝ E = 2)
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (hcχ : HasCompactSupport χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))
    {a : ℝ} (hp : χ =ᶠ[nhds p] fun _ => a) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioc 0 T, ∀ q : M,
      |cutoffHeatParametrixResidual g B χ 1 t q| ≤ C := by
  obtain ⟨A, hA, hcoeff⟩ := exists_cutoffHeatParametrix_coefficient_bound B hχ hcχ hs
  obtain ⟨K, _, hKs, _, c, hc, hKenergy, hKvanish⟩ :=
    exists_pos_le_branchEnergy_on_laplacian_gradient_support B hcχ (fun q hq => (hs hq).1) hp
  obtain ⟨Ccomm, hCcomm, hcomm⟩ := exists_gaussian_cutoff_commutator_bound
    (Module.finrank ℝ E) T A hc hA
  let Cmain : ℝ := A * A / (4 * Real.pi)
  have hCmain : 0 ≤ Cmain := by dsimp only [Cmain]; positivity
  refine ⟨Cmain + Ccomm, add_nonneg hCmain hCcomm, ?_⟩
  intro t ht q
  have htpos : 0 < t := ht.1
  by_cases hqS : q ∈ tsupport χ
  · have hqU := hs hqS
    obtain ⟨hχA, ha₀A, ha₁A, hl₁A, hlχA, hdA, hb₀A, hb₁A⟩ := hcoeff q hqS
    have henergy : 0 ≤ branchEnergy g B q := by
      change 0 ≤ (1 / 2 : ℝ) * g.inner p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q))
      apply mul_nonneg (by norm_num)
      by_cases hv : (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm (B.inv q) = 0
      · simp only [hv, map_zero]; exact le_rfl
      · exact (g.pos p _ hv).le
    have hexp : Real.exp (-branchEnergy g B q / (2 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr henergy)
        (by positivity))
    have hbase : 0 ≤ (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    have hpref : (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * t =
        1 / (4 * Real.pi) := by
      rw [hn]
      norm_num only [Nat.cast_ofNat, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    have hterm : |χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p 1) q| ≤ Cmain := by
      simp only [abs_mul, abs_of_nonneg hbase, Real.abs_exp, abs_of_pos htpos]
      calc
        _ ≤ A * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * 1 * t * A := by
          gcongr
        _ = A * A * ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) * t) := by ring
        _ = Cmain := by rw [hpref]; dsimp only [Cmain]; ring
    have hcommbound : |heatParametrix g B 1 t q * laplacian (LeviCivita g) g χ q +
        2 * g.inner q (gradientFun g χ q)
          (gradientFun g (heatParametrix g B 1 t) q)| ≤ Ccomm := by
      by_cases hqK : q ∈ K
      · rw [inner_gradient_heatParametrix_one B hqU (gradientFun g χ q) t]
        have hscalar := hcomm t ht (branchEnergy g B q)
          (heatParametrixCoefficient g p 0 q) (heatParametrixCoefficient g p 1 q)
          (g.inner q (gradientFun g χ q) (gradientFun g (heatParametrixCoefficient g p 0) q))
          (g.inner q (gradientFun g χ q) (gradientFun g (heatParametrixCoefficient g p 1) q))
          (g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g B) q))
          (laplacian (LeviCivita g) g χ q)
          (hKenergy q hqK) ha₀A ha₁A hb₀A hb₁A hdA hlχA
        simpa only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero,
          zero_add, pow_zero, pow_one, one_mul] using hscalar
      · obtain ⟨hlzero, hgradzero⟩ := hKvanish q hqK
        simpa only [hlzero, hgradzero, map_zero, zero_apply,
          mul_zero, add_zero, abs_zero] using hCcomm
    have htri := abs_sub
      (-(χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p 1) q))
      (heatParametrix g B 1 t q * laplacian (LeviCivita g) g χ q +
        2 * g.inner q (gradientFun g χ q)
          (gradientFun g (heatParametrix g B 1 t) q))
    simp only [abs_neg] at htri
    have heq : cutoffHeatParametrixResidual g B χ 1 t q =
      -(χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p 1) q) -
      (heatParametrix g B 1 t q * laplacian (LeviCivita g) g χ q +
        2 * g.inner q (gradientFun g χ q)
          (gradientFun g (heatParametrix g B 1 t) q)) := by
      dsimp only [cutoffHeatParametrixResidual]; rw [pow_one]; ring
    rw [heq]
    exact htri.trans (add_le_add hterm hcommbound)
  · have hχzero : χ q = 0 := image_eq_zero_of_notMem_tsupport hqS
    obtain ⟨hlzero, hgradzero⟩ := hKvanish q (fun hq => hqS (hKs hq))
    simpa only [cutoffHeatParametrixResidual, hχzero, hlzero, hgradzero,
      map_zero, zero_apply, neg_zero, zero_mul, mul_zero, sub_zero, abs_zero]
      using add_nonneg hCmain hCcomm

private theorem cutoffHeatParametrixResidual_eq_zero_of_notMem_tsupport
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} {q : M} (hq : q ∉ tsupport χ)
    (N : ℕ) (t : ℝ) : cutoffHeatParametrixResidual g B χ N t q = 0 := by
  have he : χ =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
  have hc : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ q := contMDiffAt_const.congr_of_eventuallyEq he
  have hgrad : gradientFun g χ q = 0 := by
    apply gradientFun_eq_zero_of_mfderiv_eq_zero
    rw [he.mfderiv_eq]
    exact mfderiv_const
  have hl : laplacian (LeviCivita g) g χ q = 0 := by
    calc
      _ = laplacian (LeviCivita g) g (fun _ : M => (0 : ℝ)) q :=
        laplacian_congr_of_eventuallyEq (LeviCivita g) g hc contMDiffAt_const he
      _ = 0 := laplacian_const (LeviCivita g) g 0 q
  simp only [cutoffHeatParametrixResidual, show χ q = 0 from he.eq_of_nhds,
    hl, hgrad, neg_zero, zero_mul, mul_zero, sub_zero, map_zero, zero_apply]

theorem continuousOn_cutoffHeatParametrixResidual_one
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) {χ : M → ℝ} (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))) :
    ContinuousOn (fun z : ℝ × M => cutoffHeatParametrixResidual g B χ 1 z.1 z.2)
      (Ioi 0 ×ˢ univ) := by
  let V := (normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)
  let U := B.dom ∩ V
  have hV : IsOpen V := (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
    (normalChartAt g p).open_source Metric.isOpen_ball
  have hU : IsOpen U := B.hom.open_target.inter hV
  intro z hz
  apply ContinuousAt.continuousWithinAt
  by_cases hzs : z.2 ∈ tsupport χ
  · have hzU : z.2 ∈ U := hs hzs
    let a₀ := heatParametrixCoefficient g p 0
    let a₁ := heatParametrixCoefficient g p 1
    let l₁ := laplacian (LeviCivita g) g a₁
    let lχ := laplacian (LeviCivita g) g χ
    let e := branchEnergy g B
    let d := fun q => g.inner q (gradientFun g χ q) (gradientFun g e q)
    let b₀ := fun q => g.inner q (gradientFun g χ q) (gradientFun g a₀ q)
    let b₁ := fun q => g.inner q (gradientFun g χ q) (gradientFun g a₁ q)
    have ha₀ : ContinuousAt a₀ z.2 := (contMDiffOn_heatParametrixCoefficient g p 0).continuousOn.continuousAt
      (hV.mem_nhds hzU.2)
    have ha₁ : ContinuousAt a₁ z.2 := (contMDiffOn_heatParametrixCoefficient g p 1).continuousOn.continuousAt
      (hV.mem_nhds hzU.2)
    have hl₁ : ContinuousAt l₁ z.2 := (contMDiffOn_laplacian_leviCivita g hV
      (contMDiffOn_heatParametrixCoefficient g p 1)).continuousOn.continuousAt (hV.mem_nhds hzU.2)
    have hlχ : ContinuousAt lχ z.2 := (contMDiff_laplacian_leviCivita g hχ).continuous.continuousAt
    have he : ContinuousAt e z.2 := (contMDiffOn_branchEnergy B).continuousOn.continuousAt
      (B.hom.open_target.mem_nhds hzU.1)
    have hd : ContinuousAt d z.2 := (continuousOn_inner_gradient g B.hom.open_target
      hχ.contMDiffOn (contMDiffOn_branchEnergy B)).continuousAt (B.hom.open_target.mem_nhds hzU.1)
    have hb₀ : ContinuousAt b₀ z.2 := (continuousOn_inner_gradient g hV
      hχ.contMDiffOn (contMDiffOn_heatParametrixCoefficient g p 0)).continuousAt (hV.mem_nhds hzU.2)
    have hb₁ : ContinuousAt b₁ z.2 := (continuousOn_inner_gradient g hV
      hχ.contMDiffOn (contMDiffOn_heatParametrixCoefficient g p 1)).continuousAt (hV.mem_nhds hzU.2)
    let G := fun w : ℝ × M => (4 * Real.pi * w.1) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-e w.2 / (2 * w.1))
    have hG : ContinuousAt G z := by
      have hbase : ContinuousAt (fun w : ℝ × M =>
          (4 * Real.pi * w.1) ^ (-(Module.finrank ℝ E : ℝ) / 2)) z :=
        (continuousAt_const.mul continuousAt_fst).rpow_const (Or.inl (by
          change 4 * Real.pi * z.1 ≠ 0
          exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (ne_of_gt hz.1)))
      exact hbase.mul (Real.continuous_exp.continuousAt.comp
        ((he.comp continuousAt_snd).neg.div (continuousAt_const.mul continuousAt_fst) (by
          change 2 * z.1 ≠ 0
          exact mul_ne_zero (by norm_num) (ne_of_gt hz.1))))
    let F := fun w : ℝ × M => -χ w.2 * G w * w.1 * l₁ w.2 -
      G w * (a₀ w.2 + w.1 * a₁ w.2) * lχ w.2 -
      2 * (G w * (b₀ w.2 + w.1 * b₁ w.2 -
        (a₀ w.2 + w.1 * a₁ w.2) / (2 * w.1) * d w.2))
    have hsum : ContinuousAt (fun w : ℝ × M => a₀ w.2 + w.1 * a₁ w.2) z :=
      (ha₀.comp continuousAt_snd).add (continuousAt_fst.mul (ha₁.comp continuousAt_snd))
    have hF : ContinuousAt F z :=
      (((hχ.continuous.continuousAt.comp continuousAt_snd).neg.mul hG).mul continuousAt_fst).mul
        (hl₁.comp continuousAt_snd) |>.sub ((hG.mul hsum).mul (hlχ.comp continuousAt_snd)) |>.sub
          (continuousAt_const.mul (hG.mul (((hb₀.comp continuousAt_snd).add
            (continuousAt_fst.mul (hb₁.comp continuousAt_snd))).sub
              ((hsum.div (continuousAt_const.mul continuousAt_fst) (by
                change 2 * z.1 ≠ 0
                exact mul_ne_zero (by norm_num) (ne_of_gt hz.1))).mul (hd.comp continuousAt_snd)))))
    apply hF.congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.preimage_mem_nhds (hU.mem_nhds hzU)] with w hw
    dsimp only [F, cutoffHeatParametrixResidual]
    rw [inner_gradient_heatParametrix_one B hw (gradientFun g χ w.2) w.1]
    simp only [heatParametrix, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, pow_one, one_mul]
    dsimp only [G, a₀, a₁, l₁, lχ, e, d, b₀, b₁]
    ring
  · have he : (fun w : ℝ × M => cutoffHeatParametrixResidual g B χ 1 w.1 w.2) =ᶠ[nhds z]
        (fun _ => 0) := by
      filter_upwards [continuousAt_snd.preimage_mem_nhds
        ((isClosed_tsupport χ).isOpen_compl.mem_nhds hzs)] with w hw
      exact cutoffHeatParametrixResidual_eq_zero_of_notMem_tsupport B hw 1 w.1
    exact continuousAt_const.congr_of_eventuallyEq he

end DifferentialGeometry.Analysis.HeatEquation
