import DifferentialGeometry.Analysis.Parabolic.ScalarHeat.TimeDependent
import DifferentialGeometry.Analysis.Heat.Parametrix.Finite
import DifferentialGeometry.Analysis.Heat.Parametrix.CoordinateCompatibility
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Analysis.HeatEquation

open Geometry.Riemannian (IsMetricNorm expMapC2Radius mem_expMapDiffeo_source_of_norm_lt_radius)
open Geometry.Riemannian.Exponential Geometry.Riemannian.NormalCoordinates
open Geometry.Riemannian.VolumeComparison Geometry.Connection Geometry.Operator

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

private def heatParametrixLocalDomain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) : Set M :=
  B.dom ∩ ((normalChartAt g p).source ∩
    (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))

private theorem isOpen_heatParametrixLocalDomain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) : IsOpen (heatParametrixLocalDomain B) :=
  B.hom.open_target.inter ((normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
    (normalChartAt g p).open_source Metric.isOpen_ball)

private theorem centre_mem_heatParametrixLocalDomain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source) :
    p ∈ heatParametrixLocalDomain B := by
  have hz : B.hom 0 = p := by
    rw [← B.hom_eq hB]
    simp only [map_zero, expMapIntrinsic_zero]
  refine ⟨?_, normalChartAt_source g p, ?_⟩
  · change p ∈ B.hom.target
    have hm := B.hom.map_source hB
    simpa only [hz] using hm
  · change normalChartAt g p p ∈ Metric.ball (0 : E) (expMapC2Radius g p)
    rw [normalChartAt_centre]
    simpa using Geometry.Riemannian.expMapC2Radius_pos g p

theorem exists_heatParametrix_cutoff
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[nhds p] 1 ∧
      tsupport χ ⊆ B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  obtain ⟨χ, hχ, hc, h1, hs, hb⟩ := DifferentialGeometry.Analysis.exists_mfd_bump
    (I := I) (K := {p}) isCompact_singleton (isOpen_heatParametrixLocalDomain B)
    (singleton_subset_iff.mpr (centre_mem_heatParametrixLocalDomain B hB))
  refine ⟨χ, hχ, hc, ?_, hs, hb⟩
  simpa only [nhdsSet_singleton] using h1

def cutoffHeatParametrix (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm g} {p : M} (B : ExponentialInverseBranch g hEnorm p)
    (χ : M → ℝ) (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  χ q * heatParametrix g B N t q

theorem contMDiff_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))) (N : ℕ) (t : ℝ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (cutoffHeatParametrix g B χ N t) := by
  apply contMDiff_of_tsupport
  intro q hq
  have hqχ : q ∈ tsupport χ :=
    tsupport_mul_subset_left hq
  have hqU := hs hqχ
  exact hχ.contMDiffAt.mul ((contMDiffOn_heatParametrix B N t q hqU).contMDiffAt
    ((isOpen_heatParametrixLocalDomain B).mem_nhds hqU))

theorem hasCompactSupport_cutoffHeatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ} (hc : HasCompactSupport χ)
    (N : ℕ) (t : ℝ) : HasCompactSupport (cutoffHeatParametrix g B χ N t) :=
  hc.mul_right

private theorem contMDiffAt_heatParametrix_joint
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) {t : ℝ} (ht : 0 < t) {q : M}
    (hq : q ∈ heatParametrixLocalDomain B) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => heatParametrix g B N z.1 z.2) (t, q) := by
  have he := (contMDiffOn_branchEnergy B q hq.1).contMDiffAt
    (B.hom.open_target.mem_nhds hq.1)
  have ha (k : ℕ) := (contMDiffOn_heatParametrixCoefficient g p k q hq.2).contMDiffAt
    (((normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball).mem_nhds hq.2)
  have harg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 4 * Real.pi * z.1) (t, q) :=
    contMDiffAt_const.mul contMDiffAt_fst
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => (4 * Real.pi * z.1) ^ (-(Module.finrank ℝ E : ℝ) / 2))
      (t, q) := by
    have hr := (Real.contDiffAt_rpow_const_of_ne (n := ∞)
      (p := -(Module.finrank ℝ E : ℝ) / 2) (by positivity : 4 * Real.pi * t ≠ 0)).contMDiffAt
    exact hr.comp (t, q) harg
  have hden : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1) (t, q) := contMDiffAt_const.mul contMDiffAt_fst
  have hneg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => -branchEnergy g B z.2) (t, q) :=
    (he.comp (t, q) contMDiffAt_snd).neg
  have hfrac := hneg.div₀ hden (by change 2 * t ≠ 0; positivity)
  have hexp := Real.contDiff_exp.contMDiff.contMDiffAt.comp (t, q) hfrac
  exact (hbase.mul hexp).mul (ContMDiffAt.sum fun k _ =>
    (contMDiffAt_fst.pow k).mul ((ha k).comp (t, q) contMDiffAt_snd))

theorem contMDiffOn_cutoffHeatParametrix_joint
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))) (N : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => cutoffHeatParametrix g B χ N z.1 z.2) (Ioi 0 ×ˢ univ) := by
  intro z hz
  apply ContMDiffAt.contMDiffWithinAt
  by_cases hq : z.2 ∈ tsupport χ
  · exact (hχ.contMDiffAt.comp z contMDiffAt_snd).mul
      (contMDiffAt_heatParametrix_joint B N hz.1 (hs hq))
  · have he : χ =ᶠ[nhds z.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hz0 : (fun w : ℝ × M => cutoffHeatParametrix g B χ N w.1 w.2) =ᶠ[nhds z]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [he.comp_tendsto continuousAt_snd] with w hw
      change χ w.2 * heatParametrix g B N w.1 w.2 = 0
      rw [show χ w.2 = 0 from hw, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq hz0

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [PseudoEMetricSpace M]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem laplacian_mul_of_contMDiffAt
    {g : SmoothRiemannianMetric I M} {χ v : M → ℝ} {q : M}
    (hχ : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ χ q) (hv : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ v q) :
    laplacian (LeviCivita g) g (fun y => χ y * v y) q =
      χ q * laplacian (LeviCivita g) g v q +
        v q * laplacian (LeviCivita g) g χ q +
          2 * g.inner q (gradientFun g χ q) (gradientFun g v q) := by
  have hn {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ f q) :
      ∀ᶠ y in nhds q, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp
      (hf.of_le (show (2 : WithTop ℕ∞) ≤ ∞ from ENat.LEInfty.out))).mono
      fun y hy => hy.mdifferentiableAt (by simp)
  exact laplacian_mul_at (LeviCivita g) g (hn hχ) (hn hv)
    ((gradientFun_contMDiffAt g hχ).mdifferentiableAt (by simp))
    ((gradientFun_contMDiffAt g hv).mdifferentiableAt (by simp))

theorem cutoffHeatParametrix_residual_on_domain
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (N : ℕ) {t : ℝ} (ht : 0 < t)
    {q : M} (hq : q ∈ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))) :
    deriv (fun s => cutoffHeatParametrix g B χ N s q) t -
        laplacian (LeviCivita g) g (cutoffHeatParametrix g B χ N t) q =
      χ q * (deriv (fun s => heatParametrix g B N s q) t -
        laplacian (LeviCivita g) g (heatParametrix g B N t) q) -
        heatParametrix g B N t q * laplacian (LeviCivita g) g χ q -
        2 * g.inner q (gradientFun g χ q) (gradientFun g (heatParametrix g B N t) q) := by
  have hv := (contMDiffOn_heatParametrix B N t q hq).contMDiffAt
    ((isOpen_heatParametrixLocalDomain B).mem_nhds hq)
  have hd := ((hasDerivAt_heatParametrix B N q ht).const_mul (χ q)).deriv
  have h0 := (hasDerivAt_heatParametrix B N q ht).deriv
  have hl := laplacian_mul_of_contMDiffAt (g := g) hχ.contMDiffAt hv
  change deriv (fun s => χ q * heatParametrix g B N s q) t -
    laplacian (LeviCivita g) g (fun y => χ y * heatParametrix g B N t y) q = _
  rw [hd, hl, h0]
  ring

theorem cutoffHeatParametrix_residual_at_exp
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ) (N : ℕ) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source)
    {t : ℝ} (ht : 0 < t) :
    let q := expMapIntrinsic g hEnorm p (show TangentSpace I p from x)
    deriv (fun s => cutoffHeatParametrix g B χ N s q) t -
        laplacian (LeviCivita g) g (cutoffHeatParametrix g B χ N t) q =
      -χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p N) q -
        heatParametrix g B N t q * laplacian (LeviCivita g) g χ q -
        2 * g.inner q (gradientFun g χ q) (gradientFun g (heatParametrix g B N t) q) := by
  let q := expMapIntrinsic g hEnorm p (show TangentSpace I p from x)
  have hqB : q ∈ B.dom := by
    rw [show q = B.hom x from B.hom_eq hB]
    exact B.hom.map_source hB
  have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p hx
  have hqexp : expMapDiffeo g p x = q := by
    rw [expMapDiffeo_apply_eq g p hsrc]
    exact congrFun (expMap_eq_expMapIntrinsic g hEnorm p) _
  have hqC : q ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
    rw [← hqexp]
    refine ⟨(expMapDiffeo g p).map_source hsrc, ?_⟩
    change normalChartAt g p (expMapDiffeo g p x) ∈ Metric.ball 0 (expMapC2Radius g p)
    have hinv : normalChartAt g p (expMapDiffeo g p x) = x :=
      (expMapDiffeo g p).left_inv hsrc
    rw [hinv]
    simpa using hx
  have h := cutoffHeatParametrix_residual_on_domain B hχ N ht ⟨hqB, hqC⟩
  dsimp only at h ⊢
  rw [heatParametrix_residual B N hx hB ht] at h
  exact h.trans (by ring)

theorem exists_heatParametrix_cutoff_in
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (hB : (0 : E) ∈ B.hom.source)
    {V : Set M} (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      χ =ᶠ[nhds p] 1 ∧
      tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))) ∩
        (B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) ∩ V ∧
      Set.range χ ⊆ Set.Icc 0 1 := by
  have hpU := centre_mem_heatParametrixLocalDomain B hB
  have hz : B.inv p = 0 := by
    have hinv := B.left_inv hB
    simpa only [map_zero, expMapIntrinsic_zero] using hinv
  have hsmall : p ∈ B.dom ∩ B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
    refine ⟨hpU.1, ?_⟩
    change B.inv p ∈ Metric.ball 0 (expMapC2Radius g p)
    rw [hz]
    simpa using Geometry.Riemannian.expMapC2Radius_pos g p
  have hopen : IsOpen (heatParametrixLocalDomain B ∩
      B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) ∩ V) := by
    have hh : IsOpen (B.dom ∩ B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
      B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target Metric.isOpen_ball
    have hh' : IsOpen (heatParametrixLocalDomain B ∩
        (B.dom ∩ B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))) :=
      (isOpen_heatParametrixLocalDomain B).inter hh
    have heq : heatParametrixLocalDomain B ∩
        (B.dom ∩ B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) =
      heatParametrixLocalDomain B ∩ B.inv ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
      ext q
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, h.1.1, h.2⟩
    rw [heq] at hh'
    exact hh'.inter hV
  obtain ⟨χ, hχ, hc, h1, hs, hb⟩ := DifferentialGeometry.Analysis.exists_mfd_bump
    (I := I) (K := {p}) isCompact_singleton hopen
    (singleton_subset_iff.mpr ⟨⟨hpU, hsmall.2⟩, hpV⟩)
  refine ⟨χ, hχ, hc, ?_, hs, hb⟩
  simpa only [nhdsSet_singleton] using h1

theorem cutoffHeatParametrix_residual_eq_zero_of_notMem_tsupport
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)))) (N : ℕ) (t : ℝ)
    {q : M} (hq : q ∉ tsupport χ) :
    deriv (fun s => cutoffHeatParametrix g B χ N s q) t -
      laplacian (LeviCivita g) g (cutoffHeatParametrix g B χ N t) q = 0 := by
  have he : χ =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
  have hz : χ q = 0 := he.eq_of_nhds
  have hf : cutoffHeatParametrix g B χ N t =ᶠ[nhds q] (fun _ => 0) := by
    filter_upwards [he] with y hy
    change χ y * heatParametrix g B N t y = 0
    rw [show χ y = 0 from hy, zero_mul]
  have hl := laplacian_congr_of_eventuallyEq (LeviCivita g) g
    (contMDiff_cutoffHeatParametrix B hχ hs N t).contMDiffAt contMDiffAt_const hf
  have htime : (fun s => cutoffHeatParametrix g B χ N s q) = (fun _ => 0) := by
    funext s
    change χ q * heatParametrix g B N s q = 0
    rw [hz, zero_mul]
  rw [htime, hl]
  simp only [deriv_const, laplacian_const, sub_self]

theorem cutoffHeatParametrix_residual
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))))
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    (N : ℕ) {t : ℝ} (ht : 0 < t) (q : M) :
    deriv (fun s => cutoffHeatParametrix g B χ N s q) t -
        laplacian (LeviCivita g) g (cutoffHeatParametrix g B χ N t) q =
      -χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p N) q -
        heatParametrix g B N t q * laplacian (LeviCivita g) g χ q -
        2 * g.inner q (gradientFun g χ q) (gradientFun g (heatParametrix g B N t) q) := by
  by_cases hq : q ∈ tsupport χ
  · have hqB := (hs hq).1
    have hx := B.hom.map_target hqB
    have h := cutoffHeatParametrix_residual_at_exp B hχ N (hsmall q hq) hx ht
    have he : expMapIntrinsic g hEnorm p (show TangentSpace I p from B.inv q) = q :=
      B.right_inv hqB
    have hinner := congrArg (fun z : M =>
      g.inner z (gradientFun g χ z) (gradientFun g (heatParametrix g B N t) z)) he
    simpa only [he, hinner] using h
  · rw [cutoffHeatParametrix_residual_eq_zero_of_notMem_tsupport B hχ hs N t hq]
    have he : χ =ᶠ[nhds q] 0 := notMem_tsupport_iff_eventuallyEq.mp hq
    have hz : χ q = 0 := he.eq_of_nhds
    have hgrad : gradientFun g χ q = 0 := by
      apply gradientFun_eq_zero_of_mfderiv_eq_zero
      rw [he.mfderiv_eq]
      exact mfderiv_const
    have hl := laplacian_congr_of_eventuallyEq (LeviCivita g) g hχ.contMDiffAt
      contMDiffAt_const he
    have hlzero : laplacian (LeviCivita g) g χ q = 0 := by
      calc
        _ = laplacian (LeviCivita g) g (fun _ : M => (0 : ℝ)) q := hl
        _ = 0 := laplacian_const (LeviCivita g) g 0 q
    have hi : g.inner q (gradientFun g χ q)
        (gradientFun g (heatParametrix g B N t) q) = 0 := by
      rw [hgrad]
      exact map_zero (g.inner q) |>.symm ▸ rfl
    rw [hz, hlzero, hi]
    ring

def cutoffHeatParametrixResidual (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm g} {p : M} (B : ExponentialInverseBranch g hEnorm p)
    (χ : M → ℝ) (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  -χ q * (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
    laplacian (LeviCivita g) g (heatParametrixCoefficient g p N) q -
    heatParametrix g B N t q * laplacian (LeviCivita g) g χ q -
    2 * g.inner q (gradientFun g χ q) (gradientFun g (heatParametrix g B N t) q)

theorem cutoffHeatParametrix_isHeatForcedOnStationary
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {χ : M → ℝ}
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (B.dom ∩ ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))))
    (hsmall : ∀ q ∈ tsupport χ, ‖B.inv q‖ < expMapC2Radius g p)
    (N : ℕ) (D : Geometry.Curvature.RealTimeInterval) (hD : D.carrier ⊆ Ioi 0) :
    Parabolic.IsHeatForcedOnStationary D g
      (cutoffHeatParametrixResidual g B χ N) (cutoffHeatParametrix g B χ N) where
  jointSmooth := (contMDiffOn_cutoffHeatParametrix_joint B hχ hs N).mono
    (prod_mono (D.regular_subset.trans hD) Subset.rfl)
  jointCont := (contMDiffOn_cutoffHeatParametrix_joint B hχ hs N).continuousOn.mono
    (prod_mono hD Subset.rfl)
  sliceSmooth t _ := contMDiff_cutoffHeatParametrix B hχ hs N t
  equation t ht q := by
    have htpos := hD (D.regular_subset ht)
    have hd := (hasDerivAt_heatParametrix B N q htpos).const_mul (χ q)
    have hder : HasDerivAt (fun s => cutoffHeatParametrix g B χ N s q)
        (deriv (fun s => cutoffHeatParametrix g B χ N s q) t) t :=
      hd.differentiableAt.hasDerivAt
    apply hder.congr_deriv
    have hres := cutoffHeatParametrix_residual B hχ hs hsmall N htpos q
    change deriv (fun s => cutoffHeatParametrix g B χ N s q) t =
      laplacian (LeviCivita g) g (cutoffHeatParametrix g B χ N t) q +
        cutoffHeatParametrixResidual g B χ N t q
    dsimp only [cutoffHeatParametrixResidual]
    exact sub_eq_iff_eq_add'.mp hres

end DifferentialGeometry.Analysis.HeatEquation
