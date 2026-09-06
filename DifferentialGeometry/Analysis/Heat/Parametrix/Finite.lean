import DifferentialGeometry.Analysis.Heat.Parametrix.Transport
import DifferentialGeometry.Geometry.Exponential.BranchEnergy
import DifferentialGeometry.Geometry.Operator.LaplacianExponential
import DifferentialGeometry.Geometry.Operator.LaplacianLinearity

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

def heatParametrix (g : SmoothRiemannianMetric I M)
    {hEnorm : IsMetricNorm g} {p : M} (B : ExpInvBranch g hEnorm p)
    (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-branchEnergy g B q / (2 * t)) *
    ∑ k ∈ Finset.range (N + 1), t ^ k * heatParametrixCoefficient g p k q

theorem hasDerivAt_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) (q : M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => heatParametrix g B N s q)
      ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) *
        ((branchEnergy g B q / (2 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) *
          (∑ k ∈ Finset.range (N + 1), t ^ k * heatParametrixCoefficient g p k q) +
          ∑ k ∈ Finset.range (N + 1),
            (k : ℝ) * t ^ (k - 1) * heatParametrixCoefficient g p k q)) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hbase : 4 * Real.pi * t ≠ 0 := by positivity
  have hn := ((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
    (p := -(Module.finrank ℝ E : ℝ) / 2) (Or.inl hbase)
  have he := ((hasDerivAt_const t (-branchEnergy g B q)).div
    ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht0)).exp
  have hs : HasDerivAt
      (fun s => ∑ k ∈ Finset.range (N + 1), s ^ k * heatParametrixCoefficient g p k q)
      (∑ k ∈ Finset.range (N + 1),
        (k : ℝ) * t ^ (k - 1) * heatParametrixCoefficient g p k q) t := by
    have hsum := HasDerivAt.sum (u := Finset.range (N + 1))
      (fun k (_ : k ∈ Finset.range (N + 1)) =>
        ((hasDerivAt_id t).pow k).mul_const (heatParametrixCoefficient g p k q))
    convert! hsum using 1
    · ext s
      simp
    · simp only [id_eq, mul_one]
  apply ((hn.mul he).mul hs).congr_deriv
  simp only [id_eq, Pi.div_apply, Pi.mul_apply, mul_one]
  rw [Real.rpow_sub_one hbase]
  field_simp
  ring

theorem contMDiffOn_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) (t : ℝ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (heatParametrix g B N t)
      (B.dom ∩ ((normalChartAt g p).source ∩
        (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p))) := by
  apply ContMDiffOn.mul
  · apply contMDiffOn_const.mul
    apply Real.contDiff_exp.contMDiff.comp_contMDiffOn
    exact ((contMDiffOn_branchEnergy B).mono (fun _ h => h.1)).neg.div_const (2 * t)
  · intro q hq
    exact ContMDiffWithinAt.sum fun k _ => contMDiffWithinAt_const.mul
      ((contMDiffOn_heatParametrixCoefficient g p k).mono (fun _ h => h.2) q hq)

theorem laplacian_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) {t : ℝ} (ht : 0 < t) {q : M}
    (hqB : q ∈ B.dom)
    (hqC : q ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :
    laplacian (LeviCivita g) g (heatParametrix g B N t) q =
      (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) *
        ∑ k ∈ Finset.range (N + 1), t ^ k *
          (laplacian (LeviCivita g) g (heatParametrixCoefficient g p k) q -
            g.inner q (gradientFun g (branchEnergy g B) q)
              (gradientFun g (heatParametrixCoefficient g p k) q) / t +
            (branchEnergy g B q / (2 * t ^ 2) -
              laplacian (LeviCivita g) g (branchEnergy g B) q / (2 * t)) *
              heatParametrixCoefficient g p k q) := by
  let c : ℝ := (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2)
  let b : ℝ := -(2 * t)⁻¹
  let e := branchEnergy g B
  let a := heatParametrixCoefficient g p
  let F : ℕ → M → ℝ := fun k y => c * (Real.exp (b * e y) * (t ^ k * a k y))
  have hV : IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  have ha : ∀ k, ContMDiffAt I 𝓘(ℝ, ℝ) 2 (a k) q := fun k =>
    ((contMDiffOn_heatParametrixCoefficient g p k q hqC).contMDiffAt
      (hV.mem_nhds hqC)).of_le ENat.LEInfty.out
  have he : ContMDiffAt I 𝓘(ℝ, ℝ) 2 e q :=
    ((contMDiffOn_branchEnergy B q hqB).contMDiffAt
      (B.hom.open_target.mem_nhds hqB)).of_le ENat.LEInfty.out
  have hne {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f q) :
      ∀ᶠ y in 𝓝 q, MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf).mono
      fun y hy => hy.mdifferentiableAt (by norm_num)
  have hmd {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f q) :
      MDiffAt (T% fun y => gradientFun g f y) q :=
    (gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero
  have hbe : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => b * e y) q :=
    contMDiffAt_const.mul he
  have hexp : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => Real.exp (b * e y)) q :=
    Real.contDiff_exp.contMDiff.contMDiffAt.comp q hbe
  have htka (k : ℕ) : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => t ^ k * a k y) q :=
    contMDiffAt_const.mul (ha k)
  have hF (k : ℕ) : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (F k) q :=
    contMDiffAt_const.mul (hexp.mul (htka k))
  have heq : heatParametrix g B N t = fun y => ∑ k ∈ Finset.range (N + 1), F k y := by
    funext y
    dsimp only [heatParametrix, F, c, b, e, a]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show -(2 * t)⁻¹ * branchEnergy g B y = -branchEnergy g B y / (2 * t) by ring]
    ring
  rw [heq, laplacian_finset_sum_at (LeviCivita g) g _
    (fun k _ => hne (hF k)) (fun k _ => hmd (hF k)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have houter := laplacian_smul_at (LeviCivita g) g c
    (hne (hexp.mul (htka k))) (hmd (hexp.mul (htka k)))
  change laplacian (LeviCivita g) g (c • (fun y => Real.exp (b * e y) * (t ^ k * a k y))) q =
    c * laplacian (LeviCivita g) g (fun y => Real.exp (b * e y) * (t ^ k * a k y)) q at houter
  have hbeΔ := laplacian_smul_at (LeviCivita g) g b (hne he) (hmd he)
  have hkaΔ := laplacian_smul_at (LeviCivita g) g (t ^ k) (hne (ha k)) (hmd (ha k))
  have hbeGrad := gradientFun_const_smul g b (he.mdifferentiableAt (by norm_num))
  have hkaGrad := gradientFun_const_smul g (t ^ k) ((ha k).mdifferentiableAt (by norm_num))
  change laplacian (LeviCivita g) g (c • (fun y => Real.exp (b * e y) * (t ^ k * a k y))) q = _
  rw [houter, laplacian_exp_mul (LeviCivita g) g hbe (htka k)]
  change c * (Real.exp (b * e q) *
    (laplacian (LeviCivita g) g ((t ^ k) • a k) q +
      2 * g.inner q (gradientFun g (b • e) q) (gradientFun g ((t ^ k) • a k) q) +
      (laplacian (LeviCivita g) g (b • e) q +
        g.inner q (gradientFun g (b • e) q) (gradientFun g (b • e) q)) *
        (t ^ k * a k q))) = _
  rw [hbeΔ, hkaΔ, hbeGrad, hkaGrad]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [show g.inner q (gradientFun g e q) (gradientFun g e q) = 2 * e q from branchEnergy_eikonal B hqB]
  have hex : b * e q = -branchEnergy g B q / (2 * t) := by dsimp [b, e]; ring
  rw [hex]
  dsimp only [c, b, e, a]
  have ht0 : t ≠ 0 := ht.ne'
  field_simp
  ring

theorem heatParametrix_residual
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExpInvBranch g hEnorm p) (N : ℕ) {x : E}
    (hx : ‖x‖ < expMapC2Radius g p) (hB : x ∈ B.hom.source)
    {t : ℝ} (ht : 0 < t) :
    let q := expMapIntrinsic g hEnorm p (show TangentSpace I p from x)
    deriv (fun s => heatParametrix g B N s q) t -
        laplacian (LeviCivita g) g (heatParametrix g B N t) q =
      -(4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
        laplacian (LeviCivita g) g (heatParametrixCoefficient g p N) q := by
  let q := expMapIntrinsic g hEnorm p (show TangentSpace I p from x)
  change deriv (fun s => heatParametrix g B N s q) t -
    laplacian (LeviCivita g) g (heatParametrix g B N t) q = _
  have ht0 : t ≠ 0 := ht.ne'
  have hqB : q ∈ B.dom := by
    rw [show q = B.hom x from B.hom_eq hB]
    exact B.hom.map_source hB
  have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius g p hx
  have hqexp : expMapDiffeo g p x = q := by
    rw [expMapDiffeo_apply_eq g p hsrc]
    exact exp_eq_intr_of_c2 g hEnorm p hx
  have hqC : q ∈ (normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p) := by
    rw [← hqexp]
    refine ⟨(expMapDiffeo g p).map_source hsrc, ?_⟩
    change normalChartAt g p (expMapDiffeo g p x) ∈ Metric.ball 0 (expMapC2Radius g p)
    have hinv : normalChartAt g p (expMapDiffeo g p x) = x := (expMapDiffeo g p).left_inv hsrc
    rw [hinv]
    simpa using hx
  have hV : IsOpen ((normalChartAt g p).source ∩
      (normalChartAt g p) ⁻¹' Metric.ball (0 : E) (expMapC2Radius g p)) :=
    (normalChartAt_contMDiffOn g p).continuousOn.isOpen_inter_preimage
      (normalChartAt g p).open_source Metric.isOpen_ball
  let C : ℕ → ℝ := fun k => heatParametrixCoefficient g p k q
  let L : ℕ → ℝ := fun k => laplacian (LeviCivita g) g (heatParametrixCoefficient g p k) q
  let R : ℕ → ℝ := fun k => g.inner q (gradientFun g (branchEnergy g B) q)
    (gradientFun g (heatParametrixCoefficient g p k) q)
  let e := branchEnergy g B q
  let d : ℝ := Module.finrank ℝ E
  let le := laplacian (LeviCivita g) g (branchEnergy g B) q
  have htransport (k : ℕ) : R k + ((k : ℝ) + (le - d) / 2) * C k =
      match k with | 0 => 0 | j + 1 => L j := by
    have hk : MDifferentiableAt I 𝓘(ℝ, ℝ) (heatParametrixCoefficient g p k) q :=
      ((contMDiffOn_heatParametrixCoefficient g p k q hqC).contMDiffAt
        (hV.mem_nhds hqC)).mdifferentiableAt (by simp)
    have hd := hasDerivAt_comp_intrinsicGeodesic B (u := (show TangentSpace I p from x)) hB hk
    have h := heatParametrixCoefficient_transport B k hx hB
    rw [hd.deriv] at h
    rw [g.symm q (gradientFun g (heatParametrixCoefficient g p k) q)
      (gradientFun g (branchEnergy g B) q)] at h
    exact h
  have hpow (k : ℕ) : (k : ℝ) * t ^ (k - 1) = (k : ℝ) * t ^ k / t := by
    cases k with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  have hsum :
      ((e / (2 * t ^ 2) - d / (2 * t)) *
        (∑ k ∈ Finset.range (N + 1), t ^ k * C k) +
        ∑ k ∈ Finset.range (N + 1), (k : ℝ) * t ^ (k - 1) * C k) -
      (∑ k ∈ Finset.range (N + 1), t ^ k *
        (L k - R k / t + (e / (2 * t ^ 2) - le / (2 * t)) * C k)) =
      ∑ k ∈ Finset.range (N + 1),
        (t ^ k / t * (match k with | 0 => 0 | j + 1 => L j) - t ^ k * L k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpow k, ← htransport k]
    field_simp
    ring
  have hcancel (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (t ^ k / t * (match k with | 0 => 0 | j + 1 => L j) - t ^ k * L k)) =
        -t ^ n * L n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [pow_succ]
      field_simp
      ring
  rw [(hasDerivAt_heatParametrix B N q ht).deriv,
    laplacian_heatParametrix B N ht hqB hqC, ← mul_sub]
  change (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
      Real.exp (-branchEnergy g B q / (2 * t)) *
      (((e / (2 * t ^ 2) - d / (2 * t)) *
        (∑ k ∈ Finset.range (N + 1), t ^ k * C k) +
        ∑ k ∈ Finset.range (N + 1), (k : ℝ) * t ^ (k - 1) * C k) -
      (∑ k ∈ Finset.range (N + 1), t ^ k *
        (L k - R k / t + (e / (2 * t ^ 2) - le / (2 * t)) * C k))) = _
  rw [hsum, hcancel N]
  ring

end DifferentialGeometry.Analysis.HeatEquation
