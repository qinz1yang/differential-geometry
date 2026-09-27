import DifferentialGeometry.Analysis.Heat.Parametrix.BranchTransport
import DifferentialGeometry.Geometry.Exponential.BranchEnergy
import DifferentialGeometry.Geometry.Operator.LaplacianExponential
import DifferentialGeometry.Geometry.Operator.LaplacianLinearity

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch

open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

private theorem hasDerivAt_gaussian_power (d e a : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (4 * Real.pi * s) ^ (-d / 2) *
      Real.exp (-e / (2 * s)) * s ^ k * a)
      ((4 * Real.pi * t) ^ (-d / 2) * Real.exp (-e / (2 * t)) *
        ((e / (2 * t ^ 2) - d / (2 * t)) * t ^ k + (k : ℝ) * t ^ (k - 1)) * a) t := by
  have ht0 := ht.ne'
  have hbase : 4 * Real.pi * t ≠ 0 := by positivity
  have hn := ((hasDerivAt_id t).const_mul (4 * Real.pi)).rpow_const
    (p := -d / 2) (Or.inl hbase)
  have he := ((hasDerivAt_const t (-e)).div
    ((hasDerivAt_id t).const_mul 2) (mul_ne_zero (by norm_num) ht0)).exp
  apply (((hn.mul he).mul ((hasDerivAt_id t).pow k)).mul_const a).congr_deriv
  simp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.pow_apply, mul_one]
  rw [Real.rpow_sub_one hbase]
  field_simp
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem laplacian_const_mul_of_contMDiffAt
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} {q : M}
    (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f q) (c : ℝ) :
    laplacian (LeviCivita g) g (fun y => c * f y) q = c * laplacian (LeviCivita g) g f q := by
  exact laplacian_smul_at (LeviCivita g) g c
    (((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hf).mono
      fun y hy => hy.mdifferentiableAt (by norm_num))
    ((gradientFun_contMDiffAt_one g hf).mdifferentiableAt one_ne_zero)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

def heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) (t : ℝ) (q : M) : ℝ :=
  (4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
    Real.exp (-branchEnergy g B q / (2 * t)) *
    ∑ k ∈ Finset.range (N + 1), t ^ k *
      heatParametrixCoefficientInCoordinates g B.hom B.inv
        (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k q

theorem hasDerivAt_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) (N : ℕ) (q : M) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => B.heatParametrix N s q)
      ((4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) *
        ((branchEnergy g B q / (2 * t ^ 2) - (Module.finrank ℝ E : ℝ) / (2 * t)) *
          (∑ k ∈ Finset.range (N + 1), t ^ k *
            heatParametrixCoefficientInCoordinates g B.hom B.inv
              (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k q) +
          ∑ k ∈ Finset.range (N + 1), (k : ℝ) * t ^ (k - 1) *
            heatParametrixCoefficientInCoordinates g B.hom B.inv
              (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) k q)) t := by
  let a := heatParametrixCoefficientInCoordinates g B.hom B.inv
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0)
  have hd := HasDerivAt.sum (u := Finset.range (N + 1)) (fun k _ =>
    hasDerivAt_gaussian_power (Module.finrank ℝ E) (branchEnergy g B q) (a k q) k ht)
  have hfun : (∑ k ∈ Finset.range (N + 1), fun s : ℝ =>
      (4 * Real.pi * s) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * s)) * s ^ k * a k q) =
      fun s => B.heatParametrix N s q := by
    funext s
    simp only [Finset.sum_apply, heatParametrix, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [a]
    ring
  rw [hfun] at hd
  apply hd.congr_deriv
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [a]
  ring

theorem contMDiffOn_heatParametrix
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    (N : ℕ) (t : ℝ) :
    ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (B.heatParametrix N t) (B.dom ∩ B.inv ⁻¹' U) := by
  apply ContMDiffOn.mul
  · apply contMDiffOn_const.mul
    apply Real.contDiff_exp.contMDiff.comp_contMDiffOn
    exact ((contMDiffOn_branchEnergy B).mono inter_subset_left).neg.div_const (2 * t)
  · intro q hq
    exact ContMDiffWithinAt.sum fun k _ => contMDiffWithinAt_const.mul
      (B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k q hq)

private theorem laplacian_gaussian_mul
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {q : M} (hq : q ∈ B.dom)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f q) (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    laplacian (LeviCivita g) g (fun y => c * (Real.exp (-branchEnergy g B y / (2 * t)) * f y)) q =
      c * Real.exp (-branchEnergy g B q / (2 * t)) *
        (laplacian (LeviCivita g) g f q -
          g.inner q (gradientFun g (branchEnergy g B) q) (gradientFun g f q) / t +
          (branchEnergy g B q / (2 * t ^ 2) -
            laplacian (LeviCivita g) g (branchEnergy g B) q / (2 * t)) * f q) := by
  let b : ℝ := -(2 * t)⁻¹
  have he : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (branchEnergy g B) q :=
    ((contMDiffOn_branchEnergy B q hq).contMDiffAt
      (B.hom.open_target.mem_nhds hq)).of_le ENat.LEInfty.out
  have hb : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (fun y => b * branchEnergy g B y) q :=
    contMDiffAt_const.mul he
  have hform (y : M) : -branchEnergy g B y / (2 * t) = b * branchEnergy g B y := by
    dsimp only [b]
    ring
  simp_rw [hform]
  have hprod : ContMDiffAt I 𝓘(ℝ, ℝ) 2
      (fun y => Real.exp (b * branchEnergy g B y) * f y) q :=
    (Real.contDiff_exp.contMDiff.contMDiffAt.comp q hb).mul hf
  rw [laplacian_const_mul_of_contMDiffAt g hprod c,
    laplacian_exp_mul (LeviCivita g) g hb hf,
    laplacian_const_mul_of_contMDiffAt g he b]
  have hg : gradientFun g (fun y => b * branchEnergy g B y) q =
      b • gradientFun g (branchEnergy g B) q :=
    gradientFun_const_smul g b (he.mdifferentiableAt (by norm_num))
  rw [hg]
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [branchEnergy_eikonal B hq]
  dsimp only [b]
  field_simp
  ring

theorem heatParametrix_residual
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {p : M}
    (B : ExponentialInverseBranch g hEnorm p) {U : Set E}
    (hU : IsOpen U) (hstar : StarConvex ℝ 0 U) (hsub : U ⊆ B.hom.source)
    (N : ℕ) {q : M} (hq : q ∈ B.dom ∩ B.inv ⁻¹' U) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => B.heatParametrix N s q) t -
        laplacian (LeviCivita g) g (B.heatParametrix N t) q =
      -(4 * Real.pi * t) ^ (-(Module.finrank ℝ E : ℝ) / 2) *
        Real.exp (-branchEnergy g B q / (2 * t)) * t ^ N *
        laplacian (LeviCivita g) g
          (heatParametrixCoefficientInCoordinates g B.hom B.inv
            (fun v => paramDensity g B.hom v / paramDensity g B.hom 0) N) q := by
  let a := heatParametrixCoefficientInCoordinates g B.hom B.inv
    (fun v => paramDensity g B.hom v / paramDensity g B.hom 0)
  let e := branchEnergy g B
  let d : ℝ := Module.finrank ℝ E
  let c : ℝ := (4 * Real.pi * t) ^ (-d / 2)
  let L : ℕ → ℝ := fun k => laplacian (LeviCivita g) g (a k) q
  let R : ℕ → ℝ := fun k => g.inner q (gradientFun g e q) (gradientFun g (a k) q)
  let F : ℕ → ℝ → M → ℝ := fun k s y =>
    (4 * Real.pi * s) ^ (-d / 2) * Real.exp (-e y / (2 * s)) * s ^ k * a k y
  have hV : IsOpen (B.dom ∩ B.inv ⁻¹' U) :=
    B.inv_contMDiffOn.continuousOn.isOpen_inter_preimage B.hom.open_target hU
  have ha (k : ℕ) : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (a k) q :=
    ((B.contMDiffOn_heatParametrixCoefficientInCoordinates hU hstar hsub k q hq).contMDiffAt
      (hV.mem_nhds hq)).of_le ENat.LEInfty.out
  have he : ContMDiffAt I 𝓘(ℝ, ℝ) 2 e q :=
    ((contMDiffOn_branchEnergy B q hq.1).contMDiffAt
      (B.hom.open_target.mem_nhds hq.1)).of_le ENat.LEInfty.out
  have hF (k : ℕ) : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (F k t) q :=
    ((contMDiffAt_const.mul (Real.contDiff_exp.contMDiff.contMDiffAt.comp q
      (he.neg.div_const (2 * t)))).mul contMDiffAt_const).mul (ha k)
  have hD (k : ℕ) : HasDerivAt (fun s => F k s q)
      (c * Real.exp (-e q / (2 * t)) *
        ((e q / (2 * t ^ 2) - d / (2 * t)) * t ^ k + (k : ℝ) * t ^ (k - 1)) * a k q) t :=
    hasDerivAt_gaussian_power d (e q) (a k q) k ht
  have hL (k : ℕ) : laplacian (LeviCivita g) g (F k t) q =
      c * Real.exp (-e q / (2 * t)) * t ^ k *
        (L k - R k / t + (e q / (2 * t ^ 2) - laplacian (LeviCivita g) g e q / (2 * t)) * a k q) := by
    have hfun : F k t = fun y => (c * t ^ k) * (Real.exp (-e y / (2 * t)) * a k y) := by
      funext y
      dsimp only [F, c]
      ring
    rw [hfun, laplacian_gaussian_mul B hq.1 (ha k) (c * t ^ k) ht.ne']
    dsimp only [L, R, e]
    ring
  have htransport (k : ℕ) : R k + ((k : ℝ) +
      (laplacian (LeviCivita g) g e q - d) / 2) * a k q =
      match k with | 0 => 0 | j + 1 => L j := by
    have hqexp : expMapIntrinsic g hEnorm p (show TangentSpace I p from B.inv q) = q :=
      B.right_inv hq.1
    have hk : MDifferentiableAt I 𝓘(ℝ, ℝ) (a k)
        (expMapIntrinsic g hEnorm p (show TangentSpace I p from B.inv q)) := by
      rw [hqexp]
      exact (ha k).mdifferentiableAt (by norm_num)
    have hd := hasDerivAt_comp_intrinsicGeodesic B
      (u := (show TangentSpace I p from B.inv q)) (B.hom.map_target hq.1) hk
    have h := B.heatParametrixCoefficientInCoordinates_transport hU hstar hsub k hq.2
    change deriv (fun s => a k (intrinsicGeodesic g hEnorm p
      (show TangentSpace I p from B.inv q) s)) 1 + _ = _ at h
    rw [hd.deriv, hqexp] at h
    rw [g.symm q (gradientFun g (a k) q) (gradientFun g e q)] at h
    exact h
  let P : ℕ → ℝ := fun k => match k with | 0 => 0 | j + 1 => t ^ j * L j
  have hterm (k : ℕ) : deriv (fun s => F k s q) t - laplacian (LeviCivita g) g (F k t) q =
      c * Real.exp (-e q / (2 * t)) * (P k - P (k + 1)) := by
    rw [(hD k).deriv, hL k]
    have hstep : t ^ k / t * (match k with | 0 => 0 | j + 1 => L j) = P k := by
      cases k with
      | zero => simp [P]
      | succ k => simp only [P, pow_succ]; field_simp
    have hp : (k : ℝ) * t ^ (k - 1) = (k : ℝ) * t ^ k / t := by
      cases k with
      | zero => simp
      | succ k => simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    rw [hp]
    rw [← hstep, ← htransport k]
    change _ = c * Real.exp (-e q / (2 * t)) * (_ - t ^ k * L k)
    have ht0 := ht.ne'
    field_simp
    ring
  have hsum (s : ℝ) : B.heatParametrix N s = fun y => ∑ k ∈ Finset.range (N + 1), F k s y := by
    funext y
    simp only [heatParametrix, Finset.mul_sum, F, d, a]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have htime : (fun s => B.heatParametrix N s q) = fun s => ∑ k ∈ Finset.range (N + 1), F k s q := by
    funext s
    exact congrFun (hsum s) q
  have hderiv : deriv (fun s => ∑ k ∈ Finset.range (N + 1), F k s q) t =
      ∑ k ∈ Finset.range (N + 1), deriv (fun s => F k s q) t := by
    have hd := (HasDerivAt.sum (u := Finset.range (N + 1)) (fun k _ => hD k)).deriv
    have hfun : (∑ i ∈ Finset.range (N + 1), fun s => F i s q) =
        (fun s => ∑ i ∈ Finset.range (N + 1), F i s q) := by
      funext s
      simp only [Finset.sum_apply]
    rw [hfun] at hd
    simpa only [(hD _).deriv] using hd
  rw [htime, hderiv, hsum t, laplacian_finset_sum_at (LeviCivita g) g _
    (fun k _ => ((contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp (hF k)).mono
      fun y hy => hy.mdifferentiableAt (by norm_num))
    (fun k _ => (gradientFun_contMDiffAt_one g (hF k)).mdifferentiableAt one_ne_zero),
    ← Finset.sum_sub_distrib]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_range_sub']
  simp only [P, zero_sub]
  dsimp only [c, d, e, L, a]
  ring

end DifferentialGeometry.Geometry.Riemannian.Exponential.ExponentialInverseBranch
