import DifferentialGeometry.Analysis.Heat.Parametrix.BranchCutoff
import DifferentialGeometry.Analysis.Heat.Parametrix.ParameterCoefficientBounds
import DifferentialGeometry.Analysis.Calculus.ExponentialAsymptotics
import DifferentialGeometry.Geometry.Exponential.BranchCutoff

noncomputable section

open Bundle Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.HeatEquation
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection

private theorem gaussian_power_le {d e t : ℝ} (he : 0 ≤ e) (ht : 0 < t) (N : ℕ) :
    (4 * Real.pi * t) ^ (-d / 2) * Real.exp (-e / (2 * t)) * t ^ N ≤
      (4 * Real.pi) ^ (-d / 2) * t ^ ((N : ℝ) - d / 2) := by
  have hbase : 0 ≤ (4 * Real.pi * t) ^ (-d / 2) := Real.rpow_nonneg (by positivity) _
  have hexp : Real.exp (-e / (2 * t)) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr he) (by positivity))
  calc
    _ ≤ (4 * Real.pi * t) ^ (-d / 2) * 1 * t ^ N := by gcongr
    _ = _ := by
      rw [mul_one, Real.mul_rpow (by positivity) ht.le, mul_assoc,
        ← Real.rpow_natCast t N, ← Real.rpow_add ht]
      congr 2
      ring

private theorem abs_sum_pow_mul_le {T A t : ℝ} (ht : t ∈ Ioc 0 T) (hA : 0 ≤ A)
    (N : ℕ) (a : ℕ → ℝ) (ha : ∀ k ∈ Finset.range (N + 1), |a k| ≤ A) :
    |∑ k ∈ Finset.range (N + 1), t ^ k * a k| ≤
      A * (1 + ∑ k ∈ Finset.range (N + 1), |T| ^ k) := by
  have htT : |t| ≤ |T| := by rw [abs_of_pos ht.1]; exact ht.2.trans (le_abs_self T)
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), |t ^ k * a k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), |T| ^ k * A := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_pow]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg t) htT k) (ha k hk)
        (abs_nonneg _) (pow_nonneg (abs_nonneg T) k)
    _ = A * ∑ k ∈ Finset.range (N + 1), |T| ^ k := by rw [← Finset.sum_mul, mul_comm]
    _ ≤ _ := by nlinarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private theorem exists_cutoffHeatParametrixResidual_le_rpow_of_bounds
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) {P K : Set M} {χ : M → ℝ} (N : ℕ) (T A : ℝ)
    (hA : 0 ≤ A)
    (hsource : ∀ p ∈ P, ∀ q ∈ tsupport χ, ∃ S : Set E, IsOpen S ∧ StarConvex ℝ 0 S ∧
      S ⊆ (B.fixed p).hom.source ∧ q ∈ (B.fixed p).dom ∩ (B.fixed p).inv ⁻¹' S)
    (hχ : ∀ q ∈ tsupport χ, |χ q| ≤ A)
    (hlχ : ∀ q ∈ tsupport χ, |laplacian (LeviCivita g) g χ q| ≤ A)
    (hcoeff : ∀ k ∈ Finset.range (N + 1), ∀ p ∈ P, ∀ q ∈ tsupport χ,
      |heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
        (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k q| ≤ A ∧
      |laplacian (LeviCivita g) g
        (heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
          (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k) q| ≤ A ∧
      |g.inner q (gradientFun g χ q)
        (gradientFun g (heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
          (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k) q)| ≤ A ∧
      |g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g (B.fixed p)) q)| ≤ A)
    {b : ℝ} (hb : 0 < b) (hgap : ∀ p ∈ P, ∀ q ∈ K, b ≤ branchEnergy g (B.fixed p) q)
    (hvanish : ∀ q ∉ K, laplacian (LeviCivita g) g χ q = 0 ∧ gradientFun g χ q = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ P, ∀ t ∈ Ioc 0 T, ∀ q : M,
      |(B.fixed p).cutoffHeatParametrixResidual χ N t q| ≤
        C * t ^ ((N : ℝ) - (Module.finrank ℝ E : ℝ) / 2) := by
  let d : ℝ := Module.finrank ℝ E
  let r : ℝ := (N : ℝ) - d / 2
  let A' := A * (1 + ∑ k ∈ Finset.range (N + 1), |T| ^ k)
  have hAA' : A ≤ A' := by
    have hsum : 0 ≤ ∑ k ∈ Finset.range (N + 1), |T| ^ k :=
      Finset.sum_nonneg (fun k _ => pow_nonneg (abs_nonneg T) k)
    dsimp only [A']
    nlinarith
  obtain ⟨Ccomm, hCcomm, hcomm⟩ := Real.exists_gaussian_commutator_le_rpow d r T A' hb (hA.trans hAA')
  let Cmain := A * (4 * Real.pi) ^ (-d / 2) * A
  have hpref : 0 ≤ (4 * Real.pi) ^ (-d / 2) := Real.rpow_nonneg (by positivity) _
  have hCmain : 0 ≤ Cmain := mul_nonneg (mul_nonneg hA hpref) hA
  refine ⟨Cmain + Ccomm, add_nonneg hCmain hCcomm, ?_⟩
  intro p hp t ht q
  have htr : 0 ≤ t ^ r := Real.rpow_nonneg ht.1.le r
  by_cases hq : q ∈ tsupport χ
  · let a := heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
      (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0)
    let G := (4 * Real.pi * t) ^ (-d / 2) * Real.exp (-branchEnergy g (B.fixed p) q / (2 * t))
    have hG : 0 ≤ G := mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (by positivity) ht.1.le) _) (Real.exp_pos _).le
    have hN : N ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_self N)
    have hbound := hcoeff N hN p hp q hq
    have he : 0 ≤ branchEnergy g (B.fixed p) q := by
      change 0 ≤ (1 / 2 : ℝ) * g.inner p
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm ((B.fixed p).inv q))
        ((tangentSpaceModelContinuousLinearEquiv (I := I) p).symm ((B.fixed p).inv q))
      apply mul_nonneg (by norm_num)
      by_cases hv : (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm ((B.fixed p).inv q) = 0
      · simp only [hv, map_zero]; exact le_rfl
      · exact (g.pos p _ hv).le
    have hmain : |χ q * G * t ^ N * laplacian (LeviCivita g) g (a N) q| ≤ Cmain * t ^ r := by
      simp only [abs_mul, abs_of_nonneg hG, abs_pow, abs_of_pos ht.1]
      calc
        _ = |χ q| * (G * t ^ N) * |laplacian (LeviCivita g) g (a N) q| := by ring
        _ ≤ A * ((4 * Real.pi) ^ (-d / 2) * t ^ r) * A := by
          apply mul_le_mul _ hbound.2.1 (abs_nonneg _) (by positivity)
          exact mul_le_mul (hχ q hq) (gaussian_power_le (d := d) he ht.1 N)
            (mul_nonneg hG (pow_nonneg ht.1.le N)) hA
        _ = Cmain * t ^ r := by dsimp only [Cmain]; ring
    have hcommbound : |(B.fixed p).heatParametrix N t q * laplacian (LeviCivita g) g χ q +
        2 * g.inner q (gradientFun g χ q) (gradientFun g ((B.fixed p).heatParametrix N t) q)| ≤
        Ccomm * t ^ r := by
      by_cases hqK : q ∈ K
      · obtain ⟨S, hS, hstar, hsub, hqS⟩ := hsource p hp q hq
        rw [(B.fixed p).inner_gradient_heatParametrix hS hstar hsub hqS (gradientFun g χ q) N t]
        have ha : |∑ k ∈ Finset.range (N + 1), t ^ k * a k q| ≤ A' :=
          abs_sum_pow_mul_le ht hA N (fun k => a k q) (fun k hk => (hcoeff k hk p hp q hq).1)
        have hg : |∑ k ∈ Finset.range (N + 1), t ^ k *
            g.inner q (gradientFun g χ q) (gradientFun g (a k) q)| ≤ A' :=
          abs_sum_pow_mul_le ht hA N _ (fun k hk => (hcoeff k hk p hp q hq).2.2.1)
        exact hcomm t ht (branchEnergy g (B.fixed p) q)
          (∑ k ∈ Finset.range (N + 1), t ^ k * a k q)
          (∑ k ∈ Finset.range (N + 1), t ^ k *
            g.inner q (gradientFun g χ q) (gradientFun g (a k) q))
          (g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g (B.fixed p)) q))
          (laplacian (LeviCivita g) g χ q) (hgap p hp q hqK) ha hg
          (hbound.2.2.2.trans hAA') ((hlχ q hq).trans hAA')
      · obtain ⟨hl, hg⟩ := hvanish q hqK
        simpa only [hl, hg, map_zero, zero_apply, mul_zero, add_zero, abs_zero] using
          mul_nonneg hCcomm htr
    have heq : (B.fixed p).cutoffHeatParametrixResidual χ N t q =
        -(χ q * G * t ^ N * laplacian (LeviCivita g) g (a N) q) -
        ((B.fixed p).heatParametrix N t q * laplacian (LeviCivita g) g χ q +
          2 * g.inner q (gradientFun g χ q) (gradientFun g ((B.fixed p).heatParametrix N t) q)) := by
      dsimp only [ExponentialInverseBranch.cutoffHeatParametrixResidual, G, d, a]
      ring
    rw [heq]
    calc
      _ ≤ |χ q * G * t ^ N * laplacian (LeviCivita g) g (a N) q| +
          |(B.fixed p).heatParametrix N t q * laplacian (LeviCivita g) g χ q +
            2 * g.inner q (gradientFun g χ q) (gradientFun g ((B.fixed p).heatParametrix N t) q)| := by
        simpa only [abs_neg] using abs_sub
          (-(χ q * G * t ^ N * laplacian (LeviCivita g) g (a N) q)) _
      _ ≤ Cmain * t ^ r + Ccomm * t ^ r := add_le_add hmain hcommbound
      _ = _ := by ring
  · rw [(B.fixed p).cutoffHeatParametrixResidual_eq_zero_of_notMem_tsupport hq N t, abs_zero]
    exact mul_nonneg (add_nonneg hCmain hCcomm) htr

theorem exists_cutoffHeatParametrix_residual_le_rpow
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) (N : ℕ) (T : ℝ) :
    ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ IsCompact (closure U) ∧
      (∀ p ∈ closure U, (0 : E) ∈ (B.fixed p).hom.source) ∧
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
        (∀ p ∈ closure U, χ =ᶠ[nhds p] 1) ∧ range χ ⊆ Icc 0 1 ∧
        (∀ p ∈ closure U, ∀ q ∈ tsupport χ, ∃ S : Set E, IsOpen S ∧ StarConvex ℝ 0 S ∧
          S ⊆ (B.fixed p).hom.source ∧ q ∈ (B.fixed p).dom ∩ (B.fixed p).inv ⁻¹' S) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closure U, ∀ t ∈ Ioc 0 T, ∀ q : M,
          |deriv (fun s => (B.fixed p).cutoffHeatParametrix χ N s q) t -
            laplacian (LeviCivita g) g ((B.fixed p).cutoffHeatParametrix χ N t) q| ≤
              C * t ^ ((N : ℝ) - (Module.finrank ℝ E : ℝ) / 2) := by
  obtain ⟨V, hV, hcV, _, hb⟩ := B.exists_heatParametrixCoefficientInCoordinates_fixed_compact_bound
  obtain ⟨W, hW, hcW, _, hs⟩ := B.exists_starConvex_fixed_source_domain
  obtain ⟨U, hU, hcU, hUc, hzero, χ, hχ, hcχ, hχone, hsupport, hχrange,
      b, hbpos, K, _, _, hgap, hvanish⟩ :=
    B.exists_cutoff_uniform_energy_gap (LeviCivita g) (hV.inter hW) ⟨hcV, hcW⟩
  have hsource : ∀ p ∈ closure U, ∀ q ∈ tsupport χ, ∃ S : Set E, IsOpen S ∧ StarConvex ℝ 0 S ∧
      S ⊆ (B.fixed p).hom.source ∧ q ∈ (B.fixed p).dom ∩ (B.fixed p).inv ⁻¹' S := by
    intro p hp q hq
    obtain ⟨S, hS, hstar, hsub, hinv⟩ := hs (p, q) (hsupport ⟨hp, hq⟩).2.2
    exact ⟨S, hS, hstar, hsub, (hsupport ⟨hp, hq⟩).1, hinv⟩
  have hbounds (k : ℕ) := hb χ hχ k (closure U ×ˢ tsupport χ) (hUc.prod hcχ)
    (fun z hz => (hsupport hz).2.1)
  choose C hC hbound using hbounds
  obtain ⟨D, hD⟩ := hcχ.exists_bound_of_continuousOn
    (contMDiff_laplacian_leviCivita g hχ).continuous.continuousOn
  let A := max 1 (max D (∑ k ∈ Finset.range (N + 1), C k))
  have hA : 0 ≤ A := zero_le_one.trans (le_max_left _ _)
  have hCA (k : ℕ) (hk : k ∈ Finset.range (N + 1)) : C k ≤ A :=
    (Finset.single_le_sum (fun j _ => hC j) hk).trans
      ((le_max_right D _).trans (le_max_right 1 _))
  have hχA : ∀ q ∈ tsupport χ, |χ q| ≤ A := by
    intro q _
    have hq := hχrange (mem_range_self q)
    have hqabs : |χ q| ≤ 1 := by simpa only [abs_of_nonneg hq.1] using hq.2
    exact hqabs.trans (le_max_left _ _)
  have hlχA : ∀ q ∈ tsupport χ, |laplacian (LeviCivita g) g χ q| ≤ A := by
    intro q hq
    exact (show |laplacian (LeviCivita g) g χ q| ≤ D from
      (by simpa only [Real.norm_eq_abs] using hD q hq)).trans
        ((le_max_left D _).trans (le_max_right 1 _))
  have hcoeff : ∀ k ∈ Finset.range (N + 1), ∀ p ∈ closure U, ∀ q ∈ tsupport χ,
      |heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
        (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k q| ≤ A ∧
      |laplacian (LeviCivita g) g
        (heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
          (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k) q| ≤ A ∧
      |g.inner q (gradientFun g χ q)
        (gradientFun g (heatParametrixCoefficientInCoordinates g (B.fixed p).hom (B.fixed p).inv
          (fun v => paramDensity g (B.fixed p).hom v / paramDensity g (B.fixed p).hom 0) k) q)| ≤ A ∧
      |g.inner q (gradientFun g χ q) (gradientFun g (branchEnergy g (B.fixed p)) q)| ≤ A := by
    intro k hk p hp q hq
    obtain ⟨ha, hl, hg, he⟩ := hbound k (p, q) ⟨hp, hq⟩
    exact ⟨ha.trans (hCA k hk), hl.trans (hCA k hk), hg.trans (hCA k hk), he.trans (hCA k hk)⟩
  obtain ⟨Cres, hCres, hres⟩ := exists_cutoffHeatParametrixResidual_le_rpow_of_bounds B N T A hA
    hsource hχA hlχA hcoeff hbpos hgap hvanish
  refine ⟨U, hU, hcU, hUc, hzero, χ, hχ, hcχ, hχone, hχrange, hsource, Cres, hCres, ?_⟩
  intro p hp t ht q
  rw [(B.fixed p).cutoffHeatParametrix_residual (hχ.of_le ENat.LEInfty.out) (hsource p hp) N ht.1 q]
  exact hres p hp t ht q

theorem exists_cutoffHeatParametrix_residual_le_mul_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm g} {c : M}
    (B : DiagonalInverseBranch g hEnorm c) (hn : Module.finrank ℝ E = 2) (T : ℝ) :
    ∃ U : Set M, IsOpen U ∧ c ∈ U ∧ IsCompact (closure U) ∧
      (∀ p ∈ closure U, (0 : E) ∈ (B.fixed p).hom.source) ∧
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
        (∀ p ∈ closure U, χ =ᶠ[nhds p] 1) ∧ range χ ⊆ Icc 0 1 ∧
        (∀ p ∈ closure U, ∀ q ∈ tsupport χ, ∃ S : Set E, IsOpen S ∧ StarConvex ℝ 0 S ∧
          S ⊆ (B.fixed p).hom.source ∧ q ∈ (B.fixed p).dom ∩ (B.fixed p).inv ⁻¹' S) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ closure U, ∀ t ∈ Ioc 0 T, ∀ q : M,
          |deriv (fun s => (B.fixed p).cutoffHeatParametrix χ 2 s q) t -
            laplacian (LeviCivita g) g ((B.fixed p).cutoffHeatParametrix χ 2 t) q| ≤
              C * t := by
  have h := B.exists_cutoffHeatParametrix_residual_le_rpow 2 T
  simpa only [hn, Nat.cast_ofNat, show (2 : ℝ) - 2 / 2 = 1 by norm_num, Real.rpow_one] using h

end DifferentialGeometry.Geometry.Riemannian.Exponential.DiagonalInverseBranch
