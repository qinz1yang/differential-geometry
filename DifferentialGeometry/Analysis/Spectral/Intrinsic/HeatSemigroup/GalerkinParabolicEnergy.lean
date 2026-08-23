import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Defs
import DifferentialGeometry.Analysis.ODE.EnergyHierarchy
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s₀ : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
lemma lambda_mul_tensorSobolevWeight
    (i : TensorEigenIdx (I := I) (M := M) g r s₀) (σ : ℝ) :
    TensorEigenIdx.lambda (I := I) (M := M) i *
        tensorSobolevWeight (I := I) (M := M) i σ =
      tensorSobolevWeight (I := I) (M := M) i (σ + 1) -
        tensorSobolevWeight (I := I) (M := M) i σ := by
  have hpos : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
    lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
  unfold tensorSobolevWeight
  rw [Real.rpow_add_one hpos.ne' σ]
  ring

noncomputable def galerkinEnergy
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ * (u t i) ^ 2

omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_nonneg
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) :
    0 ≤ galerkinEnergy (I := I) (M := M) s u σ t := by
  unfold galerkinEnergy
  refine Finset.sum_nonneg (fun i _ => ?_)
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) i σ
  positivity

omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_continuousOn
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {J : Set ℝ}
    (hu : ∀ i ∈ s, ContinuousOn (fun t => u t i) J) :
    ContinuousOn (galerkinEnergy (I := I) (M := M) s u σ) J := by
  unfold galerkinEnergy
  refine continuousOn_finset_sum s (fun i hi => ?_)
  exact continuousOn_const.mul ((hu i hi).pow 2)

omit [NeZero (Module.finrank ℝ E)] in
lemma galerkinEnergy_hasDerivWithinAt
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (du : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {t : ℝ}
    (hu : ∀ i ∈ s,
      HasDerivWithinAt (fun s => u s i) (du t i) (Set.Ici t) t) :
    HasDerivWithinAt (galerkinEnergy (I := I) (M := M) s u σ)
      (∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
        (2 * u t i * du t i)) (Set.Ici t) t := by
  unfold galerkinEnergy
  apply HasDerivWithinAt.fun_sum
  intro i hi
  have hsq : HasDerivWithinAt (fun s => (u s i) ^ 2)
      (2 * u t i ^ 1 * du t i) (Set.Ici t) t :=
    (hu i hi).fun_pow 2
  have := hsq.const_mul (tensorSobolevWeight (I := I) (M := M) i σ)
  simpa [pow_one] using this

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkinEnergy_deriv_identity
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (F : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) (t : ℝ) :
    (∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
        (2 * u t i *
          (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i))) =
      -2 * galerkinEnergy (I := I) (M := M) s u (σ + 1) t +
        2 * galerkinEnergy (I := I) (M := M) s u σ t +
        2 * ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ * (u t i * F t i) := by
  have hterm : ∀ i ∈ s,
      tensorSobolevWeight (I := I) (M := M) i σ *
          (2 * u t i * (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i)) =
        -2 * (tensorSobolevWeight (I := I) (M := M) i (σ + 1) * (u t i) ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * (u t i) ^ 2) +
          2 * (tensorSobolevWeight (I := I) (M := M) i σ * (u t i * F t i)) := by
    intro i _
    have halg := lambda_mul_tensorSobolevWeight (I := I) (M := M) i σ
    have hwσ1 : tensorSobolevWeight (I := I) (M := M) i (σ + 1) =
        TensorEigenIdx.lambda (I := I) (M := M) i *
          tensorSobolevWeight (I := I) (M := M) i σ +
          tensorSobolevWeight (I := I) (M := M) i σ := by linarith [halg]
    rw [hwσ1]; ring
  rw [Finset.sum_congr rfl hterm]
  unfold galerkinEnergy
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_add_distrib]

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkinEnergy_hasDerivWithinAt_ode
    (s : Finset (TensorEigenIdx (I := I) (M := M) g r s₀))
    (u : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ)
    (F : ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ) (σ : ℝ) {t : ℝ}
    (hu : ∀ i ∈ s,
      HasDerivWithinAt (fun s => u s i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i)
        (Set.Ici t) t) :
    HasDerivWithinAt (galerkinEnergy (I := I) (M := M) s u σ)
      (-2 * galerkinEnergy (I := I) (M := M) s u (σ + 1) t +
        2 * galerkinEnergy (I := I) (M := M) s u σ t +
        2 * ∑ i ∈ s, tensorSobolevWeight (I := I) (M := M) i σ *
          (u t i * F t i)) (Set.Ici t) t := by
  have hderiv := galerkinEnergy_hasDerivWithinAt (I := I) (M := M)
    s u (fun t i => -(TensorEigenIdx.lambda (I := I) (M := M) i) * u t i + F t i) σ hu
  have hid := galerkinEnergy_deriv_identity (I := I) (M := M) s u F σ t
  rwa [hid] at hderiv

theorem energy_hierarchy_explicit_bound
    {T c C : ℝ} {Mk Mk' : ℕ → ℝ → ℝ} {seed B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t)
    (hcont : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ -c * (Mk (k + 1) t) + C * (Mk k t) + seed k * Real.sqrt (Mk k t))
    (hinit : ∀ k, Mk k 0 ≤ B0 k) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mk k t ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := by
  intro k
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ r, Mk' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Mk k z - Mk k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ (C + 1) * Mk k t + (seed k) ^ 2 / 4 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hMt : 0 ≤ Mk k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ Mk (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (Mk (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (Mk (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : seed k * Real.sqrt (Mk k t) ≤ (seed k) ^ 2 / 4 + Mk k t :=
      mul_sqrt_le_sq_div_four_add (seed k) hMt
    nlinarith [hneg, hdiss', hyoung]
  intro t htIcc
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using hinit k) hbound
  have hKnn : (0 : ℝ) ≤ C + 1 := by linarith
  have hεnn : (0 : ℝ) ≤ (seed k) ^ 2 / 4 := by positivity
  have hB0nn : 0 ≤ B0 k :=
    le_trans (hMnonneg k 0 ⟨le_refl 0, htIcc.1.trans htIcc.2⟩) (hinit k)
  have hmono : gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) (t - 0) ≤
      gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := by
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    exact gronwallBound_mono (δ := B0 k) (K := C + 1) (ε := (seed k) ^ 2 / 4)
      hB0nn hεnn hKnn hle
  calc Mk k t ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) (C + 1) ((seed k) ^ 2 / 4) T := hmono

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem energy_hierarchy_explicit_bound_perScale
    {T c : ℝ} {C : ℕ → ℝ} {Mk Mk' : ℕ → ℝ → ℝ} {seed B0 : ℕ → ℝ}
    (hc : 0 < c) (hC : ∀ k, 0 ≤ C k)
    (hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t)
    (hcont : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ -c * (Mk (k + 1) t) + C k * (Mk k t) + seed k * Real.sqrt (Mk k t))
    (hinit : ∀ k, Mk k 0 ≤ B0 k) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mk k t ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by
  intro k
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ r, Mk' k t < r →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Mk k z - Mk k t) < r := by
    intro t ht r hr
    have := (hderiv k t ht).liminf_right_slope_le hr
    refine this.mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ (C k + 1) * Mk k t + (seed k) ^ 2 / 4 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hMt : 0 ≤ Mk k t := hMnonneg k t htIcc
    have hMt1 : 0 ≤ Mk (k + 1) t := hMnonneg (k + 1) t htIcc
    have hneg : -c * (Mk (k + 1) t) ≤ 0 := by
      have : 0 ≤ c * (Mk (k + 1) t) := mul_nonneg hc.le hMt1
      linarith
    have hdiss' := hdiss k t ht
    have hyoung : seed k * Real.sqrt (Mk k t) ≤ (seed k) ^ 2 / 4 + Mk k t :=
      mul_sqrt_le_sq_div_four_add (seed k) hMt
    nlinarith [hneg, hdiss', hyoung]
  intro t htIcc
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    (hcont k) hf' (by simpa using hinit k) hbound
  have hKnn : (0 : ℝ) ≤ C k + 1 := by linarith [hC k]
  have hεnn : (0 : ℝ) ≤ (seed k) ^ 2 / 4 := by positivity
  have hB0nn : 0 ≤ B0 k :=
    le_trans (hMnonneg k 0 ⟨le_refl 0, htIcc.1.trans htIcc.2⟩) (hinit k)
  have hmono : gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) (t - 0) ≤
      gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    exact gronwallBound_mono (δ := B0 k) (K := C k + 1) (ε := (seed k) ^ 2 / 4)
      hB0nn hεnn hKnn hle
  calc Mk k t ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) (t - 0) := hgron t htIcc
    _ ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := hmono

theorem energy_hier_l1_bound
    {T c Sbd : ℝ} {C : ℕ → ℝ} {Mk Mk' : ℕ → ℝ → ℝ} {seed B0 : ℕ → ℝ}
    {A S : ℝ → ℝ}
    (hc : 0 < c) (hC : ∀ k, 0 ≤ C k) (hseed : ∀ k, 0 ≤ seed k)
    (hS0 : S 0 = 0) (hSnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S t)
    (hScont : ContinuousOn S (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt S (A t) (Set.Ici t) t)
    (hSbd : ∀ t ∈ Set.Icc (0 : ℝ) T, S t ≤ Sbd)
    (hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t)
    (hcont : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t)
    (hdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Mk' k t ≤ -c * (Mk (k + 1) t) + (C k + A t) * (Mk k t) +
        seed k * Real.sqrt (Mk k t))
    (hinit : ∀ k, Mk k 0 ≤ B0 k) :
    ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mk k t ≤ Real.exp Sbd * gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by
  set Nk : ℕ → ℝ → ℝ := fun k t => Mk k t * Real.exp (-S t) with hNkdef
  set Nk' : ℕ → ℝ → ℝ :=
    fun k t => (Mk' k t - A t * Mk k t) * Real.exp (-S t) with hNk'def
  have hNnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Nk k t := by
    intro k t ht
    exact mul_nonneg (hMnonneg k t ht) (Real.exp_nonneg _)
  have hNcont : ∀ k, ContinuousOn (Nk k) (Set.Icc (0 : ℝ) T) := by
    intro k
    exact (hcont k).mul (Real.continuous_exp.comp_continuousOn hScont.neg)
  have hNderiv : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (Nk k) (Nk' k t) (Set.Ici t) t := by
    intro k t ht
    have hexp : HasDerivWithinAt (fun u => Real.exp (-S u))
        (Real.exp (-S t) * -A t) (Set.Ici t) t := ((hSderiv t ht).neg).exp
    have hmul := (hderiv k t ht).mul hexp
    have hEq : Mk' k t * Real.exp (-S t) + Mk k t * (Real.exp (-S t) * -A t) =
        Nk' k t := by
      simp only [hNk'def]; ring
    rwa [hEq] at hmul
  have hNdiss : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
      Nk' k t ≤ -c * (Nk (k + 1) t) + C k * (Nk k t) +
        seed k * Real.sqrt (Nk k t) := by
    intro k t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    set e : ℝ := Real.exp (-S t) with hedef
    have hepos : 0 < e := Real.exp_pos _
    have hele : e ≤ 1 := by
      rw [hedef, Real.exp_le_one_iff]
      linarith [hSnn t htIcc]
    have hMnn : 0 ≤ Mk k t := hMnonneg k t htIcc
    have hsqrt : Real.sqrt (Mk k t) * e ≤ Real.sqrt (Nk k t) := by
      have hsplit : Real.sqrt (Nk k t) = Real.sqrt (Mk k t) * Real.sqrt e := by
        simp only [hNkdef, ← hedef]
        exact Real.sqrt_mul hMnn e
      have hle : e ≤ Real.sqrt e := by
        have hsq : e ^ 2 ≤ e := by nlinarith
        calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq hepos.le).symm
          _ ≤ Real.sqrt e := Real.sqrt_le_sqrt hsq
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
    have hseedle : seed k * (Real.sqrt (Mk k t) * e) ≤ seed k * Real.sqrt (Nk k t) :=
      mul_le_mul_of_nonneg_left hsqrt (hseed k)
    have hbase := hdiss k t ht
    have hmul : (Mk' k t - A t * Mk k t) * e ≤
        (-c * (Mk (k + 1) t) + C k * (Mk k t) + seed k * Real.sqrt (Mk k t)) * e := by
      apply mul_le_mul_of_nonneg_right _ hepos.le
      linarith
    have hexpand : (-c * (Mk (k + 1) t) + C k * (Mk k t) +
        seed k * Real.sqrt (Mk k t)) * e =
        -c * (Nk (k + 1) t) + C k * (Nk k t) +
          seed k * (Real.sqrt (Mk k t) * e) := by
      simp only [hNkdef, ← hedef]; ring
    have hNk't : Nk' k t = (Mk' k t - A t * Mk k t) * e := by
      simp only [hNk'def, ← hedef]
    rw [hNk't]
    linarith [hmul, hexpand.le, hexpand.ge, hseedle]
  have hNinit : ∀ k, Nk k 0 ≤ B0 k := by
    intro k
    have : Nk k 0 = Mk k 0 := by simp [hNkdef, hS0]
    rw [this]; exact hinit k
  have hkey := energy_hierarchy_explicit_bound_perScale (c := c) (C := C)
    (Mk := Nk) (Mk' := Nk') (seed := seed) (B0 := B0)
    hc hC hNnonneg hNcont hNderiv hNdiss hNinit
  intro k t ht
  have hNle := hkey k t ht
  have hMeq : Mk k t = Nk k t * Real.exp (S t) := by
    simp only [hNkdef]
    rw [mul_assoc, ← Real.exp_add]
    simp
  rw [hMeq]
  calc Nk k t * Real.exp (S t) ≤ Nk k t * Real.exp Sbd :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hSbd t ht)) (hNnonneg k t ht)
    _ ≤ gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T * Real.exp Sbd :=
        mul_le_mul_of_nonneg_right hNle (Real.exp_nonneg _)
    _ = Real.exp Sbd * gronwallBound (B0 k) (C k + 1) ((seed k) ^ 2 / 4) T := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_energy_uniform_bound_perScale
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ₀ Cδ : ℝ} {Cmid seed B0 : ℕ → ℝ}
    (hCδ : Cδ < 2) (hCmid : ∀ k, 0 ≤ Cmid k)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          Cmid k * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          seed k *
            Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
    (hinit : ∀ (N : ℕ) (k : ℕ),
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) 0 ≤ B0 k) :
    ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t ≤ Bound := by
  set Mfam : ℕ → ℕ → ℝ → ℝ :=
    fun N k t => galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    with hMfam
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mfam N k t ≤ gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T := by
    intro N
    set Mk : ℕ → ℝ → ℝ := fun k t => Mfam N k t with hMk
    set Mk' : ℕ → ℝ → ℝ :=
      fun k t =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          2 * ∑ i ∈ sseq N,
            tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
              (U N t i * Fseq N t i)
      with hMk'
    have hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t := by
      intro k t _
      exact galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    have hcontk : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T) := by
      intro k
      exact galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N)
        (σ₀ + (k : ℝ)) (fun i hi => hcont N i hi)
    have hderivk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t := by
      intro k t ht
      exact galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N) (U N)
        (Fseq N) (σ₀ + (k : ℝ)) (fun i hi => hderiv N t ht i hi)
    have hdissk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        Mk' k t ≤ -(2 - Cδ) * (Mk (k + 1) t) + (Cmid k + 2) * (Mk k t) +
          seed k * Real.sqrt (Mk k t) := by
      intro k t ht
      have hcl := hclosure N k t ht
      have hMk1 : Mk (k + 1) t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t := by
        have hσ : σ₀ + ((k + 1 : ℕ) : ℝ) = σ₀ + (k : ℝ) + 1 := by push_cast; ring
        simp only [hMk, hMfam, hσ]
      have hMkk : Mk k t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t := by
        simp only [hMk, hMfam]
      rw [hMk', hMk1, hMkk]
      linarith [hcl]
    have hinitk : ∀ k, Mk k 0 ≤ B0 k := by
      intro k
      exact hinit N k
    have hc : (0 : ℝ) < 2 - Cδ := by linarith
    have hC : ∀ k, (0 : ℝ) ≤ Cmid k + 2 := by intro k; linarith [hCmid k]
    intro k t ht
    exact energy_hierarchy_explicit_bound_perScale (c := 2 - Cδ) (C := fun k => Cmid k + 2)
      (Mk := Mk) (Mk' := Mk') (seed := seed) (B0 := B0)
      hc hC hMnonneg hcontk hderivk hdissk hinitk k t ht
  refine fun k => ⟨gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T,
    fun N t ht => ?_⟩
  exact hkey N k t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_energy_uniform_bound
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ₀ Cδ Cmid : ℝ} {seed B0 : ℕ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          Cmid * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          seed k *
            Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
    (hinit : ∀ (N : ℕ) (k : ℕ),
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) 0 ≤ B0 k) :
    ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t ≤ Bound := by
  set Mfam : ℕ → ℕ → ℝ → ℝ :=
    fun N k t => galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    with hMfam
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mfam N k t ≤ gronwallBound (B0 k) (Cmid + 2 + 1) ((seed k) ^ 2 / 4) T := by
    intro N
    set Mk : ℕ → ℝ → ℝ := fun k t => Mfam N k t with hMk
    set Mk' : ℕ → ℝ → ℝ :=
      fun k t =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          2 * ∑ i ∈ sseq N,
            tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
              (U N t i * Fseq N t i)
      with hMk'
    have hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t := by
      intro k t _
      exact galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    have hcontk : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T) := by
      intro k
      exact galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N)
        (σ₀ + (k : ℝ)) (fun i hi => hcont N i hi)
    have hderivk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t := by
      intro k t ht
      exact galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N) (U N)
        (Fseq N) (σ₀ + (k : ℝ)) (fun i hi => hderiv N t ht i hi)
    have hdissk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        Mk' k t ≤ -(2 - Cδ) * (Mk (k + 1) t) + (Cmid + 2) * (Mk k t) +
          seed k * Real.sqrt (Mk k t) := by
      intro k t ht
      have hcl := hclosure N k t ht
      have hMk1 : Mk (k + 1) t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t := by
        have hσ : σ₀ + ((k + 1 : ℕ) : ℝ) = σ₀ + (k : ℝ) + 1 := by push_cast; ring
        simp only [hMk, hMfam, hσ]
      have hMkk : Mk k t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t := by
        simp only [hMk, hMfam]
      rw [hMk', hMk1, hMkk]
      linarith [hcl]
    have hinitk : ∀ k, Mk k 0 ≤ B0 k := by
      intro k
      exact hinit N k
    have hc : (0 : ℝ) < 2 - Cδ := by linarith
    have hC : (0 : ℝ) ≤ Cmid + 2 := by linarith
    intro k t ht
    exact energy_hierarchy_explicit_bound (c := 2 - Cδ) (C := Cmid + 2)
      (Mk := Mk) (Mk' := Mk') (seed := seed) (B0 := B0)
      hc hC hMnonneg hcontk hderivk hdissk hinitk k t ht
  refine fun k => ⟨gronwallBound (B0 k) (Cmid + 2 + 1) ((seed k) ^ 2 / 4) T,
    fun N t ht => ?_⟩
  exact hkey N k t ht

end Spectral
end Analysis
end DifferentialGeometry

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

variable {g : SmoothRiemannianMetric I M} {r s₀ : ℕ}

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_energy_l1_bound
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ₀ Cδ Sbd : ℝ} {Cmid seed B0 : ℕ → ℝ} {A S : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : ∀ k, 0 ≤ Cmid k) (hseed : ∀ k, 0 ≤ seed k)
    (hS0 : ∀ N, S N 0 = 0)
    (hSnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S N t)
    (hScont : ∀ N, ContinuousOn (S N) (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (S N) (A N t) (Set.Ici t) t)
    (hSbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, S N t ≤ Sbd)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun r => U N r i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ (N : ℕ) (k : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          (Cmid k + A N t) *
            galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          seed k *
            Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t))
    (hinit : ∀ (N : ℕ) (k : ℕ),
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) 0 ≤ B0 k) :
    ∀ k : ℕ, ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t ≤ Bound := by
  set Mfam : ℕ → ℕ → ℝ → ℝ :=
    fun N k t => galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    with hMfam
  have hkey : ∀ N, ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Mfam N k t ≤
        Real.exp Sbd * gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T := by
    intro N
    set Mk : ℕ → ℝ → ℝ := fun k t => Mfam N k t with hMk
    set Mk' : ℕ → ℝ → ℝ :=
      fun k t =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t +
          2 * ∑ i ∈ sseq N,
            tensorSobolevWeight (I := I) (M := M) i (σ₀ + (k : ℝ)) *
              (U N t i * Fseq N t i)
      with hMk'
    have hMnonneg : ∀ k, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Mk k t := by
      intro k t _
      exact galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t
    have hcontk : ∀ k, ContinuousOn (Mk k) (Set.Icc (0 : ℝ) T) := by
      intro k
      exact galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N)
        (σ₀ + (k : ℝ)) (fun i hi => hcont N i hi)
    have hderivk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (Mk k) (Mk' k t) (Set.Ici t) t := by
      intro k t ht
      exact galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N) (U N)
        (Fseq N) (σ₀ + (k : ℝ)) (fun i hi => hderiv N t ht i hi)
    have hdissk : ∀ k, ∀ t ∈ Set.Ico (0 : ℝ) T,
        Mk' k t ≤ -(2 - Cδ) * (Mk (k + 1) t) + ((Cmid k + 2) + A N t) * (Mk k t) +
          seed k * Real.sqrt (Mk k t) := by
      intro k t ht
      have hcl := hclosure N k t ht
      have hMk1 : Mk (k + 1) t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ) + 1) t := by
        have hσ : σ₀ + ((k + 1 : ℕ) : ℝ) = σ₀ + (k : ℝ) + 1 := by push_cast; ring
        simp only [hMk, hMfam, hσ]
      have hMkk : Mk k t =
          galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ₀ + (k : ℝ)) t := by
        simp only [hMk, hMfam]
      rw [hMk', hMk1, hMkk]
      nlinarith [hcl]
    have hinitk : ∀ k, Mk k 0 ≤ B0 k := by
      intro k
      exact hinit N k
    have hc : (0 : ℝ) < 2 - Cδ := by linarith
    have hC : ∀ k, (0 : ℝ) ≤ Cmid k + 2 := by intro k; linarith [hCmid k]
    intro k t ht
    exact energy_hier_l1_bound (c := 2 - Cδ) (C := fun k => Cmid k + 2)
      (Mk := Mk) (Mk' := Mk') (seed := seed) (B0 := B0) (A := A N) (S := S N)
      (Sbd := Sbd)
      hc hC hseed (hS0 N) (hSnn N) (hScont N) (hSderiv N) (hSbd N)
      hMnonneg hcontk hderivk hdissk hinitk k t ht
  refine fun k => ⟨Real.exp Sbd *
    gronwallBound (B0 k) ((Cmid k + 2) + 1) ((seed k) ^ 2 / 4) T, fun N t ht => ?_⟩
  exact hkey N k t ht

theorem energy_l1_single
    {T c Sbd C seed B0 c₀ : ℝ} {Y Yhi Y' A S : ℝ → ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hseed : 0 ≤ seed) (hc₀ : 0 ≤ c₀)
    (hS0 : S 0 = 0) (hSnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S t)
    (hScont : ContinuousOn S (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt S (A t) (Set.Ici t) t)
    (hSbd : ∀ t ∈ Set.Icc (0 : ℝ) T, S t ≤ Sbd)
    (hYnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Y t)
    (hYhinn : ∀ t ∈ Set.Ico (0 : ℝ) T, 0 ≤ Yhi t)
    (hcont : ContinuousOn Y (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivWithinAt Y (Y' t) (Set.Ici t) t)
    (hdiss : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Y' t ≤ -c * Yhi t + (C + A t) * Y t + seed * Real.sqrt (Y t) + c₀)
    (hinit : Y 0 ≤ B0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y t ≤ Real.exp Sbd * gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T := by
  set Z : ℝ → ℝ := fun t => Y t * Real.exp (-S t) with hZdef
  set Z' : ℝ → ℝ := fun t => (Y' t - A t * Y t) * Real.exp (-S t) with hZ'def
  have hZnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Z t := fun t ht =>
    mul_nonneg (hYnn t ht) (Real.exp_nonneg _)
  have hZcont : ContinuousOn Z (Set.Icc (0 : ℝ) T) :=
    hcont.mul (Real.continuous_exp.comp_continuousOn hScont.neg)
  have hZderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt Z (Z' t) (Set.Ici t) t := by
    intro t ht
    have hexp : HasDerivWithinAt (fun u => Real.exp (-S u))
        (Real.exp (-S t) * -A t) (Set.Ici t) t := ((hSderiv t ht).neg).exp
    have hmul := (hderiv t ht).mul hexp
    have hEq : Y' t * Real.exp (-S t) + Y t * (Real.exp (-S t) * -A t) = Z' t := by
      simp only [hZ'def]; ring
    rwa [hEq] at hmul
  have hZbound : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Z' t ≤ (C + 1) * Z t + (seed ^ 2 / 4 + c₀) := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    set e : ℝ := Real.exp (-S t) with hedef
    have hepos : 0 < e := Real.exp_pos _
    have hele : e ≤ 1 := by
      rw [hedef, Real.exp_le_one_iff]; linarith [hSnn t htIcc]
    have hYt : 0 ≤ Y t := hYnn t htIcc
    have hZt : 0 ≤ Z t := hZnn t htIcc
    have hsqrt : Real.sqrt (Y t) * e ≤ Real.sqrt (Z t) := by
      have hsplit : Real.sqrt (Z t) = Real.sqrt (Y t) * Real.sqrt e := by
        simp only [hZdef, ← hedef]; exact Real.sqrt_mul hYt e
      have hle : e ≤ Real.sqrt e := by
        have hsq : e ^ 2 ≤ e := by nlinarith
        calc e = Real.sqrt (e ^ 2) := (Real.sqrt_sq hepos.le).symm
          _ ≤ Real.sqrt e := Real.sqrt_le_sqrt hsq
      rw [hsplit]
      exact mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
    have hseedle : seed * (Real.sqrt (Y t) * e) ≤ seed * Real.sqrt (Z t) :=
      mul_le_mul_of_nonneg_left hsqrt hseed
    have hmul : (Y' t - A t * Y t) * e ≤
        (-c * Yhi t + C * Y t + seed * Real.sqrt (Y t) + c₀) * e := by
      refine mul_le_mul_of_nonneg_right ?_ hepos.le
      have := hdiss t ht; nlinarith [this]
    have hexpand : (-c * Yhi t + C * Y t + seed * Real.sqrt (Y t) + c₀) * e =
        -c * (Yhi t * e) + C * Z t + seed * (Real.sqrt (Y t) * e) + c₀ * e := by
      simp only [hZdef, ← hedef]; ring
    have hdrop : 0 ≤ c * (Yhi t * e) :=
      mul_nonneg hc (mul_nonneg (hYhinn t ht) hepos.le)
    have hc₀e : c₀ * e ≤ c₀ := by nlinarith
    have hZ't : Z' t = (Y' t - A t * Y t) * e := by simp only [hZ'def, ← hedef]
    have hyoung : seed * Real.sqrt (Z t) ≤ seed ^ 2 / 4 + Z t :=
      mul_sqrt_le_sq_div_four_add seed hZt
    rw [hZ't]
    linarith [hmul, hexpand.le, hexpand.ge, hseedle, hdrop, hc₀e, hyoung]
  have hf' : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ b, Z' t < b →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Z z - Z t) < b := by
    intro t ht b hb
    refine ((hZderiv t ht).liminf_right_slope_le hb).mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hZ0 : Z 0 ≤ B0 := by
    have : Z 0 = Y 0 := by simp [hZdef, hS0]
    rw [this]; exact hinit
  intro t htIcc
  have hgron := le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := T)
    hZcont hf' (by simpa using hZ0) hZbound
  have hKnn : (0 : ℝ) ≤ C + 1 := by linarith
  have hεnn : (0 : ℝ) ≤ seed ^ 2 / 4 + c₀ := by positivity
  have hB0nn : 0 ≤ B0 := le_trans (hYnn 0 ⟨le_refl 0, htIcc.1.trans htIcc.2⟩) hinit
  have hmono : gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) (t - 0) ≤
      gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T := by
    have hle : (t - 0) ≤ T := by simpa using htIcc.2
    exact gronwallBound_mono (δ := B0) (K := C + 1) (ε := seed ^ 2 / 4 + c₀)
      hB0nn hεnn hKnn hle
  have hZle : Z t ≤ gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T :=
    le_trans (hgron t htIcc) hmono
  have hYeq : Y t = Z t * Real.exp (S t) := by
    simp only [hZdef]
    rw [mul_assoc, ← Real.exp_add]; simp
  rw [hYeq]
  calc Z t * Real.exp (S t) ≤ Z t * Real.exp Sbd :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hSbd t htIcc)) (hZnn t htIcc)
    _ ≤ gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T * Real.exp Sbd :=
        mul_le_mul_of_nonneg_right hZle (Real.exp_nonneg _)
    _ = Real.exp Sbd * gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T := by ring

omit [NeZero (Module.finrank ℝ E)] in
theorem galerkin_l1_single
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ Cδ Cmid seed B0 c₀ Sbd : ℝ} {A S : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid) (hseed : 0 ≤ seed) (hc₀ : 0 ≤ c₀)
    (hS0 : ∀ N, S N 0 = 0)
    (hSnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S N t)
    (hScont : ∀ N, ContinuousOn (S N) (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (S N) (A N t) (Set.Ici t) t)
    (hSbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, S N t ≤ Sbd)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun u => U N u i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t +
          (Cmid + A N t) * galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
          seed * Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) +
          c₀)
    (hinit : ∀ N, galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ 0 ≤ B0) :
    ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t ≤ Bound := by
  refine ⟨Real.exp Sbd *
    gronwallBound B0 (Cmid + 2 + 1) (seed ^ 2 / 4 + c₀) T, fun N t ht => ?_⟩
  refine energy_l1_single (c := 2 - Cδ) (C := Cmid + 2) (seed := seed)
    (B0 := B0) (c₀ := c₀) (Sbd := Sbd) (A := A N) (S := S N)
    (Y := galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ)
    (Yhi := galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1))
    (Y' := fun t =>
      -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t +
        2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
        2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * Fseq N t i))
    (by linarith) (by linarith) hseed hc₀ (hS0 N) (hSnn N) (hScont N)
    (hSderiv N) (hSbd N)
    (fun u _ => galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) σ u)
    (fun u _ => galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) (σ + 1) u)
    (galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N) σ
      (fun i hi => hcont N i hi))
    (fun u hu => galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N)
      (U N) (Fseq N) σ (fun i hi => hderiv N u hu i hi))
    (fun u hu => by nlinarith [hclosure N u hu]) (hinit N) t ht

omit [NeZero (Module.finrank ℝ E)] in
theorem gal_rider_bound_at
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ ρ Cδ Cmid seed B0 c₀ Crid B : ℝ} {P : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid) (hseed : 0 ≤ seed)
    (hc₀ : 0 ≤ c₀) (hCrid : 0 ≤ Crid)
    (hP0 : ∀ N, P N 0 = 0)
    (hPnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ P N t)
    (hPcont : ∀ N, ContinuousOn (P N) (Set.Icc (0 : ℝ) T))
    (hPderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (P N)
        (galerkinEnergy (I := I) (M := M) (sseq N) (U N) ρ t) (Set.Ici t) t)
    (hPbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, P N t ≤ B)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun u => U N u i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t +
          (Cmid +
              Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) ρ t)) *
            galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
          seed * Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) +
          c₀)
    (hinit : ∀ N, galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ 0 ≤ B0) :
    ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t ≤ Bound := by
  refine galerkin_l1_single (Cδ := Cδ) (Cmid := Cmid) (seed := seed)
    (B0 := B0) (c₀ := c₀) (Sbd := Crid * (T + B))
    (A := fun N t =>
      Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) ρ t))
    (S := fun N t => Crid * (t + P N t))
    hCδ hCmid hseed hc₀ (fun N => by simp only [hP0 N]; ring) ?_ ?_ ?_ ?_
    hcont hderiv hclosure hinit
  · intro N t ht
    exact mul_nonneg hCrid (add_nonneg ht.1 (hPnn N t ht))
  · intro N
    exact continuousOn_const.mul (continuousOn_id.add (hPcont N))
  · intro N t ht
    have hid : HasDerivWithinAt (fun u : ℝ => u) 1 (Set.Ici t) t :=
      hasDerivWithinAt_id t _
    exact (hid.add (hPderiv N t ht)).const_mul Crid
  · intro N t ht
    have hle : t + P N t ≤ T + B := add_le_add ht.2 (hPbd N t ht)
    exact mul_le_mul_of_nonneg_left hle hCrid

omit [NeZero (Module.finrank ℝ E)] in
theorem galRiderBound
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ Cδ Cmid seed B0 c₀ Crid B : ℝ} {P : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid) (hseed : 0 ≤ seed)
    (hc₀ : 0 ≤ c₀) (hCrid : 0 ≤ Crid)
    (hP0 : ∀ N, P N 0 = 0)
    (hPnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ P N t)
    (hPcont : ∀ N, ContinuousOn (P N) (Set.Icc (0 : ℝ) T))
    (hPderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (P N)
        (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) (Set.Ici t) t)
    (hPbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, P N t ≤ B)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun u => U N u i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t +
          (Cmid +
              Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t)) *
            galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
          seed * Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) +
          c₀)
    (hinit : ∀ N, galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ 0 ≤ B0) :
    ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t ≤ Bound := by
  refine galerkin_l1_single (Cδ := Cδ) (Cmid := Cmid) (seed := seed)
    (B0 := B0) (c₀ := c₀) (Sbd := Crid * (T + B))
    (A := fun N t =>
      Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t))
    (S := fun N t => Crid * (t + P N t))
    hCδ hCmid hseed hc₀ (fun N => by simp only [hP0 N]; ring) ?_ ?_ ?_ ?_
    hcont hderiv hclosure hinit
  · intro N t ht
    exact mul_nonneg hCrid (add_nonneg ht.1 (hPnn N t ht))
  · intro N
    exact continuousOn_const.mul (continuousOn_id.add (hPcont N))
  · intro N t ht
    have hid : HasDerivWithinAt (fun u : ℝ => u) 1 (Set.Ici t) t :=
      hasDerivWithinAt_id t _
    exact (hid.add (hPderiv N t ht)).const_mul Crid
  · intro N t ht
    have hle : t + P N t ≤ T + B := add_le_add ht.2 (hPbd N t ht)
    exact mul_le_mul_of_nonneg_left hle hCrid

theorem energy_l1_diss
    {T c Sbd C seed B0 c₀ : ℝ} {Y Yhi Y' A S D : ℝ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hseed : 0 ≤ seed) (hc₀ : 0 ≤ c₀)
    (hAnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ A t)
    (hS0 : S 0 = 0) (hSnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ S t)
    (hScont : ContinuousOn S (Set.Icc (0 : ℝ) T))
    (hSderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt S (A t) (Set.Ici t) t)
    (hSbd : ∀ t ∈ Set.Icc (0 : ℝ) T, S t ≤ Sbd)
    (hD0 : D 0 = 0) (hDnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ D t)
    (hDcont : ContinuousOn D (Set.Icc (0 : ℝ) T))
    (hDderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt D (Yhi t) (Set.Ici t) t)
    (hYnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ Y t)
    (hcont : ContinuousOn Y (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt Y (Y' t) (Set.Ici t) t)
    (hdiss : ∀ t ∈ Set.Ico (0 : ℝ) T,
      Y' t ≤ -c * Yhi t + (C + A t) * Y t + seed * Real.sqrt (Y t) + c₀)
    (hinit : Y 0 ≤ B0) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      Y t + c * D t ≤
        Real.exp Sbd * gronwallBound B0 (C + 1) (seed ^ 2 / 4 + c₀) T := by
  let W : ℝ → ℝ := fun t => Y t + c * D t
  let W' : ℝ → ℝ := fun t => Y' t + c * Yhi t
  have hWnn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ W t := by
    intro t ht
    simp only [W]
    exact add_nonneg (hYnn t ht) (mul_nonneg hc.le (hDnn t ht))
  have hWcont : ContinuousOn W (Set.Icc (0 : ℝ) T) := by
    simp only [W]
    exact hcont.add (continuousOn_const.mul hDcont)
  have hWderiv : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt W (W' t) (Set.Ici t) t := by
    intro t ht
    simpa only [W, W'] using (hderiv t ht).add ((hDderiv t ht).const_mul c)
  have hWdiss : ∀ t ∈ Set.Ico (0 : ℝ) T,
      W' t ≤ (C + A t) * W t + seed * Real.sqrt (W t) + c₀ := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self ht
    have hYleW : Y t ≤ W t := by
      simp only [W]
      exact le_add_of_nonneg_right (mul_nonneg hc.le (hDnn t htIcc))
    have hcoef : 0 ≤ C + A t := add_nonneg hC (hAnn t htIcc)
    have hmul : (C + A t) * Y t ≤ (C + A t) * W t :=
      mul_le_mul_of_nonneg_left hYleW hcoef
    have hsqrt : Real.sqrt (Y t) ≤ Real.sqrt (W t) := Real.sqrt_le_sqrt hYleW
    have hseedle : seed * Real.sqrt (Y t) ≤ seed * Real.sqrt (W t) :=
      mul_le_mul_of_nonneg_left hsqrt hseed
    have hbase := hdiss t ht
    simp only [W']
    nlinarith
  have hWinit : W 0 ≤ B0 := by
    simp only [W, hD0, mul_zero, add_zero]
    exact hinit
  exact energy_l1_single (c := 0) (C := C) (seed := seed) (B0 := B0)
    (c₀ := c₀) (Sbd := Sbd) (Y := W) (Yhi := fun _ => 0) (Y' := W')
    (A := A) (S := S) le_rfl hC hseed hc₀ hS0 hSnn hScont hSderiv hSbd
    hWnn (fun _ _ => le_rfl) hWcont hWderiv
    (fun t ht => by simpa only [zero_mul, neg_zero, zero_add] using hWdiss t ht)
    hWinit

omit [NeZero (Module.finrank ℝ E)] in
theorem galRiderDiss
    {U : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {Fseq : ℕ → ℝ → TensorEigenIdx (I := I) (M := M) g r s₀ → ℝ}
    {sseq : ℕ → Finset (TensorEigenIdx (I := I) (M := M) g r s₀)}
    {T σ Cδ Cmid seed B0 c₀ Crid B : ℝ} {P D : ℕ → ℝ → ℝ}
    (hCδ : Cδ < 2) (hCmid : 0 ≤ Cmid) (hseed : 0 ≤ seed)
    (hc₀ : 0 ≤ c₀) (hCrid : 0 ≤ Crid)
    (hP0 : ∀ N, P N 0 = 0)
    (hPnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ P N t)
    (hPcont : ∀ N, ContinuousOn (P N) (Set.Icc (0 : ℝ) T))
    (hPderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (P N)
        (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) (Set.Ici t) t)
    (hPbd : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, P N t ≤ B)
    (hD0 : ∀ N, D N 0 = 0)
    (hDnn : ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ D N t)
    (hDcont : ∀ N, ContinuousOn (D N) (Set.Icc (0 : ℝ) T))
    (hDderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (D N)
        (galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t)
        (Set.Ici t) t)
    (hcont : ∀ N, ∀ i ∈ sseq N,
      ContinuousOn (fun t => U N t i) (Set.Icc (0 : ℝ) T))
    (hderiv : ∀ N, ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ i ∈ sseq N,
      HasDerivWithinAt (fun u => U N u i)
        (-(TensorEigenIdx.lambda (I := I) (M := M) i) * U N t i + Fseq N t i)
        (Set.Ici t) t)
    (hclosure : ∀ N : ℕ, ∀ t ∈ Set.Ico (0 : ℝ) T,
      2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
          (U N t i * Fseq N t i) ≤
        Cδ * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) t +
          (Cmid +
              Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t)) *
            galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
          seed * Real.sqrt (galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t) +
          c₀)
    (hinit : ∀ N, galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ 0 ≤ B0) :
    ∃ Bound : ℝ, ∀ N, ∀ t ∈ Set.Icc (0 : ℝ) T,
      galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t ≤ Bound ∧
        D N t ≤ Bound / (2 - Cδ) := by
  let Bound : ℝ := Real.exp (Crid * (T + B)) *
    gronwallBound B0 (Cmid + 2 + 1) (seed ^ 2 / 4 + c₀) T
  refine ⟨Bound, fun N t ht => ?_⟩
  have hc : 0 < 2 - Cδ := by linarith
  have hS0 : Crid * (0 + P N 0) = 0 := by simp only [hP0 N]; ring
  have hSnn : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 ≤ Crid * (u + P N u) := by
    intro u hu
    exact mul_nonneg hCrid (add_nonneg hu.1 (hPnn N u hu))
  have hScont : ContinuousOn (fun u => Crid * (u + P N u)) (Set.Icc (0 : ℝ) T) :=
    continuousOn_const.mul (continuousOn_id.add (hPcont N))
  have hSderiv : ∀ u ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun v => Crid * (v + P N v))
        (Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ u))
        (Set.Ici u) u := by
    intro u hu
    have hid : HasDerivWithinAt (fun v : ℝ => v) 1 (Set.Ici u) u :=
      hasDerivWithinAt_id u _
    exact (hid.add (hPderiv N u hu)).const_mul Crid
  have hSbd : ∀ u ∈ Set.Icc (0 : ℝ) T,
      Crid * (u + P N u) ≤ Crid * (T + B) := by
    intro u hu
    exact mul_le_mul_of_nonneg_left (add_le_add hu.2 (hPbd N u hu)) hCrid
  have hAnn : ∀ u ∈ Set.Icc (0 : ℝ) T,
      0 ≤ Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ u) := by
    intro u _
    exact mul_nonneg hCrid (by
      linarith [galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) σ u])
  have haug : galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t +
      (2 - Cδ) * D N t ≤ Bound := by
    simp only [Bound]
    refine energy_l1_diss (c := 2 - Cδ) (C := Cmid + 2) (seed := seed)
      (B0 := B0) (c₀ := c₀) (Sbd := Crid * (T + B))
      (Y := galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ)
      (Yhi := galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1))
      (Y' := fun u =>
        -2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) (σ + 1) u +
          2 * galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ u +
          2 * ∑ i ∈ sseq N, tensorSobolevWeight (I := I) (M := M) i σ *
            (U N u i * Fseq N u i))
      (A := fun u =>
        Crid * (1 + galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ u))
      (S := fun u => Crid * (u + P N u)) (D := D N)
      hc (by linarith) hseed hc₀ hAnn hS0 hSnn hScont hSderiv hSbd
      (hD0 N) (hDnn N) (hDcont N) (hDderiv N)
      (fun u _ => galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) σ u)
      (galerkinEnergy_continuousOn (I := I) (M := M) (sseq N) (U N) σ
        (fun i hi => hcont N i hi))
      (fun u hu => galerkinEnergy_hasDerivWithinAt_ode (I := I) (M := M) (sseq N)
        (U N) (Fseq N) σ (fun i hi => hderiv N u hu i hi))
      (fun u hu => by nlinarith [hclosure N u hu]) (hinit N) t ht
  have hEnn : 0 ≤ galerkinEnergy (I := I) (M := M) (sseq N) (U N) σ t :=
    galerkinEnergy_nonneg (I := I) (M := M) (sseq N) (U N) σ t
  have hDterm : 0 ≤ (2 - Cδ) * D N t := mul_nonneg hc.le (hDnn N t ht)
  constructor
  · nlinarith
  · apply (le_div_iff₀ hc).2
    nlinarith

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
