/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedDeckWeakEquation
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.C1IsothermalPrincipal
import DifferentialGeometry.Analysis.Elliptic.Planar.WeakCoordinateChange
import DifferentialGeometry.Analysis.Elliptic.Planar.WeakFirstOrderCoefficient
import DifferentialGeometry.Analysis.Elliptic.Planar.GradientGauge
import DifferentialGeometry.Analysis.Elliptic.Planar.NodalArcs
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundedGauge
import DifferentialGeometry.Analysis.Complex.WeakHolomorphic.Continuous
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
noncomputable section

open Set Metric Filter MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry
open scoped Topology ContDiff InnerProductSpace ComplexConjugate Matrix.Norms.Elementwise

namespace DifferentialGeometry.Analysis


private theorem branch_weak_laplacian_mono
    {Ω Θ : Set ℂ} (hΘΩ : Θ ⊆ Ω) (v S : ℂ → ℝ)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ z in Ω, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) = ∫ z in Ω, S z * φ z)
    (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Θ) :
    (∫ z in Θ, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
      fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) = ∫ z in Θ, S z * φ z := by
  have hleft (D : Set ℂ) (hD : tsupport φ ⊆ D) :
      (∫ z in D, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
      ∫ z, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hDφ : fderiv ℝ φ z = 0 :=
      fderiv_of_notMem_tsupport ℝ (fun h => hz (hD h))
    simp only [hDφ, zero_apply, mul_zero, add_zero]
  have hright (D : Set ℂ) (hD : tsupport φ ⊆ D) :
      (∫ z in D, S z * φ z) = ∫ z, S z * φ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hD h)), mul_zero]
  have hh := hweak φ hφ hc (hs.trans hΘΩ)
  rw [hleft Ω (hs.trans hΘΩ), hright Ω (hs.trans hΘΩ)] at hh
  rw [hleft Θ hs, hright Θ hs]
  exact hh

private theorem branch_principal_posDef
    {K : Matrix (Fin 2) (Fin 2) ℝ} (hsymm : K.IsSymm)
    (hlower : ∀ z : ℂ, (1 / 2 : ℝ) * ‖z‖ ^ 2 ≤
      ⟪z, complexPlaneMatrixOperator K z⟫_ℝ) : K.PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.isHermitian_iff_isSymm.mpr hsymm, ?_⟩
  intro x hx
  let z : ℂ := ⟨x 0, x 1⟩
  have hz : z ≠ 0 := by
    intro h
    apply hx
    ext i
    fin_cases i
    · exact congrArg Complex.re h
    · exact congrArg Complex.im h
  have hp : 0 < ⟪z, complexPlaneMatrixOperator K z⟫_ℝ :=
    lt_of_lt_of_le (mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr hz) 2)) (hlower z)
  convert hp using 1
  simp [z, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Complex.inner, complexPlaneMatrixOperator, Complex.real_smul,
    Complex.mul_re, Complex.mul_im]
  ring

/-- The proved whole-ball deck equation and its literal principal produce a
centered C1 isothermal chart and the exact weak equation of the SAME scalar
composed with that chart's inverse. The divergence correction is retained.
The chart, transformed equation and scalar are all outputs. -/
theorem exists_branch_deck_isothermal_weak_equation
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω)
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (hK : ContDiffOn ℝ 1 K Ω)
    (hsymm : ∀ z ∈ Ω, (K z).IsSymm)
    (hdetK : ∀ z ∈ Ω, (K z).det = 1)
    (hlower : ∀ z ∈ Ω, ∀ v : ℂ, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      ⟪v, complexPlaneMatrixOperator (K z) v⟫_ℝ)
    (hw : ContDiffOn ℝ 2 w Ω) (hw0 : w 0 = 0) (hDw0 : fderiv ℝ w 0 = 0)
    (hpde : ∀ z ∈ Ω, planarScalarOperator K beta c w z = 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ e.source ⊆ Ω ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ z ∈ e.source, 0 < (fderiv ℝ e z).det) ∧
      let d : ℂ → Fin 2 → ℝ := fun z j => beta z j -
        ∑ i : Fin 2, fderiv ℝ (fun y => K y i j) z ((![1, Complex.I] : Fin 2 → ℂ) i)
      let v : ℂ → ℝ := fun y => w (e.symm y)
      let B : ℂ → ℂ := fun y => ((fderiv ℝ e (e.symm y)).det)⁻¹ •
        (∑ j : Fin 2, d (e.symm y) j •
          fderiv ℝ e (e.symm y) ((![1, Complex.I] : Fin 2 → ℂ) j))
      let q : ℂ → ℝ := fun y => c (e.symm y) / (fderiv ℝ e (e.symm y)).det
      v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧ ContDiffOn ℝ 1 v e.target ∧
      (∀ z ∈ e.source, v (e z) = w z) ∧
      ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ e.target →
        (∫ y in e.target, fderiv ℝ v y 1 * fderiv ℝ φ y 1 +
          fderiv ℝ v y Complex.I * fderiv ℝ φ y Complex.I) =
        ∫ y in e.target, (fderiv ℝ v y (B y) + q y * v y) * φ y := by
  have hKentry (i j : Fin 2) : ContDiffOn ℝ 1 (fun z => K z i j) Ω :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp hK) i)) j
  obtain ⟨e, he0, heΩ, hezero, he, hei, hedet, heprincipal⟩ :=
    exists_c1_isothermal_principal_chart hΩ h0 K hKentry
      (fun z hz => branch_principal_posDef (hsymm z hz) (hlower z hz)) hdetK
  refine ⟨e, he0, heΩ, hezero, he, hei, hedet, ?_⟩
  intro d v B q
  have hwsource : ContDiffOn ℝ 2 w e.source := hw.mono heΩ
  have hweak (φ : ℂ → ℝ) (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ e.source) :=
    planarScalarOperator_zero_weak_divergence e.open_source K beta c
      (fun i j => (hKentry i j).mono heΩ) hwsource
      (fun z hz => hpde z (heΩ hz)) φ hφ hc hs
  obtain ⟨hv, hsame, hvweak⟩ := planar_weak_divergence_pushforward K d c w e
    (hwsource.of_le (by norm_num)) he hei hedet heprincipal (by
      intro φ hφ hc hs
      simpa only [d, Finset.sum_mul] using hweak φ hφ hc hs)
  have hinv0 : e.symm 0 = 0 := by
    simpa only [hezero] using e.left_inv he0
  have htarget0 : (0 : ℂ) ∈ e.target := by rw [← hezero]; exact e.map_source he0
  have hv0 : v 0 = 0 := by simpa only [v, hinv0] using hw0
  have hDv0 : fderiv ℝ v 0 = 0 := by
    have hwD : DifferentiableAt ℝ w (e.symm 0) := by
      rw [hinv0]
      exact (hw.contDiffAt (hΩ.mem_nhds h0)).differentiableAt (by norm_num)
    have heD := (hei.contDiffAt (e.open_target.mem_nhds htarget0)).differentiableAt one_ne_zero
    change fderiv ℝ (fun y => w (e.symm y)) 0 = 0
    rw [fderiv_fun_comp 0 hwD heD, hinv0, hDw0]
    rfl
  exact ⟨hv0, hDv0, hv, hsame, hvweak⟩

private theorem branch_scalar_source_locallyIntegrable
    {Ω : Set ℂ} (hΩ : IsOpen Ω) {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hB : Measurable (fun z : Ω => B z)) (hq : Measurable (fun z : Ω => q z))
    {b₀ q₀ : ℝ} (hb₀ : 0 ≤ b₀) (hq₀ : 0 ≤ q₀)
    (hBbound : ∀ z ∈ Ω, ‖B z‖ ≤ b₀) (hqbound : ∀ z ∈ Ω, |q z| ≤ q₀) :
    LocallyIntegrableOn (fun z => fderiv ℝ v z (B z) + q z * v z) Ω := by
  let S : ℂ → ℝ := fun z => fderiv ℝ v z (B z) + q z * v z
  have hDv := hv.continuousOn_fderiv_of_isOpen hΩ le_rfl
  have heval : Continuous (fun p : (ℂ →L[ℝ] ℝ) × ℂ => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hS : Measurable (fun z : Ω => S z) :=
    (heval.measurable.comp (hDv.domRestrict.measurable.prodMk hB)).add
      (hq.mul hv.continuousOn.domRestrict.measurable)
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro k hkΩ hk
  obtain ⟨Cv, hCv⟩ := hk.exists_bound_of_continuousOn (hv.continuousOn.mono hkΩ)
  obtain ⟨Cd, hCd⟩ := hk.exists_bound_of_continuousOn (hDv.mono hkΩ)
  have hSk : AEStronglyMeasurable S (volume.restrict k) := by
    rw [← map_comap_subtype_coe hk.measurableSet]
    exact (MeasurableEmbedding.subtype_coe hk.measurableSet).aestronglyMeasurable_map_iff.mpr
      (hS.comp (measurable_inclusion hkΩ)).aestronglyMeasurable
  apply IntegrableOn.of_bound hk.measure_lt_top hSk (Cd * b₀ + q₀ * Cv)
  filter_upwards [ae_restrict_mem hk.measurableSet] with z hz
  calc
    ‖S z‖ ≤ ‖fderiv ℝ v z (B z)‖ + ‖q z * v z‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ v z‖ * ‖B z‖ + |q z| * ‖v z‖ := by
      simpa only [norm_mul, Real.norm_eq_abs] using
        add_le_add ((fderiv ℝ v z).le_opNorm (B z)) (le_refl ‖q z * v z‖)
    _ ≤ Cd * b₀ + q₀ * Cv :=
      add_le_add
        ((mul_le_mul_of_nonneg_left (hBbound z (hkΩ hz)) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right (hCd z hz) hb₀))
        ((mul_le_mul_of_nonneg_right (hqbound z (hkΩ hz)) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (hCv z hz) hq₀))

/-- A literal C1 weak scalar equation with bounded measurable lower fields
produces one unit integral gauge and a zero-germ or finite C1 nodal alternative
for that SAME scalar. No gauge, analytic section or nodal witness is assumed. -/
theorem exists_branch_deck_analytic_inverse_gauge
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω)
    {v : ℂ → ℝ} (hv : ContDiffOn ℝ 1 v Ω)
    (hv0 : v 0 = 0) (hDv0 : fderiv ℝ v 0 = 0)
    {B : ℂ → ℂ} {q : ℂ → ℝ}
    (hB : Measurable (fun z : Ω => B z)) (hq : Measurable (fun z : Ω => q z))
    {b₀ q₀ : ℝ} (hb₀ : 0 ≤ b₀) (hq₀ : 0 ≤ q₀)
    (hBbound : ∀ z ∈ Ω, ‖B z‖ ≤ b₀) (hqbound : ∀ z ∈ Ω, |q z| ≤ q₀)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ z in Ω, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
      ∫ z in Ω, (fderiv ℝ v z (B z) + q z * v z) * φ z) :
    ∃ R : ℝ, 0 < R ∧ closedBall (0 : ℂ) R ⊆ Ω ∧
      ∃ A : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ),
        Measurable A ∧
        (∀ z ∈ Ω, A z (planarGradientSection v z) =
          (-((fderiv ℝ v z (B z) + q z * v z : ℝ) : ℂ) / 4,
            conj (planarComplexGradient v z))) ∧
        (∀ z, ‖A z‖ ≤ b₀ / 2 + q₀ / 4 + 1) ∧
        ∃ P : C(closedBall (0 : ℂ) R, (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)),
          (∀ z : closedBall (0 : ℂ) R, IsUnit (P z)) ∧
          let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
            1 + diskCauchyIntegral (fun w : closedBall (0 : ℂ) R => A w * P w) z
          (∀ z : closedBall (0 : ℂ) R, P₀ z = P z) ∧
          AnalyticOnNhd ℂ (fun z => Ring.inverse (P₀ z) (planarGradientSection v z))
            (ball (0 : ℂ) (R / 2)) ∧
          ((∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
            ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) (R / 2) ∧
              (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
              ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
                (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
                  HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
                  Set.InjOn (Γ s) (Ico 0 ρ) ∧
                  ∀ r ∈ Ico 0 ρ, ‖Γ s r‖ = r ∧ v (Γ s r) = 0) ∧
                ∀ z ∈ ball (0 : ℂ) ρ,
                  v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) := by
  classical
  let C : ℝ := b₀ / 2 + q₀ / 4 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨A, hAmeas, hAeq, hAbound, _hAzero⟩ :=
    exists_measurable_planarGradientSection_weak_coefficient hΩ hv hB hq hb₀ hq₀ hBbound hqbound
  obtain ⟨r, hr, hrΩ⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hΩ.mem_nhds h0)
  let R : ℝ := min r (1 / (16 * (C + 1)))
  have hR : 0 < R := lt_min hr (by positivity)
  have hRΩ : closedBall (0 : ℂ) R ⊆ Ω :=
    (closedBall_subset_closedBall (min_le_left _ _)).trans hrΩ
  have hsmall : R * (16 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 16 * (C + 1))).mp (min_le_right _ _)
  have hk : 4 * R * C < 1 / 2 := by nlinarith
  have hAR : AEStronglyMeasurable (fun z : closedBall (0 : ℂ) R => A z)
      (volume.comap ((↑) : closedBall (0 : ℂ) R → ℂ)) :=
    (hAmeas.comp measurable_subtype_coe).aestronglyMeasurable
  obtain ⟨P, _hfixed, hnear, hunit, hPrep, hPunit, hPweak⟩ :=
    DiskRegularity.ConsumerAudit.bounded_measurable_unit_gauge_with_weak_equation
      0 R hR (fun z : closedBall (0 : ℂ) R => A z) hAR C hC.le
      (Eventually.of_forall (fun z => hAbound z)) hk
  let P₀ : ℂ → (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := fun z =>
    1 + diskCauchyIntegral (fun w : closedBall (0 : ℂ) R => A w * P w) z
  let S : ℂ → ℝ := fun z => fderiv ℝ v z (B z) + q z * v z
  let δ : ℝ := (4 * R * C) / (1 - 4 * R * C)
  have hden : 0 < 1 - 4 * R * C := by linarith
  have hδ0 : 0 ≤ δ := div_nonneg (by positivity) hden.le
  have hδ : δ < 1 := (div_lt_one hden).mpr (by linarith)
  have hnear₀ : ∀ z ∈ closedBall (0 : ℂ) R, ‖P₀ z - 1‖ ≤ δ := by
    intro z hz
    rw [show P₀ z = P ⟨z, hz⟩ from hPrep ⟨z, hz⟩]
    exact ((P - 1).norm_coe_le_norm ⟨z, hz⟩).trans hnear
  have hballΩ : ball (0 : ℂ) R ⊆ Ω := ball_subset_closedBall.trans hRΩ
  have hSR : LocallyIntegrableOn S (ball (0 : ℂ) R) :=
    (branch_scalar_source_locallyIntegrable hΩ hv hB hq hb₀ hq₀ hBbound hqbound).mono_set hballΩ
  have hscalar : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : ℂ) R →
      (∫ z in ball (0 : ℂ) R, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
      ∫ z in ball (0 : ℂ) R, S z * φ z := by
    intro φ hφ hc hs
    exact branch_weak_laplacian_mono hballΩ v S hweak φ (hφ.of_le (by simp)) hc hs
  obtain ⟨hcontinuous, hintegral⟩ := actual_planarGradientSection_inverse_gauge_weak_equation
    0 R hR P P₀ A hPrep hAmeas.aestronglyMeasurable hδ0 hδ hC.le hnear₀ hAbound
    (fun φ hφ hc hs => (hPweak φ hφ hc hs).2) v S (hv.mono hballΩ) hSR hscalar
    (fun z hz => hAeq z (hballΩ hz))
  have hanalytic : AnalyticOnNhd ℂ (fun z => Ring.inverse (P₀ z) (planarGradientSection v z))
      (ball (0 : ℂ) (R / 2)) := by
    apply analyticOnNhd_of_continuousOn_of_integral_realTestDbar_smul_eq_zero isOpen_ball hcontinuous
    intro φ hφ hc hs
    have hφc : ContDiff ℝ ∞ (fun z => (φ z : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hφ
    have hh := hintegral (fun z => (φ z : ℂ)) hφc (hc.comp_left Complex.ofReal_zero)
      ((tsupport_comp_subset Complex.ofReal_zero φ).trans hs)
    have heq (z : ℂ) := complexDbar_ofReal (hφ.differentiable (by simp) z)
    simpa only [heq] using hh
  have hsmallR : ball (0 : ℂ) (R / 2) ⊆ closedBall (0 : ℂ) R :=
    (ball_subset_ball (half_le_self hR.le)).trans ball_subset_closedBall
  have hPcontinuous : ContinuousOn P₀ (closedBall (0 : ℂ) R) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact P.continuous.congr (fun z => (hPrep z).symm)
  refine ⟨R, hR, hRΩ, A, hAmeas, hAeq, hAbound, P, hunit, hPrep, hanalytic, ?_⟩
  by_cases hgerm : ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0
  · exact Or.inl hgerm
  · apply Or.inr
    simpa only [sub_zero] using exists_finite_nodal_arcs_of_analytic_inverse_gauge
      isOpen_ball (mem_ball_self (half_pos hR)) (hv.mono (hsmallR.trans hRΩ))
      (hPcontinuous.mono hsmallR) (hPunit 0 (mem_closedBall_self hR.le))
      (hanalytic 0 (mem_ball_self (half_pos hR))) hgerm hv0 hDv0


/-- The literal determinant-normalized lower fields in a supplied C1 principal
chart are measurable and bounded on a smaller centered ball. The original
coefficient fields and this exact chart are preserved. The column-divergence
correction is controlled using the actual C1 principal. -/
theorem exists_bounded_branch_isothermal_lower_fields
    (e : OpenPartialHomeomorph ℂ ℂ)
    (he0 : (0 : ℂ) ∈ e.source) (hezero : e 0 = 0)
    (he : ContDiffOn ℝ 1 e e.source)
    (hedet : ∀ z ∈ e.source, 0 < (fderiv ℝ e z).det)
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (hK : ContDiffOn ℝ 1 K e.source)
    (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ)
    (hbeta : ∀ j, Measurable (fun z : e.source => beta z j))
    (hc : Measurable (fun z : e.source => c z))
    {b₀ c₀ : ℝ} (hb₀ : 0 ≤ b₀) (hc₀ : 0 ≤ c₀)
    (hbetaBound : ∀ z ∈ e.source, ∀ j, |beta z j| ≤ b₀)
    (hcBound : ∀ z ∈ e.source, |c z| ≤ c₀) :
    let d : ℂ → Fin 2 → ℝ := fun z j => beta z j -
      ∑ i : Fin 2, fderiv ℝ (fun y => K y i j) z ((![1, Complex.I] : Fin 2 → ℂ) i)
    let B : ℂ → ℂ := fun y => ((fderiv ℝ e (e.symm y)).det)⁻¹ •
      (∑ j : Fin 2, d (e.symm y) j •
        fderiv ℝ e (e.symm y) ((![1, Complex.I] : Fin 2 → ℂ) j))
    let q : ℂ → ℝ := fun y => c (e.symm y) / (fderiv ℝ e (e.symm y)).det
    ∃ r B₀ Q₀ : ℝ, 0 < r ∧ 0 ≤ B₀ ∧ 0 ≤ Q₀ ∧
      closedBall (0 : ℂ) r ⊆ e.target ∧
      Measurable (fun z : ball (0 : ℂ) r => B z) ∧
      Measurable (fun z : ball (0 : ℂ) r => q z) ∧
      (∀ z ∈ ball (0 : ℂ) r, ‖B z‖ ≤ B₀) ∧
      (∀ z ∈ ball (0 : ℂ) r, |q z| ≤ Q₀) := by
  classical
  intro d B q
  let E : ℂ → ℂ →L[ℝ] ℂ := fun y => fderiv ℝ e (e.symm y)
  let J : ℂ → ℝ := fun y => ((E y).det)⁻¹
  let T : ℂ → Fin 2 → ℝ := fun y j =>
    ∑ i : Fin 2, fderiv ℝ (fun z => K z i j) (e.symm y)
      ((![1, Complex.I] : Fin 2 → ℂ) i)
  let invMap : e.target → e.source := fun y => ⟨e.symm y, e.map_target y.property⟩
  have hInvMap : Measurable invMap :=
    e.continuousOn_symm.domRestrict.measurable.subtype_mk
  have hE : ContinuousOn E e.target :=
    (he.continuousOn_fderiv_of_isOpen e.open_source le_rfl).comp
      e.continuousOn_symm (fun y hy => e.map_target hy)
  have hdet : ContinuousOn (fun y => (E y).det) e.target :=
    ContinuousLinearMap.continuous_det.comp_continuousOn hE
  have hJ : ContinuousOn J e.target :=
    hdet.inv₀ (fun y hy => (hedet _ (e.map_target hy)).ne')
  have hKentry (i j : Fin 2) : ContDiffOn ℝ 1 (fun z => K z i j) e.source :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp hK) i)) j
  have hT (j : Fin 2) : ContinuousOn (fun y => T y j) e.target := by
    dsimp only [T]
    apply continuousOn_finsetSum
    intro i _
    exact ((hKentry i j).continuousOn_fderiv_of_isOpen e.open_source le_rfl).clm_apply
      continuousOn_const |>.comp e.continuousOn_symm (fun y hy => e.map_target hy)
  have hd (j : Fin 2) : Measurable (fun y : e.target => d (e.symm y) j) :=
    ((hbeta j).comp hInvMap).sub (hT j).domRestrict.measurable
  have hEB (j : Fin 2) : Measurable (fun y : e.target =>
      E y ((![1, Complex.I] : Fin 2 → ℂ) j)) :=
    (hE.clm_apply continuousOn_const).domRestrict.measurable
  have hBmeas : Measurable (fun y : e.target => B y) := by
    change Measurable (fun y : e.target => J y •
      (∑ j : Fin 2, d (e.symm y) j • E y ((![1, Complex.I] : Fin 2 → ℂ) j)))
    exact hJ.domRestrict.measurable.smul
      (Finset.measurable_sum _ (fun j _ => (hd j).smul (hEB j)))
  have hqmeas : Measurable (fun y : e.target => q y) :=
    (hc.comp hInvMap).div hdet.domRestrict.measurable
  have htarget0 : (0 : ℂ) ∈ e.target := by rw [← hezero]; exact e.map_source he0
  obtain ⟨r, hr, hrT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds htarget0)
  have hcompact : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall _ _
  obtain ⟨CE, hCE⟩ := hcompact.exists_bound_of_continuousOn (hE.mono hrT)
  obtain ⟨CJ, hCJ⟩ := hcompact.exists_bound_of_continuousOn (hJ.mono hrT)
  have hTabs : ContinuousOn (fun y => |T y 0| + |T y 1|) e.target :=
    (hT 0).abs.add (hT 1).abs
  obtain ⟨CT, hCT⟩ := hcompact.exists_bound_of_continuousOn (hTabs.mono hrT)
  have hCE0 : 0 ≤ CE := (norm_nonneg _).trans (hCE 0 (mem_closedBall_self hr.le))
  have hCJ0 : 0 ≤ CJ := (norm_nonneg _).trans (hCJ 0 (mem_closedBall_self hr.le))
  have hCT0 : 0 ≤ CT := (norm_nonneg _).trans (hCT 0 (mem_closedBall_self hr.le))
  let B₀ : ℝ := CJ * ((2 * b₀ + CT) * CE)
  let Q₀ : ℝ := c₀ * CJ
  have hballT : ball (0 : ℂ) r ⊆ e.target := ball_subset_closedBall.trans hrT
  refine ⟨r, B₀, Q₀, hr, by dsimp [B₀]; positivity, by dsimp [Q₀]; positivity,
    hrT, hBmeas.comp (measurable_inclusion hballT),
    hqmeas.comp (measurable_inclusion hballT), ?_, ?_⟩
  · intro y hy
    have hyc := ball_subset_closedBall hy
    have hys := e.map_target (hballT hy)
    have hTsum : |T y 0| + |T y 1| ≤ CT := by
      have hnonneg : (0 : ℝ) ≤ |T y 0| + |T y 1| :=
        add_nonneg (abs_nonneg (T y 0)) (abs_nonneg (T y 1))
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hCT y hyc
    have hdsum : |d (e.symm y) 0| + |d (e.symm y) 1| ≤ 2 * b₀ + CT := by
      have h0 : |d (e.symm y) 0| ≤ |beta (e.symm y) 0| + |T y 0| := abs_sub _ _
      have h1 : |d (e.symm y) 1| ≤ |beta (e.symm y) 1| + |T y 1| := abs_sub _ _
      linarith [hbetaBound _ hys 0, hbetaBound _ hys 1]
    have hE1 : ‖E y 1‖ ≤ CE := by
      have hh : ‖E y 1‖ ≤ ‖E y‖ := by simpa using (E y).le_opNorm (1 : ℂ)
      exact hh.trans (hCE y hyc)
    have hEI : ‖E y Complex.I‖ ≤ CE := by
      have hh : ‖E y Complex.I‖ ≤ ‖E y‖ := by simpa using (E y).le_opNorm Complex.I
      exact hh.trans (hCE y hyc)
    have hsum : ‖∑ j : Fin 2, d (e.symm y) j • E y ((![1, Complex.I] : Fin 2 → ℂ) j)‖ ≤
        (2 * b₀ + CT) * CE := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      calc
        _ ≤ |d (e.symm y) 0| * ‖E y 1‖ + |d (e.symm y) 1| * ‖E y Complex.I‖ := by
          simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
            (d (e.symm y) 0 • E y 1) (d (e.symm y) 1 • E y Complex.I)
        _ ≤ |d (e.symm y) 0| * CE + |d (e.symm y) 1| * CE :=
          add_le_add (mul_le_mul_of_nonneg_left hE1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hEI (abs_nonneg _))
        _ = (|d (e.symm y) 0| + |d (e.symm y) 1|) * CE := by ring
        _ ≤ (2 * b₀ + CT) * CE := mul_le_mul_of_nonneg_right hdsum hCE0
    change ‖J y • (∑ j : Fin 2, d (e.symm y) j • E y ((![1, Complex.I] : Fin 2 → ℂ) j))‖ ≤ B₀
    rw [norm_smul]
    exact mul_le_mul (hCJ y hyc) hsum (norm_nonneg _) hCJ0
  · intro y hy
    have hys := e.map_target (hballT hy)
    have hJy : |J y| ≤ CJ := by simpa only [Real.norm_eq_abs] using hCJ y (ball_subset_closedBall hy)
    change |c (e.symm y) / (E y).det| ≤ c₀ * CJ
    rw [div_eq_mul_inv, abs_mul]
    exact mul_le_mul (hcBound _ hys) hJy (abs_nonneg _) hc₀


/-- Receiving classifier for the original whole-ball deck-height equation. All
isothermal and gauge data are constructed from its literal coefficients. The
output scalar is exactly the supplied scalar composed with the one selected
C1 inverse chart. This is the consumer of the original Morrey weak-deck tuple
once its literal lower fields have been shown measurable. -/
theorem exists_branch_deck_c1_nodal_chart
    {Ω : Set ℂ} (hΩ : IsOpen Ω) (h0 : (0 : ℂ) ∈ Ω)
    (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (beta : ℂ → Fin 2 → ℝ) (c w : ℂ → ℝ)
    (hK : ContDiffOn ℝ 1 K Ω)
    (hsymm : ∀ z ∈ Ω, (K z).IsSymm)
    (hdetK : ∀ z ∈ Ω, (K z).det = 1)
    (hlower : ∀ z ∈ Ω, ∀ v : ℂ, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
      ⟪v, complexPlaneMatrixOperator (K z) v⟫_ℝ)
    (hw : ContDiffOn ℝ 2 w Ω) (hw0 : w 0 = 0) (hDw0 : fderiv ℝ w 0 = 0)
    (hpde : ∀ z ∈ Ω, planarScalarOperator K beta c w z = 0)
    (hbeta : ∀ j, Measurable (fun z : Ω => beta z j))
    (hc : Measurable (fun z : Ω => c z))
    {b₀ c₀ : ℝ} (hb₀ : 0 ≤ b₀) (hc₀ : 0 ≤ c₀)
    (hbetaBound : ∀ z ∈ Ω, ∀ j, |beta z j| ≤ b₀)
    (hcBound : ∀ z ∈ Ω, |c z| ≤ c₀) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      0 ∈ e.source ∧ e.source ⊆ Ω ∧ e 0 = 0 ∧
      ContDiffOn ℝ 1 e e.source ∧ ContDiffOn ℝ 1 e.symm e.target ∧
      (∀ z ∈ e.source, 0 < (fderiv ℝ e z).det) ∧
      let v : ℂ → ℝ := fun y => w (e.symm y)
      v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧ ContDiffOn ℝ 1 v e.target ∧
      (∀ z ∈ e.source, v (e z) = w z) ∧
      ((∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
        ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ e.target ∧
          (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
          ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
            (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
              HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
              Set.InjOn (Γ s) (Ico 0 ρ) ∧
              ∀ r ∈ Ico 0 ρ, ‖Γ s r‖ = r ∧ v (Γ s r) = 0) ∧
            ∀ z ∈ ball (0 : ℂ) ρ,
              v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) := by
  obtain ⟨e, he0, heΩ, hezero, he, hei, hedet, hv0, hDv0, hv, hsame, hweak⟩ :=
    exists_branch_deck_isothermal_weak_equation hΩ h0 K beta c w
      hK hsymm hdetK hlower hw hw0 hDw0 hpde
  let d : ℂ → Fin 2 → ℝ := fun z j => beta z j -
    ∑ i : Fin 2, fderiv ℝ (fun y => K y i j) z ((![1, Complex.I] : Fin 2 → ℂ) i)
  let v : ℂ → ℝ := fun y => w (e.symm y)
  let B : ℂ → ℂ := fun y => ((fderiv ℝ e (e.symm y)).det)⁻¹ •
    (∑ j : Fin 2, d (e.symm y) j •
      fderiv ℝ e (e.symm y) ((![1, Complex.I] : Fin 2 → ℂ) j))
  let q : ℂ → ℝ := fun y => c (e.symm y) / (fderiv ℝ e (e.symm y)).det
  obtain ⟨r, B₀, Q₀, hr, hB₀, hQ₀, hrT, hBmeas, hqmeas, hBbound, hqbound⟩ :=
    exists_bounded_branch_isothermal_lower_fields e he0 hezero he hedet K (hK.mono heΩ) beta c
      (fun j => (hbeta j).comp (measurable_inclusion heΩ))
      (hc.comp (measurable_inclusion heΩ)) hb₀ hc₀
      (fun z hz => hbetaBound z (heΩ hz)) (fun z hz => hcBound z (heΩ hz))
  have hballT : ball (0 : ℂ) r ⊆ e.target := ball_subset_closedBall.trans hrT
  have hweakBall : ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ ball (0 : ℂ) r →
      (∫ z in ball (0 : ℂ) r, fderiv ℝ v z 1 * fderiv ℝ φ z 1 +
        fderiv ℝ v z Complex.I * fderiv ℝ φ z Complex.I) =
      ∫ z in ball (0 : ℂ) r, (fderiv ℝ v z (B z) + q z * v z) * φ z := by
    intro φ hφ hc hs
    exact branch_weak_laplacian_mono hballT v
      (fun z => fderiv ℝ v z (B z) + q z * v z) hweak φ hφ hc hs
  obtain ⟨R, hR, hRball, A, _hAmeas, _hAeq, _hAbound, P, _hPunit, _hPrep,
      _hanalytic, hnodal⟩ :=
    exists_branch_deck_analytic_inverse_gauge isOpen_ball (mem_ball_self hr)
      (hv.mono hballT) hv0 hDv0 hBmeas hqmeas hB₀ hQ₀ hBbound hqbound hweakBall
  refine ⟨e, he0, heΩ, hezero, he, hei, hedet, hv0, hDv0, hv, hsame, ?_⟩
  rcases hnodal with hzero | ⟨ρ, hρ, hρR, hgrad, S, hS, Γ, hΓ, hcover⟩
  · exact Or.inl hzero
  · refine Or.inr ⟨ρ, hρ, ?_, hgrad, S, hS, Γ, hΓ, hcover⟩
    exact hρR.trans
      (((ball_subset_ball (half_le_self hR.le)).trans ball_subset_closedBall).trans
        (hRball.trans hballT))

end DifferentialGeometry.Analysis
