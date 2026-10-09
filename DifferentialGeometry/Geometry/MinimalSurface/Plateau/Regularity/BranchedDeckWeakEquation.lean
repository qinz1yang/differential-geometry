/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.ProjectionGraphHessian
import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphPowerDifference
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientRootLowerTerms
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientNormalizedConductivityStructure
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.WeakEquation

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval InnerProductSpace
open scoped Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry

private theorem branch_secondJet_comp_zero
    {w : ℂ → ℝ} {f : ℂ → ℂ} {y : ℂ}
    (hw : ContDiffAt ℝ 2 w (f y)) (hf : ContDiffAt ℝ 2 f y)
    (hd0 : fderiv ℝ w (f y) = 0) (hdd0 : fderiv ℝ (fderiv ℝ w) (f y) = 0) :
    fderiv ℝ (fun z => w (f z)) y = 0 ∧
      fderiv ℝ (fderiv ℝ (fun z => w (f z))) y = 0 := by
  have hwd := (hw.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfd := hf.differentiableAt (by norm_num)
  have hfdd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : fderiv ℝ (fun z => w (f z)) =ᶠ[𝓝 y]
      fun z => (fderiv ℝ w (f z)).comp (fderiv ℝ f z) := by
    filter_upwards [hf.eventually (by norm_num),
      hf.continuousAt (hw.eventually (by norm_num))] with z hfz hwz
    change ContDiffAt ℝ 2 w (f z) at hwz
    exact fderiv_fun_comp z (hwz.differentiableAt (by norm_num))
      (hfz.differentiableAt (by norm_num))
  constructor
  · rw [fderiv_fun_comp y (hw.differentiableAt (by norm_num)) hfd, hd0]
    rfl
  · have hsecond := ((hwd.hasFDerivAt.comp y hfd.hasFDerivAt).clm_comp
      hfdd.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hsecond
    rw [hnear.fderiv_eq, hsecond]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.flip_apply, hd0, hdd0, zero_apply, add_zero]

private theorem branch_deck_secondJet_zero
    {H : ℂ → ℝ} (hH : ContDiffAt ℝ 2 H 0)
    (hDH : fderiv ℝ H 0 = 0) (hDDH : fderiv ℝ (fderiv ℝ H) 0 = 0) (ζ : ℂ) :
    fderiv ℝ (fun w => H w - H (ζ * w)) 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (fun w => H w - H (ζ * w))) 0 = 0 := by
  have hrot : ContDiffAt ℝ 2 (fun w : ℂ => ζ * w) 0 := by fun_prop
  have hHcenter : ContDiffAt ℝ 2 H (ζ * 0) := by simpa only [mul_zero] using hH
  have hHrot : ContDiffAt ℝ 2 (fun w => H (ζ * w)) 0 := hHcenter.comp 0 hrot
  obtain ⟨hDrot, hDDrot⟩ := branch_secondJet_comp_zero hHcenter hrot
    (by simpa only [mul_zero] using hDH) (by simpa only [mul_zero] using hDDH)
  have hnear : fderiv ℝ (fun w => H w - H (ζ * w)) =ᶠ[𝓝 (0 : ℂ)]
      (fun w => fderiv ℝ H w - fderiv ℝ (fun v => H (ζ * v)) w) := by
    filter_upwards [hH.eventually (by norm_num), hHrot.eventually (by norm_num)]
      with w hw hwr
    exact fderiv_sub (hw.differentiableAt (by norm_num))
      (hwr.differentiableAt (by norm_num))
  constructor
  · rw [hnear.self_of_nhds]
    change fderiv ℝ H 0 - fderiv ℝ (fun w => H (ζ * w)) 0 = 0
    rw [hDH, hDrot, sub_self]
  · rw [hnear.fderiv_eq]
    change fderiv ℝ (fderiv ℝ H - fderiv ℝ (fun w => H (ζ * w))) 0 = 0
    rw [fderiv_sub
      ((hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
        ((hHrot.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)),
      hDDH, hDDrot, sub_self]

/-- The actual root coordinate and its original projection graph germs produce
one whole-ball weak equation for every deck-height difference. The principal
and lower fields are the literal geometric fields; no PDE or coefficient bound
is assumed. The root Hessian data are exactly those supplied by the same Morrey
branch tuple. The original metric, map, root coordinate and normal remain fixed. -/
theorem chartLeadingPlaneProjection_root_pair_weak_equation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ s, diskMapTension g U z = 0)
    {a : ℂ} {p : M} (has : a ∈ s)
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p (U a) i j : ℂ) * b i * b j) = 0)
    (N : E) (hunit : chartGramBilin g p (U a) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (U a) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
          (fun i => (2 : ℝ) *
            (chartLeadingPlaneProjection g p (U a) b v * b i).re) +
        (chartGramBilin g p (U a) N v) • N)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ v, L v = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (v * b i).re))
    {m : ℕ} (hm : 1 ≤ m) (eRoot : OpenPartialHomeomorph ℂ ℂ)
    (he0 : (0 : ℂ) ∈ eRoot.target)
    (hgraphs : ∀ w ∈ eRoot.target, w ≠ 0 →
      ∃ eGraph : OpenPartialHomeomorph ℂ ℂ,
        eRoot.symm w ∈ eGraph.source ∧ eGraph.source ⊆ s ∧
        (eGraph : ℂ → ℂ) = (fun z => chartLeadingPlaneProjection g p (U a) b
          (extChartAt 𝓘(ℝ, E) p (U z))) ∧
        ContDiffOn ℝ ∞ eGraph.symm eGraph.target)
    (hpower : ∀ v ∈ eRoot.target,
      chartLeadingPlaneProjection g p (U a) b (extChartAt 𝓘(ℝ, E) p (U (eRoot.symm v))) =
        chartLeadingPlaneProjection g p (U a) b (extChartAt 𝓘(ℝ, E) p (U a)) +
          v ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) :
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
    let c := F a
    let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p (U a) + L (q.1.1 - c) + q.1.2 • N
    let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) (V q.2 i) (V q.2 j)
    let A : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q =>
      Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1)
    let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => Q N - l.comp proj
    let Phi : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → ℝ :=
      fun T q => ∑ i : Fin 2, ∑ j : Fin 2,
        A q i j * (T (dirs i) (dirs j) +
          theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q)))
    let R : ℂ → (ℂ →L[ℝ] ℝ) := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let T2 : ℂ → ℂ → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := fun zeta w =>
      (fderiv ℝ R (zeta * w)).comp
        (ContinuousLinearMap.mul ℝ ℂ (((zeta * w) ^ m)⁻¹))
    let Jet : Type := ℝ × (ℂ →L[ℝ] ℝ)
    let J1 : ℂ → Jet := fun w => (H w, R w)
    let J2 : ℂ → ℂ → Jet := fun zeta w => (H (zeta * w), R (zeta * w))
    let J : ℂ → ℂ → ℝ → Jet := fun zeta w t => (1 - t) • J2 zeta w + t • J1 w
    let PhiRoot : ℂ → ℂ → Jet → ℝ := fun zeta w j =>
      Phi (T2 zeta w) ((P w, j.1), j.2)
    let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
    let betaRoot : ℂ → ℂ → Fin 2 → ℝ := fun zeta w i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (0, duals i)
    let cRoot : ℂ → ℂ → ℝ := fun zeta w =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (1, 0)
    let A1 : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => A ((P w, H w), R w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix ((w ^ m)⁻¹) * A1 w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let bTilde : ℂ → ℂ → ℂ := fun zeta w =>
      star (w ^ m) * ((betaRoot zeta w 0 : ℂ) + (betaRoot zeta w 1 : ℂ) * Complex.I) -
        ((m : ℂ) / w) * Analysis.planarMatrixSpin (K w)
    let cTilde : ℂ → ℂ → ℝ := fun zeta w => ‖w ^ m‖ ^ 2 * cRoot zeta w
    let W : ℂ → ℂ → ℝ := fun zeta w => H w - H (zeta * w)
    ContDiffAt ℝ 2 H 0 → H 0 = 0 → fderiv ℝ H 0 = 0 →
    fderiv ℝ (fderiv ℝ H) 0 = 0 →
    (∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) →
    ∃ ε C : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧
      ball (0 : ℂ) ε ⊆ eRoot.target ∧
      K 0 = 1 ∧ ContDiffOn ℝ 1 K (ball (0 : ℂ) ε) ∧
      (∀ w ∈ ball (0 : ℂ) ε, (K w).IsSymm ∧ (K w).det = 1 ∧
        ∀ v : ℂ, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ ⟪v, complexPlaneMatrixOperator (K w) v⟫_ℝ ∧
          ⟪v, complexPlaneMatrixOperator (K w) v⟫_ℝ ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2) ∧
      ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
        W ζ 0 = 0 ∧ fderiv ℝ (W ζ) 0 = 0 ∧ fderiv ℝ (fderiv ℝ (W ζ)) 0 = 0 ∧
        ContDiffOn ℝ 2 (W ζ) (ball (0 : ℂ) ε) ∧
        (∀ w ∈ ball (0 : ℂ) ε,
          ‖bTilde ζ w‖ ≤ C * ‖w‖ ∧ ‖cTilde ζ w‖ ≤ C * ‖w‖ ^ m) ∧
        (∀ w ∈ ball (0 : ℂ) ε,
          Analysis.planarScalarOperator K
            (fun v => ![(bTilde ζ v).re, (bTilde ζ v).im]) (cTilde ζ) (W ζ) w = 0) ∧
        ∀ φ : ℂ → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
          tsupport φ ⊆ ball (0 : ℂ) ε →
          (∫ w in ball (0 : ℂ) ε, ∑ i : Fin 2,
            (∑ j : Fin 2, K w i j *
              fderiv ℝ (W ζ) w ((![1, Complex.I] : Fin 2 → ℂ) j)) *
              fderiv ℝ φ w ((![1, Complex.I] : Fin 2 → ℂ) i)) =
          ∫ w in ball (0 : ℂ) ε,
            ((∑ j : Fin 2,
              ((![(bTilde ζ w).re, (bTilde ζ w).im] : Fin 2 → ℝ) j -
                ∑ i : Fin 2, fderiv ℝ (fun v => K v i j) w
                  ((![1, Complex.I] : Fin 2 → ℂ) i)) *
                fderiv ℝ (W ζ) w ((![1, Complex.I] : Fin 2 → ℂ) j)) +
              cTilde ζ w * W ζ w) * φ w := by
  classical
  intro X F c H Q proj dirs Y V G A theta Phi R P T2 Jet J1 J2 J PhiRoot duals
    betaRoot cRoot A1 K bTilde cTilde W hH hH0 hDH hDDH hHess
  have hsrc := hchart a has
  obtain ⟨_hA0, _hKop, hK0, hKC1, _hDK0, _CK, _hCK,
      _hAnear, _hKnear, _hphysical⟩ :=
    chartLeadingPlaneProjection_normalized_conductivity
      g hsrc hb hnull hprojN hunit L hL c hm hH hH0 hDH hHess
  change K 0 = 1 at hK0
  change ContDiffAt ℝ 1 K 0 at hKC1
  obtain ⟨rS, hrS, hstructure⟩ :=
    chartLeadingPlaneProjection_normalized_conductivity_structure
      g hsrc hb hnull hprojN hunit L hL c hm hH hH0 hDH hHess
  obtain ⟨rL, C, hrL, hrL1, hC, hlower⟩ :=
    chartLeadingPlaneProjection_root_lower_term_bounds
      g hsrc hb hnull hprojN hunit L hL c hm hH hH0 hDH hHess
  obtain ⟨hPζ, _CJ, _hCJ, hinterpolated⟩ :=
    chartLeadingPlaneProjection_interpolated_root_slope_bound
      g hsrc hb hnull hprojN hunit L hL c hm hH hH0 hDH hHess
  have hphysical : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      ∀ t ∈ Icc (0 : ℝ) 1,
        Y ((P w, (J ζ w t).1), (J ζ w t).2) ∈ (extChartAt 𝓘(ℝ, E) p).target := by
    filter_upwards [hinterpolated] with w hw
    intro ζ hζ t ht
    have hh := (hw ζ hζ t ht).1.1
    have hJeq : (1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
        t • ((P w, H w), R w) = ((P w, (J ζ w t).1), (J ζ w t).2) := by
      apply Prod.ext
      · apply Prod.ext
        · change (1 - t) • P (ζ * w) + t • P w = P w
          have hP : P (ζ * w) = P w := hPζ ζ hζ w
          rw [hP, ← add_smul, sub_add_cancel, one_smul]
        · rfl
      · rfl
    change Y ((1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
      t • ((P w, H w), R w)) ∈ (extChartAt 𝓘(ℝ, E) p).target at hh
    rwa [hJeq] at hh
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ eRoot.target ∧
      ContDiffAt ℝ 2 H w ∧ ContDiffAt ℝ 1 K w ∧
      ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
        Y ((P w, (J ζ w t).1), (J ζ w t).2) ∈ (extChartAt 𝓘(ℝ, E) p).target := by
    filter_upwards [eRoot.open_target.mem_nhds he0, hH.eventually (by norm_num),
      hKC1.eventually (by norm_num), hphysical] with w hw hHw hKw hpw
    exact ⟨hw, hHw, hKw, hpw⟩
  obtain ⟨r0, hr0, hrnear⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min r0 (min rL rS)
  have hε : 0 < ε := lt_min hr0 (lt_min hrL hrS)
  have hε0 : ball (0 : ℂ) ε ⊆ ball (0 : ℂ) r0 :=
    ball_subset_ball (min_le_left _ _)
  have hεL : ball (0 : ℂ) ε ⊆ ball (0 : ℂ) rL :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hεS : ball (0 : ℂ) ε ⊆ ball (0 : ℂ) rS :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hnear' (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) := hrnear (hε0 hw)
  have hHball : ContDiffOn ℝ 2 H (ball (0 : ℂ) ε) :=
    fun w hw => (hnear' w hw).2.1.contDiffWithinAt
  have hKball : ContDiffOn ℝ 1 K (ball (0 : ℂ) ε) :=
    fun w hw => (hnear' w hw).2.2.1.contDiffWithinAt
  have hKentry (i j : Fin 2) : ContDiffOn ℝ 1 (fun w => K w i j) (ball (0 : ℂ) ε) :=
    (contDiffOn_pi.mp ((contDiffOn_pi.mp hKball) i)) j
  refine ⟨ε, C, hε, ((min_le_right _ _).trans (min_le_left _ _)).trans hrL1, hC,
    (fun w hw => (hnear' w hw).1), hK0, hKball, ?_, ?_⟩
  · intro w hw
    exact (hstructure w (hεS hw)).2.2
  · intro ζ hζ
    have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by omega)
    have hrot (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) : ζ * w ∈ ball (0 : ℂ) ε := by
      simpa only [mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul] using hw
    have hWball : ContDiffOn ℝ 2 (W ζ) (ball (0 : ℂ) ε) :=
      hHball.sub (hHball.comp (contDiffOn_const.mul contDiffOn_id) hrot)
    have hW0 : W ζ 0 = 0 := by simp only [W, mul_zero, sub_self]
    obtain ⟨hDW0, hDDW0⟩ := branch_deck_secondJet_zero hH hDH hDDH ζ
    change fderiv ℝ (W ζ) 0 = 0 at hDW0
    change fderiv ℝ (fderiv ℝ (W ζ)) 0 = 0 at hDDW0
    have hpde (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) :
        Analysis.planarScalarOperator K
          (fun v => ![(bTilde ζ v).re, (bTilde ζ v).im]) (cTilde ζ) (W ζ) w = 0 := by
      by_cases hw0 : w = 0
      · subst w
        simp [Analysis.planarScalarOperator, hW0, hDW0, hDDW0]
      have hwtarget := (hnear' w hw).1
      have hζwtarget := (hnear' (ζ * w) (hrot w hw)).1
      have hζ0 : ζ ≠ 0 := by intro h; simp [h] at hζ
      obtain ⟨e₁, hw₁, hs₁, he₁, hei₁⟩ := hgraphs w hwtarget hw0
      obtain ⟨e₂, hw₂, hs₂, he₂, hei₂⟩ :=
        hgraphs (ζ * w) hζwtarget (mul_ne_zero hζ0 hw0)
      exact chartLeadingPlaneProjection_root_pair_height_difference
        g hs hU hconformal htension hchart N hunit hprojN hsplit L hL hm
        eRoot e₁ e₂ hs₁ hs₂ he₁ he₂ hei₁ hei₂ hpower
        ζ w hζ hw0 hwtarget hζwtarget hw₁ hw₂ ((hnear' w hw).2.2.2 ζ hζ)
    refine ⟨hW0, hDW0, hDDW0, hWball, ?_, hpde, ?_⟩
    · intro w hw
      exact ⟨((hlower ζ hζ).2.2 w (hεL hw)).2.1,
        ((hlower ζ hζ).2.2 w (hεL hw)).2.2⟩
    · intro φ hφ hφc hφs
      exact Analysis.planarScalarOperator_zero_weak_divergence isOpen_ball K
        (fun v => ![(bTilde ζ v).re, (bTilde ζ v).im]) (cTilde ζ)
        hKentry hWball hpde φ hφ hφc hφs

end DifferentialGeometry.Geometry
