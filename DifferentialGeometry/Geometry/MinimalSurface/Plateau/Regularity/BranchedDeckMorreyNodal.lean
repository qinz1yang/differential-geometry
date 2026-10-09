/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BranchedDeckWeakGauge
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientRootLowerMeasurable

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval InnerProductSpace ComplexConjugate
  Matrix.Norms.Elementwise

namespace DifferentialGeometry.Geometry

-- Construct the literal fields in small contexts before elaborating their continuation.
private abbrev morreyNodalFields1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) (a : ℂ)
    (B : ℂ → Fin (Module.finrank ℝ E) → ℂ)
    (eRoot : OpenPartialHomeomorph ℂ ℂ) (N : E)
    (k : (ℂ → M) → M → (Fin (Module.finrank ℝ E) → ℂ) →
      (ℂ → E) → (ℂ → ℂ) → ℂ → (ℂ → ℝ) → Prop) : Prop :=
  let U : ℂ → M := diskExtension q
  let p := U a
  let b := B a
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
  let c := F a
  let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
  k U p b X F c H

private theorem morreyNodalFields1_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (q : C(closedDisk, M)) (a : ℂ)
    (B : ℂ → Fin (Module.finrank ℝ E) → ℂ)
    (eRoot : OpenPartialHomeomorph ℂ ℂ) (N : E)
    (k : (ℂ → M) → M → (Fin (Module.finrank ℝ E) → ℂ) →
      (ℂ → E) → (ℂ → ℂ) → ℂ → (ℂ → ℝ) → Prop) :
    morreyNodalFields1 g q a B eRoot N k =
      (let U : ℂ → M := diskExtension q
       let p := U a
       let b := B a
       let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
       let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
       let c := F a
       let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
       k U p b X F c H) := rfl

private abbrev morreyNodalFields2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (a : ℂ) (p : M)
    (b : Fin (Module.finrank ℝ E) → ℂ) (c : ℂ) (m : ℕ) (H : ℂ → ℝ)
    (k : (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] ℂ) →
      (ℂ → ℂ) → (ℂ → ℂ → ℝ) → Prop) : Prop :=
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  let W : ℂ → ℂ → ℝ := fun ζ w => H w - H (ζ * w)
  k Q proj P W

private theorem morreyNodalFields2_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (U : ℂ → M) (a : ℂ) (p : M)
    (b : Fin (Module.finrank ℝ E) → ℂ) (c : ℂ) (m : ℕ) (H : ℂ → ℝ)
    (k : (E →L[ℝ] E →L[ℝ] ℝ) → (E →L[ℝ] ℂ) →
      (ℂ → ℂ) → (ℂ → ℂ → ℝ) → Prop) :
    morreyNodalFields2 g U a p b c m H k =
      (let Q := chartGramBilin g p (U a)
       let proj := chartLeadingPlaneProjection g p (U a) b
       let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
       let W : ℂ → ℂ → ℝ := fun ζ w => H w - H (ζ * w)
       k Q proj P W) := rfl

-- This scalar conclusion needs none of the ambient manifold instances.
private abbrev morreyNodalScalarTail
    (m : ℕ) (eRoot : OpenPartialHomeomorph ℂ ℂ)
    (H : ℂ → ℝ) (W : ℂ → ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 1 H eRoot.target ∧
  ContDiffOn ℝ ∞ H (eRoot.target \ {0}) ∧
  ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ball (0 : ℂ) ε ⊆ eRoot.target ∧
    ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      ContDiffOn ℝ 2 (W ζ) (ball (0 : ℂ) ε) ∧
      ContDiffOn ℝ ∞ (W ζ) (ball (0 : ℂ) ε \ {0}) ∧
      ∃ eIso : OpenPartialHomeomorph ℂ ℂ,
        0 ∈ eIso.source ∧ eIso.source ⊆ ball (0 : ℂ) ε ∧ eIso 0 = 0 ∧
        ContDiffOn ℝ 1 eIso eIso.source ∧
        ContDiffOn ℝ 1 eIso.symm eIso.target ∧
        (∀ z ∈ eIso.source, 0 < (fderiv ℝ eIso z).det) ∧
        let v : ℂ → ℝ := fun y => W ζ (eIso.symm y)
        v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧ ContDiffOn ℝ 1 v eIso.target ∧
        (∀ z ∈ eIso.source, v (eIso z) = W ζ z) ∧
        ((∀ᶠ w in 𝓝 (0 : ℂ), W ζ w = 0) ∨
          ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ eIso.target ∧
            (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
            ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
              (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
                HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
                Set.InjOn (Γ s) (Ico 0 ρ) ∧
                ∀ r ∈ Ico 0 ρ, ‖Γ s r‖ = r ∧ v (Γ s r) = 0) ∧
              ∀ z ∈ ball (0 : ℂ) ρ,
                v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r)

private theorem morreyNodalScalarTail_eq
    (m : ℕ) (eRoot : OpenPartialHomeomorph ℂ ℂ)
    (H : ℂ → ℝ) (W : ℂ → ℂ → ℝ) :
    morreyNodalScalarTail m eRoot H W =
      (ContDiffOn ℝ 1 H eRoot.target ∧
       ContDiffOn ℝ ∞ H (eRoot.target \ {0}) ∧
       ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ball (0 : ℂ) ε ⊆ eRoot.target ∧
         ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
           ContDiffOn ℝ 2 (W ζ) (ball (0 : ℂ) ε) ∧
           ContDiffOn ℝ ∞ (W ζ) (ball (0 : ℂ) ε \ {0}) ∧
           ∃ eIso : OpenPartialHomeomorph ℂ ℂ,
             0 ∈ eIso.source ∧ eIso.source ⊆ ball (0 : ℂ) ε ∧ eIso 0 = 0 ∧
             ContDiffOn ℝ 1 eIso eIso.source ∧
             ContDiffOn ℝ 1 eIso.symm eIso.target ∧
             (∀ z ∈ eIso.source, 0 < (fderiv ℝ eIso z).det) ∧
             let v : ℂ → ℝ := fun y => W ζ (eIso.symm y)
             v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧ ContDiffOn ℝ 1 v eIso.target ∧
             (∀ z ∈ eIso.source, v (eIso z) = W ζ z) ∧
             ((∀ᶠ w in 𝓝 (0 : ℂ), W ζ w = 0) ∨
               ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ eIso.target ∧
                 (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
                 ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
                   (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
                     HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
                     Set.InjOn (Γ s) (Ico 0 ρ) ∧
                     ∀ r ∈ Ico 0 ρ, ‖Γ s r‖ = r ∧ v (Γ s r) = 0) ∧
                   ∀ z ∈ ball (0 : ℂ) ρ,
                     v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r)) := rfl

private theorem morrey_nodal_scalar_facts
    {P0 P1 P2 P3 P4 P5 P6 : Prop}
    (h : P0 ∧ P1 ∧ P2 ∧ P3 ∧ P4 ∧ P5 ∧ P6) :
    P0 ∧ P1 ∧ P3 ∧ P4 ∧ P5 :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩

private theorem morrey_nodal_deck_radius_of_scalar_equations
    (m : ℕ) (eRoot : OpenPartialHomeomorph ℂ ℂ)
    (H : ℂ → ℝ) (K : ℂ → Matrix (Fin 2) (Fin 2) ℝ)
    (bTilde : ℂ → ℂ → ℂ) (cTilde : ℂ → ℂ → ℝ)
    (εP εM C : ℝ)
    (hεP : 0 < εP) (hεP1 : εP ≤ 1) (hεM : 0 < εM) (hC : 0 < C)
    (hεPRoot : ball (0 : ℂ) εP ⊆ eRoot.target)
    (hHsmooth : ContDiffOn ℝ ∞ H (eRoot.target \ {0}))
    (hK : ContDiffOn ℝ 1 K (ball (0 : ℂ) εP))
    (hKstructure : ∀ w ∈ ball (0 : ℂ) εP,
      (K w).IsSymm ∧ (K w).det = 1 ∧
        ∀ v : ℂ, (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
          ⟪v, complexPlaneMatrixOperator (K w) v⟫_ℝ ∧
          ⟪v, complexPlaneMatrixOperator (K w) v⟫_ℝ ≤ (3 / 2 : ℝ) * ‖v‖ ^ 2)
    (hPDE : ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      (fun w : ℂ => H w - H (ζ * w)) 0 = 0 ∧
      fderiv ℝ (fun w : ℂ => H w - H (ζ * w)) 0 = 0 ∧
      ContDiffOn ℝ 2 (fun w : ℂ => H w - H (ζ * w)) (ball (0 : ℂ) εP) ∧
      (∀ w ∈ ball (0 : ℂ) εP,
        ‖bTilde ζ w‖ ≤ C * ‖w‖ ∧ ‖cTilde ζ w‖ ≤ C * ‖w‖ ^ m) ∧
      ∀ w ∈ ball (0 : ℂ) εP,
        Analysis.planarScalarOperator K
          (fun v => ![(bTilde ζ v).re, (bTilde ζ v).im]) (cTilde ζ)
          (fun v : ℂ => H v - H (ζ * v)) w = 0)
    (hMeas : ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      Measurable (fun w : ball (0 : ℂ) εM => bTilde ζ w) ∧
      Measurable (fun w : ball (0 : ℂ) εM => cTilde ζ w)) :
  ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ball (0 : ℂ) ε ⊆ eRoot.target ∧
    ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      ContDiffOn ℝ 2 ((fun w : ℂ => H w - H (ζ * w))) (ball (0 : ℂ) ε) ∧
      ContDiffOn ℝ ∞ ((fun w : ℂ => H w - H (ζ * w))) (ball (0 : ℂ) ε \ {0}) ∧
      ∃ eIso : OpenPartialHomeomorph ℂ ℂ,
        0 ∈ eIso.source ∧ eIso.source ⊆ ball (0 : ℂ) ε ∧ eIso 0 = 0 ∧
        ContDiffOn ℝ 1 eIso eIso.source ∧
        ContDiffOn ℝ 1 eIso.symm eIso.target ∧
        (∀ z ∈ eIso.source, 0 < (fderiv ℝ eIso z).det) ∧
        let v : ℂ → ℝ := fun y => (fun w : ℂ => H w - H (ζ * w)) (eIso.symm y)
        v 0 = 0 ∧ fderiv ℝ v 0 = 0 ∧ ContDiffOn ℝ 1 v eIso.target ∧
        (∀ z ∈ eIso.source, v (eIso z) = (fun w : ℂ => H w - H (ζ * w)) z) ∧
        ((∀ᶠ w in 𝓝 (0 : ℂ), (fun w : ℂ => H w - H (ζ * w)) w = 0) ∨
          ∃ ρ : ℝ, 0 < ρ ∧ ball (0 : ℂ) ρ ⊆ eIso.target ∧
            (∀ z ∈ ball (0 : ℂ) ρ, z ≠ 0 → fderiv ℝ v z ≠ 0) ∧
            ∃ S : Set ℝ, S.Finite ∧ ∃ Γ : S → ℝ → ℂ,
              (∀ s, Γ s 0 = 0 ∧ ContDiffOn ℝ 1 (Γ s) (Ioo (-ρ) ρ) ∧
                HasDerivAt (Γ s) (Complex.exp (((s : ℝ) : ℂ) * Complex.I)) 0 ∧
                Set.InjOn (Γ s) (Ico 0 ρ) ∧
                ∀ r ∈ Ico 0 ρ, ‖Γ s r‖ = r ∧ v (Γ s r) = 0) ∧
              ∀ z ∈ ball (0 : ℂ) ρ,
                v z = 0 ↔ z = 0 ∨ ∃ s : S, ∃ r ∈ Ioo 0 ρ, z = Γ s r) := by
  classical
  let W : ℂ → ℂ → ℝ := fun ζ w => H w - H (ζ * w)
  let ε : ℝ := min εP εM
  have hε : 0 < ε := lt_min hεP hεM
  have hεPsub : ball (0 : ℂ) ε ⊆ ball (0 : ℂ) εP :=
    ball_subset_ball (min_le_left _ _)
  have hεMsub : ball (0 : ℂ) ε ⊆ ball (0 : ℂ) εM :=
    ball_subset_ball (min_le_right _ _)
  have hεRoot : ball (0 : ℂ) ε ⊆ eRoot.target := hεPsub.trans hεPRoot
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans hεP1
  refine ⟨ε, hε, hε1, hεRoot, ?_⟩
  intro ζ hζ
  obtain ⟨hW0, hDW0, hW, hbounds, hpde⟩ := hPDE ζ hζ
  obtain ⟨hbmeas, hcmeas⟩ := hMeas ζ hζ
  have hbmeas' : Measurable (fun w : ball (0 : ℂ) ε => bTilde ζ w) :=
    hbmeas.comp (measurable_inclusion hεMsub)
  have hcmeas' : Measurable (fun w : ball (0 : ℂ) ε => cTilde ζ w) :=
    hcmeas.comp (measurable_inclusion hεMsub)
  let beta : ℂ → Fin 2 → ℝ := fun w => ![(bTilde ζ w).re, (bTilde ζ w).im]
  have hbeta : ∀ j, Measurable (fun w : ball (0 : ℂ) ε => beta w j) := by
    intro j
    fin_cases j
    · exact Complex.continuous_re.measurable.comp hbmeas'
    · exact Complex.continuous_im.measurable.comp hbmeas'
  have hnorm (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) : ‖w‖ ≤ 1 := by
    have hw' : ‖w‖ < ε := by simpa only [mem_ball, dist_zero_right] using hw
    exact hw'.le.trans hε1
  have hbBound (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) : ‖bTilde ζ w‖ ≤ C := by
    calc
      ‖bTilde ζ w‖ ≤ C * ‖w‖ := (hbounds w (hεPsub hw)).1
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (hnorm w hw) hC.le
      _ = C := mul_one C
  have hbetaBound : ∀ w ∈ ball (0 : ℂ) ε, ∀ j, |beta w j| ≤ C := by
    intro w hw j
    fin_cases j
    · exact (Complex.abs_re_le_norm (bTilde ζ w)).trans (hbBound w hw)
    · exact (Complex.abs_im_le_norm (bTilde ζ w)).trans (hbBound w hw)
  have hcBound (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε) : |cTilde ζ w| ≤ C := by
    calc
      |cTilde ζ w| = ‖cTilde ζ w‖ := (Real.norm_eq_abs _).symm
      _ ≤ C * ‖w‖ ^ m := (hbounds w (hεPsub hw)).2
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left
        (pow_le_one₀ (norm_nonneg w) (hnorm w hw)) hC.le
      _ = C := mul_one C
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by omega)
  have hζ0 : ζ ≠ 0 := by
    intro hz
    simp [hz] at hζ
  have hrot (w : ℂ) (hw : w ∈ ball (0 : ℂ) ε \ {0}) :
      ζ * w ∈ eRoot.target \ {0} := by
    refine ⟨hεRoot ?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul] using hw.1
    · simp only [mem_singleton_iff] at hw ⊢
      exact mul_ne_zero hζ0 hw.2
  have hWsmooth : ContDiffOn ℝ ∞ (W ζ) (ball (0 : ℂ) ε \ {0}) :=
    (hHsmooth.mono (fun w hw => ⟨hεRoot hw.1, hw.2⟩)).sub
      (hHsmooth.comp (contDiffOn_const.mul contDiffOn_id) hrot)
  obtain ⟨eIso, he0, heBall, hezero, heC1, heiC1, hedet,
      hv0, hDv0, hv, hsame, hnodal⟩ :=
    Analysis.exists_branch_deck_c1_nodal_chart isOpen_ball (mem_ball_self hε)
      K beta (cTilde ζ) (W ζ) (hK.mono hεPsub)
      (fun w hw => (hKstructure w (hεPsub hw)).1)
      (fun w hw => (hKstructure w (hεPsub hw)).2.1)
      (fun w hw v => ((hKstructure w (hεPsub hw)).2.2 v).1)
      (hW.mono hεPsub) hW0 hDW0 (fun w hw => hpde w (hεPsub hw))
      hbeta hcmeas' hC.le hC.le hbetaBound hcBound
  refine ⟨hW.mono hεPsub, hWsmooth, eIso, he0, heBall, hezero, heC1, heiC1,
    hedet, hv0, hDv0, hv, hsame, ?_⟩
  rcases hnodal with hzero | hnodal
  · left
    have heTendsto : Tendsto eIso (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
      simpa only [hezero] using (eIso.continuousAt he0).tendsto
    have hzeroPull : ∀ᶠ w in 𝓝 (0 : ℂ), W ζ (eIso.symm (eIso w)) = 0 :=
      heTendsto.eventually hzero
    filter_upwards [hzeroPull, eIso.open_source.mem_nhds he0] with w hw hws
    simpa only [eIso.left_inv hws] using hw
  · exact Or.inr hnodal

private theorem morrey_nodal_scalar_tail_of_projection_graph
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
    let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
    ContDiffAt ℝ 2 H 0 → H 0 = 0 → fderiv ℝ H 0 = 0 →
    fderiv ℝ (fderiv ℝ H) 0 = 0 →
    (∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) →
    ContDiffOn ℝ 1 H eRoot.target →
    ContDiffOn ℝ ∞ H (eRoot.target \ {0}) →
    morreyNodalScalarTail m eRoot H (fun ζ w => H w - H (ζ * w)) := by
  classical
  intro X H hH hH0 hDH hDDH hHess hHroot hHsmooth
  let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
  let c := F a
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
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
  have hWeak := chartLeadingPlaneProjection_root_pair_weak_equation g hs
    hU hconformal htension has hchart hb hnull N hunit hprojN hsplit
    L hL hm eRoot he0 hgraphs hpower hH hH0 hDH hDDH hHess
  obtain ⟨εP, C, hεP, hεP1, hC, hεPRoot, _hK0, hK, hKstructure, hPDE⟩ := hWeak
  have hMeas := chartLeadingPlaneProjection_root_lower_terms_measurable g
    (hchart a has) hb hnull hprojN hunit L hL c hm hH hH0 hDH hHess
  obtain ⟨εM, hεM, _hεM1, hMeas⟩ := hMeas
  have hPDEscalar (ζ : ℂ) (hζ : ζ ^ (m + 1) = 1) :=
    morrey_nodal_scalar_facts (hPDE ζ hζ)
  have hRadius := morrey_nodal_deck_radius_of_scalar_equations m eRoot H K bTilde cTilde
    εP εM C hεP hεP1 hεM hC hεPRoot hHsmooth hK hKstructure hPDEscalar hMeas
  exact ⟨hHroot, hHsmooth, hRadius⟩

/-- One actual Morrey branch tuple supplies its literal deck equations, their
measurable lower coefficients, and the resulting C1 nodal classification. The
root coordinate, normal, disk and original metric are shared by both analytic
suppliers. The zero alternative is stated back in the original root coordinate;
the nodal alternative retains the one constructed isothermal coordinate. -/
theorem IsMorreyDisk.exists_branched_deck_nodal_chart_of_not_injective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hd3 : Module.finrank ℝ E = 3)
    {a : ℂ} (ha : a ∈ ball (0 : ℂ) 1)
    (hbranch : ¬ Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) a)) :
    ∃ (m : ℕ) (B : ℂ → Fin (Module.finrank ℝ E) → ℂ)
      (eRoot : OpenPartialHomeomorph ℂ ℂ) (N : E) (L : ℂ →L[ℝ] E),
      1 ≤ m ∧ ContDiffAt ℝ 1 B a ∧ B a ≠ 0 ∧
      (∀ᶠ z in 𝓝 a,
        (fun i => chartComplexGradient (E := E)
          (diskExtension q a) (diskExtension q) i z) = (z - a) ^ m • B z) ∧
      morreyNodalFields1 g q a B eRoot N (fun U p b _X F c H =>
        morreyNodalFields2 g U a p b c m H (fun Q proj P W =>
          a ∈ eRoot.source ∧ eRoot a = 0 ∧ eRoot.source ⊆ ball (0 : ℂ) 1 ∧
            HasFDerivAt (eRoot : ℂ → ℂ) (ContinuousLinearMap.id ℝ ℂ) a ∧
            ContDiffOn ℝ 1 (eRoot : ℂ → ℂ) eRoot.source ∧
            ContDiffOn ℝ 1 (eRoot.symm : ℂ → ℂ) eRoot.target ∧
            ContDiffOn ℝ ∞ (eRoot : ℂ → ℂ) (eRoot.source \ {a}) ∧
            ContDiffOn ℝ ∞ (eRoot.symm : ℂ → ℂ) (eRoot.target \ {0}) ∧
            (∀ z ∈ eRoot.source, U z ∈ (chartAt E p).source) ∧
            (∀ z ∈ eRoot.source, z ≠ a → (fderiv ℝ F z).IsInvertible) ∧
            (∀ w ∈ eRoot.target, F (eRoot.symm w) = P w) ∧
            Q N N = 1 ∧ proj N = 0 ∧
            (∀ v : E, v = L (proj v) + (Q N v) • N) ∧
            (∀ v, L v = (chartModelBasis E).equivFunL.symm
              (fun i => (2 : ℝ) * (v * b i).re)) ∧
          morreyNodalScalarTail m eRoot H W)) := by
  classical
  obtain ⟨m, B, hB, hBne, hfactor, hpositive, hrest⟩ :=
    DiskRegularity.ConsumerAudit.morrey_branched_coordinate_with_projection_graph_hessian_bound
      hq hγ hd3 ha
  have hm : 1 ≤ m := hpositive hbranch
  dsimp only at hrest
  obtain ⟨r, δ, hr, _hδ, hsub, hchart, hreg, _hcenter, _hgap, _hcover, _hcard,
    ρ, hρ, hρr, eRoot, hesource, he, hea, hederiv, heC1, heiC1,
    heSmooth, heiSmooth, _hepower, hheight, N, hNN, hN, hsplit, hgraphs, _hgraphHessian⟩ := hrest
  let L : ℂ →L[ℝ] E := (chartModelBasis E).equivFunL.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => (2 : ℝ) •
      Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (B a i)))
  have hL (v : ℂ) : L v = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (v * B a i).re) := by
    simp [L, smul_eq_mul, mul_comm]
  refine ⟨m, B, eRoot, N, L, hm, hB, hBne, hfactor, ?_⟩
  let U : ℂ → M := diskExtension q
  let p := U a
  let b := B a
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => chartLeadingPlaneProjection g p (U a) b (X z)
  let c := F a
  let H : ℂ → ℝ := fun v => chartGramBilin g p (U a) N (X (eRoot.symm v) - X a)
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
  let W : ℂ → ℂ → ℝ := fun ζ w => H w - H (ζ * w)
  have hae : a ∈ eRoot.source := by rw [hesource]; exact mem_ball_self hρ
  have hrootBall : eRoot.source ⊆ ball a r := by
    rw [hesource]
    exact ball_subset_ball hρr.le
  have hrootClosed : eRoot.source ⊆ closedBall a r :=
    hrootBall.trans ball_subset_closedBall
  have hrootInterior : eRoot.source ⊆ ball (0 : ℂ) 1 := hrootClosed.trans hsub
  have heD : HasFDerivAt (eRoot : ℂ → ℂ) (ContinuousLinearMap.id ℝ ℂ) a := by
    rw [he]
    exact hederiv
  obtain ⟨hpower, hH, hDH, hDDH, hHess, _hgradientBounds⟩ := hheight hm N hN
  have hLsplit (v : E) : v = L (proj v) + (Q N v) • N := by
    rw [hL]
    exact hsplit v
  have h0target : (0 : ℂ) ∈ eRoot.target := by
    rw [← hea]
    exact eRoot.map_source hae
  have hinv0 : eRoot.symm 0 = a := by
    rw [← hea]
    exact eRoot.left_inv hae
  have hH0 : H 0 = 0 := by
    change Q N (X (eRoot.symm 0) - X a) = 0
    rw [hinv0, sub_self, map_zero]
  have hnull : (∑ i, ∑ j, (chartGramMatrix g p (U a) i j : ℂ) * b i * b j) = 0 :=
    chartComplexGradient_leading_isotropic g isOpen_ball
      (hq.smoothInterior.of_le (by simp)) hq.conformal ha (mem_chart_source E p)
      hB.continuousAt hfactor
  have hsInterior : ball a r ⊆ ball (0 : ℂ) 1 := ball_subset_closedBall.trans hsub
  have hgraphData : ∀ w ∈ eRoot.target, w ≠ 0 →
      ∃ eGraph : OpenPartialHomeomorph ℂ ℂ,
        eRoot.symm w ∈ eGraph.source ∧ eGraph.source ⊆ ball a r ∧
        (eGraph : ℂ → ℂ) = F ∧ ContDiffOn ℝ ∞ eGraph.symm eGraph.target := by
    intro w hw hw0
    obtain ⟨eGraph, hwGraph, hGraphSource, heGraph, heiGraph, _hGraphData⟩ :=
      hgraphs w hw hw0
    exact ⟨eGraph, hwGraph, fun z hz => (hGraphSource hz).1, heGraph, heiGraph⟩
  have hXsmooth : ContDiffOn ℝ ∞ X eRoot.source := by
    intro z hz
    have hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U z :=
      hq.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds (hrootInterior hz))
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hchart z (hrootClosed hz))
    exact ((hc.comp z hU).contDiffAt).contDiffWithinAt
  have hHroot : ContDiffOn ℝ 1 H eRoot.target :=
    (Q N).contDiff.comp_contDiffOn
      (((hXsmooth.of_le (by simp)).comp heiC1
        (fun w hw => eRoot.map_target hw)).sub contDiffOn_const)
  have hHsmooth : ContDiffOn ℝ ∞ H (eRoot.target \ {0}) :=
    (Q N).contDiff.comp_contDiffOn
      ((hXsmooth.comp heiSmooth
        (fun w hw => eRoot.map_target hw.1)).sub contDiffOn_const)
  refine ⟨hae, hea, hrootInterior, heD, heC1, heiC1, heSmooth, heiSmooth,
    (fun z hz => hchart z (hrootClosed hz)),
    (fun z hz hza => hreg z (hrootClosed hz) hza), hpower, hNN, hN, hLsplit, hL, ?_⟩
  have hScalar := morrey_nodal_scalar_tail_of_projection_graph g isOpen_ball
    (hq.smoothInterior.mono hsInterior)
    (fun z hz => hq.conformal z (hsInterior hz))
    (fun z hz => hq.harmonic z (hsInterior hz)) (mem_ball_self hr)
    (fun z hz => hchart z (ball_subset_closedBall hz)) hBne hnull N hNN hN hsplit
    L hL hm eRoot h0target hgraphData hpower hH hH0 hDH hDDH hHess
    hHroot hHsmooth
  exact hScalar

end DifferentialGeometry.Geometry
