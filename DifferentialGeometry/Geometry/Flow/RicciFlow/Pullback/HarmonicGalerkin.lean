import DifferentialGeometry.Analysis.ODE.GlobalLipschitzAffineExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicPrincipal
import DifferentialGeometry.Geometry.Metric.TensorInner.CoerciveBilinInverse
import DifferentialGeometry.Analysis.Spectral.Tensor.EllipticBridge.EigenvectorWeakSolution.Smooth.EigenvectorSmoothToL2
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Finite moving-mass systems for the harmonic-map gauge

The weak harmonic-map equation has a time-dependent mass pairing because its
domain volume measure is the volume measure of the Ricci flow.  This file
packages the two finite-dimensional facts needed by a Galerkin construction:

* restriction of the smooth HMF mass and principal forms to a fixed finite
  trial space;
* existence for an ODE whose velocity is obtained by raising a Lipschitz
  covector field through a continuous uniformly coercive moving mass form.

The ODE theorem keeps the right derivative on `Ico 0 T`, hence includes the
one-sided derivative at the initial edge.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.Measure

/-! ## A moving coercive mass ODE -/

/-- A continuous family of uniformly coercive mass forms raises any
time-continuous, globally Lipschitz covector field to a forward ODE solution.
Only coercivity on the closed solution interval is required. -/
theorem coerciveODE_exists
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {mass : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    {resid : ℝ → V → (V →L[ℝ] ℝ)} {T c A : ℝ} {L : ℝ≥0}
    (hT : 0 < T) (hc : 0 < c) (hA : 0 ≤ A)
    (hmass : ContinuousOn mass (Icc (0 : ℝ) T))
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      c * ‖v‖ * ‖v‖ ≤ mass t v v)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hcont : ∀ v : V, ContinuousOn (fun t => resid t v) (Icc (0 : ℝ) T))
    (haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : V) :
    let hco : ∀ t ∈ Icc (0 : ℝ) T, IsCoercive (mass t) := fun t ht =>
      ⟨c, hc, hcoer t ht⟩
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((hco t ⟨ht.1, le_of_lt ht.2⟩).sharpCLM (resid t (γ t)))
          (Ici (0 : ℝ)) t := by
  classical
  dsimp only
  let hco : ∀ t ∈ Icc (0 : ℝ) T, IsCoercive (mass t) := fun t ht =>
    ⟨c, hc, hcoer t ht⟩
  let cinv : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  let K : ℝ≥0 := cinv * L
  let f : ℝ → V → V := fun t v =>
    if ht : t ∈ Icc (0 : ℝ) T then
      (hco t ht).sharpCLM (resid t v)
    else 0
  have hsharp_norm : ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      ‖(hco t ht).sharpCLM‖ ≤ c⁻¹ := by
    intro t ht
    exact (hco t ht).sharpCLM_norm_le hc (hcoer t ht)
  have hlip_f : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith K (f t) := by
    intro t ht
    have hsharp : LipschitzWith ‖(hco t ht).sharpCLM‖₊
        (hco t ht).sharpCLM := (hco t ht).sharpCLM.lipschitz
    have hcomp := hsharp.comp (hlip t ht)
    have hnorm_nn : ‖(hco t ht).sharpCLM‖₊ ≤ cinv := by
      exact_mod_cast hsharp_norm t ht
    have hKL : ‖(hco t ht).sharpCLM‖₊ * L ≤ K := by
      exact mul_le_mul_right' hnorm_nn L
    simpa only [f, dif_pos ht] using hcomp.weaken hKL
  have hsharp_cont : Continuous
      (fun t : Icc (0 : ℝ) T => (hco t t.2).sharpCLM) := by
    exact IsCoercive.sharpCLM_cont_sub mass hmass hco
  have hcont_f : ∀ v : V, ContinuousOn (fun t => f t v) (Icc (0 : ℝ) T) := by
    intro v
    rw [continuousOn_iff_continuous_restrict]
    have hres : Continuous (fun t : Icc (0 : ℝ) T => resid t v) :=
      (hcont v).restrict
    have happ := hsharp_cont.clm_apply hres
    simpa only [f, Set.restrict_apply, dif_pos] using happ
  have haff_f : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      ‖f t v‖ ≤ c⁻¹ * A + (K : ℝ) * ‖v‖ := by
    intro t ht v
    have hop := ContinuousLinearMap.le_opNorm
      (hco t ht).sharpCLM (resid t v)
    have hcnn : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    calc
      ‖f t v‖ = ‖(hco t ht).sharpCLM (resid t v)‖ := by
        simp only [f, dif_pos ht]
      _ ≤ ‖(hco t ht).sharpCLM‖ * ‖resid t v‖ := hop
      _ ≤ c⁻¹ * (A + (L : ℝ) * ‖v‖) :=
        mul_le_mul (hsharp_norm t ht) (haff t ht v) (norm_nonneg _) hcnn
      _ = c⁻¹ * A + (K : ℝ) * ‖v‖ := by
        simp only [K, cinv, NNReal.coe_mul, NNReal.coe_mk]
        ring
  have hA' : 0 ≤ c⁻¹ * A := mul_nonneg (inv_nonneg.mpr hc.le) hA
  obtain ⟨γ, hγ0, hγcont, hγderiv⟩ :=
    forward_solution_of_lipschitzWith_affineBound
      (E := V) (f := f) hT hA' hlip_f hcont_f haff_f v₀
  refine ⟨γ, hγ0, hγcont, ?_⟩
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_of_lt ht.2⟩
  simpa only [f, dif_pos ht'] using hγderiv t ht

/-! ## Globalization of a finite residual from one closed ball -/

/-- A residual which is continuous in time and `C¹` in the state on one
finite-dimensional closed ball can be composed with the radial retraction to
give the global Lipschitz/affine data required by `coerciveODE_exists`.

Crucially, the hypotheses ask only for joint continuity of the state
derivative, not differentiability in time.  This keeps the statement usable at
the initial edge of a Ricci flow, where the public uniqueness endpoint assumes
only joint `C⁰` metric regularity. -/
theorem retractResid_data
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : ℝ → V → W) {T R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn (Function.uncurry F)
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : V) R))
    (hD : ContinuousOn
      (fun p : ℝ × V => fderiv ℝ (F p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : V) R))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T, ∀ v ∈ Metric.closedBall (0 : V) R,
      DifferentiableAt ℝ (F t) v) :
    ∃ A : ℝ, ∃ L : ℝ≥0, 0 ≤ A ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        LipschitzWith L (fun v => F t (ballRetraction R v))) ∧
      (∀ v : V, ContinuousOn
        (fun t => F t (ballRetraction R v)) (Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
        ‖F t (ballRetraction R v)‖ ≤ A + (L : ℝ) * ‖v‖) := by
  let Q : Set (ℝ × V) :=
    Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : V) R
  have hQ : IsCompact Q :=
    isCompact_Icc.prod (isCompact_closedBall (0 : V) R)
  have hDnorm : ContinuousOn
      (fun p : ℝ × V => ‖fderiv ℝ (F p.1) p.2‖) Q := by
    exact hD.norm
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hDnorm
  let L : ℝ≥0 := ⟨max C 0, le_max_right C 0⟩
  have hDbound : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ v ∈ Metric.closedBall (0 : V) R,
        ‖fderiv ℝ (F t) v‖₊ ≤ L := by
    intro t ht v hv
    rw [← NNReal.coe_le_coe]
    exact (hC (t, v) ⟨ht, hv⟩).trans (le_max_left C 0)
  have hballLip : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith L (F t) (Metric.closedBall (0 : V) R) := by
    intro t ht
    exact lipschitzOnWith_of_nnnorm_fderiv_le
      (fun v hv => hdiff t ht v hv) (hDbound t ht)
      (convex_closedBall (0 : V) R)
  have hret : LipschitzWith 1 (ballRetraction (X := V) R) :=
    lipschitzWith_ballRetraction hR
  have hret_mem : ∀ v : V, ballRetraction R v ∈
      Metric.closedBall (0 : V) R := by
    intro v
    rw [Metric.mem_closedBall, dist_zero_right]
    exact ballRetraction_mem_closedBall hR v
  have hglobalLip : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzWith L (fun v => F t (ballRetraction R v)) := by
    intro t ht
    refine LipschitzWith.of_dist_le_mul (fun u v => ?_)
    have hlocal := (hballLip t ht).dist_le_mul
      (ballRetraction R u) (hret_mem u)
      (ballRetraction R v) (hret_mem v)
    have hnonexp := hret.dist_le_mul u v
    exact hlocal.trans
      (mul_le_mul_of_nonneg_left hnonexp L.coe_nonneg)
  have htime : ∀ v : V, ContinuousOn
      (fun t => F t (ballRetraction R v)) (Icc (0 : ℝ) T) := by
    intro v
    exact hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, hret_mem v⟩)
  have hzero_mem : (0 : V) ∈ Metric.closedBall (0 : V) R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR
  have hzero_cont : ContinuousOn (fun t => F t (0 : V)) (Icc (0 : ℝ) T) := by
    exact hF.comp (continuousOn_id.prodMk continuousOn_const)
      (fun t ht => ⟨ht, hzero_mem⟩)
  obtain ⟨C₀, hC₀⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hzero_cont
  let A : ℝ := |C₀|
  have hret_zero : ballRetraction R (0 : V) = 0 :=
    ballRetraction_eq_self_of_mem (by simpa using hR)
  have hzero_bound : ∀ t ∈ Icc (0 : ℝ) T,
      ‖F t (ballRetraction R (0 : V))‖ ≤ A := by
    intro t ht
    rw [hret_zero]
    exact (hC₀ t ht).trans (le_abs_self C₀)
  have haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      ‖F t (ballRetraction R v)‖ ≤ A + (L : ℝ) * ‖v‖ := by
    intro t ht v
    let G : V → W := fun w => F t (ballRetraction R w)
    have hdist := (hglobalLip t ht).dist_le_mul v 0
    have hdiff_norm : ‖G v - G 0‖ ≤ (L : ℝ) * ‖v‖ := by
      simpa only [G, dist_eq_norm, sub_zero] using hdist
    calc
      ‖F t (ballRetraction R v)‖ = ‖(G v - G 0) + G 0‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖G v - G 0‖ + ‖G 0‖ := norm_add_le _ _
      _ ≤ (L : ℝ) * ‖v‖ + A :=
        add_le_add hdiff_norm (hzero_bound t ht)
      _ = A + (L : ℝ) * ‖v‖ := add_comm _ _
  exact ⟨A, L, abs_nonneg C₀, hglobalLip, htime, haff⟩

/-! ## Restriction of the HMF forms to a finite trial space -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- The moving HMF mass pairing restricted along a fixed finite-dimensional
linear trial-space realization. -/
noncomputable def hmfFinMass
    (q h : SmoothRiemannianMetric I M)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => hmfMass (I := I) (M := M) q h (J u) (J v))
    (fun u₁ u₂ v => by rw [map_add, hmfMass_add_left])
    (fun a u v => by rw [map_smul, hmfMass_smul_left])
    (fun u v₁ v₂ => by rw [map_add, hmfMass_add_right])
    (fun a u v => by rw [map_smul, hmfMass_smul_right])).toContinuousBilinearMap

@[simp] theorem hmfFinMass_apply
    (q h : SmoothRiemannianMetric I M)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1) (u v : V) :
    hmfFinMass (I := I) (M := M) q h J u v =
      hmfMass (I := I) (M := M) q h (J u) (J v) := rfl

/-- The moving HMF principal form restricted to the same trial space. -/
noncomputable def hmfFinForm
    (q h : SmoothRiemannianMetric I M)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  (LinearMap.mk₂ ℝ
    (fun u v => hmfWeakForm (I := I) (M := M) q h (J u) (J v))
    (fun u₁ u₂ v => by rw [map_add, hmfWeak_add_left])
    (fun a u v => by rw [map_smul, hmfWeak_smul_left])
    (fun u v₁ v₂ => by rw [map_add, hmfWeak_add_right])
    (fun a u v => by rw [map_smul, hmfWeak_smul_right])).toContinuousBilinearMap

@[simp] theorem hmfFinForm_apply
    (q h : SmoothRiemannianMetric I M)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1) (u v : V) :
    hmfFinForm (I := I) (M := M) q h J u v =
      hmfWeakForm (I := I) (M := M) q h (J u) (J v) := rfl

/-- Joint chart-Gram continuity gives operator-norm continuity of every
finite HMF mass matrix. -/
theorem hmfFinMass_cont
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1) :
    ContinuousOn (fun t => hmfFinMass (I := I) (M := M) q (g t) J) K := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  simpa only [hmfFinMass_apply] using
    hmfMass_time_cont (I := I) (M := M) q g hK hcont (J u) (J v)

/-- A reference-orthonormal finite realization and reverse volume domination
give the explicit lower bound for the moving mass matrix. -/
theorem hmfFinMass_lower
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1)
    (horth : ∀ u : V,
      hmfMass (I := I) (M := M) q q (J u) (J u) = ‖u‖ ^ 2)
    (u : V) :
    C.toReal⁻¹ * ‖u‖ * ‖u‖ ≤
      hmfFinMass (I := I) (M := M) q h J u u := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  have hrev := hmfMass_self_rev (I := I) (M := M)
    q h C hC0 hCtop hvol (J u)
  rw [horth u] at hrev
  calc
    C.toReal⁻¹ * ‖u‖ * ‖u‖ = C.toReal⁻¹ * ‖u‖ ^ 2 := by ring
    _ ≤ hmfMass (I := I) (M := M) q h (J u) (J u) :=
      (inv_mul_le_iff₀ hCr).2 hrev
    _ = hmfFinMass (I := I) (M := M) q h J u u := by
      rw [hmfFinMass_apply]

/-- The finite moving mass matrix is coercive with the same explicit lower
constant. -/
theorem hmfFinMass_coercive
    (q h : SmoothRiemannianMetric I M) (C : ℝ≥0∞)
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) h)
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1)
    (horth : ∀ u : V,
      hmfMass (I := I) (M := M) q q (J u) (J u) = ‖u‖ ^ 2) :
    IsCoercive (hmfFinMass (I := I) (M := M) q h J) := by
  refine ⟨C.toReal⁻¹, inv_pos.mpr (ENNReal.toReal_pos hC0 hCtop), ?_⟩
  exact hmfFinMass_lower (I := I) (M := M)
    q h C hC0 hCtop hvol J horth

/-- On a compact time set, the inverse finite HMF mass matrix is continuous.
The proof uses only mass-coefficient continuity and the uniform reverse
volume comparison. -/
theorem hmfFinSharp_cont
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {K : Set ℝ} (hK : IsCompact K)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (K ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ K, riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1)
    (horth : ∀ u : V,
      hmfMass (I := I) (M := M) q q (J u) (J u) = ‖u‖ ^ 2) :
    Continuous (fun t : K =>
      (hmfFinMass_coercive (I := I) (M := M) q (g t) C hC0 hCtop
        (hvol t t.2) J horth).sharpCLM) := by
  apply IsCoercive.sharpCLM_cont_sub
  exact hmfFinMass_cont (I := I) (M := M) q g hK hcont J

/-- The finite moving-mass Galerkin system exists on the whole prescribed
time interval once its covector residual has uniform Lipschitz and affine
bounds.  Its equation holds on `Ico 0 T`, including the one-sided derivative
at `t = 0`. -/
theorem hmfFin_exists
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Icc (0 : ℝ) T ×ˢ
        (trivializationAt E (TangentSpace I) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (J : V →ₗ[ℝ] SmoothCcTensor q 0 1)
    (horth : ∀ u : V,
      hmfMass (I := I) (M := M) q q (J u) (J u) = ‖u‖ ^ 2)
    (resid : ℝ → V → (V →L[ℝ] ℝ)) {A : ℝ} {L : ℝ≥0} (hA : 0 ≤ A)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hres_cont : ∀ v : V,
      ContinuousOn (fun t => resid t v) (Icc (0 : ℝ) T))
    (haff : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : V) :
    ∃ γ : ℝ → V, γ 0 = v₀ ∧ ContinuousOn γ (Icc (0 : ℝ) T) ∧
      ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
        HasDerivWithinAt γ
          ((hmfFinMass_coercive (I := I) (M := M) q (g t) C hC0 hCtop
              (hvol t ⟨ht.1, le_of_lt ht.2⟩) J horth).sharpCLM
            (resid t (γ t)))
          (Ici (0 : ℝ)) t := by
  have hCr : 0 < C.toReal := ENNReal.toReal_pos hC0 hCtop
  let mass : ℝ → V →L[ℝ] V →L[ℝ] ℝ := fun t =>
    hmfFinMass (I := I) (M := M) q (g t) J
  have hmass : ContinuousOn mass (Icc (0 : ℝ) T) :=
    hmfFinMass_cont (I := I) (M := M) q g isCompact_Icc hcont J
  have hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ v : V,
      C.toReal⁻¹ * ‖v‖ * ‖v‖ ≤ mass t v v := by
    intro t ht v
    exact hmfFinMass_lower (I := I) (M := M)
      q (g t) C hC0 hCtop (hvol t ht) J horth v
  simpa only [mass] using
    (coerciveODE_exists (mass := mass) (resid := resid) hT (inv_pos.mpr hCr)
      hA hmass hcoer hlip hres_cont haff v₀)

/-! ## The canonical finite spectral trial spaces -/

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The smooth intrinsic eigenvectors are orthonormal for the frozen HMF
mass pairing. -/
theorem hmfSpec_orthonormal
    (q : SmoothRiemannianMetric I M) :
    Orthonormal ℝ
      (fun i : TensorEigenIdx (I := I) (M := M) q 0 1 =>
        eigenvectorSmooth (I := I) (M := M) q 0 1 i) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← DifferentialGeometry.Integral.L2.SmoothCcTensor.inner_toL2,
    eigenvectorSmooth_toL2 (I := I) (M := M) q 0 1 i,
    eigenvectorSmooth_toL2 (I := I) (M := M) q 0 1 j]
  have horth :=
    (tensorResolventHilbertEigenbasisSigma (I := I) (M := M)
      (tensorResolventL2_isCompactOperator (I := I) (M := M) q 0 1)).orthonormal
  rw [orthonormal_iff_ite] at horth
  simpa only [tensorResolventHilbertEigenbasisSigma_apply] using horth i j

/-- The canonical realization of a finite Euclidean coordinate vector as a
smooth `(0,1)` eigen-tensor combination. -/
noncomputable def hmfSpecIncl
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    EuclideanSpace ℝ {i // i ∈ S} →ₗ[ℝ] SmoothCcTensor q 0 1 where
  toFun u := ∑ j : {i // i ∈ S},
    u j • eigenvectorSmooth (I := I) (M := M) q 0 1 j.1
  map_add' u v := by
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

@[simp] theorem hmfSpecIncl_apply
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfSpecIncl (I := I) (M := M) q S u =
      ∑ j : {i // i ∈ S},
        u j • eigenvectorSmooth (I := I) (M := M) q 0 1 j.1 := rfl

/-- The canonical finite spectral realization is exactly isometric for the
frozen HMF mass. -/
theorem hmfSpecIncl_orth
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfMass (I := I) (M := M) q q
        (hmfSpecIncl (I := I) (M := M) q S u)
        (hmfSpecIncl (I := I) (M := M) q S u) = ‖u‖ ^ 2 := by
  rw [hmfMass_self]
  change ⟪hmfSpecIncl (I := I) (M := M) q S u,
      hmfSpecIncl (I := I) (M := M) q S u⟫_ℝ = ‖u‖ ^ 2
  rw [hmfSpecIncl_apply, hmfSpecIncl_apply]
  have horth : Orthonormal ℝ
      (fun j : {i // i ∈ S} =>
        eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) :=
    (hmfSpec_orthonormal (I := I) (M := M) q).comp
      Subtype.val Subtype.val_injective
  rw [horth.inner_sum (fun j => u j) (fun j => u j) Finset.univ]
  simp only [RCLike.conj_to_real]
  rw [EuclideanSpace.norm_sq_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Canonical finite spectral HMF Galerkin solutions exist for every finite
mode set once the full weak residual has the stated finite-dimensional
Lipschitz bounds.  The orbit equation includes the initial one-sided
derivative. -/
theorem hmfSpec_exists
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M) {T : ℝ} (hT : 0 < T)
    (hcont : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)), ContinuousOn
      (fun p : ℝ × M => chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
      (Icc (0 : ℝ) T ×ˢ
        (trivializationAt E (TangentSpace I) x₀).baseSet))
    (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I) (M := M) q ≤
        C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (resid : ℝ → EuclideanSpace ℝ {i // i ∈ S} →
      (EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ))
    {A : ℝ} {L : ℝ≥0} (hA : 0 ≤ A)
    (hlip : ∀ t ∈ Icc (0 : ℝ) T, LipschitzWith L (resid t))
    (hres_cont : ∀ v : EuclideanSpace ℝ {i // i ∈ S},
      ContinuousOn (fun t => resid t v) (Icc (0 : ℝ) T))
    (haff : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ v : EuclideanSpace ℝ {i // i ∈ S},
        ‖resid t v‖ ≤ A + (L : ℝ) * ‖v‖)
    (v₀ : EuclideanSpace ℝ {i // i ∈ S}) :
    ∃ γ : ℝ → EuclideanSpace ℝ {i // i ∈ S},
      γ 0 = v₀ ∧ ContinuousOn γ (Icc (0 : ℝ) T) ∧
        ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
          HasDerivWithinAt γ
            ((hmfFinMass_coercive (I := I) (M := M) q (g t) C hC0 hCtop
                (hvol t ⟨ht.1, le_of_lt ht.2⟩)
                (hmfSpecIncl (I := I) (M := M) q S)
                (hmfSpecIncl_orth (I := I) (M := M) q S)).sharpCLM
              (resid t (γ t)))
            (Ici (0 : ℝ)) t := by
  exact hmfFin_exists (I := I) (M := M) q g hT hcont C hC0 hCtop hvol
    (hmfSpecIncl (I := I) (M := M) q S)
    (hmfSpecIncl_orth (I := I) (M := M) q S)
    resid hA hlip hres_cont haff v₀

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
