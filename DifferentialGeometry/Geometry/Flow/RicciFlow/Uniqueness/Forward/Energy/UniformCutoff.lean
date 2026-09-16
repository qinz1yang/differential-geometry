import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Energy.CutoffInequality
import DifferentialGeometry.Geometry.Curvature.Bounds.MixedMetricDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [I.Boundaryless] [SigmaCompactSpace M]

theorem forward_uniqueness_cutoff_energy_uniform_bound
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M)
    {a b : ℝ}
    (hjoint₁ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₁ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hjoint₂ : ∀ (α : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => chartGramMatrix (I := I) (g₂ p.1) α p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) α).baseSet))
    (hpde₁ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₁ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₁ t) x v w) (Ici a) t)
    (hpde₂ : ∀ t ∈ Ico a b, ∀ (x : M) (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g₂ s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := I) (g₂ t) x v w) (Ici a) t)
    {C R₁ R₂ D₁ D₂ : ℝ} (hC : 1 ≤ C)
    (hEquiv : ∀ t ∈ Ico a b, ∀ x : M, ∀ v : TangentSpace I x,
      C⁻¹ * (g₁ t).inner x v v ≤ (g₂ t).inner x v v ∧
        (g₂ t).inner x v v ≤ C * (g₁ t).inner x v v)
    (hR₁ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₁ t) x 4 (metricRm04At (I := I) (g₁ t) x) ≤ R₁)
    (hR₂ : ∀ t ∈ Ico a b, ∀ x : M,
      normSq0S (I := I) (g₂ t) x 4 (metricRm04At (I := I) (g₂ t) x) ≤ R₂)
    (hD₁ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 5
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ D₁)
    (hD₂ : ∀ t ∈ Ico a b, ∀ x : M, normSq0S (I := I) (g₂ t) x 6
      (metricNabla0S (I := I) (g₂ t) (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.rm04Section (I := I) (g₂ t) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t)))) x) ≤ D₂) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (χ : C^∞⟮I, M; ℝ⟯), HasCompactSupport (χ : M → ℝ) →
      ∀ t ∈ Ioo a b,
      let S := forwardUniquenessSfield (I := I) g₁ g₂ t
      let A := metricNabla0S (I := I) (g₁ t) S
      let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
        ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
          (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
        (unitZeroSec (I := I) (M := M) x)
      let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
      deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
        ∂riemannianMeasureFamily g₁ s) t ≤
        K * (∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ) -
        (∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ) +
        10 * (∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ) := by
  let n : ℝ := Module.finrank ℝ E
  let Background : ℝ := C ^ 2 * n
  let BH : ℝ := 2 * n + 2 * Background
  let BR2 : ℝ := C ^ 4 * R₂
  let BP : ℝ := n ^ 7 * C ^ 6 * R₂
  let BRic2 : ℝ := n ^ 4 * R₂
  let BRic21 : ℝ := C ^ 2 * BRic2
  let Λric : ℝ := n ^ 4 * R₁
  let B5 : ℝ := C ^ 5 * D₁
  let B6 : ℝ := C ^ 6 * D₂
  let B₁ : ℝ := C ^ 3 * (n ^ 5 * D₁)
  let KQ : ℝ :=
    16 * (4 * n ^ 14 * (2 + 2 * n ^ 6 * BP) * (R₁ + BR2) +
      2 * (6 * n ^ 18 * C ^ 2 + 4 * n ^ 22 * C ^ 4 * BH) * BR2 ^ 2)
  let KD : ℝ := 32 * n ^ 6 * (n ^ 4 * R₁ + BRic21)
  let KR0 : ℝ := 200 * n ^ 12 * B5 + 8 * n ^ 10 * C ^ 2 * B6 + 16 * KQ + 2 * KD
  let BSpeed : ℝ := 8 * n ^ 6 * D₂ + 512 * n ^ 14 * R₂ ^ 2 + 72 * n ^ 6 * (BRic2 * R₂)
  let KG : ℝ := 8 * n ^ 10 * BP + 2 * C ^ 6 * n ^ 6 * BSpeed
  let C_rem : ℝ := 2 * KR0 + 2 * KG
  let KA : ℝ := 2 * (200 * (n ^ 6 + 1))
  let C_A : ℝ := max (8 * Λric + KA * ((1 + C) ^ 2 * (B₁ + BRic21))) KA
  let C_R : ℝ := (4 * n ^ 6 + 6 * n ^ 8 + 8 * n ^ 10) * Real.sqrt Λric
  let δ : ℝ := (4 * (C_A + 1))⁻¹
  let C_rest : ℝ := C_R + 4 * n ^ 4 + 1 + δ * C_A + δ⁻¹ + Real.sqrt (n * Λric)
  let C_U : ℝ := 32 * n ^ 5 * BR2 + 8 * n ^ 10 * (BP * Background)
  let C_V : ℝ := 4 * n ^ 15 * C ^ 7 * (C ^ 5 * B5) +
    (16 * n ^ 18 * C ^ 8 + 32 * n ^ 19 * C ^ 6) * R₂ * BH
  let K₀ : ℝ := C_rest + C_rem + 1 + ((1 / 4 : ℝ)⁻¹ + 2) * (2 * C_U + 2 * C_V)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCA : 0 ≤ C_A := (show 0 ≤ KA by dsimp [KA]; positivity).trans (le_max_right _ _)
  have hden : 0 < 4 * (C_A + 1) := by positivity
  have hδ : 0 < δ := inv_pos.mpr hden
  have hδCA : δ * C_A ≤ 1 / 4 := by
    change (4 * (C_A + 1))⁻¹ * C_A ≤ 1 / 4
    rw [mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    linarith
  refine ⟨max K₀ 0, le_max_right _ _, fun χ hχ t ht => ?_⟩
  have htime : t ∈ Ico a b := Ioo_subset_Ico_self ht
  have heq (x : M) := hEquiv t htime x
  have hsymm (x : M) := metric_equiv_symm (I := I) (g₁ t) (g₂ t) x hC (heq x)
  have htransfer {s : ℕ} (x : M) (T : Tensor0SSpace s I x) {B : ℝ}
      (hT : normSq0S (I := I) (g₂ t) x s T ≤ B) :
      normSq0S (I := I) (g₁ t) x s T ≤ C ^ s * B :=
    (normSq0S_upper_le_of_equiv (I := I) (g₂ t) (g₁ t) x s hC (hsymm x) T).trans
      (mul_le_mul_of_nonneg_left hT (pow_nonneg hC0 s))
  have hself (g : SmoothRiemannianMetric I M) (x : M) :
      normSq0S (I := I) g x 2 (metricTensorField (I := I) g x) = n := by
    obtain ⟨basis, hON⟩ := exists_orthonormal_basis (I := I) g x
    have hinv := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    have hfield : metricTensorField (I := I) g x = metricTensor0S (I := I) g x := by
      ext v
      rw [metricTensorField_apply, metricTensor0S_apply]
    rw [hfield]
    have hcard := normSq0S_metricTensor0S_eq_card (I := I) g basis _ hinv
    rw [Fintype.card_fin, show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl] at hcard
    exact hcard
  have hBackground (x : M) : normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₂ t) x) ≤ Background :=
    htransfer x _ (hself (g₂ t) x).le
  have hBH (x : M) : metricDiffSq (I := I) (g₁ t) (g₂ t) x ≤ BH := by
    have h := _root_.Tensor0SBundle.normSq0S_sub_le (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₁ t) x) (metricTensorField (I := I) (g₂ t) x)
    rw [hself] at h
    change normSq0S (I := I) (g₁ t) x 2
      (metricTensorField (I := I) (g₁ t) x - metricTensorField (I := I) (g₂ t) x) ≤ BH
    calc
      _ ≤ 2 * n + 2 * normSq0S (I := I) (g₁ t) x 2
          (metricTensorField (I := I) (g₂ t) x) := h
      _ ≤ 2 * n + 2 * Background :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hBackground x) (by norm_num : (0 : ℝ) ≤ 2))
  have hBP (x : M) : normSq0S (I := I) (g₁ t) x 4
      (CovariantDerivative.riemannCurvature04At (I := I) (g₁ t) (metricCov (I := I) (g₂ t))
        (metricCov_smooth (I := I) (g₂ t)) x) ≤ BP :=
    (norm_sq_cross_curvature_le (I := I) (g₁ t) (g₂ t) x hC (heq x)).trans
      (mul_le_mul_of_nonneg_left (hR₂ t htime x) (by positivity))
  have hRic₁ (x : M) : normSq0S (I := I) (g₁ t) x 2 (metricRicciAt (I := I) (g₁ t) x) ≤ Λric :=
    (ricciSq_le_rm04 (I := I) (g₁ t) (g₁ t) x).trans
      (mul_le_mul_of_nonneg_left (hR₁ t htime x) (pow_nonneg hn 4))
  have hRic₂ (x : M) : normSq0S (I := I) (g₂ t) x 2 (metricRicciAt (I := I) (g₂ t) x) ≤ BRic2 :=
    (ricciSq_le_rm04 (I := I) (g₂ t) (g₂ t) x).trans
      (mul_le_mul_of_nonneg_left (hR₂ t htime x) (pow_nonneg hn 4))
  have hD_Ric (x : M) : normSq0S (I := I) (g₂ t) x 3
      (metricNabla0S (I := I) (g₂ t)
        (CovariantDerivative.ricciSection (I := I) (metricCov (I := I) (g₂ t))
          (metricCov_smooth (I := I) (g₂ t))) x) ≤ n ^ 5 * D₁ := by
    let : CompleteSpace E := FiniteDimensional.complete ℝ E
    have hRic : metricRicci (g₂ t) =
        DifferentialGeometry.Tensor.RSTensor.metricTraceCovariantFourField (g₂ t) (metricRm04 (g₂ t)) := by
      simpa only [metricRicci, metricRm04, metricCov] using
        levi_civita_ricci_section_eq_riemann_trace (I := I) (g₂ t)
    have h := iterRic_normSq_le (g₂ t) (metricRm04 (g₂ t)) 1 x
    rw [← hRic] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hD₁ t htime x) (pow_nonneg hn 5))
  have henergy := forward_uniqueness_corrected_cutoff_energy_deriv_le (I := I)
    g₁ g₂ χ hχ hjoint₁ hjoint₂ hpde₁ hpde₂ ht hC0
    (fun x _ v => (hsymm x v).2) hC (fun x _ => heq x)
    (fun x _ => hBH x) (fun x _ => hR₁ t htime x)
    (fun x _ => htransfer x _ (hR₂ t htime x))
    (fun x _ => hBP x) (fun x _ => htransfer x _ (hRic₂ x))
    (fun x _ => htransfer x _ (hD₁ t htime x))
    (fun x _ => htransfer x _ (hD₂ t htime x))
    (fun x _ => hR₂ t htime x) (fun x _ => hRic₂ x) (fun x _ => hD₂ t htime x)
    (fun x _ => hBackground x) (η := 1 / 4) (ε := 1 / 4) (δ := δ)
    (by norm_num) (by norm_num) hδ (fun x _ => hRic₁ x)
    (fun x _ => htransfer x _ (hD_Ric x))
  let S := forwardUniquenessSfield (I := I) g₁ g₂ t
  let A := metricNabla0S (I := I) (g₁ t) S
  let B := fun x => (covGradBundleEquiv (I := I) (M := M) 0 4 x
    ((mvfderiv (I := I) (χ : M → ℝ) x).smulRight
      (unitScalarRSLiftSection (I := I) (M := M) (fun y => S y) x)))
    (unitZeroSec (I := I) (M := M) x)
  let μ := riemannianVolumeMeasure (I := I) (M := M) (g₁ t)
  let energy : ℝ := ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x ∂μ
  let dissipation : ℝ := ∫ x, χ x ^ 2 * normSq0S (I := I) (g₁ t) x 5 (A x) ∂μ
  let boundary : ℝ := ∫ x, normSq0S (I := I) (g₁ t) x 5 (B x) ∂μ
  have henergy0 : 0 ≤ energy := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg (χ x)) (density_nonneg (I := I) g₁ g₂ t x)
  have hdissipation0 : 0 ≤ dissipation := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg (χ x)) (normSq0S_nonneg (I := I) (g₁ t) x 5 (A x))
  change deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤
    K₀ * energy + (δ * C_A + 2 * (1 / 4) + 1 / 4 - 2) * dissipation +
      (2 * (1 / 4 : ℝ)⁻¹ + 2) * boundary at henergy
  change deriv (fun s => ∫ x, χ x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ s x
      ∂riemannianMeasureFamily g₁ s) t ≤ max K₀ 0 * energy - dissipation + 10 * boundary
  have hcoef : δ * C_A + 2 * (1 / 4) + 1 / 4 - 2 ≤ (-1 : ℝ) := by linarith
  have hdiss := mul_le_mul_of_nonneg_right hcoef hdissipation0
  have hK := mul_le_mul_of_nonneg_right (le_max_left K₀ 0) henergy0
  norm_num only [one_div, inv_inv] at henergy
  linarith only [henergy, hdiss, hK]

end DifferentialGeometry.PDE.RicciFlow
