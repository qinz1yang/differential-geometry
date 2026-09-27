import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.HoleFilling
import DifferentialGeometry.Geometry.HarmonicMap.WeakGradientBound
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BoundedDerivative

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

open Manifold
open scoped Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M]
  {ι : Type*} [Fintype ι]

open DifferentialGeometry.Analysis

theorem exists_weak_energy_hole_filling_factor
    (g : SmoothRiemannianMetric I M) {Φ : M → EuclideanSpace ℝ ι}
    (hΦ : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ ι) ∞ Φ)
    {ρ : EuclideanSpace ℝ ι → M} {U : Set (EuclideanSpace ℝ ι)}
    (hU : IsOpen U) (hρ : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ ι) I ∞ ρ U)
    (hΦU : range Φ ⊆ U) (hleft : Function.LeftInverse ρ Φ) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ 0 ≤ C / (1 + C) ∧ C / (1 + C) < 1 ∧
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin 2))), IsOpen Ω →
      ∀ (w : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι)
        (hw : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => w x i) Ω),
      (∀ᵐ x ∂volume.restrict Ω, w x ∈ range Φ) →
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ Ω →
      ∀ R : ℝ, 0 < R → R < 1 →
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
        ∑ j : Fin 2, pullbackMetricCoefficients g ρ (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) < ε →
      (∀ (q : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ ι)
        (hq : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => q x i) (Metric.ball 0 1)),
        (∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1),
          q x ∈ range Φ) →
        (q =ᵐ[volume.restrict
          (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1 \ Metric.closedBall 0 R)] w) →
        (∑ j : Fin 2, ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
          pullbackMetricCoefficients g ρ (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
        ∑ j : Fin 2, ∫ x in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R,
          pullbackMetricCoefficients g ρ (q x)
            (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hq i).weakGrad x j))) →
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R / 2),
        ∑ j : Fin 2, pullbackMetricCoefficients g ρ (w x)
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
          (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))) ≤
        C / (1 + C) * ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R,
          ∑ j : Fin 2, pullbackMetricCoefficients g ρ (w x)
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j))
            (WithLp.toLp 2 (fun i => (hw i).weakGrad x j)) := by
  let K := range Φ
  let A := pullbackMetricCoefficients g ρ
  have hK : IsCompact K := isCompact_range hΦ.continuous
  have hA : ContinuousOn A K :=
    (contDiffOn_pullback_metric_coefficients g hU hρ).continuousOn.mono hΦU
  have hpos : ∀ y ∈ K, ∀ v, 0 ≤ A y v v :=
    fun y _ v => metric_inner_self_nonneg g (ρ y) _
  obtain ⟨Λ₀, hΛ₀⟩ := hK.bddAbove_image
    ((@continuous_norm (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
      inferInstance).comp_continuousOn hA)
  let Λ := max Λ₀ 0
  have hΛ : ∀ y ∈ K, ‖A y‖ ≤ Λ := fun y hy =>
    (hΛ₀ (mem_image_of_mem _ hy)).trans (le_max_left _ _)
  have hΛ0 : 0 ≤ Λ := le_max_right _ _
  have hret : ContDiffOn ℝ ∞ (Φ ∘ ρ) U := (hΦ.comp_contMDiffOn hρ).contDiffOn
  have hretK : MapsTo (Φ ∘ ρ) U K := fun y _ => mem_range_self _
  have hretfix : ∀ y ∈ K, (Φ ∘ ρ) y = y := by
    rintro y ⟨p, rfl⟩
    exact congrArg Φ (hleft p)
  obtain ⟨V, T, L, hV, hKV, _, _, hT, _, _, hL, hTK, hfix⟩ :=
    exists_contDiff_retraction_extension_fderiv_bound hK hU hΦU (Φ ∘ ρ) hret hretK hretfix
  obtain ⟨η, hη, hηV⟩ := hK.exists_thickening_subset_open hV hKV
  have htube : ∀ p ∈ K, Metric.ball p η ⊆ V :=
    fun p hp => (Metric.ball_subset_thickening hp η).trans hηV
  obtain ⟨C₀, hC₀, hcoercive⟩ :=
    exists_weak_gradient_norm_sq_le_pullback_metric_on_ball g hΦ hU hρ hΦU hleft
  let κ : ℝ := (C₀ : ℝ) ^ 2
  have hκ : 0 < κ := sq_pos_of_pos (by exact_mod_cast hC₀)
  let ε := η ^ 2 / (8 * Real.pi * κ)
  let C := 40 * Λ * Real.pi ^ 2 * L ^ 2 * κ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hden : 0 < 1 + C := by positivity
  refine ⟨ε, C, by dsimp only [ε]; positivity, hC, div_nonneg hC hden.le,
    (div_lt_one hden).mpr (by linarith), ?_⟩
  intro Ω hΩ w hw hwK hball R hR hR1 hsmallE hmin
  let ew := weakMapMetricDensity A hw
  let nw := fun x =>
    ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 0) : EuclideanSpace ℝ ι)‖ ^ 2 +
    ‖(WithLp.toLp 2 (fun i => (hw i).weakGrad x 1) : EuclideanSpace ℝ ι)‖ ^ 2
  let S := Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 (R / 2)
  have hBΩ : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R ⊆ Ω :=
    (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hR1.le)).trans hball
  have hwKR : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R), w x ∈ K :=
    ae_restrict_of_ae_restrict_of_subset hBΩ hwK
  have hiw : IntegrableOn ew (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R) :=
    integrable_weakMapMetricDensity hBΩ hw hK A hA hwKR
  have hG (j : Fin 2) : MemLp (fun x =>
      (WithLp.toLp 2 (fun i => (hw i).weakGrad x j) : EuclideanSpace ℝ ι)) 2
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :=
    MemLp.of_eval_piLp fun i => ((hw i).weakGrad_component_memLp j).mono_measure
      (Measure.restrict_mono_set volume hBΩ)
  have hin : IntegrableOn nw (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R) :=
    (hG 0).norm.integrable_sq.add (hG 1).norm.integrable_sq
  have hcoer : ∀ᵐ x ∂volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R),
      nw x ≤ κ * ew x := by
    have h0 := hcoercive 2 Ω hΩ w hw hwK 0 R
      ((Metric.closedBall_subset_closedBall hR1.le).trans hball) 0
    have h1 := hcoercive 2 Ω hΩ w hw hwK 0 R
      ((Metric.closedBall_subset_closedBall hR1.le).trans hball) 1
    filter_upwards [h0, h1] with x hx0 hx1
    simpa only [nw, ew, weakMapMetricDensity, Fin.sum_univ_two, mul_add] using
      add_le_add hx0 hx1
  have hNann : (∫ x in S, nw x) ≤ κ * ∫ x in S, ew x := by
    rw [← integral_const_mul]
    exact integral_mono_ae (hin.mono_set sdiff_subset)
      ((hiw.mono_set sdiff_subset).const_mul κ)
      (ae_restrict_of_ae_restrict_of_subset sdiff_subset hcoer)
  have hhalf : R / 2 < R := by linarith
  have hsplit := integral_ball_add_collar ew hhalf.le hiw
  have hEhalf0 : 0 ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R / 2), ew x := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (Metric.ball_subset_ball hhalf.le) hwKR] with x hx
    exact Finset.sum_nonneg fun j _ => hpos (w x) hx _
  have hEann : (∫ x in S, ew x) ≤ ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ew x := by
    linarith
  have hNball := hNann.trans (mul_le_mul_of_nonneg_left hEann hκ.le)
  have hratio : 4 * Real.pi * R / (R - R / 2) = 8 * Real.pi := by
    field_simp
    ring
  have hsmall : (4 * Real.pi * R / (R - R / 2)) * (∫ x in S, nw x) < η ^ 2 := by
    rw [hratio]
    apply (mul_le_mul_of_nonneg_left hNball (by positivity : 0 ≤ 8 * Real.pi)).trans_lt
    have hs : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ew x) <
        η ^ 2 / (8 * Real.pi * κ) := hsmallE
    have ht := (lt_div_iff₀ (by positivity : 0 < 8 * Real.pi * κ)).mp hs
    nlinarith
  have hhole := weak_energy_ball_le_annulus_of_minimal hK hV hKV T hT hTK hfix hL
    hΩ hw hwK hball (by positivity : 0 < R / 2) hhalf hR1 hη htube
    A hA hpos hΛ hΛ0 hsmall hmin
  have hfactor : 4 * Λ * ((5 * Real.pi ^ 2 * R / (R - R / 2)) * L ^ 2) * κ = C := by
    have hradius : 5 * Real.pi ^ 2 * R / (R - R / 2) = 10 * Real.pi ^ 2 := by
      field_simp
      ring
    rw [hradius]
    dsimp only [C]
    ring
  have hstep : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R / 2), ew x) ≤
      C * ∫ x in S, ew x := by
    have hc : 0 ≤ 4 * Λ * ((5 * Real.pi ^ 2 * R / (R - R / 2)) * L ^ 2) := by
      have hd := sub_pos.mpr hhalf
      positivity
    have ht := hhole.trans (mul_le_mul_of_nonneg_left hNann hc)
    rwa [← mul_assoc, hfactor] at ht
  have hfinal : (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R / 2), ew x) ≤
      C / (1 + C) * ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ew x := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).mpr
      (show (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (R / 2), ew x) * (1 + C) ≤
        C * ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, ew x from by nlinarith)
  exact hfinal

end DifferentialGeometry.Geometry

end
