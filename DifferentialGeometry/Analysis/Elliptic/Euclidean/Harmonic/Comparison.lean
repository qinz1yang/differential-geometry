import DifferentialGeometry.Analysis.Elliptic.Euclidean.LaplaceCoefficient
import DifferentialGeometry.External.DeGiorgi.WeakFormulation.ExistenceTheory
import DifferentialGeometry.Analysis.Integration.Integral.QuadraticComparison
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WitnessCongruence
import DifferentialGeometry.Analysis.Sobolev.Euclidean.DirichletEnergy.WeakLowerSemicontinuity
import DifferentialGeometry.Analysis.Elliptic.Euclidean.Harmonic.Decay
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Replacement.Harmonic
import DifferentialGeometry.Analysis.Integration.Integral.MeanSquareDeviation

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

omit [NeZero d] in
private theorem bilinear_apply_eq_sum [DecidableEq ι]
    (A : F →L[ℝ] F →L[ℝ] ℝ) (v w : F) :
    A v w = ∑ i : ι, ∑ k : ι,
      A (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) * v i * w k := by
  classical
  have hv : (∑ i : ι, v i • EuclideanSpace.single i 1) = v := by
    ext i
    simp [EuclideanSpace.single, Pi.single_apply]
  have hw : (∑ i : ι, w i • EuclideanSpace.single i 1) = w := by
    ext i
    simp [EuclideanSpace.single, Pi.single_apply]
  have hleft : A v w = ∑ i : ι, v i * A (EuclideanSpace.single i 1) w := by
    conv_lhs => rw [← hv]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro i hi
  have hright : A (EuclideanSpace.single i 1) w =
      ∑ k : ι, w k * A (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) := by
    conv_lhs => rw [← hw]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

omit [NeZero d] in
private theorem sum_bilinear_columns_eq_sum_inner [DecidableEq ι]
    (A : F →L[ℝ] F →L[ℝ] ℝ) (G H : ι → E) :
    (∑ j : Fin d, A (WithLp.toLp 2 (fun i => G i j)) (WithLp.toLp 2 (fun i => H i j))) =
      ∑ i : ι, ∑ k : ι, A (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
        inner ℝ (G i) (H k) := by
  have hexp (j : Fin d) := bilinear_apply_eq_sum A
    (WithLp.toLp 2 (fun i => G i j)) (WithLp.toLp 2 (fun i => H i j))
  simp only [hexp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [PiLp.inner_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [Fintype ι] in
theorem integral_bilinear_weakGrad_eq_zero_of_harmonic [Finite ι]
    {Ω : Set E} (hΩ : IsOpen Ω) {h v : E → F}
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) Ω)
    (hv : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => v x i) Ω)
    (hv0 : ∀ i, DeGiorgi.MemW01p 2 (fun x => v x i) Ω)
    (heuler : ∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    (A : F →L[ℝ] F →L[ℝ] ℝ) :
    (∫ x in Ω, ∑ j : Fin d,
      A (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hv i).weakGrad x j))) = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  have hsol (i : ι) : DeGiorgi.IsHomogeneousWeakSolution (DeGiorgi.EllipticCoeff.identity d Ω)
      (fun x => h x i) := by
    refine ⟨(hh i).memW1p, ?_⟩
    apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ
      (DeGiorgi.EllipticCoeff.identity d Ω) (fun _ => 0)
      (by intros; simp) (by intros; simp) 0 (by intros; simp) (hh i)
    intro φ hφ
    simpa only [DeGiorgi.bilinFormOfCoeff_identity, DeGiorgi.smoothTestWitness] using heuler i φ hφ
  have horth (i k : ι) : (∫ x in Ω, inner ℝ ((hh i).weakGrad x) ((hv k).weakGrad x)) = 0 := by
    simpa only [DeGiorgi.bilinFormOfCoeff_identity] using
      (hsol i).2 (hh i) (fun x => v x k) (hv0 k) (hv k)
  have hi (i k : ι) : IntegrableOn
      (fun x => A (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
        inner ℝ ((hh i).weakGrad x) ((hv k).weakGrad x)) Ω :=
    by
      have hinner : Integrable
          (fun x => inner ℝ ((hh i).weakGrad x) ((hv k).weakGrad x)) (volume.restrict Ω) := by
        have hi := DeGiorgi.integrable_bilinFormIntegrandOfCoeff
          (DeGiorgi.EllipticCoeff.identity d Ω) (hh i) (hv k)
        change Integrable (fun x => inner ℝ
          (DeGiorgi.matMulE 1 ((hh i).weakGrad x)) ((hv k).weakGrad x))
          (volume.restrict Ω) at hi
        simpa only [DeGiorgi.matMulE_one] using hi
      exact hinner.const_mul _
  simp_rw [sum_bilinear_columns_eq_sum_inner]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hi i k))]
  have heq (i : ι) : (∫ x in Ω, ∑ k : ι,
      A (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) *
        inner ℝ ((hh i).weakGrad x) ((hv k).weakGrad x)) = 0 := by
    rw [integral_finsetSum _ (fun k _ => hi i k)]
    simp_rw [integral_const_mul, horth, mul_zero]
    exact Finset.sum_const_zero
  simp only [heq, Finset.sum_const_zero]

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι

theorem sum_integral_weakGrad_norm_sq_eq_sum_columns
    {Ω : Set E} {u : E → F} (hu : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => u x i) Ω) :
    (∑ i : ι, ∫ x in Ω, ‖(hu i).weakGrad x‖ ^ 2) =
      ∑ j : Fin d, ∫ x in Ω,
        ‖(WithLp.toLp 2 (fun i => (hu i).weakGrad x j) : F)‖ ^ 2 := by
  have hrow (i : ι) : IntegrableOn (fun x => ‖(hu i).weakGrad x‖ ^ 2) Ω :=
    (hu i).weakGrad_memLp.norm.integrable_sq
  have hcol (j : Fin d) : MemLp (fun x => (WithLp.toLp 2
      (fun i => (hu i).weakGrad x j) : F)) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hu i).weakGrad_component_memLp j
  rw [← integral_finsetSum _ (fun i _ => hrow i),
    ← integral_finsetSum _ (fun j _ => (hcol j).norm.integrable_sq)]
  apply integral_congr_ae
  filter_upwards with x
  simp_rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_comm

theorem integral_weakGrad_difference_sq_le_of_harmonic_comparison
    [NeZero d] {Ω : Set E} (hΩ : IsOpen Ω) {z h : E → F}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) Ω)
    (htrace : ∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - z x i) Ω)
    (heuler : ∀ i (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    (A₀ : F →L[ℝ] F →L[ℝ] ℝ) (hsym : ∀ v w, A₀ v w = A₀ w v)
    {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 ≤ ε)
    (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ A₀ v v)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ)
    (hBz : ∀ v w, AEStronglyMeasurable (fun x => B (z x) v w) (volume.restrict Ω))
    (hBh : ∀ v w, AEStronglyMeasurable (fun x => B (h x) v w) (volume.restrict Ω))
    (hzclose : ∀ᵐ x ∂volume.restrict Ω, ‖B (z x) - A₀‖ ≤ ε)
    (hhclose : ∀ᵐ x ∂volume.restrict Ω, ‖B (h x) - A₀‖ ≤ ε)
    (hmin : (∑ j : Fin d, ∫ x in Ω, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      ∑ j : Fin d, ∫ x in Ω, B (h x)
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j)))
:
    (∑ i : ι, ∫ x in Ω, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
      (2 * ε / lam) * ∑ i : ι, ∫ x in Ω, ‖(hz i).weakGrad x‖ ^ 2 := by
  let diff := fun x => z x - h x
  let hd (i : ι) : DeGiorgi.MemW1pWitness 2 (fun x => diff x i) Ω :=
    ((hz i).add ((hh i).smul (-1))).congr (Eventually.of_forall fun x => by
      change z x i + -1 * h x i = z x i - h x i
      ring)
  have hd0 (i : ι) : DeGiorgi.MemW01p 2 (fun x => diff x i) Ω := by
    have ht := (htrace i).smul (-1)
    have heq : (fun x => -1 * (h x i - z x i)) = (fun x => diff x i) := by
      funext x
      change -1 * (h x i - z x i) = z x i - h x i
      ring
    rwa [← heq]
  have henergy : (∑ i : ι, ∫ x in Ω, ‖(hh i).weakGrad x‖ ^ 2) ≤
      ∑ i : ι, ∫ x in Ω, ‖(hz i).weakGrad x‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hsol : DeGiorgi.IsHomogeneousWeakSolution (DeGiorgi.EllipticCoeff.identity d Ω)
        (fun x => h x i) := by
      refine ⟨(hh i).memW1p, ?_⟩
      apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ
        (DeGiorgi.EllipticCoeff.identity d Ω) (fun _ => 0)
        (by intros; simp) (by intros; simp) 0 (by intros; simp) (hh i)
      intro φ hφ
      simpa only [DeGiorgi.bilinFormOfCoeff_identity, DeGiorgi.smoothTestWitness] using
        heuler i φ hφ
    have horthi : (∫ x in Ω, inner ℝ ((hh i).weakGrad x) ((hd i).weakGrad x)) = 0 := by
      simpa only [DeGiorgi.bilinFormOfCoeff_identity] using
        hsol.2 (hh i) (fun x => diff x i) (hd0 i) (hd i)
    have hLp : inner ℝ (DeGiorgi.gradLpOfWitness (hh i)) (DeGiorgi.gradLpOfWitness (hd i)) = 0 := by
      change (∫ x in Ω, inner ℝ (DeGiorgi.gradLpOfWitness (hh i) x)
        (DeGiorgi.gradLpOfWitness (hd i) x)) = 0
      apply (integral_congr_ae ?_).trans horthi
      filter_upwards [(hh i).weakGrad_memLp.coeFn_toLp, (hd i).weakGrad_memLp.coeFn_toLp]
        with x hx hy
      change inner ℝ ((hh i).weakGrad_memLp.toLp _ x) ((hd i).weakGrad_memLp.toLp _ x) = _
      rw [hx, hy]
    have hLp' :
        inner ℝ (DeGiorgi.gradLpOfWitness (hd i)) (DeGiorgi.gradLpOfWitness (hh i)) = 0 := by
      rw [real_inner_comm]
      exact hLp
    have hEq : DeGiorgi.gradLpOfWitness (hz i) =
        DeGiorgi.gradLpOfWitness (hd i) + DeGiorgi.gradLpOfWitness (hh i) :=
      gradLpOfWitness_eq_add_of_sub hΩ (hz i) (hh i) (hd i)
    rw [← norm_gradLpOfWitness_sq_eq_integral (hh i),
      ← norm_gradLpOfWitness_sq_eq_integral (hz i),
      hEq, norm_add_sq_real, hLp']
    nlinarith [sq_nonneg ‖DeGiorgi.gradLpOfWitness (hd i)‖]
  let G (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hz i).weakGrad x j)
  let H (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hh i).weakGrad x j)
  have hG (j : Fin d) : MemLp (G j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hz i).weakGrad_component_memLp j
  have hH (j : Fin d) : MemLp (H j) 2 (volume.restrict Ω) :=
    MemLp.of_eval_piLp fun i => (hh i).weakGrad_component_memLp j
  have hD (x : E) (j : Fin d) : (WithLp.toLp 2 (fun i => (hd i).weakGrad x j) : F) =
      G j x - H j x := by
    ext i
    change (hz i).weakGrad x j + -1 * (hh i).weakGrad x j =
      (hz i).weakGrad x j - (hh i).weakGrad x j
    ring
  have horth : (∫ x in Ω, ∑ j : Fin d, A₀ (H j x) (G j x - H j x)) = 0 := by
    have ho := integral_bilinear_weakGrad_eq_zero_of_harmonic hΩ hh hd hd0 heuler A₀
    simpa only [hD] using ho
  have henergy' : (∑ j : Fin d, ∫ x in Ω, ‖H j x‖ ^ 2) ≤
      ∑ j : Fin d, ∫ x in Ω, ‖G j x‖ ^ 2 := by
    rw [← sum_integral_weakGrad_norm_sq_eq_sum_columns hh,
      ← sum_integral_weakGrad_norm_sq_eq_sum_columns hz]
    exact henergy
  have hc :=
    DifferentialGeometry.Analysis.integral_quadratic_difference_le_of_coefficient_comparison
    A₀ hsym hlam hε hcoerce (fun x => B (z x)) (fun x => B (h x))
    hBz hBh hzclose hhclose G H hG hH horth hmin henergy'
  have hdiff : (∑ i : ι, ∫ x in Ω, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) =
      ∑ j : Fin d, ∫ x in Ω, ‖G j x - H j x‖ ^ 2 := by
    have heq (i : ι) (x : E) : (hd i).weakGrad x = (hz i).weakGrad x - (hh i).weakGrad x := by
      change (hz i).weakGrad x + -1 • (hh i).weakGrad x = _
      simp only [neg_one_smul, sub_eq_add_neg]
    have hs := sum_integral_weakGrad_norm_sq_eq_sum_columns hd
    simp_rw [hD] at hs
    simpa only [heq] using hs
  rw [hdiff, sum_integral_weakGrad_norm_sq_eq_sum_columns hz]
  exact hc

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_weakGrad_sq_le_of_harmonic_comparison_error
    {z h : V → F} {b : V} {r R δ : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 4)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball b R))
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (Metric.ball b R))
    (hEuler : ∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b R) φ →
      (∫ x in Metric.ball b R, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    (herror : (∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
      δ * ∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x‖ ^ 2)
:
    (∑ i : ι, ∫ x in Metric.ball b r, ‖(hz i).weakGrad x‖ ^ 2) ≤
      (256 * (1 + δ) * (r / R) ^ 2 + 2 * δ) *
        ∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x‖ ^ 2 := by
  let Ei (i : ι) (a : ℝ) := ∫ x in Metric.ball b a, ‖(hz i).weakGrad x‖ ^ 2
  let Hi (i : ι) (a : ℝ) := ∫ x in Metric.ball b a, ‖(hh i).weakGrad x‖ ^ 2
  let Di (i : ι) (a : ℝ) := ∫ x in Metric.ball b a, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2
  have hsub : Metric.ball b r ⊆ Metric.ball b R := Metric.ball_subset_ball (by linarith)
  have hzi (i : ι) : IntegrableOn (fun x => ‖(hz i).weakGrad x‖ ^ 2) (Metric.ball b R) :=
    (hz i).weakGrad_memLp.norm.integrable_sq
  have hhi (i : ι) : IntegrableOn (fun x => ‖(hh i).weakGrad x‖ ^ 2) (Metric.ball b R) :=
    (hh i).weakGrad_memLp.norm.integrable_sq
  have hdi (i : ι) : IntegrableOn (fun x => ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2)
      (Metric.ball b R) := ((hz i).weakGrad_memLp.sub (hh i).weakGrad_memLp).norm.integrable_sq
  have hpoint (v w : V) : ‖v‖ ^ 2 ≤ 2 * ‖v - w‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
    have hnorm : ‖v‖ ≤ ‖v - w‖ + ‖w‖ := by simpa only [sub_add_cancel] using norm_add_le (v - w) w
    nlinarith [sq_nonneg (‖v - w‖ - ‖w‖), norm_nonneg v, norm_nonneg (v - w), norm_nonneg w]
  have hsplit (i : ι) : Ei i r ≤ 2 * Di i r + 2 * Hi i r := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hdi i).mono_set hsub |>.const_mul 2) ((hhi i).mono_set hsub |>.const_mul 2)]
    exact integral_mono_ae ((hzi i).mono_set hsub)
      (((hdi i).mono_set hsub |>.const_mul 2).add ((hhi i).mono_set hsub |>.const_mul 2))
      (Eventually.of_forall fun x => hpoint _ _)
  have hreverse (i : ι) : Hi i R ≤ 2 * Di i R + 2 * Ei i R := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hdi i).const_mul 2) ((hzi i).const_mul 2)]
    apply integral_mono_ae (hhi i) (((hdi i).const_mul 2).add ((hzi i).const_mul 2))
    filter_upwards with x
    have hp := hpoint ((hh i).weakGrad x) ((hz i).weakGrad x)
    rwa [norm_sub_rev ((hh i).weakGrad x)] at hp
  have hD (i : ι) : Di i r ≤ Di i R := setIntegral_mono_set (hdi i)
    (Eventually.of_forall fun _ => sq_nonneg _) (Eventually.of_forall hsub)
  have hH (i : ι) : Hi i r ≤ 64 * (r / R) ^ 2 * Hi i R :=
    integral_weakGrad_sq_le_radius_ratio_sq_of_harmonic hR hr hrR (hh i) (hEuler i)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    (hsplit i).trans (add_le_add (mul_le_mul_of_nonneg_left (hD i) (by norm_num))
      (mul_le_mul_of_nonneg_left (hH i) (by norm_num))))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hreverseSum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hreverse i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hreverseSum
  change (∑ i, Di i R) ≤ δ * ∑ i, Ei i R at herror
  have henergy : (∑ i, Hi i R) ≤ 2 * (1 + δ) * ∑ i, Ei i R := by linarith
  have h1 := mul_le_mul_of_nonneg_left herror (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 128 * (r / R) ^ 2)
  change (∑ i, Ei i r) ≤ _
  nlinarith

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_weakGrad_difference_sq_le_of_holder_harmonic_comparison
    {z h : V → F} {b : V} {R α Lz lam : ℝ} (hR : 0 < R) (hα : 0 ≤ α) (hLz : 0 ≤ Lz)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball b R))
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (Metric.ball b R))
    (htrace : ∀ i, DeGiorgi.MemW01p 2 (fun x => h x i - z x i) (Metric.ball b R))
    (hEuler : ∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b R) φ →
      (∫ x in Metric.ball b R, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0)
    (B : F → F →L[ℝ] F →L[ℝ] ℝ) {K : Set F} (hK : IsCompact K)
    (hzK : ∀ᵐ x ∂volume.restrict (Metric.ball b R), z x ∈ K)
    (hhK : ∀ᵐ x ∂volume.restrict (Metric.ball b R), h x ∈ K) (hzb : z b ∈ K)
    {L : ℝ≥0} (hBLip : LipschitzOnWith L B K)
    (hsym : ∀ v w, B (z b) v w = B (z b) w v) (hlam : 0 < lam)
    (hcoerce : ∀ v, lam * ‖v‖ ^ 2 ≤ B (z b) v v)
    (hzHolder : ∀ x ∈ Metric.ball b R, ‖z x - z b‖ ≤ Lz * ‖x - b‖ ^ α)
    (hmin : (∑ j : Fin 2, ∫ x in Metric.ball b R, B (z x)
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hz i).weakGrad x j))) ≤
      ∑ j : Fin 2, ∫ x in Metric.ball b R, B (h x)
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))
        (WithLp.toLp 2 (fun i => (hh i).weakGrad x j))) :
    (∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤
      (2 * (L : ℝ) * (Fintype.card ι + 1) * Lz / lam) * R ^ α *
        ∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x‖ ^ 2 := by
  have hzBound : ∀ᵐ x ∂volume.restrict (Metric.ball b R), ‖z x - z b‖ ≤ Lz * R ^ α := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    apply (hzHolder x hx).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (by simpa only [Metric.mem_ball, dist_eq_norm] using (Metric.mem_ball.mp hx).le) hα) hLz
  have hhBound := ae_norm_sub_le_of_weakly_harmonic_of_memW01p_sub
    (by norm_num : 2 ≤ 2) Metric.isOpen_ball Metric.isBounded_ball hz hh htrace hEuler (z b) hzBound
  let ε := (L : ℝ) * (Fintype.card ι + 1) * Lz * R ^ α
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hzClose : ∀ᵐ x ∂volume.restrict (Metric.ball b R), ‖B (z x) - B (z b)‖ ≤ ε := by
    filter_upwards [hzK, hzBound] with x hxK hxB
    have hh := (hBLip.norm_sub_le hxK hzb).trans (mul_le_mul_of_nonneg_left hxB L.coe_nonneg)
    have he : (L : ℝ) * (Lz * R ^ α) ≤ ε := by
      dsimp only [ε]
      have hN := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
      have ht : 0 ≤ (L : ℝ) * Lz * R ^ α := by positivity
      nlinarith
    exact hh.trans he
  have hhClose : ∀ᵐ x ∂volume.restrict (Metric.ball b R), ‖B (h x) - B (z b)‖ ≤ ε := by
    filter_upwards [hhK, hhBound] with x hxK hxB
    have hh := (hBLip.norm_sub_le hxK hzb).trans (mul_le_mul_of_nonneg_left hxB L.coe_nonneg)
    have he : (L : ℝ) * (Fintype.card ι * (Lz * R ^ α)) ≤ ε := by
      dsimp only [ε]
      have ht : 0 ≤ (L : ℝ) * Lz * R ^ α := by positivity
      nlinarith
    exact hh.trans he
  classical
  have hBm : Measurable (K.piecewise B 0) :=
    hBLip.continuousOn.measurable_piecewise continuous_zero.continuousOn hK.measurableSet
  have hm (f : V → F) (hf : MemLp f 2 (volume.restrict (Metric.ball b R)))
      (hfK : ∀ᵐ x ∂volume.restrict (Metric.ball b R), f x ∈ K) :
      AEStronglyMeasurable (fun x => B (f x)) (volume.restrict (Metric.ball b R)) :=
    (hBm.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable.congr
      (hfK.mono fun x hx => Set.piecewise_eq_of_mem K B 0 hx)
  have hBz := hm z (MemLp.of_eval_piLp fun i => (hz i).memLp) hzK
  have hBh := hm h (MemLp.of_eval_piLp fun i => (hh i).memLp) hhK
  have herr := integral_weakGrad_difference_sq_le_of_harmonic_comparison Metric.isOpen_ball hz hh
    htrace hEuler (B (z b)) hsym hlam hε hcoerce B
    (fun v w => (hBz.apply_continuousLinearMap v).apply_continuousLinearMap w)
    (fun v w => (hBh.apply_continuousLinearMap v).apply_continuousLinearMap w) hzClose hhClose hmin
  have heq : 2 * ε / lam = (2 * (L : ℝ) * (Fintype.card ι + 1) * Lz / lam) * R ^ α := by
    dsimp only [ε]
    ring
  rw [heq] at herr
  exact herr

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {ι : Type*} [Fintype ι]
local notation "V" => EuclideanSpace ℝ (Fin 2)
local notation "F" => EuclideanSpace ℝ ι

theorem integral_weakGrad_sub_average_sq_le_of_harmonic_comparison
    {z h : V → F} {b : V} {r R : ℝ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R / 8)
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) (Metric.ball b R))
    (hh : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => h x i) (Metric.ball b R))
    (hEuler : ∀ i (φ : V → ℝ), DeGiorgi.IsSmoothTestOn (Metric.ball b R) φ →
      (∫ x in Metric.ball b R, inner ℝ ((hh i).weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    (∑ i : ι, ∫ x in Metric.ball b r,
      ‖(hz i).weakGrad x - ⨍ y in Metric.ball b r, (hz i).weakGrad y‖ ^ 2) ≤
      16384 * (r / R) ^ 4 *
        (∑ i : ι, ∫ x in Metric.ball b R,
          ‖(hz i).weakGrad x - ⨍ y in Metric.ball b R, (hz i).weakGrad y‖ ^ 2) +
      (2 + 16384 * (r / R) ^ 4) *
        ∑ i : ι, ∫ x in Metric.ball b R, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball b R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (Metric.ball b r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hsub : Metric.ball b r ⊆ Metric.ball b R := Metric.ball_subset_ball (by linarith)
  let c := fun i => ⨍ y in Metric.ball b R, (hz i).weakGrad y
  let Z := fun i => ∫ x in Metric.ball b R, ‖(hz i).weakGrad x - c i‖ ^ 2
  let D := fun i => ∫ x in Metric.ball b R, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2
  have hcomponent (i : ι) :
      (∫ x in Metric.ball b r,
        ‖(hz i).weakGrad x - ⨍ y in Metric.ball b r, (hz i).weakGrad y‖ ^ 2) ≤
        16384 * (r / R) ^ 4 * Z i + (2 + 16384 * (r / R) ^ 4) * D i := by
    obtain ⟨a, ha⟩ := exists_integral_weakGrad_sub_sq_le_radius_ratio_pow_four_of_harmonic
      hR hr hrR (hh i) (c i) (hEuler i)
    have hzi := (hz i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hsub)
    have hhi := (hh i).weakGrad_memLp.mono_measure (Measure.restrict_mono_set volume hsub)
    have hmin :=
      DifferentialGeometry.Analysis.integral_norm_sub_average_sq_le_integral_norm_sub_sq hzi a
    have hsplit :=
      DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add hzi hhi a
    have hreverse := DifferentialGeometry.Analysis.integral_norm_sub_const_sq_le_two_difference_add
      (hh i).weakGrad_memLp (hz i).weakGrad_memLp (c i)
    have hdiff : (∫ x in Metric.ball b r, ‖(hz i).weakGrad x - (hh i).weakGrad x‖ ^ 2) ≤ D i :=
      setIntegral_mono_set ((hz i).weakGrad_memLp.sub (hh i).weakGrad_memLp).norm.integrable_sq
        (Eventually.of_forall fun x => sq_nonneg _) (Eventually.of_forall hsub)
    have hrevereq :
        (∫ x in Metric.ball b R, ‖(hh i).weakGrad x - (hz i).weakGrad x‖ ^ 2) = D i := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only [D]; rw [norm_sub_rev]
    rw [hrevereq] at hreverse
    have hmult := mul_le_mul_of_nonneg_left hreverse (by positivity : 0 ≤ 4096 * (r / R) ^ 4)
    have hresult := hmin.trans hsplit
    nlinarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcomponent i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
