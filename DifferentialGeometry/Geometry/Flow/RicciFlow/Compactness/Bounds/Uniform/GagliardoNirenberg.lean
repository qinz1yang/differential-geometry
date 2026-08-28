import DifferentialGeometry.Analysis.Sobolev.GagliardoNirenbergLpFiberNorm

import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.JetProductIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.CovariantSumCross
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.MorreySecondDerivative

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Sobolev.Tensor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

noncomputable def metricVolRadius (g : SmoothRiemannianMetric I M) : ℝ :=
  Real.sqrt ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal

noncomputable def volCompareC (Λ : ℝ) : ℝ :=
  Real.sqrt (Λ ^ Module.finrank ℝ E)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volumeReal_cross
    (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal ∧
      ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal := by
  let μBase := riemannianVolumeMeasure (I := I) (M := M) gBase
  let μg := riemannianVolumeMeasure (I := I) (M := M) g
  let L : ℝ := volCompareC (E := E) Λ
  have : IsFiniteMeasure μBase :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) gBase
  have : IsFiniteMeasure μg :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hmeas := volumeMeasure_cross_le (I := I) (M := M) gBase g hEq
  constructor
  · have hle : μg Set.univ ≤ ENNReal.ofReal L * μBase Set.univ := by
      have h := hmeas.1 Set.univ
      simpa only [μg, μBase, L, volCompareC, Measure.smul_apply, smul_eq_mul] using h
    have htop : ENNReal.ofReal L * μBase Set.univ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μBase Set.univ)
    have hreal := ENNReal.toReal_mono htop hle
    simpa only [μg, μBase, L, volCompareC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hreal
  · have hle : μBase Set.univ ≤ ENNReal.ofReal L * μg Set.univ := by
      have h := hmeas.2 Set.univ
      simpa only [μg, μBase, L, volCompareC, Measure.smul_apply, smul_eq_mul] using h
    have htop : ENNReal.ofReal L * μg Set.univ ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μg Set.univ)
    have hreal := ENNReal.toReal_mono htop hle
    simpa only [μg, μBase, L, volCompareC, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using hreal

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volRadius_cross
    (gBase g : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    metricVolRadius (I := I) (M := M) g ≤
        Real.sqrt (volCompareC (E := E) Λ) * metricVolRadius (I := I) (M := M) gBase ∧
      metricVolRadius (I := I) (M := M) gBase ≤
        Real.sqrt (volCompareC (E := E) Λ) * metricVolRadius (I := I) (M := M) g := by
  have hvol := volumeReal_cross (I := I) (M := M) gBase g hEq
  have hL : 0 ≤ volCompareC (E := E) Λ := by
    exact Real.sqrt_nonneg _
  constructor
  · refine le_trans (Real.sqrt_le_sqrt hvol.1) ?_
    rw [Real.sqrt_mul hL]
    rfl
  · refine le_trans (Real.sqrt_le_sqrt hvol.2) ?_
    rw [Real.sqrt_mul hL]
    rfl

noncomputable def volClassC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) : ℝ :=
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  max (S * VBase) (if VBase = 0 then 0 else S / VBase)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem volClassC_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) :
    0 ≤ volClassC (E := E) (I := I) (M := M) gBase Λ := by
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hVBase : 0 ≤ VBase := Real.sqrt_nonneg _
  unfold volClassC
  dsimp only
  exact le_trans (mul_nonneg hS hVBase) (le_max_left _ _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem volClassC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) :
    metricVolRadius (I := I) (M := M) g ≤
        volClassC (E := E) (I := I) (M := M) gBase Λ ∧
      1 / metricVolRadius (I := I) (M := M) g ≤
        volClassC (E := E) (I := I) (M := M) gBase Λ := by
  let S := Real.sqrt (volCompareC (E := E) Λ)
  let VBase := metricVolRadius (I := I) (M := M) gBase
  let Vg := metricVolRadius (I := I) (M := M) g
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  have hVBase : 0 ≤ VBase := Real.sqrt_nonneg _
  have hVg : 0 ≤ Vg := Real.sqrt_nonneg _
  have hrad := volRadius_cross (I := I) (M := M) gBase g hEq
  have hfwd : Vg ≤ S * VBase := hrad.1
  have hrev : VBase ≤ S * Vg := hrad.2
  change Vg ≤ max (S * VBase) (if VBase = 0 then 0 else S / VBase) ∧
    1 / Vg ≤ max (S * VBase) (if VBase = 0 then 0 else S / VBase)
  constructor
  · exact le_trans hfwd (le_max_left _ _)
  · by_cases hVBase0 : VBase = 0
    · have hVg0 : Vg = 0 := by
        rw [hVBase0, mul_zero] at hfwd
        exact le_antisymm hfwd hVg
      simp [hVg0, hVBase0]
    · have hVBasePos : 0 < VBase :=
        lt_of_le_of_ne hVBase (fun h => hVBase0 h.symm)
      have hVgPos : 0 < Vg := by
        have hVgNe : Vg ≠ 0 := by
          intro hVg0
          rw [hVg0, mul_zero] at hrev
          exact hVBase0 (le_antisymm hrev hVBase)
        exact lt_of_le_of_ne hVg (fun h => hVgNe h.symm)
      have hinv : 1 / Vg ≤ S / VBase := by
        rw [div_le_div_iff₀ hVgPos hVBasePos]
        simpa only [one_mul] using hrev
      rw [if_neg hVBase0]
      exact le_trans hinv (le_max_right _ _)

def gnClassLogC (n k : ℕ) (B : ℝ) : ℝ :=
  max (max (gnStepConst n k) 1) (gnStepConst n k * B + gnStepConst n k)

noncomputable def gnClassC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) : ℝ :=
  let B := volClassC (E := E) (I := I) (M := M) gBase Λ
  gnClassLogC (Module.finrank ℝ E) k B ^ (2 * k ^ 2) * (max 1 B) ^ 2

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
theorem gnClassC_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) :
    0 ≤ gnClassC (E := E) (I := I) (M := M) gBase Λ k := by
  unfold gnClassC
  exact mul_nonneg (pow_nonneg (le_trans zero_le_one
    (le_trans (le_max_right _ _) (le_max_left _ _))) _) (sq_nonneg _)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
theorem gnClassC_spec
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ}
    (g : SmoothRiemannianMetric I M)
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ) (k : ℕ) :
    gnRsConst (Module.finrank ℝ E) k (metricVolRadius (I := I) (M := M) g) ≤
      gnClassC (E := E) (I := I) (M := M) gBase Λ k := by
  let n := Module.finrank ℝ E
  let V := metricVolRadius (I := I) (M := M) g
  let B := volClassC (E := E) (I := I) (M := M) gBase Λ
  have hvol := volClassC_spec (I := I) (M := M) gBase g hEq
  have hV : V ≤ B := hvol.1
  have hInv : 1 / V ≤ B := hvol.2
  have hStep : 0 ≤ gnStepConst n k := by
    unfold gnStepConst
    exact le_trans zero_le_one (le_max_right _ _)
  have hLog : gnLogConst n k V ≤ gnClassLogC n k B := by
    unfold gnLogConst gnClassLogC
    apply max_le_max (le_refl _)
    simpa only [add_comm] using
      (add_le_add_right (mul_le_mul_of_nonneg_left hInv hStep) (gnStepConst n k))
  have hLog0 : 0 ≤ gnLogConst n k V := by
    unfold gnLogConst
    exact le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hClassLog0 : 0 ≤ gnClassLogC n k B := by
    unfold gnClassLogC
    exact le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hMax : max 1 V ≤ max 1 B := max_le_max (le_refl _) hV
  have hLogPow : gnLogConst n k V ^ (2 * k ^ 2) ≤
      gnClassLogC n k B ^ (2 * k ^ 2) :=
    pow_le_pow_left₀ hLog0 hLog _
  have hMaxPow : (max 1 V) ^ 2 ≤ (max 1 B) ^ 2 :=
    pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hMax _
  have hmul := mul_le_mul hLogPow hMaxPow (sq_nonneg _) (pow_nonneg hClassLog0 _)
  simpa only [n, V, B, gnRsConst, gnClassC] using hmul

theorem gn_rs_uniform
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ gnClassC (E := E) (I := I) (M := M) gBase Λ k ∧
      ∀ (g : SmoothRiemannianMetric I M),
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        ∀ (r s : ℕ) (u : Integral.L2.SmoothCcTensor g r s) (Λ₀ : ℝ), 0 ≤ Λ₀ →
          (∀ x : M,
            riemannianFiberNormSq (I := I) (M := M) g r s x (u.toSection x) ≤ Λ₀ ^ 2) →
          ∀ j : ℕ, 0 < j → j < k →
            (∫ x, (riemannianFiberNormSq (I := I) (M := M) g r (s + j) x
                    ((iteratedCovGrad (I := I) g r s j u).toSection x)) ^ ((k : ℝ) / j)
                ∂(riemannianVolumeMeasure I M g)) ^ ((j : ℝ) / k) ≤
              gnClassC (E := E) (I := I) (M := M) gBase Λ k *
                Λ₀ ^ (2 * (1 - (j : ℝ) / k)) *
                (Integral.L2.tensorL2Norm (I := I) g r (s + k)
                  (iteratedCovGrad (I := I) g r s k u).toFun) ^ (2 * (j : ℝ) / k) := by
  refine ⟨gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ k, ?_⟩
  intro g hEq r s u Λ₀ hΛ₀ hsup j hj0 hjk
  have hgn := (gn_rs_bound (I := I) (M := M) g r s k hk).2 u Λ₀ hΛ₀ hsup j hj0 hjk
  have hcoef := gnClassC_spec (I := I) (M := M) gBase g hEq k
  refine le_trans hgn ?_
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hΛ₀ _)
  · exact Real.rpow_nonneg
      (Integral.L2.tensorL2Norm_nonneg (I := I) (M := M) g r (s + k) _) _

noncomputable def rankTwoGridC
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (R : ℝ) : ℝ :=
  (∑ n ∈ Finset.range (k + 1),
      ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) *
    ((k : ℝ) *
      (max
        (morreyTwoC (I := I) (M := M) gBase Λ * R)
        (max (gnClassC (E := E) (I := I) (M := M) gBase Λ k) 1)) ^
          (7 * k))

omit [BoundarylessManifold I M] in
theorem rank_two_grid_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (k : ℕ) (R : ℝ) :
    0 ≤ rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R := by
  unfold rankTwoGridC
  exact mul_nonneg
    (Finset.sum_nonneg (fun n _ => Nat.cast_nonneg _))
    (mul_nonneg (Nat.cast_nonneg k)
      (pow_nonneg (le_trans zero_le_one
        (le_trans (le_max_right _ 1) (le_max_right _ _))) _))

theorem rank_two_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R A : ℝ),
        0 ≤ R →
        0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 k P‖ ≤ A →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range (k + 1),
              ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * A ^ 2 := by
  classical
  intro g hEq hjet1 hjet2 P R A hR hA hP2 htop
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  have hdim : Module.finrank ℝ E / 2 + 2 = 3 := by
    rw [hDim]
  obtain ⟨hCpt, hpt⟩ := morreyTwoC_spec (I := I) (M := M) gBase hΛ hdim
  have hCgn := gnClassC_nonneg (E := E) (I := I) (M := M) gBase Λ k
  let Lam : ℝ := morreyTwoC (I := I) (M := M) gBase Λ * R
  have hLam : 0 ≤ Lam := mul_nonneg hCpt hR
  have hrange : Finset.range (Module.finrank ℝ E / 2 + 2) = Finset.range 3 := by
    rw [hDim]
  have hLamSup : ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 2 x (P.toSection x) ≤
        Lam ^ 2 := by
    intro x
    have hx := hpt g hEq hjet1 hjet2 P x
    rw [hrange] at hx
    calc
      _ ≤ morreyTwoC (I := I) (M := M) gBase Λ ^ 2 *
          (∑ j ∈ Finset.range 3,
            ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) := hx
      _ ≤ morreyTwoC (I := I) (M := M) gBase Λ ^ 2 * R ^ 2 :=
        mul_le_mul_of_nonneg_left hP2 (sq_nonneg _)
      _ = Lam ^ 2 := by
        exact (mul_pow _ _ 2).symm
  have hGNP : ∀ j : ℕ, 0 < j → j < k →
      (∫ x, (riemannianFiberNormSq (I := I) (M := M) g 0 (2 + j) x
              ((iteratedCovGrad (I := I) g 0 2 j P).toSection x)) ^
            ((k : ℝ) / (j : ℝ))
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^
            ((j : ℝ) / (k : ℝ)) ≤
        gnClassC (E := E) (I := I) (M := M) gBase Λ k *
          Lam ^ (2 * (1 - (j : ℝ) / (k : ℝ))) *
          A ^ (2 * (j : ℝ) / (k : ℝ)) := by
    intro j hj0 hjk
    have hb := (gn_rs_uniform (E := E) (I := I) (M := M) gBase Λ k hk).2
      g hEq 0 2 P Lam hLam hLamSup j hj0 hjk
    have hnorm : Integral.L2.tensorL2Norm (I := I) g 0 (2 + k)
        (iteratedCovGrad (I := I) g 0 2 k P).toFun =
        ‖iteratedCovGrad (I := I) g 0 2 k P‖ :=
      (Integral.L2.SmoothCcTensor.norm_def
        (iteratedCovGrad (I := I) g 0 2 k P)).symm
    rw [hnorm] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow
        (norm_nonneg (iteratedCovGrad (I := I) g 0 2 k P))
        htop (by positivity))
      (mul_nonneg hCgn (Real.rpow_nonneg hLam _)))
  let G : ℝ :=
    (k : ℝ) *
      (max Lam (max (gnClassC (E := E) (I := I) (M := M) gBase Λ k) 1)) ^
        (7 * k) * A ^ 2
  have hterm : ∀ n ∈ Finset.range (k + 1),
      ∀ e ∈ Finset.Nat.antidiagonalTuple n k,
        MeasureTheory.Integrable
            (fun x => ∏ m : Fin n,
              riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∏ m : Fin n,
                riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                  ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤ G := by
    intro n hn e he
    have hn_le : n ≤ k := by
      have := Finset.mem_range.mp hn
      omega
    have hsum : ∑ m, e m = k := Finset.Nat.mem_antidiagonalTuple.mp he
    have hres := Integral.Connection.grid_prod_int_le (I := I) (M := M) g P
      hA k hk hLam hLamSup htop hCgn hGNP n hn_le e hsum
    simpa only [G] using hres
  have hint : MeasureTheory.Integrable
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
    apply MeasureTheory.integrable_finsetSum
    intro n hn
    apply MeasureTheory.integrable_finsetSum
    intro e he
    exact (hterm n hn e he).1
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_finsetSum _
    (fun n hn => MeasureTheory.integrable_finsetSum _
      (fun e he => (hterm n hn e he).1))]
  have hinner : ∀ n ∈ Finset.range (k + 1),
      (∫ x, ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) =
      ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
        ∫ x, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    intro n hn
    exact MeasureTheory.integral_finsetSum _ (fun e he => (hterm n hn e he).1)
  rw [Finset.sum_congr rfl hinner]
  calc
    ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
          ∫ x, ∏ m : Fin n,
            riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
              ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)
        ≤ ∑ n ∈ Finset.range (k + 1),
            ∑ _e ∈ Finset.Nat.antidiagonalTuple n k, G := by
          apply Finset.sum_le_sum
          intro n hn
          apply Finset.sum_le_sum
          intro e he
          exact (hterm n hn e he).2
    _ = (∑ n ∈ Finset.range (k + 1),
          ((Finset.Nat.antidiagonalTuple n k).card : ℝ)) * G := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro n _
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * A ^ 2 := by
        simp only [rankTwoGridC, G, Lam, mul_assoc]

noncomputable def h2GridC
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then
    volCompareC (E := E) Λ *
      ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
  else
    rankTwoGridC (E := E) (I := I) (M := M) gBase Λ k R * R ^ 2

omit [BoundarylessManifold I M] in
theorem h2_grid_nonneg
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) (k : ℕ) :
    0 ≤ h2GridC (E := E) (I := I) (M := M) gBase Λ R k := by
  unfold h2GridC
  split_ifs
  · exact mul_nonneg (Real.sqrt_nonneg _) ENNReal.toReal_nonneg
  · exact mul_nonneg
      (rank_two_grid_nonneg (E := E) (I := I) (M := M) gBase Λ k R)
      (sq_nonneg R)

theorem h2_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R : ℝ),
        0 ≤ R →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ∀ k : ℕ, k ≤ 2 →
          MeasureTheory.Integrable
              (fun x => ∑ n ∈ Finset.range (k + 1),
                ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
              (riemannianVolumeMeasure (I := I) (M := M) g) ∧
            (∫ x, ∑ n ∈ Finset.range (k + 1),
                  ∑ e ∈ Finset.Nat.antidiagonalTuple n k,
                    ∏ m : Fin n,
                      riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                        ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
              h2GridC (E := E) (I := I) (M := M) gBase Λ R k := by
  classical
  intro g hEq hjet1 hjet2 P R hR hP2 k hk2
  have : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace g
  by_cases hk0 : k = 0
  · subst k
    have hgrid : (fun x => ∑ n ∈ Finset.range (0 + 1),
        ∑ e ∈ Finset.Nat.antidiagonalTuple n 0, ∏ m : Fin n,
          riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
            ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)) =
        (fun _ : M => (1 : ℝ)) := by
      funext x
      simp only [Nat.zero_add, Finset.sum_range_one,
        Finset.Nat.antidiagonalTuple_zero_zero, Finset.sum_singleton,
        Finset.univ_eq_empty, Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · rw [hgrid]
      exact MeasureTheory.integrable_const 1
    · rw [hgrid, MeasureTheory.integral_const, smul_eq_mul, mul_one,
        MeasureTheory.measureReal_def]
      change ((riemannianVolumeMeasure (I := I) (M := M) g) Set.univ).toReal ≤
        volCompareC (E := E) Λ *
          ((riemannianVolumeMeasure (I := I) (M := M) gBase) Set.univ).toReal
      exact (volumeReal_cross (I := I) (M := M) gBase g hEq).1
  · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hmem : k ∈ Finset.range 3 := Finset.mem_range.mpr (by omega)
    have hsingle : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ^ 2 ≤ R ^ 2 :=
      (Finset.single_le_sum
        (f := fun j : ℕ => ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2)
        (fun j _ => sq_nonneg _) hmem).trans hP2
    have htop : ‖iteratedCovGrad (I := I) g 0 2 k P‖ ≤ R := by
      nlinarith [norm_nonneg (iteratedCovGrad (I := I) g 0 2 k P)]
    have hgrid := rank_two_grid_uniform (E := E) (I := I) (M := M)
      hDim gBase hΛ k hk1 g hEq hjet1 hjet2 P R R hR hR hP2 htop
    simpa only [h2GridC, if_neg hk0] using hgrid

noncomputable def h3TopGridC
    (gBase : SmoothRiemannianMetric I M) (Λ R : ℝ) : ℝ :=
  rankTwoGridC (E := E) (I := I) (M := M) gBase Λ 3 R

theorem h3_top_grid_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 0 ≤ Λ) :
    ∀ (g : SmoothRiemannianMetric I M),
      MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g gBase Λ →
      MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g gBase Λ →
      ∀ (P : Integral.L2.SmoothCcTensor g 0 2) (R A : ℝ),
        0 ≤ R →
        0 ≤ A →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j P‖ ^ 2) ≤ R ^ 2 →
        ‖iteratedCovGrad (I := I) g 0 2 3 P‖ ≤ A →
        MeasureTheory.Integrable
            (fun x => ∑ n ∈ Finset.range 4,
              ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                ∏ m : Fin n,
                  riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                    ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x))
            (riemannianVolumeMeasure (I := I) (M := M) g) ∧
          (∫ x, ∑ n ∈ Finset.range 4,
                ∑ e ∈ Finset.Nat.antidiagonalTuple n 3,
                  ∏ m : Fin n,
                    riemannianFiberNormSq (I := I) (M := M) g 0 (2 + e m) x
                      ((iteratedCovGrad (I := I) g 0 2 (e m) P).toSection x)
              ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
            h3TopGridC (E := E) (I := I) (M := M) gBase Λ R * A ^ 2 := by
  intro g hEq hjet1 hjet2 P R A hR hA hP2 htop
  simpa only [h3TopGridC, Nat.reduceAdd] using
    (rank_two_grid_uniform (E := E) (I := I) (M := M)
      hDim gBase hΛ 3 (by omega) g hEq hjet1 hjet2 P R A hR hA hP2 htop)

end RicciFlow
end PDE
end DifferentialGeometry
