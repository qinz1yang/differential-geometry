import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Maximal.Flow
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.VolumeDistortion

/-!
# Diameter and volume of a curvature-controlled compact flow at positive time

For a Ricci flow `P : FlowTo g₀ τ` on a closed manifold with `T < τ` and `|Rm| ≤ B` on `[0, T]`
(the part-B output shape of the merged LFR50 design), the metrics on `[0, T]` are uniformly
equivalent (the Ricci tensor is bounded by `n² B g`, `n = dim M`, and the metric evolves by
`∂ₜ g = -2 Ric`). Hence an initial diameter bound `d` and an initial total-volume bound `v` give,
at every `t ∈ [0, T]`,

* `riemannianEDistOf_le_of_flowTo`: diameter `≤ e^{n² B t} (max d 0 + 1)`;
* `ofReal_le_volume_univ_of_flowTo`: total volume `≥ v e^{-n³ B t}`;

with constants depending only on `n`, `B`, `t`, `d`, `v`. The suppliers are the existing flow
comparisons `inner_le_exp_mul_inner_of_rmNormSq_le` (`Perelman/Noncollapsing/ForwardTransfer.lean`,
built on the Ricci quadratic-form bound and the PDE of the solution) and
`riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le` (`…/VolumeDistortion.lean`), at the scale
`ρ = 1/√B`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [BoundarylessManifold I M]

section Slab

variable {g₀ : SmoothRiemannianMetric I M} {τ : ℝ} (P : FlowTo (I := I) (M := M) g₀ τ)
  {T B : ℝ}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private theorem flowTo_slab (hTτ : T < τ) :
    Icc 0 T ⊆ (RealTimeInterval.closedOpen 0 τ P.time_pos).carrier :=
  fun _ ht => ⟨ht.1, lt_of_le_of_lt ht.2 hTτ⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
private theorem flowTo_regular (hTτ : T < τ) :
    Ioo 0 T ⊆ (RealTimeInterval.closedOpen 0 τ P.time_pos).regular :=
  fun _ ht => ⟨ht.1, lt_trans ht.2 hTτ⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] [CompactSpace M] in
/-- `|Rm| ≤ B` in the scale-`ρ = 1/√B` form `ρ⁴ |Rm|² ≤ 1` of the Perelman flow comparisons. -/
private theorem flowTo_rmNormSq_scaled (hB : 0 < B)
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (P.S.base.metric t) x 4
        (metricRm04 (P.S.base.metric t) x)) ≤ B) :
    ∀ u ∈ Icc 0 T, ∀ y : M,
      (Real.sqrt B)⁻¹ ^ 4 * Perelman.FlowMetricBall.rmNormSq P.S u y ≤ 1 := by
  intro u hu y
  have h := (Real.sqrt_le_iff.mp (hcurv u hu y)).2
  have hB2 : (0 : ℝ) < B ^ 2 := by positivity
  have hpow : (Real.sqrt B)⁻¹ ^ 4 = (B ^ 2)⁻¹ := by
    rw [inv_pow, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt hB.le]
  rw [hpow, inv_mul_le_iff₀ hB2, mul_one]
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] in
/-- Uniform equivalence of the metrics on `[0, T]`:
`g(s₁) ≤ e^{2 n² B |s₁ - s₂|} g(s₂)`. -/
theorem inner_le_exp_mul_inner_of_flowTo (hTτ : T < τ) (hB : 0 < B)
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (P.S.base.metric t) x 4
        (metricRm04 (P.S.base.metric t) x)) ≤ B)
    {s₁ s₂ : ℝ} (hs₁ : s₁ ∈ Icc 0 T) (hs₂ : s₂ ∈ Icc 0 T) (y : M) (v : TangentSpace I y) :
    (P.S.base.metric s₁).inner y v v ≤
      Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * B * |s₁ - s₂|)) *
        (P.S.base.metric s₂).inner y v v := by
  have hρ : 0 < (Real.sqrt B)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hB)
  have h := Perelman.inner_le_exp_mul_inner_of_rmNormSq_le (I := I) P.isSolution hρ
    (flowTo_slab P hTτ) (flowTo_regular P hTτ)
    (fun u hu => flowTo_rmNormSq_scaled P hB hcurv u hu y) hs₁ hs₂ v
  have hρ2 : (Module.finrank ℝ E : ℝ) ^ 2 / (Real.sqrt B)⁻¹ ^ 2 =
      (Module.finrank ℝ E : ℝ) ^ 2 * B := by
    rw [inv_pow, Real.sq_sqrt hB.le, div_inv_eq_mul]
  rw [hρ2] at h
  exact h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] in
/-- **Diameter at positive time.** If `g₀` has diameter `≤ d`, then `g(t)`, `t ∈ [0, T]`, has
diameter `≤ e^{n² B t} (max d 0 + 1)`. -/
theorem riemannianEDistOf_le_of_flowTo (hTτ : T < τ) (hB : 0 < B)
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (P.S.base.metric t) x 4
        (metricRm04 (P.S.base.metric t) x)) ≤ B)
    {d : ℝ} (hdiam : ∀ x y : M, riemannianEDistOf g₀ x y ≤ ENNReal.ofReal d)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x y : M) :
    riemannianEDistOf (P.S.base.metric t) x y ≤
      ENNReal.ofReal (Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * B * t) * (max d 0 + 1)) := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hstart : P.S.base.metric 0 = g₀ := P.start
  let Q : ℝ := Real.exp (2 * ((Module.finrank ℝ E : ℝ) ^ 2 * B * |t - 0|))
  have hQ : 0 < Q := Real.exp_pos _
  have hsub := riemannianBallOf_subset_of_inner_le_mul (P.S.base.metric 0)
    (P.S.base.metric t) x (r := max d 0 + 1) hQ
    (fun q _ w => inner_le_exp_mul_inner_of_flowTo P hTτ hB hcurv ht h0 q w)
  have hy : y ∈ riemannianBallOf (P.S.base.metric 0) x (max d 0 + 1) := by
    change riemannianEDistOf (P.S.base.metric 0) x y < ENNReal.ofReal (max d 0 + 1)
    rw [hstart]
    refine (hdiam x y).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
    linarith [le_max_left d 0]
  have hQroot : Real.sqrt Q = Real.exp ((Module.finrank ℝ E : ℝ) ^ 2 * B * t) := by
    dsimp only [Q]
    rw [sub_zero, abs_of_nonneg ht.1, show 2 * ((Module.finrank ℝ E : ℝ) ^ 2 * B * t) =
      (Module.finrank ℝ E : ℝ) ^ 2 * B * t + (Module.finrank ℝ E : ℝ) ^ 2 * B * t by ring,
      Real.exp_add, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hmem := hsub hy
  change riemannianEDistOf (P.S.base.metric t) x y <
    ENNReal.ofReal (Real.sqrt Q * (max d 0 + 1)) at hmem
  rw [hQroot] at hmem
  exact hmem.le

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
/-- **Volume at positive time.** If `g₀` has total volume `≥ v`, then `g(t)`, `t ∈ [0, T]`, has
total volume `≥ v e^{-n³ B t}`. -/
theorem ofReal_le_volume_univ_of_flowTo (hTτ : T < τ) (hB : 0 < B)
    (hcurv : ∀ t ∈ Icc 0 T, ∀ x : M,
      Real.sqrt (Tensor0SBundle.normSq0S (P.S.base.metric t) x 4
        (metricRm04 (P.S.base.metric t) x)) ≤ B)
    {v : ℝ} (hvol : ENNReal.ofReal v ≤ riemannianVolumeMeasure I M g₀ Set.univ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal (v * Real.exp (-((Module.finrank ℝ E : ℝ) ^ 3 * B * t))) ≤
      riemannianVolumeMeasure I M (P.S.base.metric t) Set.univ := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hρ : 0 < (Real.sqrt B)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hB)
  have hdist := Perelman.riemannianVolumeMeasure_le_exp_mul_of_rmNormSq_le (I := I) P.isSolution
    hρ (flowTo_slab P hTτ) (flowTo_regular P hTτ) MeasurableSet.univ
    (fun u hu y _ => flowTo_rmNormSq_scaled P hB hcurv u hu y) (subset_refl Set.univ) h0 ht
  have hρ2 : (Module.finrank ℝ E : ℝ) ^ 3 / (Real.sqrt B)⁻¹ ^ 2 * |0 - t| =
      (Module.finrank ℝ E : ℝ) ^ 3 * B * t := by
    rw [inv_pow, Real.sq_sqrt hB.le, div_inv_eq_mul, zero_sub, abs_neg, abs_of_nonneg ht.1]
  rw [hρ2] at hdist
  have hstart : P.S.base.metric 0 = g₀ := P.start
  rw [hstart] at hdist
  set c : ℝ := (Module.finrank ℝ E : ℝ) ^ 3 * B * t
  have hec : 0 < Real.exp c := Real.exp_pos c
  rw [← ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hec).ne' ENNReal.ofReal_ne_top]
  refine le_trans ?_ (hvol.trans hdist)
  rcases le_or_gt v 0 with hv | hv
  · have hz : v * Real.exp (-c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv (Real.exp_pos _).le
    rw [ENNReal.ofReal_of_nonpos hz, mul_zero]
    exact bot_le
  · rw [← ENNReal.ofReal_mul hec.le]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Slab

end DifferentialGeometry.PDE.RicciFlow
