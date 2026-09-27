import DifferentialGeometry.Analysis.Integration.Lp.QuadraticConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import DifferentialGeometry.Topology.Order.LiminfSum

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

private theorem eventually_mem_closedBall_iff_of_tendsto_radius
    {P I : Type*} [PseudoMetricSpace P] {l : Filter I} {c x : P}
    {r : ℝ} {rn : I → ℝ} (hr : Tendsto rn l (𝓝 r))
    (hx : x ∉ Metric.sphere c r) :
    ∀ᶠ n in l, (x ∈ Metric.closedBall c (rn n) ↔ x ∈ Metric.closedBall c r) := by
  have hne : dist x c ≠ r := by simpa only [Metric.mem_sphere] using hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · filter_upwards [(tendsto_order.1 hr).1 (dist x c) hlt] with n hn
    simp only [Metric.mem_closedBall]
    exact iff_of_true hn.le hlt.le
  · filter_upwards [(tendsto_order.1 hr).2 (dist x c) hgt] with n hn
    simp only [Metric.mem_closedBall]
    exact iff_of_false (not_le_of_gt hn) (not_le_of_gt hgt)

theorem ae_tendsto_indicator_closedBall_of_tendsto_radius
    {P I E : Type*} [PseudoMetricSpace P] [MeasurableSpace P]
    [TopologicalSpace E] [Zero E] {μ : Measure P} {l : Filter I}
    {c : P} {r : ℝ} {rn : I → ℝ}
    (f : I → P → E) (f₀ : P → E)
    (hr : Tendsto rn l (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hf : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) l (𝓝 (f₀ x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (Metric.closedBall c (rn n)).indicator (f n) x) l
      (𝓝 ((Metric.closedBall c r).indicator f₀ x)) := by
  have hzero : ∀ᵐ x ∂μ, x ∉ Metric.sphere c r := by
    rw [ae_iff]
    convert hsphere using 1
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, not_not]
  filter_upwards [hzero, hf] with x hx hfx
  have hmem := eventually_mem_closedBall_iff_of_tendsto_radius hr hx
  by_cases hx₀ : x ∈ Metric.closedBall c r
  · rw [Set.indicator_of_mem hx₀]
    apply Filter.Tendsto.congr' _ hfx
    filter_upwards [hmem] with n hn
    exact (Set.indicator_of_mem (hn.mpr hx₀) (f n)).symm
  · rw [Set.indicator_of_notMem hx₀]
    apply Filter.Tendsto.congr' _ (tendsto_const_nhds (x := (0 : E)))
    filter_upwards [hmem] with n hn
    exact (Set.indicator_of_notMem (fun h => hx₀ (hn.mp h)) (f n)).symm

theorem ae_tendsto_indicator_closedBall_restrict_volume_complex
    {I E : Type*} [TopologicalSpace E] [Zero E] {l : Filter I}
    (Ω : Set ℂ) {c : ℂ} {r : ℝ} {rn : I → ℝ}
    (f : I → ℂ → E) (f₀ : ℂ → E)
    (hr : Tendsto rn l (𝓝 r))
    (hf : ∀ᵐ x ∂volume.restrict Ω, Tendsto (fun n => f n x) l (𝓝 (f₀ x))) :
    ∀ᵐ x ∂volume.restrict Ω,
      Tendsto (fun n => (Metric.closedBall c (rn n)).indicator (f n) x) l
        (𝓝 ((Metric.closedBall c r).indicator f₀ x)) := by
  apply ae_tendsto_indicator_closedBall_of_tendsto_radius f f₀ hr _ hf
  exact le_antisymm
    ((Measure.restrict_apply_le (μ := volume) Ω (Metric.sphere c r)).trans_eq
      (Measure.addHaar_sphere volume c r)) bot_le

private theorem norm_indicator_le_max
    {P E : Type*} [MeasurableSpace P] {μ : Measure P} [NormedAddCommGroup E]
    (s : Set P) (f : P → E) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖s.indicator f x‖ ≤ max 0 C := by
  filter_upwards [hC] with x hx
  by_cases hxs : x ∈ s
  · simpa only [Set.indicator_of_mem hxs] using hx.trans (le_max_right 0 C)
  · simpa only [Set.indicator_of_notMem hxs, norm_zero] using le_max_left (0 : ℝ) C

variable {P X : Type*} [PseudoMetricSpace P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [PseudoMetricSpace P] [OpensMeasurableSpace P] in
private theorem integral_indicator_bilinear
    (s : Set P) (hs : MeasurableSet s)
    (A : P → X →L[ℝ] X →L[ℝ] ℝ) (u : P → X) :
    (∫ x, s.indicator A x (u x) (u x) ∂μ) = ∫ x in s, A x (u x) (u x) ∂μ := by
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]
    · simp only [Set.indicator_of_notMem hxs, zero_apply]

theorem integral_quadratic_closedBall_le_liminf_of_weak_of_tendsto_radius
    {c : P} {r : ℝ} {rn : ℕ → ℝ}
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (A₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ C)
    (hpos : ∀ n, ∀ᵐ x ∂μ, ∀ z, 0 ≤ A n x z z)
    (hr : Tendsto rn atTop (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A₀ x)))
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ)
    (hu : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀))) :
    (∫ x in Metric.closedBall c r, A₀ x (u₀ x) (u₀ x) ∂μ) ≤
      liminf (fun n => ∫ x in Metric.closedBall c (rn n), A n x (u n x) (u n x) ∂μ)
        atTop := by
  have hpos' (n : ℕ) : ∀ᵐ x ∂μ, ∀ z,
      0 ≤ (Metric.closedBall c (rn n)).indicator (A n) x z z := by
    filter_upwards [hpos n] with x hx
    intro z
    by_cases hxs : x ∈ Metric.closedBall c (rn n)
    · simpa only [Set.indicator_of_mem hxs] using hx z
    · simp only [Set.indicator_of_notMem hxs, zero_apply, le_refl]
  have h := integral_quadratic_le_liminf_of_weak_of_ae_tendsto (μ := μ) (X := X)
    (fun n => (Metric.closedBall c (rn n)).indicator (A n))
    ((Metric.closedBall c r).indicator A₀)
    (fun n => (hA n).indicator measurableSet_closedBall)
    (max 0 C) (fun n => norm_indicator_le_max (μ := μ) (E := X →L[ℝ] X →L[ℝ] ℝ)
      (Metric.closedBall c (rn n)) (A n) (hC n))
    (ae_tendsto_indicator_closedBall_of_tendsto_radius A A₀ hr hsphere hconv)
    hpos' u u₀ hu
  simpa only [integral_indicator_bilinear _ measurableSet_closedBall] using h

theorem tendsto_integral_quadratic_closedBall_of_tendsto_L2_of_tendsto_radius
    {c : P} {r : ℝ} {rn : ℕ → ℝ}
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (A₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ C)
    (hr : Tendsto rn atTop (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A₀ x)))
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ) (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto
      (fun n => ∫ x in Metric.closedBall c (rn n), A n x (u n x) (u n x) ∂μ) atTop
      (𝓝 (∫ x in Metric.closedBall c r, A₀ x (u₀ x) (u₀ x) ∂μ)) := by
  have h := tendsto_integral_quadratic_of_tendsto_L2_of_ae_tendsto (μ := μ) (X := X)
    (fun n => (Metric.closedBall c (rn n)).indicator (A n))
    ((Metric.closedBall c r).indicator A₀)
    (fun n => (hA n).indicator measurableSet_closedBall)
    (fun n => norm_indicator_le_max (μ := μ) (E := X →L[ℝ] X →L[ℝ] ℝ)
      (Metric.closedBall c (rn n)) (A n) (hC n))
    (ae_tendsto_indicator_closedBall_of_tendsto_radius A A₀ hr hsphere hconv) u u₀ hu
  simpa only [integral_indicator_bilinear _ measurableSet_closedBall] using h

theorem tendsto_integral_quadratic_closedBall_of_tendsto_eLpNorm_of_tendsto_radius
    {c : P} {r : ℝ} {rn : ℕ → ℝ}
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (A₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ C)
    (hr : Tendsto rn atTop (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A₀ x)))
    (f : ℕ → P → X) (f₀ : P → X)
    (hf : ∀ n, MemLp (f n) 2 μ) (hf₀ : MemLp f₀ 2 μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => f n x - f₀ x) 2 μ) atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ x in Metric.closedBall c (rn n), A n x (f n x) (f n x) ∂μ) atTop
      (𝓝 (∫ x in Metric.closedBall c r, A₀ x (f₀ x) (f₀ x) ∂μ)) := by
  have h := tendsto_integral_quadratic_of_tendsto_eLpNorm_of_ae_tendsto (μ := μ) (X := X)
    (fun n => (Metric.closedBall c (rn n)).indicator (A n))
    ((Metric.closedBall c r).indicator A₀)
    (fun n => (hA n).indicator measurableSet_closedBall)
    (fun n => norm_indicator_le_max (μ := μ) (E := X →L[ℝ] X →L[ℝ] ℝ)
      (Metric.closedBall c (rn n)) (A n) (hC n))
    (ae_tendsto_indicator_closedBall_of_tendsto_radius A A₀ hr hsphere hconv)
    f f₀ hf hf₀ hlim
  simpa only [integral_indicator_bilinear _ measurableSet_closedBall] using h

end MeasureTheory

end

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {P X : Type*} [PseudoMetricSpace P] [MeasurableSpace P]
  [OpensMeasurableSpace P] {μ : Measure P}
  [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem isBoundedUnder_integral_quadratic_closedBall_of_weak
    {c : P} (rn : ℕ → ℝ)
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ C)
    (u : ℕ → Lp X 2 μ) (u₀ : Lp X 2 μ)
    (hu : ∀ F : Lp X 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => F (u n)) atTop (𝓝 (F u₀))) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n => ∫ x in Metric.closedBall c (rn n), A n x (u n x) (u n x) ∂μ) := by
  let AI : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ :=
    fun n => (Metric.closedBall c (rn n)).indicator (A n)
  have hAI (n : ℕ) : AEStronglyMeasurable (AI n) μ :=
    (hA n).indicator measurableSet_closedBall
  have hCI (n : ℕ) : ∀ᵐ x ∂μ, ‖AI n x‖ ≤ max 0 C := by
    filter_upwards [hC n] with x hx
    by_cases hxs : x ∈ Metric.closedBall c (rn n)
    · simpa only [AI, Set.indicator_of_mem hxs] using hx.trans (le_max_right 0 C)
    · change ‖(Metric.closedBall c (rn n)).indicator (A n) x‖ ≤ max 0 C
      rw [Set.indicator_of_notMem hxs]
      exact (ContinuousLinearMap.opNorm_zero : ‖(0 : X →L[ℝ] X →L[ℝ] ℝ)‖ = 0).le.trans
        (le_max_left 0 C)
  obtain ⟨D, hD⟩ := isBoundedUnder_integral_quadratic_of_weak AI
    (fun n x y => ((hAI n).apply_continuousLinearMap x).apply_continuousLinearMap y)
    (Eventually.of_forall hCI) u u₀ hu
  have heq (n : ℕ) : (∫ x, AI n x (u n x) (u n x) ∂μ) =
      ∫ x in Metric.closedBall c (rn n), A n x (u n x) (u n x) ∂μ := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      by_cases hxs : x ∈ Metric.closedBall c (rn n)
      · simp only [AI, Set.indicator_of_mem hxs]
      · simp only [AI, Set.indicator_of_notMem hxs, zero_apply]
  refine ⟨D, ?_⟩
  change ∀ᶠ n in atTop,
    (∫ x in Metric.closedBall c (rn n), A n x (u n x) (u n x) ∂μ) ≤ D
  change ∀ᶠ n in atTop, ‖∫ x, AI n x (u n x) (u n x) ∂μ‖ ≤ D at hD
  filter_upwards [hD] with n hn
  exact (le_abs_self _).trans (by simpa only [heq, Real.norm_eq_abs] using hn)

theorem sum_integral_quadratic_closedBall_le_liminf_of_weak_of_tendsto_radius
    {ι : Type*} [Fintype ι] {c : P} {r : ℝ} {rn : ℕ → ℝ}
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (A₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    {C : ℝ} (hC : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ C)
    (hpos : ∀ n, ∀ᵐ x ∂μ, ∀ z, 0 ≤ A n x z z)
    (hr : Tendsto rn atTop (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A₀ x)))
    (u : ι → ℕ → Lp X 2 μ) (u₀ : ι → Lp X 2 μ)
    (hu : ∀ j (F : Lp X 2 μ →L[ℝ] ℝ),
      Tendsto (fun n => F (u j n)) atTop (𝓝 (F (u₀ j)))) :
    (∑ j, ∫ x in Metric.closedBall c r, A₀ x (u₀ j x) (u₀ j x) ∂μ) ≤
      liminf (fun n => ∑ j, ∫ x in Metric.closedBall c (rn n),
        A n x (u j n x) (u j n x) ∂μ) atTop := by
  let q (j : ι) (n : ℕ) := ∫ x in Metric.closedBall c (rn n),
    A n x (u j n x) (u j n x) ∂μ
  have hlo (j : ι) : IsBoundedUnder (· ≥ ·) atTop (q j) := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q j n
    exact Eventually.of_forall fun n => integral_nonneg_of_ae
      (ae_restrict_of_ae ((hpos n).mono fun x hx => hx _))
  have hhi (j : ι) : IsBoundedUnder (· ≤ ·) atTop (q j) :=
    isBoundedUnder_integral_quadratic_closedBall_of_weak rn A hA hC (u j) (u₀ j) (hu j)
  have hlsc (j : ι) : (∫ x in Metric.closedBall c r, A₀ x (u₀ j x) (u₀ j x) ∂μ) ≤
      liminf (q j) atTop :=
    integral_quadratic_closedBall_le_liminf_of_weak_of_tendsto_radius
      A A₀ hA hC hpos hr hsphere hconv (u j) (u₀ j) (hu j)
  have hsum := sum_liminf_le Finset.univ q (fun j _ => hlo j) (fun j _ => hhi j)
  have heqsum : (∑ j, q j) = (fun n => ∑ j, q j n) := by
    funext n
    exact Finset.sum_apply n Finset.univ q
  rw [heqsum] at hsum
  exact (Finset.sum_le_sum fun j _ => hlsc j).trans hsum

theorem sum_integral_quadratic_closedBall_le_of_weak_of_tendsto_L2
    {ι : Type*} [Fintype ι] {c : P} {r : ℝ} {rn : ℕ → ℝ}
    (A : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (A₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (B : ℕ → P → X →L[ℝ] X →L[ℝ] ℝ) (B₀ : P → X →L[ℝ] X →L[ℝ] ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    (hB : ∀ n, AEStronglyMeasurable (B n) μ)
    {CA CB : ℝ}
    (hCA : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ CA)
    (hCB : ∀ n, ∀ᵐ x ∂μ, ‖B n x‖ ≤ CB)
    (hpos : ∀ n, ∀ᵐ x ∂μ, ∀ z, 0 ≤ A n x z z)
    (hr : Tendsto rn atTop (𝓝 r)) (hsphere : μ (Metric.sphere c r) = 0)
    (hAconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (A₀ x)))
    (hBconv : ∀ᵐ x ∂μ, Tendsto (fun n => B n x) atTop (𝓝 (B₀ x)))
    (u : ι → ℕ → Lp X 2 μ) (u₀ : ι → Lp X 2 μ)
    (v : ι → ℕ → Lp X 2 μ) (v₀ : ι → Lp X 2 μ)
    (hu : ∀ j (F : Lp X 2 μ →L[ℝ] ℝ),
      Tendsto (fun n => F (u j n)) atTop (𝓝 (F (u₀ j))))
    (hv : ∀ j, Tendsto (v j) atTop (𝓝 (v₀ j)))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop,
      (∑ j, ∫ x in Metric.closedBall c (rn n), A n x (u j n x) (u j n x) ∂μ) ≤
        (∑ j, ∫ x in Metric.closedBall c (rn n), B n x (v j n x) (v j n x) ∂μ) + ε n) :
    (∑ j, ∫ x in Metric.closedBall c r, A₀ x (u₀ j x) (u₀ j x) ∂μ) ≤
      ∑ j, ∫ x in Metric.closedBall c r, B₀ x (v₀ j x) (v₀ j x) ∂μ := by
  let q (n : ℕ) := ∑ j, ∫ x in Metric.closedBall c (rn n),
    A n x (u j n x) (u j n x) ∂μ
  let q₀ := ∑ j, ∫ x in Metric.closedBall c r, B₀ x (v₀ j x) (v₀ j x) ∂μ
  have hlo : IsBoundedUnder (· ≥ ·) atTop q := by
    refine ⟨0, ?_⟩
    change ∀ᶠ n in atTop, 0 ≤ q n
    exact Eventually.of_forall fun n => Finset.sum_nonneg fun j _ => integral_nonneg_of_ae
      (ae_restrict_of_ae ((hpos n).mono fun x hx => hx _))
  have hstrong : Tendsto (fun n => ∑ j,
      ∫ x in Metric.closedBall c (rn n), B n x (v j n x) (v j n x) ∂μ)
      atTop (𝓝 q₀) :=
    tendsto_finsetSum Finset.univ fun j _ =>
      tendsto_integral_quadratic_closedBall_of_tendsto_L2_of_tendsto_radius
        B B₀ hB hCB hr hsphere hBconv (v j) (v₀ j) (hv j)
  have hright : Tendsto (fun n => (∑ j,
      ∫ x in Metric.closedBall c (rn n), B n x (v j n x) (v j n x) ∂μ) + ε n)
      atTop (𝓝 q₀) := by
    simpa only [add_zero] using hstrong.add hε
  have hupp : liminf q atTop ≤ q₀ := by
    apply liminf_le_of_le hlo
    intro b hb
    apply ge_of_tendsto hright
    filter_upwards [hb, hle] with n hbn hn
    exact hbn.trans hn
  exact (sum_integral_quadratic_closedBall_le_liminf_of_weak_of_tendsto_radius
    A A₀ hA hCA hpos hr hsphere hAconv u u₀ hu).trans hupp

end MeasureTheory

end
