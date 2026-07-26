import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartWkpCompat

/-!
# Completeness of the genuine tensor chart `W^{k,p}` carrier

This file assembles the exact compatibility and quantitative transport results
of the preceding tensor chart files.  A Cauchy sequence has scalar limits in
every POU-weighted chart component.  Those limits are pulled back as genuine
dependent tensor sections and summed over the finite canonical active atlas.

The proof never identifies a tensor section with an unconstrained array of
scalar functions.  `tensorLimitSec` is a genuine section, `tensorLimit_mem`
proves its chart `W^{k,p}` membership, and `wkpTensor_limit` proves convergence
in the total tensor chart norm.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma ae_sum
    {X ι A : Type*} [MeasurableSpace X] [AddCommMonoid A]
    {μ : Measure X} (t : Finset ι) (f h : ι → X → A)
    (heq : ∀ i ∈ t, f i =ᵐ[μ] h i) :
    (fun x => ∑ i ∈ t, f i x) =ᵐ[μ]
      (fun x => ∑ i ∈ t, h i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (heq i (Finset.mem_insert_self i t)).add
        (ih (fun j hj => heq j (Finset.mem_insert_of_mem hj)))

private lemma memWkp_sum
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {d k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set X} (hΩ : IsOpen Ω) {ι : Type*} (t : Finset ι)
    (f : ι → X → ℝ)
    (hf : ∀ i ∈ t, MemWkp (d := d) k p (f i) Ω) :
    MemWkp (d := d) k p (fun x => ∑ i ∈ t, f i x) Ω := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MemWkp_zero_fun (d := d) hp hΩ
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact MemWkp.add (d := d) hp hΩ
        (hf i (Finset.mem_insert_self i t))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private lemma wkpNorm_sum_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {d k : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {Ω : Set X} (hΩ : IsOpen Ω) {ι : Type*} (t : Finset ι)
    (f : ι → X → ℝ)
    (hf : ∀ i ∈ t, MemWkp (d := d) k p (f i) Ω) :
    wkpNorm (d := d) k p (fun x => ∑ i ∈ t, f i x) Ω ≤
      ∑ i ∈ t, wkpNorm (d := d) k p (f i) Ω := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [wkpNorm_zero_fun_zero (d := d) hp hΩ]
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      exact (wkpNorm_add_le (d := d) hp hΩ
        (hf i (Finset.mem_insert_self i t))
        (memWkp_sum (d := d) hp hΩ t f
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
        (add_le_add_left
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) _)

private lemma secComp_sum
    {r s : ℕ} {ι : Type*} (t : Finset ι)
    (F : ι → RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s (∑ i ∈ t, F i) α P.1 P.2 =
      fun y => ∑ i ∈ t,
        secChartComp (I := I) (M := M) r s (F i) α P.1 P.2 y := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [secChartComp_zero (I := I) (M := M)]
      rfl
  | @insert i t hi ih =>
      simp only [Finset.sum_insert hi]
      rw [secChartComp_add (I := I) (M := M), ih]
      rfl

private lemma secTerm_sub
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (β α : M)
    (P Q : TensorCompIdx (E := E) r s) (v w : EuclN → ℝ) :
    secTransTerm (I := I) (M := M) g r s β α P Q (fun y => v y - w y) =
      fun y => secTransTerm (I := I) (M := M) g r s β α P Q v y -
        secTransTerm (I := I) (M := M) g r s β α P Q w y := by
  classical
  funext y
  unfold secTransTerm chartPushed
  set x : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y)
  by_cases hx : x ∈ (chartAt H β).source
  · rw [chartPullback_apply_of_mem (I := I) (M := M) β _ hx,
      chartPullback_apply_of_mem (I := I) (M := M) β _ hx,
      chartPullback_apply_of_mem (I := I) (M := M) β _ hx]
    ring
  · rw [chartPullback_apply_of_notMem (I := I) (M := M) β _ hx,
      chartPullback_apply_of_notMem (I := I) (M := M) β _ hx,
      chartPullback_apply_of_notMem (I := I) (M := M) β _ hx]
    ring

/-- Every POU-weighted chart component has pointwise closed support in the
fixed compact POU kernel of its chart. -/
theorem secComp_support
    (r s : ℕ) (S : RSTensorSection I M r s) (α : M)
    (P : TensorCompIdx (E := E) r s) :
    tsupport (secChartComp (I := I) (M := M) r s S α P.1 P.2) ⊆
      chartImagePOUTsupport (I := I) (M := M) α := by
  refine closure_minimal ?_
    (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
  intro y hy
  by_contra hyK
  have hzero : secChartComp (I := I) (M := M) r s S α P.1 P.2 y = 0 := by
    by_cases hyΩ : y ∈ chartTargetEuclid (I := I) (M := M) α
    · exact secComp_zero_kernel (I := I) (M := M) r s S α P.1 P.2 hyΩ hyK
    · exact secComp_apply_off (I := I) (M := M) r s S α P.1 P.2 hyΩ
  exact hy hzero

/-- The scalar error between an iterate and the closed-kernel representative
of its chosen component limit. -/
def secCompErr
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (n : ℕ) (β : M) (Q : TensorCompIdx (E := E) r s) : EuclN → ℝ :=
  fun y => secChartComp (I := I) (M := M) r s (u n).1 β Q.1 Q.2 y -
    secCompRep (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β Q.1 Q.2 y

/-- Each source component error belongs to `W^{k,p}`. -/
theorem secCompErr_mem
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (n : ℕ) (β : M) (Q : TensorCompIdx (E := E) r s) :
    MemWkp (d := Module.finrank ℝ E) k p
      (secCompErr (I := I) (M := M) g r s k hp hp_top u h_cauchy n β Q)
      (chartTargetEuclid (I := I) (M := M) β) := by
  exact MemWkp.sub (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) β)
    ((u n).2 β Q.1 Q.2)
    (secCompRep_mem (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β Q.1 Q.2)

/-- Each source component error has the same fixed compact POU support. -/
theorem secCompErr_supp
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (n : ℕ) (β : M) (Q : TensorCompIdx (E := E) r s) :
    tsupport
        (secCompErr (I := I) (M := M) g r s k hp hp_top u h_cauchy n β Q) ⊆
      chartImagePOUTsupport (I := I) (M := M) β := by
  refine closure_minimal ?_
    (chartImagePOUTsupport_isCompact (I := I) (M := M) β).isClosed
  intro y hy
  by_contra hyK
  have hleft : secChartComp (I := I) (M := M) r s (u n).1 β Q.1 Q.2 y = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hs => hyK (secComp_support (I := I) (M := M) r s (u n).1 β Q hs))
  have hright : secCompRep (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β Q.1 Q.2 y = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun hs => hyK (secCompRep_support (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2 hs))
  exact hy (by simp only [secCompErr, hleft, hright, sub_zero])

/-- Each scalar source error tends to zero in `W^{k,p}`. -/
theorem secCompErr_tendsto
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (β : M) (Q : TensorCompIdx (E := E) r s) :
    Tendsto
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (secCompErr (I := I) (M := M) g r s k hp hp_top u h_cauchy n β Q)
        (chartTargetEuclid (I := I) (M := M) β))
      atTop (𝒩 0) := by
  simpa only [secCompErr] using
    (secCompRep_tendsto (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β Q.1 Q.2)

/-- Target components of the genuine assembled limit are the finite sums of
the transported scalar source limits. -/
theorem tensorLimit_comp
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s
        (tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy)
        α P.1 P.2 =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Q : TensorCompIdx (E := E) r s,
          secTransTerm (I := I) (M := M) g r s β α P Q
            (secCompRep (I := I) (M := M) g r s k hp hp_top u
              h_cauchy β Q.1 Q.2) y) := by
  classical
  let Sf := chartAtlasPOU_finset (I := I) (M := M)
  let F : M → RSTensorSection I M r s := fun β =>
    secModelPull (I := I) (M := M) r s β
      (secModelLimit (I := I) (M := M) g r s k hp hp_top u h_cauchy β)
  have hlimit : tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy =
      ∑ β ∈ Sf, F β := by
    funext x
    rfl
  rw [hlimit, secComp_sum (I := I) (M := M) Sf F α P]
  exact ae_sum Sf
    (fun β => secChartComp (I := I) (M := M) r s (F β) α P.1 P.2)
    (fun β y => ∑ Q : TensorCompIdx (E := E) r s,
      secTransTerm (I := I) (M := M) g r s β α P Q
        (secCompRep (I := I) (M := M) g r s k hp hp_top u
          h_cauchy β Q.1 Q.2) y)
    (fun β _ => secPullLimitEq (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β α P)

/-- The genuine finite POU assembly of the chart limits belongs to the tensor
chart `W^{k,p}` carrier. -/
theorem tensorLimit_mem
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε) :
    MemWkpTensor (I := I) (M := M) g k p
      (tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy) := by
  classical
  intro α Idx Jdx
  let Sf := chartAtlasPOU_finset (I := I) (M := M)
  let P : TensorCompIdx (E := E) r s := ⟨Idx, Jdx⟩
  let q : M → TensorCompIdx (E := E) r s → EuclN → ℝ := fun β Q =>
    secTransTerm (I := I) (M := M) g r s β α P Q
      (secCompRep (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2)
  have hq_mem : ∀ β Q, MemWkp (d := Module.finrank ℝ E) k p (q β Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
    intro β Q
    have htransport :=
      (secTermJointK (I := I) (M := M) g r s k hp hp_top β α P Q).choose_spec.2
      (secCompRep_mem (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2)
      (secCompRep_support (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2)
    exact htransport.1
  have hinner : ∀ β, MemWkp (d := Module.finrank ℝ E) k p
      (fun y => ∑ Q : TensorCompIdx (E := E) r s, q β Q y)
      (chartTargetEuclid (I := I) (M := M) α) := fun β =>
    memWkp_sum (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α) Finset.univ (q β)
      (fun Q _ => hq_mem β Q)
  have hsum : MemWkp (d := Module.finrank ℝ E) k p
      (fun y => ∑ β ∈ Sf, ∑ Q : TensorCompIdx (E := E) r s, q β Q y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    memWkp_sum (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α) Sf
      (fun β y => ∑ Q : TensorCompIdx (E := E) r s, q β Q y)
      (fun β _ => hinner β)
  exact (MemWkp_congr_ae (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)
    (tensorLimit_comp (I := I) (M := M) g r s k hp hp_top u
      h_cauchy α P)).mpr hsum

/-- The target-chart error is exactly the finite transport of the scalar
source-chart errors. -/
theorem tensorErr_comp
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (n : ℕ) (α : M) (P : TensorCompIdx (E := E) r s) :
    secChartComp (I := I) (M := M) r s
        ((u n).1 -
          tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy)
        α P.1 P.2 =ᵐ[
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)]
      (fun y => ∑ β ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Q : TensorCompIdx (E := E) r s,
          secTransTerm (I := I) (M := M) g r s β α P Q
            (secCompErr (I := I) (M := M) g r s k hp hp_top u
              h_cauchy n β Q) y) := by
  classical
  rw [secChartComp_sub (I := I) (M := M)]
  filter_upwards
    [secCompDecomp (I := I) (M := M) g r s (u n).1 α P,
      tensorLimit_comp (I := I) (M := M) g r s k hp hp_top u
        h_cauchy α P] with y hyu hyv
  simp only [Pi.sub_apply]
  rw [hyu, hyv, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro β _
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro Q _
  simpa only [secCompErr] using
    (congrFun (secTerm_sub (I := I) (M := M) g r s β α P Q
      (secChartComp (I := I) (M := M) r s (u n).1 β Q.1 Q.2)
      (secCompRep (I := I) (M := M) g r s k hp hp_top u
        h_cauchy β Q.1 Q.2)) y).symm

/-- The chart sum defining the tensor norm is the finite sum over the
canonical active atlas. -/
theorem tensorNorm_eq_sum
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (S : RSTensorSection I M r s) :
    wkpTensorNorm (I := I) (M := M) g k p S =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) k p
              (secChartComp (I := I) (M := M) r s S α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  unfold wkpTensorNorm
  rw [tsum_eq_sum (s := chartAtlasPOU_finset (I := I) (M := M))]
  intro α hα
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [secComp_zero_off (I := I) (M := M) r s S hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) hp
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- Each fixed target component of the genuine assembled tensor limit is the
limit of the corresponding component of the original Cauchy sequence. -/
theorem targetErr_tendsto
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε)
    (α : M) (P : TensorCompIdx (E := E) r s) :
    Tendsto
      (fun n => wkpNorm (d := Module.finrank ℝ E) k p
        (secChartComp (I := I) (M := M) r s
          ((u n).1 -
            tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy)
          α P.1 P.2)
        (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝒩 0) := by
  classical
  let Sf := chartAtlasPOU_finset (I := I) (M := M)
  let C : M → TensorCompIdx (E := E) r s → ℝ := fun β Q =>
    (secTermJointK (I := I) (M := M) g r s k hp hp_top β α P Q).choose
  let q : ℕ → M → TensorCompIdx (E := E) r s → EuclN → ℝ :=
    fun n β Q => secTransTerm (I := I) (M := M) g r s β α P Q
      (secCompErr (I := I) (M := M) g r s k hp hp_top u
        h_cauchy n β Q)
  have hq : ∀ n β Q,
      MemWkp (d := Module.finrank ℝ E) k p (q n β Q)
          (chartTargetEuclid (I := I) (M := M) α) ∧
        wkpNorm (d := Module.finrank ℝ E) k p (q n β Q)
            (chartTargetEuclid (I := I) (M := M) α) ≤
          ENNReal.ofReal (C β Q) *
            wkpNorm (d := Module.finrank ℝ E) k p
              (secCompErr (I := I) (M := M) g r s k hp hp_top u
                h_cauchy n β Q)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro n β Q
    exact (secTermJointK (I := I) (M := M) g r s k hp hp_top
      β α P Q).choose_spec.2
        (secCompErr_mem (I := I) (M := M) g r s k hp hp_top u
          h_cauchy n β Q)
        (secCompErr_supp (I := I) (M := M) g r s k hp hp_top u
          h_cauchy n β Q)
  have h_bound : ∀ n,
      wkpNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s
            ((u n).1 -
              tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy)
            α P.1 P.2)
          (chartTargetEuclid (I := I) (M := M) α) ≤
        ∑ β ∈ Sf, ∑ Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal (C β Q) *
            wkpNorm (d := Module.finrank ℝ E) k p
              (secCompErr (I := I) (M := M) g r s k hp hp_top u
                h_cauchy n β Q)
              (chartTargetEuclid (I := I) (M := M) β) := by
    intro n
    rw [wkpNorm_congr_ae (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
      (tensorErr_comp (I := I) (M := M) g r s k hp hp_top u
        h_cauchy n α P)]
    refine (wkpNorm_sum_le (d := Module.finrank ℝ E) hp
      (chartTargetEuclid_isOpen (I := I) (M := M) α) Sf
      (fun β y => ∑ Q : TensorCompIdx (E := E) r s, q n β Q y)
      ?_).trans ?_
    · intro β _
      exact memWkp_sum (d := Module.finrank ℝ E) hp
        (chartTargetEuclid_isOpen (I := I) (M := M) α) Finset.univ
        (q n β) (fun Q _ => (hq n β Q).1)
    · refine Finset.sum_le_sum ?_
      intro β _
      exact (wkpNorm_sum_le (d := Module.finrank ℝ E) hp
        (chartTargetEuclid_isOpen (I := I) (M := M) α) Finset.univ
        (q n β) (fun Q _ => (hq n β Q).1)).trans
          (Finset.sum_le_sum (fun Q _ => (hq n β Q).2))
  have h_pair : ∀ β ∈ Sf, ∀ Q : TensorCompIdx (E := E) r s,
      Tendsto
        (fun n => ENNReal.ofReal (C β Q) *
          wkpNorm (d := Module.finrank ℝ E) k p
            (secCompErr (I := I) (M := M) g r s k hp hp_top u
              h_cauchy n β Q)
            (chartTargetEuclid (I := I) (M := M) β))
        atTop (𝒩 0) := by
    intro β _ Q
    have herr := secCompErr_tendsto (I := I) (M := M) g r s k hp hp_top u
      h_cauchy β Q
    have hC_ne_top : ENNReal.ofReal (C β Q) ≠ (⊤ : ℝ≥0∞) :=
      ENNReal.ofReal_ne_top
    have hmul := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (C β Q)) (b := 0) herr
      (Or.inr hC_ne_top)
    simpa using hmul
  have h_inner : ∀ β ∈ Sf,
      Tendsto
        (fun n => ∑ Q : TensorCompIdx (E := E) r s,
          ENNReal.ofReal (C β Q) *
            wkpNorm (d := Module.finrank ℝ E) k p
              (secCompErr (I := I) (M := M) g r s k hp hp_top u
                h_cauchy n β Q)
              (chartTargetEuclid (I := I) (M := M) β))
        atTop (𝒩 0) := by
    intro β hβ
    simpa using tendsto_finset_sum Finset.univ
      (fun Q _ => h_pair β hβ Q)
  have h_rhs : Tendsto
      (fun n => ∑ β ∈ Sf, ∑ Q : TensorCompIdx (E := E) r s,
        ENNReal.ofReal (C β Q) *
          wkpNorm (d := Module.finrank ℝ E) k p
            (secCompErr (I := I) (M := M) g r s k hp hp_top u
              h_cauchy n β Q)
            (chartTargetEuclid (I := I) (M := M) β))
      atTop (𝒩 0) := by
    simpa using tendsto_finset_sum Sf h_inner
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds h_rhs
    (Filter.Eventually.of_forall (fun _ => zero_le _))
    (Filter.Eventually.of_forall h_bound)

/-- The original tensor Cauchy sequence converges to the genuine finite POU
assembly in the total tensor chart norm. -/
theorem tensorLimit_tendsto
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε) :
    Tendsto
      (fun n => wkpTensorNorm (I := I) (M := M) g k p
        ((u n).1 -
          tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy))
      atTop (𝒩 0) := by
  classical
  let Sf := chartAtlasPOU_finset (I := I) (M := M)
  have hcomp : ∀ α ∈ Sf,
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∀ Jdx : Fin s → Fin (Module.finrank ℝ E),
      Tendsto
        (fun n => wkpNorm (d := Module.finrank ℝ E) k p
          (secChartComp (I := I) (M := M) r s
            ((u n).1 - tensorLimitSec (I := I) (M := M)
              g r s k hp hp_top u h_cauchy) α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝒩 0) := by
    intro α _ Idx Jdx
    exact targetErr_tendsto (I := I) (M := M) g r s k hp hp_top u
      h_cauchy α ⟨Idx, Jdx⟩
  have hJ : ∀ α ∈ Sf,
      ∀ Idx : Fin r → Fin (Module.finrank ℝ E),
      Tendsto
        (fun n => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) k p
            (secChartComp (I := I) (M := M) r s
              ((u n).1 - tensorLimitSec (I := I) (M := M)
                g r s k hp hp_top u h_cauchy) α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝒩 0) := by
    intro α hα Idx
    simpa using tendsto_finset_sum Finset.univ
      (fun Jdx _ => hcomp α hα Idx Jdx)
  have hIdx : ∀ α ∈ Sf,
      Tendsto
        (fun n => ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) k p
              (secChartComp (I := I) (M := M) r s
                ((u n).1 - tensorLimitSec (I := I) (M := M)
                  g r s k hp hp_top u h_cauchy) α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
        atTop (𝒩 0) := by
    intro α hα
    simpa using tendsto_finset_sum Finset.univ
      (fun Idx _ => hJ α hα Idx)
  have htotal : Tendsto
      (fun n => ∑ α ∈ Sf,
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) k p
              (secChartComp (I := I) (M := M) r s
                ((u n).1 - tensorLimitSec (I := I) (M := M)
                  g r s k hp hp_top u h_cauchy) α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α))
      atTop (𝒩 0) := by
    simpa using tendsto_finset_sum Sf hIdx
  simpa only [tensorNorm_eq_sum (I := I) (M := M) g r s k hp] using htotal

/-- Representative-level completeness for genuine tensor `W^{k,p}` sections.
The limit is a genuine dependent tensor section, not an arbitrary compatible
array of chart functions. -/
theorem wkpTensor_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε) :
    ∃ v : WkpTensor (I := I) (M := M) g r s k p hp,
      Tendsto
        (fun n => wkpTensorNorm (I := I) (M := M) g k p
          ((u n).1 - v.1))
        atTop (𝒩 0) := by
  refine ⟨⟨tensorLimitSec (I := I) (M := M) g r s k hp hp_top u h_cauchy,
    tensorLimit_mem (I := I) (M := M) g r s k hp hp_top u h_cauchy⟩, ?_⟩
  exact tensorLimit_tendsto (I := I) (M := M) g r s k hp hp_top u h_cauchy

/-- The representative completeness theorem expressed through the norm that
already descends to `WkpTensorQuot`.  This avoids installing global quotient
algebra or metric instances: the class of each difference has quotient norm
tending to zero. -/
theorem wkpTensorQ_limit
    (g : SmoothRiemannianMetric I M) (r s k : ℕ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (u : ℕ → WkpTensor (I := I) (M := M) g r s k p hp)
    (h_cauchy : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m n : ℕ,
      N ≤ m → N ≤ n →
      wkpTensorNorm (I := I) (M := M) g k p
        ((u m).1 - (u n).1) ≤ ENNReal.ofReal ε) :
    ∃ v : WkpTensor (I := I) (M := M) g r s k p hp,
      Tendsto
        (fun n => wkpTensorQNorm (I := I) (M := M) g r s k p hp
          (Quotient.mk
            (tensorChartSetoid (I := I) (M := M) g r s k p hp)
            ⟨(u n).1 - v.1,
              MemWkpTensor.sub (I := I) (M := M) g hp (u n).2 v.2⟩))
        atTop (𝒩 0) := by
  obtain ⟨v, hv⟩ :=
    wkpTensor_limit (I := I) (M := M) g r s k hp hp_top u h_cauchy
  refine ⟨v, ?_⟩
  simpa only [wkpTensorQNorm_mk] using hv

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
