import DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff ENNReal NNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ ι
local notation "H" => EuclideanSpace ℝ κ

private theorem hasWeakPartialDeriv_ball_of_forall_smaller_ball
    {c : E} {a : ℝ} {u v : E → ℝ} {j : Fin d}
    (h : ∀ r < a, DeGiorgi.HasWeakPartialDeriv j v u (Metric.ball c r)) :
    DeGiorgi.HasWeakPartialDeriv j v u (Metric.ball c a) := by
  intro ψ hψ hψc hψB
  obtain ⟨r, hra, hψr⟩ := exists_lt_subset_ball (isClosed_tsupport ψ) hψB
  have hid := h r hra ψ hψ hψc hψr
  have hleft (s : Set E) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1)) =
        ∫ x, u x * fderiv ℝ ψ x (EuclideanSpace.single j 1) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport ψ := fun hmem => hx (hs hmem)
    rw [fderiv_of_notMem_tsupport ℝ hxs, zero_apply, mul_zero]
  have hright (s : Set E) (hs : tsupport ψ ⊆ s) :
      (∫ x in s, v x * ψ x) = ∫ x, v x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxs : x ∉ tsupport ψ := fun hmem => hx (hs hmem)
    rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero]
  rw [hleft (Metric.ball c r) hψr, hright (Metric.ball c r) hψr] at hid
  rw [hleft (Metric.ball c a) hψB, hright (Metric.ball c a) hψB]
  exact hid

theorem exists_memW1pWitnesses_comp_contDiff_on_ball_of_bounded_fderiv
    {c : E} {a : ℝ} {f : E → F}
    (hf : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => f x i) (Metric.ball c a))
    (T : F → H) (hT : ContDiff ℝ 1 T)
    {C : ℝ} (hC : ∀ y, ‖fderiv ℝ T y‖ ≤ C) :
    ∃ hw : ∀ k, DeGiorgi.MemW1pWitness 2 (fun x => T (f x) k) (Metric.ball c a),
      ∀ k x j, (hw k).weakGrad x j =
        (fderiv ℝ T (f x) (WithLp.toLp 2 (fun i => (hf i).weakGrad x j))) k := by
  let B := Metric.ball c a
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono Metric.ball_subset_closedBall).trans_lt
      (isCompact_closedBall c a).measure_lt_top).ne
  have hfm : MemLp f 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => (hf i).memLp
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ T 0)).trans (hC 0)
  let L : ℝ≥0 := NNReal.mk C hC0
  have hLip : LipschitzWith L T := lipschitzWith_of_nnnorm_fderiv_le
    (hT.differentiable one_ne_zero) (fun y => hC y)
  have hTm : MemLp (fun x => T (f x)) 2 (volume.restrict B) := by
    have hsub : MemLp (fun x => T (f x) - T 0) 2 (volume.restrict B) := by
      apply hfm.of_le_mul
        ((hT.continuous.comp_aestronglyMeasurable hfm.aestronglyMeasurable).sub
          aestronglyMeasurable_const)
      exact Filter.Eventually.of_forall fun x => by
        change ‖T (f x) - T 0‖ ≤ (L : ℝ) * ‖f x‖
        simpa only [sub_zero] using hLip.norm_sub_le (f x) 0
    simpa only [Pi.add_def, sub_add_cancel] using hsub.add (memLp_const (T 0))
  let G (j : Fin d) (x : E) : F := WithLp.toLp 2 (fun i => (hf i).weakGrad x j)
  have hG (j : Fin d) : MemLp (G j) 2 (volume.restrict B) :=
    MemLp.of_eval_piLp fun i => (hf i).weakGrad_component_memLp j
  have htarget (j : Fin d) :
      MemLp (fun x => fderiv ℝ T (f x) (G j x)) 2 (volume.restrict B) :=
    MemLp.clm_apply_of_ae_norm_le
      ((hT.continuous_fderiv one_ne_zero).comp_aestronglyMeasurable hfm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hC (f x)) (hG j)
  have hweak (k : κ) (j : Fin d) :
      DeGiorgi.HasWeakPartialDeriv j
        (fun x => (fderiv ℝ T (f x) (G j x)) k) (fun x => T (f x) k) B := by
    apply hasWeakPartialDeriv_ball_of_forall_smaller_ball
    intro r hra
    obtain ⟨hw, hweq⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball
      Metric.isOpen_ball hf T hT hC (Metric.closedBall_subset_ball hra)
    have heq : (fun x => (hw k).weakGrad x j) =
        fun x => (fderiv ℝ T (f x) (G j x)) k := by
      funext x
      exact hweq k x j
    have hh := (hw k).isWeakGrad j
    change DeGiorgi.HasWeakPartialDeriv j (fun x => (hw k).weakGrad x j)
      (fun x => T (f x) k) (Metric.ball c r) at hh
    rw [heq] at hh
    exact hh
  let hw (k : κ) : DeGiorgi.MemW1pWitness 2 (fun x => T (f x) k) B :=
    { memLp := hTm.eval_piLp k
      weakGrad := fun x => WithLp.toLp 2 (fun j => (fderiv ℝ T (f x) (G j x)) k)
      weakGrad_component_memLp := fun j => (htarget j).eval_piLp k
      isWeakGrad := fun j => hweak k j }
  exact ⟨hw, fun k x j => rfl⟩

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end
