import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Basic
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.H1.Compactness.Modulus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.SeparableMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal Topology InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TimeSobolev

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem integral_uIoc_le (f : timeL2 X T) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ∫ s in uIoc a b, ‖f s‖ ≤ Real.sqrt |b - a| * ‖f‖ := by
  let μ : Measure ℝ := volume.restrict (uIoc a b)
  have hsub : uIoc a b ⊆ Icc (0 : ℝ) T :=
    uIoc_subset_uIcc.trans (uIcc_subset_Icc ha hb)
  have hle : μ ≤ timeMeasure T := by
    exact Measure.restrict_mono hsub le_rfl
  have hmeas : AEStronglyMeasurable (fun s => f s) μ :=
    (Lp.aestronglyMeasurable f).mono_measure hle
  have hmono : eLpNorm (fun s => f s) 2 μ ≤
      eLpNorm (fun s => f s) 2 (timeMeasure T) :=
    eLpNorm_mono_measure _ hle
  have hne : eLpNorm (fun s => f s) 2 μ ≠ ∞ :=
    (hmono.trans_lt (Lp.eLpNorm_ne_top f).lt_top).ne
  have hint : ∫ s in uIoc a b, ‖f s‖ =
      (eLpNorm (fun s => f s) 1 μ).toReal := by
    rw [show (∫ s in uIoc a b, ‖f s‖) = ∫ s, ‖f s‖ ∂μ from rfl,
      integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ) (p := 1) (q := 2) (by norm_num) hmeas
  have hfin : eLpNorm (fun s => f s) 2 μ *
      μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    refine ENNReal.mul_ne_top hne ?_
    simp only [μ, Measure.restrict_apply_univ, Real.volume_uIoc]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (by finiteness)
  rw [hint]
  refine le_trans (ENNReal.toReal_mono hfin hholder) ?_
  rw [ENNReal.toReal_mul, show μ Set.univ = ENNReal.ofReal |b - a| by
    simp only [μ, Measure.restrict_apply_univ, Real.volume_uIoc],
    show (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by
      norm_num,
    toReal_ofReal_rpow_half, mul_comm (Real.sqrt |b - a|) ‖f‖]
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hmono

namespace timeH1

omit [CompleteSpace X] in
theorem toFun_sub_le (u : timeH1 X T) {a b : ℝ}
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    ‖u.toFun b - u.toFun a‖ ≤ Real.sqrt |b - a| * ‖u.deriv‖ := by
  rw [u.toFun_sub_toFun ha hb]
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    (TimeSobolev.integral_uIoc_le u.deriv ha hb)

private def evalAt (t : Icc (0 : ℝ) T) : timeH1 X T →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun u => u.toFun t
      map_add' := fun u v => toFun_add u v t.property
      map_smul' := fun c u => toFun_smul c u t.property }
    (1 + Real.sqrt T) fun u => u.norm_toFun_le_norm t.property

omit [CompleteSpace X] in
@[simp]
private theorem evalAt_apply (t : Icc (0 : ℝ) T) (u : timeH1 X T) :
    evalAt t u = u.toFun t :=
  rfl

private def contRep (u : timeH1 X T) : C(Icc (0 : ℝ) T, X) :=
  ⟨fun t => u.toFun t, u.continuousOn_toFun.domRestrict⟩

omit [CompleteSpace X] in
@[simp]
private theorem contRep_apply (u : timeH1 X T) (t : Icc (0 : ℝ) T) :
    contRep u t = u.toFun t :=
  rfl

section Hilbert

variable {Y : Type*} [NormedAddCommGroup Y] [CompleteSpace Y]
  [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem compact_subseq (u : ℕ → timeH1 Y T) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ (phi : ℕ → ℕ) (uLim : timeH1 Y T),
      StrictMono phi ∧
        (∀ z, Tendsto (fun n => inner ℝ (u (phi n)) z) atTop
          (nhds (inner ℝ uLim z))) ∧
        TendstoUniformly
          (fun n (t : Icc (0 : ℝ) T) => (u (phi n)).toFun t)
          (fun t => uLim.toFun t) atTop := by
  let f : ℕ → C(Icc (0 : ℝ) T, Y) := fun n => contRep (u n)
  have hmod : Tendsto (fun r : ℝ => C * Real.sqrt r) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun r : ℝ => C * Real.sqrt r) 0 :=
      Real.continuous_sqrt.continuousAt.const_mul C
    simpa only [ContinuousAt, Real.sqrt_zero, mul_zero] using hcont
  have hequi : Equicontinuous (fun n => (f n : Icc (0 : ℝ) T → Y)) := by
    refine Metric.equicontinuous_of_continuity_modulus
      (fun r : ℝ => C * Real.sqrt r) hmod _ ?_
    intro a b n
    simp only [f, contRep_apply, dist_eq_norm]
    change ‖(u n).toFun a - (u n).toFun b‖ ≤ C * Real.sqrt (dist a b)
    calc
      ‖(u n).toFun a - (u n).toFun b‖
          = ‖(u n).toFun b - (u n).toFun a‖ := norm_sub_rev _ _
      _ ≤ Real.sqrt |(b : ℝ) - a| * ‖(u n).deriv‖ :=
        (u n).toFun_sub_le a.property b.property
      _ ≤ Real.sqrt |(b : ℝ) - a| * C := by
        exact mul_le_mul_of_nonneg_left ((u n).norm_deriv_le.trans (hu n))
          (Real.sqrt_nonneg _)
      _ = C * Real.sqrt (dist a b) := by
        rw [mul_comm]
        congr 2
        simpa [Real.dist_eq, abs_sub_comm] using
          (congrArg Real.sqrt (Subtype.dist_eq a b)).symm
  have hbdd : ∀ t : Icc (0 : ℝ) T, ∃ M : ℝ, ∀ n, ‖f n t‖ ≤ M := by
    intro t
    refine ⟨(1 + Real.sqrt T) * C, fun n => ?_⟩
    calc
      ‖f n t‖ = ‖(u n).toFun t‖ := rfl
      _ ≤ (1 + Real.sqrt T) * ‖u n‖ := (u n).norm_toFun_le_norm t.property
      _ ≤ (1 + Real.sqrt T) * C := by
        exact mul_le_mul_of_nonneg_left (hu n) (by positivity)
  rcases DifferentialGeometry.CheegerGromovCompactness.arzelaAscoli_subseq_vec f hequi hbdd with
    ⟨phi₁, g, hphi₁, hg⟩
  have hguniform : TendstoUniformly (fun n => f (phi₁ n)) g atTop :=
    tendstoUniformlyOn_univ.mp (hg Set.univ isCompact_univ)
  let w : ℕ → WeakDual ℝ (timeH1 Y T) := fun n =>
    StrongDual.toWeakDual (innerSL ℝ (u (phi₁ n)))
  have hwmem : ∀ n, w n ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ (timeH1 Y T)) C := by
    intro n
    rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    change ‖WeakDual.toStrongDual
      (StrongDual.toWeakDual (innerSL ℝ (u (phi₁ n))))‖ ≤ C
    rw [WeakDual.toStrongDual, LinearEquiv.symm_apply_apply, innerSL_apply_norm]
    exact hu (phi₁ n)
  let : SecondCountableTopology Y := inferInstance
  let : TopologicalSpace.SeparableSpace Y := inferInstance
  let : IsSeparable (timeMeasure T) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (timeL2 Y T) := Lp.SecondCountableTopology
  let : SecondCountableTopology (timeH1 Y T) := by
    unfold timeH1
    exact WithLp.secondCountableTopology 2 Y (timeL2 Y T)
  let : TopologicalSpace.SeparableSpace (timeH1 Y T) :=
    TopologicalSpace.SecondCountableTopology.to_separableSpace
  rcases WeakDual.isSeqCompact_closedBall ℝ (timeH1 Y T)
      (0 : StrongDual ℝ (timeH1 Y T)) C hwmem with
    ⟨wLim, _hwLim, phi₂, hphi₂, hw⟩
  let uLim : timeH1 Y T :=
    (InnerProductSpace.toDual ℝ (timeH1 Y T)).symm (WeakDual.toStrongDual wLim)
  have hweak : ∀ z, Tendsto (fun n => inner ℝ (u (phi₁ (phi₂ n))) z) atTop
      (nhds (inner ℝ uLim z)) := by
    intro z
    have heval := (WeakDual.eval_continuous z).continuousAt.tendsto.comp hw
    simpa only [Function.comp_apply, Function.comp_def, w, StrongDual.toWeakDual_apply,
      WeakDual.toStrongDual_apply, innerSL_apply_apply, uLim,
      InnerProductSpace.toDual_symm_apply] using heval
  have hguniform' : TendstoUniformly (fun n => f (phi₁ (phi₂ n))) g atTop := by
    intro V hV
    have h := hphi₂.tendsto_atTop.eventually (hguniform V hV)
    change ∀ᶠ n in atTop, ∀ x, (g x, f (phi₁ (phi₂ n)) x) ∈ V at h
    exact h
  have hgeq : ∀ t : Icc (0 : ℝ) T, g t = uLim.toFun t := by
    intro t
    apply ext_inner_right ℝ
    intro y
    have hgpoint := hguniform'.tendsto_at t
    have hginner : Tendsto
        (fun n => inner ℝ ((u (phi₁ (phi₂ n))).toFun t) y) atTop
        (nhds (inner ℝ (g t) y)) := by
      simpa only [f, contRep_apply] using hgpoint.inner tendsto_const_nhds
    have hwinner := hweak ((evalAt (X := Y) t).adjoint y)
    have hulim : Tendsto
        (fun n => inner ℝ ((u (phi₁ (phi₂ n))).toFun t) y) atTop
        (nhds (inner ℝ (uLim.toFun t) y)) := by
      simpa only [ContinuousLinearMap.adjoint_inner_right, evalAt_apply] using hwinner
    exact tendsto_nhds_unique hginner hulim
  refine ⟨phi₁ ∘ phi₂, uLim, hphi₁.comp hphi₂, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hweak
  · have hgfun : (fun t : Icc (0 : ℝ) T => uLim.toFun t) = g :=
      funext fun t => (hgeq t).symm
    rw [hgfun]
    intro V hV
    have h := hguniform' V hV
    change ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) T,
      (g t, (u (phi₁ (phi₂ n))).toFun t) ∈ V
    change ∀ᶠ n in atTop, ∀ t : Icc (0 : ℝ) T,
      (g t, f (phi₁ (phi₂ n)) t) ∈ V at h
    simpa only [f, contRep_apply] using h

private theorem compact_subseq_fin_aux {m : ℕ} (T : Fin m → ℝ)
    (u : (i : Fin m) → ℕ → timeH1 Y (T i)) (C : Fin m → ℝ)
    (hu : ∀ i n, ‖u i n‖ ≤ C i) :
    ∃ (phi : ℕ → ℕ) (uLim : (i : Fin m) → timeH1 Y (T i)),
      StrictMono phi ∧
        (∀ i z, Tendsto (fun n => inner ℝ (u i (phi n)) z) atTop
          (nhds (inner ℝ (uLim i) z))) ∧
        (∀ i, TendstoUniformly
          (fun n (t : Icc (0 : ℝ) (T i)) => (u i (phi n)).toFun t)
          (fun t => (uLim i).toFun t) atTop) := by
  induction m with
  | zero =>
      refine ⟨id, fun i => Fin.elim0 i, fun _ _ h => h, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      let T₀ : Fin m → ℝ := fun i => T i.castSucc
      let u₀ : (i : Fin m) → ℕ → timeH1 Y (T₀ i) := fun i => u i.castSucc
      let C₀ : Fin m → ℝ := fun i => C i.castSucc
      have hu₀ : ∀ i n, ‖u₀ i n‖ ≤ C₀ i := fun i n => hu i.castSucc n
      obtain ⟨phi₀, uLim₀, hphi₀, hweak₀, huniform₀⟩ := ih T₀ u₀ C₀ hu₀
      let iLast : Fin (m + 1) := Fin.last m
      let uLast : ℕ → timeH1 Y (T iLast) := fun n => u iLast (phi₀ n)
      have huLast : ∀ n, ‖uLast n‖ ≤ C iLast := fun n => hu iLast (phi₀ n)
      obtain ⟨psi, uLimLast, hpsi, hweakLast, huniformLast⟩ :=
        compact_subseq uLast huLast
      let phi : ℕ → ℕ := phi₀ ∘ psi
      let uLim : (i : Fin (m + 1)) → timeH1 Y (T i) :=
        fun i => Fin.lastCases uLimLast (fun j => uLim₀ j) i
      refine ⟨phi, uLim, hphi₀.comp hpsi, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · intro z
          simpa only [phi, uLast, iLast, Function.comp_apply, uLim,
            Fin.lastCases_last] using hweakLast z
        · intro z
          have hz := (hweak₀ j z).comp hpsi.tendsto_atTop
          simpa only [phi, u₀, T₀, Function.comp_apply, Function.comp_def, uLim,
            Fin.lastCases_castSucc] using hz
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [phi, uLast, iLast, Function.comp_apply, uLim,
            Fin.lastCases_last] using huniformLast
        · intro V hV
          have hVevent := hpsi.tendsto_atTop.eventually (huniform₀ j V hV)
          simpa only [phi, u₀, T₀, Function.comp_apply, uLim,
            Fin.lastCases_castSucc] using hVevent

theorem compact_subseq_fin {m : ℕ} (T : Fin m → ℝ)
    (u : (i : Fin m) → ℕ → timeH1 Y (T i)) (C : Fin m → ℝ)
    (hu : ∀ i n, ‖u i n‖ ≤ C i) :
    ∃ (phi : ℕ → ℕ) (uLim : (i : Fin m) → timeH1 Y (T i)),
      StrictMono phi ∧
        (∀ i (z : timeL2 Y (T i)),
          Tendsto (fun n => inner ℝ (u i (phi n)).deriv z) atTop
            (nhds (inner ℝ (uLim i).deriv z))) ∧
        (∀ i, TendstoUniformly
          (fun n (t : Icc (0 : ℝ) (T i)) => (u i (phi n)).toFun t)
          (fun t => (uLim i).toFun t) atTop) := by
  obtain ⟨phi, uLim, hphi, hweak, huniform⟩ := compact_subseq_fin_aux T u C hu
  refine ⟨phi, uLim, hphi, ?_, huniform⟩
  intro i z
  have hz := hweak i (timeH1.mk 0 z)
  simpa only [timeH1.inner_def, initial_mk, deriv_mk, inner_zero_right, zero_add] using hz

end Hilbert

end timeH1

end TimeSobolev
end Parabolic
end Analysis
end DifferentialGeometry
