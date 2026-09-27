import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace DifferentialGeometry.Analysis.Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialPotential (omega : E → E →L[ℝ] ℝ) (x0 x : E) : ℝ :=
  ∫ t in (0 : ℝ)..1, omega (x0 + t • (x - x0)) (x - x0)

private def radialPotentialIntegrandFDeriv
    (omega : E → E →L[ℝ] ℝ) (x0 x : E) (t : ℝ) : E →L[ℝ] ℝ :=
  (omega (x0 + t • (x - x0))).comp (ContinuousLinearMap.id ℝ E) +
    ((fderiv ℝ omega (x0 + t • (x - x0))).comp
      (t • ContinuousLinearMap.id ℝ E)).flip (x - x0)

private theorem radialPotentialIntegrand_hasFDerivAt
    {omega : E → E →L[ℝ] ℝ}
    (x0 x : E) (t : ℝ) :
    DifferentiableAt ℝ omega (x0 + t • (x - x0)) →
    HasFDerivAt (fun y => omega (x0 + t • (y - x0)) (y - x0))
      (radialPotentialIntegrandFDeriv omega x0 x t) x := by
  intro homega
  have hinner : HasFDerivAt (fun y : E => x0 + t • (y - x0))
      (t • ContinuousLinearMap.id ℝ E) x := by
    convert (hasFDerivAt_id x).sub_const x0 |>.const_smul t |>.const_add x0 using 1
    ext v
    simp
  have houter : HasFDerivAt omega (fderiv ℝ omega (x0 + t • (x - x0)))
      (x0 + t • (x - x0)) := homega.hasFDerivAt
  have hc := houter.comp x hinner
  have hv : HasFDerivAt (fun y : E => y - x0) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  exact hc.clm_apply hv

private theorem radialPotentialIntegrandFDeriv_continuous
    {omega : E → E →L[ℝ] ℝ} {V : Set E} (hV : IsOpen V)
    (homega : ContDiffOn ℝ 1 omega V) (x0 x : E)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (x - x0) ∈ V) :
    ContinuousOn (fun t => radialPotentialIntegrandFDeriv omega x0 x t)
      (Set.Icc (0 : ℝ) 1) := by
  unfold radialPotentialIntegrandFDeriv
  have hline : Continuous fun t : ℝ => x0 + t • (x - x0) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hfd : ContinuousOn (fun t => fderiv ℝ omega (x0 + t • (x - x0)))
      (Set.Icc (0 : ℝ) 1) :=
    (homega.continuousOn_fderiv_of_isOpen hV le_rfl).comp hline.continuousOn hsegment
  have hcomp : ContinuousOn (fun t =>
      (fderiv ℝ omega (x0 + t • (x - x0))).comp
        (t • ContinuousLinearMap.id ℝ E)) (Set.Icc (0 : ℝ) 1) :=
    hfd.clm_comp (continuous_id.smul continuous_const).continuousOn
  have hflip : ContinuousOn (fun t =>
      ((fderiv ℝ omega (x0 + t • (x - x0))).comp
        (t • ContinuousLinearMap.id ℝ E)).flip) (Set.Icc (0 : ℝ) 1) :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).continuous.comp_continuousOn hcomp
  have homegaLine : ContinuousOn (fun t => omega (x0 + t • (x - x0)))
      (Set.Icc (0 : ℝ) 1) :=
    homega.continuousOn.comp hline.continuousOn hsegment
  exact (homegaLine.clm_comp continuousOn_const).add
    (hflip.clm_apply continuousOn_const)

theorem radialPotential_hasFDerivAt
    {omega : E → E →L[ℝ] ℝ} {V : Set E} (hV : IsOpen V)
    (homega : ContDiffOn ℝ 1 omega V) {x0 x : E}
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (x - x0) ∈ V)
    (hsymm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v w : E,
      fderiv ℝ omega (x0 + t • (x - x0)) v w =
        fderiv ℝ omega (x0 + t • (x - x0)) w v) :
    HasFDerivAt (radialPotential omega x0) (omega x) x := by
  let line : E × ℝ → E := fun p => x0 + p.2 • (p.1 - x0)
  have hline : ContDiff ℝ 1 line := by
    have hconst : ContDiff ℝ 1 (fun _p : E × ℝ => x0) := contDiff_const
    have hfst : ContDiff ℝ 1 (fun p : E × ℝ => p.1) := contDiff_fst
    have hsnd : ContDiff ℝ 1 (fun p : E × ℝ => p.2) := contDiff_snd
    exact hconst.add (hsnd.smul (hfst.sub hconst))
  have hopen : IsOpen (line ⁻¹' V) := hV.preimage hline.continuous
  have hslice : ({x} : Set E) ×ˢ Set.Icc (0 : ℝ) 1 ⊆ line ⁻¹' V := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    simp only [Set.mem_singleton_iff] at hy
    subst y
    exact hsegment t ht
  obtain ⟨U, S, hU, hS, hxU, hIS, hUS⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hslice
  let f : E → ℝ → ℝ := fun y t => omega (x0 + t • (y - x0)) (y - x0)
  have hf : ContDiffOn ℝ 1 (fun p : E × ℝ => f p.1 p.2) (U ×ˢ S) := by
    have hconst : ContDiff ℝ 1 (fun _p : E × ℝ => x0) := contDiff_const
    have hfst : ContDiff ℝ 1 (fun p : E × ℝ => p.1) := contDiff_fst
    have hdiff : ContDiff ℝ 1 (fun p : E × ℝ => p.1 - x0) := hfst.sub hconst
    have homegaComp : ContDiffOn ℝ 1 (omega ∘ line) (U ×ˢ S) :=
      homega.comp hline.contDiffOn hUS
    simpa only [f, line, Function.comp_apply] using homegaComp.clm_apply hdiff.contDiffOn
  have hmain := hasFDerivAt_paramInt f U hU 0 1 S hS
    (fun t ht => hIS (by simpa [Set.uIcc_of_le zero_le_one] using ht))
    x (hxU (Set.mem_singleton x)) hf
  have hderiv : (∫ t in (0 : ℝ)..1, fderiv ℝ (fun y : E => f y t) x) =
      ∫ t in (0 : ℝ)..1, radialPotentialIntegrandFDeriv omega x0 x t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    have homegaAt : DifferentiableAt ℝ omega (x0 + t • (x - x0)) :=
      (homega.contDiffAt (hV.mem_nhds (hsegment t htIcc))).differentiableAt one_ne_zero
    exact (radialPotentialIntegrand_hasFDerivAt x0 x t homegaAt).fderiv
  rw [hderiv] at hmain
  have hintegral :
      (∫ t in (0 : ℝ)..1, radialPotentialIntegrandFDeriv omega x0 x t) = omega x := by
    apply ContinuousLinearMap.ext
    intro v
    let instRealNorm : NormedAddCommGroup ℝ := Real.normedAddCommGroup
    let instRealSpace : NormedSpace ℝ ℝ := RCLike.toInnerProductSpaceReal.toNormedSpace
    have hradialCont :=
      radialPotentialIntegrandFDeriv_continuous hV homega x0 x hsegment
    have hradialCont' : ContinuousOn
        (fun t => radialPotentialIntegrandFDeriv omega x0 x t)
        (Set.uIcc (0 : ℝ) 1) := by
      simpa [Set.uIcc_of_le zero_le_one] using hradialCont
    rw [ContinuousLinearMap.intervalIntegral_apply hradialCont'.intervalIntegrable]
    let q : ℝ → ℝ := fun t => t • omega (x0 + t • (x - x0)) v
    have hcont : ContinuousOn (fun t => radialPotentialIntegrandFDeriv omega x0 x t v)
        (Set.uIcc (0 : ℝ) 1) :=
      hradialCont'.clm_apply continuousOn_const
    have hqraw (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
        @HasDerivAt ℝ _ ℝ instRealNorm.toAddCommGroup instRealSpace.toModule _ _ q
          (omega (x0 + t • (x - x0)) v +
            t • ((fderiv ℝ omega (x0 + t • (x - x0))) (x - x0)) v) t := by
      have hinner : HasDerivAt (fun s : ℝ => x0 + s • (x - x0)) (x - x0) t := by
        convert ((hasDerivAt_id t).smul_const (x - x0)).const_add x0 using 1 <;> simp
      have homegaAt : DifferentiableAt ℝ omega (x0 + t • (x - x0)) :=
        (homega.contDiffAt (hV.mem_nhds (hsegment t ht))).differentiableAt one_ne_zero
      have hmap := homegaAt.hasFDerivAt.comp_hasDerivAt t hinner
      have hvalue : HasDerivAt (fun s => omega (x0 + s • (x - x0)) v)
          (((fderiv ℝ omega (x0 + t • (x - x0))) (x - x0)) v) t := by
        simpa using hmap.clm_apply (hasDerivAt_const t v)
      convert (hasDerivAt_id t).smul hvalue using 1
      · ext s
        rfl
      · simp only [id_eq, one_smul, add_comm]
    have hqderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        @HasDerivAt ℝ _ ℝ instRealNorm.toAddCommGroup instRealSpace.toModule _ _ q
          (radialPotentialIntegrandFDeriv omega x0 x t v) t := by
      intro t ht
      convert hqraw t ht using 1
      simp only [radialPotentialIntegrandFDeriv, add_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.flip_apply, smul_apply, map_smul,
        hsymm t ht v (x - x0)]
    have hmem (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le zero_le_one] using ht
    have hftc : (∫ t in (0 : ℝ)..1, radialPotentialIntegrandFDeriv omega x0 x t v) =
        q 1 - q 0 := by
      apply @intervalIntegral.integral_eq_sub_of_hasDerivAt ℝ instRealNorm instRealSpace
      · intro t ht
        exact hqderiv t (hmem t ht)
      · exact hcont.intervalIntegrable
    rw [hftc]
    simp [q]
  rw [hintegral] at hmain
  exact hmain

end DifferentialGeometry.Analysis.Calculus
