import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Quadratic.L1Regularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

def timeNlinPot (V : ℝ → X → ℝ) (u : timeH1 X T) : ℝ :=
  ∫ t in (0 : ℝ)..T, V t (u.toFun t)

def timeNlinAction
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (V : ℝ → X → ℝ) (u : timeH1 X T) : ℝ :=
  timeQuad A hA C hC u.deriv + timeNlinPot V u

noncomputable def coeffForce
    (DB : X →L[ℝ] (X →L[ℝ] X)) (p : X) : X :=
  (InnerProductSpace.toDual ℝ X).symm
    ((innerSL ℝ p).comp ((ContinuousLinearMap.apply ℝ X p).comp DB))

theorem coeffForce_apply
    (DB : X →L[ℝ] (X →L[ℝ] X)) (p w : X) :
    inner ℝ (coeffForce DB p) w = inner ℝ ((DB w) p) p := by
  have h := congrArg (fun L : X →L[ℝ] ℝ ↦ L w)
    ((InnerProductSpace.toDual ℝ X).apply_symm_apply
      ((innerSL ℝ p).comp ((ContinuousLinearMap.apply ℝ X p).comp DB)))
  simpa only [coeffForce, InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    innerSL_apply_apply, real_inner_comm] using h

def timeCoeffAction
    (B : ℝ → X → X →L[ℝ] X) (u : timeH1 X T) : ℝ :=
  ∫ t in (0 : ℝ)..T,
    inner ℝ (B t (u.toFun t) (u.deriv t)) (u.deriv t)

def coeffLineLag
    (B : ℝ → X → X →L[ℝ] X) (u v : timeH1 X T)
    (c t : ℝ) : ℝ :=
  inner ℝ
    (B t (u.toFun t + c • v.toFun t) (u.deriv t + c • v.deriv t))
    (u.deriv t + c • v.deriv t)

def coeffLineDeriv
    (B : ℝ → X → X →L[ℝ] X)
    (DB : ℝ → X → X →L[ℝ] (X →L[ℝ] X))
    (u v : timeH1 X T) (c t : ℝ) : ℝ :=
  inner ℝ
      (coeffForce (DB t (u.toFun t + c • v.toFun t))
        (u.deriv t + c • v.deriv t))
      (v.toFun t) +
    2 * inner ℝ
      (B t (u.toFun t + c • v.toFun t)
        (u.deriv t + c • v.deriv t))
      (v.deriv t)

theorem coeffQuad_line
    (B : X → X →L[ℝ] X)
    (DB : X → X →L[ℝ] (X →L[ℝ] X))
    (hB : ∀ x, HasFDerivAt B (DB x) x)
    (hself : ∀ x, IsSelfAdjoint (B x))
    (x p w q : X) (c : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦
        inner ℝ (B (x + z • w) (p + z • q)) (p + z • q))
      (inner ℝ (((DB (x + c • w)) w) (p + c • q)) (p + c • q) +
        2 * inner ℝ (B (x + c • w) (p + c • q)) q) c := by
  let xc : ℝ → X := fun z ↦ x + z • w
  let pc : ℝ → X := fun z ↦ p + z • q
  have hxc : HasDerivAt xc w c := by
    simpa only [xc, id_eq, one_smul] using
      ((hasDerivAt_id c).smul_const w).const_add x
  have hpc : HasDerivAt pc q c := by
    simpa only [pc, id_eq, one_smul] using
      ((hasDerivAt_id c).smul_const q).const_add p
  have hBc : HasDerivAt (fun z ↦ B (xc z)) ((DB (xc c)) w) c :=
    (hB (xc c)).comp_hasDerivAt c hxc
  have hBpc : HasDerivAt (fun z ↦ B (xc z) (pc z))
      (((DB (xc c)) w) (pc c) + B (xc c) q) c :=
    hBc.clm_apply hpc
  have hinner := hBpc.inner ℝ hpc
  have hsym : inner ℝ (B (xc c) q) (pc c) =
      inner ℝ (B (xc c) (pc c)) q := by
    calc
      inner ℝ (B (xc c) q) (pc c) =
          inner ℝ (pc c) (B (xc c) q) := real_inner_comm _ _
      _ = inner ℝ (B (xc c) (pc c)) q :=
        (hself (xc c)).isSymmetric (pc c) q |>.symm
  simpa only [xc, pc, inner_add_left, hsym, two_mul, add_assoc, add_comm,
    add_left_comm] using hinner

theorem timeCoeff_line
    (hT : 0 ≤ T)
    (B : ℝ → X → X →L[ℝ] X)
    (DB : ℝ → X → X →L[ℝ] (X →L[ℝ] X))
    (hB : ∀ t x, HasFDerivAt (B t) (DB t x) x)
    (hself : ∀ t x, IsSelfAdjoint (B t x))
    (u v : timeH1 X T)
    (bound : ℝ → ℝ)
    (hmeas : ∀ᶠ c in nhds (0 : ℝ),
      AEStronglyMeasurable (coeffLineLag B u v c)
        (volume.restrict (uIoc (0 : ℝ) T)))
    (hint : IntervalIntegrable (coeffLineLag B u v 0) volume 0 T)
    (hdmeas : AEStronglyMeasurable (coeffLineDeriv B DB u v 0)
      (volume.restrict (uIoc (0 : ℝ) T)))
    (hbound : ∀ᵐ t ∂volume, t ∈ uIoc (0 : ℝ) T →
      ∀ c ∈ Icc (-1 : ℝ) 1, ‖coeffLineDeriv B DB u v c t‖ ≤ bound t)
    (hboundInt : IntervalIntegrable bound volume 0 T) :
    IntervalIntegrable (coeffLineDeriv B DB u v 0) volume 0 T ∧
      HasDerivAt (fun c : ℝ ↦ timeCoeffAction B (u + c • v))
        (∫ t in (0 : ℝ)..T, coeffLineDeriv B DB u v 0 t) 0 := by
  have hslice (c t : ℝ) :
      HasDerivAt (fun z : ℝ ↦ coeffLineLag B u v z t)
        (coeffLineDeriv B DB u v c t) c := by
    have h := coeffQuad_line (B t) (DB t) (hB t) (hself t)
      (u.toFun t) (u.deriv t) (v.toFun t) (v.deriv t) c
    simpa only [coeffLineLag, coeffLineDeriv, coeffForce_apply] using h
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := coeffLineLag B u v) (F' := coeffLineDeriv B DB u v)
      (x₀ := (0 : ℝ)) (μ := volume) (s := Icc (-1 : ℝ) 1)
      (a := (0 : ℝ)) (b := T) (bound := bound)
      (Icc_mem_nhds (by norm_num) (by norm_num)) hmeas hint hdmeas hbound
      hboundInt (Eventually.of_forall fun t _ c _ ↦ hslice c t)
  refine ⟨hparam.1, ?_⟩
  have hlineEq (c : ℝ) : timeCoeffAction B (u + c • v) =
      ∫ t in (0 : ℝ)..T, coeffLineLag B u v c t := by
    unfold timeCoeffAction
    have hderiv : ⇑((u + c • v).deriv) =ᵐ[timeMeasure T]
        fun t ↦ u.deriv t + c • v.deriv t := by
      have hdadd : (u + c • v).deriv = u.deriv + (c • v).deriv :=
        timeH1.deriv_add u (c • v)
      have hdsmul : (c • v).deriv = c • v.deriv :=
        timeH1.deriv_smul c v
      rw [hdadd, hdsmul]
      filter_upwards [Lp.coeFn_add u.deriv (c • v.deriv),
        Lp.coeFn_smul c v.deriv] with t hadd hsmul
      calc
        (u.deriv + c • v.deriv) t = u.deriv t + (c • v.deriv) t := by
          simpa only [Pi.add_apply] using hadd
        _ = u.deriv t + c • v.deriv t := by
          exact congrArg (fun z ↦ u.deriv t + z)
            (by simpa only [Pi.smul_apply] using hsmul)
    have hderiv' : ⇑((u + c • v).deriv) =ᵐ[volume.restrict (uIoc (0 : ℝ) T)]
        fun t ↦ u.deriv t + c • v.deriv t := by
      have hsub : uIoc (0 : ℝ) T ⊆ Icc (0 : ℝ) T :=
        by simpa only [uIcc_of_le hT] using
          (uIoc_subset_uIcc : uIoc (0 : ℝ) T ⊆ uIcc (0 : ℝ) T)
      have hm := hderiv.filter_mono
        (ae_mono (Measure.restrict_mono hsub le_rfl))
      simpa only [timeMeasure] using hm
    apply intervalIntegral.integral_congr_ae_restrict
    filter_upwards [hderiv', ae_restrict_mem measurableSet_uIoc] with t hd ht
    have ht' : t ∈ Icc (0 : ℝ) T :=
      by simpa only [uIcc_of_le hT] using uIoc_subset_uIcc ht
    change inner ℝ (B t ((u + c • v).toFun t) ((u + c • v).deriv t))
      ((u + c • v).deriv t) = coeffLineLag B u v c t
    rw [timeH1.toFun_add u (c • v) ht',
      timeH1.toFun_smul c v ht', hd]
    rfl
  exact hparam.2.congr_of_eventuallyEq (Eventually.of_forall hlineEq)

omit [CompleteSpace X] in
theorem timeNlinPot_line
    (hT : 0 ≤ T)
    (V : ℝ → X → ℝ) (G : ℝ → X → X)
    (hVcont : Continuous (fun p : ℝ × X ↦ V p.1 p.2))
    (hGcont : Continuous (fun p : ℝ × X ↦ G p.1 p.2))
    (hgrad : ∀ t x, HasFDerivAt (V t) (innerSL ℝ (G t x)) x)
    (u v : timeH1 X T) :
    HasDerivAt (fun c : ℝ ↦ timeNlinPot V (u + c • v))
      (∫ t in (0 : ℝ)..T, inner ℝ (G t (u.toFun t)) (v.toFun t)) 0 := by
  let lag : ℝ → ℝ → ℝ := fun c t ↦
    V t (u.toFun t + c • v.toFun t)
  let dLag : ℝ → ℝ → ℝ := fun c t ↦
    inner ℝ (G t (u.toFun t + c • v.toFun t)) (v.toFun t)
  have hu : ContinuousOn u.toFun (Icc (0 : ℝ) T) :=
    u.continuousOn_toFun
  have hv : ContinuousOn v.toFun (Icc (0 : ℝ) T) :=
    v.continuousOn_toFun
  have hlagCont (c : ℝ) : ContinuousOn (lag c) (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT]
    apply hVcont.continuousOn.comp
      (continuousOn_id.prodMk (hu.add (continuousOn_const.smul hv)))
    exact Set.mapsTo_univ _ _
  have hdCont (c : ℝ) : ContinuousOn (dLag c) (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT]
    have hGc : ContinuousOn
        (fun t ↦ G t (u.toFun t + c • v.toFun t)) (Icc (0 : ℝ) T) := by
      apply hGcont.continuousOn.comp
        (continuousOn_id.prodMk (hu.add (continuousOn_const.smul hv)))
      exact Set.mapsTo_univ _ _
    exact hGc.inner hv
  have hslice (c t : ℝ) : HasDerivAt (fun z : ℝ ↦ lag z t) (dLag c t) c := by
    have hline : HasDerivAt (fun z : ℝ ↦ u.toFun t + z • v.toFun t)
        (v.toFun t) c := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id c).smul_const (v.toFun t)).const_add (u.toFun t)
    simpa only [lag, dLag, Function.comp_def, innerSL_apply_apply] using
      (hgrad t (u.toFun t + c • v.toFun t)).comp_hasDerivAt c hline
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ uIcc (0 : ℝ) T
  have hdJoint : ContinuousOn (fun p : ℝ × ℝ ↦ dLag p.1 p.2) K := by
    have hu' : ContinuousOn (fun p : ℝ × ℝ ↦ u.toFun p.2) K :=
      hu.comp continuousOn_snd (fun p hp ↦ by
        simpa only [uIcc_of_le hT] using hp.2)
    have hv' : ContinuousOn (fun p : ℝ × ℝ ↦ v.toFun p.2) K :=
      hv.comp continuousOn_snd (fun p hp ↦ by
        simpa only [uIcc_of_le hT] using hp.2)
    have hG' : ContinuousOn
        (fun p : ℝ × ℝ ↦
          G p.2 (u.toFun p.2 + p.1 • v.toFun p.2)) K := by
      apply hGcont.continuousOn.comp
        (continuousOn_snd.prodMk (hu'.add (continuousOn_fst.smul hv')))
      exact Set.mapsTo_univ _ _
    exact hG'.inner hv'
  have hKcompact : IsCompact K := isCompact_Icc.prod isCompact_uIcc
  obtain ⟨C₀, hC₀⟩ := hKcompact.bddAbove_image hdJoint.norm
  let B : ℝ := max C₀ 0
  have hB : ∀ p ∈ K, ‖dLag p.1 p.2‖ ≤ B := by
    intro p hp
    exact (hC₀ ⟨p, hp, rfl⟩).trans (le_max_left C₀ 0)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := lag) (F' := dLag) (x₀ := (0 : ℝ)) (μ := volume)
      (s := Icc (-1 : ℝ) 1) (a := (0 : ℝ)) (b := T)
      (bound := fun _ : ℝ ↦ B)
      (Icc_mem_nhds (by norm_num) (by norm_num))
      (Eventually.of_forall fun c ↦
        ((hlagCont c).mono uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc)
      ((hlagCont 0).intervalIntegrable)
      (((hdCont 0).mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc)
      (Eventually.of_forall fun t ht c hc ↦
        hB (c, t) ⟨hc, uIoc_subset_uIcc ht⟩)
      continuousOn_const.intervalIntegrable
      (Eventually.of_forall fun t _ c _ ↦ hslice c t)
  have hlineEq (c : ℝ) : timeNlinPot V (u + c • v) = ∫ t in (0 : ℝ)..T, lag c t := by
    unfold timeNlinPot
    apply intervalIntegral.integral_congr
    intro t ht
    change V t ((u + c • v).toFun t) = lag c t
    rw [timeH1.toFun_add u (c • v) (by simpa only [uIcc_of_le hT] using ht),
      timeH1.toFun_smul c v (by simpa only [uIcc_of_le hT] using ht)]
  with_unfolding_all
    simpa only [dLag, zero_smul, add_zero] using
      hparam.2.congr_of_eventuallyEq (Eventually.of_forall fun c ↦ hlineEq c)

theorem timeNlin_euler
    (hT : 0 < T)
    (A : ℝ → X →L[ℝ] X)
    (hA : AEStronglyMeasurable A (timeMeasure T))
    (C : NNReal)
    (hC : ∀ᵐ t ∂timeMeasure T, ‖A t‖ ≤ (C : ℝ))
    (hself : ∀ᵐ t ∂timeMeasure T, IsSelfAdjoint (A t))
    (V : ℝ → X → ℝ) (G : ℝ → X → X)
    (hVcont : Continuous (fun p : ℝ × X ↦ V p.1 p.2))
    (hGcont : Continuous (fun p : ℝ × X ↦ G p.1 p.2))
    (hgrad : ∀ t x, HasFDerivAt (V t) (innerSL ℝ (G t x)) x)
    (u : timeH1 X T)
    (hmin : IsLocalMinOn (timeNlinAction A hA C hC V)
      (sameTimeEnds u) u) :
    let F : ℝ → X := fun t ↦ G t (u.toFun t)
    IntegrableOn F (Icc (0 : ℝ) T) volume ∧
      ∀ v : timeH1 X T, v.init = 0 → v.toFun T = 0 →
        2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
          ∫ t in Icc (0 : ℝ) T, inner ℝ (F t) (v.toFun t) = 0 := by
  dsimp only
  have hu : ContinuousOn u.toFun (Icc (0 : ℝ) T) :=
    u.continuousOn_toFun
  have hFcont : ContinuousOn (fun t ↦ G t (u.toFun t)) (Icc (0 : ℝ) T) := by
    apply hGcont.continuousOn.comp (continuousOn_id.prodMk hu)
    exact Set.mapsTo_univ _ _
  refine ⟨hFcont.integrableOn_Icc, ?_⟩
  intro v hv0 hvT
  let line : ℝ → timeH1 X T := fun c ↦ u + c • v
  have hline0 : line 0 = u := by simp only [line, zero_smul, add_zero]
  have hmaps : univ ⊆ line ⁻¹' sameTimeEnds u := by
    intro c _
    constructor
    · simp only [line, timeH1.init_add, timeH1.init_smul, hv0, smul_zero, add_zero]
    · change (u + c • v).toFun T = u.toFun T
      rw [timeH1.toFun_add u (c • v) ⟨hT.le, le_rfl⟩,
        timeH1.toFun_smul c v ⟨hT.le, le_rfl⟩, hvT, smul_zero, add_zero]
  have hscalar : IsLocalMin (timeNlinAction A hA C hC V ∘ line) 0 := by
    rw [← isLocalMinOn_univ_iff]
    have hmin' : IsLocalMinOn (timeNlinAction A hA C hC V)
        (sameTimeEnds u) (line 0) := by
      simpa only [hline0] using hmin
    exact hmin'.comp_continuousOn hmaps
      (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
      (mem_univ (0 : ℝ))
  have hkin : HasDerivAt
      (fun c : ℝ ↦ timeQuad A hA C hC ((line c).deriv))
      (2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv) 0 := by
    simpa only [line, timeH1.deriv_add, timeH1.deriv_smul] using
      timeQuad_line A hA C hC hself u.deriv v.deriv
  have hpot := timeNlinPot_line hT.le V G hVcont hGcont hgrad u v
  have henergy : _root_.deriv (timeNlinAction A hA C hC V ∘ line) 0 =
      2 * inner ℝ (timeOp A hA C hC u.deriv) v.deriv +
        ∫ t in (0 : ℝ)..T,
          inner ℝ (G t (u.toFun t)) (v.toFun t) := by
    have hfun : timeNlinAction A hA C hC V ∘ line =
        (fun c : ℝ => timeQuad A hA C hC ((line c).deriv)) +
          fun c : ℝ => timeNlinPot V (u + c • v) := by
      funext c
      rfl
    rw [hfun]
    exact (hkin.add hpot).deriv
  have hzero := hscalar.deriv_eq_zero
  rw [henergy] at hzero
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  exact hzero

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
