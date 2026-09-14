import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Analysis.ODE.Gronwall.Integral
import DifferentialGeometry.Analysis.Calculus.Derivative.ParametricIntervalIntegral
import DifferentialGeometry.Analysis.Calculus.TimeJet.PartialDerivatives
import DifferentialGeometry.Analysis.Integration.IntervalGreenIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]
variable [hBoundary : I.Boundaryless] {D : RealTimeInterval} {a b s u : ℝ}
include hBoundary


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem continuousOn_integral_of_continuousOn {F : ℝ → ℝ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) ((univ : Set ℝ) ×ˢ Icc s u)) :
    ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..1, F x t) (Icc s u) := by
  intro t₀ ht₀
  refine DifferentialGeometry.Analysis.Calculus.continuousWithinAt_paramIntervalIntegral
    isCompact_Icc ?_ ht₀
  exact hF.comp (ContinuousOn.prodMk continuousOn_snd continuousOn_fst)
    (fun p hp => ⟨mem_univ _, hp.1⟩)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem contDiffOn_derivWithin_snd {s u : ℝ} (hsu : s < u) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc s u)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => derivWithin (fun τ => F p.1 τ) (Icc s u) p.2)
      (univ ×ˢ Icc s u) := by
  intro p hp
  exact DifferentialGeometry.Analysis.contDiffWithinAt_derivWithin_snd
    (uniqueDiffOn_Icc hsu) hp (hF p hp) (by simp)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem contDiffOn_paramIntervalIntegral_Icc {s u : ℝ} (hsu : s < u) {F : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc s u)) :
    ContDiffOn ℝ ∞ (fun τ : ℝ => ∫ x in (0 : ℝ)..1, F x τ) (Icc s u) := by
  have hS : UniqueDiffOn ℝ (Icc s u) := uniqueDiffOn_Icc hsu
  have key : ∀ k : ℕ, ∀ {F : ℝ → ℝ → ℝ},
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (univ ×ˢ Icc s u) →
      ContDiffOn ℝ (k : ℕ∞ω) (fun τ : ℝ => ∫ x in (0 : ℝ)..1, F x τ) (Icc s u) := by
    intro k
    induction k with
    | zero =>
      intro F hF
      refine contDiffOn_zero.mpr ?_
      intro t₀ ht₀
      refine DifferentialGeometry.Analysis.Calculus.continuousWithinAt_paramIntervalIntegral
        isCompact_Icc ?_ ht₀
      exact hF.continuousOn.comp
        (ContinuousOn.prodMk continuousOn_snd continuousOn_fst)
        (fun p hp => ⟨mem_univ _, hp.1⟩)
    | succ k ih =>
      intro F hF
      have hG : ContDiffOn ℝ ∞
          (fun p : ℝ × ℝ => derivWithin (fun τ => F p.1 τ) (Icc s u) p.2)
          (univ ×ˢ Icc s u) := contDiffOn_derivWithin_snd hsu hF
      have hderiv : ∀ x t, t ∈ Icc s u →
          HasDerivWithinAt (fun τ => F x τ)
            (derivWithin (fun τ => F x τ) (Icc s u) t) (Icc s u) t := by
        intro x t ht
        have hx : ContDiffWithinAt ℝ ∞ (fun τ : ℝ => F x τ) (Icc s u) t := by
          have harg : ContDiffWithinAt ℝ ∞ (fun τ : ℝ => (x, τ)) (Icc s u) t :=
            contDiffWithinAt_const.prodMk contDiffWithinAt_id
          exact (hF.contDiffWithinAt ⟨mem_univ x, ht⟩).comp t harg
            (fun τ hτ => ⟨mem_univ x, hτ⟩)
        exact (hx.differentiableWithinAt (by norm_num)).hasDerivWithinAt
      have hmain := DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_paramIntervalIntegral
        hF.continuousOn hG.continuousOn hderiv
      rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin hS]
      refine ⟨fun t ht => (hmain t ht).differentiableWithinAt, ?_, ?_⟩
      · intro hk
        exact absurd hk (by simp)
      · refine (ih (F := fun x τ => derivWithin (fun r => F x r) (Icc s u) τ) hG).congr
          (fun t ht => ?_)
        exact (hmain t ht).derivWithin (hS t ht)
  rw [contDiffOn_iff_forall_nat_le]
  intro m _
  exact key m hF


private theorem ricciTangent_ge_neg (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x τ : ℝ) (hτ : τ ∈ Icc s u) :
    -B.B₀ ≤ c.ricciTangent B.family x τ := by
  have htt : (B.family.metric τ).inner (c.lift x τ)
      (c.unitTangent B.family.metric x τ) (c.unitTangent B.family.metric x τ) = 1 :=
    (tangent_curvature_geometry B.family.metric c (Icc s u) hc.smooth hc.immersed x τ hτ).1
  have h := ricci_pair_ge B τ (hwindow hτ) (c.unitTangent B.family.metric x τ)
  rw [htt, mul_one] at h
  simpa only [CurveMap.ricciTangent] using h

private theorem ricciTangent_integral_ge (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (v : ℝ) (hv : v ∈ Icc s u) :
    -B.B₀ * c.length B.family.metric v ≤
      c.integral B.family.metric (c.ricciTangent B.family) v := by
  have hv' : Continuous fun x : ℝ => c.speed B.family.metric x v :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv).continuous
  have hr' : Continuous fun x : ℝ => c.ricciTangent B.family x v := by
    have h := (CurveMap.ricciTangent_continuousOn B hwindow c hc).comp
      (s := (univ : Set ℝ))
      (continuous_id.prodMk continuous_const).continuousOn (fun x _ => ⟨mem_univ x, hv⟩)
    exact continuousOn_univ.mp h
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x : ℝ => -B.B₀ * c.speed B.family.metric x v)
    (g := fun x : ℝ => c.ricciTangent B.family x v * c.speed B.family.metric x v)
    ((continuous_const.mul hv').intervalIntegrable 0 1) ((hr'.mul hv').intervalIntegrable 0 1)
    (fun x _ => mul_le_mul_of_nonneg_right
      (ricciTangent_ge_neg B hwindow c hc x v hv) (c.speed_nonneg B.family.metric x v))
  have hleft : (∫ x in (0 : ℝ)..1, -B.B₀ * c.speed B.family.metric x v) =
      -B.B₀ * c.length B.family.metric v := by
    rw [intervalIntegral.integral_const_mul]
    simp only [CurveMap.length, CurveMap.integral, one_mul]
  have hright : (∫ x in (0 : ℝ)..1, c.ricciTangent B.family x v *
      c.speed B.family.metric x v) = c.integral B.family.metric (c.ricciTangent B.family) v := rfl
  rw [hleft, hright] at hmono
  exact hmono

omit [SigmaCompactSpace M] hBoundary in
private theorem contDiffOn_length (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContDiffOn ℝ ∞ (c.length B.family.metric) (Icc s u) := by
  have h := contDiffOn_paramIntervalIntegral_Icc hsu (F := fun x t => c.speed B.family.metric x t)
    (CurveMap.Field.smoothOn_speed B.family.metric B.smooth
      (fun _ hr => B.regular (hwindow hr)) c hc.smooth hc.immersed)
  refine h.congr (fun t _ => ?_)
  simp only [CurveMap.length, CurveMap.integral, one_mul]

omit [SigmaCompactSpace M] in
private theorem joint_continuousOn_curvature (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContinuousOn (fun p : ℝ × ℝ => c.curvature B.family.metric p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
  (Real.continuous_sqrt.comp_continuousOn
    (CurveMap.Field.smoothOn_curvatureSq B.family.metric B.smooth
      (fun _ hr => B.regular (hwindow hr)) (uniqueDiffOn_Icc hsu) c hc.smooth
      hc.immersed).continuousOn)

omit [SigmaCompactSpace M] hBoundary in
private theorem joint_continuousOn_speed (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContinuousOn (fun p : ℝ × ℝ => c.speed B.family.metric p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
  (CurveMap.Field.smoothOn_speed B.family.metric B.smooth
    (fun _ hr => B.regular (hwindow hr)) c hc.smooth hc.immersed).continuousOn

omit [SigmaCompactSpace M] in
private theorem continuousOn_totalCurvature (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContinuousOn (c.totalCurvature B.family.metric) (Icc s u) := by
  have hjoin : ContinuousOn (fun p : ℝ × ℝ =>
      c.curvature B.family.metric p.1 p.2 * c.speed B.family.metric p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
    (joint_continuousOn_curvature B hsu hwindow c hc).mul
      (joint_continuousOn_speed B hwindow c hc)
  have h := continuousOn_integral_of_continuousOn
    (F := fun x t => c.curvature B.family.metric x t * c.speed B.family.metric x t) hjoin
  refine h.congr (fun t _ => ?_)
  simp only [CurveMap.totalCurvature, CurveMap.integral]

omit [SigmaCompactSpace M] in
private theorem continuousOn_energy (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContinuousOn (c.energy B.family.metric) (Icc s u) := by
  have hjoin : ContinuousOn (fun p : ℝ × ℝ =>
      c.curvatureSq B.family.metric p.1 p.2 * c.speed B.family.metric p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
    (CurveMap.Field.smoothOn_curvatureSq B.family.metric B.smooth
      (fun _ hr => B.regular (hwindow hr)) (uniqueDiffOn_Icc hsu) c hc.smooth
      hc.immersed).continuousOn.mul (joint_continuousOn_speed B hwindow c hc)
  have h := continuousOn_integral_of_continuousOn
    (F := fun x t => c.curvatureSq B.family.metric x t * c.speed B.family.metric x t) hjoin
  refine h.congr (fun t _ => ?_)
  simp only [CurveMap.energy, CurveMap.integral]

omit [SigmaCompactSpace M] hBoundary in
private theorem continuousOn_ricciTangent_integral (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContinuousOn (c.integral B.family.metric (c.ricciTangent B.family)) (Icc s u) := by
  have hjoin : ContinuousOn (fun p : ℝ × ℝ =>
      c.ricciTangent B.family p.1 p.2 * c.speed B.family.metric p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
    (CurveMap.ricciTangent_continuousOn B hwindow c hc).mul
      (joint_continuousOn_speed B hwindow c hc)
  exact continuousOn_integral_of_continuousOn
    (F := fun x t => c.ricciTangent B.family x t * c.speed B.family.metric x t) hjoin

private theorem length_hasDerivWithinAt (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (t : ℝ) (ht : t ∈ Icc s u) :
    HasDerivWithinAt (c.length B.family.metric)
      (-c.energy B.family.metric t -
        c.integral B.family.metric (c.ricciTangent B.family) t) (Icc s u) t := by
  have hsp := CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
    (CurveMap.pairingEvolution B hsu hwindow c hc)
  have hv := joint_continuousOn_speed B hwindow c hc
  have hq := CurveMap.q_continuousOn B hsu hwindow c hc
  have hmain := DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_paramIntervalIntegral
    hv (hq.neg.mul hv) (fun x τ hτ => hsp x τ hτ)
  have hfun : c.length B.family.metric =
      fun τ : ℝ => ∫ x in (0 : ℝ)..1, c.speed B.family.metric x τ := by
    funext τ
    simp only [CurveMap.length, CurveMap.integral, one_mul]
  rw [hfun]
  refine (hmain t ht).congr_deriv ?_
  have hκ : Continuous fun x : ℝ => c.curvatureSq B.family.metric x t :=
    (c.curvatureSq_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed
      t ht).continuous
  have hv' : Continuous fun x : ℝ => c.speed B.family.metric x t :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed
      t ht).continuous
  have hric : Continuous fun x : ℝ => c.ricciTangent B.family x t := by
    have h := (CurveMap.ricciTangent_continuousOn B hwindow c hc).comp
      (s := (univ : Set ℝ))
      (continuous_id.prodMk continuous_const).continuousOn (fun x _ => ⟨mem_univ x, ht⟩)
    exact continuousOn_univ.mp h
  have hsplit : ∀ x : ℝ, -(c.q B.family x t) * c.speed B.family.metric x t =
      -((c.curvatureSq B.family.metric x t + c.ricciTangent B.family x t) *
        c.speed B.family.metric x t) := by
    intro x
    simp only [CurveMap.q]
    ring
  have hsplit2 : ∀ x : ℝ,
      (c.curvatureSq B.family.metric x t + c.ricciTangent B.family x t) *
        c.speed B.family.metric x t =
      c.curvatureSq B.family.metric x t * c.speed B.family.metric x t +
        c.ricciTangent B.family x t * c.speed B.family.metric x t := by
    intro x
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hsplit x), intervalIntegral.integral_neg]
  rw [intervalIntegral.integral_congr (fun x _ => hsplit2 x)]
  rw [intervalIntegral.integral_add
    (f := fun x : ℝ => c.curvatureSq B.family.metric x t * c.speed B.family.metric x t)
    (g := fun x : ℝ => c.ricciTangent B.family x t * c.speed B.family.metric x t)
    ((hκ.mul hv').intervalIntegrable 0 1) ((hric.mul hv').intervalIntegrable 0 1)]
  simp only [CurveMap.energy, CurveMap.integral]
  ring

private theorem derivWithin_length (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (t : ℝ) (ht : t ∈ Icc s u) :
    derivWithin (c.length B.family.metric) (Icc s u) t =
      -c.energy B.family.metric t -
        c.integral B.family.metric (c.ricciTangent B.family) t :=
  (length_hasDerivWithinAt B hsu hwindow c hc t ht).derivWithin
    ((uniqueDiffOn_Icc hsu) t ht)

private theorem speed_le_exp_mul (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (x r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    c.speed B.family.metric x t ≤ Real.exp (B.B₀ * (t - r)) * c.speed B.family.metric x r := by
  have hsp := CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
    (CurveMap.pairingEvolution B hsu hwindow c hc)
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  have hcont' : ContinuousOn
      (fun τ => c.speed B.family.metric x τ * Real.exp (-B.B₀ * (τ - r))) (Icc s u) := by
    refine ContinuousOn.mul ?_ ?_
    · exact fun τ hτ => (hsp x τ hτ).continuousWithinAt
    · exact Real.continuous_exp.comp_continuousOn
        ((continuousOn_id.sub continuousOn_const).const_mul (-B.B₀))
  have hcont : ContinuousOn
      (fun τ => c.speed B.family.metric x τ * Real.exp (-B.B₀ * (τ - r))) (Icc r t) :=
    hcont'.mono hsub
  have hderiv : ∀ τ ∈ interior (Icc r t),
      deriv (fun σ => c.speed B.family.metric x σ * Real.exp (-B.B₀ * (σ - r))) τ ≤ 0 := by
    intro τ hτ
    rw [interior_Icc] at hτ
    have hτI : τ ∈ Icc s u := hsub ⟨hτ.1.le, hτ.2.le⟩
    have h1 : HasDerivAt (fun σ => c.speed B.family.metric x σ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp x τ hτI).hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt hr.1 hτ.1)
        (lt_of_lt_of_le hτ.2 ht.2))
    have h2 : HasDerivAt (fun σ => Real.exp (-B.B₀ * (σ - r)))
        (Real.exp (-B.B₀ * (τ - r)) * (-B.B₀)) τ := by
      have h3 : HasDerivAt (fun σ : ℝ => -B.B₀ * (σ - r)) (-B.B₀) τ := by
        simpa using ((hasDerivAt_id τ).sub_const r).const_mul (-B.B₀)
      simpa using h3.exp
    have hdv : deriv (fun σ => c.speed B.family.metric x σ * Real.exp (-B.B₀ * (σ - r))) τ =
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) * Real.exp (-B.B₀ * (τ - r)) +
          c.speed B.family.metric x τ * (Real.exp (-B.B₀ * (τ - r)) * (-B.B₀)) :=
      (h1.mul h2).deriv
    rw [hdv]
    have hvnn : 0 ≤ c.speed B.family.metric x τ := c.speed_nonneg B.family.metric x τ
    have hexp : 0 < Real.exp (-B.B₀ * (τ - r)) := Real.exp_pos _
    have hq : -B.B₀ ≤ c.q B.family x τ := by
      have h := ricciTangent_ge_neg B hwindow c hc x τ hτI
      have h2' : 0 ≤ c.curvatureSq B.family.metric x τ := by
        rw [← CurveMap.curvature_sq c B.family.metric x τ]
        exact sq_nonneg _
      simp only [CurveMap.q]
      linarith
    have hfac : (-(c.q B.family x τ) * c.speed B.family.metric x τ) *
          Real.exp (-B.B₀ * (τ - r)) +
        c.speed B.family.metric x τ * (Real.exp (-B.B₀ * (τ - r)) * (-B.B₀))
        = -(Real.exp (-B.B₀ * (τ - r)) *
            (c.speed B.family.metric x τ * (c.q B.family x τ + B.B₀))) := by ring
    rw [hfac]
    nlinarith [hexp, mul_nonneg hvnn (by linarith : (0:ℝ) ≤ c.q B.family x τ + B.B₀)]
  have hdiff : DifferentiableOn ℝ
      (fun σ => c.speed B.family.metric x σ * Real.exp (-B.B₀ * (σ - r)))
      (interior (Icc r t)) := by
    intro τ hτ
    rw [interior_Icc] at hτ
    have hτI : τ ∈ Icc s u := hsub ⟨hτ.1.le, hτ.2.le⟩
    have h1 : HasDerivAt (fun σ => c.speed B.family.metric x σ)
        (-(c.q B.family x τ) * c.speed B.family.metric x τ) τ :=
      (hsp x τ hτI).hasDerivAt (Icc_mem_nhds (lt_of_le_of_lt hr.1 hτ.1)
        (lt_of_lt_of_le hτ.2 ht.2))
    have h2 : HasDerivAt (fun σ => Real.exp (-B.B₀ * (σ - r)))
        (Real.exp (-B.B₀ * (τ - r)) * (-B.B₀)) τ := by
      have h3 : HasDerivAt (fun σ : ℝ => -B.B₀ * (σ - r)) (-B.B₀) τ := by
        simpa using ((hasDerivAt_id τ).sub_const r).const_mul (-B.B₀)
      simpa using h3.exp
    exact (h1.mul h2).differentiableAt.differentiableWithinAt
  have hmono := antitoneOn_of_deriv_nonpos (convex_Icc r t) hcont hdiff hderiv
  have h1 := hmono (left_mem_Icc.mpr hrt) (right_mem_Icc.mpr hrt) hrt
  have hφr : (fun σ => c.speed B.family.metric x σ * Real.exp (-B.B₀ * (σ - r))) r =
      c.speed B.family.metric x r := by simp
  rw [hφr] at h1
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg (B.B₀ * (t - r)))
  have h4 : (c.speed B.family.metric x t * Real.exp (-B.B₀ * (t - r))) *
      Real.exp (B.B₀ * (t - r)) = c.speed B.family.metric x t := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  rw [h4] at h3
  calc c.speed B.family.metric x t ≤
        c.speed B.family.metric x r * Real.exp (B.B₀ * (t - r)) := h3
    _ = Real.exp (B.B₀ * (t - r)) * c.speed B.family.metric x r := by ring

private theorem length_le_exp_mul (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    c.length B.family.metric t ≤ Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r := by
  have hvt : Continuous fun x : ℝ => c.speed B.family.metric x t :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed t ht).continuous
  have hvr : Continuous fun x : ℝ => c.speed B.family.metric x r :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed r hr).continuous
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hvt.intervalIntegrable 0 1)
    ((continuous_const.mul hvr).intervalIntegrable 0 1)
    (fun x _ => speed_le_exp_mul B hsu hwindow c hc x r t hr ht hrt)
  have hconst : (∫ x in (0 : ℝ)..1,
        Real.exp (B.B₀ * (t - r)) * c.speed B.family.metric x r) =
      Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r := by
    rw [intervalIntegral.integral_const_mul]
    simp only [CurveMap.length, CurveMap.integral, one_mul]
  calc c.length B.family.metric t = ∫ x in (0 : ℝ)..1, c.speed B.family.metric x t := by
        simp only [CurveMap.length, CurveMap.integral, one_mul]
    _ ≤ ∫ x in (0 : ℝ)..1, Real.exp (B.B₀ * (t - r)) * c.speed B.family.metric x r := hmono
    _ = Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r := hconst

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem hasDerivWithinAt_Ioi_of_Icc {A B : ℝ} {f : ℝ → ℝ} {x c : ℝ}
    (hA : A ≤ x) (hxB : x < B) (h : HasDerivWithinAt f c (Icc A B) x) :
    HasDerivWithinAt f c (Ioi x) x := by
  have hsub : Ioo x B ⊆ Icc A B := fun z hz => ⟨hA.trans hz.1.le, hz.2.le⟩
  have hmono : HasDerivWithinAt f c (Ioo x B) x := h.mono hsub
  have h1 : Filter.Tendsto (slope f x) (𝓝[Ioo x B] x) (𝓝 c) :=
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Ioo x B)).mp hmono
  rw [nhdsWithin_Ioo_eq_nhdsGT hxB] at h1
  exact (hasDerivWithinAt_iff_tendsto_slope' (by simp : x ∉ Ioi x)).mpr h1

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem integral_exp_mul_sub (B : ℝ) (hB : B ≠ 0) (r t : ℝ) :
    (∫ v in r..t, Real.exp (B * (v - r))) = (Real.exp (B * (t - r)) - 1) / B := by
  have hderiv : ∀ v ∈ uIcc r t,
      HasDerivAt (fun w : ℝ => Real.exp (B * (w - r)) / B) (Real.exp (B * (v - r))) v := by
    intro v _
    have h1 : HasDerivAt (fun w : ℝ => B * (w - r)) B v := by
      simpa using ((hasDerivAt_id v).sub_const r).const_mul B
    have h2 : HasDerivAt (fun w : ℝ => Real.exp (B * (w - r))) (Real.exp (B * (v - r)) * B) v :=
      h1.exp
    have h3 : HasDerivAt (fun w : ℝ => Real.exp (B * (w - r)) / B)
        (Real.exp (B * (v - r)) * B / B) v := h2.div_const B
    simpa [hB] using h3
  have hint : IntervalIntegrable (fun v : ℝ => Real.exp (B * (v - r))) volume r t :=
    ((Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable r t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have hrr : Real.exp (B * (r - r)) = 1 := by simp
  rw [hrr]
  field_simp

omit [SigmaCompactSpace M] hBoundary in
private theorem length_nonneg (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) (t : ℝ) : 0 ≤ c.length B.family.metric t := by
  rw [CurveMap.length, CurveMap.integral]
  exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
    (fun x _ => mul_nonneg zero_le_one (c.speed_nonneg B.family.metric x t))

private theorem energy_integral_le (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    (∫ v in r..t, c.energy B.family.metric v) ≤
      Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r := by
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  have hLcont : ContinuousOn (c.length B.family.metric) (Icc r t) :=
    ((contDiffOn_length B hsu hwindow c hc).continuousOn).mono hsub
  have hEcont : ContinuousOn (c.energy B.family.metric) (Icc r t) :=
    (continuousOn_energy B hsu hwindow c hc).mono hsub
  have hφcont : ContinuousOn (fun v : ℝ => -c.energy B.family.metric v +
      B.B₀ * c.length B.family.metric v) (Icc r t) :=
    (hEcont.neg).add (continuousOn_const.mul hLcont)
  have hderiv : ∀ v ∈ Ioo r t,
      HasDerivWithinAt (c.length B.family.metric)
        (derivWithin (c.length B.family.metric) (Icc s u) v) (Ioi v) v := by
    intro v hv
    refine hasDerivWithinAt_Ioi_of_Icc (f := c.length B.family.metric) (x := v)
      (hr.1.trans hv.1.le) (lt_of_lt_of_le hv.2 ht.2) ?_
    refine (length_hasDerivWithinAt B hsu hwindow c hc v
      ⟨hr.1.trans hv.1.le, (hv.2.le.trans ht.2)⟩).congr_deriv ?_
    exact (derivWithin_length B hsu hwindow c hc v
      ⟨hr.1.trans hv.1.le, (hv.2.le.trans ht.2)⟩).symm
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hrt hLcont hderiv
    (hφcont.integrableOn_compact isCompact_Icc)
    (fun v hv => by
      rw [derivWithin_length B hsu hwindow c hc v
        ⟨hr.1.trans hv.1.le, hv.2.le.trans ht.2⟩]
      have hI := ricciTangent_integral_ge B hwindow c hc v
        (hsub ⟨hv.1.le, hv.2.le⟩)
      have hEnn : 0 ≤ c.energy B.family.metric v := by
        rw [CurveMap.energy, CurveMap.integral]
        exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
          (fun x _ => mul_nonneg (c.normSq_nonneg B.family.metric
            (c.curvatureVector B.family.metric) x v) (c.speed_nonneg B.family.metric x v))
      linarith)
  have hmain' : c.length B.family.metric t - c.length B.family.metric r ≤
      -(∫ v in r..t, c.energy B.family.metric v) +
        B.B₀ * ∫ v in r..t, c.length B.family.metric v := by
    have hsplit : (∫ v in r..t, -c.energy B.family.metric v +
        B.B₀ * c.length B.family.metric v) =
        -(∫ v in r..t, c.energy B.family.metric v) +
          B.B₀ * ∫ v in r..t, c.length B.family.metric v := by
      rw [intervalIntegral.integral_add (f := fun v : ℝ => -c.energy B.family.metric v)
        (g := fun v : ℝ => B.B₀ * c.length B.family.metric v)
        (hEcont.neg.intervalIntegrable_of_Icc hrt)
        ((continuousOn_const.mul hLcont).intervalIntegrable_of_Icc hrt)]
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    rw [hsplit] at hmain
    exact hmain
  have hLbound : (∫ v in r..t, c.length B.family.metric v) ≤
      c.length B.family.metric r * ∫ v in r..t, Real.exp (B.B₀ * (v - r)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (μ := volume) hrt ?_ ?_
      (fun v hv => (length_le_exp_mul B hsu hwindow c hc r v hr (hsub hv)
        (by linarith [hv.1] : r ≤ v)).trans_eq (mul_comm _ _))
    · exact hLcont.intervalIntegrable_of_Icc hrt
    · exact (continuousOn_const.mul
        ((Real.continuous_exp.comp (continuous_const.mul
          (continuous_id.sub continuous_const))).continuousOn)).intervalIntegrable_of_Icc hrt
  have hlen_nn : 0 ≤ c.length B.family.metric r := length_nonneg B c r
  have hLt_nn : 0 ≤ c.length B.family.metric t := length_nonneg B c t
  rcases eq_or_ne B.B₀ 0 with hb | hb
  · simp only [hb, zero_mul, Real.exp_zero, one_mul]
    have hmain'' : c.length B.family.metric t - c.length B.family.metric r ≤
        -(∫ v in r..t, c.energy B.family.metric v) := by
      have h := hmain'
      rw [hb, zero_mul, add_zero] at h
      exact h
    linarith [hmain'', hLt_nn]
  · have hexp := integral_exp_mul_sub B.B₀ hb r t
    have hstep : B.B₀ * (c.length B.family.metric r *
        ∫ v in r..t, Real.exp (B.B₀ * (v - r))) =
        c.length B.family.metric r * (Real.exp (B.B₀ * (t - r)) - 1) := by
      rw [hexp]
      field_simp
    have hmul : B.B₀ * (∫ v in r..t, c.length B.family.metric v) ≤
        B.B₀ * (c.length B.family.metric r *
          ∫ v in r..t, Real.exp (B.B₀ * (v - r))) :=
      mul_le_mul_of_nonneg_left hLbound B.B₀_nonneg
    have hgoal : (∫ v in r..t, c.energy B.family.metric v) ≤
        c.length B.family.metric r * Real.exp (B.B₀ * (t - r)) := by
      linarith [hmain', hmul, hstep, hlen_nn, hLt_nn]
    rwa [mul_comm] at hgoal

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem deriv_add_period_eq {f : ℝ → ℝ} {x : ℝ} (hper : Function.Periodic f 1)
    (hfd : DifferentiableAt ℝ f (x + 1)) :
    deriv f (x + 1) = deriv f x := by
  have hcomp : HasDerivAt (fun y : ℝ => f (y + 1)) (deriv f (x + 1)) x := by
    have h := hfd.hasDerivAt.comp x ((hasDerivAt_id x).add_const 1)
    rw [mul_one] at h
    exact h
  have heq : (fun y : ℝ => f (y + 1)) = f := funext (fun y => hper y)
  rw [heq] at hcomp
  exact hcomp.deriv.symm

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] hBoundary in
private theorem sliceMDiff (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (v : ℝ) (hv : v ∈ Icc s u) :
    ∀ y, MDifferentiableAt 𝓘(ℝ, ℝ) I (fun z => c.lift z v) y := fun y =>
  (contMDiffOn_univ.mp (c.space_slice_contMDiffOn (Icc s u) hc v hv)).mdifferentiableAt
    (by norm_num)

omit [SigmaCompactSpace M] in
private theorem curvatureSq_add_period (B : RicciBackground (I := I) (M := M) D a b)
    (_hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (v : ℝ) (hv : v ∈ Icc s u) (x : ℝ) :
    c.curvatureSq B.family.metric (x + 1) v = c.curvatureSq B.family.metric x v := by
  have hγ := sliceMDiff c hc.smooth v hv
  have hs : c.speed B.family.metric (x + 1) v = c.speed B.family.metric x v :=
    c.speed_add_period B.family.metric v x (hγ (x + 1))
  have hD : c.Dx B.family.metric (c.unitTangent B.family.metric) (x + 1) v =
      c.Dx B.family.metric (c.unitTangent B.family.metric) x v :=
    c.Dx_add_period B.family.metric v x (c.unitTangent B.family.metric)
      (fun y => c.unitTangent_add_period B.family.metric v y (hγ (y + 1)))
      (c.unitTangent_contMDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv) (hγ (x + 1))
  have hH : c.curvatureVector B.family.metric (x + 1) v = c.curvatureVector B.family.metric x v := by
    change (c.speed B.family.metric (x + 1) v)⁻¹ • c.Dx B.family.metric
        (c.unitTangent B.family.metric) (x + 1) v =
      (c.speed B.family.metric x v)⁻¹ • c.Dx B.family.metric
        (c.unitTangent B.family.metric) x v
    rw [hs, hD]
    rfl
  have hl : c.lift (x + 1) v = c.lift x v := c.lift_add_period v x
  change (B.family.metric v).inner (c.lift (x + 1) v)
      (c.curvatureVector B.family.metric (x + 1) v) (c.curvatureVector B.family.metric (x + 1) v) =
    (B.family.metric v).inner (c.lift x v)
      (c.curvatureVector B.family.metric x v) (c.curvatureVector B.family.metric x v)
  rw [hH, hl]

omit [SigmaCompactSpace M] in
private theorem regularizedCurvature_add_period (B : RicciBackground (I := I) (M := M) D a b)
    (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (v : ℝ) (hv : v ∈ Icc s u)
    (x : ℝ) :
    c.regularizedCurvature B.family.metric ε (x + 1) v =
      c.regularizedCurvature B.family.metric ε x v := by
  have h := curvatureSq_add_period B hwindow c hc v hv x
  simp only [CurveMap.regularizedCurvature, h]

private theorem regularizedCurvature_slice_contDiff (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    ContDiff ℝ ∞ (fun x : ℝ => c.regularizedCurvature B.family.metric ε x v) := by
  have hjoint := (rfs_csf_regularized_curvature B hsu hwindow c hc ε hε).1
  have hinner : ContDiffOn ℝ ∞ (fun x : ℝ => (x, v)) (univ : Set ℝ) :=
    (contDiff_id.prodMk contDiff_const).contDiffOn
  have h := hjoint.comp hinner (fun x _ => ⟨mem_univ x, hv⟩)
  rwa [contDiffOn_univ] at h

private theorem integral_ds_ds_regularizedCurvature_mul_speed_eq_zero
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    (∫ x in (0 : ℝ)..1, c.ds B.family.metric (c.ds B.family.metric
        (c.regularizedCurvature B.family.metric ε)) x v * c.speed B.family.metric x v) = 0 := by
  set F : ℝ → ℝ := fun x => c.regularizedCurvature B.family.metric ε x v with hFdef
  have hFsmooth : ContDiff ℝ ∞ F := regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε v hv
  have hFper : Function.Periodic F 1 := fun x => regularizedCurvature_add_period B hwindow c hc ε v hv x
  set ψ : ℝ → ℝ := fun x => (c.speed B.family.metric x v)⁻¹ * deriv F x with hψdef
  have hspos : ∀ x : ℝ, 0 < c.speed B.family.metric x v :=
    fun x => c.speed_pos B.family.metric hc.immersed x v hv
  have hspos' : ∀ x : ℝ, c.speed B.family.metric x v ≠ 0 := fun x => ne_of_gt (hspos x)
  have hγ := sliceMDiff c hc.smooth v hv
  have hψper : Function.Periodic ψ 1 := by
    intro x
    have hs : c.speed B.family.metric (x + 1) v = c.speed B.family.metric x v :=
      c.speed_add_period B.family.metric v x (hγ (x + 1))
    have hd : deriv F (x + 1) = deriv F x :=
      deriv_add_period_eq hFper (hFsmooth.differentiable (by simp) (x + 1))
    simp only [hψdef, hs, hd]
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    have hsd : ContDiff ℝ ∞ (fun x : ℝ => c.speed B.family.metric x v) :=
      c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv
    exact (hsd.inv (fun x => hspos' x)).mul (hFsmooth.iterate_deriv 1)
  have hderiveq : (∫ x in (0 : ℝ)..1, deriv ψ x) = ψ 1 - ψ 0 :=
    intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hψsmooth.differentiable (by simp) x)
      ((hψsmooth.continuous_deriv (by simp)).continuousOn.intervalIntegrable)
  have hcongr : ∀ x : ℝ, c.ds B.family.metric (c.ds B.family.metric
      (c.regularizedCurvature B.family.metric ε)) x v * c.speed B.family.metric x v =
      deriv ψ x := by
    intro x
    have h2 : c.ds B.family.metric (c.ds B.family.metric (c.regularizedCurvature B.family.metric ε))
        x v = (c.speed B.family.metric x v)⁻¹ * deriv ψ x := rfl
    rw [h2]
    field_simp [hspos' x]
  rw [intervalIntegral.integral_congr (fun x _ => hcongr x), hderiveq]
  have h10 : ψ 1 = ψ 0 := by simpa using hψper 0
  rw [h10, sub_self]




private theorem regularizedCurvature_joint (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => c.regularizedCurvature B.family.metric ε p.1 p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
  (rfs_csf_regularized_curvature B hsu hwindow c hc ε hε).1

private theorem hasDerivWithinAt_regularizedCurvature_slice
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (x : ℝ) (v : ℝ) (hv : v ∈ Icc s u) :
    HasDerivWithinAt (fun τ => c.regularizedCurvature B.family.metric ε x τ)
      (derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v)
      (Icc s u) v := by
  have hjoint := regularizedCurvature_joint B hsu hwindow c hc ε hε
  have hx : ContDiffWithinAt ℝ ∞
      (fun τ : ℝ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v := by
    have harg : ContDiffWithinAt ℝ ∞ (fun τ : ℝ => (x, τ)) (Icc s u) v :=
      contDiffWithinAt_const.prodMk contDiffWithinAt_id
    exact (hjoint.contDiffWithinAt ⟨mem_univ x, hv⟩).comp v harg
      (fun τ hτ => ⟨mem_univ x, hτ⟩)
  exact (hx.differentiableWithinAt (by norm_num)).hasDerivWithinAt

private theorem continuousOn_derivWithin_regularizedCurvature
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε) :
    ContinuousOn (fun p : ℝ × ℝ =>
      derivWithin (fun τ => c.regularizedCurvature B.family.metric ε p.1 τ) (Icc s u) p.2)
      ((univ : Set ℝ) ×ˢ Icc s u) :=
  (contDiffOn_derivWithin_snd hsu (regularizedCurvature_joint B hsu hwindow c hc ε hε)).continuousOn

private theorem hasDerivWithinAt_weighted_regularizedTotalCurvature
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (ε : ℝ) (hε : 0 < ε) {p q t : ℝ} (hpq : p ≤ q) (ht : t ∈ Icc s u)
    {φ φt : ℝ → ℝ → ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    : HasDerivWithinAt (fun τ => ∫ x in p..q,
        φ x τ * c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ)
      (∫ x in p..q,
        (φt x t * c.regularizedCurvature B.family.metric ε x t +
          φ x t * derivWithin (fun σ => c.regularizedCurvature B.family.metric ε x σ) (Icc s u) t) *
          c.speed B.family.metric x t + φ x t * c.regularizedCurvature B.family.metric ε x t *
          (-(c.q B.family x t) * c.speed B.family.metric x t)) (Icc s u) t := by
  have hsub : Icc p q ×ˢ Icc s u ⊆ (univ : Set ℝ) ×ˢ Icc s u :=
    Set.prod_mono (Set.subset_univ _) Subset.rfl
  have hRj := (regularizedCurvature_joint B hsu hwindow c hc ε hε).continuousOn.mono hsub
  have hvj := (joint_continuousOn_speed B hwindow c hc).mono hsub
  have hqj := (CurveMap.q_continuousOn B hsu hwindow c hc).mono hsub
  have hRtj := (continuousOn_derivWithin_regularizedCurvature B hsu hwindow c hc ε hε).mono hsub
  let G : ℝ → ℝ → ℝ := fun x τ =>
    (φt x τ * c.regularizedCurvature B.family.metric ε x τ +
      φ x τ * derivWithin (fun σ => c.regularizedCurvature B.family.metric ε x σ) (Icc s u) τ) *
      c.speed B.family.metric x τ + φ x τ * c.regularizedCurvature B.family.metric ε x τ *
      (-(c.q B.family x τ) * c.speed B.family.metric x τ)
  have hGc : ContinuousOn (fun z : ℝ × ℝ => G z.1 z.2) (Icc p q ×ˢ Icc s u) :=
    ((hφtc.mul hRj).add (hφc.mul hRtj)).mul hvj |>.add
      ((hφc.mul hRj).mul (hqj.neg.mul hvj))
  have hsp := CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
    (CurveMap.pairingEvolution B hsu hwindow c hc)
  have hpoint : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ * c.regularizedCurvature B.family.metric ε x σ *
        c.speed B.family.metric x σ) (G x τ) (Icc s u) τ := by
    intro x hx τ hτ
    exact ((hφt x hx τ hτ).mul
      (hasDerivWithinAt_regularizedCurvature_slice B hsu hwindow c hc ε hε x τ hτ)).mul
      (hsp x τ hτ)
  have hd := DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_paramIntervalIntegral_on_interval
    hpq ((hφc.mul hRj).mul hvj) hGc hpoint t ht
  exact hd

private theorem hasDerivWithinAt_integral_regularizedCurvature
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    HasDerivWithinAt
      (fun τ => c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) τ)
      (∫ x in (0 : ℝ)..1,
        derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v *
            c.speed B.family.metric x v +
          c.regularizedCurvature B.family.metric ε x v *
            (-(c.q B.family x v) * c.speed B.family.metric x v)) (Icc s u) v := by
  have hd := hasDerivWithinAt_weighted_regularizedTotalCurvature B hsu hwindow c hc ε hε
    (p := 0) (q := 1) zero_le_one hv (φ := fun _ _ => 1) (φt := fun _ _ => 0)
    continuousOn_const continuousOn_const
    (fun _ _ τ _ => hasDerivWithinAt_const τ (Icc s u) 1)
  simpa only [zero_mul, zero_add, one_mul, CurveMap.integral] using hd





theorem weighted_regularized_total_curvature_derivWithin_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (ε : ℝ) (hε : 0 < ε) {p q t : ℝ} (hpq : p ≤ q) (ht : t ∈ Icc s u)
    {φ φt : ℝ → ℝ → ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    (hφxx : ∀ x ∈ Icc p q, ContDiffAt ℝ 2 (fun y => φ y t) x)
    (hφn : ∀ x ∈ Icc p q, 0 ≤ φ x t)
    (hφp : φ p t = 0) (hφq : φ q t = 0)
    (hφp' : deriv (fun y => φ y t) p = 0)
    (hφq' : deriv (fun y => φ y t) q = 0) :
    derivWithin (fun τ => ∫ x in p..q,
      φ x τ * c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ)
      (Icc s u) t ≤
      ∫ x in p..q, ((φt x t + c.ds B.family.metric (c.ds B.family.metric φ) x t +
        (B.C + B.B₀) * φ x t) * c.regularizedCurvature B.family.metric ε x t +
        B.C * φ x t) * c.speed B.family.metric x t := by
  have hsub : Icc p q ×ˢ Icc s u ⊆ (univ : Set ℝ) ×ˢ Icc s u :=
    Set.prod_mono (Set.subset_univ _) Subset.rfl
  have hRj := (regularizedCurvature_joint B hsu hwindow c hc ε hε).continuousOn.mono hsub
  have hvj := (joint_continuousOn_speed B hwindow c hc).mono hsub
  have hqj := (CurveMap.q_continuousOn B hsu hwindow c hc).mono hsub
  have hRtj := (continuousOn_derivWithin_regularizedCurvature B hsu hwindow c hc ε hε).mono hsub
  let G : ℝ → ℝ → ℝ := fun x τ =>
    (φt x τ * c.regularizedCurvature B.family.metric ε x τ +
      φ x τ * derivWithin (fun σ => c.regularizedCurvature B.family.metric ε x σ) (Icc s u) τ) *
      c.speed B.family.metric x τ + φ x τ * c.regularizedCurvature B.family.metric ε x τ *
      (-(c.q B.family x τ) * c.speed B.family.metric x τ)
  have hGc : ContinuousOn (fun z : ℝ × ℝ => G z.1 z.2) (Icc p q ×ˢ Icc s u) :=
    ((hφtc.mul hRj).add (hφc.mul hRtj)).mul hvj |>.add
      ((hφc.mul hRj).mul (hqj.neg.mul hvj))
  have hsp := CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
    (CurveMap.pairingEvolution B hsu hwindow c hc)
  have hpoint : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ * c.regularizedCurvature B.family.metric ε x σ *
        c.speed B.family.metric x σ) (G x τ) (Icc s u) τ := by
    intro x hx τ hτ
    exact ((hφt x hx τ hτ).mul
      (hasDerivWithinAt_regularizedCurvature_slice B hsu hwindow c hc ε hε x τ hτ)).mul
      (hsp x τ hτ)
  have hd := DifferentialGeometry.Analysis.Calculus.hasDerivWithinAt_paramIntervalIntegral_on_interval
    hpq ((hφc.mul hRj).mul hvj) hGc hpoint t ht
  rw [hd.derivWithin ((uniqueDiffOn_Icc hsu) t ht)]
  let v := fun x => c.speed B.family.metric x t
  let h := fun x => c.regularizedCurvature B.family.metric ε x t
  let w := fun x => φ x t
  let P := fun x => (v x)⁻¹
  have hv : ContDiff ℝ ∞ v := c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed t ht
  have hvne : ∀ x, v x ≠ 0 := fun x => ne_of_gt (c.speed_pos B.family.metric hc.immersed x t ht)
  have hh : ContDiff ℝ ∞ h := regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε t ht
  have hP : ContDiff ℝ ∞ P := hv.inv hvne
  have hPh : ContDiff ℝ ∞ (fun x => P x * deriv h x) := hP.mul (hh.iterate_deriv 1)
  have hw : ∀ x ∈ uIcc p q, ContDiffAt ℝ 2 w x := by
    simpa only [uIcc_of_le hpq] using hφxx
  have hPw : ∀ x ∈ uIcc p q, ContDiffAt ℝ 1 (fun y => P y * deriv w y) x :=
    fun x hx => (hP.of_le (by simp)).contDiffAt.mul ((hw x hx).derivWithin (by norm_num))
  have hgreen := DifferentialGeometry.Analysis.Integration.integral_mul_deriv_mul_deriv_eq
    hw (fun x _ => (hh.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    (fun x _ => (hP.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffAt)
  have hgreen' : (∫ x in p..q, w x * deriv (fun y => P y * deriv h y) x) =
      ∫ x in p..q, h x * deriv (fun y => P y * deriv w y) x := by
    simpa only [w, hφp, hφq, hφp', hφq', zero_mul, mul_zero, sub_zero, zero_sub, neg_zero,
      zero_add] using hgreen
  let f := fun x => φt x t * h x * v x + (B.C + B.B₀) * w x * h x * v x +
    B.C * w x * v x
  have hφts : ContinuousOn (fun x => φt x t) (uIcc p q) := by
    rw [uIcc_of_le hpq]
    exact hφtc.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, ht⟩)
  have hws : ContinuousOn w (uIcc p q) := fun x hx => (hw x hx).continuousAt.continuousWithinAt
  have hf : ContinuousOn f (uIcc p q) :=
    ((hφts.mul hh.continuous.continuousOn).mul hv.continuous.continuousOn).add
      (((continuousOn_const.mul hws).mul hh.continuous.continuousOn).mul hv.continuous.continuousOn)
      |>.add ((continuousOn_const.mul hws).mul hv.continuous.continuousOn)
  have hdiffh : ContinuousOn (fun x => w x * deriv (fun y => P y * deriv h y) x) (uIcc p q) :=
    hws.mul (hPh.continuous_deriv (by simp)).continuousOn
  have hdiffw : ContinuousOn (fun x => h x * deriv (fun y => P y * deriv w y) x) (uIcc p q) :=
    hh.continuous.continuousOn.mul (fun x hx =>
      ((hPw x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt)
  have hGs : ContinuousOn (fun x => G x t) (uIcc p q) := by
    rw [uIcc_of_le hpq]
    exact hGc.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, ht⟩)
  calc
    (∫ x in p..q, G x t) ≤ ∫ x in p..q,
        f x + w x * deriv (fun y => P y * deriv h y) x := by
      apply intervalIntegral.integral_mono_on hpq hGs.intervalIntegrable (hf.add hdiffh).intervalIntegrable
      intro x hx
      have he := weighted_regularized_curvature_density_evolution_le B hsu hwindow c hc ε hε x t ht
        (hφt x hx t ht) (hφn x hx)
      rw [(hpoint x hx t ht).derivWithin ((uniqueDiffOn_Icc hsu) t ht)] at he
      have heq : c.ds B.family.metric (c.ds B.family.metric
          (c.regularizedCurvature B.family.metric ε)) x t * v x =
          deriv (fun y => P y * deriv h y) x := by
        change (v x)⁻¹ * deriv (fun y => P y * deriv h y) x * v x = _
        field_simp [hvne x]
      change G x t ≤ _ at he
      dsimp only [f, w, h, v]
      rw [show φ x t * c.ds B.family.metric (c.ds B.family.metric
        (c.regularizedCurvature B.family.metric ε)) x t * c.speed B.family.metric x t =
        φ x t * deriv (fun y => P y * deriv h y) x from by
          rw [mul_assoc, heq]] at he
      dsimp only [Pi.add_apply, h] at he ⊢
      linarith only [he]
    _ = (∫ x in p..q, f x) + ∫ x in p..q, h x * deriv (fun y => P y * deriv w y) x := by
      rw [intervalIntegral.integral_add hf.intervalIntegrable hdiffh.intervalIntegrable, hgreen']
    _ = ∫ x in p..q, f x + h x * deriv (fun y => P y * deriv w y) x :=
      (intervalIntegral.integral_add hf.intervalIntegrable hdiffw.intervalIntegrable).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      have heq : c.ds B.family.metric (c.ds B.family.metric φ) x t * v x =
          deriv (fun y => P y * deriv w y) x := by
        change (v x)⁻¹ * deriv (fun y => P y * deriv w y) x * v x = _
        field_simp [hvne x]
      dsimp only [f, w, h, v]
      rw [← heq]
      ring

theorem weighted_regularized_total_curvature_le_of_cutoff_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (ε : ℝ) (hε : 0 < ε) {p q t L Θ : ℝ} (hpq : p ≤ q) (ht : t ∈ Icc s u)
    {φ φt : ℝ → ℝ → ℝ} {F : ℝ → ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    (hφxx : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q, ContDiffAt ℝ 2 (fun y => φ y τ) x)
    (hφrange : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q, φ x τ ∈ Icc 0 1)
    (hφboundary : ∀ τ ∈ Ioo s t, φ p τ = 0 ∧ φ q τ = 0 ∧
      deriv (fun y => φ y τ) p = 0 ∧ deriv (fun y => φ y τ) q = 0)
    (hF : IntervalIntegrable F volume s t) (hFn : ∀ τ ∈ Ioo s t, 0 ≤ F τ)
    (hcut : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q,
      φt x τ + c.ds B.family.metric (c.ds B.family.metric φ) x τ ≤ F τ)
    (hL : ∀ τ ∈ Ioo s t, (∫ x in p..q, c.speed B.family.metric x τ) ≤ L)
    (hΘ : ∀ τ ∈ Ioo s t,
      (∫ x in p..q, c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ) ≤ Θ) :
    (∫ x in p..q, φ x t * c.regularizedCurvature B.family.metric ε x t * c.speed B.family.metric x t) ≤
      (∫ x in p..q, φ x s * c.regularizedCurvature B.family.metric ε x s * c.speed B.family.metric x s) +
      Θ * (∫ τ in s..t, F τ + (B.C + B.B₀)) + B.C * L * (t - s) := by
  let E := fun τ => ∫ x in p..q,
    φ x τ * c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ
  have hEd : ∀ τ ∈ Icc s u, DifferentiableWithinAt ℝ E (Icc s u) τ := fun τ hτ =>
    (hasDerivWithinAt_weighted_regularizedTotalCurvature B hsu hwindow c hc ε hε hpq hτ
      hφc hφtc hφt).differentiableWithinAt
  have hC : 0 ≤ B.C := by
    dsimp only [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hCB : 0 ≤ B.C + B.B₀ := add_nonneg hC B.B₀_nonneg
  have hbound : ∀ τ ∈ Ioo s t,
      derivWithin E (Icc s u) τ ≤ (F τ + (B.C + B.B₀)) * Θ + B.C * L := by
    intro τ hτ
    have hτ' : τ ∈ Icc s u := ⟨hτ.1.le, hτ.2.le.trans ht.2⟩
    have hw := weighted_regularized_total_curvature_derivWithin_le B hsu hwindow c hc ε hε hpq hτ'
      hφc hφtc hφt (hφxx τ hτ) (fun x hx => (hφrange τ hτ x hx).1)
      (hφboundary τ hτ).1 (hφboundary τ hτ).2.1
      (hφboundary τ hτ).2.2.1 (hφboundary τ hτ).2.2.2
    have hv := c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed τ hτ'
    have hh := regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε τ hτ'
    have hvi := hv.inv (fun x => ne_of_gt (c.speed_pos B.family.metric hc.immersed x τ hτ'))
    have hφs : ContinuousOn (fun x => φ x τ) (uIcc p q) := by
      rw [uIcc_of_le hpq]
      exact fun x hx => (hφxx τ hτ x hx).continuousAt.continuousWithinAt
    have hφts : ContinuousOn (fun x => φt x τ) (uIcc p q) := by
      rw [uIcc_of_le hpq]
      exact hφtc.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, hτ'⟩)
    have hds2 : ContinuousOn (fun x => c.ds B.family.metric (c.ds B.family.metric φ) x τ)
        (uIcc p q) := by
      intro x hx
      have hx' : x ∈ Icc p q := by simpa only [uIcc_of_le hpq] using hx
      have hdx : ContDiffAt ℝ 1 (deriv (fun y => φ y τ)) x :=
        (hφxx τ hτ x hx').derivWithin (by norm_num)
      have hhx : ContDiffAt ℝ 1 (fun y => (c.speed B.family.metric y τ)⁻¹ *
          deriv (fun z => φ z τ) y) x := (hvi.of_le (by simp)).contDiffAt.mul hdx
      exact (hvi.continuous.continuousAt.mul
        (hhx.derivWithin (m := 0) (by norm_num)).continuousAt).continuousWithinAt
    have hleft : IntervalIntegrable (fun x =>
        ((φt x τ + c.ds B.family.metric (c.ds B.family.metric φ) x τ +
          (B.C + B.B₀) * φ x τ) * c.regularizedCurvature B.family.metric ε x τ +
          B.C * φ x τ) * c.speed B.family.metric x τ) volume p q :=
      ((((hφts.add hds2).add (continuousOn_const.mul hφs)).mul hh.continuous.continuousOn).add
        (continuousOn_const.mul hφs)).mul hv.continuous.continuousOn |>.intervalIntegrable
    have hright : IntervalIntegrable (fun x =>
        (F τ + (B.C + B.B₀)) * (c.regularizedCurvature B.family.metric ε x τ *
          c.speed B.family.metric x τ) + B.C * c.speed B.family.metric x τ) volume p q :=
      ((((hh.continuous.mul hv.continuous).intervalIntegrable p q).const_mul _).add
        ((hv.continuous.intervalIntegrable p q).const_mul _))
    have hmono := intervalIntegral.integral_mono_on hpq hleft hright (fun x hx => by
      have hn : 0 ≤ c.regularizedCurvature B.family.metric ε x τ := by
        exact Real.sqrt_nonneg _
      have h1 := mul_le_mul_of_nonneg_right
        (add_le_add (hcut τ hτ x hx)
          (mul_le_mul_of_nonneg_left (hφrange τ hτ x hx).2 hCB)) hn
      have h2 := mul_le_mul_of_nonneg_left (hφrange τ hτ x hx).2 hC
      have h3 := mul_le_mul_of_nonneg_right (add_le_add h1 h2) (c.speed_nonneg B.family.metric x τ)
      nlinarith only [h3])
    rw [intervalIntegral.integral_add
      (f := fun x => (F τ + (B.C + B.B₀)) *
        (c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ))
      (g := fun x => B.C * c.speed B.family.metric x τ)
      (((hh.continuous.mul hv.continuous).intervalIntegrable p q).const_mul _)
      ((hv.continuous.intervalIntegrable p q).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
    exact hw.trans (hmono.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hΘ τ hτ) (add_nonneg (hFn τ hτ) hCB))
      (mul_le_mul_of_nonneg_left (hL τ hτ) hC)))
  have hsub : Icc s t ⊆ Icc s u := Icc_subset_Icc le_rfl ht.2
  have hEc : ContinuousOn E (Icc s t) := fun τ hτ =>
    ((hEd τ (hsub hτ)).continuousWithinAt).mono hsub
  have hEr : ∀ τ ∈ Ioo s t,
      HasDerivWithinAt E (derivWithin E (Icc s u) τ) (Ioi τ) τ := by
    intro τ hτ
    exact ((hEd τ ⟨hτ.1.le, hτ.2.le.trans ht.2⟩).hasDerivWithinAt.hasDerivAt
      (Icc_mem_nhds hτ.1 (hτ.2.trans_le ht.2))).hasDerivWithinAt
  have hint : IntervalIntegrable (fun τ => (F τ + (B.C + B.B₀)) * Θ + B.C * L) volume s t :=
    ((hF.add intervalIntegrable_const).mul_const Θ).add intervalIntegrable_const
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1 hEc hEr
    ((intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mp hint) hbound
  rw [intervalIntegral.integral_add ((hF.add intervalIntegrable_const).mul_const Θ)
    intervalIntegrable_const, intervalIntegral.integral_mul_const, intervalIntegral.integral_const] at hi
  dsimp only [E] at hi
  simp only [smul_eq_mul] at hi
  linarith only [hi]

theorem weighted_total_curvature_le_of_cutoff_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {p q t L Θ : ℝ} (hpq : p ≤ q) (ht : t ∈ Icc s u)
    {φ φt : ℝ → ℝ → ℝ} {F : ℝ → ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    (hφxx : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q, ContDiffAt ℝ 2 (fun y => φ y τ) x)
    (hφrange : ∀ τ ∈ Icc s t, ∀ x ∈ Icc p q, φ x τ ∈ Icc 0 1)
    (hφboundary : ∀ τ ∈ Ioo s t, φ p τ = 0 ∧ φ q τ = 0 ∧
      deriv (fun y => φ y τ) p = 0 ∧ deriv (fun y => φ y τ) q = 0)
    (hF : IntervalIntegrable F volume s t) (hFn : ∀ τ ∈ Ioo s t, 0 ≤ F τ)
    (hcut : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q,
      φt x τ + c.ds B.family.metric (c.ds B.family.metric φ) x τ ≤ F τ)
    (hL : ∀ τ ∈ Icc s t, (∫ x in p..q, c.speed B.family.metric x τ) ≤ L)
    (hΘ : ∀ τ ∈ Ioo s t,
      (∫ x in p..q, c.curvature B.family.metric x τ * c.speed B.family.metric x τ) ≤ Θ) :
    (∫ x in p..q, φ x t * c.curvature B.family.metric x t * c.speed B.family.metric x t) ≤
      (∫ x in p..q, φ x s * c.curvature B.family.metric x s * c.speed B.family.metric x s) +
      Θ * (∫ τ in s..t, F τ + (B.C + B.B₀)) + B.C * L * (t - s) := by
  let J := ∫ τ in s..t, F τ + (B.C + B.B₀)
  let W := L * (1 + J)
  refine le_of_forall_pos_le_add fun η hη => ?_
  let ε := η / (|W| + 1)
  have hden : 0 < |W| + 1 := by positivity
  have hε : 0 < ε := div_pos hη hden
  have hεsmall : ε * W ≤ η := by
    have heq : ε * (|W| + 1) = η := div_mul_cancel₀ η (ne_of_gt hden)
    have hW : W ≤ |W| := le_abs_self W
    nlinarith [mul_le_mul_of_nonneg_left hW hε.le]
  have hsub : Icc s t ⊆ Icc s u := Icc_subset_Icc le_rfl ht.2
  have hcmp (τ : ℝ) (hτ : τ ∈ Icc s t) (ψ : ℝ → ℝ)
      (hψ : ContinuousOn ψ (Icc p q)) (hψrange : ∀ x ∈ Icc p q, ψ x ∈ Icc 0 1) :
      (∫ x in p..q, ψ x * c.curvature B.family.metric x τ * c.speed B.family.metric x τ) ≤
        (∫ x in p..q, ψ x * c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ) ∧
      (∫ x in p..q, ψ x * c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ) ≤
        (∫ x in p..q, ψ x * c.curvature B.family.metric x τ * c.speed B.family.metric x τ) + ε * L := by
    have hv := (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed τ (hsub hτ)).continuous
    have hk : Continuous (fun x => c.curvature B.family.metric x τ) :=
      (c.curvatureSq_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed τ (hsub hτ)).continuous.sqrt
    have hr := (regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε τ (hsub hτ)).continuous
    have hψ' : ContinuousOn ψ (uIcc p q) := by simpa only [uIcc_of_le hpq] using hψ
    have hki := ((hψ'.mul hk.continuousOn).mul hv.continuousOn).intervalIntegrable (μ := volume)
    have hri := ((hψ'.mul hr.continuousOn).mul hv.continuousOn).intervalIntegrable (μ := volume)
    constructor
    · apply intervalIntegral.integral_mono_on hpq hki hri
      intro x hx
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (sub_nonneg.mp (c.regularizedCurvature_error B.family.metric ε hε.le x τ).1)
          (hψrange x hx).1) (c.speed_nonneg B.family.metric x τ)
    · have hvi := (hv.intervalIntegrable (μ := volume) p q).const_mul ε
      have hm := intervalIntegral.integral_mono_on hpq hri (hki.add hvi) (fun x hx => by
        have he := (c.regularizedCurvature_error B.family.metric ε hε.le x τ).2
        have h1 := mul_le_mul_of_nonneg_left he (hψrange x hx).1
        have h2 := mul_le_mul_of_nonneg_right (hψrange x hx).2 hε.le
        have h3 : ψ x * c.regularizedCurvature B.family.metric ε x τ ≤
            ψ x * c.curvature B.family.metric x τ + ε := by nlinarith only [h1, h2]
        have h4 := mul_le_mul_of_nonneg_right h3 (c.speed_nonneg B.family.metric x τ)
        dsimp only [Pi.add_apply, Pi.mul_apply]
        nlinarith only [h4])
      rw [intervalIntegral.integral_add hki hvi, intervalIntegral.integral_const_mul] at hm
      exact hm.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hL τ hτ) hε.le))
  have hΘε : ∀ τ ∈ Ioo s t,
      (∫ x in p..q, c.regularizedCurvature B.family.metric ε x τ * c.speed B.family.metric x τ) ≤ Θ + ε * L := by
    intro τ hτ
    have he := (hcmp τ ⟨hτ.1.le, hτ.2.le⟩ (fun _ => 1) continuousOn_const
      (fun _ _ => ⟨zero_le_one, le_rfl⟩)).2
    simp only [one_mul] at he
    exact he.trans (add_le_add (hΘ τ hτ) le_rfl)
  have he := weighted_regularized_total_curvature_le_of_cutoff_bound B hsu hwindow c hc ε hε hpq ht
    hφc hφtc hφt hφxx (fun τ hτ => hφrange τ ⟨hτ.1.le, hτ.2.le⟩)
    hφboundary hF hFn hcut (fun τ hτ => hL τ ⟨hτ.1.le, hτ.2.le⟩) hΘε
  have hψs (τ : ℝ) (hτ : τ ∈ Icc s t) : ContinuousOn (fun x => φ x τ) (Icc p q) :=
    hφc.comp (continuousOn_id.prodMk continuousOn_const) (fun x hx => ⟨hx, hsub hτ⟩)
  have hleft := (hcmp t ⟨ht.1, le_rfl⟩ (fun x => φ x t)
    (hψs t ⟨ht.1, le_rfl⟩) (hφrange t ⟨ht.1, le_rfl⟩)).1
  have hright := (hcmp s ⟨le_rfl, ht.1⟩ (fun x => φ x s)
    (hψs s ⟨le_rfl, ht.1⟩) (hφrange s ⟨le_rfl, ht.1⟩)).2
  change _ ≤ _ + (Θ + ε * L) * J + _ at he
  change ε * (L * (1 + J)) ≤ η at hεsmall
  change _ ≤ _ + Θ * J + _ + η
  nlinarith only [hleft, hright, he, hεsmall]

theorem weighted_total_curvature_le_of_sqrt_cutoff_bound
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    {p q t L Θ : ℝ} (hpq : p ≤ q) (ht : t ∈ Icc s u)
    {φ φt : ℝ → ℝ → ℝ} {α β : ℝ}
    (hφc : ContinuousOn (fun z : ℝ × ℝ => φ z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφtc : ContinuousOn (fun z : ℝ × ℝ => φt z.1 z.2) (Icc p q ×ˢ Icc s u))
    (hφt : ∀ x ∈ Icc p q, ∀ τ ∈ Icc s u,
      HasDerivWithinAt (fun σ => φ x σ) (φt x τ) (Icc s u) τ)
    (hφxx : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q, ContDiffAt ℝ 2 (fun y => φ y τ) x)
    (hφrange : ∀ τ ∈ Icc s t, ∀ x ∈ Icc p q, φ x τ ∈ Icc 0 1)
    (hφboundary : ∀ τ ∈ Ioo s t, φ p τ = 0 ∧ φ q τ = 0 ∧
      deriv (fun y => φ y τ) p = 0 ∧ deriv (fun y => φ y τ) q = 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hcut : ∀ τ ∈ Ioo s t, ∀ x ∈ Icc p q,
      φt x τ + c.ds B.family.metric (c.ds B.family.metric φ) x τ ≤ α / Real.sqrt (τ - s) + β)
    (hL : ∀ τ ∈ Icc s t, (∫ x in p..q, c.speed B.family.metric x τ) ≤ L)
    (hΘ : ∀ τ ∈ Ioo s t,
      (∫ x in p..q, c.curvature B.family.metric x τ * c.speed B.family.metric x τ) ≤ Θ) :
    (∫ x in p..q, φ x t * c.curvature B.family.metric x t * c.speed B.family.metric x t) ≤
      (∫ x in p..q, φ x s * c.curvature B.family.metric x s * c.speed B.family.metric x s) +
      Θ * (2 * α * Real.sqrt (t - s) + (β + (B.C + B.B₀)) * (t - s)) + B.C * L * (t - s) := by
  let f := fun τ => (τ - s) ^ (-(1 / 2 : ℝ))
  have hf : IntervalIntegrable f volume s t := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - s)
      (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_right s
    simpa only [zero_add, sub_add_cancel] using h
  have hfeq (τ : ℝ) (hτ : s < τ) : α * f τ = α / Real.sqrt (τ - s) := by
    dsimp only [f]
    rw [Real.rpow_neg (sub_nonneg.mpr hτ.le), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  have hnonneg : ∀ τ ∈ Ioo s t, 0 ≤ α * f τ + β := by
    intro τ hτ
    rw [hfeq τ hτ.1]
    exact add_nonneg (div_nonneg hα (Real.sqrt_nonneg _)) hβ
  have h := weighted_total_curvature_le_of_cutoff_bound B hsu hwindow c hc hpq ht
    hφc hφtc hφt hφxx hφrange hφboundary ((hf.const_mul α).add intervalIntegrable_const)
    hnonneg (fun τ hτ x hx => by rw [hfeq τ hτ.1]; exact hcut τ hτ x hx) hL hΘ
  have hfi : (∫ τ in s..t, f τ) = 2 * Real.sqrt (t - s) := by
    rw [show f = (fun τ => (τ - s) ^ (-(1 / 2 : ℝ))) from rfl,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) s, sub_self,
      integral_rpow (Or.inl (by norm_num : -1 < -(1 / 2 : ℝ)))]
    norm_num
    rw [← Real.sqrt_eq_rpow]
    ring
  have hi : (∫ τ in s..t, α * f τ + β + (B.C + B.B₀)) =
      2 * α * Real.sqrt (t - s) + (β + (B.C + B.B₀)) * (t - s) := by
    rw [intervalIntegral.integral_add ((hf.const_mul α).add intervalIntegrable_const) intervalIntegrable_const,
      intervalIntegral.integral_add (hf.const_mul α) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, hfi,
      intervalIntegral.integral_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  exact h.trans_eq (by rw [hi])


private theorem derivWithin_length_le (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (v : ℝ) (hv : v ∈ Icc s u) :
    derivWithin (c.length B.family.metric) (Icc s u) v ≤ B.B₀ * c.length B.family.metric v := by
  rw [derivWithin_length B hsu hwindow c hc v hv]
  have hI := ricciTangent_integral_ge B hwindow c hc v hv
  have hEnn : 0 ≤ c.energy B.family.metric v := by
    rw [CurveMap.energy, CurveMap.integral]
    exact intervalIntegral.integral_nonneg (by norm_num : (0 : ℝ) ≤ 1)
      (fun x _ => mul_nonneg (c.normSq_nonneg B.family.metric
        (c.curvatureVector B.family.metric) x v) (c.speed_nonneg B.family.metric x v))
  linarith

private theorem regularizedTotalCurvature_derivWithin_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    derivWithin (fun τ => c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v ≤
      (B.C + B.B₀) * c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
        B.C * c.length B.family.metric v := by
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) v := (uniqueDiffOn_Icc hsu) v hv
  have hderiv := (hasDerivWithinAt_integral_regularizedCurvature B hsu hwindow c hc ε hε v hv)
  rw [hderiv.derivWithin huniq]
  have hRj := regularizedCurvature_joint B hsu hwindow c hc ε hε
  have hvj := joint_continuousOn_speed B hwindow c hc
  have hspv : Continuous fun x : ℝ => c.speed B.family.metric x v := by
    have h := hvj.comp (s := (univ : Set ℝ))
      (continuous_id.prodMk continuous_const).continuousOn (fun x _ => ⟨mem_univ x, hv⟩)
    exact continuousOn_univ.mp h
  have hDv : Continuous fun x : ℝ =>
      derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v := by
    have h := (continuousOn_derivWithin_regularizedCurvature B hsu hwindow c hc ε hε).comp
      (s := (univ : Set ℝ)) (continuous_id.prodMk continuous_const).continuousOn
      (fun x _ => ⟨mem_univ x, hv⟩)
    exact continuousOn_univ.mp h
  have hqv : Continuous fun x : ℝ => c.q B.family x v := by
    have h := (CurveMap.q_continuousOn B hsu hwindow c hc).comp (s := (univ : Set ℝ))
      (continuous_id.prodMk continuous_const).continuousOn (fun x _ => ⟨mem_univ x, hv⟩)
    exact continuousOn_univ.mp h
  have hRx : Continuous fun x : ℝ => c.regularizedCurvature B.family.metric ε x v :=
    (regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε v hv).continuous
  have hstep : ∀ x : ℝ,
      derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v *
          c.speed B.family.metric x v +
        c.regularizedCurvature B.family.metric ε x v *
          (-(c.q B.family x v) * c.speed B.family.metric x v) ≤
      c.ds B.family.metric (c.ds B.family.metric (c.regularizedCurvature B.family.metric ε)) x v *
          c.speed B.family.metric x v +
        (((B.C + B.B₀) * c.regularizedCurvature B.family.metric ε x v) *
            c.speed B.family.metric x v + B.C * c.speed B.family.metric x v) := by
    intro x
    have h := weighted_regularized_curvature_density_evolution_le B hsu hwindow c hc ε hε x v hv
      (φ := fun _ => 1) (φt := 0) (hasDerivWithinAt_const v (Icc s u) 1) zero_le_one
    have hsp := CurveMap.speedEvolution_of_pairingEvolution B c hc.immersed
      (CurveMap.pairingEvolution B hsu hwindow c hc) x v hv
    have hd := ((hasDerivWithinAt_regularizedCurvature_slice B hsu hwindow c hc ε hε x v hv).mul
      hsp).derivWithin ((uniqueDiffOn_Icc hsu) v hv)
    change derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ *
      c.speed B.family.metric x τ) (Icc s u) v = _ at hd
    simp only [one_mul, zero_mul, zero_add, mul_one] at h
    rw [hd] at h
    simpa only [add_assoc] using h
  have hψa : ContDiff ℝ ∞ (fun x : ℝ => (c.speed B.family.metric x v)⁻¹ *
      deriv (fun z : ℝ => c.regularizedCurvature B.family.metric ε z v) x) := by
    have hsd : ContDiff ℝ ∞ (fun x : ℝ => c.speed B.family.metric x v) :=
      c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv
    exact (hsd.inv (fun x => ne_of_gt (c.speed_pos B.family.metric hc.immersed x v hv))).mul
      ((regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε v hv).iterate_deriv 1)
  have hds_ds_eq : ∀ x : ℝ, c.ds B.family.metric (c.ds B.family.metric
      (c.regularizedCurvature B.family.metric ε)) x v =
      (c.speed B.family.metric x v)⁻¹ * deriv (fun y : ℝ => (c.speed B.family.metric y v)⁻¹ *
        deriv (fun z : ℝ => c.regularizedCurvature B.family.metric ε z v) y) x := fun x => rfl
  have hInt1 : IntervalIntegrable (fun x : ℝ => c.ds B.family.metric (c.ds B.family.metric
      (c.regularizedCurvature B.family.metric ε)) x v * c.speed B.family.metric x v) volume 0 1 := by
    have hfun : (fun x : ℝ => c.ds B.family.metric (c.ds B.family.metric
        (c.regularizedCurvature B.family.metric ε)) x v * c.speed B.family.metric x v) =
        (fun x => deriv (fun y : ℝ => (c.speed B.family.metric y v)⁻¹ *
          deriv (fun z : ℝ => c.regularizedCurvature B.family.metric ε z v) y) x) := by
      funext x
      rw [hds_ds_eq x]
      field_simp [ne_of_gt (c.speed_pos B.family.metric hc.immersed x v hv)]
    rw [hfun]
    exact (hψa.continuous_deriv (by simp)).intervalIntegrable 0 1
  have hInt2 : IntervalIntegrable (fun x : ℝ => ((B.C + B.B₀) *
      c.regularizedCurvature B.family.metric ε x v) * c.speed B.family.metric x v) volume 0 1 :=
    ((continuous_const.mul hRx).mul hspv).intervalIntegrable 0 1
  have hInt3 : IntervalIntegrable (fun x : ℝ => B.C * c.speed B.family.metric x v) volume 0 1 :=
    ((continuous_const.mul hspv)).intervalIntegrable 0 1
  set A : ℝ → ℝ := fun x => c.ds B.family.metric (c.ds B.family.metric
      (c.regularizedCurvature B.family.metric ε)) x v * c.speed B.family.metric x v with hA
  set Bx : ℝ → ℝ := fun x => ((B.C + B.B₀) * c.regularizedCurvature B.family.metric ε x v) *
      c.speed B.family.metric x v with hBx
  set Cc : ℝ → ℝ := fun x => B.C * c.speed B.family.metric x v with hCc
  have hIntA : IntervalIntegrable A volume 0 1 := by rw [hA]; exact hInt1
  have hIntB : IntervalIntegrable Bx volume 0 1 := by rw [hBx]; exact hInt2
  have hIntC : IntervalIntegrable Cc volume 0 1 := by rw [hCc]; exact hInt3
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x : ℝ =>
      derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v *
          c.speed B.family.metric x v +
        c.regularizedCurvature B.family.metric ε x v *
          (-(c.q B.family x v) * c.speed B.family.metric x v))
    (g := fun x : ℝ => A x + (Bx x + Cc x))
    (((hDv.mul hspv).add (hRx.mul (hqv.neg.mul hspv))).intervalIntegrable 0 1)
    (hIntA.add (hIntB.add hIntC))
    (fun x _ => by
      have h := hstep x
      simpa only [hA, hBx, hCc] using h)
  refine hmono.trans ?_
  have e1 : (∫ x in (0 : ℝ)..1, A x + (Bx x + Cc x)) =
      (∫ x in (0 : ℝ)..1, A x) + ((∫ x in (0 : ℝ)..1, Bx x) + ∫ x in (0 : ℝ)..1, Cc x) := by
    have hsplit2 : (∫ x in (0 : ℝ)..1, Bx x + Cc x) =
        (∫ x in (0 : ℝ)..1, Bx x) + ∫ x in (0 : ℝ)..1, Cc x :=
      intervalIntegral.integral_add (f := Bx) (g := Cc) hIntB hIntC
    calc (∫ x in (0 : ℝ)..1, A x + (Bx x + Cc x))
        = (∫ x in (0 : ℝ)..1, A x) + (∫ x in (0 : ℝ)..1, Bx x + Cc x) :=
          intervalIntegral.integral_add (f := A) (g := fun x : ℝ => Bx x + Cc x)
            hIntA (hIntB.add hIntC)
      _ = (∫ x in (0 : ℝ)..1, A x) + ((∫ x in (0 : ℝ)..1, Bx x) + ∫ x in (0 : ℝ)..1, Cc x) := by
          rw [hsplit2]
  have e2 : (∫ x in (0 : ℝ)..1, Bx x) =
      (B.C + B.B₀) * (∫ x in (0 : ℝ)..1,
        c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v) := by
    rw [hBx]
    have hfun2 : (fun x : ℝ => ((B.C + B.B₀) * c.regularizedCurvature B.family.metric ε x v) *
        c.speed B.family.metric x v) = fun x : ℝ => (B.C + B.B₀) *
        (c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v) := by
      funext x
      ring
    rw [hfun2]
    rw [intervalIntegral.integral_const_mul]
  have e3 : (∫ x in (0 : ℝ)..1, Cc x) = B.C * (∫ x in (0 : ℝ)..1, c.speed B.family.metric x v) := by
    rw [hCc]
    exact intervalIntegral.integral_const_mul B.C _
  rw [e1]
  simp only [hA, hBx, hCc]
  rw [integral_ds_ds_regularizedCurvature_mul_speed_eq_zero B hsu hwindow c hc ε hε v hv, zero_add]
  rw [e2, e3]
  simp only [CurveMap.integral, CurveMap.length, one_mul]
  exact le_of_eq (by ring)


private theorem derivWithin_integral_regularizedCurvature
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    derivWithin (fun τ => c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v =
      ∫ x in (0 : ℝ)..1,
        derivWithin (fun τ => c.regularizedCurvature B.family.metric ε x τ) (Icc s u) v *
            c.speed B.family.metric x v +
          c.regularizedCurvature B.family.metric ε x v *
            (-(c.q B.family x v) * c.speed B.family.metric x v) :=
  (hasDerivWithinAt_integral_regularizedCurvature B hsu hwindow c hc ε hε v hv).derivWithin
    ((uniqueDiffOn_Icc hsu) v hv)

private theorem totalCurvature_le_regularized (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (v : ℝ) (hv : v ∈ Icc s u) :
    c.totalCurvature B.family.metric v ≤
        c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v ∧
      c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v ≤
        c.totalCurvature B.family.metric v + ε * c.length B.family.metric v := by
  have hperr := rfs_csf_regularized_curvature B hsu hwindow c hc ε hε
  have hv' : Continuous fun x : ℝ => c.speed B.family.metric x v :=
    (c.speed_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv).continuous
  have hcurv : Continuous fun x : ℝ => c.curvature B.family.metric x v :=
    (Real.continuous_sqrt.comp
      ((c.curvatureSq_contDiff B.family.metric (Icc s u) hc.smooth hc.immersed v hv).continuous))
  have hreg : Continuous fun x : ℝ => c.regularizedCurvature B.family.metric ε x v :=
    (regularizedCurvature_slice_contDiff B hsu hwindow c hc ε hε v hv).continuous
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x : ℝ => c.curvature B.family.metric x v * c.speed B.family.metric x v)
    (g := fun x : ℝ => c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v)
    ((hcurv.mul hv').intervalIntegrable 0 1) ((hreg.mul hv').intervalIntegrable 0 1)
    (fun x _ => mul_le_mul_of_nonneg_right
      (sub_nonneg.mp (hperr.2.1 x v hv).1) (c.speed_nonneg B.family.metric x v))
  have hmono2 := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (f := fun x : ℝ => c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v)
    (g := fun x : ℝ => c.curvature B.family.metric x v * c.speed B.family.metric x v +
      ε * c.speed B.family.metric x v)
    ((hreg.mul hv').intervalIntegrable 0 1)
    (((hcurv.mul hv').add (continuous_const.mul hv')).intervalIntegrable 0 1)
    (fun x _ => by
      have h1 := (hperr.2.1 x v hv).2
      calc c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v
          ≤ (c.curvature B.family.metric x v + ε) * c.speed B.family.metric x v :=
            mul_le_mul_of_nonneg_right (by linarith) (c.speed_nonneg B.family.metric x v)
        _ = c.curvature B.family.metric x v * c.speed B.family.metric x v +
            ε * c.speed B.family.metric x v := by ring)
  constructor
  · have h1 : (∫ x in (0 : ℝ)..1, c.curvature B.family.metric x v * c.speed B.family.metric x v) ≤
        ∫ x in (0 : ℝ)..1, c.regularizedCurvature B.family.metric ε x v * c.speed B.family.metric x v :=
      hmono
    simpa only [CurveMap.totalCurvature, CurveMap.integral] using h1
  · have hsplit : (∫ x in (0 : ℝ)..1, c.curvature B.family.metric x v * c.speed B.family.metric x v +
        ε * c.speed B.family.metric x v) =
        (∫ x in (0 : ℝ)..1, c.curvature B.family.metric x v * c.speed B.family.metric x v) +
          ε * (∫ x in (0 : ℝ)..1, c.speed B.family.metric x v) := by
      rw [intervalIntegral.integral_add
        (f := fun x : ℝ => c.curvature B.family.metric x v * c.speed B.family.metric x v)
        (g := fun x : ℝ => ε * c.speed B.family.metric x v)
        ((hcurv.mul hv').intervalIntegrable 0 1) ((continuous_const.mul hv').intervalIntegrable 0 1)]
      rw [intervalIntegral.integral_const_mul]
    rw [hsplit] at hmono2
    simpa only [CurveMap.totalCurvature, CurveMap.length, CurveMap.integral, one_mul] using hmono2

private theorem regularizedTotalCurvature_sub_le_integral
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t ≤
      c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
        ∫ v in r..t, ((B.C + B.B₀) * c.integral B.family.metric
            (c.regularizedCurvature B.family.metric ε) v + B.C * c.length B.family.metric v) := by
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  have hcont : ContinuousOn (fun τ => c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) τ) (Icc r t) :=
    ((continuousOn_integral_of_continuousOn
      ((regularizedCurvature_joint B hsu hwindow c hc ε hε).continuousOn.mul
        (joint_continuousOn_speed B hwindow c hc))).mono hsub)
  have hderiv : ∀ v ∈ Ico r t, HasDerivWithinAt (fun τ => c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) τ)
      (derivWithin (fun τ => c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v) (Ioi v) v := by
    intro v hv
    have h0 := hasDerivWithinAt_integral_regularizedCurvature B hsu hwindow c hc ε hε v
      ⟨hr.1.trans hv.1, hv.2.le.trans ht.2⟩
    rw [← derivWithin_integral_regularizedCurvature B hsu hwindow c hc ε hε v
      ⟨hr.1.trans hv.1, hv.2.le.trans ht.2⟩] at h0
    exact hasDerivWithinAt_Ioi_of_Icc (A := s) (B := u) (f := fun τ => c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) τ) (x := v) (hr.1.trans hv.1)
      (lt_of_lt_of_le hv.2 ht.2) h0
  have hLcont : ContinuousOn (c.length B.family.metric) (Icc r t) :=
    ((contDiffOn_length B hsu hwindow c hc).continuousOn).mono hsub
  have hφcont : ContinuousOn (fun v : ℝ => (B.C + B.B₀) * c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) v + B.C * c.length B.family.metric v)
      (Icc r t) :=
    (ContinuousOn.const_mul hcont (B.C + B.B₀)).add (ContinuousOn.const_mul hLcont B.C)
  have hmain := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le_Ico hrt hcont hderiv
    (hφcont.integrableOn_compact isCompact_Icc)
    (fun v hv => by
      exact regularizedTotalCurvature_derivWithin_le B hsu hwindow c hc ε hε v
        ⟨hr.1.trans hv.1, hv.2.le.trans ht.2⟩)
  linarith [hmain]





private theorem totalCurvature_sub_le_integral (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    c.totalCurvature B.family.metric t ≤ c.totalCurvature B.family.metric r +
      ∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
        B.C * c.length B.family.metric v) := by
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  have hKnn : 0 ≤ B.C + B.B₀ := by
    rw [RicciBackground.C]
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hLr_nn : 0 ≤ c.length B.family.metric r := length_nonneg B c r
  have hLcont : ContinuousOn (c.length B.family.metric) (Icc r t) :=
    ((contDiffOn_length B hsu hwindow c hc).continuousOn).mono hsub
  have hΘcont : ContinuousOn (c.totalCurvature B.family.metric) (Icc r t) :=
    (continuousOn_totalCurvature B hsu hwindow c hc).mono hsub
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set S₀ : ℝ := ∫ v in r..t, c.length B.family.metric v with hS₀
  have hSnn : 0 ≤ S₀ := by
    rw [hS₀]
    exact intervalIntegral.integral_nonneg hrt (fun v _ => length_nonneg B c v)
  have hden : 0 < 1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀) := by
    nlinarith [hLr_nn, hSnn, mul_nonneg hKnn hSnn]
  set ε : ℝ := δ / (1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀)) with hεdef
  have hεpos : 0 < ε := div_pos hδ hden
  have hεsmall : ε * (c.length B.family.metric r + (B.C + B.B₀) * S₀) ≤ δ := by
    have h2 : ε * (1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀)) ≤ δ := by
      have hX : ε * (1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀)) =
          δ * (1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀)) /
            (1 + (c.length B.family.metric r + (B.C + B.B₀) * S₀)) := by
        rw [hεdef]
        ring
      rw [hX, div_le_iff₀ hden]
    nlinarith [h2, hεpos.le, mul_nonneg hKnn hSnn, hLr_nn]
  have hstar := regularizedTotalCurvature_sub_le_integral B hsu hwindow c hc ε hεpos
    r t hr ht hrt
  have hcmp_t := (totalCurvature_le_regularized B hsu hwindow c hc ε hεpos t ht).1
  have hcmp_r := (totalCurvature_le_regularized B hsu hwindow c hc ε hεpos r hr).2
  have hΘεcont : ContinuousOn (fun v : ℝ => c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) v) (Icc r t) :=
    (continuousOn_integral_of_continuousOn
      ((regularizedCurvature_joint B hsu hwindow c hc ε hεpos).continuousOn.mul
        (joint_continuousOn_speed B hwindow c hc))).mono hsub
  have hInt1 : IntervalIntegrable (fun v : ℝ => (B.C + B.B₀) * c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) v + B.C * c.length B.family.metric v)
      volume r t :=
    ((ContinuousOn.const_mul hΘεcont (B.C + B.B₀)).add
      (ContinuousOn.const_mul hLcont B.C)).intervalIntegrable_of_Icc hrt
  have hInt2 : IntervalIntegrable (fun v : ℝ => (B.C + B.B₀) * c.totalCurvature B.family.metric v +
      B.C * c.length B.family.metric v) volume r t :=
    ((ContinuousOn.const_mul hΘcont (B.C + B.B₀)).add
      (ContinuousOn.const_mul hLcont B.C)).intervalIntegrable_of_Icc hrt
  have hInt3 : IntervalIntegrable (fun v : ℝ => (B.C + B.B₀) * ε * c.length B.family.metric v)
      volume r t :=
    (ContinuousOn.const_mul hLcont ((B.C + B.B₀) * ε)).intervalIntegrable_of_Icc hrt
  have hint_mono : (∫ v in r..t, ((B.C + B.B₀) * c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) v + B.C * c.length B.family.metric v)) ≤
      (∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
          B.C * c.length B.family.metric v) + (B.C + B.B₀) * ε * c.length B.family.metric v) := by
    refine intervalIntegral.integral_mono_on (μ := volume) hrt hInt1 ?_ (fun v hv => ?_)
    · exact (hInt2.add hInt3)
    · have h1 := (totalCurvature_le_regularized B hsu hwindow c hc ε hεpos v (hsub hv)).2
      have hLnn := length_nonneg B c v
      nlinarith [h1, hKnn, hLnn]
  have hsplit3 : (∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
        B.C * c.length B.family.metric v) + (B.C + B.B₀) * ε * c.length B.family.metric v) =
      (∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
          B.C * c.length B.family.metric v)) + (B.C + B.B₀) * ε * S₀ := by
    rw [intervalIntegral.integral_add
      (f := fun v : ℝ => (B.C + B.B₀) * c.totalCurvature B.family.metric v +
        B.C * c.length B.family.metric v)
      (g := fun v : ℝ => (B.C + B.B₀) * ε * c.length B.family.metric v) hInt2 hInt3]
    congr 1
    rw [hS₀]
    have hfun3 : (fun v : ℝ => (B.C + B.B₀) * ε * c.length B.family.metric v) =
        fun v : ℝ => ((B.C + B.B₀) * ε) * c.length B.family.metric v := by
      funext v
      ring
    rw [hfun3]
    rw [intervalIntegral.integral_const_mul]
  linarith [hstar, hcmp_t, hcmp_r, hint_mono, hsplit3.le, hεsmall]





private theorem exp_neg_mul_regularizedTotalCurvature_add_length_le
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u)) (ε : ℝ) (hε : 0 < ε)
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    Real.exp (-(B.C + B.B₀) * (t - r)) *
        (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
          c.length B.family.metric t) ≤
      Real.exp (-(B.C + B.B₀) * (r - r)) *
        (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
          c.length B.family.metric r) := by
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  set V : ℝ → ℝ := fun v => Real.exp (-(B.C + B.B₀) * (v - r)) *
    (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
      c.length B.family.metric v) with hV
  have hΘcont : ContinuousOn (fun v : ℝ => c.integral B.family.metric
      (c.regularizedCurvature B.family.metric ε) v) (Icc r t) :=
    (continuousOn_integral_of_continuousOn
      ((regularizedCurvature_joint B hsu hwindow c hc ε hε).continuousOn.mul
        (joint_continuousOn_speed B hwindow c hc))).mono hsub
  have hLcont : ContinuousOn (c.length B.family.metric) (Icc r t) :=
    ((contDiffOn_length B hsu hwindow c hc).continuousOn).mono hsub
  have hcont : ContinuousOn V (Icc r t) := by
    refine ContinuousOn.mul ?_ (hΘcont.add hLcont)
    exact Real.continuous_exp.comp_continuousOn
      ((continuousOn_id.sub continuousOn_const).const_mul (-(B.C + B.B₀)))
  have hdiff : DifferentiableOn ℝ V (interior (Icc r t)) := by
    intro v hv
    rw [interior_Icc] at hv
    have hvS : v ∈ Icc s u := ⟨hr.1.trans hv.1.le, hv.2.le.trans ht.2⟩
    have hΘ : HasDerivAt (fun τ => c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) τ)
        (derivWithin (fun τ => c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v) v :=
      ((hasDerivWithinAt_integral_regularizedCurvature B hsu hwindow c hc ε hε v hvS).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hr.1 hv.1) (lt_of_lt_of_le hv.2 ht.2))).congr_deriv
        (derivWithin_integral_regularizedCurvature B hsu hwindow c hc ε hε v hvS).symm
    have hLd : HasDerivAt (c.length B.family.metric)
        (derivWithin (c.length B.family.metric) (Icc s u) v) v :=
      ((length_hasDerivWithinAt B hsu hwindow c hc v hvS).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hr.1 hv.1) (lt_of_lt_of_le hv.2 ht.2))).congr_deriv
        (derivWithin_length B hsu hwindow c hc v hvS).symm
    have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-(B.C + B.B₀) * (τ - r)))
        (Real.exp (-(B.C + B.B₀) * (v - r)) * (-(B.C + B.B₀))) v := by
      have h3 : HasDerivAt (fun τ : ℝ => -(B.C + B.B₀) * (τ - r)) (-(B.C + B.B₀)) v := by
        simpa using ((hasDerivAt_id v).sub_const r).const_mul (-(B.C + B.B₀))
      simpa using h3.exp
    exact ((hexp.mul (hΘ.add hLd)).differentiableAt).differentiableWithinAt
  have hderiv : ∀ v ∈ interior (Icc r t), deriv V v ≤ 0 := by
    intro v hv
    rw [interior_Icc] at hv
    have hvS : v ∈ Icc s u := ⟨hr.1.trans hv.1.le, hv.2.le.trans ht.2⟩
    have hΘ : HasDerivAt (fun τ => c.integral B.family.metric
        (c.regularizedCurvature B.family.metric ε) τ)
        (derivWithin (fun τ => c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v) v :=
      ((hasDerivWithinAt_integral_regularizedCurvature B hsu hwindow c hc ε hε v hvS).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hr.1 hv.1) (lt_of_lt_of_le hv.2 ht.2))).congr_deriv
        (derivWithin_integral_regularizedCurvature B hsu hwindow c hc ε hε v hvS).symm
    have hLd : HasDerivAt (c.length B.family.metric)
        (derivWithin (c.length B.family.metric) (Icc s u) v) v :=
      ((length_hasDerivWithinAt B hsu hwindow c hc v hvS).hasDerivAt
        (Icc_mem_nhds (lt_of_le_of_lt hr.1 hv.1) (lt_of_lt_of_le hv.2 ht.2))).congr_deriv
        (derivWithin_length B hsu hwindow c hc v hvS).symm
    have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-(B.C + B.B₀) * (τ - r)))
        (Real.exp (-(B.C + B.B₀) * (v - r)) * (-(B.C + B.B₀))) v := by
      have h3 : HasDerivAt (fun τ : ℝ => -(B.C + B.B₀) * (τ - r)) (-(B.C + B.B₀)) v := by
        simpa using ((hasDerivAt_id v).sub_const r).const_mul (-(B.C + B.B₀))
      simpa using h3.exp
    have hdv : deriv V v = Real.exp (-(B.C + B.B₀) * (v - r)) * (-(B.C + B.B₀)) *
          (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
            c.length B.family.metric v) +
        Real.exp (-(B.C + B.B₀) * (v - r)) *
          (derivWithin (fun τ => c.integral B.family.metric
              (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v +
            derivWithin (c.length B.family.metric) (Icc s u) v) := by
      rw [hV]
      exact (hexp.mul (hΘ.add hLd)).deriv
    rw [hdv]
    have hdΘ := regularizedTotalCurvature_derivWithin_le B hsu hwindow c hc ε hε v hvS
    have hdL := derivWithin_length_le B hsu hwindow c hc v hvS
    have hexp_pos : 0 < Real.exp (-(B.C + B.B₀) * (v - r)) := Real.exp_pos _
    have hfac : -(B.C + B.B₀) *
          (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
            c.length B.family.metric v) +
        (derivWithin (fun τ => c.integral B.family.metric
              (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v +
            derivWithin (c.length B.family.metric) (Icc s u) v) =
        (derivWithin (fun τ => c.integral B.family.metric
              (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v -
            (B.C + B.B₀) * c.integral B.family.metric
              (c.regularizedCurvature B.family.metric ε) v) +
          (derivWithin (c.length B.family.metric) (Icc s u) v -
            (B.C + B.B₀) * c.length B.family.metric v) := by ring
    have hfun4 : Real.exp (-(B.C + B.B₀) * (v - r)) * (-(B.C + B.B₀)) *
          (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
            c.length B.family.metric v) +
        Real.exp (-(B.C + B.B₀) * (v - r)) *
          (derivWithin (fun τ => c.integral B.family.metric
              (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v +
            derivWithin (c.length B.family.metric) (Icc s u) v) =
        Real.exp (-(B.C + B.B₀) * (v - r)) *
          (-(B.C + B.B₀) *
              (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) v +
                c.length B.family.metric v) +
            (derivWithin (fun τ => c.integral B.family.metric
                (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v +
              derivWithin (c.length B.family.metric) (Icc s u) v)) := by
      ring
    rw [hfun4]
    rw [hfac]
    have h1 : derivWithin (fun τ => c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v -
        (B.C + B.B₀) * c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) v ≤ B.C * c.length B.family.metric v := by
      linarith [hdΘ]
    have h2 : derivWithin (c.length B.family.metric) (Icc s u) v -
        (B.C + B.B₀) * c.length B.family.metric v ≤
        -(B.C) * c.length B.family.metric v := by
      linarith [hdL]
    have h3 : (derivWithin (fun τ => c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) τ) (Icc s u) v -
        (B.C + B.B₀) * c.integral B.family.metric
          (c.regularizedCurvature B.family.metric ε) v) +
        (derivWithin (c.length B.family.metric) (Icc s u) v -
          (B.C + B.B₀) * c.length B.family.metric v) ≤ 0 := by
      linarith [h1, h2]
    exact mul_nonpos_of_nonneg_of_nonpos hexp_pos.le h3
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc r t) hcont hdiff hderiv
  exact hanti (left_mem_Icc.mpr hrt) (right_mem_Icc.mpr hrt) hrt

private theorem totalCurvature_add_length_le_exp (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b) (c : CurveMap M)
    (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (r t : ℝ) (hr : r ∈ Icc s u) (ht : t ∈ Icc s u) (hrt : r ≤ t) :
    c.totalCurvature B.family.metric t + c.length B.family.metric t ≤
      Real.exp ((B.C + B.B₀) * (t - r)) *
        (c.totalCurvature B.family.metric r + c.length B.family.metric r) := by
  have hsub : Icc r t ⊆ Icc s u := Icc_subset_Icc hr.1 ht.2
  have hLr_nn : 0 ≤ c.length B.family.metric r := length_nonneg B c r
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hden : 0 < 1 + Real.exp ((B.C + B.B₀) * (t - r)) * c.length B.family.metric r := by
    have := Real.exp_pos ((B.C + B.B₀) * (t - r))
    nlinarith [hLr_nn]
  set ε : ℝ := δ / (1 + Real.exp ((B.C + B.B₀) * (t - r)) * c.length B.family.metric r) with hεdef
  have hεpos : 0 < ε := div_pos hδ hden
  have hsmall : ε * Real.exp ((B.C + B.B₀) * (t - r)) * c.length B.family.metric r ≤ δ := by
    have hexpnn : 0 ≤ Real.exp ((B.C + B.B₀) * (t - r)) * c.length B.family.metric r :=
      mul_nonneg (Real.exp_nonneg _) hLr_nn
    have h2 : ε * (Real.exp ((B.C + B.B₀) * (t - r)) * c.length B.family.metric r) ≤ δ := by
      rw [hεdef]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hδ.le, hexpnn]
    simpa only [mul_assoc] using h2
  have hV := exp_neg_mul_regularizedTotalCurvature_add_length_le B hsu hwindow c hc ε hεpos
    r t hr ht hrt
  have hexpK : 0 < Real.exp ((B.C + B.B₀) * (t - r)) :=
    Real.exp_pos ((B.C + B.B₀) * (t - r))
  have h1 : c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
        c.length B.family.metric t ≤
      Real.exp ((B.C + B.B₀) * (t - r)) *
        (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
          c.length B.family.metric r) := by
    have h := mul_le_mul_of_nonneg_right hV hexpK.le
    have hrr : Real.exp (-(B.C + B.B₀) * (r - r)) = 1 := by simp
    rw [hrr] at h
    have hexp1 : Real.exp (-(B.C + B.B₀) * (t - r)) *
        Real.exp ((B.C + B.B₀) * (t - r)) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    have h1' : (Real.exp (-(B.C + B.B₀) * (t - r)) *
        (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
          c.length B.family.metric t)) * Real.exp ((B.C + B.B₀) * (t - r)) =
        c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
          c.length B.family.metric t := by
      calc (Real.exp (-(B.C + B.B₀) * (t - r)) *
            (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
              c.length B.family.metric t)) * Real.exp ((B.C + B.B₀) * (t - r))
          = (Real.exp (-(B.C + B.B₀) * (t - r)) * Real.exp ((B.C + B.B₀) * (t - r))) *
              (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
                c.length B.family.metric t) := by ring
        _ = c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) t +
              c.length B.family.metric t := by rw [hexp1, one_mul]
    have h2' : (1 * (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
        c.length B.family.metric r)) * Real.exp ((B.C + B.B₀) * (t - r)) =
        Real.exp ((B.C + B.B₀) * (t - r)) *
          (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
            c.length B.family.metric r) := by ring
    rwa [h1', h2'] at h
  have h2 := (totalCurvature_le_regularized B hsu hwindow c hc ε hεpos t ht).1
  have h3 := (totalCurvature_le_regularized B hsu hwindow c hc ε hεpos r hr).2
  have h4 : Real.exp ((B.C + B.B₀) * (t - r)) * (ε * c.length B.family.metric r) ≤ δ := by
    nlinarith [hsmall]
  have hstep : Real.exp ((B.C + B.B₀) * (t - r)) *
      (c.totalCurvature B.family.metric r + ε * c.length B.family.metric r +
        c.length B.family.metric r) ≤
      Real.exp ((B.C + B.B₀) * (t - r)) *
        (c.totalCurvature B.family.metric r + c.length B.family.metric r) + δ := by
    nlinarith [h4]
  have h5 : Real.exp ((B.C + B.B₀) * (t - r)) *
      (c.integral B.family.metric (c.regularizedCurvature B.family.metric ε) r +
        c.length B.family.metric r) ≤
      Real.exp ((B.C + B.B₀) * (t - r)) *
        (c.totalCurvature B.family.metric r + ε * c.length B.family.metric r +
          c.length B.family.metric r) := by
    refine mul_le_mul_of_nonneg_left ?_ hexpK.le
    linarith [h3]
  linarith [h1, h2, h5, hstep]

theorem rfs_csf_integral_bounds (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) :
    ContDiffOn ℝ ∞ (c.length B.family.metric) (Icc s u) ∧
    ContinuousOn (c.totalCurvature B.family.metric) (Icc s u) ∧
    ContinuousOn (c.energy B.family.metric) (Icc s u) ∧
    (∀ t ∈ Icc s u, derivWithin (c.length B.family.metric) (Icc s u) t =
      -c.energy B.family.metric t - c.integral B.family.metric (c.ricciTangent B.family) t) ∧
    (∀ r ∈ Icc s u, ∀ t ∈ Icc r u,
      c.length B.family.metric t ≤ Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      (∫ v in r..t, c.energy B.family.metric v) ≤
        Real.exp (B.B₀ * (t - r)) * c.length B.family.metric r ∧
      c.totalCurvature B.family.metric t ≤ c.totalCurvature B.family.metric r +
        ∫ v in r..t, ((B.C + B.B₀) * c.totalCurvature B.family.metric v +
          B.C * c.length B.family.metric v) ∧
      c.totalCurvature B.family.metric t + c.length B.family.metric t ≤
        Real.exp ((B.C + B.B₀) * (t - r)) *
          (c.totalCurvature B.family.metric r + c.length B.family.metric r)) := by
  refine ⟨contDiffOn_length B hsu hwindow c hc,
    continuousOn_totalCurvature B hsu hwindow c hc,
    continuousOn_energy B hsu hwindow c hc, ?_, ?_⟩
  · intro t ht
    exact derivWithin_length B hsu hwindow c hc t ht
  · rintro r hr t ht
    exact ⟨length_le_exp_mul B hsu hwindow c hc r t hr ⟨hr.1.trans ht.1, ht.2⟩ ht.1,
      energy_integral_le B hsu hwindow c hc r t hr ⟨hr.1.trans ht.1, ht.2⟩ ht.1,
      totalCurvature_sub_le_integral B hsu hwindow c hc r t hr ⟨hr.1.trans ht.1, ht.2⟩ ht.1,
      totalCurvature_add_length_le_exp B hsu hwindow c hc r t hr ⟨hr.1.trans ht.1, ht.2⟩ ht.1⟩

theorem totalCurvature_upper_right_slope
    (B : RicciBackground (I := I) (M := M) D a b)
    (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (t : ℝ) (ht : t ∈ Ico s u) :
    ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Ioo (0 : ℝ) δ, t + h ≤ u →
      (c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t) / h ≤
        (B.C + B.B₀) * c.totalCurvature B.family.metric t +
          B.C * c.length B.family.metric t + ε := by
  obtain ⟨hL, hTheta, _, _, hbounds⟩ := rfs_csf_integral_bounds B hsu hwindow c hc
  let F : ℝ → ℝ := fun v =>
    (B.C + B.B₀) * c.totalCurvature B.family.metric v + B.C * c.length B.family.metric v
  have hF : ContinuousOn F (Icc s u) :=
    (hTheta.const_mul _).add (hL.continuousOn.const_mul _)
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    Metric.continuousWithinAt_iff.mp (hF t ⟨ht.1, ht.2.le⟩) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh htu
  have hth : t ≤ t + h := le_add_of_nonneg_right hh.1.le
  have hsub : Icc t (t + h) ⊆ Icc s u := Icc_subset_Icc ht.1 htu
  have hmono : (∫ v in t..t + h, F v) ≤ h * (F t + ε) := by
    have hle : ∀ v ∈ Icc t (t + h), F v ≤ F t + ε := by
      intro v hv
      have hdist : dist v t < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hv.1)]
        linarith [hv.2, hh.2]
      have habs := hclose (hsub hv) hdist
      rw [Real.dist_eq] at habs
      linarith [(abs_lt.mp habs).2]
    have hint := intervalIntegral.integral_mono_on hth
      ((hF.mono hsub).intervalIntegrable_of_Icc hth)
      (continuous_const.intervalIntegrable (μ := volume) t (t + h)) hle
    simpa only [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul] using hint
  have hint := (hbounds t ⟨ht.1, ht.2.le⟩ (t + h) ⟨hth, htu⟩).2.2.1
  apply (div_le_iff₀ hh.1).mpr
  change c.totalCurvature B.family.metric (t + h) - c.totalCurvature B.family.metric t ≤
    (F t + ε) * h
  change c.totalCurvature B.family.metric (t + h) ≤
    c.totalCurvature B.family.metric t + ∫ v in t..t + h, F v at hint
  nlinarith

section MaxPrincipleHelpers

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_velocity_contMDiff (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (mfderiv 𝓘(ℝ, ℝ) I γ x (1 : ℝ))) := by
  have hunit : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ).tangent ∞
      (fun x : ℝ => TotalSpace.mk' ℝ
        (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ)) := by
    intro x
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_id, ?_⟩
    simpa only [trivializationAt_model_space_apply] using
      (contMDiffAt_const (c := (1 : ℝ)))
  change ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
    (tangentMap 𝓘(ℝ, ℝ) I γ ∘ fun x : ℝ =>
      TotalSpace.mk' ℝ (E := (TangentSpace 𝓘(ℝ, ℝ) : ℝ → Type _)) x (1 : ℝ))
  exact (hγ.contMDiff_tangentMap (le_refl _)).comp hunit

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_inner_contDiff (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V W : ∀ x, TangentSpace I (γ x))
    (hg : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (V x)))
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (γ x) (W x))) :
    ContDiff ℝ ∞ (fun x => g.inner (γ x) (V x) (W x)) := by
  have htotal : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun x => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ)
        (γ x) (g.inner (γ x) (V x) (W x))) := by
    apply ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact g.contMDiff.comp hg
    · exact hV
    · exact hW
  apply contMDiff_iff_contDiff.mp
  intro x
  have hx := htotal x
  simp only [contMDiffAt_totalSpace] at hx
  exact hx.2

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem mp_speed_contDiff (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (hi : c.ImmersedOn (I := I) (Icc s u)) (hc : c.SmoothOn (I := I) (Icc s u))
    (t : ℝ) (ht : t ∈ Icc s u) :
    ContDiff ℝ ∞ (fun x => c.speed g x t) := by
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) :=
    contMDiffOn_univ.mp (CurveMap.space_slice_contMDiffOn c (Icc s u) hc t ht)
  have hX : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun x => TotalSpace.mk' E (c.lift x t) (c.X (I := I) x t)) := by
    have h := mp_velocity_contMDiff (I := I) (fun x => c.lift x t) hγ
    simpa only [CurveMap.X] using h
  have hinner := mp_inner_contDiff (I := I) (g t) (fun x => c.lift x t)
    (fun x => c.X x t) (fun x => c.X x t) hγ hX hX
  exact hinner.sqrt (fun x => ne_of_gt ((g t).pos (c.lift x t) (c.X x t) (hi x t ht)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem mp_deriv_deriv_nonpos_of_isLocalMax {G : ℝ → ℝ} {x₀ : ℝ}
    (hmax : IsLocalMax G x₀) (hG : ContDiffAt ℝ 2 G x₀) :
    deriv (deriv G) x₀ ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hd0 : deriv G x₀ = 0 := hmax.deriv_eq_zero
  have h2 : HasDerivAt (deriv G) (deriv (deriv G) x₀) x₀ :=
    ((hG.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasDerivAt
  have hEv : ∀ᶠ y in 𝓝 x₀, y ≠ x₀ → deriv (deriv G) x₀ / 2 < slope (deriv G) x₀ y := by
    exact eventually_nhdsWithin_iff.mp
      (h2.tendsto_slope.eventually (eventually_gt_nhds (by linarith)))
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hEv
  obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hmax
  obtain ⟨v, hvopen, hvmem, hvCD⟩ :=
    (hG.contDiffWithinAt (s := univ)).contDiffOn' (m := 2) le_rfl (by simp)
  have hvmem' : v ∈ 𝓝 x₀ := hvopen.mem_nhds hvmem
  have hvCD' : ContDiffOn ℝ 2 G v := by simpa using hvCD
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp hvmem'
  have hm : 0 < min δ (min ε ρ) := lt_min hδpos (lt_min hεpos hρpos)
  have hhδ : min δ (min ε ρ) / 2 < δ := by
    have := min_le_left δ (min ε ρ); linarith
  have hhε : min δ (min ε ρ) / 2 < ε := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_left ε ρ; linarith
  have hhρ : min δ (min ε ρ) / 2 < ρ := by
    have h1 := min_le_right δ (min ε ρ); have h2 := min_le_right ε ρ; linarith
  have hderivpos : ∀ y ∈ Ioo x₀ (x₀ + min δ (min ε ρ) / 2), 0 < deriv G y := by
    intro y hy
    have hdist : dist y x₀ < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith [hy.1])]
      linarith [hy.2, hhδ]
    have hne : y ≠ x₀ := by linarith [hy.1]
    have hb := hδ hdist hne
    have hsl : slope (deriv G) x₀ y = deriv G y / (y - x₀) := by
      rw [slope_def_field, hd0, sub_zero]
    rw [hsl] at hb
    have hyx : 0 < y - x₀ := by linarith [hy.1]
    have : 0 < deriv G y / (y - x₀) := by linarith
    exact (div_pos_iff_of_pos_right hyx).mp this
  have hcont : ContinuousOn G (Icc x₀ (x₀ + min δ (min ε ρ) / 2)) := by
    refine hvCD'.continuousOn.mono ?_
    intro y hy
    refine hρ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1, hm], by linarith [hy.2, hhρ]⟩
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
    (fun y hy => by
      rw [interior_Icc] at hy
      exact hderivpos y hy)
  have hlt : G x₀ < G (x₀ + min δ (min ε ρ) / 2) :=
    hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith))
      (by linarith)
  have hle : G (x₀ + min δ (min ε ρ) / 2) ≤ G x₀ :=
    hε (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hm], by linarith [hhε]⟩)
  linarith

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] hBoundary in
private theorem mp_deriv_inv_mul_nonpos {σ φ : ℝ → ℝ} {x₀ L : ℝ}
    (hσ : ContinuousAt σ x₀) (hσpos : 0 < σ x₀)
    (hφ0 : φ x₀ = 0) (hφ : HasDerivAt φ L x₀) (hL : L ≤ 0) :
    deriv (fun y => (σ y)⁻¹ * φ y) x₀ ≤ 0 := by
  have hderiv : HasDerivAt (fun y => (σ y)⁻¹ * φ y) ((σ x₀)⁻¹ * L) x₀ := by
    rw [hasDerivAt_iff_tendsto_slope]
    have h1 : Tendsto (fun y => (σ y)⁻¹) (𝓝[≠] x₀) (𝓝 ((σ x₀)⁻¹)) :=
      (hσ.inv₀ (ne_of_gt hσpos)).tendsto.mono_left inf_le_left
    have h2 : Tendsto (fun y => (φ y - φ x₀) / (y - x₀)) (𝓝[≠] x₀) (𝓝 L) := by
      simpa only [slope_fun_def_field] using hφ.tendsto_slope
    refine Tendsto.congr' ?_ (h1.mul h2)
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [slope_def_field]
    rw [hφ0]
    ring
  rw [hderiv.deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hL

end MaxPrincipleHelpers

theorem rfs_csf_maximum_principle (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      derivWithin (f.lift x) (Icc s u) t ≤
        c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
          A * f.lift x t + F t)
    (hinit : ∀ x, f.lift x s ≤ y s) :
    ∀ x t, t ∈ Icc s u → f.lift x t ≤ y t := by
  classical
  have _ := hBoundary
  have _ : FiniteDimensional ℝ E := inferInstance
  have _ : CompleteSpace E := inferInstance
  have _ : SigmaCompactSpace M := inferInstance
  have _ : T2Space M := inferInstance
  have _ := hd
  have _ := hF
  have hyc : ContinuousOn y (Icc s u) := fun t ht => (hy t ht).continuousWithinAt
  have hliftper : ∀ (x t : ℝ), f.lift (x + 1) t = f.lift x t := by
    intro x t
    simp only [CurveMap.lift, AddCircle.coe_add_period]
  suffices hkey : ∀ η : ℝ, 0 < η → ∀ x ∈ Icc 0 1, ∀ t ∈ Icc s u,
      Real.exp (-A * (t - s)) * (f.lift x t - y t) ≤ η * (1 + (t - s)) by
    intro x t ht
    have hx : f.lift x t = f.lift (Int.fract x) t := by
      have hp : Function.Periodic (fun z => f.lift z t) 1 := fun z => hliftper z t
      have h1 := hp.int_mul ⌊x⌋ (Int.fract x)
      simp only [mul_one] at h1
      rw [Int.fract_add_floor x] at h1
      exact h1
    have hxI : Int.fract x ∈ Icc 0 1 :=
      ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
    have hmain : Real.exp (-A * (t - s)) * (f.lift x t - y t) ≤ 0 := by
      rw [hx]
      have hpos1 : 0 < 1 + (t - s) := by linarith [ht.1]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hη : 0 < ε / (1 + (t - s)) := div_pos hε hpos1
      have h1 := hkey (ε / (1 + (t - s))) hη (Int.fract x) hxI t ht
      have h2 : ε / (1 + (t - s)) * (1 + (t - s)) = ε := by field_simp
      linarith
    nlinarith [hmain, Real.exp_pos (-A * (t - s))]
  intro η hη x₁ hx₁ t₁ ht₁
  by_contra hcon
  rw [not_le] at hcon
  set W : ℝ → ℝ → ℝ := fun x t =>
    Real.exp (-A * (t - s)) * (f.lift x t - y t) - η * (1 + (t - s)) with hW
  have hWper : ∀ x t, W (x + 1) t = W x t := by
    intro x t
    simp only [hW, hliftper x t]
  have hcontW : ContinuousOn (fun p : ℝ × ℝ => W p.1 p.2) (Icc 0 1 ×ˢ Icc s u) := by
    have hexp : ContinuousOn (fun p : ℝ × ℝ => Real.exp (-A * (p.2 - s))) univ :=
      Real.continuous_exp.comp_continuousOn (by fun_prop)
    have hy2 : ContinuousOn (fun p : ℝ × ℝ => y p.2) (univ ×ˢ Icc s u) :=
      hyc.comp (f := fun p : ℝ × ℝ => p.2) continuous_snd.continuousOn
        (fun p hp => hp.2)
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        Real.exp (-A * (p.2 - s)) * (f.lift p.1 p.2 - y p.2)) (univ ×ˢ Icc s u) :=
      (hexp.mono (Set.subset_univ _)).mul (hf.continuousOn.sub hy2)
    have h2 : ContinuousOn (fun p : ℝ × ℝ => η * (1 + (p.2 - s))) univ :=
      (continuous_const.mul (continuous_const.add
        (continuous_snd.sub continuous_const))).continuousOn
    refine (h1.sub (h2.mono (Set.subset_univ _))).mono ?_
    exact Set.prod_mono (Set.subset_univ _) Subset.rfl
  obtain ⟨p₀, hp₀K, hp₀max⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    ⟨(0, s), ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, hsu.le⟩⟩⟩ hcontW
  have hp₀max' : ∀ p ∈ (Icc 0 1 ×ˢ Icc s u),
      W p.1 p.2 ≤ W p₀.1 p₀.2 := fun _ hp => hp₀max hp
  have ht₀ : p₀.2 ∈ Icc s u := hp₀K.2
  have hx₀ : p₀.1 ∈ Icc 0 1 := hp₀K.1
  have hmaxT : IsMaxOn (fun t => W p₀.1 t) (Icc s u) p₀.2 :=
    fun t ht => hp₀max' (p₀.1, t) ⟨hx₀, ht⟩
  have hMpos : 0 < W p₀.1 p₀.2 := by
    have hle : W x₁ t₁ ≤ W p₀.1 p₀.2 := hp₀max' (x₁, t₁) ⟨hx₁, ht₁⟩
    have h1 : 0 < W x₁ t₁ := by
      simp only [hW]
      linarith
    exact lt_of_lt_of_le h1 hle
  have hWs : W p₀.1 s < 0 := by
    have h1 : W p₀.1 s = (f.lift p₀.1 s - y s) - η := by
      simp only [hW, sub_self, mul_zero, Real.exp_zero, one_mul, add_zero, mul_one]
    rw [h1]
    linarith [hinit p₀.1, hη]
  have ht₀pos : s < p₀.2 := by
    rcases lt_or_eq_of_le ht₀.1 with h | h
    · exact h
    · exfalso
      rw [← h] at hMpos
      linarith
  have huniq : UniqueDiffWithinAt ℝ (Icc s u) p₀.2 := (uniqueDiffOn_Icc hsu) p₀.2 ht₀
  have hfdiff : HasDerivWithinAt (fun t => f.lift p₀.1 t)
      (derivWithin (f.lift p₀.1) (Icc s u) p₀.2) (Icc s u) p₀.2 := by
    have hcomp : ContDiffWithinAt ℝ ∞ (fun t : ℝ => f.lift p₀.1 t) (Icc s u) p₀.2 :=
      (hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩).comp p₀.2
        (contDiffWithinAt_const.prodMk contDiffWithinAt_id)
        (fun t ht => ⟨trivial, ht⟩)
    exact (hcomp.differentiableWithinAt (by norm_num)).hasDerivWithinAt
  have hderivW : HasDerivWithinAt (fun t => W p₀.1 t)
      (Real.exp (-A * (p₀.2 - s)) * (-A * (f.lift p₀.1 p₀.2 - y p₀.2) +
        (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))) - η)
      (Icc s u) p₀.2 := by
    have h1 : HasDerivWithinAt (fun t : ℝ => Real.exp (-A * (t - s)))
        (Real.exp (-A * (p₀.2 - s)) * (-A)) (Icc s u) p₀.2 := by
      have h2 : HasDerivAt (fun t : ℝ => -A * (t - s)) (-A) p₀.2 := by
        simpa using ((hasDerivAt_id p₀.2).sub_const s).const_mul (-A)
      exact h2.exp.hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t => f.lift p₀.1 t - y t)
        (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2))
        (Icc s u) p₀.2 :=
      hfdiff.sub (hy p₀.2 ht₀)
    have h4 : HasDerivWithinAt (fun t : ℝ => η * (1 + (t - s))) η (Icc s u) p₀.2 := by
      have h5 : HasDerivAt (fun t : ℝ => η * (1 + (t - s))) η p₀.2 := by
        simpa using (((hasDerivAt_id p₀.2).sub_const s).const_add 1).const_mul η
      exact h5.hasDerivWithinAt
    have h6 := (h1.mul h3).sub h4
    refine h6.congr_deriv ?_
    ring
  have hnonneg : 0 ≤ derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 := by
    have htend := hasDerivWithinAt_iff_tendsto_slope.mp hderivW
    have hsub : (Icc s u \ {p₀.2}) ∩ Iio p₀.2 ⊆ Icc s u \ {p₀.2} :=
      Set.inter_subset_left
    have htend2 := htend.mono_left (nhdsWithin_mono p₀.2 hsub)
    have hcl : p₀.2 ∈ closure ((Icc s u \ {p₀.2}) ∩ Iio p₀.2) := by
      have hsub' : Ioo s p₀.2 ⊆ (Icc s u \ {p₀.2}) ∩ Iio p₀.2 := by
        intro t ht
        exact ⟨⟨⟨ht.1.le, ht.2.le.trans ht₀.2⟩, ne_of_lt ht.2⟩, ht.2⟩
      have h2 : p₀.2 ∈ closure (Ioo s p₀.2) := by
        rw [closure_Ioo (ne_of_lt ht₀pos)]
        exact right_mem_Icc.mpr ht₀pos.le
      exact closure_mono hsub' h2
    rw [hderivW.derivWithin huniq]
    refine ge_of_tendsto (hx := mem_closure_iff_nhdsWithin_neBot.mp hcl) htend2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    obtain ⟨⟨htJ, htne⟩, htlt⟩ := ht
    have hlt : t < p₀.2 := htlt
    have hle : W p₀.1 t ≤ W p₀.1 p₀.2 := hmaxT htJ
    rw [slope_def_field]
    exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, by linarith⟩)
  have hlocalW : ∀ᶠ x in 𝓝 p₀.1, W x p₀.2 ≤ W p₀.1 p₀.2 := by
    rw [Metric.eventually_nhds_iff]
    refine ⟨1 / 2, by norm_num, fun y hy => ?_⟩
    rw [Real.dist_eq, abs_lt] at hy
    by_cases hy01 : y ∈ Icc 0 1
    · exact hp₀max' (y, p₀.2) ⟨hy01, ht₀⟩
    · rw [mem_Icc] at hy01
      have hy01' : 0 ≤ y → 1 < y := by
        intro h
        by_contra h1
        exact hy01 ⟨h, not_lt.mp h1⟩
      rcases lt_or_ge y 0 with hlt | hge
      · have hy1 : y + 1 ∈ Icc 0 1 :=
          ⟨by linarith [hy.1, hx₀.1], by linarith [hlt]⟩
        rw [← hWper y p₀.2]
        exact hp₀max' (y + 1, p₀.2) ⟨hy1, ht₀⟩
      · have hgt : 1 < y := hy01' hge
        have hy1 : y - 1 ∈ Icc 0 1 :=
          ⟨by linarith [hgt], by linarith [hy.2, hx₀.2]⟩
        have hshift : y - 1 + 1 = y := by ring
        rw [← hshift, hWper (y - 1) p₀.2]
        exact hp₀max' (y - 1, p₀.2) ⟨hy1, ht₀⟩
  have hlocmaxW : IsLocalMax (fun x => W x p₀.2) p₀.1 := hlocalW
  have hlocmaxf : IsLocalMax (fun x => f.lift x p₀.2) p₀.1 := by
    filter_upwards [hlocalW] with z hz
    simp only [hW] at hz
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have h2 : Real.exp (-A * (p₀.2 - s)) * (f.lift z p₀.2 - y p₀.2) ≤
        Real.exp (-A * (p₀.2 - s)) * (f.lift p₀.1 p₀.2 - y p₀.2) := by linarith
    have h3 := le_of_mul_le_mul_left h2 hexp
    linarith
  have hslice2 : ContDiffAt ℝ 2 (fun x => f.lift x p₀.2) p₀.1 := by
    have hjoint : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2)
        (univ ×ˢ Icc s u) (p₀.1, p₀.2) := hf (p₀.1, p₀.2) ⟨trivial, ht₀⟩
    have hsnd : ContDiffWithinAt ℝ ∞ (fun x : ℝ => (x, p₀.2)) univ p₀.1 := by
      fun_prop
    have hmaps : MapsTo (fun x : ℝ => (x, p₀.2)) univ (univ ×ˢ Icc s u) :=
      fun _ _ => ⟨trivial, ht₀⟩
    have hcomp := hjoint.comp p₀.1 hsnd hmaps
    exact ((contDiffWithinAt_univ.mp hcomp).of_le (m := 2)
      (WithTop.coe_le_coe.mpr le_top))
  have hderiv0 : deriv (fun x => f.lift x p₀.2) p₀.1 = 0 := hlocmaxf.deriv_eq_zero
  have hsecond : deriv (deriv (fun x => f.lift x p₀.2)) p₀.1 ≤ 0 :=
    mp_deriv_deriv_nonpos_of_isLocalMax hlocmaxf hslice2
  have hds0 : c.ds g f.lift p₀.1 p₀.2 = 0 := by
    simp only [CurveMap.ds, hderiv0, mul_zero]
  have hdsds : c.ds g (c.ds g f.lift) p₀.1 p₀.2 ≤ 0 := by
    have hσcont : ContinuousAt (fun y => c.speed g y p₀.2) p₀.1 :=
      (mp_speed_contDiff c g hi hc p₀.2 ht₀).continuous.continuousAt
    have hσpos : 0 < c.speed g p₀.1 p₀.2 := c.speed_pos g hi p₀.1 p₀.2 ht₀
    have hφderiv : HasDerivAt (fun y => deriv (fun z => f.lift z p₀.2) y)
        (deriv (deriv (fun z => f.lift z p₀.2)) p₀.1) p₀.1 :=
      ((hslice2.derivWithin (m := 1) (by norm_num)).differentiableAt
        (by norm_num)).hasDerivAt
    have hkey := mp_deriv_inv_mul_nonpos hσcont hσpos hderiv0 hφderiv hsecond
    have hfund : c.ds g (c.ds g f.lift) p₀.1 p₀.2 =
        (c.speed g p₀.1 p₀.2)⁻¹ *
          deriv (fun y => (c.speed g y p₀.2)⁻¹ * deriv (fun z => f.lift z p₀.2) y) p₀.1 :=
      rfl
    rw [hfund]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hσpos.le) hkey
  have hbound : derivWithin (fun t => W p₀.1 t) (Icc s u) p₀.2 < 0 := by
    rw [hderivW.derivWithin huniq]
    have hexp : 0 < Real.exp (-A * (p₀.2 - s)) := Real.exp_pos _
    have hpde' := hpde p₀.1 p₀.2 ht₀
    have hA : -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (derivWithin (f.lift p₀.1) (Icc s u) p₀.2 - (A * y p₀.2 + F p₀.2)) ≤
        -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
            d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 +
            A * f.lift p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) := by linarith
    have hB : -A * (f.lift p₀.1 p₀.2 - y p₀.2) +
          (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
            d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 +
            A * f.lift p₀.1 p₀.2 + F p₀.2 - (A * y p₀.2 + F p₀.2)) =
        c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
          d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2 := by ring
    have hC : Real.exp (-A * (p₀.2 - s)) * (c.ds g (c.ds g f.lift) p₀.1 p₀.2 +
          d.lift p₀.1 p₀.2 * c.ds g f.lift p₀.1 p₀.2) ≤ 0 := by
      rw [hds0, mul_zero, add_zero]
      exact mul_nonpos_of_nonneg_of_nonpos hexp.le hdsds
    have hD := mul_le_mul_of_nonneg_left (hA.trans_eq hB) hexp.le
    linarith
  linarith [hnonneg, hbound]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] hBoundary in
private theorem ds_neg (g : ℝ → SmoothRiemannianMetric I M)
    (c : CurveMap M) (f : ℝ → ℝ → ℝ) :
    c.ds g (fun x t => -f x t) = fun x t => -c.ds g f x t := by
  funext x t
  simp only [CurveMap.ds, deriv.fun_neg, mul_neg]

theorem scalar_lower_comparison (g : ℝ → SmoothRiemannianMetric I M)
    (hsu : s < u) (c : CurveMap M) (hc : c.SmoothOn (I := I) (Icc s u))
    (hi : c.ImmersedOn (I := I) (Icc s u))
    (f d : CurveMap ℝ)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => f.lift p.1 p.2) (univ ×ˢ Icc s u))
    (hd : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => d.lift p.1 p.2) (univ ×ˢ Icc s u))
    (A : ℝ) (F y : ℝ → ℝ) (hF : ContinuousOn F (Icc s u))
    (hy : ∀ t ∈ Icc s u, HasDerivWithinAt y (A * y t + F t) (Icc s u) t)
    (hpde : ∀ x t, t ∈ Icc s u →
      c.ds g (c.ds g f.lift) x t + d.lift x t * c.ds g f.lift x t +
        A * f.lift x t + F t ≤ derivWithin (f.lift x) (Icc s u) t)
    (hinit : ∀ x, y s ≤ f.lift x s) :
    ∀ x t, t ∈ Icc s u → y t ≤ f.lift x t := by
  let fn : CurveMap ℝ := fun z t => -f z t
  have hfn : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => fn.lift p.1 p.2) (univ ×ˢ Icc s u) := hf.neg
  have hyn : ∀ t ∈ Icc s u,
      HasDerivWithinAt (fun r => -y r) (A * (-y t) + (-F t)) (Icc s u) t := by
    intro t ht
    convert! (hy t ht).neg using 1
    simp only [neg_add, mul_neg]
  have hpden : ∀ x t, t ∈ Icc s u →
      derivWithin (fn.lift x) (Icc s u) t ≤
        c.ds g (c.ds g fn.lift) x t + d.lift x t * c.ds g fn.lift x t +
          A * fn.lift x t + (-F t) := by
    intro x t ht
    have h := hpde x t ht
    change derivWithin (fun r => -f.lift x r) (Icc s u) t ≤
      c.ds g (c.ds g (fun z r => -f.lift z r)) x t +
        d.lift x t * c.ds g (fun z r => -f.lift z r) x t + A * (-f.lift x t) + (-F t)
    rw [derivWithin.fun_neg, ds_neg g c f.lift, ds_neg g c (c.ds g f.lift)]
    nlinarith
  have hn := rfs_csf_maximum_principle g hsu c hc hi fn d hfn hd A
    (fun r => -F r) (fun r => -y r) hF.neg hyn hpden (fun x => neg_le_neg (hinit x))
  intro x t ht
  exact neg_le_neg_iff.mp (hn x t ht)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
