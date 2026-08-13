import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.LocalStrong
import DifferentialGeometry.Geometry.Boundary.DefiningFunction

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def strongBarrierPhase
    (rho : M → Real) (kappa tau : Real) (t : Real) (x : M) : Real :=
  rho x + kappa * (t - tau) ^ 2

private def strongBarrier
    (rho : M → Real) (epsilon alpha R kappa tau : Real)
    (t : Real) (x : M) : Real :=
  epsilon * (Real.exp (-alpha * strongBarrierPhase rho kappa tau t x) -
    Real.exp (-alpha * R))

private def strongStaticMetricFamily
    (g : SmoothRiemannianMetric I M) :
    MetricConnectionFamily (I := I) (M := M) Real where
  metric := fun _ => g
  connection := fun _ => LeviCivita (I := I) g
  metricCompatible := by
    intro t
    simpa using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)

@[simp] private theorem strongStaticMetricFamily_metric
    (g : SmoothRiemannianMetric I M) (t : Real) :
    (strongStaticMetricFamily (I := I) g).metric t = g := by
  rfl

private theorem strongBarrier_joint_continuous
    {rho : M → Real} (hrho : Continuous rho)
    (epsilon alpha R kappa tau : Real) :
    Continuous (fun p : Real × M =>
      strongBarrier rho epsilon alpha R kappa tau p.1 p.2) := by
  unfold strongBarrier strongBarrierPhase
  fun_prop

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem strongBarrier_slice_contMDiff
    {rho : M → Real} (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (epsilon alpha R kappa tau t : Real) :
    ContMDiff I 𝓘(Real, Real) ∞
      (strongBarrier rho epsilon alpha R kappa tau t) := by
  have harg : ContMDiff I 𝓘(Real, Real) ∞
      (fun x => -alpha * (rho x + kappa * (t - tau) ^ 2)) :=
    contMDiff_const.mul (hrho.add contMDiff_const)
  exact contMDiff_const.mul
    ((Real.contDiff_exp.contMDiff.comp harg).sub contMDiff_const)

omit [TopologicalSpace M] [IsManifold I ∞ M] in
private theorem strongBarrier_time_differentiable
    (rho : M → Real) (epsilon alpha R kappa tau : Real) (x : M) :
    Differentiable Real
      (fun t => strongBarrier rho epsilon alpha R kappa tau t x) := by
  unfold strongBarrier strongBarrierPhase
  fun_prop

omit [TopologicalSpace M] [IsManifold I ∞ M] in
private theorem strongBarrierPhase_time_derivWithin
    (rho : M → Real) {T kappa tau t : Real}
    (hT : 0 < T) (ht : t ∈ Set.Icc 0 T) (x : M) :
    derivWithin (fun s => strongBarrierPhase rho kappa tau s x)
        (Set.Icc 0 T) t = 2 * kappa * (t - tau) := by
  have hderiv : HasDerivAt
      (fun s => strongBarrierPhase rho kappa tau s x)
      (2 * kappa * (t - tau)) t := by
    unfold strongBarrierPhase
    convert (hasDerivAt_const t (rho x)).add
      (((hasDerivAt_id t).sub_const tau).pow 2 |>.const_mul kappa) using 1
    simp only [id_eq]
    ring
  exact hderiv.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht)

private theorem strongBarrierPhase_gradient
    (g : SmoothRiemannianMetric I M) {rho : M → Real}
    {x : M}
    (hrho : MDifferentiableAt I 𝓘(Real, Real) rho x)
    (kappa tau t : Real) :
    gradientFun (I := I) g (strongBarrierPhase rho kappa tau t) x =
      gradientFun (I := I) g rho x := by
  rw [show strongBarrierPhase rho kappa tau t =
      fun y => rho y + kappa * (t - tau) ^ 2 from rfl]
  rw [gradientFun_add (I := I) g hrho mdifferentiableAt_const]
  rw [gradientFun_const, add_zero]

private theorem strongBarrierPhase_parabolicOperator
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {rho : M → Real} (hrho : ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) rho x)
    {kappa tau t : Real} (ht : t ∈ Set.Icc 0 T) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X
        (strongBarrierPhase rho kappa tau) t x =
      2 * kappa * (t - tau) -
        heatOperatorWithDrift (I := I) G t (X t) rho x := by
  unfold parabolicOperatorWithDrift
  rw [strongBarrierPhase_time_derivWithin rho hT ht x]
  have hheat : heatOperatorWithDrift (I := I) G t (X t)
      (strongBarrierPhase rho kappa tau t) x =
      heatOperatorWithDrift (I := I) G t (X t) rho x := by
    have hsub := heatOperatorWithDrift_sub_const (I := I)
      G t (X t) (-(kappa * (t - tau) ^ 2)) hrho x
    simpa only [sub_neg_eq_add] using hsub
  rw [hheat]

private def expNegMulStrong (alpha : Real) : Real → Real :=
  Real.exp ∘ ((-alpha) * ·)

private theorem expNegMulStrong_hasDerivAt (alpha s : Real) :
    HasDerivAt (expNegMulStrong alpha)
      (-alpha * Real.exp (-alpha * s)) s := by
  have hraw := (Real.hasDerivAt_exp (-alpha * s)).comp s
    ((hasDerivAt_id s).const_mul (-alpha))
  have hev : expNegMulStrong alpha =ᶠ[nhds s]
      Real.exp ∘ HMul.hMul (-alpha) :=
    Filter.Eventually.of_forall fun y => by simp [expNegMulStrong]
  have h := hraw.congr_of_eventuallyEq hev
  convert h using 1
  ring

private theorem expNegMulStrong_deriv (alpha s : Real) :
    deriv (expNegMulStrong alpha) s = -alpha * Real.exp (-alpha * s) :=
  (expNegMulStrong_hasDerivAt alpha s).deriv

private theorem expNegMulStrong_secondDeriv (alpha s : Real) :
    deriv (deriv (expNegMulStrong alpha)) s =
      alpha ^ 2 * Real.exp (-alpha * s) := by
  have hderiv : deriv (expNegMulStrong alpha) =
      fun z => -alpha * Real.exp (-alpha * z) := by
    funext z
    exact expNegMulStrong_deriv alpha z
  have harg := (hasDerivAt_id s).const_mul (-alpha)
  have hexp := (Real.hasDerivAt_exp (-alpha * s)).comp s harg
  have hs := hexp.const_mul (-alpha)
  rw [hderiv]
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hs.deriv

private theorem exp_strongBarrierPhase_parabolicOperator
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (alpha : Real) {kappa tau t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X
        (fun s y => Real.exp
          (-alpha * strongBarrierPhase rho kappa tau s y)) t x =
      Real.exp (-alpha * strongBarrierPhase rho kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x)) := by
  let phi := expNegMulStrong alpha
  have hphi : Differentiable Real phi := by
    intro s
    exact (expNegMulStrong_hasDerivAt alpha s).differentiableAt
  have hphi' : DifferentiableAt Real (deriv phi)
      (strongBarrierPhase rho kappa tau t x) := by
    have hd : deriv phi = fun s => -alpha * Real.exp (-alpha * s) := by
      funext s
      exact expNegMulStrong_deriv alpha s
    rw [hd]
    fun_prop
  have htime : DifferentiableWithinAt Real
      (fun s => strongBarrierPhase rho kappa tau s x)
      (Set.Icc 0 T) t := by
    unfold strongBarrierPhase
    fun_prop
  have hphase_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t)
        (strongBarrierPhase rho kappa tau t) y) x := by
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (hrho.add contMDiff_const) x
  have hchain := parabolic_comp (I := I) G T X
    (strongBarrierPhase rho kappa tau) t x hphi hphi' htime
    (fun y => (hrho.add contMDiff_const).mdifferentiable (by simp) y)
    hphase_grad
  rw [strongBarrierPhase_parabolicOperator (I := I) G T hT X
    (fun y => hrho.mdifferentiable (by simp) y) ht x] at hchain
  rw [expNegMulStrong_deriv, expNegMulStrong_secondDeriv] at hchain
  unfold gradientAt at hchain
  rw [strongBarrierPhase_gradient (I := I) (G.metric t)
    (hrho.mdifferentiable (by simp) x) kappa tau t] at hchain
  have hchain' :
      parabolicOperatorWithDrift (I := I) G T X
          (fun s y => Real.exp
            (-alpha * strongBarrierPhase rho kappa tau s y)) t x =
        -alpha * Real.exp (-alpha * strongBarrierPhase rho kappa tau t x) *
            (2 * kappa * (t - tau) -
              heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * Real.exp
              (-alpha * strongBarrierPhase rho kappa tau t x) *
            (G.metric t).inner x
              (gradientFun (I := I) (G.metric t) rho x)
              (gradientFun (I := I) (G.metric t) rho x) := by
    simpa [phi, expNegMulStrong, gradientAt_eq] using hchain
  rw [hchain']
  ring

private theorem strongBarrier_parabolicOperator
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (epsilon alpha R : Real) {kappa tau t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    parabolicOperatorWithDrift (I := I) G T X
        (strongBarrier rho epsilon alpha R kappa tau) t x =
      epsilon * Real.exp
          (-alpha * strongBarrierPhase rho kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x)) := by
  let e : Real → M → Real := fun s y => Real.exp
    (-alpha * strongBarrierPhase rho kappa tau s y)
  let q : Real → M → Real := fun s y => e s y - Real.exp (-alpha * R)
  have he_smooth : ContMDiff I 𝓘(Real, Real) ∞ (e t) := by
    exact Real.contDiff_exp.contMDiff.comp
      (contMDiff_const.mul (hrho.add contMDiff_const))
  have he_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (e t) y := by
    intro y
    exact he_smooth.mdifferentiable (by simp) y
  have he_time : DifferentiableWithinAt Real (fun s => e s x)
      (Set.Icc 0 T) t := by
    dsimp [e, strongBarrierPhase]
    fun_prop
  have hc_time : DifferentiableWithinAt Real
      (fun _ : Real => Real.exp (-alpha * R)) (Set.Icc 0 T) t :=
    differentiableWithinAt_const _
  have hsub := parabolic_sub_time_curve_identity (I := I)
    G T X e (fun _ => Real.exp (-alpha * R)) t
    he_space x he_time hc_time
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
    (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
  have hc_deriv : derivWithin (fun _ : Real => Real.exp (-alpha * R))
      (Set.Icc 0 T) t = 0 :=
    (hasDerivWithinAt_const (x := t) (s := Set.Icc 0 T)
      (c := Real.exp (-alpha * R))).derivWithin huniq
  rw [hc_deriv, sub_zero] at hsub
  have hq_time : DifferentiableWithinAt Real (fun s => q s x)
      (Set.Icc 0 T) t := he_time.sub hc_time
  have hq_smooth : ContMDiff I 𝓘(Real, Real) ∞ (q t) :=
    he_smooth.sub contMDiff_const
  have hq_space : ∀ y : M,
      MDifferentiableAt I 𝓘(Real, Real) (q t) y := by
    intro y
    exact hq_smooth.mdifferentiable (by simp) y
  have hq_grad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (q t) y) x :=
    gradientFun_mdiffAt (I := I) (G.metric t) hq_smooth x
  have hscale := parabolic_smul (I := I) G T X epsilon q t x
    hq_time hq_space hq_grad
  have hexp := exp_strongBarrierPhase_parabolicOperator (I := I)
    G T hT X hrho alpha (kappa := kappa) (tau := tau) ht x
  change parabolicOperatorWithDrift (I := I) G T X q t x =
    parabolicOperatorWithDrift (I := I) G T X e t x at hsub
  change parabolicOperatorWithDrift (I := I) G T X
      (strongBarrier rho epsilon alpha R kappa tau) t x =
    epsilon * parabolicOperatorWithDrift (I := I) G T X q t x at hscale
  rw [hsub, hexp] at hscale
  calc
    parabolicOperatorWithDrift (I := I) G T X
        (strongBarrier rho epsilon alpha R kappa tau) t x =
      epsilon * (Real.exp
          (-alpha * strongBarrierPhase rho kappa tau t x) *
        (-alpha * (2 * kappa * (t - tau) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x))) := hscale
    _ = _ := by ring

private theorem strong_derivWithin_nonpos_at_Icc_min_of_pos
    {phi : Real → Real} {T t : Real}
    (hmin : IsLocalMinOn phi (Set.Icc 0 T) t)
    (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
    (_hphi : DifferentiableWithinAt Real phi (Set.Icc 0 T) t) :
    derivWithin phi (Set.Icc 0 T) t ≤ 0 := by
  have hdir : (0 : Real) - t ∈ posTangentConeAt (Set.Icc 0 T) t := by
    have hseg : segment Real t 0 ⊆ Set.Icc 0 T := by
      rw [segment_symm, segment_eq_Icc ht.1]
      intro y hy
      exact ⟨hy.1, hy.2.trans ht.2⟩
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg : 0 ≤
      (fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) :=
    hmin.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real) (0 - t) =
        (0 - t) * derivWithin phi (Set.Icc 0 T) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Set.Icc 0 T) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc 0 T) t : Real →L[Real] Real).map_smul
        (0 - t) (1 : Real))
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg (sub_neg.mpr htpos)

omit [TopologicalSpace M] in
private theorem strong_derivWithin_add_eps_mul_time
    {w : Real → M → Real} {T t epsilon : Real} {x : M}
    (huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t)
    (hw : DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t) :
    derivWithin (fun s => w s x + epsilon * s) (Set.Icc 0 T) t =
      derivWithin (fun s => w s x) (Set.Icc 0 T) t + epsilon := by
  have hlinear : DifferentiableWithinAt Real (fun s => epsilon * s)
      (Set.Icc 0 T) t := by
    simpa using
      (differentiableWithinAt_id' (s := Set.Icc 0 T) (x := t)).const_mul epsilon
  have hderiv_linear : derivWithin (fun s => epsilon * s)
      (Set.Icc 0 T) t = epsilon := by
    rw [derivWithin_const_mul epsilon (d := fun s : Real => s)
      (s := Set.Icc 0 T) (x := t) differentiableWithinAt_id]
    rw [derivWithin_id' (s := Set.Icc 0 T) (x := t) huniq]
    ring
  rw [derivWithin_fun_add hw hlinear, hderiv_linear]

theorem strict_barrier_on_compact_set_of_isInteriorPoint
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKinterior : interior K ⊆ I.interior M)
    (w : Real → M → Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ K))
    (hw0 : ∀ x ∈ K, 0 ≤ w 0 x)
    (hw_boundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K, 0 ≤ w t x)
    (hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      w t x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, 0 ≤ w t x := by
  have hbarrier : ∀ epsilon : Real, 0 < epsilon →
      ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, 0 ≤ w t x + epsilon * t := by
    intro epsilon hepsilon
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨tb, htb, xb, hxbK, hbneg⟩
    let Phi : Real × M → Real := fun p => w p.1 p.2 + epsilon * p.1
    have hPhi_cont : ContinuousOn Phi (Set.Icc 0 T ×ˢ K) := by
      exact hw_cont.add (continuous_const.mul continuous_fst).continuousOn
    have hslab_compact : IsCompact (Set.Icc 0 T ×ˢ K) :=
      isCompact_Icc.prod hK
    have hslab_nonempty : (Set.Icc 0 T ×ˢ K).Nonempty := by
      rcases hKne with ⟨x, hx⟩
      exact ⟨(0, x), ⟨⟨le_rfl, hT⟩, hx⟩⟩
    obtain ⟨p0, hp0, hp0min⟩ :=
      hslab_compact.exists_isMinOn hslab_nonempty hPhi_cont
    rcases p0 with ⟨t0, x0⟩
    have ht0 : t0 ∈ Set.Icc 0 T := hp0.1
    have hx0K : x0 ∈ K := hp0.2
    have hPhi_bad : Phi (t0, x0) ≤ Phi (tb, xb) :=
      hp0min ⟨htb, hxbK⟩
    have hPhi_neg : Phi (t0, x0) < 0 := lt_of_le_of_lt hPhi_bad hbneg
    have ht0_ne : t0 ≠ 0 := by
      intro ht0zero
      have hnonneg : 0 ≤ Phi (t0, x0) := by
        simp [Phi, ht0zero, hw0 x0 hx0K]
      exact not_lt_of_ge hnonneg hPhi_neg
    have ht0pos : 0 < t0 := lt_of_le_of_ne ht0.1 (Ne.symm ht0_ne)
    have hTpos : 0 < T := lt_of_lt_of_le ht0pos ht0.2
    have hx0_not_boundary : x0 ∉ frontier K := by
      intro hxfrontier
      have hw_nonneg := hw_boundary t0 ht0 x0 hxfrontier
      have heps_nonneg : 0 ≤ epsilon * t0 :=
        mul_nonneg hepsilon.le ht0.1
      dsimp [Phi] at hPhi_neg
      linarith
    have hx0int : x0 ∈ interior K :=
      (mem_interior_iff_notMem_frontier hx0K).mpr hx0_not_boundary
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t0 :=
      (uniqueDiffOn_Icc hTpos).uniqueDiffWithinAt ht0
    have htime_min : IsMinOn (fun s => w s x0 + epsilon * s)
        (Set.Icc 0 T) t0 := by
      intro s hs
      exact hp0min (show (s, x0) ∈ Set.Icc 0 T ×ˢ K from ⟨hs, hx0K⟩)
    have htime_diff : DifferentiableWithinAt Real
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 :=
      (hw_time t0 ht0 ht0pos x0 hx0int).add
        ((differentiableWithinAt_id' (s := Set.Icc 0 T) (x := t0)).const_mul epsilon)
    have hderiv_nonpos : derivWithin
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 ≤ 0 :=
      strong_derivWithin_nonpos_at_Icc_min_of_pos
        htime_min.localize ht0 ht0pos htime_diff
    have hderiv_eq : derivWithin
        (fun s => w s x0 + epsilon * s) (Set.Icc 0 T) t0 =
        derivWithin (fun s => w s x0) (Set.Icc 0 T) t0 + epsilon :=
      strong_derivWithin_add_eps_mul_time (M := M) huniq
        (hw_time t0 ht0 ht0pos x0 hx0int)
    have hw_deriv_le : derivWithin (fun s => w s x0)
        (Set.Icc 0 T) t0 ≤ -epsilon := by
      linarith
    have hwneg : w t0 x0 < 0 := by
      have heps_nonneg : 0 ≤ epsilon * t0 :=
        mul_nonneg hepsilon.le ht0.1
      dsimp [Phi] at hPhi_neg
      linarith
    have hspatial_min : IsLocalMin (w t0) x0 := by
      unfold IsLocalMin IsMinFilter
      have hKnhds : K ∈ nhds x0 :=
        mem_of_superset (isOpen_interior.mem_nhds hx0int) interior_subset
      filter_upwards [hKnhds] with y hy
      have hymin := hp0min (show (t0, y) ∈ Set.Icc 0 T ×ˢ K from ⟨ht0, hy⟩)
      dsimp [Phi] at hymin
      linarith
    have hheat_nonneg : 0 ≤
        heatOperatorWithDrift (I := I) G t0 (X t0) (w t0) x0 :=
      heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
        (I := I) G t0 (X t0) hspatial_min (hKinterior hx0int)
        (hw_mdiff t0 ht0 ht0pos x0 hx0int)
        (by
          filter_upwards [isOpen_interior.mem_nhds hx0int] with y hy
          exact hw_mdiff t0 ht0 ht0pos y hy)
        (hw_grad t0 ht0 ht0pos x0 hx0int)
    have hPneg : parabolicOperatorWithDrift (I := I) G T X w t0 x0 < 0 := by
      unfold parabolicOperatorWithDrift
      linarith
    exact not_lt_of_ge
      (hnegative t0 ht0 ht0pos x0 hx0int hwneg) hPneg
  intro t ht x hxK
  by_contra hnot
  have hwneg : w t x < 0 := lt_of_not_ge hnot
  by_cases htzero : t = 0
  · exact not_lt_of_ge (by simpa [htzero] using hw0 x hxK) hwneg
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
    let epsilon : Real := -(w t x) / (2 * t)
    have hepsilon : 0 < epsilon :=
      div_pos (neg_pos.mpr hwneg) (mul_pos two_pos htpos)
    have hnonneg := hbarrier epsilon hepsilon t ht x hxK
    have hepsilon_mul : epsilon * t = -(w t x) / 2 := by
      dsimp [epsilon]
      field_simp [htzero]
    rw [hepsilon_mul] at hnonneg
    linarith

theorem strict_barrier_on_compact_set
    [I.Boundaryless]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (w : Real → M → Real)
    (hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ K))
    (hw0 : ∀ x ∈ K, 0 ≤ w 0 x)
    (hw_boundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K, 0 ≤ w t x)
    (hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t)
    (hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x)
    (hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x)
    (hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      w t x < 0 →
        0 ≤ parabolicOperatorWithDrift (I := I) G T X w t x) :
    ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, 0 ≤ w t x :=
  strict_barrier_on_compact_set_of_isInteriorPoint
    (I := I) G T hT X hK hKne
      (fun _ _ => BoundarylessManifold.isInteriorPoint)
      w hw_cont hw0 hw_boundary hw_time hw_mdiff hw_grad hnegative

private theorem deriv_nonneg_at_right_endpoint
    {f : Real → Real} {a d : Real} (ha : 0 < a)
    (hmin : IsMinOn f (Set.Icc 0 a) 0)
    (hderiv : HasDerivAt f d 0) :
    0 ≤ d := by
  have hdir : a - 0 ∈ posTangentConeAt (Set.Icc 0 a) 0 := by
    have hseg : segment Real 0 a ⊆ Set.Icc 0 a := by
      rw [segment_eq_Icc ha.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg : 0 ≤
      (fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real) (a - 0) :=
    hmin.localize.fderivWithin_nonneg hdir
  have huniq : UniqueDiffWithinAt Real (Set.Icc 0 a) 0 :=
    (uniqueDiffOn_Icc ha).uniqueDiffWithinAt (left_mem_Icc.mpr ha.le)
  have hderivWithin : derivWithin f (Set.Icc 0 a) 0 = d := by
    exact hderiv.hasDerivWithinAt.derivWithin huniq
  have hlin :
      (fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real) (a - 0) =
        (a - 0) * derivWithin f (Set.Icc 0 a) 0 := by
    rw [← fderivWithin_derivWithin (f := f) (s := Set.Icc 0 a) (x := 0)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real f (Set.Icc 0 a) 0 : Real →L[Real] Real).map_smul
        (a - 0) (1 : Real))
  rw [hlin, hderivWithin] at hnonneg
  exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hnonneg) ha

theorem scalar_hopf_boundary_point_of_barrier_of_isInteriorPoint
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (hKinterior : interior K ⊆ I.interior M)
    (u v : Real → M → Real)
    (hcont : ContinuousOn (fun p : Real × M => u p.1 p.2 - v p.1 p.2)
      (Set.Icc 0 T ×ˢ K))
    (hinit : ∀ x ∈ K, 0 ≤ u 0 x - v 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K,
      0 ≤ u t x - v t x)
    (htime : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => u s x - v s x) (Set.Icc 0 T) t)
    (hmdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I 𝓘(Real, Real) (fun y => u t y - v t y) x)
    (hgrad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t)
        (fun z => u t z - v t z) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      u t x - v t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - v s y) t x)
    {p : M} (hp : p ∈ frontier K)
    (gamma : Real → M) {a du dv : Real} (ha : 0 < a)
    (hgamma0 : gamma 0 = p)
    (hgamma : Set.MapsTo gamma (Set.Icc 0 a) K)
    (heq : u T p = v T p)
    (hu_deriv : HasDerivAt (fun s => u T (gamma s)) du 0)
    (hv_deriv : HasDerivAt (fun s => v T (gamma s)) dv 0)
    (hdv : 0 < dv) :
    0 < du := by
  let w : Real → M → Real := fun t x => u t x - v t x
  have hw_nonneg := strict_barrier_on_compact_set_of_isInteriorPoint (I := I)
    G T hT X hK hKne hKinterior w hcont hinit hboundary
      htime hmdiff hgrad hoperator
  have hpK : p ∈ K := by
    have hpcl : p ∈ closure K := frontier_subset_closure hp
    simpa [hK.isClosed.closure_eq] using hpcl
  let f : Real → Real := fun s => u T (gamma s) - v T (gamma s)
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [hgamma0, heq, sub_self]
  have hf_nonneg : ∀ s ∈ Set.Icc 0 a, 0 ≤ f s := by
    intro s hs
    by_cases hs0 : s = 0
    · subst s
      dsimp [f]
      rw [hgamma0]
      exact hw_nonneg T ⟨hT, le_rfl⟩ p hpK
    · exact hw_nonneg T ⟨hT, le_rfl⟩ (gamma s) (hgamma hs)
  have hfmin : IsMinOn f (Set.Icc 0 a) 0 := by
    intro s hs
    rw [hf0]
    exact hf_nonneg s hs
  have hfderiv : HasDerivAt f (du - dv) 0 := by
    exact hu_deriv.sub hv_deriv
  have hdiff : 0 ≤ du - dv :=
    deriv_nonneg_at_right_endpoint ha hfmin hfderiv
  linarith

theorem scalar_hopf_boundary_point_of_barrier
    [I.Boundaryless]
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) (hT : 0 ≤ T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (u v : Real → M → Real)
    (hcont : ContinuousOn (fun p : Real × M => u p.1 p.2 - v p.1 p.2)
      (Set.Icc 0 T ×ˢ K))
    (hinit : ∀ x ∈ K, 0 ≤ u 0 x - v 0 x)
    (hboundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K,
      0 ≤ u t x - v t x)
    (htime : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => u s x - v s x) (Set.Icc 0 T) t)
    (hmdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I 𝓘(Real, Real) (fun y => u t y - v t y) x)
    (hgrad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t)
        (fun z => u t z - v t z) y) x)
    (hoperator : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      u t x - v t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X
          (fun s y => u s y - v s y) t x)
    {p : M} (hp : p ∈ frontier K)
    (gamma : Real → M) {a du dv : Real} (ha : 0 < a)
    (hgamma0 : gamma 0 = p)
    (hgamma : Set.MapsTo gamma (Set.Icc 0 a) K)
    (heq : u T p = v T p)
    (hu_deriv : HasDerivAt (fun s => u T (gamma s)) du 0)
    (hv_deriv : HasDerivAt (fun s => v T (gamma s)) dv 0)
    (hdv : 0 < dv) :
    0 < du :=
  scalar_hopf_boundary_point_of_barrier_of_isInteriorPoint
    (I := I) G T hT X hK hKne
      (fun _ _ => BoundarylessManifold.isInteriorPoint)
      u v hcont hinit hboundary htime hmdiff hgrad hoperator hp
      gamma ha hgamma0 hgamma heq hu_deriv hv_deriv hdv

omit [FiniteDimensional Real E] [IsManifold I ∞ M] in
private theorem hasDerivAt_comp_mfderiv
    (f : M → Real) (gamma : Real → M) (t : Real)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f (gamma t))
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma t) :
    HasDerivAt (fun s => f (gamma s))
      (NormedSpace.fromTangentSpace (f (gamma t))
        (mfderiv I (modelWithCornersSelf Real Real) f (gamma t)
          (mfderiv (modelWithCornersSelf Real Real) I gamma t 1))) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  have hcomp := hf.hasMFDerivAt.comp t hgamma.hasMFDerivAt
  have hcomp' := hcomp.hasFDerivAt
  convert hcomp' using 1
  change ContinuousLinearMap.toSpanSingleton Real
      (((mfderiv I (modelWithCornersSelf Real Real) f (gamma t)).comp
        (mfderiv (modelWithCornersSelf Real Real) I gamma t)) 1) = _
  exact ContinuousLinearMap.toSpanSingleton_apply_map_one
    (R₁ := Real) (M₂ := Real) _

private theorem hasDerivAt_comp_neg_gradient
    (g : SmoothRiemannianMetric I M)
    (f rho : M → Real) (p : M) (gamma : Real → M)
    (hgamma0 : gamma 0 = p)
    (hf : MDifferentiableAt I (modelWithCornersSelf Real Real) f p)
    (hgamma : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0)
    (hvelocity : mfderiv (modelWithCornersSelf Real Real) I gamma 0 1 =
      -gradientFun (I := I) g rho p) :
    HasDerivAt (fun s => f (gamma s))
      (-g.inner p (gradientFun (I := I) g f p)
        (gradientFun (I := I) g rho p)) 0 := by
  have hcurve := hasDerivAt_comp_mfderiv (I := I) f gamma 0
    (by simpa [hgamma0] using hf) hgamma
  rw [hgamma0] at hcurve
  convert hcurve using 1
  change -g.inner p (gradientFun (I := I) g f p)
      (gradientFun (I := I) g rho p) =
    mfderiv I (modelWithCornersSelf Real Real) f p
      (mfderiv (modelWithCornersSelf Real Real) I gamma 0 1)
  rw [hvelocity, map_neg]
  rw [inner_gradientFun]
  rfl

theorem scalar_hopf_boundary_point_of_defining_function
    [I.Boundaryless]
    [T2Space M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    {K : Set M} (hK : IsCompact K) (hKne : K.Nonempty)
    (rho : M → Real)
    (hrho : ContMDiff I (modelWithCornersSelf Real Real) ∞ rho)
    {r R eta m B kappa alpha : Real}
    (hr : 0 ≤ r) (heta : 0 < eta)
    (hrange : ∀ x ∈ K, r ≤ rho x ∧ rho x ≤ R)
    (hfrontier : ∀ x ∈ frontier K, rho x = r ∨ rho x = R)
    (hkappa : 0 < kappa) (hinit : R ≤ r + kappa * T ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      m ≤ (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (Set.Icc 0 T ×ˢ K))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, 0 ≤ u t x)
    (hu_inner : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K,
      rho x = r → eta ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {p : M} (hp : p ∈ frontier K) (hp_outer : rho p = R)
    (hgrad_boundary : 0 < (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) rho p)
      (gradientFun (I := I) (G.metric T) rho p))
    (gamma : Real → M) {a : Real} (ha : 0 < a)
    (hgamma0 : gamma 0 = p)
    (hgamma : Set.MapsTo gamma (Set.Icc 0 a) K)
    (hgamma_mdiff : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma 0)
    (hgamma_velocity :
      mfderiv (modelWithCornersSelf Real Real) I gamma 0 1 =
        -gradientFun (I := I) (G.metric T) rho p)
    (hu_zero : u T p = 0) :
    (G.metric T).inner p
      (gradientFun (I := I) (G.metric T) (u T) p)
      (levelSetOutwardNormal (I := I) (G.metric T) rho p) < 0 := by
  let epsilon : Real := eta / 2
  let v : Real → M → Real :=
    strongBarrier rho epsilon alpha R kappa T
  let w : Real → M → Real := fun t x => u t x - v t x
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hkappa_nonneg : 0 ≤ kappa := hkappa.le
  have hfrontier_mem : ∀ x ∈ frontier K, x ∈ K := by
    intro x hx
    have hxcl : x ∈ closure K := frontier_subset_closure hx
    simpa [hK.isClosed.closure_eq] using hxcl
  have hphase_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K,
      0 ≤ strongBarrierPhase rho kappa T t x := by
    intro t ht x hx
    exact add_nonneg (hr.trans (hrange x hx).1)
      (mul_nonneg hkappa_nonneg (sq_nonneg _))
  have hv_lt_epsilon : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K,
      v t x < epsilon := by
    intro t ht x hx
    have hexp_le : Real.exp
        (-alpha * strongBarrierPhase rho kappa T t x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le)
        (hphase_nonneg t ht x hx)
    have hexpR : 0 < Real.exp (-alpha * R) := Real.exp_pos _
    have hdiff : Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
        Real.exp (-alpha * R) < 1 := by
      linarith
    change epsilon *
      (Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
        Real.exp (-alpha * R)) < epsilon
    simpa only [mul_comm] using (mul_lt_iff_lt_one_left hepsilon).mpr hdiff
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (Set.Icc 0 T ×ˢ K) :=
    (strongBarrier_joint_continuous hrho.continuous
      epsilon alpha R kappa T).continuousOn
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (Set.Icc 0 T ×ˢ K) := hu_cont.sub hv_cont
  have hw0 : ∀ x ∈ K, 0 ≤ w 0 x := by
    intro x hx
    have hphase0 : R ≤ strongBarrierPhase rho kappa T 0 x := by
      unfold strongBarrierPhase
      have hrho_lower := (hrange x hx).1
      nlinarith
    have hexp_le : Real.exp
        (-alpha * strongBarrierPhase rho kappa T 0 x) ≤
        Real.exp (-alpha * R) := Real.exp_le_exp.mpr (by nlinarith)
    have hv0 : v 0 x ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hepsilon.le
        (sub_nonpos.mpr hexp_le)
    dsimp [w]
    linarith [hu_nonneg 0 ⟨le_rfl, hT.le⟩ x hx]
  have hw_boundary : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ frontier K,
      0 ≤ w t x := by
    intro t ht x hx
    have hxK := hfrontier_mem x hx
    rcases hfrontier x hx with hinner | houter
    · have hv_lt := hv_lt_epsilon t ht x hxK
      have hu_eta := hu_inner t ht x hx hinner
      dsimp [w, epsilon] at hv_lt ⊢
      linarith
    · have hphase : R ≤ strongBarrierPhase rho kappa T t x := by
        unfold strongBarrierPhase
        rw [houter]
        exact le_add_of_nonneg_right
          (mul_nonneg hkappa_nonneg (sq_nonneg _))
      have hexp_le : Real.exp
          (-alpha * strongBarrierPhase rho kappa T t x) ≤
          Real.exp (-alpha * R) := Real.exp_le_exp.mpr (by nlinarith)
      have hv_nonpos : v t x ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos hepsilon.le
          (sub_nonpos.mpr hexp_le)
      dsimp [w]
      linarith [hu_nonneg t ht x hxK]
  have hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (strongBarrier_time_differentiable
      rho epsilon alpha R kappa T x t).differentiableWithinAt
  have hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (v t) x := by
    intro t ht htpos x
    exact (strongBarrier_slice_contMDiff hrho
      epsilon alpha R kappa T t).mdifferentiable (by simp) x
  have hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (strongBarrier_slice_contMDiff hrho epsilon alpha R kappa T t) x
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x hx
    exact (hu_time t ht htpos x).sub (hv_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDifferentiableAt I (modelWithCornersSelf Real Real) (w t) x := by
    intro t ht htpos x hx
    exact (hu_mdiff t ht htpos x).sub (hv_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x hx
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (u t) y -
              gradientFun (I := I) (G.metric t) (v t) y) := by
      funext z
      apply congrArg (fun q =>
        (⟨z, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hu_mdiff t ht htpos z) (hv_mdiff t ht htpos z)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
  have hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x ∈ interior K,
      w t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hx _hwneg
    have hheat := hheat_upper t ht htpos x hx
    have hgrad := hgrad_lower t ht htpos x hx
    have hformula := strongBarrier_parabolicOperator (I := I)
      G T hT X hrho epsilon alpha R (kappa := kappa) (tau := T) ht x
    have hkt : 0 ≤ kappa * t := mul_nonneg hkappa_nonneg ht.1
    have hlin :
        -(2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) ≤
          2 * kappa * T + B := by
      nlinarith
    have hqmul : alpha * m ≤ alpha * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x) :=
      mul_le_mul_of_nonneg_left hgrad halpha.le
    have hlinq :
        -(2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) ≤
          alpha * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x) :=
      hlin.trans (hdom.trans hqmul)
    have hmul := mul_le_mul_of_nonneg_left hlinq halpha.le
    have hbracket :
        -alpha * (2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x) ≤ 0 := by
      calc
        -alpha * (2 * kappa * (t - T) -
            heatOperatorWithDrift (I := I) G t (X t) rho x) -
            alpha ^ 2 * (G.metric t).inner x
              (gradientFun (I := I) (G.metric t) rho x)
              (gradientFun (I := I) (G.metric t) rho x) =
          alpha * (-(2 * kappa * (t - T) -
            heatOperatorWithDrift (I := I) G t (X t) rho x)) -
            alpha * (alpha * (G.metric t).inner x
              (gradientFun (I := I) (G.metric t) rho x)
              (gradientFun (I := I) (G.metric t) rho x)) := by ring
        _ ≤ 0 := sub_nonpos.mpr hmul
    have hPv_nonpos :
        parabolicOperatorWithDrift (I := I) G T X v t x ≤ 0 := by
      change parabolicOperatorWithDrift (I := I) G T X
        (strongBarrier rho epsilon alpha R kappa T) t x ≤ 0
      rw [hformula]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hepsilon.le (Real.exp_pos _).le) hbracket
    have hsub := parabolic_sub (I := I) G T X u v t x
      (hu_time t ht htpos x) (hv_time t ht htpos x)
      (hu_mdiff t ht htpos) (hv_mdiff t ht htpos)
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hsub
    rw [hsub]
    linarith [hu_super t ht htpos x hx]
  have heq : u T p = v T p := by
    rw [hu_zero]
    simp [v, strongBarrier, strongBarrierPhase, hp_outer]
  let du : Real := -(G.metric T).inner p
    (gradientFun (I := I) (G.metric T) (u T) p)
    (gradientFun (I := I) (G.metric T) rho p)
  let drho : Real := -(G.metric T).inner p
    (gradientFun (I := I) (G.metric T) rho p)
    (gradientFun (I := I) (G.metric T) rho p)
  have hu_deriv : HasDerivAt (fun s => u T (gamma s)) du 0 := by
    simpa [du] using hasDerivAt_comp_neg_gradient (I := I)
      (G.metric T) (u T) rho p gamma hgamma0
      (hu_mdiff T ⟨hT.le, le_rfl⟩ hT p) hgamma_mdiff hgamma_velocity
  have hrho_deriv : HasDerivAt (fun s => rho (gamma s)) drho 0 := by
    simpa [drho] using hasDerivAt_comp_neg_gradient (I := I)
      (G.metric T) rho rho p gamma hgamma0
      (hrho.mdifferentiable (by simp) p) hgamma_mdiff hgamma_velocity
  have hdrho : drho < 0 := by
    dsimp [drho]
    linarith
  let dv : Real := epsilon *
    (Real.exp (-alpha * R) * (-alpha * drho))
  have harg : HasDerivAt (fun s => -alpha * rho (gamma s))
      (-alpha * drho) 0 := hrho_deriv.const_mul (-alpha)
  have harg0 : -alpha * rho (gamma 0) = -alpha * R := by
    rw [hgamma0, hp_outer]
  have hexp : HasDerivAt (fun s => Real.exp (-alpha * rho (gamma s)))
      (Real.exp (-alpha * R) * (-alpha * drho)) 0 := by
    have hraw := (Real.hasDerivAt_exp
      (-alpha * rho (gamma 0))).comp 0 harg
    rw [harg0] at hraw
    exact hraw
  have hv_deriv : HasDerivAt (fun s => v T (gamma s)) dv 0 := by
    simpa [v, dv, strongBarrier, strongBarrierPhase] using
      (hexp.sub_const (Real.exp (-alpha * R))).const_mul epsilon
  have hdv : 0 < dv := by
    dsimp [dv]
    have hneg : 0 < -alpha * drho := mul_pos_of_neg_of_neg (neg_neg_of_pos halpha) hdrho
    exact mul_pos hepsilon (mul_pos (Real.exp_pos _) hneg)
  have hdu := scalar_hopf_boundary_point_of_barrier (I := I)
    G T hT.le X hK hKne u v hw_cont hw0 hw_boundary hw_time hw_mdiff
      hw_grad hnegative hp gamma ha hgamma0 hgamma heq hu_deriv hv_deriv hdv
  have hgradient :
      (G.metric T).inner p
        (gradientFun (I := I) (G.metric T) (u T) p)
        (gradientFun (I := I) (G.metric T) rho p) < 0 := by
    dsimp [du] at hdu
    linarith
  exact inner_levelSetOutwardNormal_neg
    (I := I) (G.metric T) rho (u T) p hgrad_boundary hgradient

theorem scalar_strong_maximum_principle_of_barrier
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta m B kappa alpha : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      m ≤ (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (hkappa : 0 < kappa) (hinit : R ≤ kappa * T ^ 2)
    (htime : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let epsilon : Real := eta / 2
  let v : Real → M → Real :=
    strongBarrier rho epsilon alpha R kappa T
  let w : Real → M → Real := fun t x => u t x - v t x
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hkappa_nonneg : 0 ≤ kappa := hkappa.le
  have hR_nonneg : 0 ≤ R := hR.le
  have hphase_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      0 ≤ strongBarrierPhase rho kappa T t x := by
    intro t ht x
    exact add_nonneg (hrho_nonneg x)
      (mul_nonneg hkappa_nonneg (sq_nonneg _))
  have hv_lt_epsilon : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      v t x < epsilon := by
    intro t ht x
    have hexp_le : Real.exp
        (-alpha * strongBarrierPhase rho kappa T t x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr halpha.le)
        (hphase_nonneg t ht x)
    have hexpR : 0 < Real.exp (-alpha * R) := Real.exp_pos _
    have hdiff : Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
        Real.exp (-alpha * R) < 1 := by
      linarith
    change epsilon *
      (Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
        Real.exp (-alpha * R)) < epsilon
    simpa only [mul_comm] using (mul_lt_iff_lt_one_left hepsilon).mpr hdiff
  have hv_pos_imp_phase_lt : ∀ t x, 0 < v t x →
      strongBarrierPhase rho kappa T t x < R := by
    intro t x hv
    have hmul : 0 < epsilon *
        (Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
          Real.exp (-alpha * R)) := hv
    have hdiff : 0 <
        Real.exp (-alpha * strongBarrierPhase rho kappa T t x) -
          Real.exp (-alpha * R) := ((mul_pos_iff.mp hmul).resolve_right
      (fun h => (not_lt_of_ge hepsilon.le h.1).elim)).2
    have harg := Real.exp_lt_exp.mp (sub_pos.mp hdiff)
    nlinarith
  have hv_cont : ContinuousOn (fun p : Real × M => v p.1 p.2)
      (spacetimeSlab (M := M) T) :=
    (strongBarrier_joint_continuous hrho.continuous
      epsilon alpha R kappa T).continuousOn
  have hw_cont : ContinuousOn (fun p : Real × M => w p.1 p.2)
      (spacetimeSlab (M := M) T) := hu_cont.sub hv_cont
  have hw0 : ∀ x : M, 0 ≤ w 0 x := by
    intro x
    have hphase0 : R ≤ strongBarrierPhase rho kappa T 0 x := by
      unfold strongBarrierPhase
      nlinarith [hrho_nonneg x]
    have hexp_le : Real.exp
        (-alpha * strongBarrierPhase rho kappa T 0 x) ≤
        Real.exp (-alpha * R) := Real.exp_le_exp.mpr (by nlinarith)
    have hv0 : v 0 x ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hepsilon.le
        (sub_nonpos.mpr hexp_le)
    dsimp [w]
    linarith [hu_nonneg 0 ⟨le_rfl, hT.le⟩ x]
  have hv_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => v s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (strongBarrier_time_differentiable
      rho epsilon alpha R kappa T x t).differentiableWithinAt
  have hv_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (v t) x := by
    intro t ht htpos x
    exact (strongBarrier_slice_contMDiff hrho
      epsilon alpha R kappa T t).mdifferentiable (by simp) x
  have hv_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (v t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (strongBarrier_slice_contMDiff hrho epsilon alpha R kappa T t) x
  have hw_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => w s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hu_time t ht htpos x).sub (hv_time t ht htpos x)
  have hw_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (w t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).sub (hv_mdiff t ht htpos x)
  have hw_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (w t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (w t) y) =
          (T% fun y : M =>
            gradientFun (I := I) (G.metric t) (u t) y -
              gradientFun (I := I) (G.metric t) (v t) y) := by
      funext z
      apply congrArg (fun q =>
        (⟨z, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      exact gradientFun_sub (I := I) (G.metric t)
        (hu_mdiff t ht htpos z) (hv_mdiff t ht htpos z)
    rw [heq]
    exact mdifferentiableAt_sub_section
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
  have hnegative : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      w t x < 0 → 0 ≤
        parabolicOperatorWithDrift (I := I) G T X w t x := by
    intro t ht htpos x hwneg
    have hvpos : 0 < v t x := by
      dsimp [w] at hwneg
      linarith [hu_nonneg t ht x]
    have hphase_lt := hv_pos_imp_phase_lt t x hvpos
    have hrho_lt : rho x < R := by
      have htime_nonneg : 0 ≤ kappa * (t - T) ^ 2 :=
        mul_nonneg hkappa_nonneg (sq_nonneg _)
      unfold strongBarrierPhase at hphase_lt
      linarith
    have htime_sq : kappa * (t - T) ^ 2 < R := by
      unfold strongBarrierPhase at hphase_lt
      linarith [hrho_nonneg x]
    have htime_close : T - delta < t := by
      have hsq : (t - T) ^ 2 < delta ^ 2 := by
        nlinarith
      nlinarith [sq_nonneg (t - T + delta)]
    have hrho_lower : r ≤ rho x := by
      by_contra hnot
      have hu_eta := hlocal t ht htime_close x (lt_of_not_ge hnot)
      have hv_eps := hv_lt_epsilon t ht x
      dsimp [w] at hwneg
      dsimp [epsilon] at hv_eps
      linarith
    have hheat := hheat_upper t ht htpos x hrho_lower hrho_lt.le
    have hgrad := hgrad_lower t ht htpos x hrho_lower hrho_lt.le
    have hformula := strongBarrier_parabolicOperator (I := I)
      G T hT X hrho epsilon alpha R (kappa := kappa) (tau := T) ht x
    have hkt : 0 ≤ kappa * t := mul_nonneg hkappa_nonneg ht.1
    have hlin :
        -(2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) ≤
          2 * kappa * T + B := by
      nlinarith
    have hqmul : alpha * m ≤ alpha * (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x) :=
      mul_le_mul_of_nonneg_left hgrad halpha.le
    have hlinq :
        -(2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) ≤
          alpha * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x) :=
      hlin.trans (hdom.trans hqmul)
    have hmul := mul_le_mul_of_nonneg_left hlinq halpha.le
    have hbracket :
        -alpha * (2 * kappa * (t - T) -
          heatOperatorWithDrift (I := I) G t (X t) rho x) -
          alpha ^ 2 * (G.metric t).inner x
            (gradientFun (I := I) (G.metric t) rho x)
            (gradientFun (I := I) (G.metric t) rho x) ≤ 0 := by
      calc
        -alpha * (2 * kappa * (t - T) -
            heatOperatorWithDrift (I := I) G t (X t) rho x) -
            alpha ^ 2 * (G.metric t).inner x
              (gradientFun (I := I) (G.metric t) rho x)
              (gradientFun (I := I) (G.metric t) rho x) =
          alpha * (-(2 * kappa * (t - T) -
            heatOperatorWithDrift (I := I) G t (X t) rho x)) -
            alpha * (alpha * (G.metric t).inner x
              (gradientFun (I := I) (G.metric t) rho x)
              (gradientFun (I := I) (G.metric t) rho x)) := by ring
        _ ≤ 0 := sub_nonpos.mpr hmul
    have hPv_nonpos : parabolicOperatorWithDrift (I := I) G T X v t x ≤ 0 := by
      change parabolicOperatorWithDrift (I := I) G T X
        (strongBarrier rho epsilon alpha R kappa T) t x ≤ 0
      rw [hformula]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hepsilon.le (Real.exp_pos _).le) hbracket
    have hsub := parabolic_sub (I := I) G T X u v t x
      (hu_time t ht htpos x) (hv_time t ht htpos x)
      (hu_mdiff t ht htpos) (hv_mdiff t ht htpos)
      (hu_grad t ht htpos x) (hv_grad t ht htpos x)
    change parabolicOperatorWithDrift (I := I) G T X w t x = _ at hsub
    rw [hsub]
    linarith [hu_super t ht htpos x]
  have hw_nonneg := strict_barrier_positive_region (I := I)
    G T X w hw_cont hw0 hw_time hw_mdiff hw_grad hnegative
    T ⟨hT.le, le_rfl⟩ y
  have hphaseT : strongBarrierPhase rho kappa T T y = rho y := by
    simp [strongBarrierPhase]
  have hexp_lt : Real.exp (-alpha * R) < Real.exp (-alpha * rho y) :=
    Real.exp_lt_exp.mpr (by nlinarith)
  have hvT_pos : 0 < v T y := by
    change 0 < epsilon *
      (Real.exp (-alpha * strongBarrierPhase rho kappa T T y) -
        Real.exp (-alpha * R))
    rw [hphaseT]
    exact mul_pos hepsilon (sub_pos.mpr hexp_lt)
  dsimp [w] at hw_nonneg
  linarith

theorem scalar_strong_maximum_principle_time_dependent_metric_of_barrier
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        laplacianAt (I := I) G t (u t) x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta m B kappa alpha : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      m ≤ (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x))
    (hlaplacian_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R → laplacianAt (I := I) G t rho x ≤ B)
    (hkappa : 0 < kappa) (hinit : R ≤ kappa * T ^ 2)
    (htime : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let X : Real → (x : M) → TangentSpace I x := fun _ x => 0
  have hu_super' : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x := by
    intro t ht htpos x
    simpa [parabolicOperatorWithDrift, heatOperatorWithDrift, driftTerm, X]
      using hu_super t ht htpos x
  have hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B := by
    intro t ht htpos x hxr hxR
    simpa [heatOperatorWithDrift, driftTerm, X]
      using hlaplacian_upper t ht htpos x hxr hxR
  exact scalar_strong_maximum_principle_of_barrier (I := I)
    G hT X u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super'
    hrho hrho_nonneg hR hdelta heta hlocal hgrad_lower hheat_upper
    hkappa hinit htime halpha hdom hy

theorem scalar_strong_maximum_principle_fixed_metric_of_barrier
    [I.Boundaryless]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hcompact : IsCompact {x : M | r ≤ rho x ∧ rho x ≤ R})
    (hgrad_ne : ∀ x : M, r ≤ rho x → rho x ≤ R →
      gradientFun (I := I) g rho x ≠ 0)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let K : Set M := {x : M | r ≤ rho x ∧ rho x ≤ R}
  let q : M → Real := fun x => g.inner x
    (gradientFun (I := I) g rho x) (gradientFun (I := I) g rho x)
  let ell : M → Real := fun x => |Δ_g (I := I) g ⟨rho, hrho⟩ x|
  have hq_cont : Continuous q := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hgrad : ContMDiffAt I (I.prod 𝓘(Real, E)) ∞
        (T% fun y : M => gradientFun (I := I) g rho y) x :=
      (gradientFun_smooth (I := I) g hrho).contMDiffAt
    exact (CovariantDerivative.metric_inner_contMDiffAt
      (I := I) g hgrad hgrad le_rfl).continuousAt
  have hell_cont : Continuous ell := by
    exact continuous_abs.comp (Δ_g_contMDiff (I := I) g ⟨rho, hrho⟩).continuous
  have hbounds : ∃ m B : Real, 0 < m ∧ 0 ≤ B ∧
      (∀ x ∈ K, m ≤ q x) ∧ (∀ x ∈ K, ell x ≤ B) := by
    by_cases hKne : K.Nonempty
    · obtain ⟨xm, hxm, hxmin⟩ := hcompact.exists_isMinOn
        (by simpa [K] using hKne) hq_cont.continuousOn
      obtain ⟨xB, hxB, hxBmax⟩ := hcompact.exists_isMaxOn
        (by simpa [K] using hKne) hell_cont.continuousOn
      have hqm_pos : 0 < q xm := by
        exact g.pos xm _ (hgrad_ne xm hxm.1 hxm.2)
      refine ⟨q xm, ell xB, hqm_pos, abs_nonneg _, ?_, ?_⟩
      · intro x hx
        exact hxmin (by simpa [K] using hx)
      · intro x hx
        exact hxBmax (by simpa [K] using hx)
    · refine ⟨1, 0, zero_lt_one, le_rfl, ?_, ?_⟩
      · intro x hx
        exact (hKne ⟨x, hx⟩).elim
      · intro x hx
        exact (hKne ⟨x, hx⟩).elim
  obtain ⟨m, B, hm, hB, hgrad_bound, hlap_bound⟩ := hbounds
  let kappa : Real := max (R / T ^ 2) (R / delta ^ 2) + 1
  have hT_sq : 0 < T ^ 2 := sq_pos_of_pos hT
  have hdelta_sq : 0 < delta ^ 2 := sq_pos_of_pos hdelta
  have hkappa : 0 < kappa := by
    have hratio : 0 < R / T ^ 2 := div_pos hR hT_sq
    dsimp [kappa]
    linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
  have hinit : R ≤ kappa * T ^ 2 := by
    have hratio : R / T ^ 2 < kappa := by
      dsimp [kappa]
      linarith [le_max_left (R / T ^ 2) (R / delta ^ 2)]
    exact (le_of_lt ((div_lt_iff₀ hT_sq).mp hratio))
  have htime : R ≤ kappa * delta ^ 2 := by
    have hratio : R / delta ^ 2 < kappa := by
      dsimp [kappa]
      linarith [le_max_right (R / T ^ 2) (R / delta ^ 2)]
    exact (le_of_lt ((div_lt_iff₀ hdelta_sq).mp hratio))
  let alpha : Real := (2 * kappa * T + B) / m + 1
  have hnum_nonneg : 0 ≤ 2 * kappa * T + B := by
    positivity
  have halpha : 0 < alpha := by
    dsimp [alpha]
    have hquot : 0 ≤ (2 * kappa * T + B) / m :=
      div_nonneg hnum_nonneg hm.le
    linarith
  have hdom : 2 * kappa * T + B ≤ alpha * m := by
    have hlt : (2 * kappa * T + B) / m < alpha := by
      dsimp [alpha]
      linarith
    exact le_of_lt ((div_lt_iff₀ hm).mp hlt)
  let G := strongStaticMetricFamily (I := I) g
  have hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x := by
    intro t ht htpos x
    exact (hu_space t ht htpos).mdifferentiable (by simp) x
  have hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (u t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) g (hu_space t ht htpos) x
  have hu_super' : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T (fun _ _ => 0) u t x := by
    intro t ht htpos x
    have hlap := laplacianAt_eq_delta (I := I) G t
      (hu_space t ht htpos) rfl x
    unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm
    rw [hlap]
    simpa using hu_super t ht htpos x
  apply scalar_strong_maximum_principle_of_barrier (I := I)
    G hT (fun _ _ => 0) u hu_cont hu_nonneg hu_time hu_mdiff hu_grad
    hu_super' hrho hrho_nonneg hR hdelta heta hlocal
    (m := m) (B := B) (kappa := kappa) (alpha := alpha)
  · intro t ht htpos x hxr hxR
    exact hgrad_bound x (by exact ⟨hxr, hxR⟩)
  · intro t ht htpos x hxr hxR
    have hlap := laplacianAt_eq_delta (I := I) G t hrho rfl x
    have habs := hlap_bound x (by exact ⟨hxr, hxR⟩)
    unfold heatOperatorWithDrift driftTerm
    rw [hlap]
    simpa using le_trans (le_abs_self _) habs
  · exact hkappa
  · exact hinit
  · exact htime
  · exact halpha
  · exact hdom
  · exact hy

theorem scalar_strong_maximum_principle_fixed_metric_with_drift_of_barrier
    [I.Boundaryless]
    [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (g : SmoothRiemannianMetric I M)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_space : ∀ t ∈ Set.Icc 0 T, 0 < t →
      ContMDiff I 𝓘(Real, Real) ∞ (u t))
    (hu_super : ∀ (t : Real) (ht : t ∈ Set.Icc 0 T) (htpos : 0 < t)
      (x : M),
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 T) t -
        (Δ_g (I := I) g ⟨u t, hu_space t ht htpos⟩ x +
          g.inner x (X t x) (gradientFun (I := I) g (u t) x)))
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta m B kappa alpha : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hgrad_lower : ∀ x : M, r ≤ rho x → rho x ≤ R →
      m ≤ g.inner x (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      Δ_g (I := I) g ⟨rho, hrho⟩ x +
        g.inner x (X t x) (gradientFun (I := I) g rho x) ≤ B)
    (hkappa : 0 < kappa) (hinit : R ≤ kappa * T ^ 2)
    (htime : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let G := strongStaticMetricFamily (I := I) g
  have hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x := by
    intro t ht htpos x
    exact (hu_space t ht htpos).mdifferentiable (by simp) x
  have hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x := by
    intro t ht htpos x
    exact gradientFun_mdiffAt (I := I) g (hu_space t ht htpos) x
  have hu_super' : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x := by
    intro t ht htpos x
    have hlap := laplacianAt_eq_delta (I := I) G t
      (hu_space t ht htpos) rfl x
    unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm gradientAt
    rw [hlap]
    simpa using hu_super t ht htpos x
  apply scalar_strong_maximum_principle_of_barrier (I := I)
    G hT X u hu_cont hu_nonneg hu_time hu_mdiff hu_grad hu_super'
    hrho hrho_nonneg hR hdelta heta hlocal
    (m := m) (B := B) (kappa := kappa) (alpha := alpha)
  · intro t ht htpos x hxr hxR
    exact hgrad_lower x hxr hxR
  · intro t ht htpos x hxr hxR
    have hlap := laplacianAt_eq_delta (I := I) G t hrho rfl x
    unfold heatOperatorWithDrift driftTerm gradientAt
    rw [hlap]
    exact hheat_upper t ht htpos x hxr hxR
  · exact hkappa
  · exact hinit
  · exact htime
  · exact halpha
  · exact hdom
  · exact hy

theorem scalar_strong_maximum_principle_with_potential_of_barrier
    [I.Boundaryless]
    [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 < T)
    (X : Real → (x : M) → TangentSpace I x)
    (V : Real → M → Real) (L : Real)
    (u : Real → M → Real)
    (hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) T))
    (hu_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ u t x)
    (hu_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 T) t)
    (hu_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x)
    (hu_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x)
    (hu_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X u t x -
        V t x * u t x)
    (hV_lower : ∀ t ∈ Set.Icc 0 T, ∀ x : M, L ≤ V t x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta m B kappa alpha : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      m ≤ (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      heatOperatorWithDrift (I := I) G t (X t) rho x ≤ B)
    (hkappa : 0 < kappa) (hinit : R ≤ kappa * T ^ 2)
    (htime : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * T + B ≤ alpha * m)
    {y : M} (hy : rho y < R) :
    0 < u T y := by
  let z : Real → M → Real := fun t x => Real.exp (-L * t) * u t x
  have hz_cont : ContinuousOn (fun p : Real × M => z p.1 p.2)
      (spacetimeSlab (M := M) T) := by
    have hscale : Continuous (fun p : Real × M => Real.exp (-L * p.1)) := by
      fun_prop
    exact hscale.continuousOn.mul hu_cont
  have hz_nonneg : ∀ t ∈ Set.Icc 0 T, ∀ x : M, 0 ≤ z t x := by
    intro t ht x
    exact mul_nonneg (Real.exp_pos _).le (hu_nonneg t ht x)
  have hscale_time : ∀ t : Real,
      DifferentiableWithinAt Real (fun s => Real.exp (-L * s))
        (Set.Icc 0 T) t := by
    intro t
    fun_prop
  have hz_time : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => z s x) (Set.Icc 0 T) t := by
    intro t ht htpos x
    exact (hscale_time t).mul (hu_time t ht htpos x)
  have hz_mdiff : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (z t) x := by
    intro t ht htpos x
    exact (hu_mdiff t ht htpos x).const_smul (Real.exp (-L * t))
  have hz_grad : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (z t) y) x := by
    intro t ht htpos x
    have heq :
        (T% fun y : M => gradientFun (I := I) (G.metric t) (z t) y) =
          (T% fun y : M => Real.exp (-L * t) •
            gradientFun (I := I) (G.metric t) (u t) y) := by
      funext y
      apply congrArg (fun q =>
        (⟨y, q⟩ : TotalSpace E (TangentSpace I : M → Type _)))
      change gradientFun (I := I) (G.metric t)
        (Real.exp (-L * t) • u t) y = _
      exact gradientFun_const_smul (I := I) (G.metric t)
        (Real.exp (-L * t)) (hu_mdiff t ht htpos y)
    rw [heq]
    exact mdifferentiableAt_const.smul_section (hu_grad t ht htpos x)
  have hz_super : ∀ t ∈ Set.Icc 0 T, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G T X z t x := by
    intro t ht htpos x
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 T) t :=
      (uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht
    have hident := parabolic_exp_rescale_identity (I := I)
      G T L X u t huniq (hu_mdiff t ht htpos) x
      (hu_grad t ht htpos x) (hu_time t ht htpos x) (hscale_time t)
    have hVu : 0 ≤ (V t x - L) * u t x :=
      mul_nonneg (sub_nonneg.mpr (hV_lower t ht x)) (hu_nonneg t ht x)
    have hbase : 0 ≤
        parabolicOperatorWithDrift (I := I) G T X u t x - L * u t x := by
      linarith [hu_super t ht htpos x]
    change 0 ≤ parabolicOperatorWithDrift (I := I) G T X
      (fun s y => Real.exp (-L * s) * u s y) t x
    rw [hident]
    exact mul_nonneg (Real.exp_pos _).le hbase
  let eta' : Real := Real.exp (-|L| * T) * eta
  have heta' : 0 < eta' := mul_pos (Real.exp_pos _) heta
  have hlocal' : ∀ t ∈ Set.Icc 0 T, T - delta < t → ∀ x : M,
      rho x < r → eta' ≤ z t x := by
    intro t ht htnear x hxr
    have hLt : L * t ≤ |L| * T := by
      calc
        L * t ≤ |L| * t :=
          mul_le_mul_of_nonneg_right (le_abs_self L) ht.1
        _ ≤ |L| * T :=
          mul_le_mul_of_nonneg_left ht.2 (abs_nonneg L)
    have hscale : Real.exp (-|L| * T) ≤ Real.exp (-L * t) :=
      Real.exp_le_exp.mpr (by linarith)
    have hu_eta := hlocal t ht htnear x hxr
    exact mul_le_mul hscale hu_eta heta.le (Real.exp_pos _).le
  have hz_pos := scalar_strong_maximum_principle_of_barrier (I := I)
    G hT X z hz_cont hz_nonneg hz_time hz_mdiff hz_grad hz_super
    hrho hrho_nonneg hR hdelta heta' hlocal'
    hgrad_lower hheat_upper hkappa hinit htime halpha hdom hy
  have hscale_pos : 0 < Real.exp (-L * T) := Real.exp_pos _
  change 0 < Real.exp (-L * T) * u T y at hz_pos
  exact ((mul_pos_iff.mp hz_pos).resolve_right
    (fun h => (not_lt_of_ge hscale_pos.le h.1).elim)).2

end

end DifferentialGeometry.Analysis.Parabolic
