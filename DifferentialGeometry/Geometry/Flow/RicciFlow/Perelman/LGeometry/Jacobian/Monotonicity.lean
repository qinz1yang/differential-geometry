import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.AdaptedField

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redLength_ray_K
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt
      (fun r ↦ redLength S T x (lExp S T x Z r) r)
      (-lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau)) tau := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  let alpha : Real → M := lRegCurve S T x Z
  let b : Real := Real.sqrt tau
  let z : E := Z
  let A : E × Real → Real := fun p ↦
    lRegAction S T (lRegCurve S T x p.1) 0 (Real.sqrt p.2)
  let c : Real := lRegLag S T alpha b / (2 * b)
  let y : M := lExp S T x Z tau
  let endMap : E → M := fun W ↦ lExp S T x W tau
  let Lz : E →L[Real] Real :=
    ((S.base.metric (T - tau)).inner y
      (lVelocity (I := I) alpha b)).comp
        (mfderiv (modelWithCornersSelf Real E) I endMap Z)
  let L : E × Real →L[Real] Real :=
    Lz.comp (ContinuousLinearMap.fst Real E Real) +
      c • ContinuousLinearMap.snd Real E Real
  have hJoint : HasFDerivAt A L (Z, tau) := by
    with_unfolding_all
      exact lRayAct_joint S hS T x Z hdom
  have htins : HasFDerivAt (fun r : Real ↦ (z, r))
      (ContinuousLinearMap.inr Real E Real) tau :=
    hasFDerivAt_prodMk_right z tau
  have hact : HasDerivAt (fun r : Real ↦ A (z, r)) c tau := by
    have hout := (hJoint.comp tau htins).hasDerivAt
    change HasDerivAt (A ∘ Prod.mk z) c tau
    apply hout.congr_deriv
    simp [L, Lz]
  have hEq : (fun r : Real ↦ A (z, r)) =ᶠ[nhds tau]
      fun r ↦ lCost S T x (lExp S T x Z r) r := by
    filter_upwards [eventually_gt_nhds htau, eventually_lt_nhds hsigma]
      with r hrpos hrlt
    have hminr : (Z, r) ∈ lMinDomain S T x :=
      lMinDomain_down S hS T x Z hmin hrpos hrlt.le
    have hcost := ((mem_lMinDomain S T x Z r).1 hminr).2
    change lRegAction S T alpha 0 (Real.sqrt r) =
      lCost S T x (lExp S T x Z r) r
    calc
      lRegAction S T alpha 0 (Real.sqrt r) =
          lLength S T (fun q : Real ↦ lExp S T x Z q) 0 r := by
        change lRegAction S T alpha 0 (Real.sqrt r) =
          lLength S T (sqrtReparam alpha) 0 r
        exact (lLength_sqrt (I := I) S T alpha r hrpos.le).symm
      _ = lCost S T x (lExp S T x Z r) r := hcost
  have hcost := hact.congr_of_eventuallyEq hEq.symm
  have hbpos : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hb0 : b ≠ 0 := hbpos.ne'
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  have hcostTau :
      lCost S T x (lExp S T x Z tau) tau =
        lRegAction S T alpha 0 b := by
    simpa only [A, alpha, b, z] using hEq.self_of_nhds.symm
  have hden0 : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hquot := hcost.div
    ((Real.hasDerivAt_sqrt htau.ne').const_mul 2) hden0
  have hderiv :
      (c * (2 * b) -
          lCost S T x (lExp S T x Z tau) tau *
            (2 * (1 / (2 * b)))) / (2 * b) ^ 2 =
        -lK S T alpha b / (2 * tau * b) := by
    rw [hcostTau, lK_ray_energy S hS T x Z hbpos hbdom]
    dsimp only [c]
    field_simp [hb0]
    rw [hbsq]
    ring
  have hquot' : HasDerivAt
      ((fun r : Real ↦ lCost S T x (lExp S T x Z r) r) /
        fun r : Real ↦ 2 * Real.sqrt r)
      (-lK S T alpha b / (2 * tau * b)) tau := by
    apply hquot.congr_deriv
    simpa only [b] using hderiv
  have hred := hquot'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun r ↦ by
      change redLength S T x (lExp S T x Z r) r =
        lCost S T x (lExp S T x Z r) r / (2 * Real.sqrt r)
      rfl)
  simpa only [alpha, b] using hred

noncomputable def lRedLog
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Real :=
  Real.log (lExpJac S T x Z tau) -
    redLength S T x (lExp S T x Z tau) tau -
    ((Module.finrank Real E : Real) / 2) * Real.log tau -
    ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)

noncomputable def lRedJac
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (Z : TangentSpace I x) (tau : Real) : Real :=
  Real.exp (lRedLog S T x Z tau)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedLog_hasDeriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt (lRedLog S T x Z)
      (laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau) +
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank Real E : Real) / (2 * tau)) tau := by
  let n2 : Real := (Module.finrank Real E : Real) / 2
  have hJ := lExpLog_hasDeriv S hS T x htau hZ
  have hl := redLength_ray_K S hS T x htau hZ
  have htlog := (Real.hasDerivAt_log htau.ne').const_mul n2
  have hout := ((hJ.sub hl).sub htlog).sub_const
    (n2 * Real.log (4 * Real.pi))
  change HasDerivAt (lRedLog S T x Z)
    (laplacian (I := I) (LeviCivita (I := I)
          (S.base.metric (T - tau))) (S.base.metric (T - tau))
          (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) +
        S.scalar (T - tau) (lExp S T x Z tau) -
      -lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
        (2 * tau * Real.sqrt tau) - n2 * tau⁻¹) tau at hout
  have hcoef :
      laplacian (I := I) (LeviCivita (I := I)
            (S.base.metric (T - tau))) (S.base.metric (T - tau))
            (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) +
          S.scalar (T - tau) (lExp S T x Z tau) -
        -lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) - n2 * tau⁻¹ =
      laplacian (I := I) (LeviCivita (I := I)
            (S.base.metric (T - tau))) (S.base.metric (T - tau))
            (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) +
          S.scalar (T - tau) (lExp S T x Z tau) +
        lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) -
        (Module.finrank Real E : Real) / (2 * tau) := by
    dsimp only [n2]
    field_simp [htau.ne']
    ring
  rw [hcoef] at hout
  with_unfolding_all exact hout

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_hasDeriv
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    HasDerivAt (lRedJac S T x Z)
      (Real.exp (lRedLog S T x Z tau) *
        (laplacian (I := I) (LeviCivita (I := I)
            (S.base.metric (T - tau))) (S.base.metric (T - tau))
            (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) +
          S.scalar (T - tau) (lExp S T x Z tau) +
          lK S T (lRegCurve S T x Z) (Real.sqrt tau) /
            (2 * tau * Real.sqrt tau) -
          (Module.finrank Real E : Real) / (2 * tau))) tau := by
  with_unfolding_all exact (lRedLog_hasDeriv S hS T x htau hZ).exp

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedLog_deriv_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) ((s / Real.sqrt tau) • P i s) :
          TangentBundle I M)) Ω)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / Real.sqrt tau) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegCurve S T x Z s)
          (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau)) :
    deriv (lRedLog S T x Z) tau ≤ 0 := by
  rw [(lRedLog_hasDeriv S hS T x htau hZ).deriv]
  have hbound := lExpLog_deriv_le S hS T x htau hZ P
    hΩ hΩseg hW hP hDP hON hIint hRint
  rw [(lExpLog_hasDeriv S hS T x htau hZ).deriv] at hbound
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_deriv_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) ((s / Real.sqrt tau) • P i s) :
          TangentBundle I M)) Ω)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / Real.sqrt tau) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegCurve S T x Z s)
          (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau)) :
    deriv (lRedJac S T x Z) tau ≤ 0 := by
  rw [(lRedJac_hasDeriv S hS T x htau hZ).deriv]
  have hlog := lRedLog_deriv_le S hS T x htau hZ P
    hΩ hΩseg hW hP hDP hON hIint hRint
  rw [(lRedLog_hasDeriv S hS T x htau hZ).deriv] at hlog
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hlog

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_deriv_le0
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau) :
    deriv (lRedJac S T x Z) tau ≤ 0 := by
  classical
  have hZ0 := hZ
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  let b : Real := Real.sqrt tau
  let alpha : Real → M := lRegCurve S T x Z
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hbsq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hpos : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hpos).2.2
  obtain ⟨P, Ω, hΩ, hseg, hPsm, hDPΩ, hON⟩ :=
    exists_lRayAdapt (I := I) S hS T x hb hbdom
  have hW (i : Fin (Module.finrank Real E)) :
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent (8 : Nat)
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) ((s / b) • P i s) : TangentBundle I M)) Ω := by
    intro s hs
    apply ContMDiffAt.contMDiffWithinAt
    have hsec :=
      (((hPsm i s hs).contMDiffAt (hΩ.mem_nhds hs)).of_le
        (by decide :
          (8 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
    have hc : ContMDiffAt (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real) 8 (fun r : Real ↦ r / b) s :=
      (contMDiff_id.div_const b).contMDiffAt
    rw [Bundle.contMDiffAt_totalSpace] at hsec ⊢
    refine ⟨hsec.1, ?_⟩
    let e := trivializationAt E (TangentSpace I) (alpha s)
    apply (hc.smul hsec.2).congr_of_eventuallyEq
    have he : ∀ᶠ r in nhds s, alpha r ∈ e.baseSet := by
      apply hsec.1.continuousAt
      exact e.open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (alpha s))
    filter_upwards [he] with r hr
    change (e ⟨alpha r, (r / b) • P i r⟩).2 =
      (r / b) • (e ⟨alpha r, P i r⟩).2
    exact (e.linear Real hr).map_smul (r / b) (P i r)
  have hPdiff (i : Fin (Module.finrank Real E)) (s : Real)
      (hs : s ∈ Set.Icc (0 : Real) b) :
      DifferentiableAt Real (chartRepAt (I := I) alpha (P i) s) s := by
    apply chartRep_diff_at
    exact (((hPsm i s (hseg hs)).contMDiffAt
      (hΩ.mem_nhds (hseg hs))).of_le (by decide :
        (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞)))
  have hregIcc : ∀ s ∈ Set.Icc (0 : Real) b,
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegDomain_reg S T x Z
      (lRegDomain_seg S T x Z hbdom hs.1 hs.2)
  have huseg : Set.uIcc (0 : Real) b ⊆ Ω := by
    simpa only [Set.uIcc_of_le hb.le] using hseg
  have hPtwo (i : Fin (Module.finrank Real E)) :
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent 2
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (P i s) : TangentBundle I M)) Ω :=
    (hPsm i).of_le (by decide :
      (2 : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
  have hIint (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦ (s / b) ^ 2 *
        lRegIndexInt S T alpha (P i) (P i) s)
      MeasureTheory.volume 0 b := by
    have hi := lRegIndex_intOn S hS T 0 b alpha (P i) (P i)
      hΩ huseg (hPtwo i) (hPtwo i) (by
        intro s hs
        apply hregIcc s
        simpa only [Set.uIcc_of_le hb.le] using hs)
    exact hi.continuousOn_mul
      ((continuous_id.div_const b).pow 2).continuousOn
  have hRint (i : Fin (Module.finrank Real E)) : IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / b ^ 2) *
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 b := by
    let K := Set.Icc (0 : Real) b
    have hsec : Continuous (fun u : K ↦
        (TotalSpace.mk' E (alpha u) (P i u) : TangentBundle I M)) := by
      change Continuous (K.domRestrict fun s : Real ↦
        (TotalSpace.mk' E (alpha s) (P i s) : TangentBundle I M))
      exact ((hPsm i).continuousOn.mono hseg).domRestrict
    have hbase : Continuous (fun u : K ↦ alpha u) :=
      (FiberBundle.continuous_proj E (TangentSpace I)).comp hsec
    have htime : Continuous (fun u : K ↦ T - (u : Real) ^ 2) :=
      continuous_const.sub (continuous_subtype_val.pow 2)
    have heval := hS.ricciCont.eval_continuous
      (P := K) htime
      (fun u ↦ D.regular_subset (hregIcc u u.2)) hbase
      (v := fun k u ↦ vec2 (P i u) (P i u) k) (by
        intro k
        fin_cases k
        · with_unfolding_all exact hsec
        · with_unfolding_all exact hsec)
    have hric : ContinuousOn
        (fun s : Real ↦ S.ricciAt (T - s ^ 2) (alpha s)
          (vec2 (P i s) (P i s))) K := by
      rw [continuousOn_iff_continuous_domRestrict]
      change Continuous (K.domRestrict fun s : Real ↦
        S.ricciAt (T - s ^ 2) (alpha s) (vec2 (P i s) (P i s)))
      with_unfolding_all exact heval
    have hc : Continuous (fun s : Real ↦ 2 * s ^ 2 / b ^ 2) :=
      (continuous_const.mul (continuous_id.pow 2)).div_const _
    exact (hc.continuousOn.mul hric).intervalIntegrable_of_Icc hb.le
  refine lRedJac_deriv_le S hS T x htau hZ0 P hΩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa only [b] using hseg
  · simpa only [alpha, b] using hW
  · simpa only [alpha, b] using hPdiff
  · intro i s hs
    simpa only [alpha, b] using hDPΩ i s (hseg (by simpa only [b] using hs))
  · intro i j
    have hout := hON i j
    rw [hbsq] at hout
    dsimp only [alpha, b] at hout
    change (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0 at hout
    with_unfolding_all exact hout
  · simpa only [alpha, b] using hIint
  · simpa only [alpha, b] using hRint

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRedJac_anti
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau₁ tau₂ : Real}
    (htau₁ : 0 < tau₁) (h12 : tau₁ ≤ tau₂)
    (hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau₂) :
    lRedJac S T x Z tau₂ ≤ lRedJac S T x Z tau₁ := by
  obtain ⟨sigma, hsigma, hmin⟩ := hZ
  have hZr (r : Real) (hr : r ∈ Set.Icc tau₁ tau₂) :
      Z ∈ lInjDomain (E := E) (I := I) S T x r :=
    ⟨sigma, lt_of_le_of_lt hr.2 hsigma, hmin⟩
  have hrpos (r : Real) (hr : r ∈ Set.Icc tau₁ tau₂) : 0 < r :=
    htau₁.trans_le hr.1
  have hder (r : Real) (hr : r ∈ Set.Icc tau₁ tau₂) :=
    lRedJac_hasDeriv S hS T x (hrpos r hr) (hZr r hr)
  have hcont : ContinuousOn (lRedJac S T x Z) (Set.Icc tau₁ tau₂) := by
    intro r hr
    exact (hder r hr).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn Real (lRedJac S T x Z)
      (interior (Set.Icc tau₁ tau₂)) := by
    intro r hr
    have hrI : r ∈ Set.Icc tau₁ tau₂ := interior_subset hr
    exact (hder r hrI).differentiableAt.differentiableWithinAt
  have hanti := antitoneOn_of_deriv_nonpos
    (convex_Icc tau₁ tau₂) hcont hdiff (fun r hr ↦ by
      have hrI : r ∈ Set.Icc tau₁ tau₂ := interior_subset hr
      exact lRedJac_deriv_le0 S hS T x (hrpos r hrI) (hZr r hrI))
  exact hanti ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12

end DifferentialGeometry.PDE.RicciFlow.Perelman
