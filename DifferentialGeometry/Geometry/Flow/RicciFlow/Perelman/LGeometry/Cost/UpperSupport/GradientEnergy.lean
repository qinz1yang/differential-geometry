import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.HamiltonGradientTrace


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_lt_energy
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegularizedCurve S T x Z s)) (Omega : Set Real),
      IsOpen Omega ∧ Icc (0 : Real) (Real.sqrt tau) ⊆ Omega ∧
      (∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (lRegularizedCurve S T x Z s) (P i s) : TangentBundle I M)) Omega) ∧
      (∀ i, IsLAdapted S T (lRegularizedCurve S T x Z) (P i) Omega) ∧
      (∀ i j, (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = if i = j then 1 else 0) ∧
      ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
        ∃ F : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ F U ∧
          F (lExp S T x Z tau) = lCost S T x (lExp S T x Z tau) tau ∧
          (∀ y ∈ U, lCost S T x y tau ≤ F y) ∧
          gradientFun (I := I) (S.base.metric (T - tau)) F
            (lExp S T x Z tau) =
              lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau) ∧
          (∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) <
            (Module.finrank Real E : Real) / Real.sqrt tau -
              Real.sqrt tau * S.scalar (T - tau) (lExp S T x Z tau) -
              lCost S T x (lExp S T x Z tau) tau / (2 * tau) +
              (S.base.metric (T - tau)).inner (lExp S T x Z tau)
                (lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau))
                (lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau)) /
                  (4 * Real.sqrt tau) + epsilon := by
  let b : Real := Real.sqrt tau
  let gamma : Real → M := lRegularizedCurve S T x Z
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hEnd : gamma b = lExp S T x Z tau := rfl
  have hbdom : b ∈ lRegularizedDomain S T x Z := by
    have hpos := ((mem_lMinDomain S T x Z tau).mp hmin).1
    exact ((mem_lExpPosDom S T x Z tau).mp hpos).2.2
  let B : Real → Real := fun a ↦
    (Module.finrank Real E : Real) / (b - a) -
      2 * b * S.scalar (T - tau) (lExp S T x Z tau) -
      lKTail S T gamma a b / (b - a) ^ 2
  let C : Real := (Module.finrank Real E : Real) / b -
    2 * b * S.scalar (T - tau) (lExp S T x Z tau) -
    lK S T gamma b / b ^ 2
  have hid : Tendsto (fun a : Real ↦ a) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_inf_left tendsto_id
  have hdenom : Tendsto (fun a : Real ↦ b - a)
      (nhdsWithin 0 (Ioi 0)) (nhds b) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := b)).sub hid
  have htail := lKTail_tendsto (I := I) S hS T x Z hb hbdom
  have hB : Tendsto B (nhdsWithin 0 (Ioi 0)) (nhds C) :=
    ((tendsto_const_nhds.div hdenom hb.ne').sub tendsto_const_nhds).sub
      (htail.div (hdenom.pow 2) (pow_ne_zero 2 hb.ne'))
  have hnear : ∀ᶠ a in nhdsWithin (0 : Real) (Ioi 0), B a < C + epsilon :=
    hB.eventually (Iio_mem_nhds (lt_add_of_pos_right C hepsilon))
  have hsmall : ∀ᶠ a : Real in nhdsWithin 0 (Ioi 0), a ∈ Ioo 0 b :=
    Ioo_mem_nhdsGT hb
  obtain ⟨a, ha, hbound⟩ := (hsmall.and hnear).exists
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_le_hamilton
      (I := I) S hS K T x hmin hreg hRm ha.1 ha.2
  have hact : lRegularizedAction S T gamma 0 b =
      lCost S T x (lExp S T x Z tau) tau := by
    calc
      lRegularizedAction S T gamma 0 b =
          lLength S T (squareRootReparametrization gamma) 0 tau := by
        simpa only [b] using
          (lLength_squareRootReparametrization_eq_lRegularizedAction
            (I := I) S T gamma tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := by
        exact ((mem_lMinDomain S T x Z tau).mp hmin).2
  have hK := lK_ray_energy (I := I) S hS T x Z hb hbdom
  have hCenergy : C =
      (Module.finrank Real E : Real) / b -
        b * S.scalar (T - b ^ 2) (gamma b) -
        lCost S T x (lExp S T x Z tau) tau / (2 * b ^ 2) +
        (S.base.metric (T - b ^ 2)).inner (gamma b)
          (lVelocity (I := I) gamma b) (lVelocity (I := I) gamma b) / (4 * b) := by
    change (Module.finrank Real E : Real) / b -
      2 * b * S.scalar (T - tau) (lExp S T x Z tau) -
      lK S T gamma b / b ^ 2 = _
    rw [hK, hact]
    unfold lRegularizedLagrangian
    rw [← hEnd, ← hb2]
    field_simp [hb.ne']
    ring
  refine ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
    U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, ?_⟩
  have htrace' : (∑ i : Fin (Module.finrank Real E),
      hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
        (P i b) (P i b)) ≤ B a := htrace
  have hstrict := htrace'.trans_lt hbound
  rw [hCenergy, hb2, hEnd] at hstrict
  exact hstrict

theorem exists_contMDiffOn_lCost_upper_support_hess_trace_lt_energy
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∃ (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegularizedCurve S T x Z s)) (Omega : Set Real),
      IsOpen Omega ∧ Icc (0 : Real) (Real.sqrt tau) ⊆ Omega ∧
      (∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (lRegularizedCurve S T x Z s) (P i s) : TangentBundle I M)) Omega) ∧
      (∀ i, IsLAdapted S T (lRegularizedCurve S T x Z) (P i) Omega) ∧
      (∀ i j, (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = if i = j then 1 else 0) ∧
      ∃ U : Set M, IsOpen U ∧ lExp S T x Z tau ∈ U ∧
        ∃ F : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ F U ∧
          F (lExp S T x Z tau) = lCost S T x (lExp S T x Z tau) tau ∧
          (∀ y ∈ U, lCost S T x y tau ≤ F y) ∧
          (∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) <
            (Module.finrank Real E : Real) / Real.sqrt tau -
              Real.sqrt tau * S.scalar (T - tau) (lExp S T x Z tau) -
              lCost S T x (lExp S T x Z tau) tau / (2 * tau) +
              (S.base.metric (T - tau)).inner (lExp S T x Z tau)
                (lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau))
                (lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau)) /
                  (4 * Real.sqrt tau) + epsilon := by
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_lt_energy
      (I := I) S hS K T x hmin hreg hRm hepsilon
  exact ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
    U, hUopen, hyU, F, hFsm, hcontact, hupper, htrace⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
