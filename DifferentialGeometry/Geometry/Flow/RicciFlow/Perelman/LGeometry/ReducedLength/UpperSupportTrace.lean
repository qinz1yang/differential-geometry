import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.GradientEnergy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff _root_.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem exists_contMDiffOn_redLength_upper_support_hess_trace_lt
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
        ∃ phi : M → Real, ContMDiffOn I 𝓘(Real, Real) ∞ phi U ∧
          phi (lExp S T x Z tau) = redLength S T x (lExp S T x Z tau) tau ∧
          (∀ y ∈ U, redLength S T x y tau ≤ phi y) ∧
          gradientFun (I := I) (S.base.metric (T - tau)) phi
            (lExp S T x Z tau) = (2 * Real.sqrt tau)⁻¹ •
              lVelocity (I := I) (lRegularizedCurve S T x Z) (Real.sqrt tau) ∧
          (∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau)
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) <
            (1 / 2 : Real) * (S.base.metric (T - tau)).inner (lExp S T x Z tau)
              (gradientFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau))
              (gradientFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau)) -
              (1 / 2 : Real) * S.scalar (T - tau) (lExp S T x Z tau) +
              ((Module.finrank Real E : Real) -
                redLength S T x (lExp S T x Z tau) tau) / (2 * tau) + epsilon := by
  let b : Real := Real.sqrt tau
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hEnd : lRegularizedCurve S T x Z b = lExp S T x Z tau := rfl
  have hscale : 0 < 2 * b := mul_pos (by norm_num) hb
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_lt_energy
      (I := I) S hS K T x hmin hreg hRm (mul_pos hscale hepsilon)
  let phi : M → Real := (2 * b)⁻¹ • F
  have hphism : ContMDiffOn I 𝓘(Real, Real) ∞ phi U := by
    change ContMDiffOn I 𝓘(Real, Real) ∞ (fun y ↦ (2 * b)⁻¹ * F y) U
    exact contMDiffOn_const.mul hFsm
  have hphicontact : phi (lExp S T x Z tau) =
      redLength S T x (lExp S T x Z tau) tau := by
    change (2 * b)⁻¹ * F (lExp S T x Z tau) =
      lCost S T x (lExp S T x Z tau) tau / (2 * b)
    rw [hcontact, div_eq_mul_inv, mul_comm]
  have hphiupper : ∀ y ∈ U, redLength S T x y tau ≤ phi y := by
    intro y hy
    change lCost S T x y tau / (2 * b) ≤ (2 * b)⁻¹ * F y
    calc
      _ ≤ F y / (2 * b) := div_le_div_of_nonneg_right (hupper y hy) hscale.le
      _ = _ := by rw [div_eq_mul_inv, mul_comm]
  have hFdiff : MDifferentiableAt I 𝓘(Real, Real) F (lExp S T x Z tau) :=
    (hFsm (lExp S T x Z tau) hyU).contMDiffAt (hUopen.mem_nhds hyU)
      |>.mdifferentiableAt (by simp)
  have hphigrad : gradientFun (I := I) (S.base.metric (T - tau)) phi
      (lExp S T x Z tau) = (2 * b)⁻¹ •
        lVelocity (I := I) (lRegularizedCurve S T x Z) b := by
    change gradientFun (I := I) (S.base.metric (T - tau)) ((2 * b)⁻¹ • F)
      (lExp S T x Z tau) = _
    rw [gradientFun_const_smul _ _ hFdiff, hgrad]
    rfl
  have htraceScale : (∑ i : Fin (Module.finrank Real E),
      hessFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau)
        (P i b) (P i b)) =
      (∑ i : Fin (Module.finrank Real E),
        hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
          (P i b) (P i b)) / (2 * b) := by
    change (∑ i : Fin (Module.finrank Real E),
      hessFun (I := I) (S.base.metric (T - tau)) ((2 * b)⁻¹ • F)
        (lExp S T x Z tau) (P i b) (P i b)) = _
    rw [hessFun_smul]
    change (∑ i : Fin (Module.finrank Real E), (2 * b)⁻¹ *
      hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
        (P i b) (P i b)) = _
    rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  have henergy :
      ((Module.finrank Real E : Real) / b -
        b * S.scalar (T - tau) (lExp S T x Z tau) -
        lCost S T x (lExp S T x Z tau) tau / (2 * tau) +
        (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (lVelocity (I := I) (lRegularizedCurve S T x Z) b)
          (lVelocity (I := I) (lRegularizedCurve S T x Z) b) / (4 * b) +
        2 * b * epsilon) / (2 * b) =
      (1 / 2 : Real) * (S.base.metric (T - tau)).inner (lExp S T x Z tau)
        (gradientFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau))
        (gradientFun (I := I) (S.base.metric (T - tau)) phi (lExp S T x Z tau)) -
        (1 / 2 : Real) * S.scalar (T - tau) (lExp S T x Z tau) +
        ((Module.finrank Real E : Real) -
          redLength S T x (lExp S T x Z tau) tau) / (2 * tau) + epsilon := by
    rw [hphigrad]
    rw [show redLength S T x (lExp S T x Z tau) tau =
      lCost S T x (lExp S T x Z tau) tau / (2 * b) from rfl]
    rw [← hEnd]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hb2]
    field_simp [hb.ne']
    ring
  refine ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
    U, hUopen, hyU, phi, hphism, hphicontact, hphiupper, hphigrad, ?_⟩
  rw [htraceScale]
  exact (div_lt_div_of_pos_right htrace hscale).trans_eq henergy

end DifferentialGeometry.PDE.RicciFlow.Perelman
