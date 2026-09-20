import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.UpperSupport.GradientIndex
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.LinearCutoffIndex
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.AdaptedFrame


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open scoped BigOperators Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_le_hamilton
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau a : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (ha : 0 < a) (hab : a < Real.sqrt tau) :
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
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) ≤
            (Module.finrank Real E : Real) / (Real.sqrt tau - a) -
              2 * Real.sqrt tau * S.scalar (T - tau) (lExp S T x Z tau) -
              lKTail S T (lRegularizedCurve S T x Z) a (Real.sqrt tau) /
                (Real.sqrt tau - a) ^ 2 := by
  let b : Real := Real.sqrt tau
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hb : 0 < b := Real.sqrt_pos.mpr htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hab' : a < b := hab
  have hEnd : lRegularizedCurve S T x Z b = lExp S T x Z tau := rfl
  have hbdom : b ∈ lRegularizedDomain S T x Z := by
    have hpos := ((mem_lMinDomain S T x Z tau).mp hmin).1
    exact ((mem_lExpPosDom S T x Z tau).mp hpos).2.2
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON⟩ :=
    exists_lRegularizedCurve_adaptedFrame (I := I) S hS T x hb hbdom
  obtain ⟨U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, hcompare⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_le_index
      (IM := I) S hS K T x hmin hreg hRm ha hab
  have hP8 : ∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (P i s) : TangentBundle I M)) Omega :=
    fun i ↦ (hPsm i).of_le (by decide : (8 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have htrace := lRegularizedIndex_trace_linear_cutoff_eq_hamilton
    (I := I) S hS T x Z a b ha hab hbdom P hOmega hsegment
    (fun i ↦ (hP8 i).of_le (by decide : (2 : WithTop ℕ∞) ≤ (8 : WithTop ℕ∞)))
    (fun i s hs ↦ hDP i s (hsegment ⟨ha.le.trans hs.1, hs.2⟩)) hON
  have hONtau : ∀ i j, (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (P i b) (P j b) = if i = j then 1 else 0 := by
    intro i j
    rw [← hEnd, ← hb2]
    exact hON i j
  refine ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hONtau,
    U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, ?_⟩
  let W : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegularizedCurve S T x Z s) :=
    fun i s ↦ ((s - a) / (b - a)) • P i s
  have hcutoff : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) (8 : Nat)
      (fun s : Real ↦ (s - a) / (b - a)) :=
    (contMDiff_id.sub contMDiff_const).div_const (b - a)
  have hWsm : ∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent (8 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (W i s) : TangentBundle I M)) Omega :=
    fun i ↦ hcutoff.contMDiffOn.smul_bundle (hP8 i)
  have hWa : ∀ i, W i a = 0 := by
    intro i
    simp only [W, sub_self, zero_div, zero_smul]
  have hWb : ∀ i, W i b = P i b := by
    intro i
    change ((b - a) / (b - a)) • P i b = P i b
    rw [div_self (sub_ne_zero.mpr hab'.ne'), one_smul]
  have hsum : (∑ i : Fin (Module.finrank Real E),
      hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
        (P i b) (P i b)) ≤
      2 * ∑ i : Fin (Module.finrank Real E),
        lRegularizedIndex S T (lRegularizedCurve S T x Z) (W i) (W i) a b := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := hcompare (W i) Omega hOmega hsegment (hWsm i) (hWa i)
    change hessFun (I := I) (S.base.metric (T - tau)) F (lExp S T x Z tau)
      (W i b) (W i b) ≤
        2 * lRegularizedIndex S T (lRegularizedCurve S T x Z) (W i) (W i) a b at hi
    rw [hWb i] at hi
    exact hi
  have htrace' : 2 * (∑ i : Fin (Module.finrank Real E),
      lRegularizedIndex S T (lRegularizedCurve S T x Z) (W i) (W i) a b) =
      (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - tau) (lExp S T x Z tau) -
        lKTail S T (lRegularizedCurve S T x Z) a b / (b - a) ^ 2 := by
    rw [hb2, hEnd] at htrace
    exact htrace
  exact hsum.trans_eq htrace'

theorem exists_contMDiffOn_lCost_upper_support_hess_trace_le_hamilton
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau a : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (ha : 0 < a) (hab : a < Real.sqrt tau) :
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
              (P i (Real.sqrt tau)) (P i (Real.sqrt tau))) ≤
            (Module.finrank Real E : Real) / (Real.sqrt tau - a) -
              2 * Real.sqrt tau * S.scalar (T - tau) (lExp S T x Z tau) -
              lKTail S T (lRegularizedCurve S T x Z) a (Real.sqrt tau) /
                (Real.sqrt tau - a) ^ 2 := by
  obtain ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
      U, hUopen, hyU, F, hFsm, hcontact, hupper, hgrad, htrace⟩ :=
    exists_contMDiffOn_lCost_upper_support_gradient_hess_trace_le_hamilton
      (I := I) S hS K T x hmin hreg hRm ha hab
  exact ⟨P, Omega, hOmega, hsegment, hPsm, hDP, hON,
    U, hUopen, hyU, F, hFsm, hcontact, hupper, htrace⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
