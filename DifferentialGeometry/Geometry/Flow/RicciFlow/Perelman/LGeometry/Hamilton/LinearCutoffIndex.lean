import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.AdaptedCutoffTrace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Hamilton.TraceIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized
import DifferentialGeometry.Bundle.Section


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped BigOperators Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [TopologicalSpace H] {I : ModelWithCorners Real E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lRegularizedIndex_trace_linear_cutoff_eq_hamilton
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (a b : Real)
    (ha : 0 < a) (hab : a < b) (hbdom : b ∈ lRegularizedDomain S T x Z)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
    {Omega : Set Real} (hOmega : IsOpen Omega)
    (hsegment : Icc (0 : Real) b ⊆ Omega)
    (hPsm : ∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent (2 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (lRegularizedCurve S T x Z s) (P i s) : TangentBundle I M)) Omega)
    (hDP : ∀ i, IsLAdapted S T (lRegularizedCurve S T x Z) (P i) (Icc a b))
    (hON : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (lRegularizedCurve S T x Z b)
        (P i b) (P j b) = if i = j then 1 else 0) :
    2 * (∑ i : Fin (Module.finrank Real E),
      lRegularizedIndex S T (lRegularizedCurve S T x Z)
        (fun s ↦ ((s - a) / (b - a)) • P i s)
        (fun s ↦ ((s - a) / (b - a)) • P i s) a b) =
      (Module.finrank Real E : Real) / (b - a) -
        2 * b * S.scalar (T - b ^ 2) (lRegularizedCurve S T x Z b) -
        lKTail S T (lRegularizedCurve S T x Z) a b / (b - a) ^ 2 := by
  let gamma : Real → M := lRegularizedCurve S T x Z
  let chi : Real → Real := fun s ↦ (s - a) / (b - a)
  have hb : 0 < b := ha.trans hab
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact lRegularizedDomain_regularity S T x Z
      (lRegularizedDomain_segment S T x Z hbdom (ha.le.trans hs.1) hs.2)
  have hgeo := lRegularizedCurve_isLRegularizedCurveOn (I := I) S hS T x Z hb hbdom
  have hgamma : ∀ s ∈ Icc a b, MDifferentiableAt 𝓘(Real, Real) I gamma s := by
    intro s hs
    apply (hgeo.2.2 s ?_).2.1
    rw [uIcc_of_le hb.le]
    exact ⟨ha.le.trans hs.1, hs.2⟩
  have hPdiff : ∀ i s, s ∈ Icc a b →
      DifferentiableAt Real (chartRepAt (I := I) gamma (P i) s) s := by
    intro i s hs
    apply differentiableAt_chartRepAt_of_contMDiffAt_two
    exact ((hPsm i s (hsegment ⟨ha.le.trans hs.1, hs.2⟩)).contMDiffAt
      (hOmega.mem_nhds (hsegment ⟨ha.le.trans hs.1, hs.2⟩)))
  have hchi : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) (2 : Nat) chi :=
    (contMDiff_id.sub contMDiff_const).div_const (b - a)
  have hWsm : ∀ i, ContMDiffOn 𝓘(Real, Real) I.tangent (2 : Nat)
      (fun s : Real ↦
        (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (gamma s) (chi s • P i s) : TangentBundle I M)) Omega :=
    fun i ↦ hchi.contMDiffOn.smul_bundle (hPsm i)
  have hIint : ∀ i, IntervalIntegrable
      (lRegularizedIndexIntegrand S T gamma
        (fun s ↦ chi s • P i s) (fun s ↦ chi s • P i s)) volume a b := by
    intro i
    apply intervalIntegrable_lRegularizedIndexIntegrand_of_contMDiffOn
      (I := I) S hS T a b gamma _ _ hOmega
    · intro s hs
      rw [uIcc_of_le hab.le] at hs
      exact hsegment ⟨ha.le.trans hs.1, hs.2⟩
    · exact hWsm i
    · exact hWsm i
    · intro s hs
      exact hreg s (by simpa only [uIcc_of_le hab.le] using hs)
  have hHamBase : IntervalIntegrable (lHamSq S T gamma) volume a b := by
    apply (lRayHam_int (I := I) S hS T x Z hb hbdom).mono_set
    rw [uIcc_of_le hab.le, uIcc_of_le hb.le]
    exact Icc_subset_Icc ha.le le_rfl
  have hweight : ContinuousOn (fun s ↦ (chi s / s) ^ 2) (uIcc a b) := by
    rw [uIcc_of_le hab.le]
    exact (hchi.continuous.continuousOn.div continuousOn_id
      (fun s hs ↦ ne_of_gt (ha.trans_le hs.1))).pow 2
  have hHam : IntervalIntegrable
      (fun s ↦ (chi s / s) ^ 2 * lHamSq S T gamma s) volume a b :=
    hHamBase.continuousOn_mul hweight
  have hderiv : ∀ s ∈ Icc a b, HasDerivAt chi (1 / (b - a)) s := by
    intro s _
    exact ((hasDerivAt_id s).sub_const a).div_const (b - a)
  have henergy : IntervalIntegrable (fun _ : Real ↦ (1 / (b - a)) ^ 2) volume a b :=
    intervalIntegrable_const
  have htrace := lRegularizedIndex_trace_smul_function (I := I)
    S hS T gamma P chi (fun _ ↦ 1 / (b - a)) a b ha hab.le
    hderiv hreg hgamma hPdiff hDP hON hIint henergy hHam
  have henergyEq : (∫ _s in a..b, (1 / (b - a)) ^ 2) = 1 / (b - a) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp [hba]
  have hHamEq : 2 * (∫ s in a..b, (chi s / s) ^ 2 * lHamSq S T gamma s) =
      lKTail S T gamma a b / (b - a) ^ 2 := by
    have heq : (∫ s in a..b, (chi s / s) ^ 2 * lHamSq S T gamma s) =
        (∫ s in a..b, ((s - a) / s) ^ 2 * lHamSq S T gamma s) / (b - a) ^ 2 := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : s ∈ Icc a b := by simpa only [uIcc_of_le hab.le] using hs
      have hs0 : s ≠ 0 := ne_of_gt (ha.trans_le hs'.1)
      dsimp only [chi]
      field_simp [hba, hs0]
    rw [heq, lKTail]
    ring
  have hchia : chi a = 0 := by simp only [chi, sub_self, zero_div]
  have hchib : chi b = 1 := by simp only [chi, div_self hba]
  change 2 * (∑ i : Fin (Module.finrank Real E),
    lRegularizedIndex S T gamma (fun s ↦ chi s • P i s)
      (fun s ↦ chi s • P i s) a b) = _
  rw [htrace, henergyEq, hchia, hchib]
  simp only [one_pow, zero_pow (by norm_num : (2 : Nat) ≠ 0), mul_one,
    mul_zero]
  linear_combination -hHamEq

end DifferentialGeometry.PDE.RicciFlow.Perelman
