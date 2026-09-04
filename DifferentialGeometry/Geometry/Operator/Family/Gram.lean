import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.InnerBridge
import DifferentialGeometry.Geometry.Metric.Family.DifferentialOperatorRegularity
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse
import DifferentialGeometry.Bundle.TangentCoordChange
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Geometry.Curvature

open Analysis.Parabolic.TensorSpectral
open Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (∞ : WithTop ℕ∞) M]

noncomputable def chartGramOp {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    (p : Real × E) : E →L[Real] E :=
  IsCoercive.gramCLM (F := E)
    (chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
    ((extChartAt I alpha).symm p.2))

theorem chartGramOp_inner {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    (p : Real × E) (v w : E) :
    inner Real (chartGramOp (I := I) G alpha p v) w =
      (G.metric p.1).inner ((extChartAt I alpha).symm p.2)
        (Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
          (I := I) (M := M) alpha ((extChartAt I alpha).symm p.2) v)
        (Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
          (I := I) (M := M) alpha ((extChartAt I alpha).symm p.2) w) := by
  rw [chartGramOp, IsCoercive.gramCLM_apply,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  exact chartGramBilin_eq_innerJinv (I := I) (M := M)
    (G.metric p.1) alpha ((extChartAt I alpha).symm p.2) v w

theorem chartGramOp_change {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) {p q x : M}
    (hp : x ∈ (extChartAt I p).source) (hq : x ∈ (extChartAt I q).source)
    (t : Real) (v w : E) :
    inner Real (chartGramOp (I := I) G p (t, extChartAt I p x) v) w =
      inner Real
        (chartGramOp (I := I) G q (t, extChartAt I q x)
          (tangentCoordChange I p q x v))
        (tangentCoordChange I p q x w) := by
  rw [chartGramOp_inner, chartGramOp_inner,
    (extChartAt I p).left_inv hp, (extChartAt I q).left_inv hq]
  simp only [Tensor.Tensor0SRiemannian.chartJinv_apply,
    symmL_coordChange hp hq]

theorem chartGramOp_self {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    (p : Real × E) : IsSelfAdjoint (chartGramOp (I := I) G alpha p) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro v w
  change inner Real (chartGramOp (I := I) G alpha p v) w =
    inner Real v (chartGramOp (I := I) G alpha p w)
  rw [chartGramOp_inner,
    real_inner_comm (chartGramOp (I := I) G alpha p w) v,
    chartGramOp_inner]
  exact (G.metric p.1).symm ((extChartAt I alpha).symm p.2) _ _

theorem chartGramOp_nonneg {D : RealTimeInterval}
    (G : MetricConnectionFamilyOn (I := I) (M := M) D) (alpha : M)
    (p : Real × E) (v : E) :
    0 ≤ inner Real (chartGramOp (I := I) G alpha p v) v := by
  rw [chartGramOp_inner]
  let w := Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
    (I := I) (M := M) alpha ((extChartAt I alpha).symm p.2) v
  change 0 ≤ (G.metric p.1).inner ((extChartAt I alpha).symm p.2) w w
  by_cases hw : w = 0
  · rw [hw]
    have hzero := congrArg
      (fun L : TangentSpace I ((extChartAt I alpha).symm p.2) →L[Real] Real => L 0)
      ((G.metric p.1).inner ((extChartAt I alpha).symm p.2)).map_zero
    calc
      0 ≤ 0 := le_rfl
      _ = (G.metric p.1).inner ((extChartAt I alpha).symm p.2) 0 0 := hzero.symm
  · exact ((G.metric p.1).pos ((extChartAt I alpha).symm p.2) w hw).le

theorem chartGramOp_cont {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJ : J ⊆ D.regular) (alpha : M) {K : Set E}
    (hK : K ⊆ interior (extChartAt I alpha).target) :
    ContinuousOn (chartGramOp (I := I) G alpha) (J ×ˢ K) := by
  classical
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      ContinuousOn
        (fun p : Real × E =>
          chartGramOnE (I := I) (G.metric p.1) alpha i j p.2)
        (J ×ˢ K) := by
    intro i j
    exact (hG.chartGramOnE_contDiffOn hJ alpha i j).continuousOn.mono
      (prod_mono_right hK)
  have hbilin : ContinuousOn
      (fun p : Real × E =>
        chartGramBilin (E := E) (I := I) (M := M) (G.metric p.1) alpha
          ((extChartAt I alpha).symm p.2))
      (J ×ˢ K) := by
    change ContinuousOn
      (fun p : Real × E =>
        ∑ j : Fin (Module.finrank Real E), ∑ k : Fin (Module.finrank Real E),
          chartGramOnE (I := I) (G.metric p.1) alpha j k p.2 •
            (chartCoordCLM E j).smulRight (chartCoordCLM E k))
      (J ×ˢ K)
    exact continuousOn_finsetSum _ fun j _ =>
      continuousOn_finsetSum _ fun k _ => (hentry j k).smul continuousOn_const
  exact (IsCoercive.gramCLM (F := E)).continuous.comp_continuousOn hbilin

theorem chartGramOp_unif {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (hKc : IsCompact K) {P idx : Type*}
    {l : Filter idx} {tau : P → Real} {u : idx → P → E} {uLim : P → E}
    (htau : ∀ p, tau p ∈ J) (huK : ∀ᶠ i in l, ∀ p, u i p ∈ K)
    (hlimK : ∀ p, uLim p ∈ K) (hu : TendstoUniformly u uLim l) :
    TendstoUniformly
      (fun i p => chartGramOp (I := I) G alpha (tau p, u i p))
      (fun p => chartGramOp (I := I) G alpha (tau p, uLim p)) l := by
  have htauSelf : TendstoUniformly (fun _ : idx => tau) tau l := by
    rw [tendstoUniformly_iff_tendsto]
    exact tendsto_diag_uniformity (tau ∘ Prod.snd) (l ×ˢ ⊤)
  have hpairTwo := htauSelf.prodMk hu
  have hpair : TendstoUniformly
      (fun i p => (tau p, u i p)) (fun p => (tau p, uLim p)) l := by
    rw [tendstoUniformly_iff_tendsto] at hpairTwo ⊢
    have hdiag : Tendsto (fun i : idx => (i, i)) l (l ×ˢ l) :=
      tendsto_id.prodMk tendsto_id
    have hpull : Tendsto (fun q : idx × P => ((q.1, q.1), q.2))
        (l ×ˢ ⊤) ((l ×ˢ l) ×ˢ ⊤) :=
      (hdiag.comp tendsto_fst).prodMk tendsto_snd
    exact hpairTwo.comp hpull
  have hcont := chartGramOp_cont (I := I) hG hJreg alpha hKchart
  have huc : UniformContinuousOn (chartGramOp (I := I) G alpha) (J ×ˢ K) :=
    (hJc.prod hKc).uniformContinuousOn_of_continuous hcont
  apply huc.comp_tendstoUniformly_eventually
  · filter_upwards [huK] with i hi
    exact fun p => ⟨htau p, hi p⟩
  · exact fun p => ⟨htau p, hlimK p⟩
  · exact hpair

theorem chartGramOp_bound {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (hKc : IsCompact K) :
    ∃ C : NNReal, ∀ p ∈ J ×ˢ K, ‖chartGramOp (I := I) G alpha p‖ ≤ C := by
  have hcont := chartGramOp_cont (I := I) hG hJreg alpha hKchart
  obtain ⟨C, hC⟩ := (hJc.prod hKc).bddAbove_image hcont.norm
  refine ⟨⟨max C 0, le_max_right C 0⟩, ?_⟩
  intro p hp
  change ‖chartGramOp (I := I) G alpha p‖ ≤ max C 0
  exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)

theorem chartGramOp_lower {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.regular) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ interior (extChartAt I alpha).target)
    (hKc : IsCompact K) :
    ∃ c : Real, 0 < c ∧ ∀ q ∈ J ×ˢ K, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ inner Real (chartGramOp (I := I) G alpha q v) v := by
  classical
  by_cases hE : Nontrivial E
  · let := hE
    let Q : ((Real × E) × E) → Real := fun q =>
      inner Real (chartGramOp (I := I) G alpha q.1 q.2) q.2
    let S : Set E := Metric.sphere 0 1
    have : ProperSpace E := FiniteDimensional.proper Real E
    have hSc : IsCompact S := isCompact_sphere 0 1
    have hSne : S.Nonempty := by
      rcases exists_ne (0 : E) with ⟨v, hv⟩
      refine ⟨‖v‖⁻¹ • v, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg v)]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)
    have hQc : ContinuousOn Q ((J ×ˢ K) ×ˢ S) := by
      have hA : ContinuousOn
          (fun q : (Real × E) × E => chartGramOp (I := I) G alpha q.1)
          ((J ×ˢ K) ×ˢ S) :=
        (chartGramOp_cont (I := I) hG hJreg alpha hKchart).comp
          continuousOn_fst (fun q hq => hq.1)
      exact (hA.clm_apply continuousOn_snd).inner continuousOn_snd
    by_cases hJK : (J ×ˢ K).Nonempty
    · have hCpt : IsCompact ((J ×ˢ K) ×ˢ S) :=
        (hJc.prod hKc).prod hSc
      obtain ⟨q₀, hq₀, hmin⟩ :=
        hCpt.exists_isMinOn (hJK.prod hSne) hQc
      have hq₀v : q₀.2 ≠ 0 := by
        intro hz
        have hs := hq₀.2
        rw [hz, Metric.mem_sphere, dist_self] at hs
        exact zero_ne_one hs
      have hq₀base :
          (extChartAt I alpha).symm q₀.1.2 ∈
            (trivializationAt E (TangentSpace I) alpha).baseSet := by
        have htarg : q₀.1.2 ∈ (extChartAt I alpha).target :=
          interior_subset (hKchart hq₀.1.2)
        have hsrc := (extChartAt I alpha).map_target htarg
        rw [extChartAt_source] at hsrc
        exact hsrc
      have hq₀triv :
          Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
              (I := I) (M := M) alpha ((extChartAt I alpha).symm q₀.1.2) q₀.2 ≠ 0 := by
        intro hz
        have hleft := Tensor.Tensor0SRiemannian.chartJ_chartJinv
          (I := I) (M := M) alpha hq₀base q₀.2
        rw [hz, map_zero] at hleft
        exact hq₀v hleft.symm
      have hq₀pos : 0 < Q q₀ := by
        dsimp only [Q]
        rw [chartGramOp_inner]
        exact (G.metric q₀.1.1).pos ((extChartAt I alpha).symm q₀.1.2) _ hq₀triv
      refine ⟨Q q₀, hq₀pos, ?_⟩
      intro q hq v
      by_cases hv : v = 0
      · subst hv
        simp
      · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
        let u : E := ‖v‖⁻¹ • v
        have huS : u ∈ S := by
          change u ∈ Metric.sphere 0 1
          rw [Metric.mem_sphere, dist_zero_right]
          change ‖‖v‖⁻¹ • v‖ = 1
          rw [norm_smul, norm_inv,
            Real.norm_eq_abs, abs_of_pos hvpos]
          exact inv_mul_cancel₀ hvpos.ne'
        have hle : Q q₀ ≤ Q (q, u) := hmin ⟨hq, huS⟩
        have hscale :
            inner Real (chartGramOp (I := I) G alpha q v) v = ‖v‖ ^ 2 * Q (q, u) := by
          simp only [Q, u, map_smul, real_inner_smul_left, real_inner_smul_right]
          field_simp [hvpos.ne']
        rw [hscale, mul_comm]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg ‖v‖)
    · refine ⟨1, one_pos, ?_⟩
      intro q hq
      exact absurd ⟨q, hq⟩ hJK
  · rw [not_nontrivial_iff_subsingleton] at hE
    refine ⟨1, one_pos, ?_⟩
    intro q hq v
    have hv : v = 0 := Subsingleton.elim v 0
    subst hv
    simp

end DifferentialGeometry.Geometry.Curvature
