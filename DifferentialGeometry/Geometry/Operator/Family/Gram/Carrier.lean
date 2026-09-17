import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic

section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor.Coordinates Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartGramOp_continuousOn_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    (alpha : M) {K : Set E} (hK : K ⊆ (extChartAt I alpha).target) :
    ContinuousOn (chartGramOp (I := I) G alpha) (D.carrier ×ˢ K) := by
  apply continuousOn_chartGramOp G alpha
  intro i j
  let P := {q : ℝ × E // q ∈ D.carrier ×ˢ K}
  let b : P → M := fun q => (extChartAt I alpha).symm q.1.2
  have hb : Continuous b := by
    exact (continuousOn_extChartAt_symm alpha).comp_continuous
      (continuous_snd.comp continuous_subtype_val) (fun q => hK q.2.2)
  have hbase (q : P) : b q ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    have hs := (extChartAt I alpha).map_target (hK q.2.2)
    simpa only [b, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hs
  let v : Fin 2 → (q : P) → TangentSpace I (b q) := fun k q =>
    chartBasisVecFiber (I := I) alpha (if k = 0 then i else j) (b q)
  have hv : ∀ k : Fin 2, Continuous (fun q : P =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v k q)) := by
    intro k
    exact (chartBasisVec_contMDiffOn (I := I) alpha (if k = 0 then i else j)).continuousOn.comp_continuous
      hb hbase
  have heval := hG.metricTensor_cont.eval_continuous
    (P := P) (τ := fun q => q.1.1) (b := b)
    (continuous_fst.comp continuous_subtype_val) (fun q => q.2.1) hb (v := v) hv
  rw [continuousOn_iff_continuous_domRestrict]
  convert heval using 1
  funext q
  simp only [chartGramOnE, chartGramMatrix]
  rw [Tensor0SBundle.metricTensorField_apply]
  simp [v, b]

theorem chartGramOp_continuousOn_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set ℝ} (hJ : J ⊆ D.carrier) (alpha : M) {K : Set E}
    (hK : K ⊆ (extChartAt I alpha).target) :
    ContinuousOn (chartGramOp (I := I) G alpha) (J ×ˢ K) :=
  (chartGramOp_continuousOn_carrier hG alpha hK).mono (prod_mono_left hJ)

end DifferentialGeometry.Geometry.Curvature

end

end

section

noncomputable section
open Filter MeasureTheory Set
open scoped Manifold Topology ContDiff Interval
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chartGramOp_uniform_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.carrier) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
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
  have hcont := chartGramOp_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart
  have huc : UniformContinuousOn (chartGramOp (I := I) G alpha) (J ×ˢ K) :=
    (hJc.prod hKc).uniformContinuousOn_of_continuous hcont
  apply huc.comp_tendstoUniformly_eventually
  · filter_upwards [huK] with i hi
    exact fun p => ⟨htau p, hi p⟩
  · exact fun p => ⟨htau p, hlimK p⟩
  · exact hpair

theorem chartGramOp_bound_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.carrier) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
    (hKc : IsCompact K) :
    ∃ C : NNReal, ∀ p ∈ J ×ˢ K, ‖chartGramOp (I := I) G alpha p‖ ≤ C := by
  have hcont := chartGramOp_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart
  obtain ⟨C, hC⟩ := (hJc.prod hKc).bddAbove_image hcont.norm
  refine ⟨⟨max C 0, le_max_right C 0⟩, ?_⟩
  intro p hp
  change ‖chartGramOp (I := I) G alpha p‖ ≤ max C 0
  exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)

end DifferentialGeometry.Geometry.Curvature

end

end

section

noncomputable section
open Bundle Filter MeasureTheory Set
open scoped Manifold Topology ContDiff Interval
namespace DifferentialGeometry.Geometry.Curvature
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem chartGramOp_lower_of_carrier {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G.metric)
    {J : Set Real} (hJreg : J ⊆ D.carrier) (hJc : IsCompact J)
    (alpha : M) {K : Set E} (hKchart : K ⊆ (extChartAt I alpha).target)
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
        (chartGramOp_continuousOn_of_carrier (I := I) hG hJreg alpha hKchart).comp
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
          hKchart hq₀.1.2
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

end

end
