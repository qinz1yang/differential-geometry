import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartRamp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.Construction.TwoPieceSplicing

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
theorem exists_lC1_join
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a c b : Real) (hac : a < c) (hcb : c < b)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (alpha beta : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha
      (Icc a c))
    (hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b))
    (hnode : alpha c = beta c) :
    ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma a = alpha a ∧ gamma b = beta b := by
  obtain ⟨eta, m, t, p, w, heta0, heta1, htmono, ht0, htlast,
      _hcnode, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb alpha beta
      halpha hbeta hnode
  obtain ⟨delta, _u, hdelta, hdelta0, hdeltab, _hsrcDelta,
      _hrepDelta, _hu, _hunif, _hdeltaAct⟩ :=
    lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T a b t htmono ht0 htlast p eta w hsrc hrep hreg
  refine ⟨delta 0, hdelta 0, ?_, ?_⟩
  · exact (hdelta0 0).trans (heta0 ⟨le_rfl, hac.le⟩)
  · exact (hdeltab 0).trans (heta1 ⟨hcb.le, le_rfl⟩)

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
theorem exists_lC1_move
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (b : Real) (hb : 0 < b)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (p : M) {K : Set E} (hK : Convex Real K)
    (hKtar : K ⊆ (extChartAt I p).target) {q q0 : E}
    (hq : q ∈ K) (hq0 : q0 ∈ K)
    (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hstart : alpha 0 = x)
    (hend : alpha b = (extChartAt I p).symm q) :
    ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = (extChartAt I p).symm q0 := by
  let c : Real := b / 2
  let L : Real := b - c
  have hc : 0 < c := half_pos hb
  have hcb : c < b := half_lt_self hb
  have hL : 0 < L := sub_pos.mpr hcb
  let alpha0 : Real → M := fun s ↦ alpha ((b / c) * s)
  let z : Real → E := fun s ↦ q + ((s - c) / L) • (q0 - q)
  let beta : Real → M := fun s ↦ (extChartAt I p).symm (z s)
  have halpha0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha0
      (Icc (0 : Real) c) := by
    exact (halpha.comp
      (contDiff_const.mul contDiff_id).contMDiff).contMDiffOn
  have hz : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real E) 1 z := by
    exact (contDiff_const.add
      (((contDiff_id.sub contDiff_const).div_const L).smul
        contDiff_const)).contMDiff
  have hzK : MapsTo z (Icc c b) K := by
    intro s hs
    let r : Real := (s - c) / L
    have hr : r ∈ Icc (0 : Real) 1 := by
      exact ⟨div_nonneg (sub_nonneg.mpr hs.1) hL.le,
        (div_le_one hL).2 (by simpa only [L] using sub_le_sub_right hs.2 c)⟩
    simpa only [z, r, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      add_comm] using hK.lineMap_mem hq hq0 hr
  have hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b) := by
    exact (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp
      hz.contMDiffOn (fun s hs ↦ hKtar (hzK hs))
  have halpha0c : alpha0 c = (extChartAt I p).symm q := by
    change alpha ((b / c) * c) = (extChartAt I p).symm q
    rw [div_mul_cancel₀ b hc.ne']
    exact hend
  have hbetac : beta c = (extChartAt I p).symm q := by
    change (extChartAt I p).symm (q + ((c - c) / L) • (q0 - q)) = _
    simp only [sub_self, zero_div, zero_smul, add_zero]
  have hbetab : beta b = (extChartAt I p).symm q0 := by
    change (extChartAt I p).symm (q + ((b - c) / L) • (q0 - q)) = _
    rw [show b - c = L by rfl, div_self hL.ne', one_smul]
    congr 1
    abel
  obtain ⟨gamma, hgamma, hgamma0, hgammab⟩ :=
    exists_lC1_join (I := I) S hS T 0 c b hc hcb hreg
      alpha0 beta halpha0 hbeta (halpha0c.trans hbetac.symm)
  refine ⟨gamma, hgamma, ?_, ?_⟩
  · rw [hgamma0]
    change alpha ((b / c) * 0) = x
    rw [mul_zero, hstart]
  · exact hgammab.trans hbetab

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem lCost_zero_no_curve
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (b : Real) (hb : 0 < b)
    (hno : ¬ ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = y) :
    lCost S T x y (b ^ 2) = 0 := by
  unfold lCost
  have hempty : {r : Real | ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha (Real.sqrt (b ^ 2)) = y ∧
        lLength S T (squareRootReparametrization alpha) 0 (b ^ 2) = r} = ∅ := by
    ext r
    simp only [mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨alpha, halpha, hstart, hend, _hr⟩
    exact hno ⟨alpha, halpha, hstart, by
      simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hend⟩
  rw [hempty, Real.sInf_empty]

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
theorem lNoCurve_nhds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (b : Real) (hb : 0 < b)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (p : M) {q0 : E} (hq0 : q0 ∈ (extChartAt I p).target)
    (hno : ¬ ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = (extChartAt I p).symm q0) :
    ∃ ε > 0, ∀ q ∈ Metric.ball q0 ε,
      ¬ ∃ alpha : Real → M,
        ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
          alpha 0 = x ∧ alpha b = (extChartAt I p).symm q := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1
    (isOpen_extChartAt_target (I := I) p) q0 hq0
  refine ⟨ε, hε, ?_⟩
  intro q hq hreach
  obtain ⟨alpha, halpha, hstart, hend⟩ := hreach
  obtain ⟨gamma, hgamma, hgamma0, hgammab⟩ :=
    exists_lC1_move (I := I) S hS T x b hb hreg p
      (convex_ball q0 ε) hball hq (Metric.mem_ball_self hε)
      alpha halpha hstart hend
  exact hno ⟨gamma, hgamma, hgamma0, hgammab⟩

omit [NeZero (Module.finrank Real E)] in
omit [CompactSpace M] in
theorem lCost_zero_lip
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (b : Real) (hb : 0 < b)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (p : M) {q0 : E} (hq0 : q0 ∈ (extChartAt I p).target)
    (hno : ¬ ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = (extChartAt I p).symm q0) :
    ∃ ε > 0, LipschitzOnWith 0
      (fun q ↦ lCost S T x ((extChartAt I p).symm q) (b ^ 2))
      (Metric.ball q0 ε) := by
  obtain ⟨ε, hε, hnoBall⟩ :=
    lNoCurve_nhds (I := I) S hS T x b hb hreg p hq0 hno
  refine ⟨ε, hε, (LipschitzOnWith.zero_iff _).2 ?_⟩
  intro q hq r hr
  rw [lCost_zero_no_curve (I := I) S T x
      ((extChartAt I p).symm q) b hb (hnoBall q hq),
    lCost_zero_no_curve (I := I) S T x
      ((extChartAt I p).symm r) b hb (hnoBall r hr)]

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
