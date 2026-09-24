import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalNormBound
import DifferentialGeometry.Geometry.Neck.NormalizedFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.QuadraticForm

noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount}

private local instance : SigmaCompactSpace (H.event i).incoming.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.event i).incoming.terminalRegularOpen.isOpen)

private theorem abs_metric_deriv_le_riemannNorm
    (j : Fin H.eventCount) {t : ℝ} (ht : t ∈ Ioo (H.time j.castSucc) (H.time j.succ))
    (x : (H.stage j.castSucc).Carrier) (v : TangentSpace ThreeModel x) :
    |deriv (fun u => ((H.event j).incoming.flow.base.metric u).inner x v v) t| ≤
      18 * (H.event j).incoming.riemannNorm t x *
        ((H.event j).incoming.flow.base.metric t).inner x v v := by
  let S := (H.event j).incoming.flow
  have hd := metricDerivAt S (H.event j).incoming.equation ⟨t, ht⟩ x v v
  have hquad := tensor02_quadForm_abs_le_of_unit_bound (S.base.metric t) (S.ricciAt t x)
    (fun u hu => ricci_quadratic_form_on_unit_vector_le_of_solution S x u hu) v
  change HasDerivAt (fun u => ((H.event j).incoming.flow.base.metric u).inner x v v)
    (-2 * S.ricciAt t x (vec2 v v)) t at hd
  rw [hd.deriv, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  have hdim : Module.finrank ℝ (TangentSpace ThreeModel x) = 3 := by
    change Module.finrank ℝ ThreeSpace = 3
    simp [ThreeSpace]
  rw [hdim] at hquad
  have hh := mul_le_mul_of_nonneg_left hquad (by norm_num : (0 : ℝ) ≤ 2)
  exact hh.trans_eq (by
    change 2 * ((3 : ℝ)^2 * (H.event j).incoming.riemannNorm t x *
      ((H.event j).incoming.flow.base.metric t).inner x v v) = _
    ring)



private theorem abs_extendedMetric_derivWithin_le_riemannNorm
    (j : Fin H.eventCount) {t : ℝ} (ht : t ∈ Icc (H.time j.castSucc) (H.time j.succ))
    (y : (H.event j).incoming.terminalRegularOpen)
    (v : TangentSpace ThreeModel y) :
    |derivWithin (fun u => ((H.event j).terminal.extendedMetric u).inner y v v)
      (Icc (H.time j.castSucc) (H.time j.succ)) t| ≤
      18 * Real.sqrt (Tensor0SBundle.normSq0S ((H.event j).terminal.extendedMetric t) y 4
        (metricRm04At ((H.event j).terminal.extendedMetric t) y)) *
        ((H.event j).terminal.extendedMetric t).inner y v v := by
  let W : TopologicalSpace.Opens (H.event j).incoming.terminalRegularOpen := ⊤
  let z : W := ⟨y, mem_univ y⟩
  have hh := abs_metric_inner_derivWithin_le_riemannNorm
    ((H.event j).terminal.closedSolution W (H.event j).incoming.lt.le)
    ((H.event j).terminal.closedSolution_isSolutionOn W le_rfl (H.event j).incoming.lt)
    (H.event j).incoming.lt Subset.rfl Subset.rfl
    ht z v
  simp only [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.closedSolution_metric,
    SolutionFamily.rm04, metricRm04_apply] at hh
  rw [rmNormSq_restrictOpen] at hh
  have hd : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by simp [ThreeSpace]
  rw [hd] at hh
  change |derivWithin (fun u => ((H.event j).terminal.extendedMetric u).inner y v v)
    (Icc (H.time j.castSucc) (H.time j.succ)) t| ≤
    2 * (3 : ℝ)^2 * Real.sqrt (Tensor0SBundle.normSq0S ((H.event j).terminal.extendedMetric t) y 4
      (metricRm04At ((H.event j).terminal.extendedMetric t) y)) *
      ((H.event j).terminal.extendedMetric t).inner y v v at hh
  exact hh.trans_eq (by ring)


theorem NormalizedNeck.exists_compact_footprint_historical_curvature_bound
    {δ₀ δ eps : ℝ} {k : ℕ} (N : NormalizedNeck (H.event i).terminal.metric δ₀ k)
    (hδ : δ₀ ≤ δ) (hδ1 : δ < 1) (hprecision : δ₀ ≤ eps)
    (hsmall : eps ≤ 1 / 8646) (hk : ⌈eps⁻¹⌉₊ ≤ k)
    (a : ℝ) (ha : 24 < a) (hpublic : δ⁻¹ + 1 ≤ a) (hfit : 4 * a < eps⁻¹)
    {q : ℝ} {C : ℝ≥0} (hq : 0 < q) (hqQ : q ≤ N.scale)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (first : Fin (H.eventCount + 1)) (hle : first ≤ i.castSucc)
    (hbound : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      ∀ x : (H.stage j.castSucc).Carrier, ∀ t ∈ Ioo (H.time j.castSucc) (H.time j.succ),
      q < (H.event j).incoming.flow.scalar t x →
      |derivWithin (fun v => (H.event j).incoming.flow.scalar v x) (Iic t) t| ≤
        C * (H.event j).incoming.flow.scalar t x ^ 2)
    (hpinch : ∀ j : Fin H.eventCount, first ≤ j.castSucc → j.castSucc ≤ i.castSucc →
      PhiAlmostNonnegative (H.event j).incoming.flow
        (Ico (H.time j.castSucc) (H.time j.succ)) Phi) :
    ∃ K : Set (H.event i).incoming.terminalRegularOpen,
      K = N.chart '' {z : neckBuffer δ₀ | -(3*a) ≤ z.val.2 ∧ z.val.2 ≤ 3*a} ∧
      IsCompact K ∧ IsConnected K ∧ N.center ∈ K ∧
      range (N.monoDelta hδ hδ1).chart ⊆ interior K ∧
      IsCompact (riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale)) ∧
      riemannianClosedBallOf (H.event i).terminal.metric N.center
        (2*a / Real.sqrt N.scale) ⊆ interior K ∧
      (∀ x ∈ K, metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * N.scale) ∧
      (∀ x ∈ K, ∀ A : BackwardPointTrace H first i.castSucc hle x.val,
        ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
        ∀ t ∈ Ico (H.time j.castSucc) (H.time j.succ),
        6 * C * (H.time i.succ - t) * N.scale ≤ 1 →
          (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * N.scale ∧
          (H.event j).incoming.riemannNorm t (A.point j.castSucc hf hl) ≤
            4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) ∧
          ∀ v : TangentSpace ThreeModel (A.point j.castSucc hf hl),
            H.time j.castSucc < t →
            |deriv (fun u => ((H.event j).incoming.flow.base.metric u).inner
              (A.point j.castSucc hf hl) v v) t| ≤
                72 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) *
                  ((H.event j).incoming.flow.base.metric t).inner
                    (A.point j.castSucc hf hl) v v) ∧
      ∀ x ∈ K, ∀ A : BackwardPointTrace H first i.castSucc hle x.val,
        ∀ j : Fin H.eventCount, ∀ hf : first ≤ j.castSucc, ∀ hl : j.castSucc ≤ i.castSucc,
        ∀ y : (H.event j).incoming.terminalRegularOpen,
          y.val = A.point j.castSucc hf hl →
          ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          6 * C * (H.time i.succ - t) * N.scale ≤ 1 →
            metricScalarAt ((H.event j).terminal.extendedMetric t) y ≤ 2 * N.scale ∧
            Real.sqrt (Tensor0SBundle.normSq0S ((H.event j).terminal.extendedMetric t) y 4
              (metricRm04At ((H.event j).terminal.extendedMetric t) y)) ≤
                4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) ∧
            ∀ v : TangentSpace ThreeModel y,
              |derivWithin (fun u => ((H.event j).terminal.extendedMetric u).inner y v v)
                (Icc (H.time j.castSucc) (H.time j.succ)) t| ≤
                72 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) *
                  ((H.event j).terminal.extendedMetric t).inner y v v := by
  obtain ⟨K,hK,hcompact,hconnected,hcenter,hchart,hball,hballsub,_,_⟩ :=
    N.exists_compact_long_neck_footprint hδ hδ1 hprecision hsmall hk a ha hpublic hfit
  have heps : 0 < eps := N.delta_pos.trans_le hprecision
  have hinv : eps⁻¹ ≤ δ₀⁻¹ := inv_anti₀ N.delta_pos hprecision
  have hk2 : 2 ≤ k := by
    have hi : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    have hh : (2 : ℝ) ≤ ⌈eps⁻¹⌉₊ := hi.trans (Nat.le_ceil _)
    exact (by exact_mod_cast hh : 2 ≤ ⌈eps⁻¹⌉₊).trans hk
  have hsc (x : (H.event i).incoming.terminalRegularOpen) (hx : x ∈ K) :
      metricScalarAt (H.event i).terminal.metric x ≤ (3 / 2 : ℝ) * N.scale := by
    rw [hK] at hx
    obtain ⟨z,hz,rfl⟩ := hx
    have hztest : z ∈ neckClosedTest δ₀ := by constructor <;> linarith [hz.1,hz.2]
    have hratio := (abs_le.mp (N.abs_scalar_ratio_sub_one_le hk2 (by linarith) z hztest)).2
    have hratio' : metricScalarAt (H.event i).terminal.metric (N.chart z) / N.scale ≤ 3 / 2 := by
      linarith
    exact (div_le_iff₀ N.scale_pos).mp hratio'
  refine ⟨K,hK,hcompact,hconnected,hcenter,hchart,hball,hballsub,hsc,?_,?_⟩
  · intro x hx A j hf hl t ht htime
    have htpos : 0 ≤ H.time i.succ - t := by
      have hji : j.val ≤ i.val := hl
      have htimeji : H.time j.succ ≤ H.time i.succ := H.time_strictMono.monotone (by
        change j.val + 1 ≤ i.val + 1
        omega)
      linarith [ht.2]
    have hA := fun j hf hl => hbound j hf hl (A.point j.castSucc hf hl)
    have hscalar := A.scalar_le_two_mul_of_terminal_scalar_le_three_halves x hq hqQ
      hA (hsc x hx) j hf hl ht htime
    have hrm := A.riemannNorm_le_of_terminal_scalar_le x hq hqQ hA
      ((hsc x hx).trans (by nlinarith [N.scale_pos])) hPhi hpinch j hf hl ht
      (by nlinarith [C.coe_nonneg, N.scale_pos])
    refine ⟨hscalar, hrm, ?_⟩
    intro v htlo
    have hd := abs_metric_deriv_le_riemannNorm j ⟨htlo, ht.2⟩
      (A.point j.castSucc hf hl) v
    apply hd.trans
    have hv := inner_self_nonneg ((H.event j).incoming.flow.base.metric t)
      (A.point j.castSucc hf hl) v
    nlinarith
  · intro x hx A j hf hl y hy t ht htime
    have hA := fun j hf hl => hbound j hf hl (A.point j.castSucc hf hl)
    have hboth : metricScalarAt ((H.event j).terminal.extendedMetric t) y ≤ 2 * N.scale ∧
        Real.sqrt (Tensor0SBundle.normSq0S ((H.event j).terminal.extendedMetric t) y 4
          (metricRm04At ((H.event j).terminal.extendedMetric t) y)) ≤
          4 * Real.sqrt 3 * (N.scale + Phi (4*N.scale) + Phi 0) := by
      rcases lt_or_eq_of_le ht.2 with hts | rfl
      · have hstage : (H.event j).incoming.flow.scalar t (A.point j.castSucc hf hl) ≤ 2 * N.scale :=
          A.scalar_le_two_mul_of_terminal_scalar_le_three_halves x hq hqQ hA (hsc x hx)
            j hf hl ⟨ht.1, hts⟩ htime
        have hrm := A.riemannNorm_le_of_terminal_scalar_le x hq hqQ hA
          ((hsc x hx).trans (by nlinarith [N.scale_pos])) hPhi hpinch j hf hl ⟨ht.1,hts⟩
          (by nlinarith [C.coe_nonneg, N.scale_pos])
        rw [(H.event j).terminal.extendedMetric_before hts,
          DifferentialGeometry.CheegerGromovCompactness.metricScalarAt_restrictOpen, rmNormSq_restrictOpen, hy]
        exact ⟨hstage, hrm⟩
      · rw [OrientedThreeStage.IncomingSlab.TerminalLimitMetric.extendedMetric_terminal]
        exact ⟨A.terminal_scalar_le_two_mul_of_time_sub_le x hq hqQ hA (hsc x hx)
          j hf hl y hy htime,
          A.riemannNorm_terminal_le_of_terminal_scalar_le x hq hqQ hA
            ((hsc x hx).trans (by nlinarith [N.scale_pos])) hPhi hpinch j hf hl y hy htime⟩
    refine ⟨hboth.1,hboth.2,?_⟩
    intro v
    apply (abs_extendedMetric_derivWithin_le_riemannNorm j ht y v).trans
    have hv := inner_self_nonneg ((H.event j).terminal.extendedMetric t) y v
    nlinarith [hboth.2]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
