import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.CarrierDensity
import DifferentialGeometry.Topology.Manifold.CurveChart.Subdivision

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem exists_contMDiff_one_lRegularizedAction_approximation_of_compatible_chartH1_pair_of_carrier
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T : Real) (t : Fin 3 → Real) (htmono : Monotone t)
    (p : Fin 2 → M)
    (v : (i : Fin 2) → timeH1 E (partitionIntervalLength t i))
    (htar : ∀ i, MapsTo (v i).toFun
      (Icc (0 : Real) (partitionIntervalLength t i)) (extChartAt I (p i)).target)
    (hnode : (extChartAt I (p 0)).symm
        ((v 0).toFun (partitionIntervalLength t 0)) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0))
    (hreg : ∀ s ∈ Icc (t 0) (t (Fin.last 2)), T - s ^ 2 ∈ D.carrier) :
    ∃ gamma : Real → M,
      Continuous gamma ∧
      (∀ i, MapsTo gamma
        (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
      (∀ i, EqOn (v i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (Icc (0 : Real) (partitionIntervalLength t i))) ∧
      gamma (t 0) = (extChartAt I (p 0)).symm ((v 0).toFun 0) ∧
      gamma (t (Fin.last 2)) = (extChartAt I (p 1)).symm
        ((v 1).toFun (partitionIntervalLength t 1)) ∧
      ∃ alpha : Nat → Real → M,
        ∃ w : (i : Fin 2) → Nat → timeH1 E (partitionIntervalLength t i),
          (∀ n, ContMDiff (modelWithCornersSelf Real Real) I 1 (alpha n)) ∧
          (∀ n, alpha n (t 0) = gamma (t 0)) ∧
          (∀ n, alpha n (t (Fin.last 2)) = gamma (t (Fin.last 2))) ∧
          (∀ i n, MapsTo (alpha n)
            (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source) ∧
          (∀ i n, EqOn (w i n).toFun
            (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
            (Icc (0 : Real) (partitionIntervalLength t i))) ∧
          (∀ i, Tendsto (w i) atTop (nhds (v i))) ∧
          TendstoUniformly
            (fun n (s : Icc (t 0) (t (Fin.last 2))) ↦ alpha n s.1)
            (fun s ↦ gamma s.1) atTop ∧
          Tendsto (fun n ↦ lRegularizedAction S T (alpha n) (t 0) (t (Fin.last 2)))
            atTop (nhds (lRegularizedAction S T gamma (t 0) (t (Fin.last 2)))) := by
  classical
  have hseg (i : Fin 2) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hlen (i : Fin 2) : 0 ≤ partitionIntervalLength t i :=
    sub_nonneg.mpr (hseg i)
  let pr (i : Fin 2) (s : Real) : Real :=
    ((Set.projIcc (0 : Real) (partitionIntervalLength t i) (hlen i) s :
      Icc (0 : Real) (partitionIntervalLength t i)) : Real)
  have hpr_mem (i : Fin 2) (s : Real) :
      pr i s ∈ Icc (0 : Real) (partitionIntervalLength t i) :=
    (Set.projIcc (0 : Real) (partitionIntervalLength t i) (hlen i) s).2
  have hpr_cont (i : Fin 2) : Continuous (pr i) :=
    continuous_subtype_val.comp continuous_projIcc
  have hpr_shift (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      pr i (s - t i.castSucc) = s - t i.castSucc := by
    simp only [pr]
    exact congrArg Subtype.val (Set.projIcc_of_mem (hlen i) ⟨
      sub_nonneg.mpr hs.1, by
        simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩)
  let lift (i : Fin 2) (s : Real) : M :=
    (extChartAt I (p i)).symm ((v i).toFun (pr i (s - t i.castSucc)))
  have hlift_cont (i : Fin 2) : Continuous (lift i) := by
    rw [← continuousOn_univ]
    exact (continuousOn_extChartAt_symm (I := I) (p i)).comp
      ((v i).continuousOn_toFun.comp_continuous
        ((hpr_cont i).comp (continuous_id.sub continuous_const))
        (fun s ↦ hpr_mem i (s - t i.castSucc))).continuousOn
      (fun s _ ↦ htar i (hpr_mem i (s - t i.castSucc)))
  have hlift_coord (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      extChartAt I (p i) (lift i s) = (v i).toFun (s - t i.castSucc) := by
    simp only [lift]
    rw [hpr_shift i hs]
    exact (extChartAt I (p i)).right_inv (htar i ⟨
      sub_nonneg.mpr hs.1, by
        simpa only [partitionIntervalLength] using sub_le_sub_right hs.2 (t i.castSucc)⟩)
  have hleft_node : lift 0 (t 1) =
      (extChartAt I (p 0)).symm ((v 0).toFun (partitionIntervalLength t 0)) := by
    simp only [lift]
    rw [hpr_shift 0 (by
      constructor
      · simpa using hseg 0
      · simp)]
    congr 2
  have hright_node : lift 1 (t 1) =
      (extChartAt I (p 1)).symm ((v 1).toFun 0) := by
    simp only [lift]
    rw [hpr_shift 1 (by
      constructor
      · simp
      · simpa using hseg 1)]
    congr 2
    rw [show (1 : Fin 2).castSucc = (1 : Fin 3) by rfl, sub_self]
  have hlifts_node : lift 0 (t 1) = lift 1 (t 1) :=
    hleft_node.trans (hnode.trans hright_node.symm)
  let gamma : Real → M := Set.piecewise (Iic (t 1)) (lift 0) (lift 1)
  have hgamma : Continuous gamma := by
    apply (hlift_cont 0).piecewise (s := Iic (t 1))
    · intro s hs
      have hst : s = t 1 := by
        simpa only [frontier_Iic, mem_singleton_iff] using hs
      simpa only [hst] using hlifts_node
    · exact hlift_cont 1
  have hgamma_piece (i : Fin 2) {s : Real}
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) : gamma s = lift i s := by
    fin_cases i
    · exact (Iic (t 1)).piecewise_eq_of_mem _ _ (by simpa using hs.2)
    · by_cases hst : s = t 1
      · subst s
        simp only [gamma]
        rw [(Iic (t 1)).piecewise_eq_of_mem _ _ (mem_Iic.mpr le_rfl)]
        exact hlifts_node
      · exact (Iic (t 1)).piecewise_eq_of_notMem _ _ (by
          rw [mem_Iic]
          intro hle
          have hge : t 1 ≤ s := by simpa using hs.1
          exact hst (le_antisymm hle hge))
  have hsrc (i : Fin 2) : MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    intro s hs
    rw [hgamma_piece i hs]
    simpa only [lift, extChartAt_source] using
      (extChartAt I (p i)).map_target
        (htar i (hpr_mem i (s - t i.castSucc)))
  have hrep (i : Fin 2) : EqOn (v i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hs : t i.castSucc + r ∈ Icc (t i.castSucc) (t i.succ) := by
      constructor
      · linarith [hr.1]
      · have hr' := hr.2
        simp only [partitionIntervalLength] at hr'
        linarith
    change (v i).toFun r =
      extChartAt I (p i) (gamma (t i.castSucc + r))
    rw [hgamma_piece i hs, hlift_coord i hs]
    congr 2
    ring
  have hgamma_left : gamma (t 0) =
      (extChartAt I (p 0)).symm ((v 0).toFun 0) := by
    rw [hgamma_piece 0 (by
      constructor
      · simp
      · simpa using hseg 0)]
    simp only [lift]
    rw [hpr_shift 0 (by
      constructor
      · simp
      · simpa using hseg 0)]
    congr 2
    rw [show (0 : Fin 2).castSucc = (0 : Fin 3) by rfl, sub_self]
  have hgamma_right : gamma (t (Fin.last 2)) =
      (extChartAt I (p 1)).symm ((v 1).toFun (partitionIntervalLength t 1)) := by
    rw [hgamma_piece 1 (by
      constructor
      · simpa using hseg 1
      · simp)]
    simp only [lift]
    rw [hpr_shift 1 (by
      constructor
      · simpa using hseg 1
      · simp)]
    congr 2
  obtain ⟨alpha, w, halpha, halpha0, halphaL, hsrcA, hrepA, hw,
      huniform, hact⟩ :=
    lAction_c1_dense_of_carrier S hMet hSc T (t 0) (t (Fin.last 2)) t htmono rfl rfl
      p gamma v hsrc hrep hreg
  exact ⟨gamma, hgamma, hsrc, hrep, hgamma_left, hgamma_right, alpha, w,
    halpha, halpha0, halphaL, hsrcA, hrepA, hw, huniform, hact⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
