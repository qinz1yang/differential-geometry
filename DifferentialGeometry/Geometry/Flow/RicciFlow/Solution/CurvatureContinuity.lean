import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Family.TensorNorm

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D}

theorem IsSolutionOn.continuousOn_rmNormSq (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M =>
      normSq0S (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2))
      (D.carrier ×ˢ (univ : Set M)) := by
  have hc := continuous_normSq0S_family S.base.metric (fun t x => S.base.rm04 t x)
    hS.smoothMetric.metricTensor_cont hS.rm04Cont
  rw [continuousOn_iff_continuous_domRestrict]
  have hm : Continuous (fun p : D.carrier ×ˢ (univ : Set M) =>
      ((⟨p.1.1, p.2.1⟩ : D.carrier), p.1.2)) :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  apply (hc.comp hm).congr
  intro p
  rfl

theorem IsSolutionOn.continuousOn_riemannNorm (hS : IsSolutionOn S) :
    ContinuousOn (fun p : ℝ × M =>
      Real.sqrt (normSq0S (S.base.metric p.1) p.2 4 (S.base.rm04 p.1 p.2)))
      (D.carrier ×ˢ (univ : Set M)) :=
  hS.continuousOn_rmNormSq.sqrt

theorem IsSolutionOn.continuousOn_riemannNorm_time (hS : IsSolutionOn S) (x : M) :
    ContinuousOn (fun t : ℝ =>
      Real.sqrt (normSq0S (S.base.metric t) x 4 (S.base.rm04 t x))) D.carrier := by
  exact hS.continuousOn_riemannNorm.comp (f := fun t : ℝ => (t, x))
    (continuous_id.prodMk continuous_const).continuousOn (fun t ht => ⟨ht, mem_univ x⟩)

theorem IsSolutionOn.continuousOn_ricciAt {D : RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => S.ricciAt t x (vec2 v w)) D.carrier := by
  let K := D.carrier
  have hcont : Continuous (fun p : K =>
      (S.ricci p.1 x) (fun i : Fin 2 => if i = 0 then v else w)) := by
    have heval := tensor0SFamilyContinuousOnSet.eval_continuous hS.ricciCont
      (P := K) (τ := fun p : K => p.1) (b := fun _ : K => x)
      continuous_subtype_val (fun p => p.2) continuous_const
      (v := fun a : Fin 2 => fun _ : K => if a = 0 then v else w)
      (by
        intro a
        fin_cases a
        · simpa using (continuous_const : Continuous (fun _ : K =>
            (⟨x, v⟩ : TangentBundle I M)))
        · simpa using (continuous_const : Continuous (fun _ : K =>
            (⟨x, w⟩ : TangentBundle I M))))
    simpa [K, vec2] using heval
  rw [continuousOn_iff_continuous_domRestrict]
  exact hcont.congr fun _ => rfl

theorem IsSolutionOn.continuousOn_ricciTensor [BoundarylessManifold I M]
    {D : RealTimeInterval} {S : SolutionOn (I := I) (M := M) D} (hS : IsSolutionOn S)
    (x : M) (v w : TangentSpace I x) :
    ContinuousOn (fun t => ricciTensor (S.base.metric t) x v w) D.carrier := by
  exact (hS.continuousOn_ricciAt x v w).congr fun t _ =>
    (metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x v w).symm

end DifferentialGeometry.PDE.RicciFlow
