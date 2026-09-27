import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.IntegratedHarnackCalculus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Curvature.Metric.LeviCivita

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff _root_.Topology Interval

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M] [BoundarylessManifold I M]
  {D : RealTimeInterval}

def smoothCurveRicciEnergy (S : SolutionOn (I := I) (M := M) D)
    (gamma : ℝ → M) (q : ℝ × ℝ) : ℝ :=
  ricciTensor (I := I) (S.base.metric q.1) (gamma q.2)
    (mfderiv 𝓘(ℝ, ℝ) I gamma q.2 (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I gamma q.2 (1 : ℝ))

theorem smoothCurveRicciEnergy_continuousOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma) :
    ContinuousOn (smoothCurveRicciEnergy S gamma) (D.carrier ×ˢ (univ : Set ℝ)) := by
  classical
  let K : Set (ℝ × ℝ) := D.carrier ×ˢ (univ : Set ℝ)
  let v : (u : ℝ) → TangentSpace I (gamma u) :=
    fun u => mfderiv 𝓘(ℝ, ℝ) I gamma u (1 : ℝ)
  have hv : Continuous (fun u : ℝ =>
      TotalSpace.mk' E (E := fun y : M => TangentSpace I y) (gamma u) (v u)) := by
    have h := MFDerivAlongCurve.continuous_tangentMap_unitLift
      (I := I) (M := M) (γ := gamma) (by norm_num) hgamma
    simpa only [v, tangentMap] using h
  rw [continuousOn_iff_continuous_domRestrict]
  have ht : Continuous (fun q : ↥K => (q : ℝ × ℝ).1) :=
    continuous_fst.comp continuous_subtype_val
  have hu : Continuous (fun q : ↥K => (q : ℝ × ℝ).2) :=
    continuous_snd.comp continuous_subtype_val
  have hx : Continuous (fun q : ↥K => gamma (q : ℝ × ℝ).2) :=
    hgamma.continuous.comp hu
  have heval := hS.ricciCont.eval_continuous
    (P := ↥K) (τ := fun q => (q : ℝ × ℝ).1)
    (b := fun q => gamma (q : ℝ × ℝ).2)
    ht (fun q => q.2.1) hx (v := fun _i q => v (q : ℝ × ℝ).2)
    (fun _i => hv.comp hu)
  have hRicAt : Continuous (fun q : ↥K =>
      S.ricciAt (q : ℝ × ℝ).1 (gamma (q : ℝ × ℝ).2)
        (vec2 (I := I) (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2))) := by
    refine heval.congr (fun q => ?_)
    simp only [SolutionOn.ricci, SolutionFamily.ricci_apply, SolutionFamily.ricciAt]
    change metricRicciAt (I := I) (S.base.metric (q : ℝ × ℝ).1)
        (gamma (q : ℝ × ℝ).2) (fun _i : Fin 2 => v (q : ℝ × ℝ).2) =
      metricRicciAt (I := I) (S.base.metric (q : ℝ × ℝ).1)
        (gamma (q : ℝ × ℝ).2)
        (vec2 (I := I) (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2))
    congr 1
    funext i
    fin_cases i <;> rfl
  refine hRicAt.congr (fun q => ?_)
  exact (metricRicciAt_apply_eq_ricciTensor (I := I)
    (S.base.metric (q : ℝ × ℝ).1) (gamma (q : ℝ × ℝ).2)
    (v (q : ℝ × ℝ).2) (v (q : ℝ × ℝ).2))

theorem smoothCurveRicciEnergy_short_intervalIntegrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {tau h : ℝ} (hh : 0 ≤ h) (hslab : Icc (tau - h) tau ⊆ D.carrier) :
    IntervalIntegrable (fun s => smoothCurveRicciEnergy S gamma (s, s - (tau - h)))
      volume (tau - h) tau := by
  have hmap : Continuous (fun s : ℝ => (s, s - (tau - h))) :=
    continuous_id.prodMk (continuous_id.sub continuous_const)
  have hc : ContinuousOn
      (fun s => smoothCurveRicciEnergy S gamma (s, s - (tau - h)))
      (Icc (tau - h) tau) :=
    (smoothCurveRicciEnergy_continuousOn S hS gamma hgamma).comp hmap.continuousOn
      (fun s hs => ⟨hslab hs, mem_univ _⟩)
  exact ContinuousOn.intervalIntegrable_of_Icc (sub_le_self _ hh) hc

theorem smoothCurveRicciEnergy_short_average_tendsto
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (gamma : ℝ → M) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I 1 gamma)
    {tau : ℝ} (hcarrier : Iic tau ⊆ D.carrier) :
    Tendsto (fun h => (∫ s in tau - h..tau,
      smoothCurveRicciEnergy S gamma (s, s - (tau - h))) / h)
      (𝓝[>] (0 : ℝ)) (𝓝 (smoothCurveRicciEnergy S gamma (tau, 0))) := by
  apply short_diagonal_average_tendsto
  · have hc := smoothCurveRicciEnergy_continuousOn S hS gamma hgamma
      (tau, 0) ⟨hcarrier (le_rfl : tau ≤ tau), mem_univ _⟩
    exact hc.mono (fun q hq => ⟨hcarrier hq.1, mem_univ _⟩)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    exact smoothCurveRicciEnergy_short_intervalIntegrable S hS gamma hgamma hh.le
      (fun s hs => hcarrier hs.2)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
