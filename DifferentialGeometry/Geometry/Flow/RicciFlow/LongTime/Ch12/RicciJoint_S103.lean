import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.StageContinuity_S85
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab
import DifferentialGeometry.Geometry.Metric.Family.QuadraticBounds

set_option autoImplicit false

/-!
# CH12-S103 / G1: joint continuity of `(r, z, V) ↦ Ric_{g_r}(V,V)` and `g_r(V,V)` on a stage

`slab_ricci_inner_jointCont_S103` : for a solution `S` on a time interval `D` with `IsSolutionOn S` and a
sub-time-set `J ⊆ D.carrier`, the maps `(r, ξ) ↦ Ric_{g_r}(ξ,ξ)` and `(r, ξ) ↦ g_r(ξ,ξ)` are continuous on
`J × TangentBundle` (from `ricciCont` / `smoothMetric`, via `tensor0SFamily_quadCont`).
`ricci_jointly_continuous_S103` : the same for the stage metrics `K.stageMetric j` of an observed history,
for `J ⊆ stageDomain j` with `J < horizon` (the constant final stage with `horizon ≤ time last` has no
such `J ≠ ∅`).
-/

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.Geometry.Riemannian GC.LongTime
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

theorem slab_ricci_inner_jointCont_S103 {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    {S : DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := ThreeModel) (M := P.Carrier) D}
    (hS : DifferentialGeometry.PDE.RicciFlow.IsSolutionOn S) {J : Set ℝ} (hJ : J ⊆ D.carrier) :
    Continuous (fun q : {r : ℝ // r ∈ J} × TangentBundle ThreeModel P.Carrier =>
      ricciTensor (S.base.metric q.1.1) q.2.proj q.2.2 q.2.2) ∧
    Continuous (fun q : {r : ℝ // r ∈ J} × TangentBundle ThreeModel P.Carrier =>
      (S.base.metric q.1.1).inner q.2.proj q.2.2 q.2.2) := by
  refine ⟨?_, ?_⟩
  · have hric := tensor0SFamilyContinuousOnSet.mono (I := ThreeModel) (M := P.Carrier) hS.ricciCont hJ
    have h := tensor0SFamily_quadCont (I := ThreeModel) (M := P.Carrier) hric
    refine h.congr (fun q => ?_)
    have hv : (fun _ : Fin 2 => q.2.2) = vec2 q.2.2 q.2.2 := by
      funext i
      simp [vec2]
    have h1 : quad02 (I := ThreeModel) (M := P.Carrier) (S.ricci q.1.1 q.2.proj) q.2.2 =
        S.ricciAt q.1.1 q.2.proj (vec2 q.2.2 q.2.2) := by
      unfold quad02
      rw [hv]
      rfl
    rw [h1]
    exact (metricRicciAt_apply_eq_ricciTensor (S.base.metric q.1.1) q.2.proj q.2.2 q.2.2)
  · exact metricTimeBundleQuad_cont_of_metricFamilySmoothOn (I := ThreeModel) (M := P.Carrier)
      (D := D) (K := J) _ hS.smoothMetric hJ

/-- **G1** (joint continuity on a stage).  For `J ⊆ stageDomain j` with `J < horizon`,
`(r, ξ) ↦ Ric_{g_r}(ξ, ξ)` and `(r, ξ) ↦ g_r(ξ, ξ)` are continuous on `J × TangentBundle`. -/
theorem ricci_jointly_continuous_S103 (K : ObservedHistory.{u}) (j : Fin (K.eventCount + 1))
    {J : Set ℝ} (hJ : J ⊆ K.stageDomain j) (hlt : ∀ r ∈ J, r < K.horizon) :
    Continuous (fun q : {r : ℝ // r ∈ J} × TangentBundle ThreeModel (K.stage j).Carrier =>
      ricciTensor (K.stageMetric j q.1.1) q.2.proj q.2.2 q.2.2) ∧
    Continuous (fun q : {r : ℝ // r ∈ J} × TangentBundle ThreeModel (K.stage j).Carrier =>
      (K.stageMetric j q.1.1).inner q.2.proj q.2.2 q.2.2) := by
  cases j using Fin.lastCases with
  | last =>
    have hdom : K.stageDomain (Fin.last K.eventCount) =
        Icc (K.time (Fin.last K.eventCount)) K.horizon := by
      ext τ
      exact ObservedHistory.mem_stageDomain_last K τ
    by_cases h : K.time (Fin.last K.eventCount) < K.horizon
    · have hm : ∀ τ, K.stageMetric (Fin.last K.eventCount) τ = (K.finalSlab h).flow.base.metric τ :=
        fun τ => ObservedHistory.stageMetric_last_of_lt (H := K) (h := h) τ
      simp only [hm]
      exact slab_ricci_inner_jointCont_S103 (K.finalSlab h).equation (J := J)
        (fun r hr => by rw [hdom] at hJ; exact hJ hr)
    · have hempty : ∀ r : ℝ, r ∉ J := by
        intro r hr
        have h1 := hJ hr
        rw [hdom] at h1
        exact h (lt_of_le_of_lt h1.1 (hlt r hr))
      have hc : ∀ f : {r : ℝ // r ∈ J} × TangentBundle ThreeModel
          (K.stage (Fin.last K.eventCount)).Carrier → ℝ, Continuous f := fun f =>
        continuous_iff_continuousAt.mpr (fun q => absurd q.1.2 (hempty q.1.1))
      exact ⟨hc _, hc _⟩
  | cast i =>
    have hdom : K.stageDomain i.castSucc = Ico (K.time i.castSucc) (K.time i.succ) := by
      rw [ObservedHistory.stageDomain, Fin.lastCases_castSucc]
    simp only [ObservedHistory.stageMetric_castSucc_apply]
    exact slab_ricci_inner_jointCont_S103 (K.event i).incoming.equation (J := J)
      (fun r hr => by rw [hdom] at hJ; exact hJ hr)

end GC.LongTime.Ch12
