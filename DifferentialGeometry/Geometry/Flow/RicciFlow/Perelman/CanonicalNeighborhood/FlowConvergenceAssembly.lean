import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension.Defs

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem convergesOn_of_eventually_metricComparisonOn {X : FlowSequence.{u}}
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (I := I3) (X.atTime 0) P f)
    {D : RealTimeInterval} (S : SolutionOn (I := I3) (M := P.M) D)
    (hwindow : ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ D.carrier →
      ∀ᶠ i in Filter.atTop, Set.Icc a b ⊆ (X.interval (f i)).carrier)
    (hcomparison : ∀ K : Set P.M, IsCompact K → ∀ a b : ℝ, a ≤ b →
      Set.Icc a b ⊆ D.carrier → ∀ order : ℕ, ∀ eps : ℝ, 0 < eps →
        ∀ᶠ i in Filter.atTop,
          Nonempty (MetricComparisonOn (fun s => S.base.metric s)
            (fun s => (X.term (f i)).S.base.metric s) (F.partialDiffeomorph i)
            K (Set.Icc a b) order eps)) :
    ConvergesOn F S := by
  intro K hK a b hab hsub order eps heps
  obtain ⟨k₀, hk₀⟩ := F.source_subset hK
  filter_upwards [hwindow a b hab hsub,
    hcomparison K hK a b hab hsub order eps heps,
    Filter.eventually_ge_atTop k₀] with i hw hc hi
  exact ⟨hw, hk₀ i hi, hc⟩

theorem eventually_window_of_depth_tendsto {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi}
    {sigma' : ℕ → ℕ} (hσ : Filter.Tendsto (fun i => X.depth (sigma' i))
      Filter.atTop Filter.atTop) :
    ∀ a b : ℝ, a ≤ b → Set.Icc a b ⊆ ancientTimeInterval.carrier →
      ∀ᶠ i in Filter.atTop, Set.Icc a b ⊆ (X.interval (sigma' i)).carrier := by
  intro a b hab hsub
  have hb : b ≤ 0 := by
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using
      hsub (Set.right_mem_Icc.mpr hab)
  filter_upwards [hσ.eventually (Filter.eventually_ge_atTop (|a| + 1))] with i hi
  rw [X.carrier_eq (sigma' i)]
  intro s hs
  exact ⟨by nlinarith [neg_le_abs a, hi, X.depth_pos (sigma' i), hs.1], hs.2.trans hb⟩

theorem isHalfLineExtension_of_eventually_metricComparisonOn
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M} {diagonal : ℕ → ℕ}
    (hdiag : StrictMono diagonal)
    (hg0 : g 0 = L.space.metric)
    (hagree : ∀ s ∈ J.carrier, g s = B.solution.base.metric s)
    (hcomparison : ∀ K : Set L.space.M, IsCompact K → ∀ a b : ℝ, a ≤ b → b ≤ 0 →
      ∀ order : ℕ, ∀ eps : ℝ, 0 < eps → ∀ᶠ i in Filter.atTop,
        Nonempty (MetricComparisonOn (fun s => g s)
          (fun s => (X.term (L.subseq (B.subseq (diagonal i)))).S.base.metric s)
          (L.maps.partialDiffeomorph (B.subseq (diagonal i)))
          K (Set.Icc a b) order eps)) :
    IsHalfLineExtension B g := by
  have hσ : Filter.Tendsto (fun i => X.depth (L.subseq (B.subseq (diagonal i))))
      Filter.atTop Filter.atTop :=
    X.depth_tendsto.comp (L.strictMono.tendsto_atTop.comp
      (B.strictMono.tendsto_atTop.comp hdiag.tendsto_atTop))
  refine ⟨hg0, hagree, diagonal, hdiag, ?_⟩
  refine convergesOn_of_eventually_metricComparisonOn (X := X.toFlowSequence) (P := L.space)
    (F := subsequenceMaps L.maps (B.subseq ∘ diagonal) (B.strictMono.comp hdiag))
    (S := ({ base := { metric := g } } :
      SolutionOn (I := I3) (M := L.space.M) ancientTimeInterval))
    (eventually_window_of_depth_tendsto hσ) ?_
  intro K hK a b hab hsub order eps heps
  filter_upwards [hcomparison K hK a b hab (by
    simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using
      hsub (Set.right_mem_Icc.mpr hab)) order eps heps] with i hi
  simpa only [subsequenceMaps, Function.comp_apply] using hi

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
