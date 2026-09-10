import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabLimitMetricEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabRicciTensorLimit
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceSwap

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

private theorem slabClosed_ricciCoeff_continuousOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    ContinuousOn (fun t => ricciTensor (I := I3) (g t) x v w) (Set.Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hev := (slabComparison_ricciTensor_cont L hle hk hcomp hab hsub).eval_continuous
    (P := ↥(Set.Icc a b)) (τ := fun q => (q : ℝ)) (b := fun _ => x)
    continuous_subtype_val (fun q => q.2) continuous_const
    (v := fun j _ => vec2 v w j) (fun _ => continuous_const)
  refine hev.congr (fun q => ?_)
  exact metricRicciAt_apply_eq_ricciTensor (I := I3) (g (q : ℝ)) x v w

theorem slabComparison_metric_hasDerivWithinAt
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a < b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    {t : ℝ} (ht : t ∈ Set.Icc a b)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I3) (g t) x v w) (Set.Icc a b) t := by
  have hf := slabComparison_metricCoeff_continuousOn L hle hcomp hab.le hsub x v w
  have hRic := slabClosed_ricciCoeff_continuousOn L hle hk hcomp hab.le hsub x v w
  apply Analysis.hasDerivIcc_of_int hab hf (continuousOn_const.mul hRic) _ ht
  intro s hs
  have ha := (hsub (Set.left_mem_Icc.mpr hab.le)).1
  have hb := (hsub (Set.right_mem_Icc.mpr hab.le)).2
  exact slabComparison_metric_hasDerivAt L hle hk hcomp
    ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩ x v w

theorem IsSlabLimit.metric_hasDerivWithinAt
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hlim : IsSlabLimit L delta hd g)
    {t : ℝ} (ht : t ∈ Set.Icc (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I3) (g t) x v w) (Set.Icc (-delta) 0) t := by
  obtain ⟨_, k, hk, hconv⟩ := hlim
  have hcomp : SlabComparison L delta k g := by
    intro K hK a b hab hsub order eps heps
    filter_upwards [hconv K hK a b hab hsub order eps heps] with i hi
    exact hi.2.2
  exact slabComparison_metric_hasDerivWithinAt L hle hk hcomp
    (by linarith) Set.Subset.rfl ht x v w

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
