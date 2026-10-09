import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

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
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

namespace NormalizedSequence

variable {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}

def reindex (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) : NormalizedSequence.{u} eps kappa sigma Phi where
  interval i := X.interval (k i)
  term i := X.term (k i)
  depth i := X.depth (k i)
  scale i := X.scale (k i)
  depth_pos i := X.depth_pos (k i)
  depth_buffer i := X.depth_buffer (k i)
  scale_pos i := X.scale_pos (k i)
  depth_tendsto := X.depth_tendsto.comp hk.tendsto_atTop
  scale_tendsto := X.scale_tendsto.comp hk.tendsto_atTop
  carrier_eq i := X.carrier_eq (k i)
  regular_eq i := X.regular_eq (k i)
  connected i := X.connected (k i)
  orientation i := X.orientation (k i)
  complete i t ht := X.complete (k i) t ht
  source_bound i := X.source_bound (k i)
  base_one i := X.base_one (k i)
  noncollapse i := X.noncollapse (k i)
  pinching i := X.pinching (k i)
  higher_good i t ht x h := X.higher_good (k i) t ht x h

@[simp] theorem reindex_term (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).term i = X.term (k i) := rfl

@[simp] theorem reindex_interval (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).interval i = X.interval (k i) := rfl

@[simp] theorem reindex_depth (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).depth i = X.depth (k i) := rfl

@[simp] theorem reindex_scale (X : NormalizedSequence.{u} eps kappa sigma Phi) (k : ℕ → ℕ)
    (hk : StrictMono k) (i : ℕ) : (X.reindex k hk).scale i = X.scale (k i) := rfl

theorem reindex_id (X : NormalizedSequence.{u} eps kappa sigma Phi) :
    X.reindex id strictMono_id = X := rfl

end NormalizedSequence

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
