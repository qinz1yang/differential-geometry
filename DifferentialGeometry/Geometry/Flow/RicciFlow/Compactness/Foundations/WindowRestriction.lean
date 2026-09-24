import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff _root_.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def FlowSequence.timeRestrict (X : FlowSequence.{u}) (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) : PointedFlowSeq.{u, 0, 0} I3 where
  D := D
  term i := (X.term i).timeRestrict D (hcarrier i) (hregular i)

@[simp] theorem FlowSequence.timeRestrict_atTime (X : FlowSequence.{u}) (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (t : ℝ) :
    (X.timeRestrict D hcarrier hregular).atTime t = X.atTime t := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted

variable (X : FlowSequence.{u})

def reindex (k : ℕ → ℕ) : FlowSequence.{u} where
  interval i := X.interval (k i)
  term i := X.term (k i)

@[simp] theorem reindex_atTime (k : ℕ → ℕ) (t : ℝ) :
    (X.reindex k).atTime t = (X.atTime t).subseq k := rfl

@[simp] theorem timeRestrict_term_metric (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (i : ℕ) :
    ((X.timeRestrict D hcarrier hregular).term i).S.base.metric =
      (X.term i).S.base.metric := rfl

def singletonTime (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) : PointedFlowSeq I3 :=
  X.timeRestrict (RealTimeInterval.closed t t le_rfl)
    (fun i s hs => by
      have hst : s = t := le_antisymm hs.2 hs.1
      simpa only [hst] using ht i)
    (fun _ s hs => False.elim (lt_irrefl t (hs.1.trans hs.2)))

@[simp] theorem singletonTime_atTime (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier)
    (s : ℝ) : (X.singletonTime t ht).atTime s = X.atTime s := rfl

@[simp] theorem singletonTime_term_metric (t : ℝ)
    (ht : ∀ i, t ∈ (X.interval i).carrier) (i : ℕ) :
    ((X.singletonTime t ht).term i).S.base.metric = (X.term i).S.base.metric := rfl

variable {X}

def timeRestrictMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) :
    PointedCGHMaps (X.timeRestrict D hcarrier hregular) P f where
  partialDiffeomorph := F.partialDiffeomorph
  source_exhausts := F.source_exhausts
  base_mem := F.base_mem
  basepoint_map := F.basepoint_map

@[simp] theorem timeRestrictMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (D : RealTimeInterval)
    (hcarrier : ∀ i, D.carrier ⊆ (X.interval i).carrier)
    (hregular : ∀ i, D.regular ⊆ (X.interval i).regular) (i : ℕ) :
    (timeRestrictMaps F D hcarrier hregular).partialDiffeomorph i =
      F.partialDiffeomorph i := rfl

def singletonTimeMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) :
    PointedCGHMaps (X.singletonTime t ht) P f where
  partialDiffeomorph := F.partialDiffeomorph
  source_exhausts := F.source_exhausts
  base_mem := F.base_mem
  basepoint_map := F.basepoint_map

@[simp] theorem singletonTimeMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (t : ℝ) (ht : ∀ i, t ∈ (X.interval i).carrier) (i : ℕ) :
    (singletonTimeMaps F t ht).partialDiffeomorph i = F.partialDiffeomorph i := rfl

def reindexMaps {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (k : ℕ → ℕ) (hk : StrictMono k) :
    PointedRiemannianConvergenceMaps ((X.reindex (f ∘ k)).atTime 0) P id where
  partialDiffeomorph i := F.partialDiffeomorph (k i)
  source_exhausts := F.source_exhausts.comp_subseq hk
  base_mem i := F.base_mem (k i)
  basepoint_map i := F.basepoint_map (k i)

@[simp] theorem reindexMaps_partialDiffeomorph
    {P : PointedRiemannianManifold.{u, 0, 0} I3} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps (X.atTime 0) P f)
    (k : ℕ → ℕ) (hk : StrictMono k) (i : ℕ) :
    (reindexMaps F k hk).partialDiffeomorph i = F.partialDiffeomorph (k i) := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.FlowSequence

end

end
