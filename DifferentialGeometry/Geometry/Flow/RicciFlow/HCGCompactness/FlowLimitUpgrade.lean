import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.RicciFlowConvergence

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# P4 assembly: concrete smooth-flow-limit upgrade data

The MSM135 Theorem 3.10 backend is assembled from genuine frontier ingredients,
given the time-zero Cheeger--Gromov compactness conclusion
`mc : MetricCompactnessConclusion (X.atZero)`:

* `L` — the limit Ricci flow (Brick A: limit-is-a-solution);
* `hL0` — the limit flow's time-zero pointed manifold is `mc.limit`;
* `maps` — the spacetime comparison maps (Brick B, from `mc.maps`);
* `scalar` — scalar-curvature pullback convergence (Brick E);
* `ricciNorm` — intrinsic squared Ricci-norm pullback convergence;
* `conv` — the window-uniform `C^p` convergence of the pulled-back metrics
  (Brick D: the norm bridge, consuming the moving-Shi bound `hShi`).

These are bundled in `FlowLimitData`; `flowLimit_upgrade` assembles them through
the already-built `SmoothCGHConverges.ofRestrictPullback`.  `FlowUpgradeData`
also records the further subsequence selected by the spacetime
Arzela--Ascoli argument.  The hard frontiers (A, D, E) remain honest input
fields here; no field accepts the desired compactness conclusion itself.  The
concrete convergence producer must prove both curvature pullback fields; this
layer only retains its outputs.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

/-- **Brick B: the spacetime comparison maps from the time-zero maps.**  The
Cheeger--Gromov comparison maps are time-INDEPENDENT diffeomorphisms of the
underlying manifolds, and `PointedFlowData.atTime` preserves `M`/topology/
charted/basepoint definitionally, so the time-zero `PointedRiemannianCGMaps`
(over the time-zero slice `L.atTime 0` of the limit flow) transport
field-for-field to the spacetime `PointedCGHMaps` over `L`. -/
def pointedCGHMaps_of_atZero
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianCGMaps (I := I) (X.atZero (I := I))
      (L.atTime (I := I) 0) subseq) :
    PointedCGHMaps (I := I) X (L.atTime 0) subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map

/-- The comparison maps over an ARBITRARY pointed Riemannian manifold `P`, the
field-copy of a `PointedRiemannianCGMaps` (metric-independent).  This is the
generic form the `mc.limit`-side endgame instantiation uses (the AA machinery is
re-indexed by `P`); `pointedCGHMaps_of_atZero` is the special case `P := L.atTime 0`. -/
def pointedCGHMaps_of_manifold
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (subseq : Nat -> Nat)
    (rmaps : PointedRiemannianCGMaps (I := I) (X.atZero (I := I)) P subseq) :
    PointedCGHMaps (I := I) X P subseq where
  partialDiffeomorph := rmaps.partialDiffeomorph
  source_exhausts := rmaps.source_exhausts
  base_mem := rmaps.base_mem
  basepoint_map := rmaps.basepoint_map

/-- **The Brick-A → Brick-B handoff: spacetime maps from the time-zero
conclusion.**  Once the limit flow `L` (Brick A) is built so that its time-zero
slice is the Cheeger--Gromov limit (`hL0 : L.atTime 0 = mc.limit`), the time-zero
comparison maps `mc.maps` transport along that equality to
`PointedRiemannianCGMaps (X.atZero) (L.atTime 0) mc.subseq`, which Brick B carries
to the spacetime `PointedCGHMaps`.  This is the producer of the `FlowLimitData`
`maps` field: with it, `FlowLimitData`'s own constructor (plus this `maps`) and
`flowLimit_upgrade` assemble `CompactnessConclusion X` from `L`, `hL0`, and the
honest frontier fields. -/
def cghMaps_of_hL0
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData.{u, uE, uH} (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit) :
    PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq :=
  pointedCGHMaps_of_atZero (I := I) X L mc.subseq (hL0.symm ▸ mc.maps)

/-- The structured frontier ingredients of the smooth-flow-limit upgrade, given
the time-zero metric Cheeger--Gromov compactness conclusion `mc`.  Each field is
one P4 brick; the hard frontiers (the limit flow `L`, the window convergence
`conv`, and the curvature convergence fields) are honest inputs here. -/
structure FlowLimitData
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))) where
  /-- Brick A: the limit Ricci flow on the time-zero limit manifold. -/
  L : PointedFlowData.{u, uE, uH} (I := I) X.D
  /-- The limit flow is based on the pointed limit supplied by Theorem 3.9. -/
  hL0 : L.atTime (I := I) 0 = mc.limit
  /-- Brick B: the spacetime comparison maps. -/
  maps : PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq
  /-- Brick E: scalar-curvature pullback convergence. -/
  scalar : ScalarPullbackTendsto (I := I) maps
  /-- Intrinsic squared Ricci-norm pullback convergence, produced by the
  concrete smooth metric convergence construction. -/
  ricciNorm : RicNormPullback (I := I) maps
  /-- Source/target σ-compactness (Brick C inputs). -/
  hσsrc : forall k : Nat,
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    IsSigmaCompact (maps.source k)
  hσtgt : forall k : Nat,
    letI : TopologicalSpace (X.term (mc.subseq k)).M :=
      (X.term (mc.subseq k)).topology
    IsSigmaCompact (maps.target k)
  /-- The per-`k` reference metric on the source domain (Brick C input). -/
  refMetric : forall k : Nat,
    letI : TopologicalSpace (SourceDomain (I := I) maps k) := sourceDomTop (I := I) maps k
    letI : ChartedSpace H (SourceDomain (I := I) maps k) := sourceDomCharted (I := I) maps k
    letI : IsManifold I ∞ (SourceDomain (I := I) maps k) := sourceDomSmooth (I := I) maps k
    Real -> SmoothRiemannianMetric I (SourceDomain (I := I) maps k)
  /-- Brick D: window-uniform `C^p` convergence of the pulled-back metrics
  (the moving-Shi norm bridge output). -/
  conv : forall K : Set (L.atTime 0).M,
    forall _hK : letI : TopologicalSpace (L.atTime 0).M := L.topology; IsCompact K,
    forall p : Nat,
    forall a b : Real, Set.Icc a b ⊆ X.D.carrier ->
      forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k ->
          forall t : Real, t ∈ Set.Icc a b ->
            ((SourceDomainMetricData.ofRestrictPullback (I := I)
              (Φ := maps) (k := k) (hσsrc k) (hσtgt k)
              (refMetric k) (letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M := L.charted; letI : IsManifold I ∞ L.M := L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := (by change IsManifold I ∞ L.M; infer_instance); letI : SigmaCompactSpace L.M := L.sigmaCompact; letI : T2Space L.M := L.t2; L.S.family.metric)).derivNormSupOn (I := I) K p t) < ε

/-- **The smooth-flow-limit upgrade, assembled.**  From the structured frontier
ingredients (Brick A–E) the time-zero conclusion `mc` upgrades to full smooth
Cheeger--Gromov--Hamilton convergence of the flows, via the canonical
restrict/pullback assembly `SmoothCGHConverges.ofRestrictPullback`. -/
theorem flowLimit_upgrade
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (d : FlowLimitData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  ⟨d.L, mc.subseq, mc.strictMono,
    ⟨SmoothCGHConverges.ofRestrictPullback (I := I)
      d.maps d.scalar d.ricciNorm d.hσsrc d.hσtgt d.refMetric (letI : TopologicalSpace d.L.M := d.L.topology; letI : ChartedSpace H d.L.M := d.L.charted; letI : IsManifold I ∞ d.L.M := d.L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) d.L.M := (by change IsManifold I ∞ d.L.M; infer_instance); letI : SigmaCompactSpace d.L.M := d.L.sigmaCompact; letI : T2Space d.L.M := d.L.t2; d.L.S.family.metric) d.conv⟩⟩

/-- Concrete data for the Theorem 3.10 upgrade after the spacetime
Arzela--Ascoli argument selects a further strictly monotone subsequence.

Unlike the legacy `SmoothFlowLimitInput`, this record cannot be inhabited by
supplying the desired conclusion: it must expose the actual limit flow,
comparison maps, scalar and squared Ricci-norm convergence, and window-uniform
metric convergence in its `FlowLimitData` field. -/
structure FlowUpgradeData
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))) where
  /-- The further subsequence selected by spacetime Arzela--Ascoli. -/
  φ : Nat -> Nat
  /-- The further subsequence is strictly monotone. -/
  hφ : StrictMono φ
  /-- The concrete smooth-flow-limit data over the reindexed metric limit. -/
  data : FlowLimitData (I := I) X (mc.compSubseq φ hφ)

namespace FlowUpgradeData

/-- Assemble the smooth CGH compactness conclusion from concrete upgrade data. -/
theorem toConclusion
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I))}
    (d : FlowUpgradeData (I := I) X mc) :
    CompactnessConclusion (I := I) X :=
  flowLimit_upgrade (I := I) X (mc.compSubseq d.φ d.hφ) d.data

end FlowUpgradeData

end HCGCompactness
end DifferentialGeometry
