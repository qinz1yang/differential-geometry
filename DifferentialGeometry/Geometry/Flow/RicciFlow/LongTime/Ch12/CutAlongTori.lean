import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongToriCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.LateCutGeometry
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.NoCuts

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.LongTime.CuspP1
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

/-- C2a input: a finite family of pairwise disjoint smooth two-sided collars `T² × (-1,1)` in a
3-manifold `N` (any 3-manifold; closedness is only used by the cutting theorem). No orientation
hypothesis: `N`'s orientation pulls back along a collar and the sign is absorbed by the torus
orientations of the `TorusGluing`. -/
structure CollaredTorusFamily_C2a (N : Type*) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] where
  count : ℕ
  collar : Fin count → PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) N ∞
  source_eq : ∀ i, (collar i).source = signedCollarSource
  disjoint : Pairwise fun i j => Disjoint (collar i).target (collar j).target

namespace CollaredTorusFamily_C2a

/-- Empty family (any `N`). -/
def empty (N : Type*) [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] :
    CollaredTorusFamily_C2a N where
  count := 0
  collar := fun i => i.elim0
  source_eq := fun i => i.elim0
  disjoint := fun i => i.elim0

/-- Non-empty inhabitant: the level-`S` tori of all cusps of a hyperbolic truncation. -/
def ofLevel {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) {S : ℝ}
    (hS : 2 ≤ S) : CollaredTorusFamily_C2a H.Carrier where
  count := T.count
  collar := levelSignedCollar_C2a T S
  source_eq := levelSignedCollar_source_C2a T hS
  disjoint := fun _ _ hij => levelSignedCollar_disjoint_C2a T hij

end CollaredTorusFamily_C2a

/-- **Empty case of `cutAlongTori_C2a`** (proved; degenerates to `NoCuts`). -/
theorem cutAlongTori_empty_C2a (M : ConnectedClosedOrientedManifold.{u} 3)
    (F : CollaredTorusFamily_C2a M.Carrier) (h0 : F.count = 0) :
    ∃ (D : GC.Topology.TorusDecomposition M) (e : Fin F.count ≃ Fin D.boundary.count),
      (∀ i (t : Torus), D.reconstructionAtlas.torusInPrime D.reconstruction (e i) t =
        F.collar i (t, 0)) ∧
      D.components.count = 1 :=
  ⟨NoCuts.torusDecomposition M,
    ⟨fun i => absurd i.2 (by omega), fun i => i.elim0, fun i => absurd i.2 (by omega),
      fun i => i.elim0⟩,
    fun i => absurd i.2 (by omega), rfl⟩

/-- **IF4 draft (`TruncatedCutData`).** Data of the cut of the slice at time `t` along the level-`S`
tori of the cusps of base truncations of the cores: the base truncations, the level, and the
depth-200 cusp buffer inside the persistent-core domain. Collars, disjointness and the target
tori are *derived* (`levelSignedCollar_C2a`, `CollaredTorusFamily_C2a.ofLevel`). -/
structure TruncatedCutData_IF4 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} (cores : GC.LongTime.PersistentHyperbolicCores F K)
    (t : ℝ) where
  base : ∀ i : Fin cores.count, HyperbolicTruncation (cores.model i)
  level : ℝ
  two_le : 2 ≤ level
  deep_domain : ∀ i (q : Fin (base i).count) (p : CuspHalfSpace), p.2.val 0 ≤ level + 200 →
    (base i).cuspMap q p ∈ (cores.domain i t : Set (cores.model i).Carrier)

namespace TruncatedCutData_IF4
variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : GC.LongTime.PersistentHyperbolicCores F K} {t : ℝ}

/-- The truncation `S_j` handed to `LateCutFamily.truncation`. -/
def truncation (D : TruncatedCutData_IF4 cores t) (i : Fin cores.count) :
    HyperbolicTruncation (cores.model i) :=
  truncationAtLevel_C1 (D.base i) D.two_le

/-- Degenerate inhabitant: all base truncations without cusps (closed models, and the empty
family `cores.count = 0`, are both covered). -/
def ofNoCusps (base : ∀ i : Fin cores.count, HyperbolicTruncation (cores.model i))
    (h0 : ∀ i, (base i).count = 0) : TruncatedCutData_IF4 cores t where
  base := base
  level := 2
  two_le := le_rfl
  deep_domain := fun i q => absurd q.2 (by have := h0 i; omega)

/-- Empty family of cores. -/
def ofEmpty (h : cores.count = 0) : TruncatedCutData_IF4 cores t :=
  ofNoCusps (fun i => absurd i.2 (by omega)) (fun i => absurd i.2 (by omega))

theorem truncation_count (D : TruncatedCutData_IF4 cores t) (i : Fin cores.count) :
    (D.truncation i).count = (D.base i).count := rfl

/-- The collar of the `q`-th level torus of core `i`, inside the model. -/
def collar (D : TruncatedCutData_IF4 cores t) (i : Fin cores.count) (q : Fin (D.base i).count) :=
  levelSignedCollar_C2a (D.base i) D.level q

theorem collar_target_subset_domain (D : TruncatedCutData_IF4 cores t) (i : Fin cores.count)
    (q : Fin (D.base i).count) :
    (D.collar i q).target ⊆ (cores.domain i t : Set (cores.model i).Carrier) := by
  intro y hy
  obtain ⟨p, hp, rfl⟩ := levelSignedCollar_height_C2a (D.base i) D.two_le q hy
  exact D.deep_domain i q p (by linarith)

/-- Nonempty-torus family inside one model (all cusps of one core). -/
def modelFamily (D : TruncatedCutData_IF4 cores t) (i : Fin cores.count) :
    CollaredTorusFamily_C2a (cores.model i).Carrier :=
  CollaredTorusFamily_C2a.ofLevel (D.base i) D.two_le

end TruncatedCutData_IF4

end GC.LongTime.Ch12
