import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Maps
import Mathlib.Topology.Connected.Clopen
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section PartialDiffeomorph

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H N]
variable {n : WithTop ℕ∞}

theorem partialDiffeomorph_target_eq_univ_of_compact_source
    [T2Space N] [PreconnectedSpace N]
    (e : PartialDiffeomorph I I M N n)
    (hcompact : IsCompact e.source) (hne : e.source.Nonempty) :
    e.target = Set.univ := by
  have himage : (e : M → N) '' e.source = e.target :=
    e.toPartialEquiv.image_source_eq_target
  have htargetCompact : IsCompact e.target := by
    rw [← himage]
    exact hcompact.image_of_continuousOn e.contMDiffOn_toFun.continuousOn
  have htargetNonempty : e.target.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, e.map_source' hx⟩
  exact IsClopen.eq_univ ⟨htargetCompact.isClosed, e.open_target⟩ htargetNonempty

def globalDiffeomorphOfUniv (e : PartialDiffeomorph I I M N n)
    (hsource : e.source = Set.univ) (htarget : e.target = Set.univ) :
    Diffeomorph I I M N n where
  toFun := e
  invFun := e.symm
  left_inv x := e.left_inv' (by rw [hsource]; exact Set.mem_univ x)
  right_inv y := e.right_inv' (by rw [htarget]; exact Set.mem_univ y)
  contMDiff_toFun := by
    change ContMDiff I I n (e : M → N)
    apply contMDiffOn_univ.mp
    simpa only [hsource] using e.contMDiffOn_toFun
  contMDiff_invFun := by
    change ContMDiff I I n (e.symm : N → M)
    apply contMDiffOn_univ.mp
    have hinverse : ContMDiffOn I I n (e.symm : N → M) e.target :=
      e.symm.contMDiffOn_toFun
    simpa only [htarget] using hinverse

end PartialDiffeomorph

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : Nat → Nat}

theorem compactLimit_eventually_source_eq_univ
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → Φ.source k = Set.univ := by
  let : TopologicalSpace L.M := L.topology
  let : CompactSpace L.M := hcompact
  obtain ⟨k0, hk0⟩ := Φ.source_subset (K := Set.univ) isCompact_univ
  refine ⟨k0, ?_⟩
  intro k hk
  exact Set.eq_univ_of_univ_subset (hk0 k hk)

theorem compactLimit_eventually_globalizes
    (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)
    (hcompact :
      let : TopologicalSpace L.M := L.topology
      CompactSpace L.M)
    (hconnected : ∀ k : Nat,
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      ConnectedSpace (X.obj (subseq k)).M) :
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k →
      let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
      let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
      Φ.source k = Set.univ ∧ Φ.target k = Set.univ ∧
        ∃ e : Diffeomorph I I L.M (X.obj (subseq k)).M (∞ : WithTop ℕ∞),
          (∀ x, e x = Φ.map k x) ∧
          (∀ y, e.symm y = (Φ.partialDiffeomorph k).symm y) ∧
          e L.basepoint = (X.obj (subseq k)).basepoint ∧
          CompactSpace (X.obj (subseq k)).M := by
  obtain ⟨k0, hk0⟩ := compactLimit_eventually_source_eq_univ Φ hcompact
  refine ⟨k0, ?_⟩
  intro k hk
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
  let : ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
  let : T2Space (X.obj (subseq k)).M := (X.obj (subseq k)).t2
  let : CompactSpace L.M := hcompact
  let : ConnectedSpace (X.obj (subseq k)).M := hconnected k
  have hsource : (Φ.partialDiffeomorph k).source = Set.univ := hk0 k hk
  have hsourceCompact : IsCompact (Φ.partialDiffeomorph k).source := by
    rw [hsource]
    exact isCompact_univ
  have htarget : (Φ.partialDiffeomorph k).target = Set.univ :=
    partialDiffeomorph_target_eq_univ_of_compact_source (Φ.partialDiffeomorph k)
      hsourceCompact ⟨L.basepoint, Φ.base_mem k⟩
  let e := globalDiffeomorphOfUniv (Φ.partialDiffeomorph k) hsource htarget
  refine ⟨hsource, htarget, e, ?_, ?_, ?_, e.toHomeomorph.compactSpace⟩
  · intro x
    rfl
  · intro y
    rfl
  · exact Φ.basepoint_map k

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section
namespace DifferentialGeometry.CheegerGromovCompactness
open Filter Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff Topology
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [NeZero (Module.finrank ℝ E)]
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianConvergenceMaps.noncompact_of_escaping_points
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {P : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X P f) (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hconnected : ∀ i, ConnectedSpace (X.obj (f i)).M)
    (x : ∀ i, (X.obj (f i)).M)
    (hescape : Tendsto (fun i =>
      (riemannianEDistOf (X.obj (f i)).metric (X.obj (f i)).basepoint (x i)).toReal)
      atTop atTop) : NoncompactSpace P.M := by
  constructor
  intro hc
  let : CompactSpace P.M := ⟨hc⟩
  obtain ⟨N, hN⟩ := compactLimit_eventually_globalizes F ‹CompactSpace P.M› hconnected
  obtain ⟨_, _, e, _, _, _, _⟩ := hN N le_rfl
  let : ConnectedSpace (X.obj (f N)).M := hconnected N
  let : ConnectedSpace P.M := e.symm.surjective.connectedSpace e.symm.continuous
  obtain ⟨R, hR, hmaps⟩ := F.exists_eventually_image_compact_subset_ball C href
    (RiemannianMetricComplete.of_compact P.metric).complete (K := univ) hc
  obtain ⟨i, hi, hiN, hiR⟩ := (hmaps.and ((eventually_ge_atTop N).and
    (hescape.eventually_gt_atTop R))).exists
  obtain ⟨_, _, ei, hei, _, _, _⟩ := hN i hiN
  obtain ⟨z, hz⟩ := ei.surjective (x i)
  have hx : x i ∈ F.map i '' (univ : Set P.M) :=
    ⟨z, mem_univ z, (hei z).symm.trans hz⟩
  exact (not_le.mpr hiR) (ENNReal.toReal_le_of_le_ofReal hR.le (hi.2 hx))

end DifferentialGeometry.CheegerGromovCompactness
