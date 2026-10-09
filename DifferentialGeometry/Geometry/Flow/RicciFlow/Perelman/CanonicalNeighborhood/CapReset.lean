import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapSlabCapture
import DifferentialGeometry.Topology.OpenPartialHomeomorph.GraphOrientation
import DifferentialGeometry.Topology.GraphBand
import DifferentialGeometry.Geometry.Neck.QuarterBandPacking
import Mathlib.Data.Nat.Nth
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCapConnectedInterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapCollar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapTruncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc t : ℝ} {p : M} {U W : Set M}

theorem SpatialNeck.quarter_band_subset_cap_core_sdiff_of_outward_graph
    (nk : SpatialNeck (S.base.metric t) eps p) (heps : eps ≤ 1 / 8646)
    (cap : LocalCap S epsc p t U)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p z)
    (f : Sphere 2 → ℝ) (hf : Continuous f) (hsmall : ∀ q, |f q| < 1 / 10)
    (hzero : f nk.center = 0) (hW : IsClosed W)
    (hfront : frontier W = range (fun q : Sphere 2 => nk.map (q, f q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → nk.map (nk.center, a) ∉ W) :
    nk.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ interior cap.core.carrier \ W := by
  have hcap := nk.image_slab_subset_cap_core_of_center_in_slab heps nk.center
    (by norm_num : |(0 : ℝ)| ≤ 4) nk.center_eq cap hdepth
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (by linarith [nk.eps_small])
  let A := nk.map '' {z : Cylinder | f z.1 < z.2 ∧ z.2 < 1}
  have hsrc : {z : Cylinder | f z.1 < z.2 ∧ z.2 < 1} ⊆ nk.map.source := by
    intro z hz
    exact nk.domain ⟨mem_univ _, by linarith [(abs_lt.mp (hsmall z.1)).1, hz.1], hz.2.trans hlen⟩
  have hfsrc (q : Sphere 2) : (q, f q) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;>
      linarith [(abs_lt.mp (hsmall q)).1, (abs_lt.mp (hsmall q)).2]⟩
  let _ : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) zero_le_one)
  have hconn : IsPreconnected A :=
    (DifferentialGeometry.Topology.isPreconnected_openGraphBand f (fun _ => 1) hf continuous_const
      (by intro q; linarith [(abs_lt.mp (hsmall q)).2])).image nk.map
      (nk.map.contMDiffOn_toFun.continuousOn.mono hsrc)
  have havoid : Disjoint A (frontier Wᶜ) := by
    rw [frontier_compl, hfront, disjoint_left]
    rintro x ⟨z, hz, rfl⟩ ⟨q, hq⟩
    have he := nk.map.toPartialEquiv.injOn (hfsrc q) (hsrc hz) hq
    have hqz : q = z.1 := congrArg Prod.fst he
    have hheight := congrArg Prod.snd he
    change f q = z.2 at hheight
    rw [hqz] at hheight
    exact hz.1.ne hheight
  obtain ⟨r, hr, hrout⟩ := hout
  let b := min r 1 / 2
  have hb : 0 < b := half_pos (lt_min hr zero_lt_one)
  have hbr : b < r := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_left _ _)
  have hb1 : b < 1 := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_right _ _)
  have hAout : A ⊆ Wᶜ :=
    (DifferentialGeometry.Topology.subset_interior_of_isPreconnected_of_disjoint_frontier
      hconn havoid ⟨nk.map (nk.center, b),
        ⟨(nk.center, b), ⟨by simpa only [hzero] using hb, hb1⟩, rfl⟩,
        hW.isOpen_compl.interior_eq.symm ▸ hrout b hb hbr⟩).trans interior_subset
  rintro x ⟨z, hz, rfl⟩
  refine ⟨hcap ⟨z, ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩, rfl⟩, ?_⟩
  exact hAout ⟨z, ⟨by linarith [(abs_lt.mp (hsmall z.1)).2, hz.2.1],
    by linarith [hz.2.2]⟩, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ}

theorem not_exists_monotone_singleton_cap_resets_in_compact
    {K : Set M} (hcompact : IsCompact K) (heps : eps ≤ 1 / 156000)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck (S.base.metric t) eps (p n))
    (U : ℕ → Set M) (cap : ∀ n, LocalCap S epsc (p n) t (U n))
    (hdepth : ∀ n, ∀ z ∈ (cap n).tube,
      10000 / Real.sqrt (S.scalar t (p n)) ≤ metricDistance (S.base.metric t) (p n) z)
    (W : ℕ → Set M) (hW : Monotone W) (hclosed : ∀ n, IsClosed (W n))
    (f : ℕ → Sphere 2 → ℝ) (hf : ∀ n, Continuous (f n))
    (hsmall : ∀ n q, |f n q| < 1 / 10) (hzero : ∀ n, f n (neck n).center = 0)
    (hfront : ∀ n, frontier (W n) = range (fun q : Sphere 2 => (neck n).map (q, f n q)))
    (hout : ∀ n, ∃ r > 0, ∀ a, 0 < a → a < r → (neck n).map ((neck n).center, a) ∉ W n)
    (habsorbed : ∀ n, (cap n).core.carrier ⊆ W (n + 1))
    (hquarter : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∈ K) : False := by
  have hband (n : ℕ) := (neck n).quarter_band_subset_cap_core_sdiff_of_outward_graph
    (by linarith) (cap n) (hdepth n) (f n) (hf n) (hsmall n) (hzero n)
    (hclosed n) (hfront n) (hout n)
  apply not_exists_monotone_fresh_neck_quarter_bands_in_compact
    (S.base.metric t) hcompact heps p neck hquarter W hW
  · intro n x hx
    exact habsorbed n (interior_subset (hband n hx).1)
  · intro n
    exact (hband n ⟨((neck n).center, 1 / 4), ⟨mem_univ _, by norm_num⟩, rfl⟩).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ}

theorem finite_singleton_cap_resets_in_compact
    {K : Set M} (hcompact : IsCompact K) (heps : eps ≤ 1 / 156000)
    (W : ℕ → Set M) (hW : Monotone W) (hclosed : ∀ n, IsClosed (W n))
    (resets : Set ℕ)
    (p : resets → M) (neck : ∀ n, SpatialNeck (S.base.metric t) eps (p n))
    (U : resets → Set M) (cap : ∀ n, LocalCap S epsc (p n) t (U n))
    (hdepth : ∀ n, ∀ z ∈ (cap n).tube,
      10000 / Real.sqrt (S.scalar t (p n)) ≤ metricDistance (S.base.metric t) (p n) z)
    (graph : resets → Sphere 2 → ℝ) (hgraph : ∀ n, Continuous (graph n))
    (hsmall : ∀ n q, |graph n q| < 1 / 10) (hzero : ∀ n, graph n (neck n).center = 0)
    (hfront : ∀ n, frontier (W n.val) = range (fun q : Sphere 2 => (neck n).map (q, graph n q)))
    (hout : ∀ n, ∃ r > 0, ∀ a, 0 < a → a < r → (neck n).map ((neck n).center, a) ∉ W n.val)
    (habsorbed : ∀ n, (cap n).core.carrier ⊆ W (n.val + 1))
    (hquarter : ∀ n, (neck n).map ((neck n).center, 1 / 4) ∈ K) : resets.Finite := by
  classical
  by_contra hfinite
  have hinfinite : resets.Infinite := hfinite
  let f : ℕ → ℕ := Nat.nth (fun n => n ∈ resets)
  have hfm : StrictMono f := Nat.nth_strictMono hinfinite
  have hf (n : ℕ) : f n ∈ resets := Nat.nth_mem_of_infinite hinfinite n
  let r (n : ℕ) : resets := ⟨f n, hf n⟩
  have hW' : Monotone (fun n => W (f n)) := hW.comp hfm.monotone
  apply not_exists_monotone_singleton_cap_resets_in_compact hcompact heps
    (fun n => p (r n)) (fun n => neck (r n)) (fun n => U (r n)) (fun n => cap (r n))
    (fun n => hdepth (r n)) (fun n => W (f n)) hW' (fun n => hclosed (f n))
    (fun n => graph (r n)) (fun n => hgraph (r n)) (fun n => hsmall (r n))
    (fun n => hzero (r n)) (fun n => hfront (r n)) (fun n => hout (r n))
    (fun n => (habsorbed (r n)).trans (hW (Nat.succ_le_iff.mpr (hfm (Nat.lt_succ_self n)))))
    (fun n => hquarter (r n))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ}

theorem not_exists_monotone_anchored_singleton_cap_resets
    (hcompact : ∀ L : ℝ, IsCompact {x : M | S.scalar t x ≤ L})
    (heps : eps ≤ 1 / 156000) (hC2 : 0 < C2)
    (p : ℕ → M) (neck : ∀ n, SpatialNeck (S.base.metric t) eps (p n))
    (witness : ∀ n, CanonicalWitness S epsc C1 C2 (p n) t)
    (cap : ∀ n, LocalCap S epsc (p n) t (witness n).domain.carrier)
    (hdepth : ∀ n, ∀ z ∈ (cap n).tube,
      10000 / Real.sqrt (S.scalar t (p n)) ≤ metricDistance (S.base.metric t) (p n) z)
    (W : ℕ → Set M) (hW : Monotone W) (hclosed : ∀ n, IsClosed (W n))
    (f : ℕ → Sphere 2 → ℝ) (hf : ∀ n, Continuous (f n))
    (hsmall : ∀ n q, |f n q| < 1 / 10) (hzero : ∀ n, f n (neck n).center = 0)
    (hfront : ∀ n, frontier (W n) = range (fun q : Sphere 2 => (neck n).map (q, f n q)))
    (hout : ∀ n, ∃ r > 0, ∀ a, 0 < a → a < r → (neck n).map ((neck n).center, a) ∉ W n)
    (hnested : ∀ n, W n ⊆ (cap n).core.carrier)
    (habsorbed : ∀ n, (cap n).core.carrier ⊆ W (n + 1))
    (anchor : M) (hanchor : anchor ∈ W 0) : False := by
  have hQ (n : ℕ) : S.scalar t (p n) ≤ C2 * S.scalar t anchor := by
    have hanc : anchor ∈ (witness n).domain.carrier :=
      interior_subset ((cap n).core_inside (hnested n (hW (Nat.zero_le n) hanchor)))
    have hb := ((witness n).scalar_bounds anchor hanc).1
    calc
      S.scalar t (p n) = C2 * (C2⁻¹ * S.scalar t (p n)) := by field_simp
      _ ≤ C2 * S.scalar t anchor := mul_le_mul_of_nonneg_left hb hC2.le
  have hband (n : ℕ) := (neck n).quarter_band_subset_cap_core_sdiff_of_outward_graph
    (by linarith) (cap n) (hdepth n) (f n) (hf n) (hsmall n) (hzero n)
    (hclosed n) (hfront n) (hout n)
  apply not_exists_monotone_fresh_neck_quarter_bands_on_scalar_sublevels
    (S.base.metric t) hcompact heps p neck hQ W hW
  · intro n x hx
    exact habsorbed n (interior_subset (hband n hx).1)
  · intro n
    exact (hband n ⟨((neck n).center, 1 / 4), ⟨mem_univ _, by norm_num⟩, rfl⟩).2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps epsc C1 C2 t : ℝ}

theorem finite_singleton_cap_resets_of_monotone_regions
    (hcompact : ∀ L : ℝ, IsCompact {x : M | S.scalar t x ≤ L})
    (heps : eps ≤ 1 / 156000) (hC2 : 0 < C2)
    (W : ℕ → Set M) (hW : Monotone W) (hclosed : ∀ n, IsClosed (W n))
    (anchor : M) (hanchor : anchor ∈ W 0) (resets : Set ℕ)
    (p : resets → M) (neck : ∀ n, SpatialNeck (S.base.metric t) eps (p n))
    (witness : ∀ n, CanonicalWitness S epsc C1 C2 (p n) t)
    (cap : ∀ n, LocalCap S epsc (p n) t (witness n).domain.carrier)
    (hdepth : ∀ n, ∀ z ∈ (cap n).tube,
      10000 / Real.sqrt (S.scalar t (p n)) ≤ metricDistance (S.base.metric t) (p n) z)
    (graph : resets → Sphere 2 → ℝ) (hgraph : ∀ n, Continuous (graph n))
    (hsmall : ∀ n q, |graph n q| < 1 / 10) (hzero : ∀ n, graph n (neck n).center = 0)
    (hfront : ∀ n, frontier (W n.val) = range (fun q : Sphere 2 => (neck n).map (q, graph n q)))
    (hout : ∀ n, ∃ r > 0, ∀ a, 0 < a → a < r → (neck n).map ((neck n).center, a) ∉ W n.val)
    (hnested : ∀ n, W n.val ⊆ (cap n).core.carrier)
    (habsorbed : ∀ n, (cap n).core.carrier ⊆ W (n.val + 1)) : resets.Finite := by
  classical
  by_contra hfinite
  have hinfinite : resets.Infinite := hfinite
  let f : ℕ → ℕ := Nat.nth (fun n => n ∈ resets)
  have hfm : StrictMono f := Nat.nth_strictMono hinfinite
  have hf (n : ℕ) : f n ∈ resets := Nat.nth_mem_of_infinite hinfinite n
  let r (n : ℕ) : resets := ⟨f n, hf n⟩
  have hW' : Monotone (fun n => W (f n)) := hW.comp hfm.monotone
  have hanchor' : anchor ∈ W (f 0) := hW (Nat.zero_le _) hanchor
  apply not_exists_monotone_anchored_singleton_cap_resets hcompact heps hC2
    (fun n => p (r n)) (fun n => neck (r n)) (fun n => witness (r n)) (fun n => cap (r n))
    (fun n => hdepth (r n)) (fun n => W (f n)) hW' (fun n => hclosed (f n))
    (fun n => graph (r n)) (fun n => hgraph (r n)) (fun n => hsmall (r n))
    (fun n => hzero (r n)) (fun n => hfront (r n)) (fun n => hout (r n)) (fun n => hnested (r n))
    (fun n => (habsorbed (r n)).trans (hW (Nat.succ_le_iff.mpr (hfm (Nat.lt_succ_self n)))))
    anchor hanchor'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps beta epsc C1 C2 t : ℝ} {p : M} {W : Set M}

theorem CanonicalWitness.exists_singleton_cap_reset_with_capCore
    (witness : CanonicalWitness S epsc C1 C2 p t)
    (hchart : witness.capTubeHasNeckChart eps)
    (cap : LocalCap S epsc p t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p z)
    (htag : witness.alternative = CanonicalAlternative.cap cap hdepth)
    (oldneck : SpatialNeck (S.base.metric t) beta p) (hbeta : beta ≤ 1 / 8646)
    (hclosed : IsClosed W)
    (graph : Sphere 2 → ℝ) (hgraph : Continuous graph)
    (hsmall : ∀ q, |graph q| < 1 / 10) (hzero : graph oldneck.center = 0)
    (hfront : frontier W = range (fun q : Sphere 2 => oldneck.map (q, graph q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → oldneck.map (oldneck.center, a) ∉ W)
    (hnested : W ⊆ cap.core.carrier) :
    ∃ (V : CompactDomain M) (v : M) (neck : SpatialNeck (S.base.metric t) eps v),
      Nonempty (CapCore V.carrier) ∧
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      W ⊆ V.carrier ∧ cap.core.carrier ⊆ V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tubeMap z) ∧
      (∀ q : Sphere 2, ∀ a, 0 < a → a < 1 / 2 → neck.map (q, 1 / 2 + a) ∉ V.carrier) ∧
      oldneck.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ V.carrier \ W := by
  obtain ⟨v, nk, hmap⟩ := hchart cap hdepth htag
  obtain ⟨V, hV, _, hVU, hVfront⟩ :=
    cap.exists_truncated_compactDomain (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
  have hmodel : Nonempty (CapCore V.carrier) := by
    rw [hV]
    exact cap.nonempty_capCore_truncated_core (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  refine ⟨V, v, nk.toSpatialNeck, hmodel, hV, ?_, ?_, hVU, ?_, ?_, ?_, ?_⟩
  · exact hnested.trans (hV ▸ subset_union_left)
  · exact hV ▸ subset_union_left
  · rw [hVfront]
    congr 1
    funext q
    exact hmap _
  · intro z
    exact (hmap z).symm
  · intro q a ha ha1
    change nk.map (q, 1 / 2 + a) ∉ V.carrier
    rw [← hmap, hV]
    intro h
    have hm := (cap.mem_truncated_core_on_tube (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1)
      q (by constructor <;> linarith : 1 / 2 + a ∈ Icc (0 : ℝ) 1)).mp h
    linarith
  · intro x hx
    have hh := oldneck.quarter_band_subset_cap_core_sdiff_of_outward_graph hbeta cap hdepth
      graph hgraph hsmall hzero hclosed hfront hout hx
    exact ⟨hV ▸ Or.inl (interior_subset hh.1), hh.2⟩

theorem CanonicalWitness.exists_singleton_cap_reset
    (witness : CanonicalWitness S epsc C1 C2 p t)
    (hchart : witness.capTubeHasNeckChart eps)
    (cap : LocalCap S epsc p t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p z)
    (htag : witness.alternative = CanonicalAlternative.cap cap hdepth)
    (oldneck : SpatialNeck (S.base.metric t) beta p) (hbeta : beta ≤ 1 / 8646)
    (hclosed : IsClosed W)
    (graph : Sphere 2 → ℝ) (hgraph : Continuous graph)
    (hsmall : ∀ q, |graph q| < 1 / 10) (hzero : graph oldneck.center = 0)
    (hfront : frontier W = range (fun q : Sphere 2 => oldneck.map (q, graph q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → oldneck.map (oldneck.center, a) ∉ W)
    (hnested : W ⊆ cap.core.carrier) :
    ∃ (V : CompactDomain M) (v : M) (neck : SpatialNeck (S.base.metric t) eps v),
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      W ⊆ V.carrier ∧ cap.core.carrier ⊆ V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tubeMap z) ∧
      (∀ q : Sphere 2, ∀ a, 0 < a → a < 1 / 2 → neck.map (q, 1 / 2 + a) ∉ V.carrier) ∧
      oldneck.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ V.carrier \ W := by
  obtain ⟨V, v, neck, _, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩ :=
    witness.exists_singleton_cap_reset_with_capCore hchart cap hdepth htag oldneck hbeta hclosed
      graph hgraph hsmall hzero hfront hout hnested
  exact ⟨V, v, neck, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩

theorem CanonicalWitness.exists_connected_singleton_cap_reset_with_capCore
    [PreconnectedSpace M] (witness : CanonicalWitness S epsc C1 C2 p t)
    (hchart : witness.capTubeHasNeckChart eps)
    (cap : LocalCap S epsc p t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p z)
    (htag : witness.alternative = CanonicalAlternative.cap cap hdepth)
    (oldneck : SpatialNeck (S.base.metric t) beta p) (hbeta : beta ≤ 1 / 8646)
    (hclosed : IsClosed W)
    (graph : Sphere 2 → ℝ) (hgraph : Continuous graph)
    (hsmall : ∀ q, |graph q| < 1 / 10) (hzero : graph oldneck.center = 0)
    (hfront : frontier W = range (fun q : Sphere 2 => oldneck.map (q, graph q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → oldneck.map (oldneck.center, a) ∉ W)
    (hnested : W ⊆ cap.core.carrier) :
    ∃ (V : CompactDomain M) (v : M) (neck : SpatialNeck (S.base.metric t) eps v),
      Nonempty (CapCore V.carrier) ∧ IsConnected (interior V.carrier) ∧
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      W ⊆ V.carrier ∧ cap.core.carrier ⊆ V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tubeMap z) ∧
      (∀ q : Sphere 2, ∀ a, 0 < a → a < 1 / 2 → neck.map (q, 1 / 2 + a) ∉ V.carrier) ∧
      oldneck.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ V.carrier \ W := by
  obtain ⟨V, v, neck, hmodel, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩ :=
    witness.exists_singleton_cap_reset_with_capCore hchart cap hdepth htag oldneck hbeta hclosed
      graph hgraph hsmall hzero hfront hout hnested
  have hconn := isConnected_interior_of_compact_regular_neck_boundary neck
    (by norm_num : |(1 / 2 : ℝ)| ≤ 4) V.compact V.regular_closed hfrontV
  exact ⟨V, v, neck, hmodel, hconn, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩

theorem CanonicalWitness.exists_connected_singleton_cap_reset
    [PreconnectedSpace M] (witness : CanonicalWitness S epsc C1 C2 p t)
    (hchart : witness.capTubeHasNeckChart eps)
    (cap : LocalCap S epsc p t witness.domain.carrier)
    (hdepth : ∀ z ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t p) ≤ metricDistance (S.base.metric t) p z)
    (htag : witness.alternative = CanonicalAlternative.cap cap hdepth)
    (oldneck : SpatialNeck (S.base.metric t) beta p) (hbeta : beta ≤ 1 / 8646)
    (hclosed : IsClosed W)
    (graph : Sphere 2 → ℝ) (hgraph : Continuous graph)
    (hsmall : ∀ q, |graph q| < 1 / 10) (hzero : graph oldneck.center = 0)
    (hfront : frontier W = range (fun q : Sphere 2 => oldneck.map (q, graph q)))
    (hout : ∃ r > 0, ∀ a, 0 < a → a < r → oldneck.map (oldneck.center, a) ∉ W)
    (hnested : W ⊆ cap.core.carrier) :
    ∃ (V : CompactDomain M) (v : M) (neck : SpatialNeck (S.base.metric t) eps v),
      IsConnected (interior V.carrier) ∧
      V.carrier = cap.core.carrier ∪ cap.tubeMap '' (univ ×ˢ Icc (0 : ℝ) (1 / 2)) ∧
      W ⊆ V.carrier ∧ cap.core.carrier ⊆ V.carrier ∧ V.carrier ⊆ witness.domain.carrier ∧
      frontier V.carrier = range (fun q : Sphere 2 => neck.map (q, 1 / 2)) ∧
      (∀ z, neck.map z = cap.tubeMap z) ∧
      (∀ q : Sphere 2, ∀ a, 0 < a → a < 1 / 2 → neck.map (q, 1 / 2 + a) ∉ V.carrier) ∧
      oldneck.map '' (univ ×ˢ Icc (1 / 8 : ℝ) (3 / 8)) ⊆ V.carrier \ W := by
  obtain ⟨V, v, neck, _, hconn, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩ :=
    witness.exists_connected_singleton_cap_reset_with_capCore hchart cap hdepth htag oldneck hbeta
      hclosed graph hgraph hsmall hzero hfront hout hnested
  exact ⟨V, v, neck, hconn, hV, hWV, hcore, hVU, hfrontV, hmap, houtV, hfresh⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
