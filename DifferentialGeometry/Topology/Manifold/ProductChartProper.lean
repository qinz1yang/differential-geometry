import DifferentialGeometry.Topology.Manifold.ProductChartGluing
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.Instances.NNReal.Lemmas

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology NNReal
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (localDiffeomorph_isSmoothEmbedding_of_injective)

section

namespace DifferentialGeometry.Topology.Manifold

variable {N M : Type*} [TopologicalSpace N] [TopologicalSpace M]

theorem continuousOn_productChartMap_nonnegative
    (P : ℕ → N × ℝ → M)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (hnear : ∀ n z, z ∈ univ ×ˢ Icc (0 : ℝ) 1 → ContinuousAt (P n) z) :
    ContinuousOn (productChartMap P) (univ ×ˢ Ici (0 : ℝ)) := by
  intro z hz
  by_cases hpos : 0 < z.2
  · obtain ⟨n, ht, heq⟩ := productChartMap_eventuallyEq_chart P hseam z hpos
    have hc : ContinuousAt (fun w : N × ℝ => P n (w.1, w.2 - n)) z :=
      (hnear n (z.1, z.2 - n) ⟨mem_univ _, ht⟩).comp
        (f := fun w : N × ℝ => (w.1, w.2 - (n : ℝ)))
        (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousAt
    exact (hc.congr heq.symm).continuousWithinAt
  · have hzero : z.2 = 0 := le_antisymm (not_lt.mp hpos) hz.2
    have hc := hnear 0 (z.1, 0) ⟨mem_univ _, by norm_num⟩
    have hc' : ContinuousWithinAt (P 0) (univ ×ˢ Ici (0 : ℝ)) z := by
      have he : z = (z.1, 0) := Prod.ext rfl hzero
      rw [he]
      exact hc.continuousWithinAt
    apply hc'.congr_of_eventuallyEq_of_mem _ hz
    have hsmall : ∀ᶠ w : N × ℝ in 𝓝 z, w.2 < 1 :=
      continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hzero]; norm_num))
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds] with w hw hwl
    have hfloor : ⌊w.2⌋₊ = 0 := Nat.floor_eq_zero.mpr hwl
    simp only [productChartMap, hfloor, Nat.cast_zero, sub_zero]

def halfCylinderProductMap (P : ℕ → N × ℝ → M) (x : N × ℝ≥0) : M :=
  productChartMap P (x.1, x.2.val)

theorem continuous_halfCylinderProductMap
    (P : ℕ → N × ℝ → M)
    (hnear : ∀ n z, z ∈ univ ×ˢ Icc (0 : ℝ) 1 → ContinuousAt (P n) z)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1)) :
    Continuous (halfCylinderProductMap P) :=
  (continuousOn_productChartMap_nonnegative P hseam hnear).comp_continuous
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    (fun x => ⟨mem_univ _, x.2.property⟩)

theorem isProperMap_halfCylinderProductMap [CompactSpace N] [T2Space M]
    [CompactlyCoherentSpace M]
    (P : ℕ → N × ℝ → M)
    (hcont : Continuous (halfCylinderProductMap P))
    (hescape : ∀ K : Set M, IsCompact K → ∀ᶠ n in atTop,
      Disjoint (P n '' (univ ×ˢ Icc (0 : ℝ) 1)) K) :
    IsProperMap (halfCylinderProductMap P) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont, ?_⟩
  intro K hK
  obtain ⟨n, hn⟩ := eventually_atTop.mp (hescape K hK)
  let L : Set (N × ℝ≥0) := univ ×ˢ Icc (0 : ℝ≥0) (n : ℝ≥0)
  have hL : IsCompact L := isCompact_univ.prod isCompact_Icc
  apply hL.of_isClosed_subset (hK.isClosed.preimage hcont)
  intro x hx
  refine ⟨mem_univ _, zero_le, ?_⟩
  by_contra h
  have hnx : (n : ℝ) < x.2.val := by exact_mod_cast not_le.mp h
  have hfloor : n ≤ ⌊x.2.val⌋₊ := Nat.le_floor hnx.le
  have hmem : halfCylinderProductMap P x ∈ P ⌊x.2.val⌋₊ '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    refine ⟨(x.1, x.2.val - (⌊x.2.val⌋₊ : ℝ)), ?_, rfl⟩
    exact ⟨mem_univ _, sub_nonneg.mpr (Nat.floor_le x.2.property),
      by linarith [Nat.lt_floor_add_one x.2.val]⟩
  exact disjoint_left.mp (hn _ hfloor) hmem hx

end DifferentialGeometry.Topology.Manifold

end

section

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [CompactSpace N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]
  [T2Space M] [CompactlyCoherentSpace M]

theorem isProperMap_product_of_compatible_slabs
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1)))
    (hescape : ∀ K : Set M, IsCompact K → ∀ᶠ n in atTop,
      Disjoint (P n '' (univ ×ˢ Icc (0 : ℝ) 1)) K) :
    IsProperMap (halfCylinderProductMap (fun n => P n)) ∧
      Function.Injective (halfCylinderProductMap (fun n => P n)) ∧
      range (halfCylinderProductMap (fun n => P n)) =
        ⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∧
      (∀ z : N, halfCylinderProductMap (fun n => P n) (z, 0) = P 0 (z, 0)) ∧
      ∀ (n : ℕ) (z : N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
        halfCylinderProductMap (fun n => P n)
          (z, ⟨(n : ℝ) + t, add_nonneg (Nat.cast_nonneg n) ht.1⟩) = P n (z, t) := by
  have hnear : ∀ n z, z ∈ univ ×ˢ Icc (0 : ℝ) 1 → ContinuousAt (P n) z :=
    fun n z hz => (P n).contMDiffOn_toFun.continuousOn.continuousAt
      ((P n).open_source.mem_nhds (hsource n hz))
  have hcont := continuous_halfCylinderProductMap (fun n => P n) hnear hseam
  have hproper := isProperMap_halfCylinderProductMap (fun n => P n) hcont hescape
  have hboundary (n : ℕ) (z : N) : P (n + 1) (z, 0) = P n (z, 1) := by
    obtain ⟨V, _, hV, heq⟩ := hseam n
    simpa only [zero_add] using heq (z, 0) (hV ⟨mem_univ _, rfl⟩)
  have hinj : Function.Injective (halfCylinderProductMap (fun n => P n)) := by
    intro x y hxy
    have h : (x.1, x.2.val) = (y.1, y.2.val) :=
      productChartMap_injOn P hsource hadjacent hseparated
        (show (x.1, x.2.val) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, x.2.property⟩)
        (show (y.1, y.2.val) ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, y.2.property⟩) hxy
    apply Prod.ext
    · exact congrArg (fun z : N × ℝ => z.1) h
    · exact Subtype.ext (congrArg (fun z : N × ℝ => z.2) h)
  have hstrip (n : ℕ) (z : N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      halfCylinderProductMap (fun n => P n)
        (z, ⟨(n : ℝ) + t, add_nonneg (Nat.cast_nonneg n) ht.1⟩) = P n (z, t) := by
    have hh := productChartMap_eq_on_closed_strip (fun n => P n) hboundary n z ((n : ℝ) + t)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [halfCylinderProductMap, add_sub_cancel_left] using hh
  refine ⟨hproper, hinj, ?_, ?_, hstrip⟩
  · ext x
    constructor
    · rintro ⟨⟨z, t⟩, rfl⟩
      refine mem_iUnion.mpr ⟨⌊t.val⌋₊, (z, t.val - (⌊t.val⌋₊ : ℝ)),
        ⟨mem_univ _, sub_nonneg.mpr (Nat.floor_le t.property), ?_⟩, rfl⟩
      linarith [Nat.lt_floor_add_one t.val]
    · intro hx
      obtain ⟨n, ⟨z, t⟩, ht, htx⟩ := mem_iUnion.mp hx
      exact ⟨(z, ⟨(n : ℝ) + t, add_nonneg (Nat.cast_nonneg n) ht.2.1⟩),
        (hstrip n z t ht.2).trans htx⟩
  · intro z
    change P ⌊(0 : ℝ)⌋₊ (z, 0 - (⌊(0 : ℝ)⌋₊ : ℝ)) = P 0 (z, 0)
    norm_num

end DifferentialGeometry.Topology.Manifold

end

section

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]

theorem productChartMap_isLocalDiffeomorphOn_nonnegative
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1)) :
    IsLocalDiffeomorphOn (I.prod 𝓘(ℝ)) J ∞
      (productChartMap (fun n => P n)) (univ ×ˢ Ici (0 : ℝ)) := by
  intro z
  by_cases hz : 0 < z.val.2
  · exact productChartMap_isLocalDiffeomorphOn P hsource hseam
      ⟨z.val, mem_univ _, hz⟩
  · have hzero : z.val.2 = 0 := le_antisymm (not_lt.mp hz) z.property.2
    apply isLocalDiffeomorphAt_of_eventuallyEq_partialDiffeomorph (P 0)
    · apply hsource 0
      exact ⟨mem_univ _, by rw [hzero]; exact ⟨le_rfl, zero_le_one⟩⟩
    · have hnear : ∀ᶠ w : N × ℝ in 𝓝 z.val, w.2 < 1 :=
        continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by rw [hzero]; norm_num))
      filter_upwards [hnear] with w hw
      have hfloor : ⌊w.2⌋₊ = 0 := Nat.floor_eq_zero.mpr hw
      simp only [productChartMap, hfloor, Nat.cast_zero, sub_zero]

theorem contMDiffOn_productChartMap_nonnegative
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1)) :
    ContMDiffOn (I.prod 𝓘(ℝ)) J ∞
      (productChartMap (fun n => P n)) (univ ×ˢ Ici (0 : ℝ)) := by
  intro z hz
  exact ((productChartMap_isLocalDiffeomorphOn_nonnegative P hsource hseam
    ⟨z, hz⟩).contMDiffAt).contMDiffWithinAt

theorem isSmoothEmbedding_productChartMap_interior
    [I.Boundaryless] [J.Boundaryless] [IsManifold I ∞ N] [IsManifold J ∞ M]
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1))) :
    let U : TopologicalSpace.Opens (N × ℝ) :=
      ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
    IsSmoothEmbedding (I.prod 𝓘(ℝ)) J ∞
      (fun p : U => productChartMap (fun n => P n) p) := by
  let U : TopologicalSpace.Opens (N × ℝ) :=
    ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
  have hlocal := DifferentialGeometry.isLocalDiffeomorph_restrict_open U
    (productChartMap_isLocalDiffeomorphOn P hsource hseam)
  apply localDiffeomorph_isSmoothEmbedding_of_injective hlocal
  intro x y heq
  apply Subtype.ext
  have hx : 0 < x.val.2 := x.property.2
  have hy : 0 < y.val.2 := y.property.2
  exact productChartMap_injOn P hsource hadjacent hseparated
    (show x.val ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, hx.le⟩)
    (show y.val ∈ univ ×ˢ Ici (0 : ℝ) from ⟨mem_univ _, hy.le⟩) heq

end DifferentialGeometry.Topology.Manifold

end
