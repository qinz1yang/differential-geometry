import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianRetractH
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# CP1-A3 (G2, stage level): description of `PersistentCuspExterior.region` through the cores
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1
open GC.LongTime

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- The image of the interior of the core of a truncation. -/
def intImg_CPA3 {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) : Set H.Carrier :=
  T.inclusion '' (T.core.interior : Set T.core.Carrier)

theorem isOpenEmbedding_map_CPA3 (i : Fin cores.count) (t : ℝ) (hc : cores.start ≤ t) :
    _root_.Topology.IsOpenEmbedding (fun x : ↥(cores.domain i t) => cores.map i t hc x) := by
  have hf := cores.embedding i t hc
  exact DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion _
    hf.contMDiff hf.isEmbedding.injective
    (fun z => DifferentialGeometry.Topology.Manifold.injective_mfderiv_of_isImmersionAt
      (𝓡 3) (𝓡 3) _ z (hf.isImmersion.isImmersionAt z)) rfl

theorem isOpen_image_domain_CPA3 (i : Fin cores.count) (t : ℝ) (hc : cores.start ≤ t) :
    IsOpen (cores.map i t hc '' (cores.domain i t : Set (cores.model i).Carrier)) := by
  have := (isOpenEmbedding_map_CPA3 (cores := cores) i t hc).isOpen_range
  rw [image_eq_range (cores.map i t hc) (cores.domain i t : Set (cores.model i).Carrier)]
  exact this

theorem continuousOn_map_CPA3 (i : Fin cores.count) (t : ℝ) (hc : cores.start ≤ t) :
    ContinuousOn (cores.map i t hc) (cores.domain i t : Set (cores.model i).Carrier) :=
  (cores.smooth i t hc).continuousOn

theorem region_eq_CPA3 (E : PersistentCuspExterior cores) {t : ℝ} (ht : E.start ≤ t) :
    E.region t = (⋃ i, cores.map i t (E.after_cores.trans ht) '' intImg_CPA3 (E.truncation i))ᶜ := by
  unfold PersistentCuspExterior.region
  rw [dif_pos ht]
  rfl

theorem range_inclusion_subset_domain_CPA3 (E : PersistentCuspExterior cores) {t : ℝ}
    (ht : E.start ≤ t) (i : Fin cores.count) :
    range (E.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier) :=
  fun _ hp => cores.advertised_ball i t (E.after_cores.trans ht) (E.in_ball i t ht hp)

theorem intImg_subset_domain_CPA3 (E : PersistentCuspExterior cores) {t : ℝ}
    (ht : E.start ≤ t) (i : Fin cores.count) :
    intImg_CPA3 (E.truncation i) ⊆ (cores.domain i t : Set (cores.model i).Carrier) := by
  rintro _ ⟨c, -, rfl⟩
  exact range_inclusion_subset_domain_CPA3 E ht i ⟨c, rfl⟩

/-- A point `m i x` of the `i`-th model patch lies in the exterior region iff `x` is not in the
interior of the `i`-th core. -/
theorem mem_region_image_iff_CPA3 (E : PersistentCuspExterior cores) {t : ℝ} (ht : E.start ≤ t)
    (i : Fin cores.count) {x : (cores.model i).Carrier}
    (hx : x ∈ (cores.domain i t : Set (cores.model i).Carrier)) :
    cores.map i t (E.after_cores.trans ht) x ∈ E.region t ↔ x ∉ intImg_CPA3 (E.truncation i) := by
  have hc := E.after_cores.trans ht
  rw [region_eq_CPA3 E ht, mem_compl_iff, not_iff_not, mem_iUnion]
  constructor
  · rintro ⟨j, y, hy, hyx⟩
    by_cases hji : j = i
    · subst hji
      have hinj := (cores.embedding j t hc).isEmbedding.injective
      have := @hinj ⟨y, intImg_subset_domain_CPA3 E ht j hy⟩ ⟨x, hx⟩ hyx
      have h2 : y = x := congrArg Subtype.val this
      rw [← h2]; exact hy
    · exfalso
      have hdis := cores.disjoint t hc hji
      exact Set.disjoint_left.mp hdis ⟨y, intImg_subset_domain_CPA3 E ht j hy, hyx⟩ ⟨x, hx, rfl⟩
  · intro hxi
    exact ⟨i, x, hxi, rfl⟩

theorem not_mem_region_of_mem_image_CPA3 (E : PersistentCuspExterior cores) {t : ℝ}
    (ht : E.start ≤ t) {p : (postStage F.observation t).Carrier}
    (hp : p ∈ E.region t) (j : Fin cores.count) (y : (cores.model j).Carrier)
    (hy : y ∈ intImg_CPA3 (E.truncation j)) :
    p ≠ cores.map j t (E.after_cores.trans ht) y := by
  intro h
  rw [region_eq_CPA3 E ht] at hp
  exact hp (mem_iUnion.mpr ⟨j, y, hy, h.symm⟩)

end GC.LongTime.CuspP1
