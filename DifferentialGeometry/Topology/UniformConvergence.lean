import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.UniformSpace.Pi

set_option autoImplicit false

open Filter Set

namespace TendstoUniformlyOn

variable {A E N : Type*} [UniformSpace E]
  {K : Set A} {X : N → A → E} {v : A → E} {l : Filter N}

theorem eventually_mapsTo_of_isCompact_image
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact (v '' K))
    {U : Set E} (hU : IsOpen U) (hv : MapsTo v K U) :
    ∀ᶠ n in l, MapsTo (X n) K U := by
  obtain ⟨V, hV, _, hball⟩ := lebesgue_number_of_compact_open
    hK hU (mapsTo_iff_image_subset.mp hv)
  filter_upwards [hX V hV] with n hn z hz
  exact hball (v z) (mem_image_of_mem v hz) (hn z hz)

theorem eventually_mapsTo_of_isCompact [TopologicalSpace A]
    (hX : TendstoUniformlyOn X v l K) (hK : IsCompact K)
    (hv : ContinuousOn v K) {U : Set E} (hU : IsOpen U) (hmap : MapsTo v K U) :
    ∀ᶠ n in l, MapsTo (X n) K U :=
  hX.eventually_mapsTo_of_isCompact_image (hK.image_of_continuousOn hv) hU hmap

theorem eventually_forall_mapsTo_of_isCompact_image
    {J : Type*} [Finite J] {xi : N → A → J → E} {f : A → J → E}
    (hxi : TendstoUniformlyOn xi f l K)
    (hK : ∀ j, IsCompact ((fun z => f z j) '' K))
    {U : J → Set E} (hU : ∀ j, IsOpen (U j))
    (hf : ∀ j, MapsTo (fun z => f z j) K (U j)) :
    ∀ᶠ n in l, ∀ j, MapsTo (fun z => xi n z j) K (U j) := by
  apply Filter.eventually_all.mpr
  intro j
  have hj : TendstoUniformlyOn (fun n z => xi n z j) (fun z => f z j) l K :=
    (Pi.uniformContinuous_proj (fun _ : J => E) j).comp_tendstoUniformlyOn hxi
  exact hj.eventually_mapsTo_of_isCompact_image (hK j) (hU j) (hf j)

end TendstoUniformlyOn

namespace TendstoUniformlyOn

variable {A E N J : Type*} [PseudoMetricSpace E] [Finite J]
  {K : Set A} {X : N → A → E} {v : A → E}
  {xi : N → A → J → E} {l : Filter N}

theorem eventually_forall_pair_mem_ball_of_isCompact_image
    (hX : TendstoUniformlyOn X v l K)
    (hxi : TendstoUniformlyOn xi (fun z _ => v z) l K)
    (hK : IsCompact (v '' K)) {a : E} {eps : ℝ}
    (hv : MapsTo v K (Metric.ball a eps)) :
    ∀ᶠ n in l, ∀ z ∈ K, ∀ j,
      (X n z, xi n z j) ∈ Metric.ball (a, a) eps := by
  have hXmem := hX.eventually_mapsTo_of_isCompact_image hK Metric.isOpen_ball hv
  have hximem := hxi.eventually_forall_mapsTo_of_isCompact_image
    (fun _ => hK) (fun _ => Metric.isOpen_ball) (fun _ => hv)
  filter_upwards [hXmem, hximem] with n hn hxn z hz j
  rw [← ball_prod_same]
  exact ⟨hn hz, hxn j hz⟩

theorem eventually_forall_pair_mem_ball_of_isCompact [TopologicalSpace A]
    (hX : TendstoUniformlyOn X v l K)
    (hxi : TendstoUniformlyOn xi (fun z _ => v z) l K)
    (hK : IsCompact K) (hvc : ContinuousOn v K) {a : E} {eps : ℝ}
    (hv : MapsTo v K (Metric.ball a eps)) :
    ∀ᶠ n in l, ∀ z ∈ K, ∀ j,
      (X n z, xi n z j) ∈ Metric.ball (a, a) eps :=
  hX.eventually_forall_pair_mem_ball_of_isCompact_image hxi
    (hK.image_of_continuousOn hvc) hv

end TendstoUniformlyOn

namespace DifferentialGeometry

theorem eventually_mapsTo_of_tendstoUniformly
    {X Y ι : Type*} [TopologicalSpace X] [UniformSpace Y]
    {A : Set X} {f : X → Y} {U : Set Y} {F : ι → X → Y} {p : Filter ι}
    (hconv : TendstoUniformly F f p) (hA : IsCompact A)
    (hf : ContinuousOn f A) (hU : IsOpen U) (hmap : MapsTo f A U) :
    ∀ᶠ n in p, MapsTo (F n) A U :=
  hconv.tendstoUniformlyOn.eventually_mapsTo_of_isCompact hA hf hU hmap

end DifferentialGeometry

theorem TendstoUniformlyOn.comp_tendstoUniformly
    {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {s : Set β} {F : ι → β → γ} {f : β → γ}
    {u : ι → α → β} {v : α → β}
    (hF : TendstoUniformlyOn F f l s) (hf : UniformContinuousOn f s)
    (hu : TendstoUniformly u v l)
    (hus : ∀ᶠ i in l, ∀ x, u i x ∈ s) (hvs : ∀ x, v x ∈ s) :
    TendstoUniformly (fun i x => F i (u i x)) (fun x => f (v x)) l := by
  have hcomp := hf.comp_tendstoUniformly_eventually hus hvs hu
  intro V hV
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  filter_upwards [hF W hW, hcomp W hW, hus] with i hi hci hsi
  intro x
  exact hWV (SetRel.prodMk_mem_comp (hci x) (hi _ (hsi x)))

noncomputable section
open scoped Topology

theorem Topology.IsClosedEmbedding.exists_continuousMap_of_tendstoUniformly
    {X M F ι : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [UniformSpace F] {f : M → F} (hf : IsClosedEmbedding f)
    {Y : ι → X → M} {YT : X → F} {l : Filter ι}
    (hlim : TendstoUniformly (fun i x => f (Y i x)) YT l)
    (hcont : ∃ᶠ i in l, Continuous (Y i)) :
    ∃ yT : C(X, M), (∀ x, f (yT x) = YT x) ∧
      ∀ x, Tendsto (fun i => Y i x) l (𝓝 (yT x)) := by
  let _ : NeBot l := (frequently_true_iff_neBot l).mp
    (hcont.mono fun _ _ => trivial)
  have hrange : ∀ x, YT x ∈ range f := by
    intro x
    exact hf.isClosed_range.mem_of_tendsto (hlim.tendsto_at x)
      (Eventually.of_forall fun i => mem_range_self (Y i x))
  choose yT hyT using hrange
  have hcontinuous : Continuous YT :=
    hlim.continuous (hcont.mono fun i hi => hf.continuous.comp hi)
  have hycontinuous : Continuous yT := hf.isEmbedding.continuous_iff.mpr
    (hcontinuous.congr fun x => (hyT x).symm)
  refine ⟨⟨yT, hycontinuous⟩, hyT, ?_⟩
  intro x
  apply hf.isEmbedding.isInducing.tendsto_nhds_iff.mpr
  change Tendsto (fun i => f (Y i x)) l (𝓝 (f (yT x)))
  rw [hyT x]
  exact hlim.tendsto_at x

end

theorem TendstoUniformlyOn.comp_of_eventually_mapsTo
    {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
    {l : Filter ι} {K : Set α} {L : Set β}
    {A : ι → β → γ} {Ainf : β → γ} {B : ι → α → β} {Binf : α → β}
    (hA : TendstoUniformlyOn A Ainf l L)
    (hAinf : UniformContinuousOn Ainf L)
    (hB : TendstoUniformlyOn B Binf l K)
    (hmap : ∀ᶠ k in l, MapsTo (B k) K L)
    (hmapInf : MapsTo Binf K L) :
    TendstoUniformlyOn (fun k x => A k (B k x)) (fun x => Ainf (Binf x)) l K := by
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hB ⊢
  apply hA.comp_tendstoUniformly hAinf hB
  · filter_upwards [hmap] with k hk x
    exact hk x.property
  · intro x
    exact hmapInf x.property
