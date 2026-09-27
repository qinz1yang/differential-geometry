import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Algebra.Order.LiminfLimsup

section

noncomputable section
open Filter Set
open scoped Topology

namespace Topology

theorem exists_mapClusterPt_of_continuous_pairwise_limits
    {ι A B : Type*} [TopologicalSpace B] [CompactSpace B]
    {l : Filter ι} [NeBot l] (f : ι → A → B)
    (delta : B × B → ℝ) (hdelta : Continuous delta)
    (D : A → A → ℝ)
    (hD : ∀ x y, Tendsto (fun i => delta (f i x, f i y)) l (𝓝 (D x y))) :
    ∃ F : A → B, MapClusterPt F l f ∧ ∀ x y, delta (F x, F y) = D x y := by
  obtain ⟨F, _, hF⟩ := (isCompact_univ : IsCompact (Set.univ : Set (A → B))).exists_mapClusterPt
    (show Filter.map f l ≤ 𝓟 (Set.univ : Set (A → B)) by simp)
  refine ⟨F, hF, ?_⟩
  intro x y
  have heval : Continuous (fun G : A → B => delta (G x, G y)) :=
    hdelta.comp ((continuous_apply x).prodMk (continuous_apply y))
  have hc := hF.continuousAt_comp heval.continuousAt
  exact eq_of_nhds_neBot (hc.clusterPt.mono (hD x y))


end Topology

end

end

section

noncomputable section
open Filter Set
open scoped Topology

namespace Topology

theorem continuous_of_compact_separating_kernel
    {A B : Type*} [PseudoMetricSpace A] [TopologicalSpace B] [CompactSpace B]
    (delta : B × B → ℝ) (hdelta : Continuous delta)
    (hzero : ∀ y z, delta (y, z) = 0 → y = z)
    (F : A → B) (hmetric : ∀ x y, delta (F x, F y) = dist x y) : Continuous F := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply (isCompact_univ : IsCompact (Set.univ : Set B)).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun _ => mem_univ _)
  intro y _ hy
  have hc : Continuous (fun z : B => delta (z, F x)) :=
    hdelta.comp (continuous_id.prodMk continuous_const)
  have hcluster := hy.continuousAt_comp hc.continuousAt
  have ht : Tendsto (fun z : A => delta (F z, F x)) (𝓝 x) (𝓝 0) := by
    simpa only [hmetric, id_eq, dist_self] using
      ((continuous_id.dist (continuous_const (y := x))).tendsto x)
  exact hzero y (F x) (eq_of_nhds_neBot (hcluster.clusterPt.mono ht))

end Topology

end

end

section

open Filter Set
open scoped Topology

namespace Topology

theorem tendsto_inverse_pair_distance_of_uniform_distance_error
    {ι Q : Type*} {M : ι → Type*} {l : Filter ι}
    (limitDistance : Q → Q → ℝ) (sourceDistance : ∀ i, M i → M i → ℝ)
    (f : ∀ i, Q → M i) (K : Set Q)
    (herror : ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ i in l, ∀ p ∈ K, ∀ q ∈ K,
      |sourceDistance i (f i p) (f i q) - limitDistance p q| < epsilon)
    (u v : ∀ i, M i) (p q : ι → Q)
    (hp : ∀ᶠ i in l, p i ∈ K ∧ f i (p i) = u i)
    (hq : ∀ᶠ i in l, q i ∈ K ∧ f i (q i) = v i)
    {D : ℝ} (hsource : Tendsto (fun i => sourceDistance i (u i) (v i)) l (𝓝 D)) :
    Tendsto (fun i => limitDistance (p i) (q i)) l (𝓝 D) := by
  have hdiff : Tendsto (fun i => sourceDistance i (u i) (v i) - limitDistance (p i) (q i)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [herror epsilon hepsilon, hp, hq] with i hi hpi hqi
    have h := hi (p i) hpi.1 (q i) hqi.1
    rw [hpi.2, hqi.2] at h
    simpa only [Real.dist_eq, sub_zero] using h
  simpa only [sub_sub_cancel, sub_zero] using hsource.sub hdiff

end Topology

end

section


open Filter Set
open scoped Topology

theorem MapClusterPt.mem_range_of_compact
    {ι B T : Type*} [TopologicalSpace B] [TopologicalSpace T] [T2Space T]
    {l : Filter ι} {D K : Set B} {u : ι → D → T} {F : D → T}
    (hF : MapClusterPt F l u) (hK : IsCompact K) (v : ι → B)
    (hv : ∀ᶠ i in l, v i ∈ K)
    (hD : ∀ x ∈ K, MapClusterPt x l v → x ∈ D) (p : T)
    (hp : ∀ (m : Filter ι), m ≤ l → m.NeBot →
      ∀ (x : B) (hx : x ∈ D), Tendsto v m (𝓝 x) →
        Tendsto (fun i => u i ⟨x, hx⟩) m (𝓝 p)) :
    p ∈ range F := by
  let lF : Filter ι := l ⊓ comap u (𝓝 F)
  have hlF : lF ≤ l := inf_le_left
  have hlF_ne : lF.NeBot := neBot_inf_comap_iff_map.mpr (by
    simpa only [inf_comm] using hF.clusterPt.neBot)
  let : lF.NeBot := hlF_ne
  have hu : Tendsto u lF (𝓝 F) := tendsto_iff_comap.mpr inf_le_right
  obtain ⟨x, hxK, hxv⟩ := hK.exists_mapClusterPt
    (show map v lF ≤ 𝓟 K from le_principal_iff.mpr (hv.filter_mono hlF))
  have hxD : x ∈ D := hD x hxK (hxv.mono hlF)
  let m : Filter ι := lF ⊓ comap v (𝓝 x)
  have hmF : m ≤ lF := inf_le_left
  have hm : m ≤ l := hmF.trans hlF
  have hm_ne : m.NeBot := neBot_inf_comap_iff_map.mpr (by
    simpa only [inf_comm] using hxv.clusterPt.neBot)
  let : m.NeBot := hm_ne
  have hvm : Tendsto v m (𝓝 x) := tendsto_iff_comap.mpr inf_le_right
  have heval : Continuous (fun G : D → T => G ⟨x, hxD⟩) := continuous_apply _
  have hum : Tendsto (fun i => u i ⟨x, hxD⟩) m (𝓝 (F ⟨x, hxD⟩)) :=
    (heval.tendsto F).comp (hu.mono_left hmF)
  exact ⟨⟨x, hxD⟩, tendsto_nhds_unique hum (hp m hm hm_ne x hxD hvm)⟩

end
