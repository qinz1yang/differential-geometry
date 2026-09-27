import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Algebra.Order.Field.Pi
import DifferentialGeometry.Topology.Compactness.Nonvanishing
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Tactic.Linarith

open Set Metric

namespace Topology.IsInducing

variable {X M F : Type*} [TopologicalSpace X] [TopologicalSpace M]
  [PseudoMetricSpace F] {e : M → F}

theorem exists_uniform_dist_mem_of_isCompact (he : IsInducing e)
    {K V : Set M} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, dist (e y) (e x) < δ → y ∈ V := by
  obtain ⟨U, hU, hUV⟩ := he.isOpen_iff.mp hV
  have hKU : e '' K ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    have hxV := hKV hx
    rwa [← hUV] at hxV
  obtain ⟨δ, hδ, hδU⟩ := (hK.image he.continuous).exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, fun x hx y hxy => ?_⟩
  rw [← hUV]
  exact hδU (mem_thickening_iff.mpr ⟨e x, ⟨x, hx, rfl⟩, hxy⟩)

theorem exists_uniform_dist_mem_of_continuousOn (he : IsInducing e)
    {f : X → M} {K : Set X} {V : Set M} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hV : IsOpen V) (hfV : MapsTo f K V) :
    ∃ δ > 0, ∀ x ∈ K, ∀ y, dist (e y) (e (f x)) < δ → y ∈ V := by
  obtain ⟨δ, hδ, hδV⟩ := he.exists_uniform_dist_mem_of_isCompact
    (hK.image_of_continuousOn hf) hV hfV.image_subset
  exact ⟨δ, hδ, fun x hx y hy => hδV (f x) ⟨x, hx, rfl⟩ y hy⟩

theorem exists_uniform_dist_mem_finite_of_continuousOn (he : IsInducing e)
    {ι : Type*} [Finite ι] {f : X → M} {K : ι → Set X} {V : ι → Set M}
    (hK : ∀ i, IsCompact (K i)) (hf : ∀ i, ContinuousOn f (K i))
    (hV : ∀ i, IsOpen (V i)) (hfV : ∀ i, MapsTo f (K i) (V i)) :
    ∃ δ > 0, ∀ i, ∀ x ∈ K i, ∀ y, dist (e y) (e (f x)) < δ → y ∈ V i := by
  choose δ hδ hδV using fun i =>
    he.exists_uniform_dist_mem_of_continuousOn (hK i) (hf i) (hV i) (hfV i)
  obtain ⟨ε, hε, hεδ⟩ := Pi.exists_forall_pos_add_lt hδ
  refine ⟨ε, hε, fun i x hx y hy => hδV i x hx y (hy.trans ?_)⟩
  simpa only [zero_add] using hεδ i

end Topology.IsInducing

open Set

namespace DifferentialGeometry.Topology

theorem exists_pos_coincidence_subset_of_isCompact
    {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
    {K W : Set X} {f g : X → Y} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hW : IsOpen W)
    (hcover : ∀ x ∈ K, f x = g x → x ∈ W) :
    ∃ ε > 0, ∀ f' g' : X → Y,
      (∀ x ∈ K, dist (f' x) (f x) < ε) →
      (∀ x ∈ K, dist (g' x) (g x) < ε) →
      ∀ x ∈ K, f' x = g' x → x ∈ W := by
  have hdist : ContinuousOn (fun x => dist (f x) (g x)) K :=
    fun x hx => (hf x hx).dist (hg x hx)
  obtain ⟨δ, hδ, hbound⟩ := exists_pos_lt_norm_of_isCompact
    (f := fun x => dist (f x) (g x)) (hK.diff hW)
    (hdist.mono sdiff_subset) (fun x hx =>
      dist_ne_zero.mpr (fun heq => hx.2 (hcover x hx.1 heq)))
  refine ⟨δ / 3, by linarith, ?_⟩
  intro f' g' hf' hg' x hx heq
  by_contra hxW
  have hsep : δ < dist (f x) (g x) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using hbound x ⟨hx, hxW⟩
  have htri : dist (f x) (g x) ≤ dist (f' x) (f x) + dist (g' x) (g x) := by
    calc
      dist (f x) (g x) ≤ dist (f x) (f' x) + dist (f' x) (g x) :=
        dist_triangle _ _ _
      _ = dist (f' x) (f x) + dist (g' x) (g x) := by
        rw [dist_comm (f x) (f' x), heq]
  linarith [hf' x hx, hg' x hx]

theorem exists_pos_coincidence_subset_of_norm_sub_lt
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {K W : Set X} {f g : X → E} (hK : IsCompact K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hW : IsOpen W)
    (hcover : ∀ x ∈ K, f x = g x → x ∈ W) :
    ∃ ε > 0, ∀ f' g' : X → E,
      (∀ x ∈ K, ‖f' x - f x‖ < ε) →
      (∀ x ∈ K, ‖g' x - g x‖ < ε) →
      ∀ x ∈ K, f' x = g' x → x ∈ W := by
  simpa only [dist_eq_norm] using
    exists_pos_coincidence_subset_of_isCompact hK hf hg hW hcover

end DifferentialGeometry.Topology

open Set

namespace DifferentialGeometry.Topology

theorem exists_pos_coincidence_subset_of_comp_injective
    {P Q M F : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    [TopologicalSpace M] [NormedAddCommGroup F]
    {K W : Set Q} (hK : IsCompact K) (hW : IsOpen W)
    {γ : P → M} {e : M → F} (hγ : Continuous γ) (he : Continuous e)
    (hei : Function.Injective e) {l r : Q → P} (hl : Continuous l) (hr : Continuous r)
    (hcover : ∀ q ∈ K, γ (l q) = γ (r q) → q ∈ W) :
    ∃ ε > 0, ∀ β : P → M,
      (∀ p ∈ (l '' K) ∪ (r '' K), ‖e (β p) - e (γ p)‖ < ε) →
      ∀ q ∈ K, β (l q) = β (r q) → q ∈ W := by
  obtain ⟨ε, hε, hstable⟩ :=
    DifferentialGeometry.Topology.exists_pos_coincidence_subset_of_norm_sub_lt hK
      (he.comp (hγ.comp hl)).continuousOn (he.comp (hγ.comp hr)).continuousOn hW
      (fun q hq heq => hcover q hq (hei heq))
  refine ⟨ε, hε, ?_⟩
  intro β hβ q hq heq
  exact hstable (fun q => e (β (l q))) (fun q => e (β (r q)))
    (fun q hq => hβ (l q) (Or.inl ⟨q, hq, rfl⟩))
    (fun q hq => hβ (r q) (Or.inr ⟨q, hq, rfl⟩)) q hq (congrArg e heq)

end DifferentialGeometry.Topology
