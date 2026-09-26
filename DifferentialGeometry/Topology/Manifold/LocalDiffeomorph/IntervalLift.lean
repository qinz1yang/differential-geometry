import DifferentialGeometry.Topology.FirstExit
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import DifferentialGeometry.Topology.Manifold.OpenTarget
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace G Y]

theorem exists_contMDiff_interval_lift_of_injective_localDiffeomorph
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (γ : ℝ → Y) (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) {a b : ℝ} (hab : a < b)
    (hstay : MapsTo γ (Icc a b) (range f)) :
    ∃ β : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧ EqOn (f ∘ β) γ (Icc a b) := by
  let U := hf.image
  let e := diffeomorphOntoImage f hf hinj
  obtain ⟨ρ, lo, hi, hlo, hhi, hρ, hρid, _, hρrange⟩ :=
    DifferentialGeometry.exists_smooth_time_clamp_range_subset
      (U.isOpen.preimage hγ.continuous) hab hstay
  let η : ℝ → U := fun t => ⟨γ (ρ t), hρrange t⟩
  have hη : ContMDiff 𝓘(ℝ, ℝ) J 1 η := by
    apply (DifferentialGeometry.Topology.contMDiff_subtypeVal_comp_iff (n := 1) U η).mp
    exact hγ.comp (hρ.contMDiff.of_le (by norm_num))
  refine ⟨e.symm ∘ η, (e.symm.contMDiff.of_le (by norm_num)).comp hη, ?_⟩
  intro t ht
  change f (e.symm (η t)) = γ t
  rw [show f (e.symm (η t)) = (η t).val from diffeomorphOntoImage_symm_apply f hf hinj (η t)]
  change γ (ρ t) = γ t
  rw [hρid ⟨hlo.le.trans ht.1, ht.2.trans hhi.le⟩]
  rfl

end DifferentialGeometry.Topology.Manifold

end

section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace G Y]

theorem exists_contMDiff_first_exit_lift_of_closed_image
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (K : Set X) (hK : IsClosed (f '' K))
    (γ : ℝ → Y) (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) {a b : ℝ}
    (haK : γ a ∈ f '' K) (hexit : ¬ MapsTo γ (Icc a b) (f '' K)) :
    ∃ (t : ℝ) (β : ℝ → X), t ∈ Ico a b ∧ ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧
      EqOn (f ∘ β) γ (Icc a t) ∧ MapsTo β (Icc a t) K ∧
      MapsTo β (Ico a t) (interior K) ∧ β t ∈ frontier K ∧
      (γ a ∈ f '' interior K → a < t) := by
  obtain ⟨t, ht, hstay, hbefore, hfront, hstrict⟩ :=
    DifferentialGeometry.exists_first_exit_frontier_Icc_of_mem_of_not_mapsTo hK
      hγ.continuous.continuousOn haK hexit
  have hlift : ∃ β : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧ EqOn (f ∘ β) γ (Icc a t) := by
    rcases ht.1.lt_or_eq with hlt | heq
    · exact exists_contMDiff_interval_lift_of_injective_localDiffeomorph f hf hinj γ hγ hlt
        (fun s hs => image_subset_range f K (hstay hs))
    · obtain ⟨x, _, hx⟩ := haK
      refine ⟨fun _ => x, contMDiff_const, ?_⟩
      intro s hs
      have hsa : s = a := le_antisymm (hs.2.trans_eq heq.symm) hs.1
      simpa only [Function.comp_apply, hsa] using hx
  obtain ⟨β, hβ, hβeq⟩ := hlift
  have hpreint : f ⁻¹' interior (f '' K) = interior K := by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.contMDiff.continuous,
      Set.preimage_image_eq K hinj]
  have hprefront : f ⁻¹' frontier (f '' K) = frontier K := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.contMDiff.continuous,
      Set.preimage_image_eq K hinj]
  refine ⟨t, β, ht, hβ, hβeq, ?_, ?_, ?_, ?_⟩
  · intro s hs
    have hmem : β s ∈ f ⁻¹' (f '' K) := by
      change (f ∘ β) s ∈ f '' K
      rw [hβeq hs]
      exact hstay hs
    simpa only [Set.preimage_image_eq K hinj] using hmem
  · intro s hs
    rw [← hpreint]
    change (f ∘ β) s ∈ interior (f '' K)
    rw [hβeq ⟨hs.1, hs.2.le⟩]
    exact hbefore hs
  · rw [← hprefront]
    change (f ∘ β) t ∈ frontier (f '' K)
    rw [hβeq ⟨ht.1, le_rfl⟩]
    exact hfront
  · exact fun ha => hstrict (hf.isOpenMap.image_interior_subset K ha)

theorem exists_contMDiff_first_exit_lift_of_compact [T2Space Y]
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Function.Injective f)
    (K : Set X) (hK : IsCompact K)
    (γ : ℝ → Y) (hγ : ContMDiff 𝓘(ℝ, ℝ) J 1 γ) {a b : ℝ}
    (haK : γ a ∈ f '' K) (hexit : ¬ MapsTo γ (Icc a b) (f '' K)) :
    ∃ (t : ℝ) (β : ℝ → X), t ∈ Ico a b ∧ ContMDiff 𝓘(ℝ, ℝ) I 1 β ∧
      EqOn (f ∘ β) γ (Icc a t) ∧ MapsTo β (Icc a t) K ∧
      MapsTo β (Ico a t) (interior K) ∧ β t ∈ frontier K ∧
      (γ a ∈ f '' interior K → a < t) :=
  exists_contMDiff_first_exit_lift_of_closed_image f hf hinj K
    (hK.image hf.contMDiff.continuous).isClosed γ hγ haK hexit

end DifferentialGeometry.Topology.Manifold

end

noncomputable section
open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology Uniformity
namespace DifferentialGeometry.Topology.Manifold
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [UniformSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_contMDiffOn_lifts_tendstoUniformly_on_interval
    (U : Opens M) {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    {a b : ℝ} (hab : a ≤ b) (α : ℕ → ℝ → M)
    (hα : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (α n) (Icc a b))
    (hKα : ∀ n, MapsTo (α n) (Icc a b) K)
    (γ : ℝ → M)
    (hconv : TendstoUniformly (fun n (r : Icc a b) => α n r.val) (fun r => γ r.val) atTop) :
    ∃ (β : ℕ → ℝ → U) (γU : ℝ → U),
      (∀ n, ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β n) (Icc a b)) ∧ Continuous γU ∧
      (∀ n, EqOn (fun r => (β n r).val) (α n) (Icc a b)) ∧
      EqOn (fun r => (γU r).val) γ (Icc a b) ∧
      (∀ n, MapsTo (β n) (Icc a b) ((Subtype.val : U → M) ⁻¹' K)) ∧
      MapsTo γU (Icc a b) ((Subtype.val : U → M) ⁻¹' K) ∧
      IsCompact ((Subtype.val : U → M) ⁻¹' K) ∧
      TendstoUniformly (fun n (r : Icc a b) => β n r.val) (fun r => γU r.val) atTop := by
  have hγ : ContinuousOn γ (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hconv.continuous (Eventually.of_forall fun n => (hα n).continuousOn.domRestrict).frequently
  have hγK : MapsTo γ (Icc a b) K := by
    intro r hr
    exact hK.isClosed.mem_of_tendsto (hconv.tendsto_at ⟨r, hr⟩)
      (Eventually.of_forall fun n => hKα n hr)
  let βI : ℕ → Icc a b → U := fun n r => ⟨α n r.val, hKU (hKα n r.property)⟩
  let β : ℕ → ℝ → U := fun n => IccExtend hab (βI n)
  have hβeq (n : ℕ) : EqOn (fun r => (β n r).val) (α n) (Icc a b) := by
    intro r hr
    exact congrArg Subtype.val (IccExtend_of_mem hab (βI n) hr)
  have hβC1 (n : ℕ) : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (β n) (Icc a b) := by
    intro r hr
    apply (DifferentialGeometry.Topology.contMDiffWithinAt_subtypeVal_comp_iff U (β n) (Icc a b) r).mp
    exact (hα n r hr).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin (fun t ht => hβeq n ht))
      (hβeq n hr)
  let γI : Icc a b → U := fun r => ⟨γ r.val, hKU (hγK r.property)⟩
  have hγI : Continuous γI := hγ.domRestrict.subtype_mk _
  let γU : ℝ → U := IccExtend hab γI
  have hγU : Continuous γU := (continuous_IccExtend_iff (h := hab)).mpr hγI
  have hγeq : EqOn (fun r => (γU r).val) γ (Icc a b) := by
    intro r hr
    exact congrArg Subtype.val (IccExtend_of_mem hab γI hr)
  have hβK (n : ℕ) : MapsTo (β n) (Icc a b) ((Subtype.val : U → M) ⁻¹' K) := by
    intro r hr
    change (β n r).val ∈ K
    have he : (β n r).val = α n r := hβeq n hr
    rw [he]
    exact hKα n hr
  have hγUK : MapsTo γU (Icc a b) ((Subtype.val : U → M) ⁻¹' K) := by
    intro r hr
    change (γU r).val ∈ K
    have he : (γU r).val = γ r := hγeq hr
    rw [he]
    exact hγK hr
  have hpre : IsCompact ((Subtype.val : U → M) ⁻¹' K) :=
    U.isOpen.isOpenEmbedding_subtypeVal.isEmbedding.isInducing.isCompact_preimage' hK
      (fun x hx => ⟨⟨x, hKU hx⟩, rfl⟩)
  refine ⟨β, γU, hβC1, hγU, hβeq, hγeq, hβK, hγUK, hpre, ?_⟩
  intro V hV
  change V ∈ Filter.comap (fun p : U × U => (p.1.val, p.2.val)) (𝓤 M) at hV
  obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
  filter_upwards [hconv W hW] with n hn
  intro r
  apply hWV
  change ((γU r.val).val, (β n r.val).val) ∈ W
  simpa only [hγeq r.property, hβeq n r.property] using hn r

end DifferentialGeometry.Topology.Manifold

end
