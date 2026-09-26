import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.IntervalLift
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.ProjIcc
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuousPartition
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

noncomputable section
open Set Manifold TopologicalSpace
open scoped Manifold ContDiff
namespace DifferentialGeometry.Topology.Manifold

open Function

variable {E F H G X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]
  [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J 1 Y]

theorem exists_absolutelyContinuousOnInterval_lift_of_injective_localDiffeomorph
    (f : X → Y) (hf : IsLocalDiffeomorph I J ∞ f) (hinj : Injective f)
    (gamma : ℝ → Y) {a b : ℝ}
    (hgamma : _root_.Manifold.absolutelyContinuousOnInterval J gamma a b)
    (hstay : MapsTo gamma (uIcc a b) (range f)) :
    ∃ beta : ℝ → X, _root_.Manifold.absolutelyContinuousOnInterval I beta a b ∧
      EqOn (f ∘ beta) gamma (uIcc a b) := by
  let U := hf.image
  let e := diffeomorphOntoImage f hf hinj
  obtain ⟨eta, heta, heq⟩ := _root_.Manifold.exists_absolutelyContinuousOnInterval_openSubtype
    U hgamma hstay
  refine ⟨e.symm ∘ eta,
    _root_.Manifold.absolutelyContinuousOnInterval_comp_contMDiff heta
      (e.symm.contMDiff.of_le (by norm_num)), ?_⟩
  intro r hr
  exact (diffeomorphOntoImage_symm_apply f hf hinj (eta r)).trans (heq hr)

end DifferentialGeometry.Topology.Manifold

end
