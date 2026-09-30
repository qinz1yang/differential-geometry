import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff Manifold

namespace PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F EP H G HP M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace HP]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {IP : ModelWithCorners 𝕜 EP HP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

def patchMap (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N) (x : P) : M := by
  classical
  exact if f x ∈ e.source then e.symm (g x) else f x

theorem patchMap_of_mem (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x : P} (hx : f x ∈ e.source) : patchMap e f g x = e.symm (g x) :=
  ite_eq_left hx

theorem patchMap_of_not_mem (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x : P} (hx : f x ∉ e.source) : patchMap e f g x = f x :=
  ite_eq_right hx

theorem patchMap_eq_self (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x : P} (hx : g x = e (f x)) : patchMap e f g x = f x := by
  by_cases h : f x ∈ e.source
  · rw [patchMap_of_mem e f g h, hx]
    exact e.left_inv h
  · exact patchMap_of_not_mem e f g h

theorem patchMap_mem_source (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x : P} (hx : f x ∈ e.source) (hg : g x ∈ e.target) :
    patchMap e f g x ∈ e.source := by
  rw [patchMap_of_mem e f g hx]
  exact e.map_target hg

theorem apply_patchMap (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x : P} (hx : f x ∈ e.source) (hg : g x ∈ e.target) :
    e (patchMap e f g x) = g x := by
  rw [patchMap_of_mem e f g hx]
  exact e.right_inv hg

theorem patchMap_eq_iff (e : PartialDiffeomorph I J M N n) (f : P → M) (g : P → N)
    {x y : P} (hx : f x ∈ e.source) (hy : f y ∈ e.source)
    (hgx : g x ∈ e.target) (hgy : g y ∈ e.target) :
    patchMap e f g x = patchMap e f g y ↔ g x = g y := by
  constructor
  · intro h
    simpa only [apply_patchMap e f g hx hgx, apply_patchMap e f g hy hgy] using congrArg e h
  · intro h
    rw [patchMap_of_mem e f g hx, patchMap_of_mem e f g hy, h]

variable [TopologicalSpace P] [ChartedSpace HP P]

theorem contMDiffOn_patchMap (e : PartialDiffeomorph I J M N n)
    {f : P → M} {g : P → N} {S K : Set P}
    (hf : ContMDiffOn IP I n f S)
    (hg : ContMDiffOn IP J n g (S ∩ f ⁻¹' e.source))
    (hmap : MapsTo g (S ∩ f ⁻¹' e.source) e.target)
    (hK : IsClosed K) (hKsource : S ∩ K ⊆ f ⁻¹' e.source)
    (hagree : ∀ x ∈ S, x ∉ K → g x = e (f x)) :
    ContMDiffOn IP I n (patchMap e f g) S := by
  intro x hx
  by_cases hxs : f x ∈ e.source
  · have hnear : f ⁻¹' e.source ∈ 𝓝[S] x :=
      (hf x hx).continuousWithinAt (e.open_source.mem_nhds hxs)
    have hgx : ContMDiffWithinAt IP J n g S x :=
      (hg x ⟨hx, hxs⟩).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hnear)
    have hi := e.symm.contMDiffOn.contMDiffAt (e.open_target.mem_nhds (hmap ⟨hx, hxs⟩))
    apply (hi.comp_contMDiffWithinAt x hgx).congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [hnear] with y hy
    exact patchMap_of_mem e f g hy
  · have hxK : x ∉ K := fun h => hxs (hKsource ⟨hx, h⟩)
    apply (hf x hx).congr_of_eventuallyEq_of_mem _ hx
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (hK.isOpen_compl.mem_nhds hxK)] with y hy hyK
    exact patchMap_eq_self e f g (hagree y hy hyK)

end PartialDiffeomorph

namespace PartialDiffeomorph

variable {E F EP H HP M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  [TopologicalSpace H] [TopologicalSpace HP]
  {I : ModelWithCorners ℝ E H} {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace HP P] {n : ℕ∞ω}

theorem exists_pos_contMDiffOn_patchMap_bump
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F n)
    {f : P → M} {ρ : P → ℝ} {S : Set P}
    (hf : ContMDiffOn IP I n f S) (hρ : ContMDiffOn IP 𝓘(ℝ) n ρ S)
    (hcompact : IsCompact (S ∩ tsupport ρ)) (hsupport : S ∩ tsupport ρ ⊆ f ⁻¹' e.source)
    (hbound : ∀ x, ‖ρ x‖ ≤ 1) :
    ∃ δ > 0,
      ContMDiffOn (𝓘(ℝ, F).prod IP) I n
        (fun q : F × P => e.patchMap f (fun x => e (f x) - ρ x • q.1) q.2)
        (ball 0 δ ×ˢ S) ∧
      (∀ v : F, ‖v‖ < δ → ∀ x ∈ S, f x ∈ e.source →
        e (f x) - ρ x • v ∈ e.target) ∧
      (∀ v : F, ∀ x, x ∉ tsupport ρ →
        e.patchMap f (fun y => e (f y) - ρ y • v) x = f x) ∧
      (∀ x, e.patchMap f (fun y => e (f y) - ρ y • (0 : F)) x = f x) ∧
      ∀ v : F, ∀ x, ‖(e (f x) - ρ x • v) - e (f x)‖ ≤ ‖v‖ := by
  have hc : ContMDiffOn IP 𝓘(ℝ, F) n (fun x => e (f x)) (S ∩ f ⁻¹' e.source) :=
    e.contMDiffOn.comp (hf.mono inter_subset_left) inter_subset_right
  have hK : IsCompact ((fun x => e (f x)) '' (S ∩ tsupport ρ)) :=
    hcompact.image_of_continuousOn (hc.continuousOn.mono (fun _ h => ⟨h.1, hsupport h⟩))
  obtain ⟨δ, hδ, hδtarget⟩ := hK.exists_cthickening_subset_open e.open_target
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hsupport hx))
  have hsmall (v : F) (x : P) :
      ‖(e (f x) - ρ x • v) - e (f x)‖ ≤ ‖v‖ := by
    rw [sub_sub_cancel_left, norm_neg, norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg v) (hbound x)
  have hmap (v : F) (hv : ‖v‖ < δ) (x : P) (hx : x ∈ S)
      (hxf : f x ∈ e.source) : e (f x) - ρ x • v ∈ e.target := by
    by_cases hxK : x ∈ tsupport ρ
    · apply hδtarget
      apply mem_cthickening_of_dist_le _ (e (f x)) δ
        ((fun x => e (f x)) '' (S ∩ tsupport ρ)) ⟨x, ⟨hx, hxK⟩, rfl⟩
      simpa only [dist_eq_norm] using (hsmall v x).trans hv.le
    · rw [image_eq_zero_of_notMem_tsupport hxK, zero_smul, sub_zero]
      exact e.map_source hxf
  have hfixed (v : F) (x : P) (hx : x ∉ tsupport ρ) :
      e.patchMap f (fun y => e (f y) - ρ y • v) x = f x := by
    apply patchMap_eq_self
    rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, sub_zero]
  refine ⟨δ, hδ, ?_, hmap, hfixed, ?_, hsmall⟩
  · let T : Set (F × P) := ball 0 δ ×ˢ S
    let f' : F × P → M := fun q => f q.2
    let g' : F × P → F := fun q => e (f q.2) - ρ q.2 • q.1
    have hf' : ContMDiffOn (𝓘(ℝ, F).prod IP) I n f' T :=
      hf.comp contMDiffOn_snd (fun _ h => h.2)
    have hρ' : ContMDiffOn (𝓘(ℝ, F).prod IP) 𝓘(ℝ) n (fun q : F × P => ρ q.2) T :=
      hρ.comp contMDiffOn_snd (fun _ h => h.2)
    have hg' : ContMDiffOn (𝓘(ℝ, F).prod IP) 𝓘(ℝ, F) n g' (T ∩ f' ⁻¹' e.source) :=
      (e.contMDiffOn.comp (hf'.mono inter_subset_left) inter_subset_right).sub
        ((hρ'.mono inter_subset_left).smul contMDiffOn_fst)
    apply contMDiffOn_patchMap e hf' hg'
    · rintro q ⟨hq, hqf⟩
      exact hmap q.1 (by simpa only [mem_ball, dist_zero_right] using hq.1) q.2 hq.2 hqf
    · exact (isClosed_tsupport ρ).preimage continuous_snd
    · rintro q ⟨hq, hqK⟩
      exact hsupport ⟨hq.2, hqK⟩
    · intro q _ hqK
      change e (f q.2) - ρ q.2 • q.1 = e (f q.2)
      rw [image_eq_zero_of_notMem_tsupport hqK, zero_smul, sub_zero]
  · intro x
    apply patchMap_eq_self
    rw [smul_zero, sub_zero]

end PartialDiffeomorph

namespace DifferentialGeometry.Manifold

variable {E F EP H HP M P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
  [TopologicalSpace H] [TopologicalSpace HP]
  {I : ModelWithCorners ℝ E H} {IP : ModelWithCorners ℝ EP HP}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace HP P] [T2Space P] [IsManifold IP ∞ P]

theorem exists_contMDiffOn_chart_perturbation
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞)
    {f : P → M} {S B : Set P} (hf : ContMDiffOn IP I ∞ f S)
    (hS : IsClosed S) (hB : IsClosed B) {x₀ : P}
    (hx₀ : x₀ ∈ S) (hx₀B : x₀ ∉ B) (hchart : f x₀ ∈ e.source) :
    ∃ (ρ : P → ℝ) (δ : ℝ),
      ContMDiff IP 𝓘(ℝ) ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ x, ρ x ∈ Icc (0 : ℝ) 1) ∧ ρ =ᶠ[𝓝 x₀] 1 ∧
      (∀ x ∈ B, ρ x = 0) ∧
      S ∩ tsupport ρ ⊆ f ⁻¹' e.source ∧ 0 < δ ∧
      ContMDiffOn (𝓘(ℝ, F).prod IP) I ∞
        (fun q : F × P => e.patchMap f (fun x => e (f x) - ρ x • q.1) q.2)
        (ball 0 δ ×ˢ S) ∧
      (∀ v : F, ‖v‖ < δ → ∀ x ∈ S, f x ∈ e.source →
        e (f x) - ρ x • v ∈ e.target) ∧
      (∀ v : F, ∀ x, x ∉ tsupport ρ →
        e.patchMap f (fun y => e (f y) - ρ y • v) x = f x) ∧
      (∀ x, e.patchMap f (fun y => e (f y) - ρ y • (0 : F)) x = f x) ∧
      ∀ v : F, ∀ x, ‖(e (f x) - ρ x • v) - e (f x)‖ ≤ ‖v‖ := by
  have hnear : f ⁻¹' e.source ∈ 𝓝[S] x₀ :=
    (hf x₀ hx₀).continuousWithinAt (e.open_source.mem_nhds hchart)
  obtain ⟨V, hV, hxV, hVS⟩ := mem_nhdsWithin.mp hnear
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := IP) x₀).mem_iff.mp
    (inter_mem (hV.mem_nhds hxV) (hB.isOpen_compl.mem_nhds hx₀B))
  have hsupp : S ∩ tsupport φ ⊆ f ⁻¹' e.source := by
    intro x hx
    exact hVS ⟨(hφ hx.2).1, hx.1⟩
  obtain ⟨δ, hδ, hjoint, htarget, hfixed, hzero, hsmall⟩ :=
    e.exists_pos_contMDiffOn_patchMap_bump hf φ.contMDiff.contMDiffOn
      (φ.hasCompactSupport.inter_left hS) hsupp
      (fun x => by rw [Real.norm_of_nonneg φ.nonneg]; exact φ.le_one)
  refine ⟨φ, δ, φ.contMDiff, φ.hasCompactSupport,
    fun _ => ⟨φ.nonneg, φ.le_one⟩, φ.eventuallyEq_one, ?_, hsupp, hδ,
    hjoint, htarget, hfixed, hzero, hsmall⟩
  intro x hxB
  exact image_eq_zero_of_notMem_tsupport (fun h => (hφ h).2 hxB)

end DifferentialGeometry.Manifold

end
