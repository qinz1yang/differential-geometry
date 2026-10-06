import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Interior points of an arc in a curve are relative interior points (lane O-G6C, G2g)

`exists_open_nbhd_arc_subset_G6C`: let `B` be locally a topological curve near a point (an embedding
`s : ℝ → H` with `range s = B ∩ O`, `O` open) and `γ` a continuous arc, injective on `[0, 1]`, with
values in `B`. Then for `t ∈ (0, 1)` with `γ t ∈ O` some open `N ∋ γ t` has `N ∩ B ⊆ γ([0, 1])`
(1-dimensional invariance of domain: `s⁻¹ ∘ γ` is strictly monotone near `t`).
-/

set_option autoImplicit false

open Set Function Topology
open scoped Real

namespace DifferentialGeometry.Topology

/-- **Arc interior points are relative interior points of the arc in a curve.** -/
theorem exists_open_nbhd_arc_subset_G6C {H : Type*} [TopologicalSpace H] {B O : Set H}
    {s : ℝ → H} (hs : IsEmbedding s) (hO : IsOpen O) (hsr : range s = B ∩ O) {γ : ℝ → H}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1)) (hγB : γ '' Icc 0 1 ⊆ B)
    {t : ℝ} (ht : t ∈ Ioo 0 1) (htO : γ t ∈ O) :
    ∃ N : Set H, IsOpen N ∧ γ t ∈ N ∧ N ∩ B ⊆ γ '' Icc 0 1 := by
  -- a closed interval `[c, d] ∋ t` inside `(0, 1)` mapped into `O`
  have hγt : ContinuousAt γ t := hγc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hpre : γ ⁻¹' O ∩ Ioo 0 1 ∈ 𝓝 t :=
    Filter.inter_mem (hγt.preimage_mem_nhds (hO.mem_nhds htO)) (Ioo_mem_nhds ht.1 ht.2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  set c := t - δ / 2
  set d := t + δ / 2
  have hcd : c < d := by simp only [c, d]; linarith
  have hsub : Icc c d ⊆ γ ⁻¹' O ∩ Ioo 0 1 := by
    intro x hx
    apply hball
    have h1 : t - δ / 2 ≤ x := hx.1
    have h2 : x ≤ t + δ / 2 := hx.2
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hIcc : Icc c d ⊆ Icc 0 1 := fun x hx => Ioo_subset_Icc_self (hsub hx).2
  have hrange : ∀ x ∈ Icc c d, γ x ∈ range s := fun x hx => by
    rw [hsr]
    exact ⟨hγB ⟨x, hIcc hx, rfl⟩, (hsub hx).1⟩
  -- the parameter `g = s⁻¹ ∘ γ` on `[c, d]`
  classical
  let g : ℝ → ℝ := fun x => if h : γ x ∈ range s then Classical.choose h else 0
  have hg : ∀ x ∈ Icc c d, s (g x) = γ x := fun x hx => by
    simp only [g, hrange x hx, ↓reduceDIte]
    exact Classical.choose_spec (hrange x hx)
  have hgc : ContinuousOn g (Icc c d) :=
    hs.isInducing.continuousOn_iff.mpr ((hγc.mono hIcc).congr fun x hx => hg x hx)
  have hgi : InjOn g (Icc c d) := fun x hx x' hx' h =>
    hγi (hIcc hx) (hIcc hx') (by rw [← hg x hx, ← hg x' hx', h])
  -- `g` maps `(c, d)` onto an open interval around `g t`
  have htcd : t ∈ Ioo c d := by constructor <;> simp only [c, d] <;> linarith
  obtain ⟨V, hVo, hgtV, hVsub⟩ : ∃ V : Set ℝ, IsOpen V ∧ g t ∈ V ∧ V ⊆ g '' Icc c d := by
    rcases hgc.strictMonoOn_of_injOn_Icc' hcd.le hgi with hmono | hanti
    · refine ⟨Ioo (g c) (g d), isOpen_Ioo, ⟨hmono ⟨le_rfl, hcd.le⟩ ⟨htcd.1.le, htcd.2.le⟩ htcd.1,
        hmono ⟨htcd.1.le, htcd.2.le⟩ ⟨hcd.le, le_rfl⟩ htcd.2⟩, ?_⟩
      exact (intermediate_value_Ioo hcd.le hgc).trans (image_mono Ioo_subset_Icc_self)
    · refine ⟨Ioo (g d) (g c), isOpen_Ioo, ⟨hanti ⟨htcd.1.le, htcd.2.le⟩ ⟨hcd.le, le_rfl⟩ htcd.2,
        hanti ⟨le_rfl, hcd.le⟩ ⟨htcd.1.le, htcd.2.le⟩ htcd.1⟩, ?_⟩
      exact (intermediate_value_Ioo' hcd.le hgc).trans (image_mono Ioo_subset_Icc_self)
  -- transport by the embedding `s`
  obtain ⟨N', hN', hN'V⟩ := hs.isOpen_iff.mp hVo
  refine ⟨N' ∩ O, hN'.inter hO, ⟨?_, htO⟩, ?_⟩
  · have : g t ∈ s ⁻¹' N' := hN'V ▸ hgtV
    rw [← hg t ⟨htcd.1.le, htcd.2.le⟩]
    exact this
  · rintro z ⟨⟨hzN', hzO⟩, hzB⟩
    have hzr : z ∈ range s := by
      rw [hsr]
      exact ⟨hzB, hzO⟩
    obtain ⟨r, rfl⟩ := hzr
    have hrV : r ∈ V := hN'V ▸ (hzN' : r ∈ s ⁻¹' N')
    obtain ⟨x, hx, hxr⟩ := hVsub hrV
    exact ⟨x, hIcc hx, by rw [← hg x hx, hxr]⟩

end DifferentialGeometry.Topology
