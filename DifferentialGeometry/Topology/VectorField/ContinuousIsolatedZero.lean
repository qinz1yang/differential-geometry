import DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import DifferentialGeometry.Topology.VectorField.Transport

set_option autoImplicit false
open Bundle Filter Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ E H) [IsManifold I 1 M]

structure HasContinuousIsolatedZero (V : ∀ x : M, TangentSpace I x) (x : M) : Prop where
  zero : V x = 0
  continuous : ∃ s ∈ 𝓝 x,
    ContinuousOn (fun y => (⟨y, V y⟩ : TangentBundle I M)) s
  isolated : ∀ᶠ y in 𝓝 x, V y = 0 → y = x


theorem HasContinuousIsolatedZero.neg {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) : HasContinuousIsolatedZero I (-V) x where
  zero := by change -V x = 0; rw [hV.zero, neg_zero]
  continuous := by
    obtain ⟨s, hs, hc⟩ := hV.continuous
    refine ⟨s, hs, ?_⟩
    intro y hy
    apply (FiberBundle.continuousWithinAt_section E).mpr
    have hh := (FiberBundle.continuousWithinAt_section E).mp (hc y hy)
    let t := trivializationAt E (TangentSpace I (M := M)) y
    have hyt : y ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt' y
    have heq (z : M) (hz : z ∈ t.baseSet) :
        (t ⟨z, -V z⟩).2 = -(t ⟨z, V z⟩).2 := by
      rw [t.apply_eq_prod_continuousLinearEquivAt ℝ z hz,
        t.apply_eq_prod_continuousLinearEquivAt ℝ z hz]
      exact map_neg _ _
    apply hh.neg.congr_of_eventuallyEq
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (t.open_baseSet.mem_nhds hyt)] with z hz
      exact heq z hz
    · exact heq y hyt
  isolated := by
    filter_upwards [hV.isolated] with y hy
    exact fun hz => hy (neg_eq_zero.mp hz)

private theorem continuousOn_model_section {P : E → E} {s : Set E}
    (hc : ContinuousOn (fun y => (⟨y, P y⟩ : TangentBundle 𝓘(ℝ, E) E)) s) :
    ContinuousOn P s := by
  intro y hy
  have hh := (FiberBundle.continuousWithinAt_section E).mp (hc y hy)
  simpa only [trivializationAt_model_space_apply] using! hh

theorem HasContinuousIsolatedZero.model_pullback {n : ℕ∞ω}
    {V : ∀ x : M, TangentSpace I x}
    (f : PartialDiffeomorph 𝓘(ℝ, E) I E M n) (hn : 1 ≤ n)
    {a : E} (ha : a ∈ f.source) (hV : HasContinuousIsolatedZero I V (f a)) :
    Poincare.LocalDegree.isolatedZero (_root_.VectorField.mpullback 𝓘(ℝ, E) I f V) a := by
  obtain ⟨s, hs, hc⟩ := hV.continuous
  obtain ⟨U, hUs, hU, haU⟩ := mem_nhds_iff.mp hs
  let t : Set E := f.source ∩ f ⁻¹' U
  have ht : t ∈ 𝓝 a := inter_mem (f.open_source.mem_nhds ha)
    ((f.toOpenPartialHomeomorph.continuousAt ha).preimage_mem_nhds (hU.mem_nhds haU))
  have hP : ContinuousOn
      (fun y => (⟨y, _root_.VectorField.mpullback 𝓘(ℝ, E) I f V y⟩ :
        TangentBundle 𝓘(ℝ, E) E)) t := by
    intro y hy
    have hVy : ContMDiffAt I I.tangent 0
        (fun z => (⟨z, V z⟩ : TangentBundle I M)) (f y) :=
      (contMDiffOn_zero_iff.mpr (hc.mono hUs)).contMDiffAt (hU.mem_nhds hy.2)
    exact (contMDiffAt_mpullback_partialDiffeomorph f (by simpa using hn) hy.1 hVy).continuousAt.continuousWithinAt
  apply Poincare.LocalDegree.isolatedZero_of_nhds ht (continuousOn_model_section hP)
  · exact (mpullback_partialDiffeomorph_eq_zero_iff f
      (ne_of_gt (zero_lt_one.trans_le hn)) V ha).mpr hV.zero
  · apply eventually_nhdsWithin_iff.mpr
    have hi := (mpullback_partialDiffeomorph_isolated_iff f
      (ne_of_gt (zero_lt_one.trans_le hn)) V ha).mpr hV.isolated
    filter_upwards [hi] with y hy
    exact fun hne hz => hne (hy hz)

theorem HasContinuousIsolatedZero.in_coordinates
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : HasContinuousIsolatedZero I V x) {n : ℕ∞ω}
    (c : PartialDiffeomorph I 𝓘(ℝ, E) M E n) (hn : 1 ≤ n) (hx : x ∈ c.source) :
    Poincare.LocalDegree.isolatedZero
      (_root_.VectorField.mpullback 𝓘(ℝ, E) I c.symm V) (c x) := by
  apply HasContinuousIsolatedZero.model_pullback I c.symm hn (c.map_source hx)
  exact (c.left_inv hx).symm ▸ hV

end Poincare.VectorField
