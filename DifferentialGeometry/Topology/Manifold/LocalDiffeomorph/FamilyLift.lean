import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Mathlib.Topology.MetricSpace.Pseudo.Defs

noncomputable section
namespace DifferentialGeometry.Topology.Manifold
open Set Bundle Filter
open scoped _root_.Manifold ContDiff _root_.Topology
variable {A E F H G X Y : Type*}
 [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
 [TopologicalSpace H] [TopologicalSpace G]
 {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
 [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
 [TopologicalSpace Y] [ChartedSpace G Y] [IsManifold J ∞ Y]

omit [IsManifold I ∞ X] [IsManifold J ∞ Y] in
theorem exists_contMDiff_family_lift_near
    (f : X → Y) {x0 : X} (hf : IsLocalDiffeomorphAt I J ∞ f x0)
    {α : A × ℝ → Y} {V : Set A} {K : Set ℝ} {a0 : A} {t0 : ℝ}
    (hV : IsOpen V) (hK : IsOpen K) (ha0 : a0 ∈ V) (ht0 : t0 ∈ K)
    (hα : ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) J ∞ α (V ×ˢ K))
    (hpoint : α (a0, t0) = f x0) :
    ∃ U : Set A, IsOpen U ∧ a0 ∈ U ∧ U ⊆ V ∧
      ∃ ε : ℝ, 0 < ε ∧ Ioo (t0 - ε) (t0 + ε) ⊆ K ∧
        ∃ β : A × ℝ → X,
          ContMDiffOn (𝓘(ℝ, A).prod 𝓘(ℝ, ℝ)) I ∞ β (U ×ˢ Ioo (t0 - ε) (t0 + ε)) ∧
          EqOn (f ∘ β) α (U ×ˢ Ioo (t0 - ε) (t0 + ε)) ∧
          β (a0, t0) = x0 := by
  have hp : (a0, t0) ∈ V ×ˢ K := ⟨ha0, ht0⟩
  have hnear : α ⁻¹' hf.localInverse.source ∩ (V ×ˢ K) ∈ 𝓝 (a0, t0) := by
    exact inter_mem (((hα _ hp).contMDiffAt ((hV.prod hK).mem_nhds hp)).continuousAt.preimage_mem_nhds
      (hf.localInverse_open_source.mem_nhds (hpoint ▸ hf.localInverse_mem_source))) ((hV.prod hK).mem_nhds hp)
  obtain ⟨U, hU, L, hL, hUL⟩ := mem_nhds_prod_iff.mp hnear
  obtain ⟨U', hU'sub, hU'open, haU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨ε, hε, hεL⟩ := Metric.mem_nhds_iff.mp hL
  have hI (r : ℝ) (hr : r ∈ Ioo (t0 - ε) (t0 + ε)) : r ∈ L := by
    apply hεL
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hdom (p : A × ℝ) (hp : p ∈ U' ×ˢ Ioo (t0 - ε) (t0 + ε)) :
      α p ∈ hf.localInverse.source ∧ p ∈ V ×ˢ K :=
    hUL ⟨hU'sub hp.1, hI p.2 hp.2⟩
  have htI : t0 ∈ Ioo (t0 - ε) (t0 + ε) := ⟨by linarith, by linarith⟩
  let β := hf.localInverse ∘ α
  refine ⟨U', hU'open, haU', (fun a ha => (hdom (a, t0) ⟨ha, htI⟩).2.1), ε, hε,
    (fun r hr => (hdom (a0, r) ⟨haU', hr⟩).2.2), β, ?_, ?_, ?_⟩
  · exact hf.contmdiffOn_localInverse.comp (hα.mono (fun p hp => (hdom p hp).2)) (fun p hp => (hdom p hp).1)
  · intro p hp
    exact hf.localInverse_right_inv (hdom p hp).1
  · change hf.localInverse (α (a0, t0)) = x0
    rw [hpoint]
    exact hf.localInverse_left_inv (by simpa [hpoint] using hf.localInverse_mem_target)

end DifferentialGeometry.Topology.Manifold
