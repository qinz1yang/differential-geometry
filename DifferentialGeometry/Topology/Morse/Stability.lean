import DifferentialGeometry.Topology.Morse.Naturality
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.Compact

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem eventually_isNondegenerateCriticalPointAt_model
    {f : P → E → ℝ} {a : P} {x : E}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (a, x))
    (ha : IsCriticalPointAt 𝓘(ℝ, E) (f a) x →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (f a) x) :
    ∀ᶠ p : P × E in 𝓝 (a, x), IsCriticalPointAt 𝓘(ℝ, E) (f p.1) p.2 →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (f p.1) p.2 := by
  have hgrad : ContDiffAt ℝ 1 (fun p : P × E => fderiv ℝ (f p.1) p.2) (a, x) := by
    have hbase : ContDiffAt ℝ 2 (fun q : (P × E) × E => f q.1.1 q.2) ((a, x), x) :=
      hf.comp ((a, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact hbase.fderiv contDiffAt_snd (by norm_num)
  have hhess : ContDiffAt ℝ 0
      (fun p : P × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2) (a, x) := by
    have hbase : ContDiffAt ℝ 1 (fun q : (P × E) × E => fderiv ℝ (f q.1.1) q.2)
        ((a, x), x) :=
      hgrad.comp ((a, x), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact hbase.fderiv contDiffAt_snd (by norm_num)
  by_cases hzero : fderiv ℝ (f a) x = 0
  · have hcrit : IsCriticalPointAt 𝓘(ℝ, E) (f a) x := by
      unfold IsCriticalPointAt
      rw [mfderiv_eq_fderiv]
      exact hzero
    have hfa : ContDiffAt ℝ 2 (f a) x :=
      hf.comp x (contDiffAt_const.prodMk contDiffAt_id)
    have hinj := ((isNondegenerateCriticalPointAt_model_iff hfa).mp (ha hcrit)).2
    have hev := hhess.continuousAt.preimage_mem_nhds
      (ContinuousLinearMap.isOpen_injective.mem_nhds hinj)
    have hreg : ∀ᶠ p : P × E in 𝓝 (a, x), ContDiffAt ℝ 2 (Function.uncurry f) p :=
      hf.eventually (by norm_num)
    filter_upwards [hev, hreg] with p hp hfp hcp
    have hfp' : ContDiffAt ℝ 2 (Function.uncurry f) (p.1, p.2) := hfp
    have hfpx : ContDiffAt ℝ 2 (f p.1) p.2 :=
      hfp'.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
    apply (isNondegenerateCriticalPointAt_model_iff hfpx).mpr
    refine ⟨?_, hp⟩
    unfold IsCriticalPointAt at hcp
    rw [mfderiv_eq_fderiv] at hcp
    exact hcp
  · filter_upwards [hgrad.continuousAt.eventually_ne hzero] with p hp hcp
    apply False.elim
    apply hp
    unfold IsCriticalPointAt at hcp
    rw [mfderiv_eq_fderiv] at hcp
    exact hcp

variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

theorem eventually_isNondegenerateCriticalPointAt_on_isCompact
    {f : P → M → ℝ} {K : Set M} (hK : IsCompact K) {a : P}
    (hf : ∀ x ∈ K, ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 2
      (Function.uncurry f) (a, x))
    (ha : ∀ x ∈ K, IsCriticalPointAt I (f a) x →
      IsNondegenerateCriticalPointAt I (f a) x) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ K, IsCriticalPointAt I (f b) x →
      IsNondegenerateCriticalPointAt I (f b) x := by
  let : IsManifold I 1 M := IsManifold.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  have hslice : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f a) x :=
    (hf x hx).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
  let e := extChartAt I x
  have hxs : x ∈ e.source := mem_extChartAt_source x
  have hxt : e x ∈ e.target := e.map_source hxs
  have hes : ContMDiffAt 𝓘(ℝ, E) I 2 e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hxt)
  let g : P → E → ℝ := fun b y => f b (e.symm y)
  have hg : ContDiffAt ℝ 2 (Function.uncurry g) (a, e x) := by
    have hfst : ContMDiffAt 𝓘(ℝ, P × E) 𝓘(ℝ, P) 2
        (Prod.fst : P × E → P) (a, e x) := contDiffAt_fst.contMDiffAt
    have hsnd : ContMDiffAt 𝓘(ℝ, P × E) I 2
        (fun p : P × E => e.symm p.2) (a, e x) :=
      hes.comp (a, e x) contDiffAt_snd.contMDiffAt
    have hfa : ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 2
        (Function.uncurry f) (a, e.symm (e x)) := by
      simpa only [e.left_inv hxs] using hf x hx
    exact (hfa.comp (a, e x) (hfst.prodMk hsnd)).contDiffAt
  have hga : IsCriticalPointAt 𝓘(ℝ, E) (g a) (e x) →
      IsNondegenerateCriticalPointAt 𝓘(ℝ, E) (g a) (e x) := by
    intro hcrit
    have hc : IsCriticalPointAt I (f a) x :=
      (isCriticalPointAt_iff_fixed_chart (hslice.mdifferentiableAt
        (by norm_num)) hxs).mpr hcrit
    exact (isNondegenerateCriticalPointAt_iff_fixed_chart hslice hxs).mp
      (ha x hx hc)
  have hstable := eventually_isNondegenerateCriticalPointAt_model hg hga
  have hec : ContinuousAt e x :=
    (continuousOn_extChartAt x).continuousAt ((isOpen_extChartAt_source x).mem_nhds hxs)
  have hmap : ContinuousAt (fun p : P × M => (p.1, e p.2)) (a, x) :=
    continuousAt_fst.prodMk (hec.comp continuousAt_snd)
  have hsource : ∀ᶠ p : P × M in 𝓝 (a, x), p.2 ∈ e.source :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_source x).mem_nhds hxs)
  have hreg : ∀ᶠ p : P × M in 𝓝 (a, x),
      ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 2 (Function.uncurry f) p :=
    (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp (hf x hx)
  filter_upwards [hmap.preimage_mem_nhds hstable, hsource, hreg] with p hp hps hfp hcrit
  have hfp' : ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 2
      (Function.uncurry f) (p.1, p.2) := hfp
  have hsp : ContMDiffAt I 𝓘(ℝ, ℝ) 2 (f p.1) p.2 :=
    hfp'.comp p.2 (contMDiffAt_const.prodMk contMDiffAt_id)
  apply (isNondegenerateCriticalPointAt_iff_fixed_chart hsp hps).mpr
  apply hp
  exact (isCriticalPointAt_iff_fixed_chart (hsp.mdifferentiableAt (by norm_num)) hps).mp hcrit

theorem isOpen_parameters_isNondegenerateCriticalPointAt_on_isCompact
    {f : P → M → ℝ} (hf : ContMDiff ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 2
      (Function.uncurry f)) {K : Set M} (hK : IsCompact K) :
    IsOpen {a : P | ∀ x ∈ K,
      IsCriticalPointAt I (f a) x → IsNondegenerateCriticalPointAt I (f a) x} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  exact eventually_isNondegenerateCriticalPointAt_on_isCompact hK
    (fun _ _ => hf.contMDiffAt) ha

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
theorem eventually_not_isCriticalPointAt_on_isCompact [IsManifold I 1 M]
    {f : P → M → ℝ} {K : Set M} (hK : IsCompact K) {a : P}
    (hf : ∀ x ∈ K, ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 1
      (Function.uncurry f) (a, x))
    (ha : ∀ x ∈ K, ¬ IsCriticalPointAt I (f a) x) :
    ∀ᶠ b in 𝓝 a, ∀ x ∈ K, ¬ IsCriticalPointAt I (f b) x := by
  apply hK.eventually_forall_of_forall_eventually
  intro x hx
  let e := extChartAt I x
  have hxs : x ∈ e.source := mem_extChartAt_source x
  have hxt : e x ∈ e.target := e.map_source hxs
  have hes : ContMDiffAt 𝓘(ℝ, E) I 1 e.symm (e x) :=
    (contMDiffOn_extChartAt_symm x).contMDiffAt ((isOpen_extChartAt_target x).mem_nhds hxt)
  let g : P → E → ℝ := fun b y => f b (e.symm y)
  have hg : ContDiffAt ℝ 1 (Function.uncurry g) (a, e x) := by
    have hfst : ContMDiffAt 𝓘(ℝ, P × E) 𝓘(ℝ, P) 1
        (Prod.fst : P × E → P) (a, e x) := contDiffAt_fst.contMDiffAt
    have hsnd : ContMDiffAt 𝓘(ℝ, P × E) I 1
        (fun p : P × E => e.symm p.2) (a, e x) :=
      hes.comp (a, e x) contDiffAt_snd.contMDiffAt
    have hf' : ContMDiffAt ((𝓘(ℝ, P)).prod I) 𝓘(ℝ, ℝ) 1
        (Function.uncurry f) (a, e.symm (e x)) := by
      simpa only [e.left_inv hxs] using hf x hx
    exact hf'.comp (a, e x) (hfst.prodMk hsnd) |>.contDiffAt
  have hgrad : ContDiffAt ℝ 0
      (fun p : P × E => fderiv ℝ (g p.1) p.2) (a, e x) := by
    have hbase : ContDiffAt ℝ 1 (fun q : (P × E) × E => g q.1.1 q.2)
        ((a, e x), e x) :=
      hg.comp ((a, e x), e x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact hbase.fderiv contDiffAt_snd (by norm_num)
  have hga : fderiv ℝ (g a) (e x) ≠ 0 := by
    intro hz
    apply ha x hx
    have hfa : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (f a) x :=
      (hf x hx).comp x (contMDiffAt_const.prodMk contMDiffAt_id)
    apply (isCriticalPointAt_iff_fixed_chart (hfa.mdifferentiableAt (by norm_num)) hxs).mpr
    unfold IsCriticalPointAt
    rw [mfderiv_eq_fderiv]
    exact hz
  have hne : ∀ᶠ p : P × E in 𝓝 (a, e x),
      fderiv ℝ (g p.1) p.2 ≠ 0 :=
    hgrad.continuousAt.eventually_ne hga
  have hec : ContinuousAt e x := (continuousOn_extChartAt x).continuousAt
    ((isOpen_extChartAt_source x).mem_nhds hxs)
  have hmap : ContinuousAt (fun p : P × M => (p.1, e p.2)) (a, x) :=
    continuousAt_fst.prodMk (hec.comp continuousAt_snd)
  have hsource : ∀ᶠ p : P × M in 𝓝 (a, x), p.2 ∈ e.source :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_source x).mem_nhds hxs)
  have hreg := hg.eventually (by norm_num)
  filter_upwards [hmap.preimage_mem_nhds hne, hsource,
    hmap.preimage_mem_nhds hreg] with p hp hps hgp hcrit
  have hgp' : ContDiffAt ℝ 1 (Function.uncurry g) (p.1, e p.2) := hgp
  have hgslice : ContDiffAt ℝ 1 (g p.1) (e p.2) :=
    hgp'.comp (e p.2) (contDiffAt_const.prodMk contDiffAt_id)
  have he : ContMDiffAt I 𝓘(ℝ, E) 1 e p.2 :=
    contMDiffAt_extChartAt' (by simpa only [e, extChartAt_source] using hps)
  have heq : f p.1 =ᶠ[𝓝 p.2] (g p.1 ∘ e) :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_source x).mem_nhds hps)
      (fun y hy => congrArg (f p.1) (e.left_inv hy).symm)
  have hfslice : ContMDiffAt I 𝓘(ℝ, ℝ) 1 (f p.1) p.2 :=
    (hgslice.contMDiffAt.comp p.2 he).congr_of_eventuallyEq heq
  apply hp
  have hc := (isCriticalPointAt_iff_fixed_chart (hfslice.mdifferentiableAt (by norm_num)) hps).mp hcrit
  unfold IsCriticalPointAt at hc
  rw [mfderiv_eq_fderiv] at hc
  exact hc

end DifferentialGeometry.Topology.Morse
