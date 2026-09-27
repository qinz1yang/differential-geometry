/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CriticalFinite
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Order.Interval.Set.Infinite

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Morse

variable {M : Type*} [TopologicalSpace M]

theorem exists_radius_dist_finitePerturbation {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, Continuous (φ i)) (hc : ∀ i, HasCompactSupport (φ i))
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : Fin n → ℝ, ‖p‖ < δ → ∀ (f : M → ℝ) x,
      dist (finitePerturbation f φ p x) (f x) < ε x := by
  let C : Set M := ⋃ i, tsupport (φ i)
  have hC : IsCompact C := isCompact_iUnion hc
  have hJ := continuous_joint_finitePerturbation (f := fun _ : M => (0 : ℝ))
    continuous_const hφ
  have hnear : ∀ᶠ p : Fin n → ℝ in 𝓝 0, ∀ x ∈ C,
      ‖finitePerturbation (fun _ => 0) φ p x‖ < ε x := by
    apply hC.eventually_forall_of_forall_eventually
    intro x hx
    apply (isOpen_lt hJ.norm (hε.comp continuous_snd)).mem_nhds
    change ‖finitePerturbation (fun _ => 0) φ 0 x‖ < ε x
    simpa only [finitePerturbation_zero, norm_zero] using hεpos x
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, fun p hp f x => ?_⟩
  by_cases hxC : x ∈ C
  · have hb := hball (show p ∈ Metric.ball 0 δ by
        simpa only [Metric.mem_ball, dist_zero_right] using hp) x hxC
    simpa only [finitePerturbation, zero_add, dist_eq_norm, add_sub_cancel_left] using hb
  · have hz : ∀ i, φ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hxC (mem_iUnion.mpr ⟨i, hi⟩))
    simpa [finitePerturbation, hz] using hεpos x

section Manifold

open DifferentialGeometry.Topology.Morse

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]

theorem finite_criticalPoints_inter_of_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ K, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    {x : M | x ∈ K ∧ IsCriticalPointAt I f x}.Finite := by
  classical
  have hlocal : ∀ x : K, ∃ V : Set M, IsOpen V ∧ x.val ∈ V ∧
      ∀ y ∈ V, IsCriticalPointAt I f y → y = x.val := by
    intro x
    by_cases hx : IsCriticalPointAt I f x
    · exact exists_open_isolated_criticalPoint hf (hKI x x.property) (hnd x x.property hx)
    · obtain ⟨V, hV, hxV, hreg⟩ := exists_open_noncriticalPoint hf (hKI x x.property) hx
      exact ⟨V, hV, hxV, fun y hy hc => (hreg y hy hc).elim⟩
  choose V hV hxV hprop using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  apply (s.finite_toSet.image (fun x : K => x.val)).subset
  intro y hy
  obtain ⟨x, hxs, hyV⟩ := mem_iUnion₂.mp (hs hy.1)
  exact ⟨x, hxs, (hprop x y hyV hy.2).symm⟩

theorem exists_regular_level_on_isCompact_between {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ K, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    {a b : ℝ} (hab : a < b) :
    ∃ c ∈ Ioo a b, ∀ x ∈ K, f x = c → ¬ IsCriticalPointAt I f x := by
  have hfinite := finite_criticalPoints_inter_of_isCompact hf hK hKI hnd
  obtain ⟨c, hc, havoid⟩ := (Ioo_infinite hab).exists_notMem_finite (hfinite.image f)
  exact ⟨c, hc, fun x hx hxc hcrit => havoid ⟨x, ⟨hx, hcrit⟩, hxc⟩⟩

variable [T2Space M]

theorem isCompact_criticalPoints_inter {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K : Set M} (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x) :
    IsCompact {x : M | x ∈ K ∧ IsCriticalPointAt I f x} := by
  apply hK.of_isClosed_subset _ (fun _ hx => hx.1)
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  by_cases hxK : x ∈ K
  · obtain ⟨V, hV, hxV, hreg⟩ := exists_open_noncriticalPoint hf (hKI x hxK)
      (fun hc => hx ⟨hxK, hc⟩)
    exact Filter.mem_of_superset (hV.mem_nhds hxV) (fun y hy hc => hreg y hy hc.2)
  · exact Filter.mem_of_superset (hK.isClosed.isOpen_compl.mem_nhds hxK)
      (fun _ hy hc => hy hc.1)

theorem exists_relative_morse_perturbation_on_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {ε : M → ℝ}
    (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (houtside : ∀ x ∈ K, x ∉ U → ¬ IsCriticalPointAt I f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ K, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      {x : M | x ∈ K ∧ IsCriticalPointAt I g x}.Finite := by
  let C : Set M := {x | x ∈ K ∧ IsCriticalPointAt I f x}
  have hC : IsCompact C := isCompact_criticalPoints_inter hf hK hKI
  have hCU : C ⊆ U := fun x hx => Classical.byContradiction
    (fun hxU => houtside x hx.1 hxU hx.2)
  obtain ⟨n, φ, hφ, hspan⟩ :=
    exists_supported_differentials_span_of_isCompact (I := I) hC hU hCU
  choose V hV hxV hregV using fun x : C => exists_open_surjective_parameterDifferential
    (fun i => (hφ i).1) (hKI x x.property.1)
      (surjective_parameterDifferential (hspan x x.property))
  let R : Set M := ⋃ x : C, V x
  have hR : IsOpen R := isOpen_iUnion hV
  have hCR : C ⊆ R := fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  have hRR : ∀ x ∈ R, Surjective (parameterDifferential (I := I) φ x) := by
    intro x hx
    obtain ⟨y, hy⟩ := mem_iUnion.mp hx
    exact (hregV y x hy).2
  obtain ⟨δ, hδ, havoid⟩ := exists_radius_mfderiv_finitePerturbation_ne_zero hf
    (fun i => (hφ i).1) (hK.inter_right hR.isClosed_compl)
      (fun x hx => hKI x hx.1) (fun x hx hc => hx.2 (hCR ⟨hx.1, hc⟩))
  obtain ⟨η, hη, hclose⟩ := exists_radius_dist_finitePerturbation
    (fun i => (hφ i).1.continuous) (fun i => (hφ i).2.1) hε hεpos
  have hae := ae_nondegenerate_finitePerturbation_on_isCompact hf
    (fun i => (hφ i).1) hK hKI
  obtain ⟨p, hp, hgood⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))
      0 (lt_min hδ hη)).ne' (MeasureTheory.ae_restrict_of_ae hae)
  have hp' : ‖p‖ < min δ η := by simpa only [Metric.mem_ball, dist_zero_right] using hp
  obtain ⟨N, hN, hUN, heq⟩ := exists_open_finitePerturbation_eq (f := f)
    (fun i => (hφ i).2.2)
  have hg := contMDiff_finitePerturbation hf (fun i => (hφ i).1) p
  have hnd : ∀ x ∈ K, IsCriticalPointAt I (finitePerturbation f φ p) x →
      IsNondegenerateCriticalPointAt I (finitePerturbation f φ p) x := by
    intro x hx hc
    have hxR : x ∈ R := by
      by_contra hxR
      exact havoid p (lt_of_lt_of_le hp' (min_le_left _ _)) x ⟨hx, hxR⟩ hc
    exact isNondegenerateCriticalPointAt_of_bijective_hessian hg (hKI x hx)
      hc (hgood x hx (hRR x hxR) hc)
  exact ⟨finitePerturbation f φ p, hg,
    hclose p (lt_of_lt_of_le hp' (min_le_right _ _)) f, ⟨N, hN, hUN, heq p⟩,
    hnd, finite_criticalPoints_inter_of_isCompact hg hK hKI hnd⟩

variable [SigmaCompactSpace M]

theorem exists_relative_morse_approx_on_isCompact {f : M → ℝ}
    (hf : Continuous f) {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {A V K : Set M} (hA : IsClosed A) (hV : IsOpen V) (hAV : A ⊆ V)
    (hfV : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, x ∈ A → ¬ IsCriticalPointAt I f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      (∃ N : Set M, IsOpen N ∧ A ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ K, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      {x : M | x ∈ K ∧ IsCriticalPointAt I g x}.Finite := by
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨W, hW, hAW, hclW⟩ := normal_exists_closure_subset hA hV hAV
  have hhalf : Continuous (fun x => ε x / 2) := hε.div_const 2
  have hhalfpos : ∀ x, 0 < ε x / 2 := fun x => half_pos (hεpos x)
  obtain ⟨f₀, hf₀close, hf₀eq, _⟩ := hf.exists_contMDiff_approx_and_eqOn I (⊤ : ℕ∞)
    hhalf hhalfpos isClosed_closure (hV.mem_nhdsSet.mpr hclW) hfV
  have hf₀reg : ∀ x ∈ K, x ∉ Aᶜ → ¬ IsCriticalPointAt I f₀ x := by
    intro x hx hxA hc
    have hxA' : x ∈ A := Classical.not_not.mp hxA
    have heq : (f₀ : M → ℝ) =ᶠ[𝓝 x] f := by
      filter_upwards [hW.mem_nhds (hAW hxA')] with y hy
      exact hf₀eq (subset_closure hy)
    exact hreg x hx hxA' (heq.mfderiv_eq.symm.trans hc)
  obtain ⟨g, hg, hgclose, ⟨N, hN, hAN, hgeq⟩, hnd, hfinite⟩ :=
    exists_relative_morse_perturbation_on_isCompact f₀.contMDiff hhalf hhalfpos
      hK hA.isOpen_compl hKI hf₀reg
  refine ⟨g, hg, ?_, ⟨N ∩ W, hN.inter hW,
    fun x hx => ⟨hAN (by simpa only [compl_compl] using hx), hAW hx⟩, ?_⟩,
    hnd, hfinite⟩
  · intro x
    calc
      dist (g x) (f x) ≤ dist (g x) (f₀ x) + dist (f₀ x) (f x) := dist_triangle _ _ _
      _ < ε x / 2 + ε x / 2 := add_lt_add (hgclose x) (hf₀close x)
      _ = ε x := add_halves _
  · intro x hx
    exact (hgeq hx.1).trans (hf₀eq (subset_closure hx.2))

theorem exists_proper_relative_morse_approx_on_isCompact {f : M → ℝ}
    (hf : IsProperMap f) {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {A V K : Set M} (hA : IsClosed A) (hV : IsOpen V) (hAV : A ⊆ V)
    (hfV : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, x ∈ A → ¬ IsCriticalPointAt I f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ IsProperMap g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      (∃ N : Set M, IsOpen N ∧ A ⊆ N ∧ EqOn g f N) ∧
      (∀ x ∈ K, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      {x : M | x ∈ K ∧ IsCriticalPointAt I g x}.Finite := by
  obtain ⟨g, hg, hclose, hfix, hnd, hfinite⟩ :=
    exists_relative_morse_approx_on_isCompact hf.continuous
      (hε.min continuous_const) (fun x => lt_min (hεpos x) zero_lt_one)
      hA hV hAV hfV hK hKI hreg
  have hproper : IsProperMap g := by
    apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨hg.continuous, fun L hL => ?_⟩
    obtain ⟨r, hr⟩ := hL.isBounded.subset_closedBall (0 : ℝ)
    apply (hf.isCompact_preimage (isCompact_closedBall (0 : ℝ) (1 + r))).of_isClosed_subset
      (hL.isClosed.preimage hg.continuous)
    intro x hx
    have hfg : dist (f x) (g x) ≤ 1 := by
      rw [dist_comm]
      exact (hclose x).le.trans (min_le_right _ _)
    exact (dist_triangle (f x) (g x) 0).trans
      (add_le_add hfg (hr hx))
  exact ⟨g, hg, hproper, fun x => lt_of_lt_of_le (hclose x) (min_le_left _ _),
    hfix, hnd, hfinite⟩

end Manifold

end DifferentialGeometry.Morse
