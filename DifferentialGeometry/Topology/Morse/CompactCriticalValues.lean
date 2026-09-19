/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.Morse.CriticalNeighborhood
import DifferentialGeometry.Topology.Morse.ExcellentFamily
import DifferentialGeometry.Topology.Morse.InteriorRestriction
import DifferentialGeometry.Topology.Order.FiniteSeparation

/-! Relative separation of critical values in compact Morse regions. -/

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Morse

open DifferentialGeometry.Topology.Morse

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [T2Space M]

theorem exists_critical_value_perturbation_family_on_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U : Set M} (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ K, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hU : IsOpen U) (hCU : {x | x ∈ K ∧ IsCriticalPointAt I f x} ⊆ U) :
    ∃ (n : ℕ) (e : Fin n → M) (φ : Fin n → M → ℝ) (ε : ℝ),
      Injective e ∧ range e = {x | x ∈ K ∧ IsCriticalPointAt I f x} ∧
      (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i) ∧ HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U) ∧
      (∀ i p, finitePerturbation f φ p =ᶠ[𝓝 (e i)] (fun y => f y + p i)) ∧
      0 < ε ∧ ∀ p : Fin n → ℝ, ‖p‖ < ε →
        {x | IsCriticalPointAt I (finitePerturbation f φ p) x} =
          {x | IsCriticalPointAt I f x} := by
  obtain ⟨V, hV, hKV, hVI, hVcrit⟩ := exists_open_criticalPoints_inter_eq hf hKI hnd
  let N : TopologicalSpace.Opens M := ⟨V, hV⟩
  let fN : N → ℝ := fun x => f x
  have hfN : ContMDiff I 𝓘(ℝ, ℝ) ∞ fN := hf.comp contMDiff_subtype_val
  have hNI (x : N) : I.IsInteriorPoint (x : M) := hVI x x.property
  have hCN : {x : N | IsCriticalPointAt I fN x} =
      Subtype.val ⁻¹' {x | x ∈ K ∧ IsCriticalPointAt I f x} := by
    ext x
    change IsCriticalPointAt I fN x ↔ (x : M) ∈ K ∧ IsCriticalPointAt I f x
    rw [isCriticalPointAt_openRestriction I hf x (hNI x)]
    exact ⟨fun hc => (Set.ext_iff.mp hVcrit x).mp ⟨x.property, hc⟩, fun hc => hc.2⟩
  have hC : {x : N | IsCriticalPointAt I fN x}.Finite := by
    rw [hCN]
    exact (finite_criticalPoints_inter_of_isCompact hf hK hKI hnd).preimage
      Subtype.val_injective.injOn
  obtain ⟨n, e, φ, ε, he, heC, hφ, hgerm, hε, hcrit⟩ :=
    exists_critical_value_perturbation_family hfN hC (hU.preimage continuous_subtype_val)
      (fun x hx => hCU ((Set.ext_iff.mp hCN x).mp hx))
      (fun x _ => I.isInteriorPoint_iff_isInteriorPoint_val.mpr (hNI x))
  let ψ : Fin n → M → ℝ := fun i => Subtype.val.extend (φ i) 0
  have hψval : ∀ i (x : N), ψ i x = φ i x :=
    fun i x => Subtype.val_injective.extend_apply (φ i) 0 x
  have hψsupport : ∀ i, tsupport (ψ i) = Subtype.val '' tsupport (φ i) :=
    fun i => (hφ i).2.1.tsupport_extend_zero continuous_subtype_val Subtype.val_injective
  have hψN : ∀ i, tsupport (ψ i) ⊆ V := by
    intro i x hx
    rw [hψsupport i] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.property
  have hψ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (ψ i) ∧
      HasCompactSupport (ψ i) ∧ tsupport (ψ i) ⊆ U := by
    intro i
    refine ⟨ContMDiff.extend_zero (hφ i).2.1 (hφ i).1,
      (hφ i).2.1.extend_zero continuous_subtype_val, ?_⟩
    intro x hx
    rw [hψsupport i] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (hφ i).2.2 hy
  have hrestrict (p : Fin n → ℝ) :
      (fun x : N => finitePerturbation f ψ p x) = finitePerturbation fN φ p := by
    funext x
    simp only [finitePerturbation, hψval, fN]
  have heRange : range (fun i => (e i : M)) =
      {x | x ∈ K ∧ IsCriticalPointAt I f x} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (Set.ext_iff.mp hCN (e i)).mp (heC ▸ mem_range_self i)
    · intro hx
      let y : N := ⟨x, hKV hx.1⟩
      have hy : IsCriticalPointAt I fN y := (Set.ext_iff.mp hCN y).mpr hx
      obtain ⟨i, hi⟩ := (heC.symm ▸ hy : y ∈ range e)
      exact ⟨i, congrArg Subtype.val hi⟩
  refine ⟨n, fun i => (e i : M), ψ, ε, Subtype.val_injective.comp he,
    heRange, hψ, ?_, hε, ?_⟩
  · intro i p
    rw [← N.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq (e i)]
    change ∀ᶠ x : N in 𝓝 (e i), finitePerturbation f ψ p x = f x + p i
    filter_upwards [hgerm i p] with x hx
    exact (congrFun (hrestrict p) x).trans hx
  · intro p hp
    have hg := contMDiff_finitePerturbation hf (fun i => (hψ i).1) p
    obtain ⟨W, hW, hNW, hfix⟩ := exists_open_finitePerturbation_eq (f := f) hψN
    ext x
    by_cases hx : x ∈ V
    · let y : N := ⟨x, hx⟩
      change IsCriticalPointAt I (finitePerturbation f ψ p) (y : M) ↔
        IsCriticalPointAt I f (y : M)
      rw [← isCriticalPointAt_openRestriction I hg y (hNI y),
        ← isCriticalPointAt_openRestriction I hf y (hNI y), hrestrict p]
      exact (Set.ext_iff.mp (hcrit p hp) y)
    · have heq : finitePerturbation f ψ p =ᶠ[𝓝 x] f := by
        filter_upwards [hW.mem_nhds (hNW hx)] with y hy
        exact hfix p hy
      exact Iff.of_eq (congrArg (fun D : E →L[ℝ] ℝ => D = 0) heq.mfderiv_eq)

theorem exists_relative_distinct_critical_values_on_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {K U : Set M} (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hnd : ∀ x ∈ K, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hU : IsOpen U) (hCU : {x | x ∈ K ∧ IsCriticalPointAt I f x} ⊆ U)
    {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      HasCompactSupport (g - f) ∧ tsupport (g - f) ⊆ U ∧
      (∃ N : Set M, IsOpen N ∧ Uᶜ ⊆ N ∧ EqOn g f N) ∧
      {x | IsCriticalPointAt I g x} = {x | IsCriticalPointAt I f x} ∧
      InjOn g {x | x ∈ K ∧ IsCriticalPointAt I g x} ∧
      (∀ x ∈ K, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      ∀ x ∈ K, IsCriticalPointAt I f x → ∃ b : ℝ, g =ᶠ[𝓝 x] (fun y => f y + b) := by
  obtain ⟨n, e, φ, δ, _, heC, hφ, hgerm, hδ, hcrit⟩ :=
    exists_critical_value_perturbation_family_on_isCompact hf hK hKI hnd hU hCU
  obtain ⟨η, hη, hclose⟩ := exists_radius_dist_finitePerturbation
    (fun i => (hφ i).1.continuous) (fun i => (hφ i).2.1) hε hεpos
  obtain ⟨p, hp, hinj⟩ := DifferentialGeometry.Topology.exists_small_injective_add
    (fun i => f (e i)) (lt_min hδ hη)
  have hpδ : ‖p‖ < δ := lt_of_lt_of_le hp (min_le_left _ _)
  have hpη : ‖p‖ < η := lt_of_lt_of_le hp (min_le_right _ _)
  let g := finitePerturbation f φ p
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ g :=
    contMDiff_finitePerturbation hf (fun i => (hφ i).1) p
  have hcritEq : {x | IsCriticalPointAt I g x} = {x | IsCriticalPointAt I f x} :=
    hcrit p hpδ
  let C : Set M := ⋃ i, tsupport (φ i)
  have hC : IsCompact C := isCompact_iUnion (fun i => (hφ i).2.1)
  have hCU' : C ⊆ U := iUnion_subset fun i => (hφ i).2.2
  have hsupport : support (g - f) ⊆ C := by
    intro x hx
    by_contra hxC
    have hz : ∀ i, φ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hxC (mem_iUnion.mpr ⟨i, hi⟩))
    exact hx (by simp [g, finitePerturbation, hz])
  have htsupport : tsupport (g - f) ⊆ C := closure_minimal hsupport hC.isClosed
  have hconstant : ∀ x ∈ K, IsCriticalPointAt I f x →
      ∃ b : ℝ, g =ᶠ[𝓝 x] (fun y => f y + b) := by
    intro x hx hc
    obtain ⟨i, rfl⟩ := (heC.symm ▸ ⟨hx, hc⟩ : x ∈ range e)
    exact ⟨p i, hgerm i p⟩
  obtain ⟨N, hN, hUN, hfix⟩ := exists_open_finitePerturbation_eq (f := f)
    (fun i => (hφ i).2.2)
  refine ⟨g, hg, hclose p hpη f, hC.of_isClosed_subset (isClosed_tsupport _) htsupport,
    htsupport.trans hCU', ⟨N, hN, hUN, hfix p⟩, hcritEq, ?_, ?_, hconstant⟩
  · intro x hx y hy hxy
    have hxC := (Set.ext_iff.mp hcritEq x).mp hx.2
    have hyC := (Set.ext_iff.mp hcritEq y).mp hy.2
    obtain ⟨i, rfl⟩ := (heC.symm ▸ ⟨hx.1, hxC⟩ : x ∈ range e)
    obtain ⟨j, rfl⟩ := (heC.symm ▸ ⟨hy.1, hyC⟩ : y ∈ range e)
    apply congrArg e
    apply hinj
    exact (hgerm i p).eq_of_nhds.symm.trans (hxy.trans (hgerm j p).eq_of_nhds)
  · intro x hx hc
    have hc' := (Set.ext_iff.mp hcritEq x).mp hc
    obtain ⟨b, hb⟩ := hconstant x hx hc'
    exact (isNondegenerateCriticalPointAt_iff_of_eventuallyEq_add_const
      (hf.mdifferentiableAt (by simp)) (hKI x hx) hb).mpr (hnd x hx hc')

variable [SigmaCompactSpace M]

theorem exists_relative_excellent_morse_approx_on_isCompact {f : M → ℝ}
    (hf : Continuous f) {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {A V K O : Set M} (hA : IsClosed A) (hV : IsOpen V) (hAV : A ⊆ V)
    (hfV : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, x ∈ A → ¬ IsCriticalPointAt I f x)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      (∃ N : Set M, IsOpen N ∧ A ⊆ N ∧ EqOn g f N) ∧
      ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ O ∧
        (∀ x ∈ closure W, I.IsInteriorPoint x) ∧
        (∀ x ∈ closure W, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
        {x | x ∈ closure W ∧ IsCriticalPointAt I g x}.Finite ∧
        InjOn g {x | x ∈ closure W ∧ IsCriticalPointAt I g x} := by
  have hhalf : Continuous (fun x => ε x / 2) := hε.div_const 2
  have hhalfpos : ∀ x, 0 < ε x / 2 := fun x => half_pos (hεpos x)
  obtain ⟨f₀, hf₀, hclose₀, ⟨N₀, hN₀, hAN₀, hfix₀⟩, hnd₀, _⟩ :=
    exists_relative_morse_approx_on_isCompact hf hhalf hhalfpos hA hV hAV hfV hK hKI hreg
  have hCU : {x | x ∈ K ∧ IsCriticalPointAt I f₀ x} ⊆ Aᶜ := by
    intro x hx hxA
    have heq : f₀ =ᶠ[𝓝 x] f := by
      filter_upwards [hN₀.mem_nhds (hAN₀ hxA)] with y hy
      exact hfix₀ hy
    exact hreg x hx.1 hxA (heq.mfderiv_eq.symm.trans hx.2)
  obtain ⟨g, hg, hclose, _, _, ⟨N, hN, hAN, hfix⟩, _, hinj, hnd, _⟩ :=
    exists_relative_distinct_critical_values_on_isCompact hf₀ hK hKI hnd₀
      hA.isOpen_compl hCU hhalf hhalfpos
  obtain ⟨W, hW, hKW, hcompact, hWO, hWI, hcritW, hndW, hfinW⟩ :=
    exists_open_morse_neighborhood_of_isCompact hg hK hO hKO hKI hnd
  refine ⟨g, hg, ?_, ⟨N ∩ N₀, hN.inter hN₀, ?_, ?_⟩,
    W, hW, hKW, hcompact, hWO, hWI, hndW, hfinW, ?_⟩
  · intro x
    calc
      dist (g x) (f x) ≤ dist (g x) (f₀ x) + dist (f₀ x) (f x) := dist_triangle _ _ _
      _ < ε x / 2 + ε x / 2 := add_lt_add (hclose x) (hclose₀ x)
      _ = ε x := add_halves _
  · intro x hx
    exact ⟨hAN (by simpa only [compl_compl] using hx), hAN₀ hx⟩
  · intro x hx
    exact (hfix hx.1).trans (hfix₀ hx.2)
  · intro x hx y hy hxy
    exact hinj ((Set.ext_iff.mp hcritW x).mp hx) ((Set.ext_iff.mp hcritW y).mp hy) hxy

theorem exists_proper_relative_excellent_morse_approx_on_isCompact {f : M → ℝ}
    (hf : IsProperMap f) {ε : M → ℝ} (hε : Continuous ε) (hεpos : ∀ x, 0 < ε x)
    {A V K O : Set M} (hA : IsClosed A) (hV : IsOpen V) (hAV : A ⊆ V)
    (hfV : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V) (hK : IsCompact K)
    (hKI : ∀ x ∈ K, I.IsInteriorPoint x)
    (hreg : ∀ x ∈ K, x ∈ A → ¬ IsCriticalPointAt I f x)
    (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧ IsProperMap g ∧
      (∀ x, dist (g x) (f x) < ε x) ∧
      (∃ N : Set M, IsOpen N ∧ A ⊆ N ∧ EqOn g f N) ∧
      ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧ IsCompact (closure W) ∧ closure W ⊆ O ∧
        (∀ x ∈ closure W, I.IsInteriorPoint x) ∧
        (∀ x ∈ closure W, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
        {x | x ∈ closure W ∧ IsCriticalPointAt I g x}.Finite ∧
        InjOn g {x | x ∈ closure W ∧ IsCriticalPointAt I g x} := by
  obtain ⟨g, hg, hclose, hfix, W, hW, hKW, hcompact, hWO, hWI, hnd, hfinite, hinj⟩ :=
    exists_relative_excellent_morse_approx_on_isCompact hf.continuous
      (hε.min continuous_const) (fun x => lt_min (hεpos x) zero_lt_one)
      hA hV hAV hfV hK hKI hreg hO hKO
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
    exact (dist_triangle (f x) (g x) 0).trans (add_le_add hfg (hr hx))
  exact ⟨g, hg, hproper, fun x => lt_of_lt_of_le (hclose x) (min_le_left _ _), hfix,
    W, hW, hKW, hcompact, hWO, hWI, hnd, hfinite, hinj⟩

end DifferentialGeometry.Morse
