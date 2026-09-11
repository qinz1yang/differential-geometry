import DifferentialGeometry.Topology.Morse.Existence
import Mathlib.Topology.Algebra.Module.Cardinality

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

variable {ι : Type*}

private theorem dense_injective_real [Countable ι] :
    Dense {f : ι → ℝ | Function.Injective f} := by
  classical
  obtain ⟨n, hn⟩ := exists_injective_nat ι
  rw [dense_iff_inter_open]
  intro U hU ⟨f, hf⟩
  let c : ι → ℝ := fun i => n i
  have hc : Function.Injective c := by
    intro i j hij
    apply hn
    dsimp [c] at hij
    exact_mod_cast hij
  let bad : Set ℝ := Set.range (fun ij : ι × ι =>
    (f ij.2 - f ij.1) / (c ij.1 - c ij.2))
  have hbad : Dense badᶜ := (Set.countable_range _).dense_compl ℝ
  have hcurve : Continuous (fun t : ℝ => fun i => f i + t * c i) := by
    exact continuous_pi fun i => continuous_const.add (continuous_id.mul continuous_const)
  have hU0 : {t : ℝ | (fun i => f i + t * c i) ∈ U} ∈ 𝓝 0 :=
    hcurve.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa using hf))
  obtain ⟨t, htbad, htU⟩ := hbad.inter_nhds_nonempty hU0
  refine ⟨fun i => f i + t * c i, htU, ?_⟩
  intro i j hij
  by_contra hne
  have hden : c i - c j ≠ 0 := sub_ne_zero.mpr (hc.ne hne)
  apply htbad
  refine ⟨(i, j), ?_⟩
  dsimp
  apply (div_eq_iff hden).mpr
  nlinarith

private theorem dense_injective_add_real [Countable ι] (v : ι → ℝ) :
    Dense {a : ι → ℝ | Function.Injective (fun i => v i + a i)} := by
  exact dense_injective_real.preimage (Homeomorph.addLeft v).isOpenMap

private theorem exists_injective_add_real_mem_nhds [Countable ι] (v : ι → ℝ)
    {U : Set (ι → ℝ)} (hU : U ∈ 𝓝 0) :
    ∃ a ∈ U, Function.Injective (fun i => v i + a i) := by
  obtain ⟨a, ha, hUa⟩ := (dense_injective_add_real v).inter_nhds_nonempty hU
  exact ⟨a, hUa, ha⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M]

private theorem finite_cutoff_sum_eventually_eq {ι : Type*} [Fintype ι]
    (a : ι → ℝ) {χ : ι → M → ℝ} {x : M} (i : ι)
    (hχi : χ i =ᶠ[𝓝 x] 1)
    (hχj : ∀ j, j ≠ i → χ j =ᶠ[𝓝 x] 0) :
    (fun y => ∑ j, a j * χ j y) =ᶠ[𝓝 x] fun _ => a i := by
  classical
  have hall : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ i → χ j y = 0 := by
    apply Filter.eventually_all.mpr
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
    · exact (hχj j hji).mono fun _ h _ => h
  filter_upwards [hχi, hall] with y hy hj
  rw [Finset.sum_eq_single i]
  · simp only [hy, Pi.one_apply, mul_one]
  · intro j _ hji
    rw [hj j hji, mul_zero]
  · simp

private theorem isCriticalPointAt_add_finite_cutoff_sum_iff {ι : Type*} [Fintype ι]
    (f : M → ℝ) (a : ι → ℝ) {χ : ι → M → ℝ} {x : M} (i : ι)
    (hχi : χ i =ᶠ[𝓝 x] 1)
    (hχj : ∀ j, j ≠ i → χ j =ᶠ[𝓝 x] 0) :
    IsCriticalPointAt I (fun y => f y + ∑ j, a j * χ j y) x ↔ IsCriticalPointAt I f x :=
  isCriticalPointAt_add_of_eventuallyEq_const (finite_cutoff_sum_eventually_eq a i hχi hχj)

private theorem add_finite_cutoff_sum_apply {ι : Type*} [Fintype ι]
    (f : M → ℝ) (a : ι → ℝ) {χ : ι → M → ℝ} {x : M} (i : ι)
    (hχi : χ i =ᶠ[𝓝 x] 1)
    (hχj : ∀ j, j ≠ i → χ j =ᶠ[𝓝 x] 0) :
    f x + ∑ j, a j * χ j x = f x + a i :=
  congrArg (fun r => f x + r) (finite_cutoff_sum_eventually_eq a i hχi hχj).eq_of_nhds

private theorem exists_smooth_cutoffs_on_finite
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] {S : Set M} (hS : S.Finite) :
    ∃ χ : S → M → ℝ, (∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i)) ∧
      (∀ i, HasCompactSupport (χ i)) ∧
      (∀ i : S, χ i =ᶠ[𝓝 (i : M)] 1) ∧
      (∀ i j : S, j ≠ i → χ j =ᶠ[𝓝 (i : M)] 0) := by
  have hex (i : S) : ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ χ =ᶠ[𝓝 (i : M)] 1 ∧
      tsupport χ ⊆ (S \ {(i : M)})ᶜ := by
    obtain ⟨χ, hχ, hc, hone, hs, _⟩ := DifferentialGeometry.Analysis.exists_mfd_bump (I := I)
      (isCompact_singleton (x := (i : M))) hS.sdiff.isClosed.isOpen_compl
      (by simp : {(i : M)} ⊆ (S \ {(i : M)})ᶜ)
    exact ⟨χ, hχ, hc, by simpa only [nhdsSet_singleton] using hone, hs⟩
  choose χ hχ hc hone hs using hex
  refine ⟨χ, hχ, hc, hone, ?_⟩
  intro i j hji
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hi
  apply hs j hi
  exact ⟨i.property, by simpa using (Subtype.coe_ne_coe.mpr hji).symm⟩


variable [IsManifold I ∞ M]

omit [IsManifold I ∞ M] in
private theorem smooth_add_finite_cutoffs_joint {ι : Type} [Fintype ι]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {χ : ι → M → ℝ}
    (hχ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (χ i)) :
    ContMDiff ((𝓘(ℝ, ι → ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ι → ℝ) × M => f p.2 + ∑ j, p.1 j * χ j p.2) := by
  apply (hf.comp contMDiff_snd).add
  apply ContMDiff.sum
  intro i _
  have hproj : ContMDiff ((𝓘(ℝ, ι → ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (ι → ℝ) × M => p.1 i) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).contMDiff.comp contMDiff_fst
  exact hproj.mul ((hχ i).comp contMDiff_snd)

omit [IsManifold I ∞ M] in
private theorem exists_open_cutoff_plateaus {S : Set M} [Finite S]
    {χ : S → M → ℝ}
    (hχi : ∀ i : S, χ i =ᶠ[𝓝 (i : M)] 1)
    (hχj : ∀ i j : S, j ≠ i → χ j =ᶠ[𝓝 (i : M)] 0) :
    ∃ U : S → Set M, (∀ i, IsOpen (U i)) ∧ (∀ i : S, (i : M) ∈ U i) ∧
      (∀ i x, x ∈ U i → χ i =ᶠ[𝓝 x] 1) ∧
      (∀ i j x, j ≠ i → x ∈ U i → χ j =ᶠ[𝓝 x] 0) := by
  let U : S → Set M := fun i => interior {x | χ i x = 1 ∧ ∀ j, j ≠ i → χ j x = 0}
  refine ⟨U, fun _ => isOpen_interior, ?_, ?_, ?_⟩
  · intro i
    apply mem_interior_iff_mem_nhds.mpr
    have hall : ∀ᶠ x in 𝓝 (i : M), ∀ j, j ≠ i → χ j x = 0 := by
      apply Filter.eventually_all.mpr
      intro j
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
      · exact (hχj i j hji).mono fun x hx _ => hx
    filter_upwards [hχi i, hall] with x hi hj
    exact ⟨hi, hj⟩
  · intro i x hx
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (interior_subset hy).1
  · intro i j x hji hx
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    exact (interior_subset hy).2 j hji

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M] [T2Space M]

theorem exists_morse_function_injOn_criticalPoints
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    ∃ g : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ g ∧
      (∀ x, IsCriticalPointAt I g x → IsNondegenerateCriticalPointAt I g x) ∧
      criticalPoints I g = criticalPoints I f ∧ Set.InjOn g (criticalPoints I g) := by
  classical
  let S := criticalPoints I f
  have hS : S.Finite := finite_criticalPoints_of_compact_of_isNondegenerate f hf hnd
  let : Fintype S := hS.fintype
  obtain ⟨χ, hχ, _, hone, hzero⟩ := exists_smooth_cutoffs_on_finite
    (I := I) hS
  obtain ⟨U, hUopen, hUmem, hUone, hUzero⟩ := exists_open_cutoff_plateaus hone hzero
  let L : Set M := (⋃ i, U i)ᶜ
  have hL : IsCompact L := (isOpen_iUnion hUopen).isClosed_compl.isCompact
  have hSsub : S ⊆ ⋃ i, U i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hUmem ⟨x, hx⟩⟩
  let F : (S → ℝ) → M → ℝ := fun a x => f x + ∑ i, a i * χ i x
  have hF : ContMDiff ((𝓘(ℝ, S → ℝ)).prod I) 𝓘(ℝ, ℝ) ∞ (Function.uncurry F) := by
    change ContMDiff ((𝓘(ℝ, S → ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : (S → ℝ) × M => f p.2 + ∑ i, p.1 i * χ i p.2)
    exact smooth_add_finite_cutoffs_joint hf hχ
  have hF0 : F 0 = f := by
    funext x
    simp [F]
  have hregular : ∀ᶠ a in 𝓝 (0 : S → ℝ), ∀ x ∈ L, ¬ IsCriticalPointAt I (F a) x := by
    apply eventually_not_isCriticalPointAt_on_isCompact hL
      (fun _ _ => (hF.of_le (by decide)).contMDiffAt)
    intro x hx hcrit
    rw [hF0] at hcrit
    exact hx (hSsub hcrit)
  have hmorse : ∀ᶠ a in 𝓝 (0 : S → ℝ), ∀ x ∈ (univ : Set M),
      IsCriticalPointAt I (F a) x → IsNondegenerateCriticalPointAt I (F a) x := by
    apply eventually_isNondegenerateCriticalPointAt_on_isCompact isCompact_univ
      (fun _ _ => (hF.of_le (by decide)).contMDiffAt)
    simpa only [hF0] using (fun x (_ : x ∈ (univ : Set M)) => hnd x)
  obtain ⟨a, ha, hinj⟩ := exists_injective_add_real_mem_nhds
    (fun i : S => f i) (hregular.and hmorse)
  have hcritical : criticalPoints I (F a) = S := by
    ext x
    change IsCriticalPointAt I (F a) x ↔ IsCriticalPointAt I f x
    by_cases hx : x ∈ ⋃ i, U i
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact isCriticalPointAt_add_finite_cutoff_sum_iff f a i (hUone i x hi)
        (fun j hji => hUzero i j x hji hi)
    · exact iff_of_false (ha.1 x hx) (fun hc => hx (hSsub hc))
  refine ⟨F a, hF.comp (contMDiff_const.prodMk contMDiff_id),
    fun x => ha.2 x (mem_univ x), hcritical, ?_⟩
  intro x hx y hy heq
  rw [hcritical] at hx hy
  have hvalues (i : S) : F a i = f i + a i :=
    add_finite_cutoff_sum_apply f a i (hone i) (hzero i)
  have hEq : (⟨x, hx⟩ : S) = ⟨y, hy⟩ := by
    apply hinj
    change f x + a ⟨x, hx⟩ = f y + a ⟨y, hy⟩
    rw [← hvalues ⟨x, hx⟩, ← hvalues ⟨y, hy⟩]
    exact heq
  exact congrArg Subtype.val hEq

theorem exists_excellent_morse_function :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) ∧
      Set.InjOn f (criticalPoints I f) := by
  obtain ⟨f, hf, hnd⟩ := exists_morse_function (I := I) (M := M)
  obtain ⟨g, hg, hgood, _, hinj⟩ := exists_morse_function_injOn_criticalPoints hf hnd
  exact ⟨g, hg, hgood, hinj⟩

end DifferentialGeometry.Topology.Morse
