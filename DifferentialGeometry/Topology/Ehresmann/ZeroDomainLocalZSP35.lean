import DifferentialGeometry.Topology.Ehresmann.ArcEndDefiningFunctionZSP35

/-!
# The zero side of ZSP05: `M₁ = (int Z)ᶜ` is a smooth domain `{F_k ≥ 0}` near `∂M₁`

Lane S-ZSP04, group G21 (kernel). For a finite family of pairwise disjoint closed sets
`Z_i = {F_i ≤ 0}` with `F_i` smooth on a boundaryless manifold and regular at its zeros
(`dF_i ≠ 0` on `{F_i = 0}`; the ZSP02 zero domains with their global ratios): every point of
`∂((int ⋃ Z_i)ᶜ)` has an open neighbourhood `U` and an index `k` with `F_k x = 0` and
`(int ⋃ Z_i)ᶜ ∩ U = {F_k ≥ 0} ∩ U` (`zero_domain_local_ZSP35`), and every zero of an `F_i` lies in
that frontier (`zero_mem_frontier_ZSP35`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Ehresmann

section Zero

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M]

/-- A regular zero of a smooth function on a boundaryless manifold is a limit of points where the
function is negative. -/
theorem mem_closure_neg_of_mfderiv_ne_zero_ZSP35 {h : M → ℝ} {x : M}
    (hh : mfderiv I 𝓘(ℝ, ℝ) h x ≠ 0) : x ∈ closure {y | h y < h x} := by
  by_contra hx
  have hmin : IsLocalMin h x := by
    by_contra hnot
    exact hx (not_isLocalMin_iff_mem_closure_lt.mp hnot)
  have h0 := hmin.mvfderiv_eq_zero (I := I) (BoundarylessManifold.isInteriorPoint (I := I))
  apply hh
  ext v
  have := congrArg (fun L => L v) h0
  change mvfderiv I h x v = 0 at this
  unfold mvfderiv at this
  exact this

variable {ι : Type*} [Finite ι] {Zs : ι → Set M} {F : ι → M → ℝ}

/-- The open complement of the other `Z_j`. -/
theorem isOpen_others_ZSP35 (hcl : ∀ i, IsClosed (Zs i)) (i : ι) :
    IsOpen (⋂ j ∈ ({i}ᶜ : Set ι), (Zs j)ᶜ) :=
  (Set.toFinite _).isOpen_biInter fun j _ => (hcl j).isOpen_compl

omit [TopologicalSpace M] [Finite ι] in
/-- A point of `Z_i` lies in the complement of the other `Z_j`. -/
theorem mem_others_ZSP35 (hdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) {i : ι} {x : M}
    (hx : x ∈ Zs i) : x ∈ ⋂ j ∈ ({i}ᶜ : Set ι), (Zs j)ᶜ := by
  simp only [mem_iInter, mem_compl_iff]
  intro j hj hxj
  exact disjoint_left.mp (hdisj i j (fun h => hj h.symm)) hx hxj

/-- A zero of `F i` is not an interior point of the union. -/
theorem zero_not_mem_interior_ZSP35 (hcl : ∀ i, IsClosed (Zs i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hle : ∀ i, {z | F i z ≤ 0} = Zs i)
    (hreg : ∀ i x, F i x = 0 → mfderiv I 𝓘(ℝ, ℝ) (F i) x ≠ 0) {i : ι} {x : M}
    (hx : F i x = 0) : x ∉ interior (⋃ j, Zs j) := by
  intro hint
  have hxZ : x ∈ Zs i := by
    rw [← hle i]
    exact hx.le
  have hxU := mem_others_ZSP35 hdisj hxZ
  have hcl' := mem_closure_pos_of_mfderiv_ne_zero_ZSP35 (I := I) (hreg i x hx)
  rw [mem_closure_iff_nhds] at hcl'
  obtain ⟨y, hyt, hyp⟩ := hcl' (interior (⋃ j, Zs j) ∩ ⋂ j ∈ ({i}ᶜ : Set ι), (Zs j)ᶜ)
    (inter_mem (isOpen_interior.mem_nhds hint) ((isOpen_others_ZSP35 hcl i).mem_nhds hxU))
  obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hyt.1)
  have hji : j = i := by
    by_contra hne
    exact (mem_iInter₂.mp hyt.2 j (fun h => hne h)) hj
  subst hji
  have : F j y ≤ 0 := by
    rw [← hle j] at hj
    exact hj
  have hyp' : F j x < F j y := hyp
  linarith

/-- **`M₁ = (int Z)ᶜ` is a smooth domain near its frontier**: every `x ∈ ∂M₁` lies in some `Z_k`
with `F_k x = 0`, and on an open `U ∋ x` (the complement of the other `Z_j`)
`M₁ ∩ U = {F_k ≥ 0} ∩ U`. -/
theorem zero_domain_local_ZSP35 (hcl : ∀ i, IsClosed (Zs i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hF : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (F i))
    (hle : ∀ i, {z | F i z ≤ 0} = Zs i)
    (hreg : ∀ i x, F i x = 0 → mfderiv I 𝓘(ℝ, ℝ) (F i) x ≠ 0) {x : M}
    (hx : x ∈ frontier (interior (⋃ j, Zs j))ᶜ) :
    ∃ (k : ι) (U : Set M), IsOpen U ∧ x ∈ U ∧ F k x = 0 ∧
      (interior (⋃ j, Zs j))ᶜ ∩ U = {z | z ∈ U ∧ 0 ≤ F k z} := by
  have hZc : IsClosed (⋃ j, Zs j) := isClosed_iUnion_of_finite hcl
  rw [frontier_compl] at hx
  have hxcl : x ∈ closure (interior (⋃ j, Zs j)) := hx.1
  have hxint : x ∉ interior (⋃ j, Zs j) := by
    have := hx.2
    rwa [interior_interior] at this
  have hxZ : x ∈ ⋃ j, Zs j := closure_minimal interior_subset hZc hxcl
  obtain ⟨k, hk⟩ := mem_iUnion.mp hxZ
  have hneg : ∀ z, F k z < 0 → z ∈ interior (⋃ j, Zs j) := by
    intro z hz
    have hsub : {y | F k y < 0} ⊆ ⋃ j, Zs j := fun y hy =>
      mem_iUnion.mpr ⟨k, by rw [← hle k]; exact le_of_lt (show F k y < 0 from hy)⟩
    exact interior_maximal hsub (isOpen_lt (hF k).continuous continuous_const) hz
  have hFk : F k x = 0 := by
    have hle0 : F k x ≤ 0 := by
      rw [← hle k] at hk
      exact hk
    rcases hle0.lt_or_eq with hlt | heq
    · exact absurd (hneg x hlt) hxint
    · exact heq
  refine ⟨k, ⋂ j ∈ ({k}ᶜ : Set ι), (Zs j)ᶜ, isOpen_others_ZSP35 hcl k, mem_others_ZSP35 hdisj hk,
    hFk, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzU⟩
    refine ⟨hzU, ?_⟩
    by_contra hneg'
    exact hz (hneg z (lt_of_not_ge hneg'))
  · rintro ⟨hzU, hz0⟩
    refine ⟨?_, hzU⟩
    rcases hz0.lt_or_eq with hpos | hzero
    · intro hint
      obtain ⟨j, hj⟩ := mem_iUnion.mp (interior_subset hint)
      by_cases hjk : j = k
      · subst hjk
        have : F j z ≤ 0 := by
          rw [← hle j] at hj
          exact hj
        linarith
      · exact (mem_iInter₂.mp hzU j (fun h => hjk h)) hj
    · exact zero_not_mem_interior_ZSP35 hcl hdisj hle hreg hzero.symm

/-- Every zero of an `F_i` lies in the frontier of `M₁ = (int Z)ᶜ`. -/
theorem zero_mem_frontier_ZSP35 (hcl : ∀ i, IsClosed (Zs i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) (hF : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (F i))
    (hle : ∀ i, {z | F i z ≤ 0} = Zs i)
    (hreg : ∀ i x, F i x = 0 → mfderiv I 𝓘(ℝ, ℝ) (F i) x ≠ 0) {i : ι} {x : M}
    (hx : F i x = 0) : x ∈ frontier (interior (⋃ j, Zs j))ᶜ := by
  rw [frontier_compl]
  refine ⟨?_, ?_⟩
  · have hcl' := mem_closure_neg_of_mfderiv_ne_zero_ZSP35 (I := I) (hreg i x hx)
    refine closure_mono ?_ hcl'
    intro z hz
    have hz' : F i z < 0 := by
      have : F i z < F i x := hz
      linarith
    have hsub : {y | F i y < 0} ⊆ ⋃ j, Zs j := fun y hy =>
      mem_iUnion.mpr ⟨i, by rw [← hle i]; exact le_of_lt (show F i y < 0 from hy)⟩
    exact interior_maximal hsub (isOpen_lt (hF i).continuous continuous_const) hz'
  · rw [interior_interior]
    exact zero_not_mem_interior_ZSP35 hcl hdisj hle hreg hx

end Zero

end DifferentialGeometry.Topology.Ehresmann
