import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# A global defining function with a prescribed local normal form (package Z0, draft 74 §5.2 A)

Lane C14-ZSP35d. Review 74 D74-7: the zero domains need a GLOBAL smooth defining function that
EQUALS a prescribed local ratio `r` near the whole zero level (for ZSP02: `r = u/v − 2/5`), while
the available global function `G` only satisfies `G = a · r` with a positive factor `a` there
(`a = v/R`). Dividing by `a` is not available where `a` is undefined or zero, so `a` is first
replaced by a global smooth positive function `â` equal to `a` near the zero level (smooth cutoff
`χ`, `â = χ a + (1 − χ)`, the product `χ a` extended by zero off the cutoff's support), and
`F = G / â`.

* `exists_ratioCompatible_global_definer_ZSP35` (the frozen contract
  `exists_ratioCompatible_global_definer74` of draft 74 §5.2 A, for any smooth Hausdorff
  `σ`-compact manifold modelled with corners on a finite-dimensional space): `F` smooth on `M`,
  `F = r` on an open `N ⊇ {G = 0}` with `closure N ⊆ O`, the same sublevel `{F ≤ 0} = {G ≤ 0}` and
  level `{F = 0} = {G = 0}`, nonzero differential on the level. Strengthening: the contract's
  smoothness hypothesis on `r` is not needed (it follows on `N` from `F = r`).
* `exists_pos_eq_near_ZSP35` (the positive factor) and `mfderiv_mul_of_eq_zero_ZSP35` (the
  product rule at a zero).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **A positive smooth factor that agrees with a given one near a closed set**: if `a` is smooth
and positive on an open `O ⊇ Z` (`Z` closed), there are an open `N` with `Z ⊆ N`,
`closure N ⊆ O` and a global smooth positive `â` with `â = a` on `N`. -/
theorem exists_pos_eq_near_ZSP35 [T2Space M] [SigmaCompactSpace M] {Z O : Set M}
    (hZ : IsClosed Z) (hO : IsOpen O) (hZO : Z ⊆ O) {a : M → ℝ}
    (ha : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ a O) (hapos : ∀ x ∈ O, 0 < a x) :
    ∃ (N : Set M) (â : M → ℝ), IsOpen N ∧ Z ⊆ N ∧ closure N ⊆ O ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ â ∧ (∀ x, 0 < â x) ∧ ∀ x ∈ N, â x = a x := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have : ParacompactSpace M := paracompact_of_locallyCompact_sigmaCompact
  obtain ⟨N₂, hN₂o, hZN₂, hN₂O⟩ := normal_exists_closure_subset hZ hO hZO
  obtain ⟨N₁, hN₁o, hZN₁, hN₁N₂⟩ := normal_exists_closure_subset hZ hN₂o hZN₂
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    hN₂o.isClosed_compl isClosed_closure
    (disjoint_compl_left_iff_subset.mpr hN₁N₂)
  have hsupp : tsupport (fun x => χ x * a x) ⊆ O := by
    refine (closure_mono fun x hx => ?_).trans hN₂O
    by_contra hxN
    exact hx (by change χ x * a x = 0; rw [hχ0 hxN]; simp)
  have hχa : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => χ x * a x) := by
    refine contMDiff_of_tsupport fun x hx => ?_
    exact (χ.contMDiff x).mul (ha.contMDiffAt (hO.mem_nhds (hsupp hx)))
  refine ⟨N₁, fun x => χ x * a x + (1 - χ x), hN₁o, hZN₁, ?_, ?_, fun x => ?_, fun x hx => ?_⟩
  · exact (hN₁N₂.trans subset_closure).trans hN₂O
  · exact hχa.add (contMDiff_const.sub χ.contMDiff)
  · obtain ⟨h0, h1⟩ := hχI x
    by_cases hx : χ x = 0
    · simp [hx]
    · have hxO : x ∈ O := by
        refine hN₂O (subset_closure ?_)
        by_contra hxN
        exact hx (hχ0 hxN)
      have := mul_pos (lt_of_le_of_ne h0 (Ne.symm hx)) (hapos x hxO)
      linarith
  · have h1 : χ x = 1 := hχ1 (subset_closure hx)
    simp [h1]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- **The product rule at a zero**: if `G x = 0`, `G` is differentiable at `x` and `b` is
differentiable at `x`, then `d(G · b)(x) = b(x) · dG(x)`. -/
theorem mfderiv_mul_of_eq_zero_ZSP35 {G b : M → ℝ} {x : M}
    (hG : MDifferentiableAt I 𝓘(ℝ, ℝ) G x) (hb : MDifferentiableAt I 𝓘(ℝ, ℝ) b x)
    (h0 : G x = 0) :
    mfderiv I 𝓘(ℝ, ℝ) (fun y => G y * b y) x = b x • mfderiv I 𝓘(ℝ, ℝ) G x := by
  have h := hG.hasMFDerivAt.mul hb.hasMFDerivAt
  have h2 : HasMFDerivAt I 𝓘(ℝ, ℝ) (G * b) x (b x • mfderiv I 𝓘(ℝ, ℝ) G x) := by
    refine h.congr_mfderiv ?_
    ext v
    rw [h0, add_apply]
    have h00 : ((0 : ℝ) • mfderiv I 𝓘(ℝ, ℝ) b x) v = 0 :=
      show (0 : ℝ) • (mfderiv I 𝓘(ℝ, ℝ) b x v) = 0 from zero_smul ℝ _
    exact (congrArg (· + ((b x • mfderiv I 𝓘(ℝ, ℝ) G x) v)) h00).trans (zero_add _)
  exact h2.mfderiv

/-- **A global defining function with a prescribed normal form near its level** (draft 74 §5.2 A,
`exists_ratioCompatible_global_definer74`; D74-7): let `G` be smooth on `M` with nonzero
differential at every zero, `O ⊇ {G = 0}` open, and on `O` let `G = a · r` with `a` smooth and
positive on `O`. Then there are a smooth `F` on `M` and an open `N ⊇ {G = 0}` with
`closure N ⊆ O` such that `F = r` on `N`, `{F ≤ 0} = {G ≤ 0}`, `{F = 0} = {G = 0}`, and `F` has
nonzero differential at every zero. (`F = G / â`, `â` from `exists_pos_eq_near_ZSP35`.) -/
theorem exists_ratioCompatible_global_definer_ZSP35 [T2Space M] [SigmaCompactSpace M]
    {G : M → ℝ} (hG : ContMDiff I 𝓘(ℝ, ℝ) ∞ G)
    (hreg : ∀ x, G x = 0 → mfderiv I 𝓘(ℝ, ℝ) G x ≠ 0)
    {O : Set M} (hO : IsOpen O) (hzero : {x | G x = 0} ⊆ O) {r a : M → ℝ}
    (ha : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ a O) (hapos : ∀ x ∈ O, 0 < a x)
    (hfactor : ∀ x ∈ O, G x = a x * r x) :
    ∃ (F : M → ℝ) (N : Set M), IsOpen N ∧ {x | G x = 0} ⊆ N ∧ closure N ⊆ O ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ F ∧ (∀ x ∈ N, F x = r x) ∧
      {x | F x ≤ 0} = {x | G x ≤ 0} ∧ {x | F x = 0} = {x | G x = 0} ∧
      ∀ x, F x = 0 → mfderiv I 𝓘(ℝ, ℝ) F x ≠ 0 := by
  obtain ⟨N, â, hNo, hZN, hNO, hâ, hâpos, hâa⟩ :=
    exists_pos_eq_near_ZSP35 (isClosed_eq hG.continuous continuous_const) hO hzero ha hapos
  have hinv : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => (â x)⁻¹) :=
    hâ.inv₀ fun x => (hâpos x).ne'
  have hFeq : ∀ x, G x * (â x)⁻¹ = 0 ↔ G x = 0 := fun x => by
    rw [mul_eq_zero, or_iff_left (inv_ne_zero (hâpos x).ne')]
  refine ⟨fun x => G x * (â x)⁻¹, N, hNo, hZN, hNO, hG.mul hinv, fun x hx => ?_, ?_, ?_,
    fun x hx => ?_⟩
  · have hxO : x ∈ O := hNO (subset_closure hx)
    change G x * (â x)⁻¹ = r x
    rw [hâa x hx, hfactor x hxO]
    field_simp [(hapos x hxO).ne']
  · ext x
    simp only [mem_ofPred_eq]
    rw [← div_eq_mul_inv, div_nonpos_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact absurd h (not_le.mpr (hâpos x))
      · exact h
    · exact fun h => Or.inr ⟨h, (hâpos x).le⟩
  · ext x
    exact hFeq x
  · have h0 : G x = 0 := (hFeq x).mp hx
    rw [mfderiv_mul_of_eq_zero_ZSP35 ((hG x).mdifferentiableAt (by simp))
      ((hinv x).mdifferentiableAt (by simp)) h0]
    exact smul_ne_zero (inv_ne_zero (hâpos x).ne') (hreg x h0)

end DifferentialGeometry.Topology.Manifold
