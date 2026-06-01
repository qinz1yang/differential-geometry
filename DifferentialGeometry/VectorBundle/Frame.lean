/-
Authors: Jack McCarthy
-/
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Extension of Local Frames to Global Sections

Given a local frame of a smooth vector bundle on a neighborhood of a point, the frame sections
can be extended to smooth global sections that agree with the frame near the point.

## Main Results

* `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd` : given a C^n local frame `{sᵢ}` on an
  open neighborhood `u` of `p`, there exist C^n global sections `{sᵢ'}` that agree with `{sᵢ}`
  on a neighborhood of `p`.
* `exists_contMDiffSection_eqOn_nhd` : the underlying extension lemma without a local-frame
  hypothesis — any family of sections that is C^n on an open neighborhood of `p` admits
  C^n global extensions agreeing with it near `p`.

## Tags

local frame, vector bundle, smooth section, extension
-/

set_option autoImplicit false

open scoped Manifold Topology ContDiff
open Bundle Filter

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F]
  {n : ℕ∞}
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, IsScalarTower ℝ 𝕜 (V x)]
  [VectorBundle ℝ F V]

variable {ι : Type*} {s : ι → (x : M) → V x} {u : Set M} {p : M}

/-- Given a family of sections `{sᵢ}` that are each C^n on an open neighborhood `u` of `p`,
there exist C^n global sections `{sᵢ'}` that agree with `{sᵢ}` on a neighborhood of `p`.

This is the underlying extension lemma behind `IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd`.
It makes no linear-independence or spanning assumption on the family, so it also applies to
`𝕜`-local frames of a bundle with `𝕜`-fiber structure (where `𝕜 : RCLike`): the caller supplies
smoothness of each section directly and frame-ness is not consulted. -/
theorem exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I] [IsManifold I ∞ M] [T2Space M]
    (hs : ∀ i, CMDiff[u] n (T% (s i))) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  -- Obtain a smooth bump function χ at p with tsupport χ ⊆ u
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  -- Define global sections: s'ᵢ(x) = χ(x) • sᵢ(x)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · -- Smoothness: χ is C^∞ globally, sᵢ is C^n on u, and tsupport χ ⊆ u
    exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs i)
  · -- χ = 1 near p, so s'ᵢ = sᵢ near p
    filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]

/-- Given a C^n local frame `{sᵢ}` on an open neighborhood `u` of `p`, there exist
C^n global sections `{sᵢ'}` that agree with `{sᵢ}` on a neighborhood of `p` -/
theorem IsLocalFrameOn.exists_contMDiffSection_eqOn_nhd
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [ContMDiffVectorBundle n F V I] [IsManifold I ∞ M] [T2Space M]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hp : p ∈ u) :
    ∃ (s' : ι → Cₛ^n⟮I; F, V⟯), ∀ᶠ x in 𝓝 p, ∀ i, s' i x = s i x := by
  -- Obtain a smooth bump function χ at p with tsupport χ ⊆ u
  obtain ⟨χ, -, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) p).mem_iff.mp (hu.mem_nhds hp)
  -- Define global sections: s'ᵢ(x) = χ(x) • sᵢ(x)
  refine ⟨fun i => ⟨fun x => χ x • s i x, ?_⟩, ?_⟩
  · -- Smoothness: χ is C^∞ globally, sᵢ is C^n on u, and tsupport χ ⊆ u
    exact (χ.contMDiff.of_le (by exact_mod_cast le_top)).contMDiffOn.smul_section_of_tsupport
      hu hχ (hs.contMDiffOn i)
  · -- χ = 1 near p, so s'ᵢ = sᵢ near p
    filter_upwards [χ.eventuallyEq_one] with x hx i
    simp [hx]
