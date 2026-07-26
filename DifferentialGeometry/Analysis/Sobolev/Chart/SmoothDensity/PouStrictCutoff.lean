import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Strict outer cutoffs for a subordinate smooth partition of unity

This file packages the second cutoff in a standard two-cutoff localization.
If a smooth partition of unity `rho` is subordinate to inner open sets `U i`,
and `U i` is contained in a larger open set `V i`, then every partition
function has a smooth outer cutoff which is one near its topological support
and whose own topological support lies in `V i`.

The statement is deliberately independent of charts and metrics. A later
finite small-chart construction supplies `U` and `V`; this lemma supplies the
outer cutoffs needed to pull non-compact Euclidean heat evolutions back to the
manifold without losing the exact partition identity on the inner carriers.
-/

noncomputable section

open Set Topology Bundle Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [I.Boundaryless]

omit [T2Space M] [NormalSpace M] [SigmaCompactSpace M] in
private lemma tsupport_subset_of_zero_compl
    {f : M → ℝ} {V : Set M} (hf : ∀ᶠ x in nhdsSet Vᶜ, f x = 0) :
    tsupport f ⊆ V := by
  rw [eventually_nhdsSet_iff_exists] at hf
  obtain ⟨W, hWopen, hVcomplW, hfW⟩ := hf
  have hsupp : Function.support f ⊆ Wᶜ := by
    intro x hx
    by_contra hxW
    exact hx (hfW x (by simpa using hxW))
  have htop : tsupport f ⊆ Wᶜ :=
    closure_minimal hsupp hWopen.isClosed_compl
  have hWV : Wᶜ ⊆ V := by
    intro x hx
    by_contra hxV
    exact hx (hVcomplW hxV)
  exact htop.trans hWV

omit [I.Boundaryless] in
/-- A closed function carrier inside an open set admits a smooth strict
cutoff. The cutoff is one near the carrier, vanishes near the complement,
takes values in `[0,1]`, and has support in the prescribed open set. -/
theorem exists_strict_cutoff
    (f : M → ℝ) (V : Set M) (hVopen : IsOpen V)
    (hsupp : tsupport f ⊆ V) :
    ∃ χ : M → ℝ,
      ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ χ ∧
      (∀ᶠ x in nhdsSet (tsupport f), χ x = 1) ∧
      (∀ x, χ x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ᶠ x in nhdsSet Vᶜ, χ x = 0) ∧
      tsupport χ ⊆ V := by
  classical
  have hdisj : Disjoint Vᶜ (tsupport f) :=
    Set.disjoint_compl_left_iff_subset.mpr hsupp
  let χb : C^∞⟮I, M; ℝ⟯ :=
    ((Classical.choose
      (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
        (n := (⊤ : ℕ∞)) hVopen.isClosed_compl
        (isClosed_tsupport f) hdisj)) : C^∞⟮I, M; ℝ⟯)
  have hχb := Classical.choose_spec
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞)) hVopen.isClosed_compl
      (isClosed_tsupport f) hdisj)
  refine ⟨fun x => ((χb : C^∞⟮I, M; ℝ⟯) : M → ℝ) x,
    χb.contMDiff, hχb.2.1, hχb.2.2, hχb.1, ?_⟩
  exact tsupport_subset_of_zero_compl hχb.1

omit [I.Boundaryless] in
/-- A partition subordinate to inner sets `U i`, with `U i ⊆ V i` and each
`V i` open, admits smooth outer cutoffs. Each cutoff is `[0,1]`-valued, is
identically one on a neighborhood of the corresponding partition carrier,
vanishes on a neighborhood of `(V i)ᶜ`, and has topological support in `V i`.

This is the reusable double-cutoff separation lemma: the partition function is
the inner cutoff and the produced function is the outer cutoff. -/
theorem exists_pou_cutoff
    {ι : Type*} {s : Set M}
    (ρ : SmoothPartitionOfUnity ι I M s)
    (U V : ι → Set M)
    (hρU : ρ.IsSubordinate U)
    (hUV : ∀ i, U i ⊆ V i)
    (hVopen : ∀ i, IsOpen (V i)) :
    ∃ χ : ι → M → ℝ,
      (∀ i, ContMDiff I (modelWithCornersSelf ℝ ℝ) ∞ (χ i)) ∧
      (∀ i, ∀ᶠ x in nhdsSet
        (tsupport ((ρ i : C^∞⟮I, M; ℝ⟯) : M → ℝ)), χ i x = 1) ∧
      (∀ i x, χ i x ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, ∀ᶠ x in nhdsSet ((V i)ᶜ), χ i x = 0) ∧
      ∀ i, tsupport (χ i) ⊆ V i := by
  classical
  have hdisj : ∀ i,
      Disjoint ((V i)ᶜ)
        (tsupport ((ρ i : C^∞⟮I, M; ℝ⟯) : M → ℝ)) := by
    intro i
    exact Set.disjoint_compl_left_iff_subset.mpr ((hρU i).trans (hUV i))
  let χb : ι → C^∞⟮I, M; ℝ⟯ := fun i =>
    ((Classical.choose
      (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
        (n := (⊤ : ℕ∞)) (hVopen i).isClosed_compl
        (isClosed_tsupport _) (hdisj i))) : C^∞⟮I, M; ℝ⟯)
  have hχb : ∀ i,
      (∀ᶠ x in nhdsSet ((V i)ᶜ),
        ((χb i : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) ∧
      (∀ᶠ x in nhdsSet
        (tsupport ((ρ i : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
        ((χb i : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1) ∧
      ∀ x, ((χb i : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈ Set.Icc (0 : ℝ) 1 := by
    intro i
    exact Classical.choose_spec
      (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
        (n := (⊤ : ℕ∞)) (hVopen i).isClosed_compl
        (isClosed_tsupport _) (hdisj i))
  refine ⟨fun i => ((χb i : C^∞⟮I, M; ℝ⟯) : M → ℝ), ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (χb i).contMDiff
  · intro i
    exact (hχb i).2.1
  · intro i x
    exact (hχb i).2.2 x
  · intro i
    exact (hχb i).1
  · intro i
    exact tsupport_subset_of_zero_compl (hχb i).1

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
