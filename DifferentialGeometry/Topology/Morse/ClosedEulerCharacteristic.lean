import DifferentialGeometry.Topology.Morse.FiniteBandEuler
import DifferentialGeometry.Topology.Morse.RelativePerturbationGlobal
import DifferentialGeometry.Topology.Morse.Excellent

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace DifferentialGeometry.Morse
variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M] [CompactSpace M]

theorem finiteHomologyType_and_eulerChar_of_finite_morse
    (K : Type) [Field K] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hfinite : {x | IsCriticalPointAt I f x}.Finite)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x)
    (hinj : InjOn f {x | IsCriticalPointAt I f x}) :
    DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
      DifferentialGeometry.Homology.eulerChar K (TopCat.of M) =
        ∑ p ∈ hfinite.toFinset, (-1 : ℤ) ^ sigNeg (chartHessianAt
          (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  obtain ⟨A,hA⟩ := (isCompact_range hf.continuous).bddAbove
  have hbelow (x : M) : f x < A + 1 := lt_of_le_of_lt (hA (mem_range_self x)) (lt_add_one A)
  have htop : sublevel f (A + 1) = univ := eq_univ_of_forall fun x => (hbelow x).le
  let eTop : SublevelSpace f (A + 1) ≃ₜ M :=
    (Homeomorph.setCongr htop).trans (Homeomorph.Set.univ M)
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  let e : E ≃L[ℝ] MorseModel (m + 1) :=
    ((Module.finBasis ℝ E).reindex (finCongr hm)).equivFunL
  obtain ⟨hfin,hχ⟩ := finiteHomologyType_and_eulerChar_of_finite_morse_sublevel I K e
    hf (A + 1) (htop ▸ isCompact_univ) (fun _ _ => BoundarylessManifold.isInteriorPoint)
    hfinite hnd hinj (fun x _ => hbelow x)
  exact ⟨(DifferentialGeometry.Homology.finiteHomologyType_iff_of_homeomorph K
      (X := TopCat.of (SublevelSpace f (A + 1))) (Y := TopCat.of M) eTop).mp hfin,
    (DifferentialGeometry.Homology.eulerChar_eq_of_homeomorph K eTop).symm.trans hχ⟩

theorem exists_morse_eulerChar :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) ∧
      InjOn f {x | IsCriticalPointAt I f x} ∧
      ∃ hfinite : {x | IsCriticalPointAt I f x}.Finite,
        ∀ (K : Type) [Field K], DifferentialGeometry.Homology.finiteHomologyType K (TopCat.of M) ∧
          DifferentialGeometry.Homology.eulerChar K (TopCat.of M) =
            ∑ p ∈ hfinite.toFinset, (-1 : ℤ)^sigNeg (chartHessianAt
              (fun y => f ((extChartAt I p).symm y)) (extChartAt I p p)) := by
  obtain ⟨g,hg,_,hgpos,hgnd,hgfin⟩ := exists_positive_relative_morse
    (I := I) (f := fun _ : M => (1 : ℝ)) contMDiff_const
    (K := univ) (U := univ) (S := univ) isCompact_univ isOpen_univ (Subset.refl _)
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (fun _ _ => mem_univ _)
    (Subset.refl _) (fun _ _ => zero_lt_one)
  obtain ⟨f,hf,_,_,hcrit,hinj,hnd,_⟩ := exists_positive_relative_excellent_morse hg hgfin
    (fun x hx => (hgnd x hx).2) (U := univ) (S := univ) isOpen_univ (subset_univ _)
    (fun _ _ => BoundarylessManifold.isInteriorPoint) (Subset.refl _) hgpos
  have hfinite : {x | IsCriticalPointAt I f x}.Finite := hcrit.symm ▸ hgfin
  refine ⟨f,hf,hnd,hinj,hfinite,?_⟩
  intro K instK
  exact finiteHomologyType_and_eulerChar_of_finite_morse I K hf hfinite hnd hinj

end DifferentialGeometry.Morse
