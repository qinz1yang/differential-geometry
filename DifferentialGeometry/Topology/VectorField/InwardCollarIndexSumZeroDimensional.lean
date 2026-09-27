import DifferentialGeometry.Topology.VectorField.InwardCollarIndexZeroDimensional
import DifferentialGeometry.Topology.VectorField.IndexSumAddedZeros

set_option autoImplicit false
noncomputable section
open Set Bundle Filter Manifold TopologicalSpace
open scoped ContDiff Topology
namespace DifferentialGeometry.VectorField

theorem interiorIndexSum_inwardCollar_patch_zeroDimensional
    {E H H' B M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace B] [ChartedSpace H B] [TopologicalSpace M] [ChartedSpace H' M]
    (J : ModelWithCorners ℝ E H)
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 1)) H')
    [IsManifold J 1 B] [IsManifold I 1 M]
    {ε a : ℝ} [Fact ((0 : ℝ) < ε)] (ha : 0 < a) (haε : a ≤ ε)
    (S : Opens (B × Icc (0 : ℝ) ε)) (Y : Opens M)
    (e : Diffeomorph (J.prod (𝓡∂ 1)) I S Y ∞)
    (V : ∀ x : M, TangentSpace I x)
    (T : ∀ p : B, TangentSpace J p) (b : B → ℝ)
    (L : ∀ q : S, TangentSpace (J.prod (𝓡∂ 1)) q)
    (hL : ∀ p : S, p.val.2.val ≤ a → L p =
      (T p.val.1, (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc p.val.2).symm
        (-a * (collarExtension T b collarTransition (p.val.1, 1 - p.val.2.val / a)).2)))
    (hheight : ∀ q : S, L q = 0 → q.val.2.val ∈ Ioo (a / 3) (2 * a / 3))
    (hbij : BijOn (fun q : S => q.val.1) {q | L q = 0} {p | T p = 0 ∧ b p < 0})
    (hb : ContMDiff J 𝓘(ℝ, ℝ) 1 b)
    (hTi : ∀ p, T p = 0 → HasContinuousIsolatedZero J T p)
    (hVf : {x | V x = 0}.Finite)
    (hVi : ∀ x, V x = 0 → HasContinuousIsolatedZero I V x)
    (hVI : ∀ x, V x = 0 → I.IsInteriorPoint x) :
    let G := patchThroughDiffeomorph Y e V L
    ∀ (hGf : {x | G x = 0}.Finite)
      (hGi : ∀ x, G x = 0 → HasContinuousIsolatedZero I G x)
      (hGI : ∀ x, G x = 0 → I.IsInteriorPoint x),
      {x | G x = 0} = (fun q : S => (e q).val) '' {q | L q = 0} ∪ {x | V x = 0} →
      Disjoint ((fun q : S => (e q).val) '' {q | L q = 0}) {x | V x = 0} →
      (∀ x, V x = 0 → G =ᶠ[𝓝 x] V) →
      interiorIndexSum I G hGf hGi hGI = interiorIndexSum I V hVf hVi hVI +
        (∑ᶠ _ : {p | T p = 0 ∧ b p < 0}, (1 : ℤ)) := by
  intro G hGf hGi hGI hzero hdis hgerm
  let j : S → M := fun q => (e q).val
  let C := j '' {q | L q = 0}
  have hj : BijOn j {q | L q = 0} {x | G x = 0 ∧ x ∈ C} := by
    refine ⟨?_, ?_, ?_⟩
    · intro q hq
      exact ⟨(patchThroughDiffeomorph_eq_zero_iff Y e V L q).mpr hq, ⟨q, hq, rfl⟩⟩
    · intro q _ r _ he
      exact e.injective (Subtype.ext he)
    · rintro x ⟨_, q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
  have hnew : interiorIndexSumOn I G hGf hGi hGI C =
      (∑ᶠ _ : {p | T p = 0 ∧ b p < 0}, (1 : ℤ)) := by
    let ej := hj.equiv j
    let ep := hbij.equiv (fun q : S => q.val.1)
    rw [interiorIndexSumOn_eq_finsum]
    rw [← finsum_comp_equiv ej (f := fun x : {x | G x = 0 ∧ x ∈ C} =>
      interiorIndex I G x (hGi x x.property.1) (hGI x x.property.1))]
    erw [← finsum_comp_equiv ep (f := fun _ : {p | T p = 0 ∧ b p < 0} =>
      (1 : ℤ))]
    apply finsum_congr
    intro q
    have ht := hheight q q.property
    have hp := hbij.mapsTo q.property
    obtain ⟨_, _, hi⟩ := exists_inwardCollar_patch_index_zeroDimensional J I ha.ne' S Y e V T b L hL q
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (by linarith [ht.2])
      (hTi q.val.val.1 hp.1) (hb q.val.val.1) hp.2.ne q.property
    exact hi
  exact (interiorIndexSum_eq_add_of_added_zeros I V G hVf hVi hVI hGf hGi hGI C hzero hdis hgerm).trans
    (congrArg (fun z => interiorIndexSum I V hVf hVi hVI + z) hnew)

end DifferentialGeometry.VectorField
