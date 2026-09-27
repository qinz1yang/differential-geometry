import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.AEMeasurable

noncomputable section

open Bundle Filter Function MeasureTheory Set
open scoped Manifold ContDiff Topology

namespace Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

omit [CompleteSpace E] [SecondCountableTopology E] in
private theorem continuous_inverseChart_tangent (q : M) :
    Continuous (fun p : (extChartAt I q).target × E =>
      (⟨(extChartAt I q).symm p.1,
        mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (extChartAt I q).target p.1 p.2⟩ :
          TangentBundle I M)) := by
  let T := (extChartAt I q).target
  let A : T × E → TangentBundle 𝓘(ℝ, E) E := fun p => ⟨p.1, p.2⟩
  have hA : Continuous A :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hr := (contMDiffOn_extChartAt_symm (I := I) (n := 1) q).continuousOn_tangentMapWithin
    le_rfl (isOpen_extChartAt_target (I := I) q).uniqueMDiffOn
  have hA' : Continuous (fun p : T × E =>
      (⟨A p, p.1.2⟩ : {z : TangentBundle 𝓘(ℝ, E) E | z.proj ∈ T})) :=
    hA.subtype_mk _
  exact hr.domRestrict.comp hA'

private theorem aemeasurable_continuous_tangentMap_on_chart
    {μ : Measure ℝ} {Ω : Set ℝ} (hΩ : IsOpen Ω) (γ : ℝ → M) (hγ : ContinuousOn γ Ω)
    (hd : ∀ᵐ t ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (F : ℝ × TangentBundle I M → ℝ) (hF : ContinuousOn F (Ω ×ˢ univ)) (q : M) :
    AEMeasurable (fun t => F (t, ⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)⟩))
      (μ.restrict (Ω ∩ γ ⁻¹' (extChartAt I q).source)) := by
  borelize E
  let c := extChartAt I q
  let U := Ω ∩ γ ⁻¹' c.source
  let z : ℝ → E := c ∘ γ
  have hU : IsOpen U := hγ.isOpen_inter_preimage hΩ (isOpen_extChartAt_source q)
  have hz : ContinuousOn z U := (continuousOn_extChartAt (I := I) q).comp
    (hγ.mono inter_subset_left) (fun t ht => ht.2)
  let J : ℝ → ℝ := fun t => F (t, ⟨c.symm (z t),
    mfderivWithin 𝓘(ℝ, E) I c.symm c.target (z t) (fderiv ℝ z t 1)⟩)
  have hJ : AEMeasurable J (μ.restrict U) := by
    apply aemeasurable_restrict_of_measurable_subtype hU.measurableSet
    let G : Ω × (c.target × E) → ℝ := fun p => F (p.1, ⟨c.symm p.2.1,
      mfderivWithin 𝓘(ℝ, E) I c.symm c.target p.2.1 p.2.2⟩)
    have hG : Continuous G := hF.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_inverseChart_tangent q).comp continuous_snd))
      (fun p => ⟨p.1.2, mem_univ _⟩)
    have hz' : Continuous (fun t : U => (⟨z t, c.map_source t.2.2⟩ : c.target)) :=
      hz.domRestrict.subtype_mk _
    have hd' : Measurable (fun t : U => fderiv ℝ z t 1) :=
      (measurable_fderiv_apply_const ℝ z 1).comp measurable_subtype_coe
    have hj : Measurable (fun t : U =>
        ((⟨t, t.2.1⟩ : Ω), (⟨z t, c.map_source t.2.2⟩ : c.target), fderiv ℝ z t 1)) :=
      (continuous_subtype_val.subtype_mk _).measurable.prodMk (hz'.measurable.prodMk hd')
    exact hG.measurable.comp hj
  apply hJ.congr
  filter_upwards [hd.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),
    ae_restrict_mem hU.measurableSet] with t hdt ht
  have htchart : γ t ∈ c.source := ht.2
  have hc : MDifferentiableAt I 𝓘(ℝ, E) c (γ t) :=
    (contMDiffAt_extChartAt' (I := I) (n := 1)
      (by simpa only [c, extChartAt_source] using htchart)).mdifferentiableAt (by simp)
  have hdz : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) z t := hc.comp t hdt
  have heq : ∀ r ∈ U, γ r = (c.symm ∘ z) r := fun r hr => (c.left_inv hr.2).symm
  let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨t, (1 : ℝ)⟩
  have hcongr := tangentMapWithin_congr (I := 𝓘(ℝ, ℝ)) (I' := I) heq p ht
  have hchain := tangentMapWithin_comp_at (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (f := z) (g := c.symm) (s := U) (u := c.target) p
    ((contMDiffOn_extChartAt_symm (I := I) (n := 1) q _ (c.map_source ht.2)).mdifferentiableWithinAt (by simp))
    hdz.mdifferentiableWithinAt (fun r hr => c.map_source hr.2) (hU.uniqueMDiffWithinAt ht)
  have hmap := hcongr.trans hchain
  rw [tangentMapWithin_eq_tangentMap (hU.uniqueMDiffWithinAt ht) hdt,
    tangentMapWithin_eq_tangentMap (hU.uniqueMDiffWithinAt ht) hdz] at hmap
  have hval := congrArg (fun v : TangentBundle I M => F (t, v)) hmap
  simp only [p, tangentMap, tangentMapWithin, mfderiv_eq_fderiv] at hval
  convert! hval.symm using 1

theorem aemeasurable_continuous_tangentMap
    {μ : Measure ℝ} {Ω : Set ℝ} (hΩ : IsOpen Ω) (γ : ℝ → M) (hγ : ContinuousOn γ Ω)
    (hd : ∀ᵐ t ∂μ.restrict Ω, MDifferentiableAt 𝓘(ℝ, ℝ) I γ t)
    (F : ℝ × TangentBundle I M → ℝ) (hF : ContinuousOn F (Ω ×ˢ univ)) :
    AEMeasurable (fun t => F (t, ⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)⟩)) (μ.restrict Ω) := by
  classical
  let U : M → Set ℝ := fun q => Ω ∩ γ ⁻¹' (extChartAt I q).source
  have hU : ∀ q, IsOpen (U q) := fun q =>
    hγ.isOpen_inter_preimage hΩ (isOpen_extChartAt_source q)
  have hcover : Ω ⊆ ⋃ q, U q := fun t ht =>
    mem_iUnion.mpr ⟨γ t, ht, mem_extChartAt_source (γ t)⟩
  obtain ⟨s, hs, hcov⟩ := (isLindelof_iff_lindelofSpace.mpr
    (inferInstance : LindelofSpace Ω)).elim_countable_subcover U hU hcover
  let : Countable s := hs.to_subtype
  have heq : Ω = ⋃ q : s, U q := by
    apply Subset.antisymm
    · intro t ht
      obtain ⟨q, hqs, htq⟩ := mem_iUnion₂.mp (hcov ht)
      exact mem_iUnion.mpr ⟨⟨q, hqs⟩, htq⟩
    · exact iUnion_subset fun _ => inter_subset_left
  rw [heq]
  exact AEMeasurable.iUnion fun q : s =>
    aemeasurable_continuous_tangentMap_on_chart hΩ γ hγ hd F hF q

end Manifold
