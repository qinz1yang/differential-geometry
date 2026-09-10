import DifferentialGeometry.Topology.Morse.RelativePerturbationMorse
import DifferentialGeometry.Topology.Morse.RelativePerturbationAvoidance

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
namespace Poincare.Morse
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H M : Type} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem exists_open_isolated_criticalPoint {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x)
    (hnd : IsNondegenerateCriticalPointAt I f x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, IsCriticalPointAt I f y → y = x := by
  let c := Poincare.Manifold.interiorChart I ∞ x
  let g : E → ℝ := fun z => f (c.symm z)
  have hxc : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hg : ContDiffAt ℝ 2 g (c x) :=
    (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
      (c.open_target.mem_nhds (c.map_source hxc))).contDiffAt).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hinj : Injective (fderiv ℝ (fderiv ℝ g) (c x)) :=
    (separatingLeft_chartHessianAt_iff hg).mp hnd.2
  have hrank : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) := by
    rw [← (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq]
    exact Subspace.dual_finrank_eq.symm
  have hbij : Bijective (fderiv ℝ (fderiv ℝ g) (c x)) :=
    ⟨hinj,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩
  let e : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
    (LinearEquiv.ofBijective (fderiv ℝ (fderiv ℝ g) (c x)).toLinearMap hbij).toContinuousLinearEquiv
  have hd : HasStrictFDerivAt (fderiv ℝ g) (e : E →L[ℝ] (E →L[ℝ] ℝ)) (c x) :=
    (hg.fderiv_right (m := 1) (by norm_num)).hasStrictFDerivAt one_ne_zero
  let d := hd.toOpenPartialHomeomorph (fderiv ℝ g)
  have hxd : c x ∈ d.source := hd.mem_toOpenPartialHomeomorph_source
  refine ⟨c.source ∩ c ⁻¹' d.source,
    c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source d.open_source,
    ⟨hxc,hxd⟩,?_⟩
  intro y hy hcy
  have hzero : ∀ z ∈ c.source, IsCriticalPointAt I f z → fderiv ℝ g (c z) = 0 := by
    intro z hz hc
    apply (fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff hf c (c.map_source hz)).mpr
    let D : M → E →L[ℝ] ℝ := fun w => mfderiv I 𝓘(ℝ, ℝ) f w
    exact (congrArg D (c.left_inv hz)).trans hc
  apply c.toOpenPartialHomeomorph.injOn hy.1 hxc
  apply d.injOn hy.2 hxd
  exact (hzero y hy.1 hcy).trans (hzero x hxc hnd.1).symm


theorem exists_open_noncriticalPoint {f : M → ℝ} {x : M}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hx : I.IsInteriorPoint x)
    (hcrit : ¬ IsCriticalPointAt I f x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, ¬ IsCriticalPointAt I f y := by
  let φ : Fin 0 → M → ℝ := fun i => Fin.elim0 i
  have hevent := eventually_mfderiv_finitePerturbation_ne_zero (φ := φ) hf
    (fun i => Fin.elim0 i) hx hcrit
  have hcont : ContinuousAt (fun y : M => ((0 : Fin 0 → ℝ),y)) x :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have hnear : ∀ᶠ y in 𝓝 x, ¬ IsCriticalPointAt I f y := by
    have hh := hcont.eventually hevent
    filter_upwards [hh] with y hy
    intro hc
    apply hy
    let D : (M → ℝ) → E →L[ℝ] ℝ := fun u => mfderiv I 𝓘(ℝ, ℝ) u y
    exact (congrArg D (finitePerturbation_zero f φ)).trans hc
  obtain ⟨V,hV,hopen,hxV⟩ := mem_nhds_iff.mp hnear
  exact ⟨V,hopen,hxV,hV⟩


theorem finite_criticalPoints_of_isCompact {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {C : Set M} (hC : IsCompact C)
    (hCI : ∀ x ∈ C, I.IsInteriorPoint x)
    (hcrit : ∀ x, IsCriticalPointAt I f x → x ∈ C)
    (hnd : ∀ x, IsCriticalPointAt I f x → IsNondegenerateCriticalPointAt I f x) :
    {x : M | IsCriticalPointAt I f x}.Finite := by
  classical
  have hlocal : ∀ x : C, ∃ V : Set M, IsOpen V ∧ x.val ∈ V ∧
      ∀ y ∈ V, IsCriticalPointAt I f y → y = x.val := by
    intro x
    by_cases hx : IsCriticalPointAt I f x
    · exact exists_open_isolated_criticalPoint hf (hCI x x.property) (hnd x hx)
    · obtain ⟨V,hV,hxV,hreg⟩ := exists_open_noncriticalPoint hf (hCI x x.property) hx
      exact ⟨V,hV,hxV,fun y hy hc => (hreg y hy hc).elim⟩
  choose V hV hxV hprop using hlocal
  obtain ⟨s,hs⟩ := hC.elim_finite_subcover V hV
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩)
  apply (s.finite_toSet.image (fun x : C => x.val)).subset
  intro y hy
  obtain ⟨x,hxs,hyV⟩ := mem_iUnion₂.mp (hs (hcrit y hy))
  exact ⟨x,hxs,(hprop x y hyV hy).symm⟩

end Poincare.Morse
