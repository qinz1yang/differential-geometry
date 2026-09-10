import DifferentialGeometry.Topology.Morse.RelativePerturbationFamily
import DifferentialGeometry.Topology.Morse.HessianNaturality
import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization
import DifferentialGeometry.Topology.Manifold.InteriorChart

set_option autoImplicit false
noncomputable section
open Set Filter Function
open scoped Manifold ContDiff Topology
namespace Poincare.Morse
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]


theorem exists_contDiff_extensions_on_nhds {ι : Type*} {g : ι → E → ℝ}
    {S : Set E} (hS : IsOpen S) (hg : ∀ i, ContDiffOn ℝ ∞ (g i) S) {x : E} (hx : x ∈ S) :
    ∃ (W : Set E) (F : ι → E → ℝ), IsOpen W ∧ x ∈ W ∧ W ⊆ S ∧
      ∀ i, ContDiff ℝ ∞ (F i) ∧ HasCompactSupport (F i) ∧ tsupport (F i) ⊆ S ∧ EqOn (F i) (g i) W := by
  obtain ⟨b,_,hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp (hS.mem_nhds hx)
  let W := interior {y : E | b y = 1} ∩ S
  refine ⟨W,fun i y => b y * g i y,isOpen_interior.inter hS,
    ⟨mem_interior_iff_mem_nhds.mpr b.eventuallyEq_one,hx⟩,inter_subset_right,fun i => ?_⟩
  have hsupp : tsupport (fun y => b y * g i y) ⊆ tsupport b := tsupport_mul_subset_left
  refine ⟨?_,b.hasCompactSupport.mono (support_mul_subset_left _ _),hsupp.trans hb,?_⟩
  · apply contMDiff_iff_contDiff.mp
    apply contMDiff_of_tsupport
    intro y hy
    exact b.contMDiffAt.mul ((hg i).contDiffAt (hS.mem_nhds (hb (hsupp hy)))).contMDiffAt
  · intro y hy
    have hb1 : b y = 1 := interior_subset (s := {y : E | b y = 1}) hy.1
    change b y * g i y = g i y
    rw [hb1,one_mul]

section Manifold
variable {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]


theorem exists_contDiff_interiorChart_extensions {ι : Type*} {g : ι → M → ℝ}
    (hg : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (g i)) {x : M} (hx : I.IsInteriorPoint x) :
    ∃ (W : Set E) (F : ι → E → ℝ), IsOpen W ∧
      Poincare.Manifold.interiorChart I ∞ x x ∈ W ∧
      W ⊆ (Poincare.Manifold.interiorChart I ∞ x).target ∧
      ∀ i, ContDiff ℝ ∞ (F i) ∧ HasCompactSupport (F i) ∧
        tsupport (F i) ⊆ (Poincare.Manifold.interiorChart I ∞ x).target ∧
        EqOn (F i) (fun z => g i ((Poincare.Manifold.interiorChart I ∞ x).symm z)) W := by
  let c := Poincare.Manifold.interiorChart I ∞ x
  have hxc : x ∈ c.source := (Poincare.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  apply exists_contDiff_extensions_on_nhds c.open_target _ (c.map_source hxc)
  intro i
  apply contMDiffOn_iff_contDiffOn.mp
  exact (hg i).comp_contMDiffOn c.symm.contMDiffOn

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem fderiv_scalar_partialDiffeomorph_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {z : E} (hz : z ∈ c.target) :
    fderiv ℝ (fun w => f (c.symm w)) z =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f (c.symm z)).comp
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) I c.symm z) := by
  have hh := (hf.mdifferentiable (by simp) (c.symm z)).hasMFDerivAt.comp z
    (c.symm.mdifferentiableAt (by simp) hz).hasMFDerivAt
  have hd := hasMFDerivAt_iff_hasFDerivAt.mp hh
  have hd' : HasFDerivAt (fun w => f (c.symm w))
      ((show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f (c.symm z)).comp
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) I c.symm z)) z := by
    unfold HasFDerivAt at hd ⊢
    exact hd
  exact hd'.fderiv

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {z : E} (hz : z ∈ c.target) :
    fderiv ℝ (fun w => f (c.symm w)) z = 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f (c.symm z) = 0 := by
  let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  let D : E →L[ℝ] ℝ := mfderiv I 𝓘(ℝ, ℝ) f (c.symm z)
  have hL : L.IsInvertible := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph
    c.symm (by simp) hz
  have hd : fderiv ℝ (fun w => f (c.symm w)) z = D.comp L :=
    fderiv_scalar_partialDiffeomorph_symm hf c hz
  change _ ↔ D = 0
  rw [hd]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := hL.surjective v
    exact congrArg (fun T : E →L[ℝ] ℝ => T w) h
  · intro h
    rw [h,ContinuousLinearMap.zero_comp]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem parameterDifferential_partialDiffeomorph_symm {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {z : E} (hz : z ∈ c.target) (p : Fin n → ℝ) :
    parameterDifferential (I := 𝓘(ℝ, E)) (fun i w => φ i (c.symm w)) z p =
      (parameterDifferential (I := I) φ (c.symm z) p).comp
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) I c.symm z) := by
  let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  let F : Fin n → E →L[ℝ] ℝ := fun i => mfderiv I 𝓘(ℝ, ℝ) (φ i) (c.symm z)
  simp only [parameterDifferential_apply, mfderiv_eq_fderiv]
  change (∑ i, p i • fderiv ℝ (fun w => φ i (c.symm w)) z) = (∑ i, p i • F i).comp L
  rw [ContinuousLinearMap.finsetSum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [ContinuousLinearMap.smul_comp]
  exact congrArg (fun T : E →L[ℝ] ℝ => p i • T) (fderiv_scalar_partialDiffeomorph_symm (hφ i) c hz)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem surjective_parameterDifferential_partialDiffeomorph_symm {n : ℕ} {φ : Fin n → M → ℝ}
    (hφ : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (φ i)) (c : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞)
    {z : E} (hz : z ∈ c.target)
    (hreg : Surjective (parameterDifferential (I := I) φ (c.symm z))) :
    Surjective (parameterDifferential (I := 𝓘(ℝ, E)) (fun i w => φ i (c.symm w)) z) := by
  let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I c.symm z
  let D := (ContinuousLinearMap.compL ℝ E E ℝ).flip L
  have hL : L.IsInvertible := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph
    c.symm (by simp) hz
  have hD : Bijective D := by
    obtain ⟨e,he⟩ := hL
    change Bijective ((ContinuousLinearMap.compL ℝ E E ℝ).flip L)
    rw [← he]
    exact bijective_dual_precomp e
  have heq : parameterDifferential (I := 𝓘(ℝ, E)) (fun i w => φ i (c.symm w)) z =
      D.comp (parameterDifferential (I := I) φ (c.symm z)) := by
    apply ContinuousLinearMap.ext
    intro p
    exact parameterDifferential_partialDiffeomorph_symm hφ c hz p
  rw [heq]
  exact hD.2.comp hreg

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem bijective_hessian_partialDiffeomorph_chart_iff {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (c d : PartialDiffeomorph I 𝓘(ℝ, E) M E ∞) {x : M}
    (hcx : x ∈ c.source) (hdx : x ∈ d.source) (hcrit : mfderiv I 𝓘(ℝ, ℝ) f x = 0) :
    Bijective (fderiv ℝ (fderiv ℝ (fun z => f (d.symm z))) (d x)) ↔
      Bijective (fderiv ℝ (fderiv ℝ (fun z => f (c.symm z))) (c x)) := by
  let ψ := d.symm.trans c
  let g : E → ℝ := fun z => f (c.symm z)
  have hz : d x ∈ ψ.source := ⟨d.map_source hdx,
    (congrArg (fun y => y ∈ c.source) (d.left_inv hdx)).mpr hcx⟩
  have hψx : ψ (d x) = c x := congrArg c (d.left_inv hdx)
  have hg : ContDiffAt ℝ 2 g (ψ (d x)) := by
    rw [hψx]
    exact (((hf.comp_contMDiffOn c.symm.contMDiffOn).contMDiffAt
      (c.open_target.mem_nhds (c.map_source hcx))).contDiffAt).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hψ : ContDiffAt ℝ 2 ψ (d x) :=
    ((contMDiffOn_iff_contDiffOn.mp ψ.contMDiffOn).contDiffAt
      (ψ.open_source.mem_nhds hz)).of_le (show (2 : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  have hzero : fderiv ℝ g (ψ (d x)) = 0 := by
    rw [hψx]
    apply (fderiv_scalar_partialDiffeomorph_symm_eq_zero_iff hf c (c.map_source hcx)).mpr
    let Df : M → E →L[ℝ] ℝ := fun y => mfderiv I 𝓘(ℝ, ℝ) f y
    change Df (c.symm (c x)) = 0
    exact (congrArg Df (c.left_inv hcx)).trans hcrit
  have hinv : (fderiv ℝ ψ (d x)).IsInvertible := by
    let L : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ψ (d x)
    have hL : L.IsInvertible := Poincare.VectorField.isInvertible_mfderiv_partialDiffeomorph ψ (by simp) hz
    have he : L = fderiv ℝ ψ (d x) := mfderiv_eq_fderiv
    rw [← he]
    exact hL
  have heq : (fun z => f (d.symm z)) =ᶠ[𝓝 (d x)] g ∘ ψ := by
    filter_upwards [ψ.open_source.mem_nhds hz] with z hz
    change f (d.symm z) = f (c.symm (c (d.symm z)))
    exact congrArg f (c.left_inv hz.2).symm
  rw [heq.fderiv.fderiv_eq]
  have hh := bijective_fderiv_fderiv_comp_at_critical_iff hg hψ hzero hinv
  simpa only [hψx] using hh

end Manifold
end Poincare.Morse
