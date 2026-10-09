import DifferentialGeometry.Analysis.Calculus.Derivative.VariableEndpointIntegral
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Fibre integrals and fibrewise height coordinates on `X × ℝ`

Suppliers of blueprint LC59 (`master207A.tex:23320`) on a product `X × ℝ` of a boundaryless smooth
manifold `X` with the line (product structure `J.prod 𝓘(ℝ, ℝ)`):

* `contMDiffOn_fiberIntegral`: if `w` is smooth on an open `Ω ⊆ X × ℝ` and the vertical segments
  from height `c` to the points of an open `U` lie in `Ω`, then `z ↦ ∫_c^{z.2} w(z.1, s) ds` is
  smooth on `U` (chart reduction to `contDiffOn_intervalIntegral_of_segment_subset`);
* `isInvertible_fst_prod_of_apply_ne_zero`: the triangular map `(v, s) ↦ (v, L (v, s))` is a
  linear isomorphism when `L (0, 1) ≠ 0`;
* `isLocalDiffeomorphAt_fst_prodMk`: `z ↦ (z.1, Q z)` is a local diffeomorphism at every point
  where `Q` is smooth and its fibre derivative `∂_u Q` is nonzero (inverse function theorem of the
  tree, `isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

/-- **Triangular linear isomorphisms.** `(v, s) ↦ (v, L (v, s))` is invertible when the last
diagonal entry `L (0, 1)` is nonzero. -/
theorem isInvertible_fst_prod_of_apply_ne_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : F × ℝ →L[ℝ] ℝ) (hL : L (0, 1) ≠ 0) :
    ((ContinuousLinearMap.fst ℝ F ℝ).prod L).IsInvertible := by
  set d := L (0, 1) with hd
  have hsplit : ∀ (v : F) (s : ℝ), L (v, s) = L (v, 0) + s * d := by
    intro v s
    have hvs : ((v, s) : F × ℝ) = (v, 0) + s • ((0 : F), (1 : ℝ)) := by
      ext <;> simp
    rw [hvs, map_add, map_smul, smul_eq_mul]
  let S : F × ℝ →L[ℝ] F × ℝ :=
    (ContinuousLinearMap.fst ℝ F ℝ).prod (d⁻¹ • (ContinuousLinearMap.snd ℝ F ℝ -
      L.comp ((ContinuousLinearMap.inl ℝ F ℝ).comp (ContinuousLinearMap.fst ℝ F ℝ))))
  have hS : ∀ p : F × ℝ, S p = (p.1, d⁻¹ * (p.2 - L (p.1, 0))) := by
    intro p
    rfl
  refine ⟨ContinuousLinearEquiv.equivOfInverse ((ContinuousLinearMap.fst ℝ F ℝ).prod L) S
    ?_ ?_, rfl⟩
  · rintro ⟨v, s⟩
    rw [hS]
    change ((v, d⁻¹ * (L (v, s) - L (v, 0))) : F × ℝ) = (v, s)
    rw [hsplit v s]
    congr 1
    field_simp
    ring
  · rintro ⟨v, t⟩
    rw [hS]
    change ((v, L (v, d⁻¹ * (t - L (v, 0)))) : F × ℝ) = (v, t)
    rw [hsplit]
    congr 1
    field_simp
    ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HX : Type*} [TopologicalSpace HX] {J : ModelWithCorners ℝ F HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]

/-- **Fibre integrals on `X × ℝ` are smooth.** If `w` is smooth on an open `Ω ⊆ X × ℝ` and, for
every point `z` of the open set `U`, the vertical segment from `(z.1, c)` to `z` lies in `Ω`, then
`z ↦ ∫_c^{z.2} w(z.1, s) ds` is smooth on `U`. -/
theorem contMDiffOn_fiberIntegral [IsManifold J ∞ X] [J.Boundaryless] {Ω : Set (X × ℝ)}
    (hΩ : IsOpen Ω) {w : X × ℝ → ℝ} (hw : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ w Ω)
    (c : ℝ) {U : Set (X × ℝ)} (hU : IsOpen U)
    (hUΩ : ∀ z ∈ U, ∀ s ∈ uIcc c z.2, (z.1, s) ∈ Ω) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun z : X × ℝ => ∫ s in c..z.2, w (z.1, s)) U := by
  intro z₀ hz₀
  refine ContMDiffAt.contMDiffWithinAt ?_
  set φ := extChartAt J z₀.1 with hφ
  let ψ : F × ℝ → X × ℝ := fun q => (φ.symm q.1, q.2)
  have hT : IsOpen (φ.target ×ˢ (univ : Set ℝ)) :=
    (isOpen_extChartAt_target (I := J) z₀.1).prod isOpen_univ
  have hψ : ContMDiffOn (𝓘(ℝ, F).prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞ ψ
      (φ.target ×ˢ (univ : Set ℝ)) := by
    refine ((contMDiffOn_extChartAt_symm (I := J) z₀.1).comp contMDiffOn_fst ?_).prodMk
      contMDiffOn_snd
    exact fun _ hq => hq.1
  have hΩ' : IsOpen ((φ.target ×ˢ (univ : Set ℝ)) ∩ ψ ⁻¹' Ω) :=
    hψ.continuousOn.isOpen_inter_preimage hT hΩ
  have hU' : IsOpen ((φ.target ×ˢ (univ : Set ℝ)) ∩ ψ ⁻¹' U) :=
    hψ.continuousOn.isOpen_inter_preimage hT hU
  have hw' : ContDiffOn ℝ ∞ (w ∘ ψ) ((φ.target ×ˢ (univ : Set ℝ)) ∩ ψ ⁻¹' Ω) := by
    have hcomp := hw.comp (hψ.mono inter_subset_left) (fun _ hq => hq.2)
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcomp
  have hQ' := DifferentialGeometry.Analysis.contDiffOn_intervalIntegral_of_segment_subset hΩ' hw'
    c hU' (fun q hq s hs => ⟨⟨hq.1.1, mem_univ s⟩, hUΩ (ψ q) hq.2 s hs⟩)
  have hsrc : z₀.1 ∈ φ.source := mem_extChartAt_source (I := J) z₀.1
  have hmem : (φ z₀.1, z₀.2) ∈ (φ.target ×ˢ (univ : Set ℝ)) ∩ ψ ⁻¹' U := by
    refine ⟨⟨φ.map_source hsrc, mem_univ _⟩, ?_⟩
    change (φ.symm (φ z₀.1), z₀.2) ∈ U
    rw [φ.left_inv hsrc]
    exact hz₀
  have hat : ContMDiffAt 𝓘(ℝ, F × ℝ) 𝓘(ℝ, ℝ) ∞
      (fun q : F × ℝ => ∫ s in c..q.2, (w ∘ ψ) (q.1, s)) (φ z₀.1, z₀.2) :=
    (hQ'.contDiffAt (hU'.mem_nhds hmem)).contMDiffAt
  have hchart : ContMDiffAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F × ℝ) ∞
      (fun z : X × ℝ => (φ z.1, z.2)) z₀ :=
    ((contMDiffAt_extChartAt (I := J) (x := z₀.1)).comp z₀ contMDiffAt_fst).prodMk_space
      contMDiffAt_snd
  refine (hat.comp z₀ hchart).congr_of_eventuallyEq ?_
  have hnhds : {z : X × ℝ | z.1 ∈ φ.source} ∈ 𝓝 z₀ :=
    continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_source (I := J) z₀.1).mem_nhds hsrc)
  filter_upwards [hnhds] with z hz
  change (∫ s in c..z.2, w (z.1, s)) = ∫ s in c..z.2, w (φ.symm (φ z.1), s)
  rw [φ.left_inv hz]

/-- **Fibrewise height coordinates are local diffeomorphisms.** If `Q` is smooth on an open
`U ⊆ X × ℝ` and its fibre derivative at `z ∈ U` is nonzero, then `z ↦ (z.1, Q z)` is a local
diffeomorphism at `z`. -/
theorem isLocalDiffeomorphAt_fst_prodMk [CompleteSpace F] [IsManifold J ∞ X] [J.Boundaryless]
    {Q : X × ℝ → ℝ} {U : Set (X × ℝ)} (hU : IsOpen U)
    (hQ : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Q U) {z : X × ℝ} (hz : z ∈ U) {d : ℝ}
    (hderiv : HasDerivAt (fun s => Q (z.1, s)) d z.2) (hd : d ≠ 0) :
    IsLocalDiffeomorphAt (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) ∞ (fun z => (z.1, Q z)) z := by
  have hmdQ : MDifferentiableAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Q z :=
    (hQ.contMDiffAt (hU.mem_nhds hz)).mdifferentiableAt (by simp)
  let L : F × ℝ →L[ℝ] ℝ := mfderiv (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Q z
  have hQL : HasMFDerivAt (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Q z L := hmdQ.hasMFDerivAt
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (J.prod 𝓘(ℝ, ℝ)) (fun s : ℝ => (z.1, s)) z.2
      ((0 : ℝ →L[ℝ] F).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ)) (I' := J) z.1 z.2).prodMk (hasMFDerivAt_id z.2)
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => Q (z.1, s)) z.2
      (L.comp ((0 : ℝ →L[ℝ] F).prod (ContinuousLinearMap.id ℝ ℝ))) :=
    hQL.comp z.2 hγ
  have hder' : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s => Q (z.1, s)) z.2
      ((1 : ℝ →L[ℝ] ℝ).smulRight d) :=
    hderiv.hasFDerivAt.hasMFDerivAt
  have huniq := hcomp.mfderiv.symm.trans hder'.mfderiv
  have hL01 : L (0, 1) = d := by
    have h1 := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) huniq
    change L ((0 : F), (1 : ℝ)) = (1 : ℝ) • d at h1
    rw [one_smul] at h1
    exact h1
  have hD : mfderiv (J.prod 𝓘(ℝ, ℝ)) (J.prod 𝓘(ℝ, ℝ)) (fun z => (z.1, Q z)) z =
      (ContinuousLinearMap.fst ℝ F ℝ).prod L :=
    ((hasMFDerivAt_fst z).prodMk hQL).mfderiv
  refine DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    hU hz (contMDiffOn_fst.prodMk hQ) ?_
  rw [hD]
  exact isInvertible_fst_prod_of_apply_ne_zero L (hL01.symm ▸ hd)

end DifferentialGeometry.Topology.Manifold
