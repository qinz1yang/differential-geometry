import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Irreducible
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BufferedSmoothCutCapTransition
import DifferentialGeometry.Topology.Manifold.Interval.Interior
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import DifferentialGeometry.Compat.Ch567.Geometry.Flow.RicciFlow.Surgery.Topology.WorldBridges

/-!
# Existence of the capped manifold for a spherical tube system

For every nonempty spherical tube system `T` in a closed oriented `3`-manifold there is a
spherical cut-cap transition whose tube system is exactly `T`. The tubes are reparametrized in
time by a smooth diffeomorphism `(-3, 3) → (-2, 2)` that is the identity on `[-5/4, 5/4]`; this
turns each tube into a buffered cylinder chart, and the finite capping construction of the
surgery library (`exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps`)
produces a transition for these charts. Its core, boundary spheres and outward normals agree
with those of `T`, so the transition is transported to one with tube system `T`. This proves
`SphereSystemCapping`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology Metric Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private def stretchBump (t : ℝ) : ℝ :=
  Real.smoothTransition (4 * t - 5) - Real.smoothTransition (-4 * t - 5)

private def stretch (t : ℝ) : ℝ := t + stretchBump t

private theorem contDiff_stretchBump : ContDiff ℝ ∞ stretchBump := by
  unfold stretchBump
  fun_prop

private theorem contDiff_stretch : ContDiff ℝ ∞ stretch := by
  unfold stretch
  exact contDiff_id.add contDiff_stretchBump

private theorem monotone_stretchBump : Monotone stretchBump := by
  intro s t hst
  unfold stretchBump
  have h₁ := Real.smoothTransition.monotone (show 4 * s - 5 ≤ 4 * t - 5 by linarith)
  have h₂ := Real.smoothTransition.monotone (show -4 * t - 5 ≤ -4 * s - 5 by linarith)
  linarith

private theorem stretchBump_eq_zero {t : ℝ} (h₁ : -(5 / 4) ≤ t) (h₂ : t ≤ 5 / 4) :
    stretchBump t = 0 := by
  unfold stretchBump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

private theorem abs_stretchBump_le (t : ℝ) : |stretchBump t| ≤ 1 := by
  unfold stretchBump
  have := Real.smoothTransition.nonneg (4 * t - 5)
  have := Real.smoothTransition.le_one (4 * t - 5)
  have := Real.smoothTransition.nonneg (-4 * t - 5)
  have := Real.smoothTransition.le_one (-4 * t - 5)
  rw [abs_le]
  constructor <;> linarith

private theorem stretch_two : stretch 2 = 3 := by
  unfold stretch stretchBump
  rw [Real.smoothTransition.one_of_one_le (by norm_num),
    Real.smoothTransition.zero_of_nonpos (by norm_num)]
  norm_num

private theorem stretch_neg_two : stretch (-2) = -3 := by
  unfold stretch stretchBump
  rw [Real.smoothTransition.zero_of_nonpos (by norm_num),
    Real.smoothTransition.one_of_one_le (by norm_num)]
  norm_num

private theorem strictMono_stretch : StrictMono stretch :=
  strictMono_id.add_monotone monotone_stretchBump

private theorem hasDerivAt_stretch (t : ℝ) :
    HasDerivAt stretch (1 + deriv stretchBump t) t :=
  (hasDerivAt_id t).add
    ((contDiff_stretchBump.differentiable (by simp)) t).hasDerivAt

private theorem surjective_stretch : Function.Surjective stretch := by
  refine contDiff_stretch.continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) tendsto_id)
    have := (abs_le.mp (abs_stretchBump_le t)).1
    unfold stretch
    simp only [id]
    linarith
  · refine tendsto_atBot_mono (fun t => ?_) (tendsto_atBot_add_const_right _ 1 tendsto_id)
    have := (abs_le.mp (abs_stretchBump_le t)).2
    unfold stretch
    simp only [id]
    linarith

private def stretchHomeomorph : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective stretch strictMono_stretch surjective_stretch).toHomeomorph

private def squeeze (t : ℝ) : ℝ := stretchHomeomorph.symm t

private theorem contDiff_squeeze : ContDiff ℝ ∞ squeeze :=
  stretchHomeomorph.contDiff_symm_deriv (f' := fun t => 1 + deriv stretchBump t)
    (fun t => by have := monotone_stretchBump.deriv_nonneg (x := t); positivity)
    hasDerivAt_stretch contDiff_stretch

private theorem stretch_squeeze (t : ℝ) : stretch (squeeze t) = t :=
  stretchHomeomorph.apply_symm_apply t

private theorem squeeze_stretch (t : ℝ) : squeeze (stretch t) = t :=
  stretchHomeomorph.symm_apply_apply t

private theorem squeeze_eq_self {t : ℝ} (h₁ : -(5 / 4) ≤ t) (h₂ : t ≤ 5 / 4) :
    squeeze t = t := by
  conv_lhs => rw [← add_zero t, ← stretchBump_eq_zero h₁ h₂]
  exact squeeze_stretch t

private theorem squeeze_mem {t : ℝ} (h₁ : -3 < t) (h₂ : t < 3) :
    -2 < squeeze t ∧ squeeze t < 2 := by
  constructor
  · rw [← strictMono_stretch.lt_iff_lt, stretch_squeeze, stretch_neg_two]; exact h₁
  · rw [← strictMono_stretch.lt_iff_lt, stretch_squeeze, stretch_two]; exact h₂

private theorem stretch_mem {t : ℝ} (h₁ : -2 < t) (h₂ : t < 2) :
    -3 < stretch t ∧ stretch t < 3 := by
  constructor
  · rw [← stretch_neg_two]; exact strictMono_stretch h₁
  · rw [← stretch_two]; exact strictMono_stretch h₂

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private def tubeStrip : TopologicalSpace.Opens (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
  ⟨{q | -2 < q.2 ∧ q.2 < 2},
    (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)⟩

private theorem mem_bufferedCylinder_half (q : bufferedCylinder (1 / 2)) :
    -3 < q.1.2 ∧ q.1.2 < 3 := by
  have h : -(1 / 2 : ℝ)⁻¹ - 1 < q.1.2 ∧ q.1.2 < (1 / 2 : ℝ)⁻¹ + 1 := q.2
  norm_num at h
  exact h

private def squeezeDiffeomorph :
    bufferedCylinder (1 / 2) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯
      tubeStrip where
  toFun q := ⟨(q.1.1, squeeze q.1.2),
    squeeze_mem (mem_bufferedCylinder_half q).1 (mem_bufferedCylinder_half q).2⟩
  invFun y := ⟨(y.1.1, stretch y.1.2), by
    have h := stretch_mem y.2.1 y.2.2
    change -(1 / 2 : ℝ)⁻¹ - 1 < stretch y.1.2 ∧ stretch y.1.2 < (1 / 2 : ℝ)⁻¹ + 1
    norm_num
    exact h⟩
  left_inv q := Subtype.ext (Prod.ext rfl (stretch_squeeze q.1.2))
  right_inv y := Subtype.ext (Prod.ext rfl (squeeze_stretch y.1.2))
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff tubeStrip _).mp ?_
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contDiff_squeeze.contMDiff.comp (contMDiff_snd.comp contMDiff_subtype_val))
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff (bufferedCylinder (1 / 2)) _).mp ?_
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contDiff_stretch.contMDiff.comp (contMDiff_snd.comp contMDiff_subtype_val))

theorem exists_bufferedChart_eqOn_tube {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    (τ : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2 → X)
    (hτ : Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ τ) :
    ∃ f : bufferedCylinder (1 / 2) → X, Topology.IsOpenEmbedding f ∧
      IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ f ∧ range f ⊆ range τ ∧
      ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (-2 : ℝ) 2,
        -(5 / 4) ≤ p.2.1 → p.2.1 ≤ 5 / 4 →
          originalTubularMap (by norm_num) (by norm_num) f p = τ p := by
  obtain ⟨d, -, hd⟩ :=
    DifferentialGeometry.Manifold.Interval.exists_iccInteriorStrip_diffeomorph
      (B := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (𝓡 2) ∞ (a := -2) (b := 2)
  let κ := Subtype.val ∘ d.symm ∘ squeezeDiffeomorph
  have hκ : IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod (𝓡∂ 1)) ∞ κ :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
      (isLocalDiffeomorph_comp d.symm.isLocalDiffeomorph squeezeDiffeomorph.isLocalDiffeomorph)
  have hfs : ContMDiff ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ (τ ∘ κ) :=
    hτ.contMDiff.comp hκ.contMDiff
  have hinj : Function.Injective (τ ∘ κ) :=
    hτ.isEmbedding.injective.comp (Subtype.val_injective.comp
      (d.symm.injective.comp squeezeDiffeomorph.injective))
  have himm :
      ∀ x, Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) (τ ∘ κ) x) := by
    intro x
    rw [mfderiv_comp x (hτ.contMDiff.mdifferentiableAt (by simp))
      (hκ.contMDiff.mdifferentiableAt (by simp))]
    have h₁ :
        Function.Injective (mfderiv ((𝓡 2).prod 𝓘(ℝ)) ((𝓡 2).prod (𝓡∂ 1)) κ x) :=
      fun a b hab => ((hκ x).mfderivToContinuousLinearEquiv (by simp)).injective hab
    exact ((hτ.isImmersion.isImmersionAt (κ x)).mfderiv_injective (by simp)).comp h₁
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  refine ⟨τ ∘ κ, Manifold.isOpenEmbedding_of_injective_immersion _ hfs hinj himm hdim,
    Manifold.isLocalDiffeomorph_of_injective_mfderiv _ hfs himm hdim,
    range_comp_subset_range _ _, fun p h₁ h₂ => ?_⟩
  have hp : (p.1, p.2.1) ∈ bufferedCylinder (1 / 2) := by
    change -(1 / 2 : ℝ)⁻¹ - 1 < p.2.1 ∧ p.2.1 < (1 / 2 : ℝ)⁻¹ + 1
    norm_num
    constructor <;> linarith [p.2.2.1, p.2.2.2]
  change τ (d.symm (squeezeDiffeomorph ⟨(p.1, p.2.1), hp⟩)).1 = τ p
  refine congrArg τ ?_
  have h := hd (squeezeDiffeomorph ⟨(p.1, p.2.1), hp⟩)
  change _ = (p.1, squeeze p.2.1) at h
  rw [squeeze_eq_self h₁ h₂] at h
  have h₃ := congrArg Prod.fst h
  have h₄ := congrArg Prod.snd h
  exact Prod.ext h₃ (Subtype.ext h₄)




private local instance : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2
private local instance : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

private def sphereIntoCore {M : ClosedOrientedManifold.{u} 3} {ι : Type} {C : Set M.Carrier}
    (bs : ι × Bool → C(S², M.Carrier)) (hmem : ∀ b z, bs b z ∈ C) (b : ι × Bool) :
    C(S², C) :=
  ⟨fun z => ⟨bs b z, hmem b z⟩, (bs b).continuous.subtype_mk _⟩

private structure CapData (M N : ClosedOrientedManifold.{u} 3) (ι : Type) (C : Set M.Carrier)
    (bs : ι × Bool → C(S², M.Carrier)) (hmem : ∀ b z, bs b z ∈ C)
    (ov : ι × Bool → S² → EuclideanSpace ℝ (Fin 3)) where
  [coreCharts : ChartedSpace (EuclideanHalfSpace 3) C]
  [coreSmooth : IsManifold (𝓡∂ 3) ∞ C]
  core_induced : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (Subtype.val : C → M.Carrier)
  core_compact : IsCompact C
  core_boundary : (𝓡∂ 3).boundary C = ⋃ b, range (sphereIntoCore bs hmem b)
  coreInclusion : C(C, N.Carrier)
  core_embedding : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ coreInclusion
  cap : ι × Bool → C(ClosedCell 3, N.Carrier)
  cap_embedding : ∀ b, IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ (cap b)
  attaching : ι × Bool → (S² ≃ₘ⟮𝓡 2, 𝓡 2⟯ S²)
  boundary_eq : ∀ b z,
    cap b (sphereToClosedCell z) = coreInclusion (sphereIntoCore bs hmem b (attaching b z))
  exhaustive : range coreInclusion ∪ (⋃ b, range (cap b)) = univ
  core_cap_intersection : ∀ b,
    range coreInclusion ∩ range (cap b) =
      range (coreInclusion.comp (sphereIntoCore bs hmem b))
  cap_disjoint : Pairwise fun b b' => Disjoint (range (cap b)) (range (cap b'))
  core_positive : ∀ x : C, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : C → M.Carrier) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : C → M.Carrier) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) coreInclusion x).toLinearMap hj))
        (M.orientation.orientation x.1) = N.orientation.orientation (coreInclusion x)
  cap_positive : ∀ b, ∀ x : ClosedCell 3, (𝓡∂ 3).IsInteriorPoint x →
    ∃ hi : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x),
    ∃ hj : Function.Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x),
      Orientation.map (Fin 3)
        ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap hi).symm.trans
          (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) (𝓡 3) (cap b) x).toLinearMap hj))
        ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) =
          (if b.2 then (1 : ℝˣ) else -1) • N.orientation.orientation (cap b x)
  boundary_orientation_reversing : ∀ b z (v w : TangentSpace (𝓡 2) z),
    let f : S² → M.Carrier := bs b ∘ attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3) (Subtype.val : S² → EuclideanSpace ℝ (Fin 3)) z
    (0 < ((M.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons (ov b (attaching b z)) (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (if b.2 then (1 : ℝ) else -1) *
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

private structure CutCapData (M Q : ClosedOrientedManifold.{u} 3) (ι : Type)
    (C : Set M.Carrier) (bs : ι × Bool → C(S², M.Carrier)) (hmem : ∀ b z, bs b z ∈ C)
    (ov : ι × Bool → S² → EuclideanSpace ℝ (Fin 3)) where
  source_nonempty : Nonempty M.Carrier
  capped : ClosedOrientedManifold.{u} 3
  capping : CapData M capped ι C bs hmem ov
  discarded : ClosedOrientedManifold.{u} 3
  presentation : capped.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ (Q.Carrier ⊕ discarded.Carrier)
  presentation_positive : ∀ x : capped.Carrier,
    Orientation.map (Fin 3)
      (presentation.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (capped.orientation.orientation x) =
        match presentation x with
        | Sum.inl q => Q.orientation.orientation q
        | Sum.inr d => discarded.orientation.orientation d
  every_component_meets_core : ∀ c : ConnectedComponents Q.Carrier,
    ∃ x : C, ∃ q : Q.Carrier,
      presentation (capping.coreInclusion x) = Sum.inl q ∧ ConnectedComponents.mk q = c
  retained_complement :
    (interior {q : Q.Carrier | ∃ x : C,
      presentation (capping.coreInclusion x) = Sum.inl q})ᶜ =
      {q : Q.Carrier | ∃ b, ∃ z : ClosedCell 3, presentation (capping.cap b z) = Sum.inl q}
  nontrivial : Nonempty ι ∨ Nonempty discarded.Carrier

private def toCutCapData {M Q : ClosedOrientedManifold.{u} 3}
    (E : SphericalCutCapTransition M Q) :
    CutCapData M Q E.tubes.Index E.tubes.core E.tubes.boundarySphere
      E.tubes.boundarySphere_mem_core
      (fun b z => (E.tubes.outwardVector b z : EuclideanSpace ℝ (Fin 3))) where
  source_nonempty := E.source_nonempty
  capped := E.capped
  capping :=
    { coreCharts := E.capping.coreCharts
      coreSmooth := E.capping.coreSmooth
      core_induced := E.capping.core_induced
      core_compact := E.capping.core_compact
      core_boundary := E.capping.core_boundary
      coreInclusion := E.capping.coreInclusion
      core_embedding := E.capping.core_embedding
      cap := E.capping.cap
      cap_embedding := E.capping.cap_embedding
      attaching := E.capping.attaching
      boundary_eq := E.capping.boundary_eq
      exhaustive := E.capping.exhaustive
      core_cap_intersection := E.capping.core_cap_intersection
      cap_disjoint := E.capping.cap_disjoint
      core_positive := E.capping.core_positive
      cap_positive := E.capping.cap_positive
      boundary_orientation_reversing := E.capping.boundary_orientation_reversing }
  discarded := E.discarded
  presentation := E.presentation
  presentation_positive := E.presentation_positive
  every_component_meets_core := E.every_component_meets_core
  retained_complement := E.retained_complement
  nontrivial := E.nontrivial

private def ofCutCapData {M Q : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)
    (D : CutCapData M Q T.Index T.core T.boundarySphere T.boundarySphere_mem_core
      (fun b z => (T.outwardVector b z : EuclideanSpace ℝ (Fin 3)))) :
    SphericalCutCapTransition M Q where
  source_nonempty := D.source_nonempty
  tubes := T
  capped := D.capped
  capping :=
    { coreCharts := D.capping.coreCharts
      coreSmooth := D.capping.coreSmooth
      core_induced := D.capping.core_induced
      core_compact := D.capping.core_compact
      core_boundary := D.capping.core_boundary
      coreInclusion := D.capping.coreInclusion
      core_embedding := D.capping.core_embedding
      cap := D.capping.cap
      cap_embedding := D.capping.cap_embedding
      attaching := D.capping.attaching
      boundary_eq := D.capping.boundary_eq
      exhaustive := D.capping.exhaustive
      core_cap_intersection := D.capping.core_cap_intersection
      cap_disjoint := D.capping.cap_disjoint
      core_positive := D.capping.core_positive
      cap_positive := D.capping.cap_positive
      boundary_orientation_reversing := D.capping.boundary_orientation_reversing }
  discarded := D.discarded
  presentation := D.presentation
  presentation_positive := D.presentation_positive
  every_component_meets_core := D.every_component_meets_core
  retained_complement := D.retained_complement
  nontrivial := D.nontrivial

private def CutCapData.transport {M Q : ClosedOrientedManifold.{u} 3} {ι : Type}
    {C C' : Set M.Carrier} {bs bs' : ι × Bool → C(S², M.Carrier)}
    {hmem : ∀ b z, bs b z ∈ C} {hmem' : ∀ b z, bs' b z ∈ C'}
    {ov ov' : ι × Bool → S² → EuclideanSpace ℝ (Fin 3)}
    (hC : C = C') (hbs : bs = bs') (hov : ov = ov') (D : CutCapData M Q ι C bs hmem ov) :
    CutCapData M Q ι C' bs' hmem' ov' := by
  subst hC hbs hov
  exact D



open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology in
private theorem exists_transition_ofSmoothOrientation {X : Type u} [TopologicalSpace X]
    [T2Space X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
    [CompactSpace X] (o : Topology.Manifold.SmoothOrientation (𝓡 3) X)
    (T : SphericalTubeSystem (ClosedOrientedManifold.ofSmoothOrientation X o))
    (hT : Nonempty T.Index) :
    ∃ (Q : ClosedOrientedManifold.{u} 3)
      (E : SphericalCutCapTransition (ClosedOrientedManifold.ofSmoothOrientation X o) Q),
      E.tubes = T := by
  classical
  choose f hf hs hrange heq using fun a => exists_bufferedChart_eqOn_tube (T.tube a) (T.smooth a)
  have hdisj : Pairwise fun a b => Disjoint (range (f a)) (range (f b)) :=
    fun a b hab => (T.disjoint hab).mono (hrange a) (hrange b)
  obtain ⟨a₀⟩ := hT
  have : Nonempty (ClosedOrientedManifold.ofSmoothOrientation X o).Carrier :=
    ⟨T.tube a₀ (⟨EuclideanSpace.single 0 1, by simp⟩, ⟨0, by norm_num, by norm_num⟩)⟩
  obtain ⟨oQ, oRet, oDisc, A, B, att, hboundary, -, -, Y, hY, hrev⟩ :=
    exists_smoothCutCapTransition_boundaryFrameReversing_of_buffered_finite_caps
      (δ := fun _ => (1 / 2 : ℝ)) (L := 1) one_pos (fun _ => by norm_num) (fun _ => by norm_num)
      f hf hdisj hs Set.univ o (Or.inl ⟨a₀⟩)
  cases Y
  dsimp only at hY
  subst hY
  let E' := SphericalCutCapTransition.ofSmoothCutCapTransition _
    (SmoothCutCapTransition.toSmoothCutCapCompletion _ hrev)
  have htube : ∀ a p, -(5 / 4) ≤ (p : S² × Icc (-2 : ℝ) 2).2.1 → p.2.1 ≤ 5 / 4 →
      E'.tubes.tube a p = T.tube a p := heq
  have hband : ∀ a, E'.tubes.removedBand a = T.removedBand a := fun a =>
    Set.EqOn.image_eq fun p hp => htube a p (by linarith [hp.1]) (by linarith [hp.2])
  have hC : E'.tubes.core = T.core := congrArg compl (iUnion_congr hband)
  have hlevel : ∀ side : Bool, -(5 / 4 : ℝ) ≤ (SphericalTubeSystem.boundaryLevel side).1 ∧
      (SphericalTubeSystem.boundaryLevel side).1 ≤ 5 / 4 := by
    intro side
    cases side <;> norm_num [SphericalTubeSystem.boundaryLevel]
  have hbs : E'.tubes.boundarySphere = T.boundarySphere := funext fun b =>
    ContinuousMap.ext fun z => htube b.1 _ (hlevel b.2).1 (hlevel b.2).2
  have hW : IsOpen {p : S² × Icc (-2 : ℝ) 2 | -(5 / 4) < p.2.1 ∧ p.2.1 < 5 / 4} :=
    (isOpen_lt continuous_const (continuous_subtype_val.comp continuous_snd)).inter
      (isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const)
  have hov : (fun b z => (E'.tubes.outwardVector b z : EuclideanSpace ℝ (Fin 3))) =
      fun b z => (T.outwardVector b z : EuclideanSpace ℝ (Fin 3)) := by
    funext b z
    have hmem : (z, SphericalTubeSystem.boundaryLevel b.2) ∈
        {p : S² × Icc (-2 : ℝ) 2 | -(5 / 4) < p.2.1 ∧ p.2.1 < 5 / 4} := by
      rcases b with ⟨a, _ | _⟩ <;> norm_num [SphericalTubeSystem.boundaryLevel]
    have hev : (E'.tubes.tube b.1 : S² × Icc (-2 : ℝ) 2 → _) =ᶠ[𝓝 (z, _)] T.tube b.1 :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds hmem) fun p hp => htube b.1 p hp.1.le hp.2.le
    change mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (E'.tubes.tube b.1) (z, _) _ =
      mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) (T.tube b.1) (z, _) _
    rw [hev.mfderiv_eq]
    rfl
  exact ⟨_, ofCutCapData T ((toCutCapData E').transport hC hbs hov), rfl⟩

theorem exists_sphericalCutCapTransition_tubes_eq (P : ClosedOrientedManifold.{u} 3)
    (T : SphericalTubeSystem P) (hT : Nonempty T.Index) :
    ∃ (Q : ClosedOrientedManifold.{u} 3) (E : SphericalCutCapTransition P Q), E.tubes = T := by
  revert T
  rw [← P.ofSmoothOrientation_smoothOrientation]
  exact fun T hT => exists_transition_ofSmoothOrientation _ T hT

theorem sphereSystemCapping : SphereSystemCapping.{u} := fun M T hT =>
  exists_sphericalCutCapTransition_tubes_eq M.toClosedOrientedManifold T hT

end GC.Endpoint
