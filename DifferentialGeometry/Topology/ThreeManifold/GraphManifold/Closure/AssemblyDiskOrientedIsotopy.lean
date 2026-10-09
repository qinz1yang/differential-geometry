import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskRimApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskBundleTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyMonodromyOrientation
import DifferentialGeometry.Topology.Manifold.ClosedDiskRimCollar.Extension
import DifferentialGeometry.Topology.Circle.Extension
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Chapter-14 assembly, D2S1 input (b): orientation-preserving disk diffeomorphisms are isotopic to the identity

Frozen statement: `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean`
(`exists_diskIsotopy_from_refl_of_preservesOrientation`), combined from (b1) (rim) and (b2) + SM-D.

Route. Let `μ` be a diffeomorphism of the closed disk. It maps the rim to the rim (boundary points
are preserved by local diffeomorphisms); its rim map `Q` is a diffeomorphism of the circle, and the
conjugate of `Q` on `ℝ/ℤ` has a periodic increasing lift `F` with `Q (e^{2πit}) = e^{±2πi F t}`
(`AddCircle/DiffeomorphLift.lean`).
* Positive sign (`exists_diskIsotopy_from_refl_of_rim_lift`): the tree's compactly supported ambient
  isotopy `Φ` of the plane that drags the unit circle along `(1 − s) t + s F t`
  (`Embedding/PeriodicCurveIsotopy.lean`) preserves the closed unit ball for `s ∈ [0, 1]` (it maps the
  circle onto itself and fixes `0`), so it restricts to an isotopy `R` of disk diffeomorphisms
  (`closedCellDiffeomorph`) from the identity to a diffeomorphism `R₁` that agrees with `μ` on the
  rim. Then `R₁⁻¹ ∘ μ` fixes the rim and is isotopic to the identity by (b2) + SM-D
  (`exists_diskIsotopy_refl_rel_rim_of_fix_rim`, lane D2S1-RIM). The isotopy of `μ` is
  `R_t ∘ L_t` with both factors flattened near the ends.
* Negative sign: then `ρ ∘ μ` (`ρ` the reflection `z ↦ z̄`) has a positive rim lift, so it is
  isotopic to the identity and preserves every orientation (`IsotopyOrientationModel.lean`); hence
  `ρ` would preserve the orientation `o`. But `ρ` fixes the centre with `det dρ = −1`, which
  contradicts the fixed-point determinant criterion (group G1).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local instance diskChartsOriented_D2S1C : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothOriented_D2S1C : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

attribute [local instance] finrank_real_complex_fact'
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "𝔸" => Complex.orthonormalBasisOneI.repr

local instance closedCellPreconnectedOriented_D2S1C : PreconnectedSpace (ClosedCell 2) :=
  closedCell_two_preconnectedSpace

/-! ## Small lemmas -/

/-- A continuous map of `ℝ` commuting with `+1` is surjective. -/
theorem surjective_of_continuous_of_map_add_one {h : ℝ → ℝ} (hc : Continuous h)
    (hp : ∀ x, h (x + 1) = h x + 1) : Surjective h := by
  intro y
  have hperiodic : Periodic (fun t => h t - t) 1 := by
    intro t
    simp only [hp]
    ring
  have hint : ∀ n : ℤ, h n = h 0 + n := by
    intro n
    have hn := hperiodic.int_mul n 0
    simp only [zero_add, mul_one, sub_zero] at hn
    linarith
  set n : ℤ := ⌊y - h 0⌋ with hn
  have hlo : h n ≤ y := by
    rw [hint]
    linarith [Int.floor_le (y - h 0)]
  have hhi : y ≤ h ((n : ℝ) + 1) := by
    have h1 := hint (n + 1)
    push_cast at h1
    rw [h1]
    linarith [Int.lt_floor_add_one (y - h 0)]
  obtain ⟨c, -, hc'⟩ := intermediate_value_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    hc.continuousOn ⟨hlo, hhi⟩
  exact ⟨c, hc'⟩

theorem addCircle_diffeomorphCircle_neg (w : AddCircle (1 : ℝ)) :
    AddCircle.diffeomorphCircle (-w) = (AddCircle.diffeomorphCircle w)⁻¹ := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective w
  rw [← QuotientAddGroup.mk_neg]
  change AddCircle.diffeomorphCircle ((-x : ℝ) : AddCircle (1 : ℝ)) =
    (AddCircle.diffeomorphCircle (x : AddCircle (1 : ℝ)))⁻¹
  rw [addCircle_diffeomorphCircle_coe, addCircle_diffeomorphCircle_coe, mul_neg, Circle.exp_neg]

theorem norm_le_one_iff_of_image_closedBall {Ψ : ℂ → ℂ} (hΨ : Injective Ψ)
    (h : Ψ '' closedBall (0 : ℂ) 1 = closedBall 0 1) {w : ℂ} : ‖Ψ w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := by
  constructor
  · intro hw
    have hmem : Ψ w ∈ Ψ '' closedBall (0 : ℂ) 1 := by
      rw [h]
      exact mem_closedBall_zero_iff.mpr hw
    obtain ⟨v, hv, hvw⟩ := hmem
    rw [← hΨ hvw]
    exact mem_closedBall_zero_iff.mp hv
  · intro hw
    have hmem : Ψ w ∈ Ψ '' closedBall (0 : ℂ) 1 := ⟨w, mem_closedBall_zero_iff.mpr hw, rfl⟩
    rw [h] at hmem
    exact mem_closedBall_zero_iff.mp hmem

/-! ## The rim of the disk as the circle -/

/-- The point of the rim with complex coordinate `z`. -/
def circleRimPoint (z : Circle) : ClosedCell 2 :=
  ⟨𝔸 (z : ℂ), by rw [LinearIsometryEquiv.norm_map, Circle.norm_coe]⟩

theorem circleRimPoint_val (z : Circle) : (circleRimPoint z).val = 𝔸 (z : ℂ) :=
  rfl

theorem circleRimPoint_mem_diskRim (z : Circle) : circleRimPoint z ∈ diskRim := by
  rw [mem_diskRim_iff, circleRimPoint_val, LinearIsometryEquiv.norm_map, Circle.norm_coe]

theorem exists_circleRimPoint_eq {x : ClosedCell 2} (hx : x ∈ diskRim) :
    ∃ z : Circle, circleRimPoint z = x := by
  have hn : ‖(𝔸).symm x.val‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_diskRim_iff.mp hx
  refine ⟨⟨(𝔸).symm x.val, mem_sphere_zero_iff_norm.mpr hn⟩, Subtype.ext ?_⟩
  change 𝔸 ((𝔸).symm x.val) = x.val
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem contMDiff_circleRimPoint : ContMDiff (𝓡 1) (𝓡∂ 2) ∞ circleRimPoint := by
  have hc : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have h : ContMDiff (𝓡 1) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun z : Circle => 𝔸 (z : ℂ)) :=
    (𝔸).toContinuousLinearEquiv.contDiff.contMDiff.comp hc
  apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
  exact ⟨h.continuous.subtype_mk _, h⟩

/-- The rim map of a disk diffeomorphism, as a map of the circle. -/
def diskRimCircleMap (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (z : Circle) : Circle :=
  ⟨(𝔸).symm (μ (circleRimPoint z)).val, mem_sphere_zero_iff_norm.mpr (by
    rw [LinearIsometryEquiv.norm_map]
    exact mem_diskRim_iff.mp
      (((μ.isLocalDiffeomorph (circleRimPoint z)).isBoundaryPoint_iff (by simp)).mp
        (circleRimPoint_mem_diskRim z)))⟩

theorem circleRimPoint_diskRimCircleMap (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)
    (z : Circle) : circleRimPoint (diskRimCircleMap μ z) = μ (circleRimPoint z) := by
  apply Subtype.ext
  change 𝔸 ((𝔸).symm (μ (circleRimPoint z)).val) = (μ (circleRimPoint z)).val
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem circleRimPoint_injective : Injective circleRimPoint := by
  intro z w h
  apply Circle.ext
  have h' := congrArg Subtype.val h
  exact (𝔸).injective h'

theorem diskRimCircleMap_symm_apply (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (z : Circle) :
    diskRimCircleMap μ.symm (diskRimCircleMap μ z) = z := by
  apply circleRimPoint_injective
  rw [circleRimPoint_diskRimCircleMap, circleRimPoint_diskRimCircleMap,
    Diffeomorph.symm_apply_apply]

theorem contMDiff_diskRimCircleMap (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (diskRimCircleMap μ) := by
  have hemb := isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)
  have h : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle => (𝔸).symm (μ (circleRimPoint z)).val) :=
    (𝔸).symm.toContinuousLinearEquiv.contDiff.contMDiff.comp
      ((isSmoothEmbedding_closedCell_inclusion 1).contMDiff.comp
        (μ.contMDiff.comp contMDiff_circleRimPoint))
  apply (ContMDiff.iff_comp_isImmersion hemb.isImmersion).mpr
  exact ⟨h.continuous.subtype_mk _, h⟩

/-- The rim map as a diffeomorphism of the circle. -/
def diskRimDiffeomorph (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) :
    Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun := diskRimCircleMap μ
  invFun := diskRimCircleMap μ.symm
  left_inv := diskRimCircleMap_symm_apply μ
  right_inv z := by
    apply circleRimPoint_injective
    rw [circleRimPoint_diskRimCircleMap, circleRimPoint_diskRimCircleMap,
      Diffeomorph.apply_symm_apply]
  contMDiff_toFun := contMDiff_diskRimCircleMap μ
  contMDiff_invFun := contMDiff_diskRimCircleMap μ.symm

theorem diskRimDiffeomorph_val (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (z : Circle) :
    (μ (circleRimPoint z)).val = 𝔸 (diskRimDiffeomorph μ z : ℂ) := by
  rw [← circleRimPoint_val]
  change (μ (circleRimPoint z)).val = (circleRimPoint (diskRimCircleMap μ z)).val
  rw [circleRimPoint_diskRimCircleMap]

/-! ## The positive case: an isotopy from the identity -/

/-- The circle curve `θ ↦ e^{2πiθ}` of the plane, a smooth embedding of `ℝ/ℤ`. -/
theorem isSmoothEmbedding_addCircle_plane :
    Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞
      (fun θ : AddCircle (1 : ℝ) => ((AddCircle.diffeomorphCircle θ : Circle) : ℂ)) := by
  have hA : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) (𝓡 1) ∞
      (AddCircle.diffeomorphCircle : AddCircle (1 : ℝ) → Circle) :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      AddCircle.diffeomorphCircle.isLocalDiffeomorph AddCircle.diffeomorphCircle.injective
  exact (isSmoothEmbedding_coe_sphere (E := ℂ) (n := 1)).comp_of_boundarylessManifold hA (by simp)

/-- A disk diffeomorphism whose rim map has a positive periodic lift is smoothly isotopic to the
identity (constant near the ends, inverses jointly smooth). -/
theorem exists_diskIsotopy_from_refl_of_rim_lift
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t)
    (hrim : ∀ t : ℝ, (μ (circleRimPoint (AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))))).val =
      𝔸 ((AddCircle.diffeomorphCircle (F t : AddCircle (1 : ℝ)) : Circle) : ℂ)) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = μ x) := by
  set C := AddCircle.diffeomorphCircle
  let f : AddCircle (1 : ℝ) → ℂ := fun θ => ((C θ : Circle) : ℂ)
  have hf : Manifold.IsSmoothEmbedding 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ∞ f := isSmoothEmbedding_addCircle_plane
  obtain ⟨Φ, hΦ, hΦi, hΦ0, htrack, Kc, -, hKc, hfix⟩ :=
    DifferentialGeometry.Topology.PeriodicCurve.exists_compactly_supported_ambient_isotopy_of_increasing_lift
      hf hF hper hpos isOpen_compl_singleton
      (show range f ⊆ ({0} : Set ℂ)ᶜ from by
        rintro _ ⟨θ, rfl⟩
        exact ne_zero_of_mem_unit_sphere (C θ))
  -- every `Φ s`, `s ∈ [0, 1]`, preserves the closed unit ball
  have hΦzero : ∀ s, Φ s 0 = 0 := fun s => (hfix s).1 (fun hz => hKc hz rfl)
  have hrangef : range f = sphere (0 : ℂ) 1 := by
    ext w
    constructor
    · rintro ⟨θ, rfl⟩
      exact (C θ).2
    · intro hw
      obtain ⟨θ, hθ⟩ := C.surjective ⟨w, hw⟩
      exact ⟨θ, congrArg Subtype.val hθ⟩
  have hball : ∀ s ∈ Icc (0 : ℝ) 1, Φ s '' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
    intro s hs
    apply (Φ s).toHomeomorph.image_closedBall_of_image_sphere_eq_of_map_center zero_lt_one
      zero_lt_one ?_ (hΦzero s)
    have hsurj : Surjective (fun x : ℝ => (1 - s) * x + s * F x) :=
      surjective_of_continuous_of_map_add_one
        ((continuous_const.mul continuous_id).add (continuous_const.mul hF.continuous))
        (fun x => by rw [hper]; ring)
    rw [← hrangef]
    ext w
    constructor
    · rintro ⟨_, ⟨θ, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
      exact ⟨_, (htrack s hs x).symm⟩
    · rintro ⟨θ, rfl⟩
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective θ
      obtain ⟨x, hx⟩ := hsurj y
      refine ⟨f (x : AddCircle (1 : ℝ)), ⟨_, rfl⟩, ?_⟩
      change Φ s (f (x : AddCircle (1 : ℝ))) = f (y : AddCircle (1 : ℝ))
      rw [htrack s hs x]
      exact congrArg (fun r : ℝ => f (r : AddCircle (1 : ℝ))) hx
  -- the flattening parameter
  let τ : ℝ → ℝ := fun t => Real.smoothTransition (3 * t - 1)
  have hτmem : ∀ t, τ t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hτlo : ∀ t, t ≤ 1 / 3 → τ t = 0 :=
    fun t ht => Real.smoothTransition.zero_of_nonpos (by linarith)
  have hτhi : ∀ t, 2 / 3 ≤ t → τ t = 1 :=
    fun t ht => Real.smoothTransition.one_of_one_le (by linarith)
  have hτs : ContDiff ℝ ∞ τ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  -- the plane isotopy in the coordinates `ℝ²`, and its restriction to the disk
  let A := (𝔸).toContinuousLinearEquiv.toDiffeomorph
  let D : ℝ → (EuclideanSpace ℝ (Fin 2) ≃ₘ⟮𝓡 2, 𝓡 2⟯ EuclideanSpace ℝ (Fin 2)) :=
    fun s => (A.symm.trans (Φ s)).trans A
  have hDapply : ∀ s v, D s v = 𝔸 (Φ s ((𝔸).symm v)) := fun _ _ => rfl
  have hDball : ∀ s ∈ Icc (0 : ℝ) 1,
      D s '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = closedBall 0 1 := by
    intro s hs
    have hn : ∀ w : ℂ, ‖Φ s w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := fun w =>
      norm_le_one_iff_of_image_closedBall (Ψ := Φ s) (w := w) (Φ s).injective (hball s hs)
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [mem_closedBall_zero_iff] at hx ⊢
      rw [hDapply, LinearIsometryEquiv.norm_map, hn, LinearIsometryEquiv.norm_map]
      exact hx
    · intro hy
      refine ⟨(D s).symm y, ?_, (D s).apply_symm_apply y⟩
      rw [mem_closedBall_zero_iff] at hy ⊢
      have h1 : ‖(D s) ((D s).symm y)‖ ≤ 1 := by
        rw [Diffeomorph.apply_symm_apply]
        exact hy
      rw [hDapply, LinearIsometryEquiv.norm_map, hn] at h1
      rwa [LinearIsometryEquiv.norm_map] at h1
  let R : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) :=
    fun t => closedCellDiffeomorph (D (τ t)) (hDball (τ t) (hτmem t))
  have hRval : ∀ t x, (R t x).val = 𝔸 (Φ (τ t) ((𝔸).symm x.val)) := fun _ _ => rfl
  have hRsymmval : ∀ t x, ((R t).symm x).val = 𝔸 ((Φ (τ t)).symm ((𝔸).symm x.val)) :=
    fun _ _ => rfl
  have hRsm : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => R x.2 x.1) :=
    contMDiff_closedCell_family_of_val (m := 1)
      (G := fun p : ℝ × EuclideanSpace ℝ (Fin 2) => 𝔸 (Φ (τ p.1) ((𝔸).symm p.2)))
      ((𝔸).toContinuousLinearEquiv.contDiff.comp
        (hΦ.comp ((hτs.comp contDiff_fst).prodMk
          ((𝔸).symm.toContinuousLinearEquiv.contDiff.comp contDiff_snd))))
      (fun x => hRval x.2 x.1)
  have hRism : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (R x.2).symm x.1) :=
    contMDiff_closedCell_family_of_val (m := 1)
      (G := fun p : ℝ × EuclideanSpace ℝ (Fin 2) => 𝔸 ((Φ (τ p.1)).symm ((𝔸).symm p.2)))
      ((𝔸).toContinuousLinearEquiv.contDiff.comp
        (hΦi.comp ((hτs.comp contDiff_fst).prodMk
          ((𝔸).symm.toContinuousLinearEquiv.contDiff.comp contDiff_snd))))
      (fun x => hRsymmval x.2 x.1)
  have hRlo : ∀ t x, t ≤ 1 / 3 → R t x = x := by
    intro t x ht
    apply Subtype.ext
    rw [hRval, hτlo t ht, hΦ0]
    exact LinearIsometryEquiv.apply_symm_apply _ _
  -- the end diffeomorphism agrees with `μ` on the rim
  let R₁ := R 1
  have hRhi : ∀ t x, 2 / 3 ≤ t → R t x = R₁ x := by
    intro t x ht
    apply Subtype.ext
    rw [hRval, hRval, hτhi t ht, hτhi 1 (by norm_num)]
  have hR₁rim : ∀ x ∈ diskRim, R₁ x = μ x := by
    intro x hx
    obtain ⟨z, rfl⟩ := exists_circleRimPoint_eq hx
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (C.symm z)
    have hz : z = C (t : AddCircle (1 : ℝ)) := by
      rw [ht, Diffeomorph.apply_symm_apply]
    rw [hz]
    apply Subtype.ext
    rw [hRval, hτhi 1 (by norm_num), hrim t, circleRimPoint_val, LinearIsometryEquiv.symm_apply_apply]
    have h := htrack 1 ⟨zero_le_one, le_rfl⟩ t
    simp only [sub_self, zero_mul, one_mul, zero_add] at h
    exact congrArg 𝔸 h
  -- `R₁⁻¹ ∘ μ` fixes the rim
  let μ' : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 := μ.trans R₁.symm
  have hμ'rim : ∀ x ∈ diskRim, μ' x = x := by
    intro x hx
    change R₁.symm (μ x) = x
    rw [← hR₁rim x hx, Diffeomorph.symm_apply_apply]
  obtain ⟨L, hL, hLi, hL0, hL1, -⟩ := exists_diskIsotopy_refl_rel_rim_of_fix_rim μ' hμ'rim
  -- flatten `L` (from the identity to `μ'`) and compose with `R`
  let L' : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) := fun t => L (1 - τ t)
  have hflip : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : ClosedCell 2 × ℝ => (x.1, 1 - τ x.2)) :=
    contMDiff_fst.prodMk (contMDiff_const.sub (hτs.contMDiff.comp contMDiff_snd))
  have hL'sm : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => L' x.2 x.1) := hL.comp hflip
  have hL'ism : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (L' x.2).symm x.1) := hLi.comp hflip
  refine ⟨fun t => (L' t).trans (R t), ?_, ?_, 1 / 3, by norm_num, ?_, ?_⟩
  · have h := hRsm.comp (hL'sm.prodMk contMDiff_snd)
    change ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => R x.2 (L' x.2 x.1))
    exact h
  · have h := hL'ism.comp (hRism.prodMk contMDiff_snd)
    change ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (L' x.2).symm ((R x.2).symm x.1))
    exact h
  · intro t x ht
    change R t (L (1 - τ t) x) = x
    rw [hτlo t ht.le, sub_zero, hL1, hRlo t x ht.le]
  · intro t x ht
    change R t (L (1 - τ t) x) = μ x
    rw [hτhi t (by linarith), sub_self, hL0, hRhi t _ (by linarith)]
    change R₁ (R₁.symm (μ x)) = μ x
    exact R₁.apply_symm_apply (μ x)

/-! ## The reflection of the disk reverses orientation -/

/-- The reflection `z ↦ z̄` of the plane, in the coordinates `ℝ²`. -/
def planeReflection : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  ((𝔸).symm.trans Complex.conjLIE).trans 𝔸

theorem planeReflection_apply (v : EuclideanSpace ℝ (Fin 2)) :
    planeReflection v = 𝔸 ((starRingEnd ℂ) ((𝔸).symm v)) :=
  rfl

theorem planeReflection_closedBall :
    planeReflection '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = closedBall 0 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, planeReflection.norm_map] using hx
  · intro hy
    refine ⟨planeReflection.symm y, ?_, planeReflection.apply_symm_apply y⟩
    simpa only [mem_closedBall, dist_zero_right, planeReflection.symm.norm_map] using hy

theorem det_planeReflection :
    LinearMap.det (planeReflection.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) = -1 := by
  have h : (planeReflection.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) =
      ((𝔸).toLinearEquiv : ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∘ₗ
        (Complex.conjLIE.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ
          ((𝔸).toLinearEquiv.symm : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℂ) :=
    LinearMap.ext fun _ => rfl
  rw [h, LinearMap.det_conj, Complex.det_conjLIE]

/-- The reflection of the closed disk. -/
def closedDiskConjReflection : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 :=
  closedCellDiffeomorph planeReflection.toContinuousLinearEquiv.toDiffeomorph
    planeReflection_closedBall

theorem closedDiskConjReflection_val (x : ClosedCell 2) :
    (closedDiskConjReflection x).val = planeReflection x.val :=
  rfl

theorem closedDiskConjReflection_center :
    closedDiskConjReflection (closedCellCenter 2) = closedCellCenter 2 :=
  Subtype.ext (map_zero planeReflection)

theorem det_mfderiv_closedDiskConjReflection_center :
    LinearMap.det (mfderiv (𝓡∂ 2) (𝓡∂ 2) closedDiskConjReflection (closedCellCenter 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap = -1 := by
  set c := closedCellCenter 2
  have hemb := isSmoothEmbedding_closedCell_inclusion 1
  let ι : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡∂ 2) (𝓡 2) (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) c
  let dR : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    mfderiv (𝓡∂ 2) (𝓡∂ 2) closedDiskConjReflection c
  have hinj : Injective ι := hemb.isImmersion.mfderiv_injective (by simp) c
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    LinearMap.linearEquivOfInjective ι.toLinearMap hinj rfl
  have hmdval : ∀ x : ClosedCell 2, MDifferentiableAt (𝓡∂ 2) (𝓡 2)
      (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) x :=
    fun x => hemb.contMDiff.mdifferentiableAt (by simp)
  have hmdR : MDifferentiableAt (𝓡∂ 2) (𝓡∂ 2) closedDiskConjReflection c :=
    closedDiskConjReflection.contMDiff.mdifferentiableAt (by simp)
  have hfun : (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) ∘ closedDiskConjReflection =
      (planeReflection.toContinuousLinearEquiv : EuclideanSpace ℝ (Fin 2) → _) ∘ Subtype.val := by
    funext x
    rfl
  have hpt : ∀ w, ι (dR w) = planeReflection (ι w) := by
    intro w
    have h1 := mfderiv_comp_apply_of_eq c (hmdval c) hmdR closedDiskConjReflection_center w
    have h2 := mfderiv_comp_apply_of_eq c
      (planeReflection.toContinuousLinearEquiv.mdifferentiableAt (x := c.val)) (hmdval c) rfl w
    rw [ContinuousLinearEquiv.mfderiv_eq] at h2
    rw [hfun] at h1
    exact h1.symm.trans h2
  have hconj : dR.toLinearMap = (e.symm : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) ∘ₗ
      (planeReflection.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) ∘ₗ
        (e : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) := by
    apply LinearMap.ext
    intro w
    apply e.injective
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_coe]
    exact hpt w
  have hdet := LinearMap.det_conj
    (planeReflection.toLinearEquiv : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _) e.symm
  rw [LinearEquiv.symm_symm] at hdet
  change LinearMap.det dR.toLinearMap = -1
  rw [hconj, hdet, det_planeReflection]

theorem closedDiskConjReflection_not_preservesOrientation (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2) :
    ¬ closedDiskConjReflection.preservesOrientation o o := by
  intro h
  have hpos := (preservesOrientation_iff_det_mfderiv_pos_of_apply_eq o (closedCellCenter 2)
    closedDiskConjReflection_center).mp h
  rw [det_mfderiv_closedDiskConjReflection_center] at hpos
  norm_num at hpos

/-! ## D2S1 input (b) -/

/-- **D2S1 input (b)**: every orientation-preserving diffeomorphism of the disk is smoothly isotopic
to the identity (constant near the ends, inverses jointly smooth). -/
theorem exists_diskIsotopy_from_refl_of_preservesOrientation
    (o : ManifoldOrientation (𝓡∂ 2) (ClosedCell 2) 2)
    (μ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2) (hμ : μ.preservesOrientation o o) :
    ∃ K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2),
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = μ x) := by
  set C := AddCircle.diffeomorphCircle
  let Q := diskRimDiffeomorph μ
  let ψ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ) := (C.trans Q).trans C.symm
  obtain ⟨F, hper, hpos, hbranch⟩ := AddCircle.exists_increasing_diffeomorphism_lift_or_neg ψ
  have hFs : ContDiff ℝ ∞ (F : ℝ → ℝ) := F.contMDiff.contDiff
  have hQ : ∀ w : AddCircle (1 : ℝ), Q (C w) = C (ψ w) := by
    intro w
    change Q (C w) = C (C.symm (Q (C w)))
    rw [Diffeomorph.apply_symm_apply]
  rcases hbranch with h | h
  · refine exists_diskIsotopy_from_refl_of_rim_lift μ hFs hper hpos (fun t => ?_)
    rw [diskRimDiffeomorph_val, hQ, h t]
  · exfalso
    let μ₂ : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2 := μ.trans closedDiskConjReflection
    have hrim₂ : ∀ t : ℝ, (μ₂ (circleRimPoint (C (t : AddCircle (1 : ℝ))))).val =
        𝔸 ((C (F t : AddCircle (1 : ℝ)) : Circle) : ℂ) := by
      intro t
      change planeReflection (μ (circleRimPoint (C (t : AddCircle (1 : ℝ))))).val = _
      rw [diskRimDiffeomorph_val, hQ, h t, addCircle_diffeomorphCircle_neg, planeReflection_apply,
        LinearIsometryEquiv.symm_apply_apply, Circle.coe_inv_eq_conj, Complex.conj_conj]
    obtain ⟨K, hK, -, ε, hε, hlo, hhi⟩ :=
      exists_diskIsotopy_from_refl_of_rim_lift μ₂ hFs hper hpos hrim₂
    have hK0 : K 0 = Diffeomorph.refl (𝓡∂ 2) (ClosedCell 2) ∞ :=
      Diffeomorph.ext fun x => hlo 0 x hε
    have hKc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) (𝓡∂ 2) ∞
        (fun q : ℝ × ClosedCell 2 => K q.1 q.2) := by
      have hswap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 2)) ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ∞
          (fun q : ℝ × ClosedCell 2 => (q.2, q.1)) := contMDiff_snd.prodMk contMDiff_fst
      have h' := hK.comp hswap
      exact h'
    have hK1 := DifferentialGeometry.Topology.Manifold.preservesOrientation_of_contMDiff_isotopy
      o K hK0 hKc 1
    have hK1eq : K 1 = μ₂ := Diffeomorph.ext fun x => hhi 1 x (by linarith)
    have hρ : closedDiskConjReflection = μ.symm.trans μ₂ := Diffeomorph.ext fun x => by
      change closedDiskConjReflection x = closedDiskConjReflection (μ (μ.symm x))
      rw [Diffeomorph.apply_symm_apply]
    apply closedDiskConjReflection_not_preservesOrientation o
    rw [hρ]
    exact Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hμ)
      (hK1eq ▸ hK1)

end GC.GraphManifold.Assembly
