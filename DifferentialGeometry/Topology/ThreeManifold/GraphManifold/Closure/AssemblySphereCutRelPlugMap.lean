import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugData
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlace
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelFoldApplications
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# Chapter-14 assembly, relative COMPARE G4: the placed plug in the capped carrier

Lane ASM-L2e, group G4. For a solid-cap plug `Y` and a placement of its two solid tori into two
tubes `φ t` of a capped carrier `X.Q` (G2 shape, with diffeomorphisms `Θ t` of the solid torus and
a diffeomorphism `Ψ` of `X.Q`), `SolidCapPlug.placedMap`: the capped carrier of the plug is mapped
into `X.Q` piece by piece, `x ↦ Ψ⁻¹ (solidTubeFill (φ t) (Θ t (solid t)⁻¹ x))`.

* `contMDiff_solidTubeFill`, `injective_solidTubeFill`, `bijective_mfderiv_solidTubeFill`,
  `range_solidTubeFill`: the fill of the solid torus into a tube.
* `placedMap_of_mem`, `contMDiff_placedMap`, `bijective_mfderiv_placedMap`, `injective_placedMap`,
  `placedMap_image_piece`: the placed map is a smooth injective immersion with image the placed
  closed unit tubes.
* `placedMap_capChart`: it carries the cap ball charts of the plug onto the given ball charts
  (the matching of the placement).
* `placedMap_retained`: on the retained port collars it is the radial tube collar.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Bijective

variable {E E' E'' H H' H'' M M' M'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {I'' : ModelWithCorners ℝ E'' H''}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace M''] [ChartedSpace H'' M'']

/-- Bijective differentials compose. -/
theorem bijective_mfderiv_comp {f : M → M'} {g : M' → M''} {x : M}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (hbf : Bijective (mfderiv I I' f x)) (hbg : Bijective (mfderiv I' I'' g (f x))) :
    Bijective (mfderiv I I'' (g ∘ f) x) := by
  rw [mfderiv_comp x hg hf]
  exact hbg.comp hbf

/-- A partial diffeomorphism has bijective differentials on its source. -/
theorem bijective_mfderiv_of_mem_source (φ : PartialDiffeomorph I I' M M' ∞) {x : M}
    (hx : x ∈ φ.source) : Bijective (mfderiv I I' φ x) := by
  have h := φ.isLocalDiffeomorphAt _ _ _ hx
  exact (h.mfderivToContinuousLinearEquiv (by simp)).bijective

/-- A diffeomorphism has bijective differentials. -/
theorem bijective_mfderiv_diffeomorph (Φ : M ≃ₘ⟮I, I'⟯ M') (x : M) :
    Bijective (mfderiv I I' Φ x) :=
  bijective_mfderiv_of_mem_source Φ.toPartialDiffeomorph (mem_univ x)

end Bijective

/-! ### The fill of the solid torus into a tube -/

section Fill

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
  [TopologicalSpace M] [ChartedSpace H M]
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) I (PlaneLift.{u} × Circle) M ∞)

theorem solidTubeFill_eq :
    solidTubeFill φ = φ ∘ planeCircleThird.{u} ∘ (Subtype.val : solidSet.{u} → _) := by
  funext x
  change φ (ULift.up (x.val.1.down / 3), x.val.2) =
    φ (ULift.up ((1 / 3 : ℝ) • x.val.1.down), x.val.2)
  congr 3
  rw [Complex.real_smul, div_eq_inv_mul]
  push_cast
  ring

variable {φ}

theorem planeCircleThird_mem_source
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) (x : solidSet.{u}) :
    planeCircleThird x.val ∈ φ.source := by
  apply h3
  change ‖(1 / 3 : ℝ) • x.val.1.down‖ ≤ 3
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)]
  have := (mem_solidSet_iff x.val).mp x.property
  change ‖x.val.1‖ ≤ 3 at this
  have h' : ‖x.val.1.down‖ = ‖x.val.1‖ := rfl
  rw [h']
  linarith

theorem contMDiff_solidTubeFill
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) :
    ContMDiff (𝓡∂ 3) I ∞ (solidTubeFill φ) := by
  rw [solidTubeFill_eq]
  exact φ.contMDiffOn.comp_contMDiff
    (planeCircleThird.contMDiff.comp solidAtlas.contMDiff_subtype_val)
    (planeCircleThird_mem_source h3)

theorem injective_solidTubeFill
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) :
    Injective (solidTubeFill φ) := by
  intro x y hxy
  rw [solidTubeFill_eq] at hxy
  exact Subtype.ext (planeCircleThird.injective
    (φ.injOn (planeCircleThird_mem_source h3 x) (planeCircleThird_mem_source h3 y) hxy))

theorem bijective_mfderiv_solidTubeFill
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) (x : solidSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) I (solidTubeFill φ) x) := by
  rw [solidTubeFill_eq]
  have hv : MDifferentiableAt (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) (Subtype.val : solidSet.{u} → _) x :=
    solidAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp)
  have ht : MDifferentiableAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓘(ℝ, ℂ).prod (𝓡 1))
      planeCircleThird.{u} x.val :=
    planeCircleThird.contMDiff.mdifferentiableAt (by simp)
  have hφ : MDifferentiableAt (𝓘(ℝ, ℂ).prod (𝓡 1)) I φ (planeCircleThird x.val) :=
    (φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds (planeCircleThird_mem_source h3 x))).mdifferentiableAt
      (by simp)
  apply bijective_mfderiv_comp (ht.comp x hv) hφ
  · exact bijective_mfderiv_comp hv ht (solidAtlas.mfderiv_subtypeVal_bijective x)
      (bijective_mfderiv_diffeomorph planeCircleThird _)
  · exact bijective_mfderiv_of_mem_source φ (planeCircleThird_mem_source h3 x)

theorem range_solidTubeFill :
    range (solidTubeFill φ) = φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(ULift.up (x.val.1.down / 3), x.val.2), ?_, rfl⟩
    change ‖x.val.1.down / 3‖ ≤ 1
    rw [norm_div, Complex.norm_ofNat]
    have := (mem_solidSet_iff x.val).mp x.property
    change ‖x.val.1‖ ≤ 3 at this
    have h' : ‖x.val.1.down‖ = ‖x.val.1‖ := rfl
    rw [h']
    linarith
  · rintro ⟨p, hp, rfl⟩
    have hp' : ‖p.1.down‖ ≤ 1 := hp
    refine ⟨⟨(ULift.up (3 * p.1.down), p.2), ?_⟩, ?_⟩
    · rw [mem_solidSet_iff]
      change ‖3 * p.1.down‖ ≤ 3
      rw [norm_mul, Complex.norm_ofNat]
      linarith
    · change φ (ULift.up (3 * p.1.down / 3), p.2) = φ p
      congr 2
      · apply ULift.ext
        change 3 * p.1.down / 3 = p.1.down
        ring

theorem solidTubeFill_val_norm (x : solidSet.{u}) {r : ℝ} (hr : ‖x.val.1.down‖ ≤ r) :
    solidTubeFill φ x ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ r / 3} := by
  refine ⟨(ULift.up (x.val.1.down / 3), x.val.2), ?_, rfl⟩
  change ‖x.val.1.down / 3‖ ≤ r / 3
  rw [norm_div, Complex.norm_ofNat]
  linarith

end Fill

/-! ### The placed plug -/

namespace SolidCapPlug

variable {P : CompactCarrier.{u}} (Y : SolidCapPlug P)

theorem mem_piece_one {x : Y.cut.Q.Carrier} (hx : x ∉ Y.piece 0) : x ∈ Y.piece 1 := by
  have h : x ∈ (Y.piece 0 : Set Y.cut.Q.Carrier) ∪ Y.piece 1 := Y.piece_cover ▸ mem_univ x
  exact h.resolve_left hx

theorem exists_mem_piece (x : Y.cut.Q.Carrier) : ∃ t, x ∈ Y.piece t := by
  by_cases hx : x ∈ Y.piece 0
  · exact ⟨0, hx⟩
  · exact ⟨1, Y.mem_piece_one hx⟩

theorem not_mem_piece_one {x : Y.cut.Q.Carrier} (hx : x ∈ Y.piece 0) : x ∉ Y.piece 1 :=
  fun h => Set.disjoint_left.mp Y.piece_disjoint hx h

/-- The inverse of the inclusion of a piece. -/
def pieceInv (t : Fin 2) :
    PartialDiffeomorph Y.cut.Q.model Y.cut.Q.model Y.cut.Q.Carrier ↥(Y.piece t) ∞ :=
  (DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph Y.cut.Q.model (Y.piece t)
    inferInstance).symm

theorem pieceInv_source (t : Fin 2) : (Y.pieceInv t).source = Y.piece t :=
  DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target Y.cut.Q.model (Y.piece t)
    inferInstance

theorem pieceInv_apply (t : Fin 2) {x : Y.cut.Q.Carrier} (hx : x ∈ Y.piece t) :
    Y.pieceInv t x = ⟨x, hx⟩ :=
  DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply Y.cut.Q.model (Y.piece t)
    inferInstance hx

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  {X : SphereCutCapped W S E}
  (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier)
  (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
    (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
  (Θ : Fin 2 → solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u})

/-- The placed solid torus of side `t`. -/
def placedSide (t : Fin 2) (x : Y.piece t) : X.Q.Carrier :=
  Ψ.symm (solidTubeFill (φ t) (Θ t ((Y.solid t).symm x)))

/-- **The placed plug in the capped carrier.** -/
def placedMap (x : Y.cut.Q.Carrier) : X.Q.Carrier :=
  haveI := Classical.propDecidable
  if h : x ∈ Y.piece 0 then Y.placedSide Ψ φ Θ 0 ⟨x, h⟩
  else Y.placedSide Ψ φ Θ 1 ⟨x, Y.mem_piece_one h⟩

theorem placedMap_of_mem (t : Fin 2) {x : Y.cut.Q.Carrier} (hx : x ∈ Y.piece t) :
    Y.placedMap Ψ φ Θ x = Y.placedSide Ψ φ Θ t ⟨x, hx⟩ := by
  fin_cases t
  · unfold placedMap
    split_ifs with h
    · rfl
    · exact (h hx).elim
  · unfold placedMap
    split_ifs with h
    · exact (Y.not_mem_piece_one h hx).elim
    · rfl

theorem placedMap_eventuallyEq (t : Fin 2) {x : Y.cut.Q.Carrier} (hx : x ∈ Y.piece t) :
    Y.placedMap Ψ φ Θ =ᶠ[𝓝 x] Y.placedSide Ψ φ Θ t ∘ Y.pieceInv t := by
  filter_upwards [(Y.piece t).isOpen.mem_nhds hx] with y hy
  rw [Function.comp_apply, Y.pieceInv_apply t hy, Y.placedMap_of_mem Ψ φ Θ t hy]

variable {Ψ φ Θ}

theorem contMDiff_placedSide
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) (t : Fin 2) :
    ContMDiff Y.cut.Q.model X.Q.model ∞ (Y.placedSide Ψ φ Θ t) :=
  Ψ.symm.contMDiff.comp ((contMDiff_solidTubeFill (h3 t)).comp
    ((Θ t).contMDiff.comp (Y.solid t).symm.contMDiff))

theorem bijective_mfderiv_placedSide
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) (t : Fin 2)
    (x : Y.piece t) :
    Bijective (mfderiv Y.cut.Q.model X.Q.model (Y.placedSide Ψ φ Θ t) x) := by
  let f1 : Y.piece t → solidSet.{u} := (Y.solid t).symm
  let f2 : solidSet.{u} → solidSet.{u} := Θ t
  let f3 : solidSet.{u} → X.Q.Carrier := solidTubeFill (φ t)
  let f4 : X.Q.Carrier → X.Q.Carrier := Ψ.symm
  have he : Y.placedSide Ψ φ Θ t = f4 ∘ (f3 ∘ (f2 ∘ f1)) := rfl
  have h1 : MDifferentiableAt Y.cut.Q.model (𝓡∂ 3) f1 x :=
    (Y.solid t).symm.contMDiff.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3) f2 (f1 x) :=
    (Θ t).contMDiff.mdifferentiableAt (by simp)
  have h3' : MDifferentiableAt (𝓡∂ 3) X.Q.model f3 (f2 (f1 x)) :=
    (contMDiff_solidTubeFill (h3 t)).mdifferentiableAt (by simp)
  have h4 : MDifferentiableAt X.Q.model X.Q.model f4 (f3 (f2 (f1 x))) :=
    Ψ.symm.contMDiff.mdifferentiableAt (by simp)
  have hb12 : Bijective (mfderiv Y.cut.Q.model (𝓡∂ 3) (f2 ∘ f1) x) :=
    bijective_mfderiv_comp (f := f1) (g := f2) h1 h2 (bijective_mfderiv_diffeomorph _ _)
      (bijective_mfderiv_diffeomorph _ _)
  have hb123 : Bijective (mfderiv Y.cut.Q.model X.Q.model (f3 ∘ (f2 ∘ f1)) x) :=
    bijective_mfderiv_comp (f := f2 ∘ f1) (g := f3) (h2.comp x h1) h3' hb12
      (bijective_mfderiv_solidTubeFill (h3 t) _)
  rw [he]
  exact bijective_mfderiv_comp (f := f3 ∘ (f2 ∘ f1)) (g := f4) (h3'.comp x (h2.comp x h1)) h4
    hb123 (bijective_mfderiv_diffeomorph _ _)

theorem contMDiff_placedMap
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source) :
    ContMDiff Y.cut.Q.model X.Q.model ∞ (Y.placedMap Ψ φ Θ) := by
  intro x
  obtain ⟨t, hx⟩ := Y.exists_mem_piece x
  have hi : ContMDiffAt Y.cut.Q.model Y.cut.Q.model ∞ (Y.pieceInv t) x :=
    (Y.pieceInv t).contMDiffOn.contMDiffAt
      ((Y.pieceInv t).open_source.mem_nhds (by rw [Y.pieceInv_source]; exact hx))
  exact ((Y.contMDiff_placedSide h3 t).contMDiffAt.comp x hi).congr_of_eventuallyEq
    (Y.placedMap_eventuallyEq Ψ φ Θ t hx)

theorem bijective_mfderiv_placedMap
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (x : Y.cut.Q.Carrier) :
    Bijective (mfderiv Y.cut.Q.model X.Q.model (Y.placedMap Ψ φ Θ) x) := by
  obtain ⟨t, hx⟩ := Y.exists_mem_piece x
  have hxs : x ∈ (Y.pieceInv t).source := by rw [Y.pieceInv_source]; exact hx
  rw [(Y.placedMap_eventuallyEq Ψ φ Θ t hx).mfderiv_eq]
  have hi : MDifferentiableAt Y.cut.Q.model Y.cut.Q.model (Y.pieceInv t) x :=
    ((Y.pieceInv t).contMDiffOn.contMDiffAt
      ((Y.pieceInv t).open_source.mem_nhds hxs)).mdifferentiableAt (by simp)
  have hs : MDifferentiableAt Y.cut.Q.model X.Q.model (Y.placedSide Ψ φ Θ t) (Y.pieceInv t x) :=
    (Y.contMDiff_placedSide h3 t).mdifferentiableAt (by simp)
  exact bijective_mfderiv_comp hi hs (bijective_mfderiv_of_mem_source _ hxs)
    (Y.bijective_mfderiv_placedSide h3 t _)

theorem placedSide_mem (t : Fin 2) (x : Y.piece t) :
    Y.placedSide Ψ φ Θ t x ∈ Ψ.symm '' (φ t '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1}) := by
  refine ⟨solidTubeFill (φ t) (Θ t ((Y.solid t).symm x)), ?_, rfl⟩
  rw [← range_solidTubeFill]
  exact mem_range_self _

theorem placedMap_image_piece (t : Fin 2) :
    Y.placedMap Ψ φ Θ '' (Y.piece t) =
      Ψ.symm '' (φ t '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1}) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Y.placedMap_of_mem Ψ φ Θ t hx]
    exact Y.placedSide_mem t _
  · rintro ⟨_, hy, rfl⟩
    rw [← range_solidTubeFill] at hy
    obtain ⟨q, rfl⟩ := hy
    let x : Y.piece t := Y.solid t ((Θ t).symm q)
    refine ⟨x.val, x.property, ?_⟩
    rw [Y.placedMap_of_mem Ψ φ Θ t x.property]
    change Ψ.symm (solidTubeFill (φ t) (Θ t ((Y.solid t).symm x))) = _
    simp only [x, Diffeomorph.symm_apply_apply, Diffeomorph.apply_symm_apply]

theorem range_placedMap :
    range (Y.placedMap Ψ φ Θ) =
      Ψ.symm '' ⋃ t, φ t '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  rw [image_iUnion]
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨t, hx⟩ := Y.exists_mem_piece x
    exact mem_iUnion.mpr ⟨t, (Y.placedMap_image_piece (Ψ := Ψ) (φ := φ) (Θ := Θ) t) ▸ ⟨x, hx, rfl⟩⟩
  · intro hw
    obtain ⟨t, ht⟩ := mem_iUnion.mp hw
    rw [← Y.placedMap_image_piece (Ψ := Ψ) (φ := φ) (Θ := Θ) t] at ht
    obtain ⟨x, -, rfl⟩ := ht
    exact mem_range_self x

theorem injective_placedMap
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφd : Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1})) :
    Injective (Y.placedMap Ψ φ Θ) := by
  have hside : ∀ t (x y : Y.piece t), Y.placedSide Ψ φ Θ t x = Y.placedSide Ψ φ Θ t y → x = y := by
    intro t x y hxy
    have h := injective_solidTubeFill (h3 t) (Ψ.symm.injective hxy)
    exact (Y.solid t).symm.injective ((Θ t).injective h)
  have hcross : ∀ (x : Y.piece 0) (y : Y.piece 1),
      Y.placedSide Ψ φ Θ 0 x ≠ Y.placedSide Ψ φ Θ 1 y := by
    intro x y hxy
    obtain ⟨a, ha, hax⟩ := Y.placedSide_mem (Ψ := Ψ) (φ := φ) (Θ := Θ) 0 x
    obtain ⟨b, hb, hby⟩ := Y.placedSide_mem (Ψ := Ψ) (φ := φ) (Θ := Θ) 1 y
    have hab : a = b := Ψ.symm.injective (hax.trans (hxy.trans hby.symm))
    exact Set.disjoint_left.mp hφd ha (hab ▸ hb)
  intro x y hxy
  obtain ⟨t, hx⟩ := Y.exists_mem_piece x
  obtain ⟨t', hy⟩ := Y.exists_mem_piece y
  rw [Y.placedMap_of_mem Ψ φ Θ t hx, Y.placedMap_of_mem Ψ φ Θ t' hy] at hxy
  fin_cases t <;> fin_cases t'
  · exact congrArg Subtype.val (hside 0 ⟨x, hx⟩ ⟨y, hy⟩ hxy)
  · exact (hcross ⟨x, hx⟩ ⟨y, hy⟩ hxy).elim
  · exact (hcross ⟨y, hy⟩ ⟨x, hx⟩ hxy.symm).elim
  · exact congrArg Subtype.val (hside 1 ⟨x, hx⟩ ⟨y, hy⟩ hxy)

end SolidCapPlug

end GC.GraphManifold.Assembly
