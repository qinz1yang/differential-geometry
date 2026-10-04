import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreTube

/-!
A single actual base chart and regular-fibre tube with full fibre saturation and disc image ledgers.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.CircleFibration

universe u

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

private def openSaturatedTranslation (a : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toEquiv := Equiv.addRight a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

private def openSaturatedScaledPlane (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r) :
    PlaneLift.{u} ≃ₘ⟮𝓘(ℝ, ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.trans
    (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toDiffeomorph.trans
      ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
        (M₁ := EuclideanSpace ℝ (Fin 2)) (Units.mk0 r hr.ne')).toDiffeomorph.trans
          (openSaturatedTranslation a)))

private theorem openSaturatedScaledPlane_dist (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hr : 0 < r) (z : PlaneLift.{u}) :
    dist (openSaturatedScaledPlane a r hr z) a = r * ‖z.down‖ := by
  change dist (r • Complex.orthonormalBasisOneI.repr z.down + a) a = _
  rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, Complex.orthonormalBasisOneI.repr.norm_map]

private theorem exists_openSaturatedBaseChart (F : CircleFibration C U) :
    ∃ b : F.base.Carrier,
    ∃ β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
        PlaneLift.{u} F.base.Carrier ∞,
      {z | ‖z.down‖ ≤ 3} ⊆ β.source ∧
      β.target ⊆ F.neighborhood b ∧
      β.target ⊆ (SurfaceModel.model F.base.kind).interior F.base.Carrier := by
  obtain ⟨b, hb⟩ :=
    (DifferentialGeometry.Topology.Manifold.dense_manifold_interior
      (I := SurfaceModel.model F.base.kind) (M := F.base.Carrier)).nonempty
  let c := DifferentialGeometry.Manifold.interiorChart (SurfaceModel.model F.base.kind) ∞ b
  obtain ⟨R, hR, ht, hV⟩ :=
    DifferentialGeometry.Manifold.exists_interiorChart_closedBall_subset
      (SurfaceModel.model F.base.kind) hb
      ((F.neighborhood b).isOpen.mem_nhds (F.mem_neighborhood b))
  let d := DifferentialGeometry.Topology.PartialDiffeomorph.restrict c
    (F.neighborhood b) (F.neighborhood b).isOpen
  let A := openSaturatedScaledPlane (c b) (R / 4) (by positivity)
  let β := A.toPartialDiffeomorph.trans d.symm
  refine ⟨b, β, ?_, ?_, ?_⟩
  · intro z hz
    have hdist : dist (A z) (c b) ≤ R := by
      rw [openSaturatedScaledPlane_dist]
      have h := mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ R / 4)
      linarith
    have hball : A z ∈ closedBall (c b) R := hdist
    change z ∈ Set.univ ∧ A z ∈ c.target ∩ c.symm ⁻¹' (F.neighborhood b)
    exact ⟨mem_univ z, ht hball, hV ⟨A z, hball, rfl⟩⟩
  · intro y hy
    exact hy.1.2
  · intro y hy
    exact DifferentialGeometry.Manifold.isInteriorPoint_of_mem_interiorChart_source
      (SurfaceModel.model F.base.kind) ∞ (by simp) hy.1.1

theorem exists_openSaturatedRegularFibreTube (F : CircleFibration C U) :
    ∃ β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
        PlaneLift.{u} F.base.Carrier ∞,
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
        (PlaneLift.{u} × Circle) C.Carrier ∞,
      {z | ‖z.down‖ ≤ 3} ⊆ β.source ∧
      φ.source = β.source ×ˢ Set.univ ∧
      φ.target ⊆ (U ⊓ C.interior : TopologicalSpace.Opens C.Carrier) ∧
      β.target ⊆ (SurfaceModel.model F.base.kind).interior F.base.Carrier ∧
      (∀ (z : PlaneLift.{u}) (t : Circle), z ∈ β.source →
        ∃ hu : φ (z, t) ∈ U, F.projection ⟨φ (z, t), hu⟩ = β z) ∧
      φ.target = Subtype.val '' {x : U | F.projection x ∈ β.target} ∧
      φ '' {p | ‖p.1.down‖ ≤ 1} =
        Subtype.val '' {x : U | F.projection x ∈ β '' {z | ‖z.down‖ ≤ 1}} ∧
      φ '' {p | ‖p.1.down‖ < 1} =
        Subtype.val '' {x : U | F.projection x ∈ β '' {z | ‖z.down‖ < 1}} := by
  obtain ⟨b, β, hβ, hV, hI⟩ := exists_openSaturatedBaseChart F
  let V := F.neighborhood b
  have hVne : Nonempty V := ⟨⟨b, F.mem_neighborhood b⟩⟩
  let incV := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := SurfaceModel.model F.base.kind) V hVne
  have hincV : incV.target = (V : Set F.base.Carrier) :=
    V.openPartialHomeomorphSubtypeCoe_target hVne
  let α := β.trans incV.symm
  have hα : α.source = β.source := by
    ext z
    change (z ∈ β.source ∧ β z ∈ incV.target) ↔ z ∈ β.source
    rw [hincV]
    exact ⟨And.left, fun hz => ⟨hz, hV (β.toPartialEquiv.map_source hz)⟩⟩
  let W := TopologicalSpace.Opens.comap F.projection V
  have hWne : Nonempty W := ⟨(F.trivialization b).symm (⟨b, F.mem_neighborhood b⟩, 1)⟩
  have hUne : Nonempty U := ⟨(Classical.choice hWne).val⟩
  let incW := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := C.model) W hWne
  let incU := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := C.model) U hUne
  have hincU : incU.target = (U : Set C.Carrier) :=
    U.openPartialHomeomorphSubtypeCoe_target hUne
  let B := ((F.trivialization b).symm.toPartialDiffeomorph.trans incW).trans incU
  have hB : B.source = Set.univ := by
    ext q
    change ((q ∈ Set.univ ∧ (F.trivialization b).symm q ∈ Set.univ) ∧
      incW ((F.trivialization b).symm q) ∈ Set.univ) ↔ q ∈ Set.univ
    simp only [mem_univ, and_self]
  let T := DifferentialGeometry.Topology.PartialDiffeomorph.prod α
    (Diffeomorph.refl (𝓡 1) Circle ∞).toPartialDiffeomorph
  let φ := T.trans B
  have hφ : φ.source = β.source ×ˢ Set.univ := by
    ext p
    change (p ∈ α.source ×ˢ Set.univ ∧ T p ∈ B.source) ↔
      p ∈ β.source ×ˢ Set.univ
    rw [hα, hB]
    simp only [mem_univ, and_true]
  have hφU : φ.target ⊆ U := by
    intro y hy
    exact hincU ▸ hy.1.1
  have htarget : φ.target ⊆ (U ⊓ C.interior : TopologicalSpace.Opens C.Carrier) := by
    intro y hy
    refine ⟨hφU hy, ?_⟩
    have hx := φ.toPartialEquiv.map_target hy
    have hlocal := φ.isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model ∞ hx
    have hi := (hlocal.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
      BoundarylessManifold.isInteriorPoint
    rwa [φ.toPartialEquiv.right_inv hy] at hi
  have hprojection : ∀ z t, z ∈ β.source → ∀ hu : φ (z, t) ∈ U,
      F.projection ⟨φ (z, t), hu⟩ = β z := by
    intro z t hz hu
    have hzV := hV (β.toPartialEquiv.map_source hz)
    have hαval : (α z).val = β z :=
      incV.toPartialEquiv.right_inv (hincV.symm ▸ hzV)
    have hproj := F.projection_trivialization b ((F.trivialization b).symm (α z, t))
    rw [Diffeomorph.apply_symm_apply, hαval] at hproj
    exact hproj.symm
  have hsaturated : φ.target = Subtype.val '' {x : U | F.projection x ∈ β.target} := by
    ext x
    constructor
    · intro hx
      have hp := φ.map_target hx
      rw [hφ] at hp
      let y : U := ⟨x, hφU hx⟩
      have hu := hφU (φ.map_source (hφ.symm ▸ hp))
      have he := hprojection (φ.symm x).1 (φ.symm x).2 hp.1 hu
      have hy : (⟨φ (φ.symm x), hu⟩ : U) = y :=
        Subtype.ext (φ.right_inv hx)
      rw [hy] at he
      refine ⟨y, ?_, rfl⟩
      change F.projection y ∈ β.target
      exact he.symm ▸ β.map_source hp.1
    · rintro ⟨xU, hx, rfl⟩
      let xW : W := ⟨xU, hV hx⟩
      let z := β.symm (F.projection xU)
      have hz : z ∈ β.source := β.map_target hx
      have hzV := hV (β.map_source hz)
      have hαval : (α z).val = β z :=
        incV.right_inv (hincV.symm ▸ hzV)
      have he : α z = (F.trivialization b xW).1 := by
        apply Subtype.ext
        rw [hαval]
        exact (β.right_inv (x := F.projection xU) hx).trans
          (F.projection_trivialization b xW).symm
      have hpoint : φ (z, (F.trivialization b xW).2) = xU.val := by
        change (((F.trivialization b).symm (α z, (F.trivialization b xW).2)).val).val = _
        rw [he, Prod.mk.eta, Diffeomorph.symm_apply_apply]
      exact hpoint ▸ φ.map_source (hφ.symm ▸ ⟨hz, mem_univ _⟩)
  have himage : ∀ S : Set PlaneLift.{u}, S ⊆ β.source →
      φ '' (S ×ˢ univ) = Subtype.val '' {x : U | F.projection x ∈ β '' S} := by
    intro S hS
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hps : p ∈ φ.source := hφ.symm ▸ ⟨hS hp.1, hp.2⟩
      let y : U := ⟨φ p, hφU (φ.map_source hps)⟩
      exact ⟨y, ⟨p.1, hp.1, (hprojection p.1 p.2 (hS hp.1) y.property).symm⟩, rfl⟩
    · rintro ⟨y, ⟨z, hz, he⟩, rfl⟩
      have hy : y.val ∈ φ.target := by
        rw [hsaturated]
        refine ⟨y, ?_, rfl⟩
        change F.projection y ∈ β.target
        rw [← he]
        exact β.map_source (hS hz)
      have hp := φ.map_target hy
      rw [hφ] at hp
      have hu := hφU (φ.map_source (hφ.symm ▸ hp))
      have hproj := hprojection (φ.symm y.val).1 (φ.symm y.val).2 hp.1 hu
      have heq : (⟨φ (φ.symm y.val), hu⟩ : U) = y := Subtype.ext (φ.right_inv hy)
      rw [heq] at hproj
      have hz' : (φ.symm y.val).1 = z :=
        β.injOn hp.1 (hS hz) (hproj.symm.trans he.symm)
      exact ⟨φ.symm y.val, ⟨hz'.symm ▸ hz, mem_univ _⟩, φ.right_inv hy⟩
  refine ⟨β, φ, hβ, hφ, htarget, hI, ?_, hsaturated, ?_, ?_⟩
  · intro z t hz
    have hp : (z, t) ∈ φ.source := hφ.symm ▸ ⟨hz, mem_univ t⟩
    have hu := hφU (φ.map_source hp)
    exact ⟨hu, hprojection z t hz hu⟩
  · have hS : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} ⊆ β.source := by
      intro z hz
      apply hβ
      change ‖z.down‖ ≤ 3
      change ‖z.down‖ ≤ 1 at hz
      linarith
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} =
        {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} ×ˢ univ := by ext p; simp
    rw [he]
    exact himage _ hS
  · have hS : {z : PlaneLift.{u} | ‖z.down‖ < 1} ⊆ β.source := by
      intro z hz
      apply hβ
      change ‖z.down‖ ≤ 3
      change ‖z.down‖ < 1 at hz
      linarith
    have he : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1} =
        {z : PlaneLift.{u} | ‖z.down‖ < 1} ×ˢ univ := by ext p; simp
    rw [he]
    exact himage _ hS

end GC.GraphManifold.CircleFibration
