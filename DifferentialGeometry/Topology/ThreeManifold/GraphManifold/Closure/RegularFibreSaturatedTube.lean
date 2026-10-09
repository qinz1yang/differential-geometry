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

private def saturatedTranslation (a : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toEquiv := Equiv.addRight a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

private def saturatedScaledPlane (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r) :
    PlaneLift.{u} ≃ₘ⟮𝓘(ℝ, ℂ), 𝓡 2⟯ EuclideanSpace ℝ (Fin 2) :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.trans
    (Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.toDiffeomorph.trans
      ((ContinuousLinearEquiv.smulLeft (R₁ := ℝ)
        (M₁ := EuclideanSpace ℝ (Fin 2)) (Units.mk0 r hr.ne')).toDiffeomorph.trans
          (saturatedTranslation a)))

private theorem saturatedScaledPlane_dist (a : EuclideanSpace ℝ (Fin 2)) (r : ℝ)
    (hr : 0 < r) (z : PlaneLift.{u}) :
    dist (saturatedScaledPlane a r hr z) a = r * ‖z.down‖ := by
  change dist (r • Complex.orthonormalBasisOneI.repr z.down + a) a = _
  rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr, Complex.orthonormalBasisOneI.repr.norm_map]

private theorem exists_saturatedBaseChart (F : CircleFibration C U) :
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
  let A := saturatedScaledPlane (c b) (R / 4) (by positivity)
  let β := A.toPartialDiffeomorph.trans d.symm
  refine ⟨b, β, ?_, ?_, ?_⟩
  · intro z hz
    have hdist : dist (A z) (c b) ≤ R := by
      rw [saturatedScaledPlane_dist]
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

theorem exists_saturatedRegularFibreTube (F : CircleFibration C ⊤) :
    ∃ β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
        PlaneLift.{u} F.base.Carrier ∞,
    ∃ φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
        (PlaneLift.{u} × Circle) C.Carrier ∞,
      {z | ‖z.down‖ ≤ 3} ⊆ β.source ∧
      φ.source = β.source ×ˢ Set.univ ∧
      φ.target ⊆ (⊤ ⊓ C.interior : TopologicalSpace.Opens C.Carrier) ∧
      β.target ⊆ (SurfaceModel.model F.base.kind).interior F.base.Carrier ∧
      (∀ (z : PlaneLift.{u}) (t : Circle), z ∈ β.source →
        F.projection ⟨φ (z, t), trivial⟩ = β z) ∧
      φ.target = {x | F.projection ⟨x, trivial⟩ ∈ β.target} ∧
      φ '' {p | ‖p.1.down‖ ≤ 1} =
        {x | F.projection ⟨x, trivial⟩ ∈ β '' {z | ‖z.down‖ ≤ 1}} ∧
      φ '' {p | ‖p.1.down‖ < 1} =
        {x | F.projection ⟨x, trivial⟩ ∈ β '' {z | ‖z.down‖ < 1}} := by
  let U : TopologicalSpace.Opens C.Carrier := ⊤
  obtain ⟨b, β, hβ, hV, hI⟩ := exists_saturatedBaseChart F
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
  have htarget : φ.target ⊆ (⊤ ⊓ C.interior : TopologicalSpace.Opens C.Carrier) := by
    intro y hy
    refine ⟨trivial, ?_⟩
    have hx := φ.toPartialEquiv.map_target hy
    have hlocal := φ.isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model ∞ hx
    have hi := (hlocal.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
      BoundarylessManifold.isInteriorPoint
    rwa [φ.toPartialEquiv.right_inv hy] at hi
  let π : C.Carrier → F.base.Carrier := fun x => F.projection ⟨x, trivial⟩
  have hprojection : ∀ z t, z ∈ β.source → F.projection ⟨φ (z, t), trivial⟩ = β z := by
    intro z t hz
    have hzV := hV (β.toPartialEquiv.map_source hz)
    have hαval : (α z).val = β z :=
      incV.toPartialEquiv.right_inv (hincV.symm ▸ hzV)
    have hproj := F.projection_trivialization b ((F.trivialization b).symm (α z, t))
    rw [Diffeomorph.apply_symm_apply, hαval] at hproj
    exact hproj.symm
  have hsaturated : φ.target = {x | F.projection ⟨x, trivial⟩ ∈ β.target} := by
    ext x
    constructor
    · intro hx
      have hp := φ.map_target hx
      rw [hφ] at hp
      have he := hprojection (φ.symm x).1 (φ.symm x).2 hp.1
      change π (φ (φ.symm x)) = β (φ.symm x).1 at he
      have he' : π x = β (φ.symm x).1 :=
        (congrArg π (φ.toPartialEquiv.right_inv hx)).symm.trans he
      change π x ∈ β.target
      exact he'.symm ▸ β.map_source hp.1
    · intro hx
      let xU : (⊤ : TopologicalSpace.Opens C.Carrier) := ⟨x, trivial⟩
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
      have hpoint : φ (z, (F.trivialization b xW).2) = x := by
        change (((F.trivialization b).symm (α z, (F.trivialization b xW).2)).val).val = x
        rw [he, Prod.mk.eta, Diffeomorph.symm_apply_apply]
      exact hpoint ▸ φ.map_source (hφ.symm ▸ ⟨hz, mem_univ _⟩)
  have himage : ∀ S : Set PlaneLift.{u}, S ⊆ β.source →
      φ '' (S ×ˢ univ) = {x | F.projection ⟨x, trivial⟩ ∈ β '' S} := by
    intro S hS
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.1, hp.1, (hprojection p.1 p.2 (hS hp.1)).symm⟩
    · rintro ⟨z, hz, he⟩
      have hx : x ∈ φ.target := by
        rw [hsaturated]
        change F.projection ⟨x, trivial⟩ ∈ β.target
        rw [← he]
        exact β.map_source (hS hz)
      have hp := φ.map_target hx
      rw [hφ] at hp
      have hproj := hprojection (φ.symm x).1 (φ.symm x).2 hp.1
      change π (φ (φ.symm x)) = β (φ.symm x).1 at hproj
      have hproj' : π x = β (φ.symm x).1 :=
        (congrArg π (φ.toPartialEquiv.right_inv hx)).symm.trans hproj
      have hz' : (φ.symm x).1 = z := β.injOn hp.1 (hS hz) (hproj'.symm.trans he.symm)
      exact ⟨φ.symm x, ⟨hz'.symm ▸ hz, mem_univ _⟩, φ.right_inv hx⟩
  refine ⟨β, φ, hβ, hφ, htarget, hI, hprojection, hsaturated, ?_, ?_⟩
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
