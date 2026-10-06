/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FixtureSolidTorusMain

set_option autoImplicit false

/-!
# Fixture FX2 (loop): the delivered abstract theorems inhabited on the solid torus
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open GC.GraphManifold
open scoped Manifold ContDiff

namespace GC.LongTime.CuspP1
open GC.Endpoint

/-- Exact boundary trace inside `W`: `diskTrace u = φ ∘ γ`. -/
theorem diskTrace_uW_FX2 : diskTrace uW_FX2 = φ_FX2.comp γ_FX2 := by
  ext θ
  exact u_boundary_FX2 θ

/-- The disk, seen in `M`, has exact trace `γ` pushed into `M`. -/
theorem diskTrace_u_FX2 (θ : loopCircle) :
    diskTrace u_FX2 θ = (φ_FX2 (γ_FX2 θ) : M_FX2) := u_boundary_FX2 θ

theorem not_simplyConnected_circle_FX2 : ¬ SimplyConnectedSpace Circle := by
  intro h
  let g := fundamentalGroupCircleEquivInt
  have hg := (simplyConnectedSpace_iff_fundamentalGroup_eq_one (1 : Circle)).mp
    inferInstance (g.symm (Multiplicative.ofAdd (1 : ℤ)))
  have he := congrArg (fun x => Multiplicative.toAdd (g x)) hg
  simp only [MulEquiv.apply_symm_apply, map_one, toAdd_ofAdd, toAdd_one] at he
  exact one_ne_zero he

/-- The meridian is essential in the boundary torus. -/
theorem meridian_not_nullhomotopic_FX2 : ¬ γ_FX2.Nullhomotopic := by
  intro H
  have h1 := H.comp_right (ContinuousMap.fst : C(Torus, Circle))
  let e : Circle ≃ₜ loopCircle := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
  have h2 := h1.comp_left (e : C(Circle, loopCircle))
  have hid : ((ContinuousMap.fst : C(Torus, Circle)).comp γ_FX2).comp (e : C(Circle, loopCircle)) =
      ContinuousMap.id Circle := by
    refine ContinuousMap.ext fun z => ?_
    change (AddCircle.toCircle (e z) : Circle) = z
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).apply_symm_apply z
  rw [hid] at h2
  have : ContractibleSpace Circle := (contractible_iff_id_nullhomotopic Circle).mpr h2
  exact not_simplyConnected_circle_FX2 inferInstance

theorem loopDegreeClass_one_ne_one_of_not_null_FX2 {X : Type*} [TopologicalSpace X]
    (γ : freeLoop X) (h : ¬ γ.Nullhomotopic) : loopDegreeClass γ 1 ≠ 1 := by
  intro h1
  apply h
  rw [loopDegreeClass, intLoop_one] at h1
  have hp : pathToCircle (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0))) = γ :=
    congrArg Subtype.val ((basedPathCircleHomeomorph (γ 0)).apply_symm_apply ⟨γ, rfl⟩)
  have h2 := (pathToCircle_nullhomotopic_iff
    (circleToPath (⟨γ, rfl⟩ : basedCircleLoop (γ 0)))).mpr (Path.Homotopic.Quotient.eq.mp h1)
  rwa [hp] at h2

/-- (1) the meridian class lies in the kernel of `π₁(∂W) → π₁(W)`. -/
theorem meridian_mem_ker_FX2 :
    loopDegreeClass γ_FX2 1 ∈ (FundamentalGroup.map φ_FX2 (γ_FX2 0)).ker := by
  refine loopDegreeClass_one_mem_ker_LTP4 φ_FX2 γ_FX2 ?_
  rw [← diskTrace_uW_FX2]
  exact diskTrace_nullhomotopic uW_FX2

/-- (1) `π₁(∂W) → π₁(W)` is not injective (kernel contains the nontrivial meridian class). -/
theorem not_injective_boundary_FX2 :
    ¬ Function.Injective (FundamentalGroup.map φ_FX2 (γ_FX2 0)) := by
  intro hinj
  have hk := meridian_mem_ker_FX2
  rw [MonoidHom.mem_ker] at hk
  exact loopDegreeClass_one_ne_one_of_not_null_FX2 γ_FX2 meridian_not_nullhomotopic_FX2
    (hinj (hk.trans (map_one _).symm))

/-- The meridian is a topological embedding. -/
theorem meridian_isEmbedding_FX2 : Topology.IsEmbedding γ_FX2 := by
  refine Continuous.isClosedEmbedding γ_FX2.continuous ?_ |>.isEmbedding
  intro a b hab
  exact AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero (congrArg Prod.fst hab)

/-- (3) the meridian is primitive in `π₁(∂W) ≅ ℤ × ℤ`. -/
theorem meridian_primitive_FX2 :
    ∃ e : FundamentalGroup Torus (γ_FX2 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
      e (loopDegreeClass γ_FX2 1) = (Multiplicative.ofAdd 1, 1) :=
  exists_primitive_of_embedded_CPP2 γ_FX2 meridian_isEmbedding_FX2 meridian_not_nullhomotopic_FX2

/-! ### Orientation and the Loop Theorem (bicollared-boundary form) -/

/-- Tangent orientation of `S³`. -/
def o_FX2 : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection M_FX2 :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TangentOrientationSection.ofManifoldOrientation
    standardThreeSphereLift.{0}.orientation

/-- (2) `exists_essential_embedded_null_of_bicollared_boundary_LTP4` applied to the solid torus:
all hypotheses (orientation, bicollar, side, front, closedness, boundary parametrisation,
non-injectivity) are supplied by the concrete data. -/
theorem loopTheorem_output_FX2 :
    ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
      loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ_FX2 (γ 0)).ker :=
  exists_essential_embedded_null_of_bicollared_boundary_LTP4 (ι := Unit) o_FX2 σ_FX2
    σ_FX2_source W_FX2 isClosed_W_FX2 hside_FX2 hfront_FX2 () φ_FX2 (fun _ => rfl) (γ_FX2 0)
    not_injective_boundary_FX2

end GC.LongTime.CuspP1
