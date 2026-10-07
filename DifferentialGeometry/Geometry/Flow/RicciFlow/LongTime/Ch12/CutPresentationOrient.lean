import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDifferential
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff
namespace GC.LongTime.Ch12

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

/-- A partial diffeomorphism is a diffeomorphism between its (open) source and target. -/
def partialDiffeoSubtype_S12 (G : PartialDiffeomorph I I N N ∞) :
    (⟨G.source, G.open_source⟩ : TopologicalSpace.Opens N) ≃ₘ⟮I, I⟯
      (⟨G.target, G.open_target⟩ : TopologicalSpace.Opens N) where
  toFun x := ⟨G x.1, G.map_source x.2⟩
  invFun y := ⟨G.symm y.1, G.symm.map_source y.2⟩
  left_inv x := Subtype.ext (G.left_inv x.2)
  right_inv y := Subtype.ext (G.right_inv y.2)
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact G.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact G.symm.contMDiffOn.comp_contMDiff contMDiff_subtype_val (fun x => x.2)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ N] in
theorem mfderiv_partialDiffeoSubtype_S12 (G : PartialDiffeomorph I I N N ∞)
    (x : (⟨G.source, G.open_source⟩ : TopologicalSpace.Opens N)) (v : TangentSpace I x) :
    mfderiv I I (partialDiffeoSubtype_S12 G) x v = mfderiv I I G x.1 v := by
  have h1 : (Subtype.val : (⟨G.target, G.open_target⟩ : TopologicalSpace.Opens N) → N) ∘
      (partialDiffeoSubtype_S12 G) = G ∘ (Subtype.val) := rfl
  have e1 := mfderiv_comp (I := I) (I' := I) (I'' := I) x
    ((contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiableAt (by simp)
      (x := partialDiffeoSubtype_S12 G x))
    ((partialDiffeoSubtype_S12 G).contMDiff.mdifferentiableAt (by simp))
  have e2 := mfderiv_comp (I := I) (I' := I) (I'' := I) x
    ((G.contMDiffOn.contMDiffAt (G.open_source.mem_nhds x.2)).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiableAt (by simp) (x := x))
  rw [h1] at e1
  rw [e2, DifferentialGeometry.mfderiv_subtype_val] at e1
  have := DFunLike.congr_fun e1 v
  rw [DifferentialGeometry.mfderiv_subtype_val] at this
  exact this.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Orientation propagation.** A partial diffeomorphism of `N` whose target is preconnected and
which preserves the orientation `O` at one point of its source preserves it at every point of its
source. -/
theorem orientation_propagate_S12 {n : ℕ} (G : PartialDiffeomorph I I N N ∞)
    (hconn : IsPreconnected G.target) (O : ManifoldOrientation I N n) {y0 : N}
    (hy0 : y0 ∈ G.source)
    (h0 : Orientation.map (Fin n)
      ((G.isLocalDiffeomorphAt I I ∞ hy0).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (O.orientation y0) = O.orientation (G y0))
    {y : N} (hy : y ∈ G.source) :
    Orientation.map (Fin n)
      ((G.isLocalDiffeomorphAt I I ∞ hy).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (O.orientation y) = O.orientation (G y) := by
  have : PreconnectedSpace (⟨G.target, G.open_target⟩ : TopologicalSpace.Opens N) :=
    isPreconnected_iff_preconnectedSpace.mp hconn
  let e := partialDiffeoSubtype_S12 G
  have key : ∀ x : (⟨G.source, G.open_source⟩ : TopologicalSpace.Opens N),
      (e.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv =
        ((G.isLocalDiffeomorphAt I I ∞ x.2).mfderivToContinuousLinearEquiv (by simp)
          |>.toLinearEquiv : TangentSpace I x ≃ₗ[ℝ] TangentSpace I (e x)) := by
    intro x
    ext v
    exact mfderiv_partialDiffeoSubtype_S12 G x v
  have hP := Diffeomorph.preservesOrientation_of_eq_at e (O.restrictOpen _) (O.restrictOpen _)
    ⟨y0, hy0⟩ (by
      rw [key]
      exact h0)
  have := hP ⟨y, hy⟩
  rw [key] at this
  exact this

/-- A partial diffeomorphism which is the identity near a point preserves every orientation
there. -/
theorem orientation_of_eventuallyEq_id_S12 {n : ℕ} (G : PartialDiffeomorph I I N N ∞)
    (O : ManifoldOrientation I N n) {y0 : N} (hy0 : y0 ∈ G.source)
    (h : G =ᶠ[nhds y0] id) :
    Orientation.map (Fin n)
      ((G.isLocalDiffeomorphAt I I ∞ hy0).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (O.orientation y0) = O.orientation (G y0) := by
  have hd : mfderiv I I G y0 = ContinuousLinearMap.id ℝ _ := by
    rw [h.mfderiv_eq]; exact mfderiv_id
  have key : ∀ (w : N) (_ : w = y0) (L : TangentSpace I y0 ≃ₗ[ℝ] TangentSpace I w),
      (∀ v, L v = v) → Orientation.map (Fin n) L (O.orientation y0) = O.orientation w := by
    rintro w rfl L hL
    have : L = LinearEquiv.refl ℝ _ := LinearEquiv.ext hL
    rw [this, Orientation.map_refl]; rfl
  refine key (G y0) h.eq_of_nhds _ (fun v => ?_)
  change mfderiv I I G y0 v = v
  rw [hd]; rfl

end General

end GC.LongTime.Ch12
