import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.Manifold.OpenSubtype

noncomputable section

open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {n : ℕ} [NeZero n] {K : Set M} {L : Set N}
  (C : SmoothBoundaryAtlas I n K) (D : SmoothBoundaryAtlas J n L)

theorem orientation_map_of_ambient_germ
    (O : ManifoldOrientation I M n) (P : ManifoldOrientation J N n)
    (f : K → L) (g : M → N) (x : K)
    (eg : E ≃L[ℝ] F)
    (hge : ∀ v : E, eg v = mfderiv I J g x.val v)
    (hg : MDifferentiableAt I J g x.val)
    (hcomm : (Subtype.val ∘ f) =ᶠ[𝓝 x] (g ∘ Subtype.val))
    (hgo : Orientation.map (Fin n) eg.toLinearEquiv (O.orientation x.val) =
      P.orientation (g x.val)) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    let _ := D.toChartedSpace
    let _ := D.isManifold
    ∀ ef : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ v, ef v = mfderiv (𝓡∂ n) (𝓡∂ n) f x v) →
      MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f x →
      Orientation.map (Fin n) ef.toLinearEquiv ((C.orientation O).orientation x) =
        (D.orientation P).orientation (f x) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  let _ := D.toChartedSpace
  let _ := D.isManifold
  dsimp only
  intro ef hfe hf
  have hval : (f x).val = g x.val := hcomm.eq_of_nhds
  have hlin : ef.toLinearEquiv.trans (D.inclusionDifferentialEquiv (f x)).toLinearEquiv =
      (C.inclusionDifferentialEquiv x).toLinearEquiv.trans eg.toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change D.inclusionDifferentialEquiv (f x) (ef v) = eg (C.inclusionDifferentialEquiv x v)
    have h₁ := mfderiv_comp_apply (I := 𝓡∂ n) (I' := 𝓡∂ n) (I'' := J) x
      (D.contMDiff_subtype_val.mdifferentiableAt (by simp)) hf v
    have h₂ := mfderiv_comp_apply (I := 𝓡∂ n) (I' := I) (I'' := J) x hg
      (C.contMDiff_subtype_val.mdifferentiableAt (by simp)) v
    change mfderiv (𝓡∂ n) J (Subtype.val ∘ f) x v =
      D.inclusionDifferentialEquiv (f x) (mfderiv (𝓡∂ n) (𝓡∂ n) f x v) at h₁
    change mfderiv (𝓡∂ n) J (g ∘ Subtype.val) x v =
      mfderiv I J g x.val (C.inclusionDifferentialEquiv x v) at h₂
    have heq : (mfderiv (𝓡∂ n) J (Subtype.val ∘ f) x :
        EuclideanSpace ℝ (Fin n) →L[ℝ] F) =
        (mfderiv (𝓡∂ n) J (g ∘ Subtype.val) x :
          EuclideanSpace ℝ (Fin n) →L[ℝ] F) := hcomm.mfderiv_eq
    have hv : (mfderiv (𝓡∂ n) J (Subtype.val ∘ f) x v : F) =
        (mfderiv (𝓡∂ n) J (g ∘ Subtype.val) x v : F) :=
      congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] F => A v) heq
    have hl : (D.inclusionDifferentialEquiv (f x) (ef v) : F) =
        (mfderiv (𝓡∂ n) J (Subtype.val ∘ f) x v : F) :=
      (congrArg (fun w => (D.inclusionDifferentialEquiv (f x) w : F)) (hfe v)).trans h₁.symm
    have hr : (mfderiv (𝓡∂ n) J (g ∘ Subtype.val) x v : F) =
        (eg (C.inclusionDifferentialEquiv x v) : F) :=
      h₂.trans (hge (C.inclusionDifferentialEquiv x v)).symm
    exact hl.trans (hv.trans hr)
  let oK : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) := (C.orientation O).orientation x
  let oL : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
    (D.orientation P).orientation (f x)
  let oM : Orientation ℝ E (Fin n) := O.orientation x.val
  let oN : Orientation ℝ F (Fin n) := P.orientation (f x).val
  have hC : Orientation.map (Fin n) (C.inclusionDifferentialEquiv x).toLinearEquiv oK = oM :=
    C.orientation_map_inclusion O x
  have hD : Orientation.map (Fin n) (D.inclusionDifferentialEquiv (f x)).toLinearEquiv oL = oN :=
    D.orientation_map_inclusion P (f x)
  let p : N → Orientation ℝ F (Fin n) := P.orientation
  have hp := congrArg p hval
  change Orientation.map (Fin n) eg.toLinearEquiv oM =
    (P.orientation (g x.val) : Orientation ℝ F (Fin n)) at hgo
  have hG : Orientation.map (Fin n) eg.toLinearEquiv oM = oN := hgo.trans hp.symm
  change Orientation.map (Fin n) ef.toLinearEquiv oK = oL
  apply (Orientation.map (Fin n) (D.inclusionDifferentialEquiv (f x)).toLinearEquiv).injective
  rw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin]
  rw [← DifferentialGeometry.VectorBundle.map_orientation_trans_between, hC, hD, hG]


theorem orientation_map_of_open_ambient_germ
    (O : ManifoldOrientation I M n) (P : ManifoldOrientation J N n)
    (f : K → L) (U : TopologicalSpace.Opens M) (g : U → N) (x : K) (hx : x.val ∈ U)
    (eg : E ≃L[ℝ] F)
    (hge : ∀ v : E, eg v = mfderiv I J g ⟨x.val, hx⟩ v)
    (hg : MDifferentiableAt I J g ⟨x.val, hx⟩)
    (hcomm : ∀ᶠ y in 𝓝 x, ∀ hy : y.val ∈ U, (f y).val = g ⟨y.val, hy⟩)
    (hgo : Orientation.map (Fin n) eg.toLinearEquiv (O.orientation x.val) =
      P.orientation (g ⟨x.val, hx⟩)) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    let _ := D.toChartedSpace
    let _ := D.isManifold
    ∀ ef : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ v, ef v = mfderiv (𝓡∂ n) (𝓡∂ n) f x v) →
      MDifferentiableAt (𝓡∂ n) (𝓡∂ n) f x →
      Orientation.map (Fin n) ef.toLinearEquiv ((C.orientation O).orientation x) =
        (D.orientation P).orientation (f x) := by
  classical
  let g' : M → N := fun y => if hy : y ∈ U then g ⟨y, hy⟩ else g ⟨x.val, hx⟩
  have hres : (fun y : U => g' y.val) = g := by
    funext y
    exact dite_eq_left y.property
  have hg' : MDifferentiableAt I J g' x.val :=
    DifferentialGeometry.mdifferentiableAt_subtype_iff.mp (hres ▸ hg)
  have hder : (mfderiv I J g' x.val : E →L[ℝ] F) =
      (mfderiv I J g ⟨x.val, hx⟩ : E →L[ℝ] F) := by
    rw [← DifferentialGeometry.mfderiv_restrict_open g' U ⟨x.val, hx⟩, hres]
  have hge' (v : E) : eg v = mfderiv I J g' x.val v := by
    rw [hder]
    exact hge v
  have hcomm' : (Subtype.val ∘ f) =ᶠ[𝓝 x] (g' ∘ Subtype.val) := by
    have hU : ∀ᶠ y : K in 𝓝 x, y.val ∈ U :=
      (continuous_subtype_val.continuousAt).eventually (U.isOpen.mem_nhds hx)
    filter_upwards [hcomm, hU] with y hy hyU
    change (f y).val = g' y.val
    have hv : g' y.val = g ⟨y.val, hyU⟩ := dite_eq_left hyU
    exact (hy hyU).trans hv.symm
  have hgo' : Orientation.map (Fin n) eg.toLinearEquiv (O.orientation x.val) =
      P.orientation (g' x.val) := by
    let p : N → Orientation ℝ F (Fin n) := P.orientation
    have hv : g' x.val = g ⟨x.val, hx⟩ := dite_eq_left hx
    have hp := congrArg p hv
    change Orientation.map (Fin n) eg.toLinearEquiv (O.orientation x.val) =
      (P.orientation (g ⟨x.val, hx⟩) : Orientation ℝ F (Fin n)) at hgo
    exact hgo.trans hp.symm
  exact C.orientation_map_of_ambient_germ D O P f g' x eg hge' hg' hcomm' hgo'

theorem orientation_map_of_open_ambient_map
    (O : ManifoldOrientation I M n) (P : ManifoldOrientation J N n)
    (f : K → L) (U : TopologicalSpace.Opens M) (g : U → N) (x : K) (hx : x.val ∈ U)
    (hg : IsLocalDiffeomorphAt I J ∞ g ⟨x.val, hx⟩)
    (hcomm : ∀ y : K, ∀ hy : y.val ∈ U, (f y).val = g ⟨y.val, hy⟩)
    (hgo : Orientation.map (Fin n)
      (hg.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (O.orientation x.val) = P.orientation (g ⟨x.val, hx⟩)) :
    let _ := C.toChartedSpace
    let _ := C.isManifold
    let _ := D.toChartedSpace
    let _ := D.isManifold
    ∀ hf : IsLocalDiffeomorphAt (𝓡∂ n) (𝓡∂ n) ∞ f x,
      Orientation.map (Fin n)
        (hf.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
        ((C.orientation O).orientation x) = (D.orientation P).orientation (f x) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  let _ := D.toChartedSpace
  let _ := D.isManifold
  dsimp only
  intro hf
  exact C.orientation_map_of_open_ambient_germ D O P f U g x hx
    (hg.mfderivToContinuousLinearEquiv (by simp)) (fun _ => rfl)
    (hg.mdifferentiableAt (by simp)) (Filter.Eventually.of_forall hcomm) hgo
    (hf.mfderivToContinuousLinearEquiv (by simp)) (fun _ => rfl)
    (hf.mdifferentiableAt (by simp))

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
