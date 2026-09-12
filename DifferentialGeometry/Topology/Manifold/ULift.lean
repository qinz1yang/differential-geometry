import DifferentialGeometry.Topology.Manifold.ClosedOriented
import Mathlib.Topology.Connected.Basic

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v uE uH

@[implicit_reducible]
def uliftChartedSpace (H : Type uH) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    ChartedSpace H (ULift.{v} M) :=
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  letI : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  ChartedSpace.comp H M (ULift.{v} M)

attribute [local instance] uliftChartedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

theorem isManifold_ulift [IsManifold I ∞ M] : IsManifold I ∞ (ULift.{v} M) := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  let : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  let : HasGroupoid (ULift.{v} M) (@idRestrGroupoid M _) :=
    h.toOpenPartialHomeomorph.singleton_hasGroupoid (by simp [h]) (@idRestrGroupoid M _)
  let : HasGroupoid (ULift.{v} M) (contDiffGroupoid ∞ I) :=
    StructureGroupoid.HasGroupoid.comp (G₂ := @idRestrGroupoid M _) (by
      intro f hf
      have hsmooth {a : OpenPartialHomeomorph M M}
          (ha : a ∈ @idRestrGroupoid M _) : ContMDiffOn I I ∞ a a.source := by
        rcases ha with ⟨s, hs, ha⟩
        refine contMDiffOn_id.congr ?_
        intro x hx
        have hx' := OpenPartialHomeomorph.EqOnSource.eqOn ha hx
        simpa using hx'
      rw [isLocalStructomorphOn_contDiffGroupoid_iff]
      exact ⟨hsmooth hf, by
        simpa only [mfld_simps] using hsmooth ((@idRestrGroupoid M _).symm hf)⟩)
  exact IsManifold.mk' I ∞ (ULift.{v} M)

attribute [local instance] isManifold_ulift

def uliftDiffeomorph : M ≃ₘ⟮I, I⟯ ULift.{v} M := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  refine
    { toEquiv := h.toEquiv.symm
      contMDiff_toFun := fun x => ?_
      contMDiff_invFun := fun x => ?_ }
  · refine contMDiffWithinAt_iff'.2 ⟨h.symm.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp
  · refine contMDiffWithinAt_iff'.2 ⟨h.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp

@[simp]
theorem uliftDiffeomorph_apply (x : M) : uliftDiffeomorph I M x = ULift.up x := rfl

@[simp]
theorem uliftDiffeomorph_symm_apply (x : ULift.{v} M) :
    (uliftDiffeomorph I M).symm x = x.down := rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] {n : ℕ}

omit [FiniteDimensional ℝ E] in
theorem chartAt_ulift (x : M) :
    chartAt H (ULift.up x : ULift.{v} M) =
      Homeomorph.ulift.toOpenPartialHomeomorph ≫ₕ chartAt H x := by
  let : ChartedSpace M (ULift.{v} M) :=
    Homeomorph.ulift.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  change @chartAt H _ (ULift.{v} M) _ (ChartedSpace.comp H M (ULift.{v} M))
    (ULift.up x) = _
  rw [chartAt_comp H M (ULift.up x : ULift.{v} M),
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extChartAt_ulift (x y : M) :
    extChartAt I (ULift.up x : ULift.{v} M) (ULift.up y) = extChartAt I x y := by
  rw [extChartAt_coe, extChartAt_coe]
  simp only [Function.comp_apply]
  rw [chartAt_ulift M x]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem hasMFDerivAt_ulift_up (x : M) :
    HasMFDerivAt I I (ULift.up : M → ULift.{v} M) x (ContinuousLinearMap.id ℝ E) := by
  constructor
  · exact continuous_uliftUp.continuousAt
  · apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := I) x)
      intro y hy
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      rw [extChartAt_ulift I M x ((extChartAt I x).symm y)]
      exact (extChartAt I x).right_inv hy
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x), extChartAt_ulift I M x x]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderiv_ulift_up (x : M) :
    mfderiv I I (ULift.up : M → ULift.{v} M) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_ulift_up I M x).mfderiv

omit [FiniteDimensional ℝ E] in
theorem mem_trivializationAt_baseSet_ulift (p x : M) :
    (ULift.up x : ULift.{v} M) ∈
        (trivializationAt E (TangentSpace I) (ULift.up p)).baseSet ↔
      x ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
    chartAt_ulift M p]
  rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage]
  exact Iff.rfl

omit [FiniteDimensional ℝ E] in
theorem tangentChartEquiv_ulift (p x : M)
    (hx : (ULift.up x : ULift.{v} M) ∈
      (trivializationAt E (TangentSpace I) (ULift.up p)).baseSet)
    (hxM : x ∈ (trivializationAt E (TangentSpace I) p).baseSet) :
    tangentChartEquiv I (ULift.{v} M) (ULift.up p) (ULift.up x) hx =
      tangentChartEquiv I M p x hxM := by
  have hu : (ULift.up x : ULift.{v} M) ∈ (chartAt H (ULift.up p)).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hm : x ∈ (chartAt H p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxM
  have hd : mfderiv I 𝓘(ℝ, E) (extChartAt I (ULift.up p)) (ULift.up x) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
    have hcomp := mfderiv_comp (x := x) (I := I) (I' := I) (I'' := 𝓘(ℝ, E))
      (f := (ULift.up : M → ULift.{v} M))
      (g := (extChartAt I (ULift.up p) : ULift.{v} M → E))
      (mdifferentiableAt_extChartAt (I := I) (x := (ULift.up p : ULift.{v} M)) hu)
      (hasMFDerivAt_ulift_up I M x).mdifferentiableAt
    have heq : mfderiv I 𝓘(ℝ, E)
        ((extChartAt I (ULift.up p)) ∘ (ULift.up : M → ULift.{v} M)) x =
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
      have hfun : ((extChartAt I (ULift.up p)) ∘ (ULift.up : M → ULift.{v} M)) =
          (extChartAt I p : M → E) :=
        funext fun z => extChartAt_ulift I M p z
      rw [hfun]
    rw [heq, mfderiv_ulift_up I M x] at hcomp
    rw [← hcomp.symm]
    exact ContinuousLinearMap.comp_id _
  have hc : (trivializationAt E (TangentSpace I) (ULift.up p)).continuousLinearMapAt ℝ
        (ULift.up x) =
      (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hu,
      TangentBundle.continuousLinearMapAt_trivializationAt hm]
    exact hd
  apply LinearEquiv.ext
  intro w
  calc
    tangentChartEquiv I (ULift.{v} M) (ULift.up p) (ULift.up x) hx w =
        (trivializationAt E (TangentSpace I) (ULift.up p)).continuousLinearMapAt ℝ
          (ULift.up x) w :=
      (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) (ULift.up p)) hx w).symm
    _ = (trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x w :=
      congrArg (fun A : E →L[ℝ] E => A w) hc
    _ = tangentChartEquiv I M p x hxM w :=
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt E (TangentSpace I) p) hxM w

def uliftTangentOrientation (o : ManifoldOrientation I M n) (x : ULift.{v} M) :
    Orientation ℝ (TangentSpace I x) (Fin n) :=
  Orientation.map (Fin n)
    ((uliftDiffeomorph I M).mfderivToContinuousLinearEquiv (by simp) x.down).toLinearEquiv
    (o.orientation x.down)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderivToContinuousLinearEquiv_ulift (y : ULift.{v} M) :
    ((uliftDiffeomorph I M).mfderivToContinuousLinearEquiv (by simp) y.down).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I y) := by
  ext v
  change mfderiv I I (ULift.up : M → ULift.{v} M) y.down v = v
  rw [mfderiv_ulift_up I M y.down]
  rfl

@[simp]
theorem uliftTangentOrientation_apply (o : ManifoldOrientation I M n) (x : M) :
    uliftTangentOrientation I M o (ULift.up x) = o.orientation x := by
  rw [uliftTangentOrientation]
  erw [mfderivToContinuousLinearEquiv_ulift I M (ULift.up x)]
  change Orientation.map (Fin n) (LinearEquiv.refl ℝ (TangentSpace I x)) (o.orientation x) =
    o.orientation x
  rw [Orientation.map_refl]
  rfl

theorem uliftTangentOrientation_locally_constant (o : ManifoldOrientation I M n) :
    ∀ p x : ULift.{v} M,
    ∀ hx : x ∈ (trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set (ULift.{v} M), IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : ULift.{v} M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p y (hU hy))
          (uliftTangentOrientation I M o y) =
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p x hx)
          (uliftTangentOrientation I M o x) := by
  rintro ⟨p⟩ ⟨x⟩ hx
  have hxM : x ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    (mem_trivializationAt_baseSet_ulift I M p x).mp hx
  obtain ⟨W, hWo, hxW, hWm, hW⟩ := o.locally_constant p x hxM
  have hU : ULift.down ⁻¹' W ⊆
      (trivializationAt E (TangentSpace I) (ULift.up p)).baseSet := by
    rintro ⟨y⟩ hy
    exact (mem_trivializationAt_baseSet_ulift I M p y).mpr (hWm hy)
  refine ⟨ULift.down ⁻¹' W, hWo.preimage continuous_uliftDown, hxW, hU, ?_⟩
  rintro ⟨y⟩ hy
  rw [uliftTangentOrientation_apply, uliftTangentOrientation_apply,
    tangentChartEquiv_ulift I M p y (hU hy) (hWm hy),
    tangentChartEquiv_ulift I M p x hx hxM]
  exact hW y hy

def uliftOrientation (o : ManifoldOrientation I M n) : ManifoldOrientation I (ULift.{v} M) n where
  dimension_eq := o.dimension_eq
  orientation := uliftTangentOrientation I M o
  locally_constant := uliftTangentOrientation_locally_constant I M o

theorem uliftDiffeomorph_preservesOrientation (o : ManifoldOrientation I M n) :
    (uliftDiffeomorph I M).preservesOrientation o (uliftOrientation I M o) := by
  intro x
  rfl

namespace ClosedOrientedManifold

def ulift (M : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{max u v} n where
  Carrier := ULift.{v} M.Carrier
  orientation := uliftOrientation _ _ M.orientation

@[simp]
theorem ulift_carrier (M : ClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

def uliftDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ (ulift.{u, v} M).Carrier :=
  DifferentialGeometry.Topology.uliftDiffeomorph _ _

theorem uliftDiffeomorph_preservesOrientation (M : ClosedOrientedManifold.{u} n) :
    (uliftDiffeomorph.{u, v} M).preservesOrientation M.orientation (ulift.{u, v} M).orientation :=
  DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation _ _ M.orientation

def uliftOrientedDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    OrientedDiffeomorph M (ulift.{u, v} M) :=
  ⟨uliftDiffeomorph M, uliftDiffeomorph_preservesOrientation M⟩

end ClosedOrientedManifold

namespace ConnectedClosedOrientedManifold

def ulift (M : ConnectedClosedOrientedManifold.{u} n) :
    ConnectedClosedOrientedManifold.{max u v} n where
  toClosedOrientedManifold := ClosedOrientedManifold.ulift.{u, v} M.toClosedOrientedManifold
  connected :=
    (Homeomorph.ulift : ULift.{v} M.Carrier ≃ₜ M.Carrier).connectedSpace_iff.mpr inferInstance

@[simp]
theorem ulift_carrier (M : ConnectedClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

end ConnectedClosedOrientedManifold

end DifferentialGeometry.Topology
