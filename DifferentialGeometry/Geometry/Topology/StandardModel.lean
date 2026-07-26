import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Standard-model copies of manifolds

This file packages a same-universe copy of a boundaryless smooth manifold whose
model with corners is the standard model on a chosen linearly equivalent normed
space.  The copy is kept type-theoretically distinct by `ULift.{0}`.
-/

open Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Topology

universe u uE uH uF

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]

/-- A copy of `M` in the same universe, presented over a standard model space. -/
structure StdModelCopy
    (I : ModelWithCorners ℝ E H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M]
    (F : Type uF) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  Q : Type u
  [topos : TopologicalSpace Q]
  [charted : ChartedSpace F Q]
  [mfld : IsManifold 𝓘(ℝ, F) ∞ Q]
  [t2 : T2Space Q]
  [sigma : SigmaCompactSpace Q]
  [boundaryless : BoundarylessManifold 𝓘(ℝ, F) Q]
  equiv : M ≃ₘ⟮I, 𝓘(ℝ, F)⟯ Q

attribute [instance] StdModelCopy.topos StdModelCopy.charted StdModelCopy.mfld
  StdModelCopy.t2 StdModelCopy.sigma StdModelCopy.boundaryless

private noncomputable def modelHomeo
    [I.Boundaryless] {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) : H ≃ₜ F :=
  I.toHomeomorph.trans e.toHomeomorph

@[implicit_reducible]
private noncomputable def stdCharts
    [I.Boundaryless] {F : Type uF}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) : ChartedSpace F M :=
  let h := modelHomeo (I := I) e
  letI : ChartedSpace F H :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  ChartedSpace.comp F H M

private noncomputable def std_diffeo
    [I.Boundaryless] [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    @Diffeomorph ℝ _ E _ _ F _ _ H _ F _ I 𝓘(ℝ, F)
      M _ (inferInstance : ChartedSpace H M)
      M _ (stdCharts (I := I) e) ∞ := by
  letI : ChartedSpace F M := stdCharts (I := I) e
  refine
    { toEquiv := Equiv.refl M
      contMDiff_toFun := fun x => ?_
      contMDiff_invFun := fun x => ?_ }
  · refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, id, Function.comp_apply]
      change
        e (extChartAt I x ((extChartAt I x).symm y)) = e y
      rw [(extChartAt I x).right_inv hy.1]
    · simp
  · refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
    refine e.symm.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Equiv.coe_refl, Equiv.refl_symm, id, Function.comp_apply]
      apply e.injective
      rw [e.apply_symm_apply]
      change
        extChartAt 𝓘(ℝ, F) x
            ((extChartAt 𝓘(ℝ, F) x).symm y) =
          y
      rw [(extChartAt 𝓘(ℝ, F) x).right_inv hy.1]
    · simp

private theorem std_mfld
    [I.Boundaryless] [IsManifold I ∞ M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    @IsManifold ℝ _ F _ _ F _ 𝓘(ℝ, F) ∞ M _
      (stdCharts (I := I) e) := by
  let h := modelHomeo (I := I) e
  let hs : ChartedSpace F H :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  letI : ChartedSpace F H := hs
  let dH :
      @Diffeomorph ℝ _ E _ _ F _ _ H _ F _ I 𝓘(ℝ, F)
        H _ (chartedSpaceSelf H) H _ hs ∞ := by
    refine
      { toEquiv := Equiv.refl H
        contMDiff_toFun := fun x => ?_
        contMDiff_invFun := fun x => ?_ }
    · refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
      refine e.contDiff.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
      · simp only [Equiv.coe_refl, id, Function.comp_apply]
        change e (extChartAt I x ((extChartAt I x).symm y)) = e y
        rw [(extChartAt I x).right_inv hy.1]
      · simp
    · refine contMDiffWithinAt_iff'.2 ⟨continuousWithinAt_id, ?_⟩
      refine e.symm.contDiff.contDiffWithinAt.congr_of_mem
        (fun y hy => ?_) ?_
      · simp only [Equiv.coe_refl, Equiv.refl_symm, id,
          Function.comp_apply]
        apply e.injective
        rw [e.apply_symm_apply]
        change
          extChartAt 𝓘(ℝ, F) x
              ((extChartAt 𝓘(ℝ, F) x).symm y) =
            y
        rw [(extChartAt 𝓘(ℝ, F) x).right_inv hy.1]
      · simp
  letI : IsManifold 𝓘(ℝ, F) ∞ H :=
    h.toOpenPartialHomeomorph.isManifold_singleton (by simp [h])
  letI : ChartedSpace F M := stdCharts (I := I) e
  letI : HasGroupoid M (contDiffGroupoid ∞ 𝓘(ℝ, F)) :=
    StructureGroupoid.HasGroupoid.comp (G₂ := contDiffGroupoid ∞ I) (by
      intro f hf
      rw [isLocalStructomorphOn_contDiffGroupoid_iff]
      constructor
      · have hfI : ContMDiffOn I I ∞ f f.source :=
          contMDiffOn_of_mem_contDiffGroupoid hf
        have hpre :
            ContMDiffOn 𝓘(ℝ, F) I ∞ (f ∘ dH.symm) f.source := by
          refine hfI.comp dH.symm.contMDiff.contMDiffOn ?_
          intro x hx
          simpa [dH] using hx
        have hpost :=
          dH.contMDiff.comp_contMDiffOn hpre
        simpa [dH, Function.comp_def] using hpost
      · have hfI : ContMDiffOn I I ∞ f.symm f.target :=
          contMDiffOn_of_mem_contDiffGroupoid
            ((contDiffGroupoid ∞ I).symm hf)
        have hpre :
            ContMDiffOn 𝓘(ℝ, F) I ∞ (f.symm ∘ dH.symm) f.target := by
          refine hfI.comp dH.symm.contMDiff.contMDiffOn ?_
          intro x hx
          simpa [dH] using hx
        have hpost :=
          dH.contMDiff.comp_contMDiffOn hpre
        simpa [dH, Function.comp_def] using hpost)
  exact IsManifold.mk' 𝓘(ℝ, F) ∞ M

/-- Replace a boundaryless smooth manifold by a distinct same-universe copy
whose model with corners is standard. -/
noncomputable def stdModelCopy
    [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) :
    StdModelCopy I M F := by
  let c : ChartedSpace F M := stdCharts (I := I) e
  letI : ChartedSpace F M := c
  letI : IsManifold 𝓘(ℝ, F) ∞ M := std_mfld (I := I) e
  let d : M ≃ₘ⟮I, 𝓘(ℝ, F)⟯ M := std_diffeo (I := I) e
  let h : ULift.{0} M ≃ₜ M := Homeomorph.ulift
  let qBase : ChartedSpace M (ULift.{0} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  let qCharts : ChartedSpace F (ULift.{0} M) :=
    @ChartedSpace.comp F _ M _ (ULift.{0} M) _ c qBase
  letI : ChartedSpace M (ULift.{0} M) := qBase
  letI : ChartedSpace F (ULift.{0} M) := qCharts
  letI : IsManifold 𝓘(ℝ, F) ∞ (ULift.{0} M) := by
    letI : HasGroupoid (ULift.{0} M) (@idRestrGroupoid M _) :=
      h.toOpenPartialHomeomorph.singleton_hasGroupoid (by simp [h])
        (@idRestrGroupoid M _)
    letI :
        HasGroupoid (ULift.{0} M) (contDiffGroupoid ∞ 𝓘(ℝ, F)) :=
      StructureGroupoid.HasGroupoid.comp
        (G₂ := @idRestrGroupoid M _) (by
        intro f hf
        have hsmooth {a : OpenPartialHomeomorph M M}
            (ha : a ∈ @idRestrGroupoid M _) :
            ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ a a.source := by
          rcases ha with ⟨s, hs, ha⟩
          refine contMDiffOn_id.congr ?_
          intro x hx
          have hx' := OpenPartialHomeomorph.EqOnSource.eqOn ha hx
          simpa using hx'
        rw [isLocalStructomorphOn_contDiffGroupoid_iff]
        exact
          ⟨hsmooth hf,
            by
              simpa only [mfld_simps] using
                hsmooth ((@idRestrGroupoid M _).symm hf)⟩)
    exact IsManifold.mk' 𝓘(ℝ, F) ∞ (ULift.{0} M)
  let qd : M ≃ₘ⟮𝓘(ℝ, F), 𝓘(ℝ, F)⟯ ULift.{0} M := by
    refine
      { toEquiv := h.toEquiv.symm
        contMDiff_toFun := fun x => ?_
        contMDiff_invFun := fun x => ?_ }
    · refine contMDiffWithinAt_iff'.2
        ⟨h.symm.continuous.continuousWithinAt, ?_⟩
      refine contDiff_id.contDiffWithinAt.congr_of_mem
        (fun y hy => ?_) ?_
      · simp only [Function.comp_apply]
        change
          extChartAt 𝓘(ℝ, F) x
              ((extChartAt 𝓘(ℝ, F) x).symm y) =
            y
        rw [(extChartAt 𝓘(ℝ, F) x).right_inv hy.1]
      · simp
    · refine contMDiffWithinAt_iff'.2
        ⟨h.continuous.continuousWithinAt, ?_⟩
      refine contDiff_id.contDiffWithinAt.congr_of_mem
        (fun y hy => ?_) ?_
      · simp only [Function.comp_apply]
        change
          extChartAt 𝓘(ℝ, F) x
              ((extChartAt 𝓘(ℝ, F) x).symm y) =
            y
        rw [(extChartAt 𝓘(ℝ, F) x).right_inv hy.1]
      · simp
  exact
    { Q := ULift.{0} M
      equiv := d.trans qd }

end Topology
end Geometry
end DifferentialGeometry
