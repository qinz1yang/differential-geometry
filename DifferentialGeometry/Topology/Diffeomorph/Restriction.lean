import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Logic.Equiv.Basic

open scoped ContDiff Manifold Topology

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {Q : Type*} [NormedAddCommGroup Q] [NormedSpace 𝕜 Q]
  {S : Type*} [TopologicalSpace S] {L : ModelWithCorners 𝕜 Q S}
  {P : Type*} [TopologicalSpace P] [ChartedSpace S P]
  {n : ℕ∞ω} {U : TopologicalSpace.Opens M} {V : TopologicalSpace.Opens N}

def restrict (e : Diffeomorph I J M N n) (h : ∀ x, x ∈ U ↔ e x ∈ V) :
    Diffeomorph I J U V n where
  toEquiv := e.toEquiv.subtypeEquiv h
  contMDiff_toFun := by
    intro x
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp I J n) (U := V)
      (e.toEquiv.subtypeEquiv h) Set.univ x).mp
        ((e.contMDiff.comp contMDiff_subtype_val) x)
  contMDiff_invFun := by
    intro x
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
      (P := ContDiffWithinAtProp J I n) (U := U)
      (e.toEquiv.subtypeEquiv h).symm Set.univ x).mp
        ((e.symm.contMDiff.comp contMDiff_subtype_val) x)

@[simp] theorem restrict_apply (e : Diffeomorph I J M N n)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (x : U) :
    (restrict e h x : N) = e x := rfl

@[simp] theorem restrict_symm_apply (e : Diffeomorph I J M N n)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) (x : V) :
    ((restrict e h).symm x : M) = e.symm x := rfl

theorem contMDiff_restrict (e : P → Diffeomorph I J M N n)
    (he : ContMDiff (L.prod I) J n (fun z : P × M => e z.1 z.2))
    (h : ∀ p x, x ∈ U ↔ e p x ∈ V) :
    ContMDiff (L.prod I) J n (fun z : P × U => restrict (e z.1) (h z.1) z.2) := by
  have hval : ContMDiff (L.prod I) I n (fun z : P × U => (z.2 : M)) :=
    contMDiff_subtype_val.comp contMDiff_snd
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp (L.prod I) J n) (U := V)
    (fun z : P × U => restrict (e z.1) (h z.1) z.2) Set.univ z).mp
      ((he.comp (contMDiff_fst.prodMk hval)) z)

theorem contMDiff_restrict_symm (e : P → Diffeomorph I J M N n)
    (hi : ContMDiff (L.prod J) I n (fun z : P × N => (e z.1).symm z.2))
    (h : ∀ p x, x ∈ U ↔ e p x ∈ V) :
    ContMDiff (L.prod J) I n
      (fun z : P × V => (restrict (e z.1) (h z.1)).symm z.2) := by
  have hval : ContMDiff (L.prod J) J n (fun z : P × V => (z.2 : N)) :=
    contMDiff_subtype_val.comp contMDiff_snd
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (P := ContDiffWithinAtProp (L.prod J) I n) (U := U)
    (fun z : P × V => (restrict (e z.1) (h z.1)).symm z.2) Set.univ z).mp
      ((hi.comp (contMDiff_fst.prodMk hval)) z)

@[simp] theorem restrict_refl :
    restrict (Diffeomorph.refl I M n) (U := U) (V := U) (fun _ => Iff.rfl) =
      Diffeomorph.refl I U n := by
  ext x
  rfl

theorem restrict_symm (e : Diffeomorph I J M N n)
    (h : ∀ x, x ∈ U ↔ e x ∈ V) :
    (restrict e h).symm = restrict e.symm
      (fun y => (by simpa only [e.apply_symm_apply] using (h (e.symm y)).symm)) := by
  ext x
  rfl

@[simp] theorem restrict_trans (e : Diffeomorph I J M N n)
    (f : Diffeomorph J L N P n) {W : TopologicalSpace.Opens P}
    (he : ∀ x, x ∈ U ↔ e x ∈ V) (hf : ∀ y, y ∈ V ↔ f y ∈ W) :
    (restrict e he).trans (restrict f hf) =
      restrict (e.trans f) (fun x => (he x).trans (hf (e x))) := by
  ext x
  rfl

end Diffeomorph
