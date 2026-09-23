import DifferentialGeometry.Topology.Manifold.SmoothTwoSidedCollar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothTwoSidedCollar

variable {E H F G K H' S M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {L : ModelWithCorners ℝ K H'}
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  [TopologicalSpace N] [ChartedSpace H' N]
  {e : S → M} (c : SmoothTwoSidedCollar I J e)

def mapAmbient (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f) (hinj : Function.Injective f) :
    SmoothTwoSidedCollar I L (f ∘ e) := by
  have hc : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ c.toFun :=
    DifferentialGeometry.isLocalDiffeomorph_comp
      (DifferentialGeometry.isLocalDiffeomorph_subtype_val c.neighborhood)
      c.toDiffeomorph.isLocalDiffeomorph
  have hcomp : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) L ∞ (f ∘ c.toFun) :=
    DifferentialGeometry.isLocalDiffeomorph_comp hf hc
  have hcomp_inj : Function.Injective (f ∘ c.toFun) :=
    hinj.comp c.isOpenEmbedding_toFun.injective
  exact {
    radius := c.radius
    radius_pos := c.radius_pos
    neighborhood := hcomp.image
    toDiffeomorph := diffeomorphRangeOfInjective hcomp hcomp_inj
    zero_eq := fun s ↦ congrArg f (c.toFun_zero s) }

@[simp] theorem mapAmbient_radius (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) : (c.mapAmbient f hf hinj).radius = c.radius := rfl

@[simp] theorem mapAmbient_toFun (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) (p : S × symmetricOpenInterval c.radius) :
    (c.mapAmbient f hf hinj).toFun p = f (c.toFun p) := rfl

@[simp] theorem mapAmbient_neighborhood (f : M → N) (hf : IsLocalDiffeomorph J L ∞ f)
    (hinj : Function.Injective f) :
    ((c.mapAmbient f hf hinj).neighborhood : Set N) = f '' (c.neighborhood : Set M) := by
  change range (f ∘ c.toFun) = f '' (c.neighborhood : Set M)
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨c.toFun p, (c.toDiffeomorph p).property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c.toDiffeomorph.symm ⟨x, hx⟩, ?_⟩
    exact congrArg (fun z : c.neighborhood ↦ f z.val) (c.toDiffeomorph.apply_symm_apply ⟨x, hx⟩)

end DifferentialGeometry.Topology.SmoothTwoSidedCollar
