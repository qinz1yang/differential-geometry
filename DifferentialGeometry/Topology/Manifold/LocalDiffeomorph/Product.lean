import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H G H' G' : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace H'] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {I' : ModelWithCorners 𝕜 E' H'} {J' : ModelWithCorners 𝕜 F' G'}
  {M N M' N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω} {f : M → N} {g : M' → N'}

theorem IsLocalDiffeomorphAt.prodMap {x : M} {y : M'}
    (hf : IsLocalDiffeomorphAt I J n f x) (hg : IsLocalDiffeomorphAt I' J' n g y) :
    IsLocalDiffeomorphAt (I.prod I') (J.prod J') n (Prod.map f g) (x, y) := by
  obtain ⟨d, hx, hd⟩ := hf
  obtain ⟨e, hy, he⟩ := hg
  let D : PartialDiffeomorph (I.prod I') (J.prod J') (M × M') (N × N') n := {
    toPartialEquiv := d.toPartialEquiv.prod e.toPartialEquiv
    open_source := d.open_source.prod e.open_source
    open_target := d.open_target.prod e.open_target
    contMDiffOn_toFun := d.contMDiffOn_toFun.prodMap e.contMDiffOn_toFun
    contMDiffOn_invFun := d.contMDiffOn_invFun.prodMap e.contMDiffOn_invFun }
  refine ⟨D, ⟨hx, hy⟩, ?_⟩
  intro z hz
  exact Prod.ext (hd hz.1) (he hz.2)

theorem IsLocalDiffeomorph.prodMap (hf : IsLocalDiffeomorph I J n f)
    (hg : IsLocalDiffeomorph I' J' n g) :
    IsLocalDiffeomorph (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun x => (hf x.1).prodMap (hg x.2)
