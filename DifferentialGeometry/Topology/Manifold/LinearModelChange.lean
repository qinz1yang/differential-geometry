import DifferentialGeometry.Topology.Manifold.ModelTransport
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Changing the model vector space of a manifold along a linear equivalence

`LinearModelChange X L` is the type `X` with its charts composed with a continuous linear
equivalence `L : E ≃L[ℝ] F` of model spaces. It is a `C^n` manifold modelled on `𝓘(ℝ, F)` whenever
`X` is one modelled on `𝓘(ℝ, E)` (`LinearModelChange.isManifold`), and the identity is a `C^n`
diffeomorphism between the two structures (`LinearModelChange.diffeomorph`). Used to read the
`Fin k → ℝ`-modelled regular-zero atlas as a `EuclideanSpace ℝ (Fin k)`-modelled one.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The type `X` with its model space changed along `L`. -/
@[nolint unusedArguments]
def LinearModelChange (X : Type*) (_L : E ≃L[ℝ] F) : Type _ := X

namespace LinearModelChange

variable {X : Type*} (L : E ≃L[ℝ] F)

/-- The identity, as a map to the original structure. -/
def toBase : LinearModelChange X L → X := id

/-- The identity, as a map from the original structure. -/
def ofBase : X → LinearModelChange X L := id

theorem toBase_ofBase (x : X) : toBase L (ofBase L x) = x := rfl

theorem ofBase_toBase (x : LinearModelChange X L) : ofBase L (toBase L x) = x := rfl

variable [TopologicalSpace X]

instance instTopologicalSpaceLinearModelChange : TopologicalSpace (LinearModelChange X L) :=
  ‹TopologicalSpace X›

instance instT2SpaceLinearModelChange [T2Space X] : T2Space (LinearModelChange X L) :=
  ‹T2Space X›

instance instSecondCountableLinearModelChange [SecondCountableTopology X] :
    SecondCountableTopology (LinearModelChange X L) :=
  ‹SecondCountableTopology X›

instance instCompactSpaceLinearModelChange [CompactSpace X] :
    CompactSpace (LinearModelChange X L) :=
  ‹CompactSpace X›

instance instConnectedSpaceLinearModelChange [ConnectedSpace X] :
    ConnectedSpace (LinearModelChange X L) :=
  ‹ConnectedSpace X›

/-- The identity homeomorphism. -/
def homeomorph : LinearModelChange X L ≃ₜ X := Homeomorph.refl X

theorem coe_homeomorph : (homeomorph L : LinearModelChange X L → X) = toBase L := rfl

theorem coe_homeomorph_symm : ((homeomorph L).symm : X → LinearModelChange X L) = ofBase L := rfl

variable [ChartedSpace E X]

instance instChartedSpaceLinearModelChange : ChartedSpace F (LinearModelChange X L) :=
  chartedSpaceTransHomeomorph (M := X) L.toHomeomorph

theorem chartAt_linearModelChange (x : LinearModelChange X L) :
    chartAt F x = (chartAt E (toBase L x)).trans L.toHomeomorph.toOpenPartialHomeomorph := rfl

/-- **The model change is a `C^n` manifold.** -/
theorem isManifold {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n X] :
    IsManifold 𝓘(ℝ, F) n (LinearModelChange X L) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨c, hc, d, hd, rfl⟩ := he
  obtain ⟨c', hc', d', hd', rfl⟩ := he'
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ (by simp) d hd
  obtain rfl := OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ (by simp) d' hd'
  have hT := HasGroupoid.compatible (G := contDiffGroupoid n 𝓘(ℝ, E)) hc hc'
  have hT' := (mem_groupoid_of_pregroupoid.mp hT).1
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    range_id, preimage_id_eq, inter_univ, Function.id_comp, Function.comp_id] at hT' ⊢
  have hmain : ContDiffOn ℝ n (L ∘ (c.symm ≫ₕ c') ∘ L.symm) (L.symm ⁻¹' (c.symm ≫ₕ c').source) :=
    L.contDiff.comp_contDiffOn (hT'.comp L.symm.contDiff.contDiffOn (fun _ hy => hy))
  exact (hmain.mono (fun y hy => ⟨hy.1.2, hy.2.1⟩)).congr (fun y _ => rfl)

variable {n : ℕ∞ω} [IsManifold 𝓘(ℝ, E) n X]

theorem contMDiff_toBase :
    letI := isManifold L (X := X) (n := n)
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) n (toBase L (X := X)) := by
  let _ := isManifold L (X := X) (n := n)
  intro x
  let c := chartAt E (toBase L x)
  have h1 : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) n (chartAt F x) (chartAt F x).source :=
    contMDiffOn_chart
  have h2 : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) n L.symm := L.symm.contDiff.contMDiff
  have h3 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n c.symm c.target := contMDiffOn_chart_symm
  have hcomp : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, E) n (c.symm ∘ L.symm ∘ chartAt F x)
      (chartAt F x).source := by
    refine h3.comp (h2.comp_contMDiffOn h1) ?_
    intro y hy
    change c.symm.source (L.symm (L (c y)))
    rw [L.symm_apply_apply]
    exact c.map_source hy.1
  have hx : x ∈ (chartAt F x).source := mem_chart_source F x
  refine (hcomp.contMDiffAt ((chartAt F x).open_source.mem_nhds hx)).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt F x).open_source.mem_nhds hx] with y hy
  change toBase L y = c.symm (L.symm (L (c y)))
  rw [L.symm_apply_apply]
  exact (c.left_inv hy.1).symm

theorem contMDiff_ofBase :
    letI := isManifold L (X := X) (n := n)
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n (ofBase L (X := X)) := by
  let _ := isManifold L (X := X) (n := n)
  intro y
  let c := chartAt E y
  let d := chartAt F (ofBase L y)
  have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) n c c.source := contMDiffOn_chart
  have h2 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) n L := L.contDiff.contMDiff
  have h3 : ContMDiffOn 𝓘(ℝ, F) 𝓘(ℝ, F) n d.symm d.target := contMDiffOn_chart_symm
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) n (d.symm ∘ L ∘ c) c.source := by
    refine h3.comp (h2.comp_contMDiffOn h1) ?_
    intro z hz
    refine ⟨mem_univ _, ?_⟩
    change L.symm (L (c z)) ∈ c.target
    rw [L.symm_apply_apply]
    exact c.map_source hz
  have hy : y ∈ c.source := mem_chart_source E y
  refine (hcomp.contMDiffAt (c.open_source.mem_nhds hy)).congr_of_eventuallyEq ?_
  filter_upwards [c.open_source.mem_nhds hy] with z hz
  change ofBase L z = c.symm (L.symm (L (c z)))
  rw [L.symm_apply_apply]
  exact (c.left_inv hz).symm

/-- **The identity is a `C^n` diffeomorphism** between the changed and the original structure. -/
def diffeomorph :
    letI := isManifold L (X := X) (n := n)
    Diffeomorph 𝓘(ℝ, F) 𝓘(ℝ, E) (LinearModelChange X L) X n :=
  letI := isManifold L (X := X) (n := n)
  { toEquiv := Equiv.refl X
    contMDiff_toFun := contMDiff_toBase L
    contMDiff_invFun := contMDiff_ofBase L }

theorem coe_diffeomorph :
    letI := isManifold L (X := X) (n := n)
    (diffeomorph L (X := X) (n := n) : LinearModelChange X L → X) = toBase L := rfl

end LinearModelChange

end DifferentialGeometry.Manifold
