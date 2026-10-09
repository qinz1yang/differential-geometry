import DifferentialGeometry.Geometry.Collapse.EdgeModelFibreDisk
import DifferentialGeometry.Topology.Manifold.ModelChange.ContinuousLinearEquiv
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# LFR28 B3: the model cylinder mapped into the source with a common model

Blueprint 207A, LFR28 (A:27223), proof step 4: the interpolation of the model map with `(f, H)`
"uses that same embedding" `j_i` on the model cylinder `U ⊆ ℝ × Z`. F7-LFR28B's
`edgeInterp_disk_bundle` (and the I6 form `edgeModelCylinder_disk_bundle`) needs ONE model with
corners on the model side and the source side. The cylinder `U ⊆ ℝ × S` is charted on
`ModelProd ℝ E2` (model `𝓘(ℝ, ℝ).prod (𝓡 2)`); the source is a `3`-manifold charted on `E3`.

* `euclideanThreeProdEquiv`, `euclideanThreeProdHomeomorph`: a fixed linear identification
  `E3 ≃L ℝ × E2`, and the compatibility `𝓘(ℝ,ℝ).prod (𝓡 2) (e y) = L (𝓘(ℝ,E3) y)`.
* `exists_edgeCylinder_source_partialDiffeomorph` (**B3**): for a `C^n` diffeomorphism
  `Θ : ℝ × S → N` (in LFR28: the exact splitting `Ψ` after the smooth carrier `φ`), a `C^n` partial
  diffeomorphism `j : N → X` (LFR14's actual embedding) and opens `U ⊆ ℝ × S`, `O ⊆ X` with
  `j(Θ(U)) ⊆ O`, the map `x ↦ j(Θ x)` is a `C^n` partial diffeomorphism `U → O` with source `univ`
  and target exactly the image, where `O` carries the `ModelProd ℝ E2` charts transported along
  `E3 ≃ ℝ × E2` as a LOCAL instance (`chartedSpaceTransHomeomorph`; no type synonym), and
  `IsManifold (𝓘(ℝ,ℝ).prod (𝓡 2)) ∞ O` (`edgeSource_isManifold`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- A fixed linear identification `E3 ≃L ℝ × E2`. -/
def euclideanThreeProdEquiv : E3 ≃L[ℝ] ℝ × E2 :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- The same identification onto the product model space `ModelProd ℝ E2`. -/
def euclideanThreeProdHomeomorph : E3 ≃ₜ ModelProd ℝ E2 :=
  euclideanThreeProdEquiv.toHomeomorph

theorem euclideanThreeProd_compat (y : E3) :
    (𝓘(ℝ, ℝ).prod (𝓡 2)) (euclideanThreeProdHomeomorph y) =
      euclideanThreeProdEquiv (𝓘(ℝ, E3) y) := rfl

/-- A `3`-manifold charted on `E3`, re-charted on `ModelProd ℝ E2`, is smooth for the product model. -/
theorem edgeSource_isManifold {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] :
    letI := chartedSpaceTransHomeomorph (M := X) euclideanThreeProdHomeomorph
    IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ X :=
  isManifold_transHomeomorph 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) euclideanThreeProdHomeomorph
    euclideanThreeProdEquiv euclideanThreeProd_compat

/-- **LFR28 B3.** The model cylinder `U ⊆ ℝ × S` mapped into the source by `j ∘ Θ` is a `C^n`
partial diffeomorphism `U → O` (source `univ`, target the image) for the common model
`𝓘(ℝ,ℝ).prod (𝓡 2)`, `O` re-charted along `E3 ≃ ℝ × E2`. -/
theorem exists_edgeCylinder_source_partialDiffeomorph
    {S : Type*} [TopologicalSpace S] [ChartedSpace E2 S]
    {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N]
    {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X]
    {n : WithTop ℕ∞} (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N n)
    (j : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N X n)
    (U : TopologicalSpace.Opens (ℝ × S)) (hUne : Nonempty U) (O : TopologicalSpace.Opens X)
    (hU : ∀ x ∈ U, Θ x ∈ j.source ∧ j (Θ x) ∈ O) :
    letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
    ∃ J : PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) U O n,
      J.source = univ ∧ (∀ x : U, ((J x : O) : X) = j (Θ x)) ∧
      ∀ y : O, y ∈ J.target ↔ ∃ x : U, j (Θ x) = y := by
  classical
  let _ := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
  -- the forward map
  let φ : U → O := fun x => ⟨j (Θ x), (hU x x.2).2⟩
  -- the target: the image
  let T : Set O := {y | ∃ x : U, j (Θ x) = y}
  have hΘU : IsOpen (Θ '' U) := Θ.toHomeomorph.isOpenMap _ U.isOpen
  have hΘUs : Θ '' U ⊆ j.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hU x hx).1
  have hjimg : IsOpen (j '' (Θ '' U)) :=
    j.toOpenPartialHomeomorph.isOpen_image_of_subset_source hΘU hΘUs
  have hTopen : IsOpen T := by
    have h := hjimg.preimage (continuous_subtype_val (p := fun x : X => x ∈ O))
    convert h using 1
    ext y
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨Θ x, ⟨x, x.2, rfl⟩, hx⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, hxy⟩
      exact ⟨⟨x, hx⟩, hxy⟩
  -- the inverse map
  let ψ : O → U := fun y =>
    if h : Θ.symm (j.symm (y : X)) ∈ U then ⟨_, h⟩ else Classical.choice hUne
  have hψφ : ∀ x : U, ψ (φ x) = x := by
    intro x
    have hjx : j.symm (j (Θ x)) = Θ x := j.left_inv (hU x x.2).1
    have hmem : Θ.symm (j.symm ((φ x : O) : X)) ∈ U := by
      change Θ.symm (j.symm (j (Θ x))) ∈ U
      rw [hjx, Θ.symm_apply_apply]
      exact x.2
    simp only [ψ, hmem, ↓reduceDIte]
    apply Subtype.ext
    change Θ.symm (j.symm (j (Θ x))) = x
    rw [hjx, Θ.symm_apply_apply]
  have hφψ : ∀ y ∈ T, φ (ψ y) = y := by
    rintro y ⟨x, hx⟩
    have hy : y = φ x := Subtype.ext hx.symm
    rw [hy, hψφ]
  -- smoothness of the forward map (transported target charts)
  have hφs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) n φ := by
    apply (contMDiff_chartedSpaceTransHomeomorph_iff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) euclideanThreeProdHomeomorph
      euclideanThreeProdEquiv euclideanThreeProd_compat (𝓘(ℝ, ℝ).prod (𝓡 2)) (M := O)).mpr
    intro x
    have hval : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) n (fun x : U => j (Θ x)) x := by
      have hj : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) n j (Θ x) :=
        (j.contMDiffOn _ (hU x x.2).1).contMDiffAt (j.open_source.mem_nhds (hU x x.2).1)
      exact hj.comp x ((Θ.contMDiff.comp contMDiff_subtype_val) x)
    exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := O) φ univ x).mp hval
  -- smoothness of the inverse on the target (transported source charts)
  have hψs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) n ψ T := by
    apply (contMDiffOn_chartedSpaceTransHomeomorph_source_iff 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2))
      euclideanThreeProdHomeomorph euclideanThreeProdEquiv euclideanThreeProd_compat (𝓘(ℝ, ℝ).prod (𝓡 2))
      (N := O)).mpr
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hyT : ∀ᶠ y' in 𝓝 y, y' ∈ T := hTopen.mem_nhds ⟨x, hx⟩
    have hjt : (y : X) ∈ j.target := by
      rw [← hx]
      exact j.map_source (hU x x.2).1
    have hinv : ContMDiffAt 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) n (fun y' : O => Θ.symm (j.symm (y' : X))) y := by
      have hjs : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, E3) n j.symm (y : X) :=
        (j.symm.contMDiffOn _ hjt).contMDiffAt (j.open_target.mem_nhds hjt)
      exact (Θ.symm.contMDiff _).comp y (hjs.comp y (contMDiff_subtype_val y))
    have heq : (Subtype.val ∘ ψ) =ᶠ[𝓝 y] fun y' : O => Θ.symm (j.symm (y' : X)) := by
      filter_upwards [hyT] with y' hy'
      obtain ⟨x', hx'⟩ := hy'
      have hjx' : j.symm (j (Θ x')) = Θ x' := j.left_inv (hU x' x'.2).1
      have hmem : Θ.symm (j.symm (y' : X)) ∈ U := by
        rw [← hx', hjx', Θ.symm_apply_apply]
        exact x'.2
      simp only [comp_apply, ψ, hmem, ↓reduceDIte]
    have hc : ContMDiffAt 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) n (Subtype.val ∘ ψ) y := hinv.congr_of_eventuallyEq heq
    have h2 : ContMDiffWithinAt 𝓘(ℝ, E3) (𝓘(ℝ, ℝ).prod (𝓡 2)) n ψ univ y :=
      (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) ψ univ y).mp hc
    exact h2.mono (subset_univ _)
  refine ⟨{ toFun := φ
            invFun := ψ
            source := univ
            target := T
            map_source' := fun x _ => ⟨x, rfl⟩
            map_target' := fun _ _ => mem_univ _
            left_inv' := fun x _ => hψφ x
            right_inv' := hφψ
            open_source := isOpen_univ
            open_target := hTopen
            contMDiffOn_toFun := hφs.contMDiffOn
            contMDiffOn_invFun := ?_ }, rfl, fun x => rfl, fun y => Iff.rfl⟩
  -- the transported-source smoothness of `ψ`, read back
  intro y hy
  have h := hψs y hy
  exact h

end DifferentialGeometry.Geometry.Collapse
