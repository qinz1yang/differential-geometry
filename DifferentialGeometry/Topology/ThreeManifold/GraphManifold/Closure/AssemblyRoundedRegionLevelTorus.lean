import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleFibredSurface
import DifferentialGeometry.Topology.Manifold.RegularLevel.Tangent
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldField
import DifferentialGeometry.Topology.Manifold.AmbientSplitOrientation
import DifferentialGeometry.Topology.Manifold.LinearRechart
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary

/-!
# FC42 packet T3, part 1: an oriented regular level fibred over the circle is a torus

Review 42 §4.4 (binding point 1 of the lead message). The orientation of a level torus is obtained
from the AMBIENT orientation, "normal first", with a transversal field `ν` (here the unit-speed field
`df(ν) = -1` of the flow-collar kernel, `RegularLevel/Collar/ManifoldField.lean`); no orientability
of the base and no orientation of the fibres is assumed. Then B2-param
(`exists_torus_param_of_circle_fibred_surface`) identifies the level with the torus.

* `isSmoothEmbedding_val_interiorSeamModel`: the inclusion of an open subset of the interior of a
  carrier, with the boundaryless recharted interior model of B2 (`interiorSeamModel`,
  `Closure/AssemblySeamCollar.lean`), is a smooth embedding into the carrier (whose model may have
  boundary);
* `exists_torus_embedding_of_oriented_level`: on a boundaryless oriented `3`-manifold with model
  over `MorseModel 3`, a compact regular level `{f = 0}` with a submersion to the circle with
  connected fibres is the image of a smooth torus embedding, compatible with the submersion.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The interior inclusion is a smooth embedding -/

section InteriorInclusion

variable (W : CompactCarrier.{u}) (O : TopologicalSpace.Opens W.Carrier)

/-- The linear identification `MorseModel 3 × {0} ≃ ℝ³` written by the interior inclusion. -/
def interiorSeamInclusionEquiv : (MorseModel 3 × PUnit.{1}) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (ContinuousLinearEquiv.prodUnique ℝ (MorseModel 3) PUnit.{1}).trans interiorSeamRechart.symm

/-- The inclusion of an open subset of the interior of a carrier, with the recharted interior model,
is a smooth embedding into the carrier. -/
theorem isSmoothEmbedding_val_interiorSeamModel :
    letI := interiorSeamCharts W O
    IsSmoothEmbedding interiorSeamModel W.model ∞
      (Subtype.val : W.pieceInterior O → W.Carrier) := by
  let _ := interiorSeamCharts W O
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    interiorSeamCharts_isManifold W O
  refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) fun x => ?_,
    Topology.IsEmbedding.subtypeVal⟩
  apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt
    continuous_subtype_val.continuousAt (interiorSeamInclusionEquiv)
  intro z hz
  rw [ModelWithCorners.extChartAt_transContinuousLinearEquiv_target] at hz
  have hw : interiorSeamRechart.symm z ∈ (extChartAt W.model x).target := by
    have h := hz
    change interiorSeamRechart.symm z ∈ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).target at h
    rw [extChartAt_target] at h
    exact interior_subset h.1
  change extChartAt W.model x.val
      (((extChartAt W.model x).symm (interiorSeamRechart.symm z) : W.pieceInterior O) : W.Carrier) =
    interiorSeamRechart.symm z
  exact (extChartAt W.model x).right_inv hw

end InteriorInclusion

/-! ## The torus of an oriented level fibred over the circle -/

section LevelTorus

open DifferentialGeometry.Manifold.RegularLevel DifferentialGeometry.Topology.Manifold

variable {H : Type*} [TopologicalSpace H] {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel 3) H) [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

/-- The linear identification of the level model with `ℝ²`. -/
abbrev levelRechart : MorseModel 2 ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm

theorem finrank_one_add_euclidean_two :
    1 + Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ (MorseModel 3) := by
  simp [MorseModel]

/-- **An oriented regular level fibred over the circle is a torus.** On a boundaryless oriented
`3`-manifold (model over `MorseModel 3`), a compact regular level `{f = 0}` with a smooth submersion
`p` to the circle whose fibres are connected is the image of a smooth torus embedding `e` with
`p ∘ e = fst`. The orientation of the level is induced "normal first" by the ambient orientation and
the unit-speed transversal field of the flow-collar kernel; B2-param then gives the torus. -/
theorem exists_torus_embedding_of_oriented_level (oM : SmoothOrientation I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = 0 → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (hK : IsCompact {x | f x = 0})
    (p : {x : M // f x = 0} → Circle)
    (hp : letI := levelChartedSpace (m := 2) I hf hr
      ContMDiff 𝓘(ℝ, MorseModel 2) (𝓡 1) ∞ p)
    (hsub : letI := levelChartedSpace (m := 2) I hf hr
      ∀ x, Surjective (mfderiv 𝓘(ℝ, MorseModel 2) (𝓡 1) p x))
    (hfib : ∀ z, IsConnected (p ⁻¹' {z})) :
    ∃ e : Torus → M, IsSmoothEmbedding torusModel I ∞ e ∧ range e = {x | f x = 0} ∧
      ∀ t, ∃ h : f (e t) = 0, p ⟨e t, h⟩ = t.1 := by
  classical
  let cS : ChartedSpace (MorseModel 2) {x : M // f x = 0} := levelChartedSpace (m := 2) I hf hr
  have hS : IsManifold 𝓘(ℝ, MorseModel 2) ∞ {x : M // f x = 0} := levelIsManifold (m := 2) I hf hr
  have : CompactSpace {x : M // f x = 0} := isCompact_iff_compactSpace.mp hK
  let cS2 : ChartedSpace (EuclideanSpace ℝ (Fin 2)) {x : M // f x = 0} :=
    linearRechart (M := {x : M // f x = 0}) levelRechart
  have hS2 : IsManifold (𝓡 2) ∞ {x : M // f x = 0} :=
    linearRechart_isManifold (M := {x : M // f x = 0}) levelRechart ∞
  let Φ := linearRechartDiffeomorph (M := {x : M // f x = 0}) levelRechart ∞
  -- the inclusion, in the `ℝ²` charts
  let ι : {x : M // f x = 0} → M := Subtype.val
  have hemb := isSmoothEmbedding_level_inclusion (m := 2) I hf hr
  have hιM : ContMDiff 𝓘(ℝ, MorseModel 2) I ∞ ι := hemb.contMDiff
  have hι : ContMDiff (𝓡 2) I ∞ ι := hιM.comp Φ.symm.contMDiff
  have hdι : ∀ x (v : TangentSpace (𝓡 2) x), mfderiv (𝓡 2) I ι x v =
      mfderiv 𝓘(ℝ, MorseModel 2) I ι x (mfderiv (𝓡 2) 𝓘(ℝ, MorseModel 2) Φ.symm x v) := by
    intro x v
    have h := mfderiv_comp x (hιM.mdifferentiableAt (by simp) (x := Φ.symm x))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp) (x := x))
    exact congrArg (fun L => L v) h
  have hΦinj : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, MorseModel 2) Φ.symm x) := fun x =>
    (Φ.symm.mfderivToContinuousLinearEquiv (by simp) x).injective
  have hιinjM : ∀ x, Injective (mfderiv 𝓘(ℝ, MorseModel 2) I ι x) := fun x =>
    (hemb.isImmersion.isImmersionAt x).mfderiv_injective (by simp)
  have hιinj : ∀ x, Injective (mfderiv (𝓡 2) I ι x) := by
    intro x v w hvw
    rw [hdι, hdι] at hvw
    exact hΦinj x (hιinjM (Φ.symm x) hvw)
  -- the transversal field
  obtain ⟨O, -, hKO, V, hV, -, hdf⟩ :=
    exists_unitSpeed_near_compact_regularSet_manifold I hf hK (fun x hx => hr x hx)
  let ν : ∀ x : {x : M // f x = 0}, ℝ →L[ℝ] TangentSpace I (ι x) := fun x =>
    ContinuousLinearMap.toSpanSingleton ℝ (V (ι x))
  have hν : ∀ a : ℝ, Continuous (fun x => (⟨ι x, ν x a⟩ : TangentBundle I M)) := by
    intro a
    have h := (hV.const_smul_section (a := a)).continuous.comp hι.continuous
    have hfun : (fun x => (⟨ι x, ν x a⟩ : TangentBundle I M)) =
        (fun y => (⟨y, (a • V) y⟩ : TangentBundle I M)) ∘ ι := by
      funext x
      simp only [Function.comp_apply, ν, ContinuousLinearMap.toSpanSingleton_apply, Pi.smul_apply]
    rw [hfun]
    exact h
  have hrange := range_mfderiv_level_inclusion (m := 2) I hf hr
  have hdfι : ∀ x (v : TangentSpace (𝓡 2) x), mfderiv I 𝓘(ℝ, ℝ) f (ι x) (mfderiv (𝓡 2) I ι x v) = 0 := by
    intro x v
    rw [hdι]
    have hmem : mfderiv 𝓘(ℝ, MorseModel 2) I ι (Φ.symm x)
        (mfderiv (𝓡 2) 𝓘(ℝ, MorseModel 2) Φ.symm x v) ∈
          (mfderiv 𝓘(ℝ, MorseModel 2) I (Subtype.val : {x : M // f x = 0} → M) (Φ.symm x)).range :=
      ⟨_, rfl⟩
    rw [hrange] at hmem
    exact hmem
  have hfin : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 2)) = Module.finrank ℝ (MorseModel 3) := by
    simp [MorseModel]
  have hbij : ∀ x, Bijective (ambientSplitFrame I (𝓡 2) ι ν x) := by
    intro x
    have hinj : Injective (ambientSplitFrame I (𝓡 2) ι ν x) := by
      rw [injective_iff_map_eq_zero]
      intro w hw
      rw [ambientSplitFrame_apply] at hw
      have hV1 : mfderiv I 𝓘(ℝ, ℝ) f (ι x) (V (ι x)) = -1 := hdf (ι x) (hKO x.2)
      have hw' : (w.1 • V (ι x) : TangentSpace I (ι x)) + mfderiv (𝓡 2) I ι x w.2 = 0 := hw
      have h0 := congrArg (mfderiv I 𝓘(ℝ, ℝ) f (ι x)) hw'
      have h3 : mfderiv I 𝓘(ℝ, ℝ) f (ι x) (mfderiv (𝓡 2) I ι x w.2) = 0 := hdfι x w.2
      rw [map_add, map_zero, map_smul, hV1, h3, add_zero] at h0
      have hw1 : w.1 = 0 := by
        have : w.1 * (-1 : ℝ) = 0 := h0
        linarith
      have hw2 : mfderiv (𝓡 2) I ι x w.2 = 0 := by
        have h1 : (ν x w.1 : MorseModel 3) = 0 := by
          change w.1 • V (ι x) = 0
          rw [hw1, zero_smul]
        rw [h1, zero_add] at hw
        exact hw
      refine Prod.ext hw1 (hιinj x ?_)
      rw [hw2]
      exact (map_zero (mfderiv (𝓡 2) I ι x)).symm
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  let σ : Fin 1 ⊕ Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) ≃
      Fin (Module.finrank ℝ (MorseModel 3)) :=
    finSumFinEquiv.trans (finCongr finrank_one_add_euclidean_two)
  let oS : SmoothOrientation (𝓡 2) {x : M // f x = 0} :=
    ambientSplitSmoothOrientation I (𝓡 2) (Module.Basis.singleton (Fin 1) ℝ) σ ι
      (hι.of_le (by norm_num)) ν hν hbij oM
  obtain ⟨O0, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  let O2 : ManifoldOrientation (𝓡 2) {x : M // f x = 0} 2 :=
    cast (congrArg (fun k => ManifoldOrientation (𝓡 2) {x : M // f x = 0} k) h2) O0
  -- the submersion in the `ℝ²` charts
  have hp2 : ContMDiff (𝓡 2) (𝓡 1) ∞ p := hp.comp Φ.symm.contMDiff
  have hsub2 : ∀ x, Surjective (mfderiv (𝓡 2) (𝓡 1) p x) := by
    intro x v
    have h := mfderiv_comp x (hp.mdifferentiableAt (by simp) (x := Φ.symm x))
      (Φ.symm.contMDiff.mdifferentiableAt (by simp) (x := x))
    obtain ⟨w, hw⟩ := hsub (Φ.symm x) v
    obtain ⟨w', hw'⟩ := (Φ.symm.mfderivToContinuousLinearEquiv (by simp) x).surjective w
    refine ⟨w', ?_⟩
    have h' := congrArg (fun L => L w') h
    change mfderiv (𝓡 2) (𝓡 1) p x w' = _ at h'
    rw [h', ContinuousLinearMap.comp_apply]
    change mfderiv 𝓘(ℝ, MorseModel 2) (𝓡 1) p (Φ.symm x)
      ((Φ.symm.mfderivToContinuousLinearEquiv (by simp) x) w') = v
    rw [hw']
    exact hw
  obtain ⟨e, he⟩ := exists_torus_param_of_circle_fibred_surface O2 p hp2 hsub2 hfib
  refine ⟨ι ∘ e, ⟨isImmersion_of_injective_mfderiv (by simp) (hι.comp e.contMDiff) ?_,
    Topology.IsEmbedding.subtypeVal.comp e.toHomeomorph.isEmbedding⟩, ?_, ?_⟩
  · intro t v w hvw
    have h := mfderiv_comp t (hι.mdifferentiableAt (by simp) (x := e t))
      (e.contMDiff.mdifferentiableAt (by simp) (x := t))
    have hv := congrArg (fun L => L v) h
    have hw := congrArg (fun L => L w) h
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [hv, hw] at hvw
    exact (e.mfderivToContinuousLinearEquiv (by simp) t).injective (hιinj (e t) hvw)
  · ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact (e t).2
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, ?_⟩
      change ((e (e.symm ⟨y, hy⟩) : {x : M // f x = 0}) : M) = y
      rw [Diffeomorph.apply_symm_apply]
  · intro t
    exact ⟨(e t).2, he t⟩

end LevelTorus

end GC.GraphManifold.Assembly
