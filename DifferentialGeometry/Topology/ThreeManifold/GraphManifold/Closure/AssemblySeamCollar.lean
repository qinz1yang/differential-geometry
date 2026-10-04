import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.ManifoldFlow
import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior
import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.ContMDiff.OpenSubtype
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Geometry.Manifold.Immersion

/-!
# Chapter-14 assembly, bridge B2-interior: torus and sphere seams of regular levels

The frozen statements `exists_torusSeam_of_regular_level` and `exists_sphereSeam_of_regular_level`
of the chapter-14 assembly design (`docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`,
§3 "B2-interior", §4 row §2). A compact connected component of a regular interior level, given by
an actual torus (resp. sphere) parametrization, gets a signed two-sided collar whose source is
exactly `signedCollarSource` (resp. `sphereSignedCollarSource`), inside any prescribed open set,
with `f (seam (t, s)) = c + δ s`.

Route. On an open subset of the interior we use the interior charts, recharted to `MorseModel 3`
(`interiorSeamModel`), and the flow collar of a compact regular level
(`RegularLevel/Collar/ManifoldFlow.lean:57`). The collar is `(t, s) ↦ F (param t, -r s)`; its
inverse is `y ↦ (param⁻¹ (F (y, f y - c)), (f y - c) / r)`, smooth by the local immersion criterion
`ContMDiffAt.iff_comp_isImmersionAt`. For the sphere the isolation of the surface in its level is
proved (`exists_isolating_open_of_regular_level`), so no `hiso` hypothesis is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
  GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The linear rechart of `ℝ³` onto the Morse model `Fin 3 → ℝ`. -/
abbrev interiorSeamRechart : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] MorseModel 3 :=
  EuclideanSpace.equiv (Fin 3) ℝ

/-- The boundaryless model of the interior of a carrier, recharted to `MorseModel 3`. -/
abbrev interiorSeamModel : ModelWithCorners ℝ (MorseModel 3) (EuclideanSpace ℝ (Fin 3)) :=
  𝓘(ℝ, EuclideanSpace ℝ (Fin 3)).transContinuousLinearEquiv interiorSeamRechart

instance interiorSeamModel_boundaryless_ASMB2 : interiorSeamModel.Boundaryless where
  range_eq_univ := by
    rw [ModelWithCorners.transContinuousLinearEquiv_range, ModelWithCorners.range_eq_univ,
      image_univ]
    exact interiorSeamRechart.surjective.range_eq

section Interior

variable (W : CompactCarrier.{u}) (O : TopologicalSpace.Opens W.Carrier)

/-- The interior charts on an open subset of the interior of a carrier. -/
abbrev interiorSeamCharts : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (W.pieceInterior O) :=
  DifferentialGeometry.Manifold.interiorChartedSpace W.model ∞

theorem interiorSeamCharts_isManifold :
    letI := interiorSeamCharts W O
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
  DifferentialGeometry.Manifold.interiorIsManifold W.model ∞

/-- The inclusion, from the recharted interior model to the carrier model, is smooth. -/
theorem contMDiff_val_interiorSeamModel :
    letI := interiorSeamCharts W O
    ContMDiff interiorSeamModel W.model ∞ (Subtype.val : W.pieceInterior O → W.Carrier) := by
  let _ := interiorSeamCharts W O
  have h : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) W.model ∞
      (Subtype.val : W.pieceInterior O → W.Carrier) :=
    (contMDiff_subtype_val (I := W.model)).comp
      (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id W.model ∞)
  exact interiorSeamRechart.contMDiff_transContinuousLinearEquiv_left.mpr h

/-- The identity, from the open-subset structure to the recharted interior model, is smooth. -/
theorem contMDiff_id_interiorSeamModel :
    letI := interiorSeamCharts W O
    ContMDiff W.model interiorSeamModel ∞ (id : W.pieceInterior O → W.pieceInterior O) := by
  let _ := interiorSeamCharts W O
  exact interiorSeamRechart.contMDiff_transContinuousLinearEquiv_right.mpr
    (DifferentialGeometry.Manifold.contMDiff_id_interiorAtlas W.model ∞)

/-- A map out of the interior is smooth at a point if its restriction is smooth in the recharted
interior model there. -/
theorem contMDiffAt_of_interiorSeamModel {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {K : ModelWithCorners ℝ F G} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace G Y] {g : W.Carrier → Y} (x : W.pieceInterior O) :
    letI := interiorSeamCharts W O
    ContMDiffAt interiorSeamModel K ∞ (g ∘ Subtype.val) x → ContMDiffAt W.model K ∞ g x := by
  let _ := interiorSeamCharts W O
  intro h
  have hid := (contMDiff_id_interiorSeamModel W O) x
  exact contMDiffAt_subtype_iff.mp (ContMDiffAt.comp (g := g ∘ Subtype.val) (f := id) x h hid)

/-- A smooth map with values in an open subset of the interior is smooth into that subset with
the recharted interior model. -/
theorem contMDiff_codRestrict_interiorSeamModel {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace G] {K : ModelWithCorners ℝ F G} {X : Type*} [TopologicalSpace X]
    [ChartedSpace G X] {g : X → W.Carrier} (hg : ContMDiff K W.model ∞ g)
    (hgO : ∀ x, g x ∈ W.pieceInterior O) :
    letI := interiorSeamCharts W O
    ContMDiff K interiorSeamModel ∞ (fun x => (⟨g x, hgO x⟩ : W.pieceInterior O)) := by
  let _ := interiorSeamCharts W O
  have h : ContMDiff K W.model ∞ (fun x => (⟨g x, hgO x⟩ : W.pieceInterior O)) :=
    (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff (W.pieceInterior O) _).mp hg
  exact (contMDiff_id_interiorSeamModel W O).comp h

end Interior

section MFDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- Local form of `mfderiv_interiorAtlas` (`MFDeriv/Interior.lean:45`): only differentiability at
the point is assumed. -/
theorem mfderiv_interiorAtlas_of_mdifferentiableAt (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] [BoundarylessManifold I M] {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) :
    let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
    (show E →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) =
      (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) := by
  let _ := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := M)
  change (show E →L[ℝ] ℝ from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x) =
    (show E →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x)
  have hf' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) f x :=
    MDifferentiableAt.comp (g := f) (f := id) x hf
      (((DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id I ∞) x).mdifferentiableAt
      (by simp))
  erw [DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint 𝓘(ℝ, E)
    hf' BoundarylessManifold.isInteriorPoint,
    DifferentialGeometry.Manifold.mfderiv_eq_fderiv_extChartAt_of_isInteriorPoint I
      hf BoundarylessManifold.isInteriorPoint]
  rfl

end MFDeriv

section Regular

variable (W : CompactCarrier.{u}) (O : TopologicalSpace.Opens W.Carrier)

/-- Regularity transfers from the carrier model to the recharted interior model. -/
theorem mfderiv_interiorSeamModel_ne_zero {f : W.Carrier → ℝ} (x : W.pieceInterior O)
    (hf : ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ f x) (hne : mfderiv W.model 𝓘(ℝ, ℝ) f x ≠ 0) :
    letI := interiorSeamCharts W O
    mfderiv interiorSeamModel 𝓘(ℝ, ℝ) (fun y : W.pieceInterior O => f y) x ≠ 0 := by
  let _ := interiorSeamCharts W O
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    interiorSeamCharts_isManifold W O
  let g : W.pieceInterior O → ℝ := fun y => f y
  have hfd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f x := hf.mdifferentiableAt (by simp)
  have hg : MDifferentiableAt W.model 𝓘(ℝ, ℝ) g x :=
    hfd.comp x (((contMDiff_subtype_val (I := W.model) (n := ∞)) x).mdifferentiableAt (by simp))
  have hopen : (show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) g x) =
      (show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) f x) := by
    have hc := mfderiv_comp (I' := W.model) x hfd
      (((contMDiff_subtype_val (I := W.model) (n := ∞)) x).mdifferentiableAt (by simp))
    change mfderiv W.model 𝓘(ℝ, ℝ) (f ∘ Subtype.val) x = _
    rw [hc, DifferentialGeometry.mfderiv_subtype_val (I := W.model)]
    rfl
  have hint := mfderiv_interiorAtlas_of_mdifferentiableAt W.model hg
  have hgE : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, ℝ) g x :=
    MDifferentiableAt.comp (g := g) (f := id) x hg
      (((DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id W.model ∞) x).mdifferentiableAt
      (by simp))
  have htr := DifferentialGeometry.Manifold.mfderiv_transContinuousLinearEquiv
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) interiorSeamRechart hgE
  intro hz
  apply hne
  have hz' : (show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) f x).comp
      interiorSeamRechart.symm.toContinuousLinearMap = 0 := by
    rw [← hopen, ← hint]
    exact htr.symm.trans hz
  apply ContinuousLinearMap.ext
  intro v
  have hv := DFunLike.congr_fun hz' (interiorSeamRechart v)
  rw [ContinuousLinearMap.comp_apply] at hv
  change (show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) f x)
    (interiorSeamRechart.symm (interiorSeamRechart v)) = 0 at hv
  exact (congrArg (fun w : EuclideanSpace ℝ (Fin 3) =>
    (show EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) f x) w)
    (interiorSeamRechart.symm_apply_apply v)).symm.trans hv

end Regular

section Core

variable {ES HS : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
  [CompactSpace S] [Nonempty S]

/-- **Signed collar of an isolated regular embedded surface.** On an open subset `O` of the
interior of a carrier, a compact smoothly embedded surface which is exactly the level `{f = c}`
inside `O`, and at which `f` is regular, has a signed two-sided collar with source exactly
`univ ×ˢ (-1, 1)`, target inside `O`, zero section the embedding, and `f (Φ (z, s)) = c + δ s`.
Kernel: `RegularLevel/Collar/ManifoldFlow.lean:57` on `O` with the recharted interior model. -/
theorem exists_signedCollar_of_isolated_level (W : CompactCarrier.{u})
    (O : TopologicalSpace.Opens W.Carrier) (f : W.Carrier → ℝ) (c : ℝ)
    (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (W.pieceInterior O))
    (param : S → W.Carrier) (hparam : IsSmoothEmbedding IS W.model ∞ param)
    (hSO : range param ⊆ W.pieceInterior O) (hc : ∀ z, f (param z) = c)
    (hlev : ∀ x ∈ W.pieceInterior O, f x = c → x ∈ range param)
    (hreg : ∀ z, mfderiv W.model 𝓘(ℝ, ℝ) f (param z) ≠ 0) :
    ∃ (δ : ℝ) (_ : 0 < δ)
      (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) W.model (S × ℝ) W.Carrier ∞),
      Φ.source = univ ×ˢ Ioo (-1) 1 ∧ Φ.target ⊆ W.pieceInterior O ∧
      (∀ z, Φ (z, 0) = param z) ∧ ∀ p ∈ Φ.source, f (Φ p) = c + δ * p.2 := by
  classical
  let O' := W.pieceInterior O
  let _ := interiorSeamCharts W O
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ O' := interiorSeamCharts_isManifold W O
  let f' : O' → ℝ := fun x => f x
  have hfat : ∀ x : O', ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ f x :=
    fun x => hf.contMDiffAt (O'.isOpen.mem_nhds x.2)
  have hf' : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞ f' :=
    fun x => (hfat x).comp x (contMDiff_val_interiorSeamModel W O x)
  let pO : S → O' := fun z => ⟨param z, hSO (mem_range_self z)⟩
  have hpO : ContMDiff IS interiorSeamModel ∞ pO :=
    contMDiff_codRestrict_interiorSeamModel W O hparam.contMDiff (fun z => hSO (mem_range_self z))
  have hlevO : ∀ x : O', f' x = c → ∃ z, pO z = x := by
    intro x hx
    obtain ⟨z, hz⟩ := hlev x x.2 hx
    exact ⟨z, Subtype.ext hz⟩
  have hK : IsCompact {x : O' | f' x = c} := by
    have hset : {x : O' | f' x = c} = range pO := by
      ext x
      constructor
      · intro hx
        obtain ⟨z, hz⟩ := hlevO x hx
        exact ⟨z, hz⟩
      · rintro ⟨z, rfl⟩
        exact hc z
    rw [hset]
    exact isCompact_range hpO.continuous
  have hr : ∀ x : O', f' x = c → mfderiv interiorSeamModel 𝓘(ℝ, ℝ) f' x ≠ 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hlevO x hx
    exact mfderiv_interiorSeamModel_ne_zero W O (pO z) (hfat (pO z)) (hreg z)
  obtain ⟨r, hr0, U', F, hF, e, hfwd, hback, htime, hval, hzero⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_flowCollar_of_compact_regularLevel_manifold
      interiorSeamModel hf' c hK hr
  have hτ : ∀ s ∈ Ioo (-1 : ℝ) 1, -(r * s) ∈ Ioo (-r) r := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  let lvl : S → {x : O' // f' x = c} := fun z => ⟨pO z, hc z⟩
  let toFun : S × ℝ → W.Carrier := fun p => (F (pO p.1, -(r * p.2)) : O').val
  have hFe : ∀ (z : S) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1),
      F (pO z, -(r * s)) = (e (lvl z, ⟨-(r * s), hτ s hs⟩) : O') := by
    intro z s hs
    rw [hfwd]
  let x₀ : O' := pO (Classical.arbitrary S)
  let toO : W.Carrier → O' := fun y => if h : y ∈ O' then ⟨y, h⟩ else x₀
  have htoO : ∀ x : O', toO x.val = x := fun x => by
    simp [toO, x.2]
  let back : O' → W.Carrier := fun x => (F (x, f' x - c)).val
  have hbackU : ∀ w : U', back (w : O') = (((e.symm w).1 : O') : W.Carrier) := by
    intro w
    simp only [back]
    rw [hback w]
  have hbackR : ∀ w : U', back (w : O') ∈ range param := by
    intro w
    obtain ⟨z, hz⟩ := hlevO _ (e.symm w).1.2
    exact ⟨z, by rw [hbackU w, ← hz]⟩
  let invFun : W.Carrier → S × ℝ := fun y => (Function.invFun param (back (toO y)), (f y - c) / r)
  have hinj : Injective param := hparam.isEmbedding.injective
  have hmapS : ∀ p ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)),
      toFun p ∈ Subtype.val '' (U' : Set O') := by
    rintro ⟨z, s⟩ ⟨-, hs⟩
    refine ⟨(e (lvl z, ⟨-(r * s), hτ s hs⟩) : O'), (e _).2, ?_⟩
    simp only [toFun]
    rw [hFe z s hs]
  have hmapT : ∀ y ∈ Subtype.val '' (U' : Set O'),
      invFun y ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)) := by
    rintro y ⟨x, hxU, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    have ht := htime ⟨x, hxU⟩
    have hb := (e.symm ⟨x, hxU⟩).2.2
    rw [ht] at hb
    change -r < c - f x ∧ c - f x < r at hb
    change -1 < (f x - c) / r ∧ (f x - c) / r < 1
    constructor
    · rw [lt_div_iff₀ hr0]
      linarith [hb.2]
    · rw [div_lt_iff₀ hr0]
      linarith [hb.1]
  have hleft : ∀ p ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)), invFun (toFun p) = p := by
    rintro ⟨z, s⟩ ⟨-, hs⟩
    let q : {x : O' // f' x = c} × Ioo (-r) r := (lvl z, ⟨-(r * s), hτ s hs⟩)
    have hy : toFun (z, s) = ((e q : O') : W.Carrier) := by
      simp only [toFun]
      rw [hFe z s hs]
    have hb : back (toO (toFun (z, s))) = param z := by
      rw [hy, htoO, hbackU, e.symm_apply_apply]
    have hv : f (toFun (z, s)) = c + r * s := by
      rw [hy]
      have := hval q
      change f ((e q : O') : W.Carrier) = c - -(r * s) at this
      rw [this]
      ring
    simp only [invFun]
    rw [hb, hv, Function.leftInverse_invFun hinj z]
    congr 1
    field_simp
    ring
  have hright : ∀ y ∈ Subtype.val '' (U' : Set O'), toFun (invFun y) = y := by
    rintro y ⟨x, hxU, rfl⟩
    let w : U' := ⟨x, hxU⟩
    let q := e.symm w
    have hz₀ : param (Function.invFun param (back (toO x.val))) = back (toO x.val) := by
      rw [htoO]
      exact Function.invFun_eq (hbackR w)
    have hpq : pO (Function.invFun param (back (toO x.val))) = (q.1 : O') := by
      apply Subtype.ext
      change param _ = _
      rw [hz₀, htoO]
      exact hbackU w
    have hsq : -(r * ((f x - c) / r)) = (q.2 : ℝ) := by
      rw [htime w]
      field_simp
      ring
    simp only [toFun, invFun]
    rw [hpq, hsq, ← hfwd q]
    change ((e (e.symm w) : O') : W.Carrier) = x
    rw [e.apply_symm_apply]
  have hbackS : ContMDiff interiorSeamModel W.model ∞ back :=
    (contMDiff_val_interiorSeamModel W O).comp
      (hF.comp (contMDiff_id.prodMk (hf'.sub contMDiff_const)))
  have htoFun : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) W.model ∞ toFun := by
    have hs : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : S × ℝ => -(r * p.2)) :=
      ((contDiff_const.mul contDiff_id).neg : ContDiff ℝ ∞ (fun s : ℝ => -(r * s))).contMDiff.comp
        contMDiff_snd
    exact (contMDiff_val_interiorSeamModel W O).comp (hF.comp ((hpO.comp contMDiff_fst).prodMk hs))
  have hinvOn : ContMDiffOn W.model (IS.prod 𝓘(ℝ, ℝ)) ∞ invFun (Subtype.val '' (U' : Set O')) := by
    rintro y ⟨x, hxU, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    refine contMDiffAt_of_interiorSeamModel (K := IS.prod 𝓘(ℝ, ℝ)) (g := invFun) W O x ?_
    have hcomp : invFun ∘ Subtype.val =
        fun x' : O' => (Function.invFun param (back x'), (f' x' - c) / r) := by
      funext x'
      simp only [Function.comp_apply, invFun, htoO]
      rfl
    rw [hcomp]
    have heq : (param ∘ fun x' : O' => Function.invFun param (back x')) =ᶠ[𝓝 x] back := by
      filter_upwards [U'.isOpen.mem_nhds hxU] with x' hx'
      exact Function.invFun_eq (hbackR ⟨x', hx'⟩)
    have hG : ContMDiffAt interiorSeamModel IS ∞ (fun x' : O' => Function.invFun param (back x')) x := by
      refine (ContMDiffAt.iff_comp_isImmersionAt
        (f := fun x' : O' => Function.invFun param (back x')) (φ := param) (x := x)
        (hparam.isImmersion.isImmersionAt (Function.invFun param (back x)))).mpr ⟨?_, ?_⟩
      · apply hparam.isEmbedding.isInducing.continuousAt_iff.mpr
        exact hbackS.continuous.continuousAt.congr heq.symm
      · exact (hbackS x).congr_of_eventuallyEq heq
    have hD : ContMDiffAt interiorSeamModel 𝓘(ℝ, ℝ) ∞ (fun x' : O' => (f' x' - c) / r) x :=
      (((contDiff_id.sub contDiff_const).div_const r :
        ContDiff ℝ ∞ (fun t : ℝ => (t - c) / r)).contMDiff.comp
        hf') x
    exact hG.prodMk hD
  let Φ0 : PartialEquiv (S × ℝ) W.Carrier :=
    { toFun := toFun
      invFun := invFun
      source := univ ×ˢ Ioo (-1) 1
      target := Subtype.val '' (U' : Set O')
      map_source' := hmapS
      map_target' := hmapT
      left_inv' := hleft
      right_inv' := hright }
  let Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) W.model (S × ℝ) W.Carrier ∞ :=
    { toPartialEquiv := Φ0
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := O'.isOpen.isOpenMap_subtype_val _ U'.isOpen
      contMDiffOn_toFun := htoFun.contMDiffOn
      contMDiffOn_invFun := hinvOn }
  refine ⟨r, hr0, Φ, rfl, ?_, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩
    exact x.2
  · intro z
    change toFun (z, 0) = param z
    have h0 := hzero (lvl z)
    rw [hfwd] at h0
    have h0' : F (pO z, 0) = pO z := h0
    simp only [toFun, mul_zero, neg_zero]
    rw [h0']
  · rintro ⟨z, s⟩ ⟨-, hs⟩
    change f (toFun (z, s)) = c + r * s
    simp only [toFun]
    rw [hFe z s hs]
    have := hval (lvl z, ⟨-(r * s), hτ s hs⟩)
    change f ((e (lvl z, ⟨-(r * s), hτ s hs⟩) : O') : W.Carrier) = c - -(r * s) at this
    rw [this]
    ring

end Core

section Isolation

variable {ES HS : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S] [CompactSpace S]

/-- **Isolation of a regular embedded surface in its level.** A compact smoothly embedded surface
of dimension two lying in a regular level of `f` is open in that level, so some open neighbourhood
meets the level only in the surface. Route: regular neighbourhood
(`RegularLevel/Collar/ManifoldField.lean:62`), level atlas (`LevelAtlas.lean:135`), and an injective
immersion of equal dimension is an open embedding (`Manifold/OpenEmbedding.lean:68`). -/
theorem exists_isolating_open_of_regular_level (hdim : Module.finrank ℝ ES = 2)
    (W : CompactCarrier.{u}) (U : TopologicalSpace.Opens W.Carrier)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (W.pieceInterior U))
    (param : S → W.Carrier) (hparam : IsSmoothEmbedding IS W.model ∞ param)
    (hSU : range param ⊆ W.pieceInterior U) (hlev : ∀ z, f (param z) = c)
    (hreg : ∀ z, mfderiv W.model 𝓘(ℝ, ℝ) f (param z) ≠ 0) :
    ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ range param ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ W.pieceInterior U, f x = c → x ∈ range param := by
  classical
  let O' := W.pieceInterior U
  let _ := interiorSeamCharts W U
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ O' := interiorSeamCharts_isManifold W U
  let f' : O' → ℝ := fun x => f x
  have hfat : ∀ x : O', ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ f x :=
    fun x => hf.contMDiffAt (O'.isOpen.mem_nhds x.2)
  have hf' : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞ f' :=
    fun x => (hfat x).comp x (contMDiff_val_interiorSeamModel W U x)
  let pO : S → O' := fun z => ⟨param z, hSU (mem_range_self z)⟩
  have hpO : ContMDiff IS interiorSeamModel ∞ pO :=
    contMDiff_codRestrict_interiorSeamModel W U hparam.contMDiff (fun z => hSU (mem_range_self z))
  obtain ⟨Rset, hRopen, hKR, Vf, -, -, hdf⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_unitSpeed_near_compact_regularSet_manifold
      interiorSeamModel hf' (isCompact_range hpO.continuous)
      (by
        rintro x ⟨z, rfl⟩
        exact mfderiv_interiorSeamModel_ne_zero W U (pO z) (hfat (pO z)) (hreg z))
  let R : TopologicalSpace.Opens O' := ⟨Rset, hRopen⟩
  let f'' : R → ℝ := fun y => f' y
  have hf'' : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞ f'' := hf'.comp contMDiff_subtype_val
  have hderiv : ∀ y : R,
      mfderiv interiorSeamModel 𝓘(ℝ, ℝ) f'' y = mfderiv interiorSeamModel 𝓘(ℝ, ℝ) f' y := by
    intro y
    have hc := mfderiv_comp (I' := interiorSeamModel) y ((hf' (y : O')).mdifferentiableAt (by simp))
      (((contMDiff_subtype_val (I := interiorSeamModel) (n := ∞)) y).mdifferentiableAt (by simp))
    change mfderiv interiorSeamModel 𝓘(ℝ, ℝ) (f' ∘ Subtype.val) y = _
    rw [hc, DifferentialGeometry.mfderiv_subtype_val (I := interiorSeamModel)]
    rfl
  have hr'' : ∀ y : R, f'' y = c → mfderiv interiorSeamModel 𝓘(ℝ, ℝ) f'' y ≠ 0 := by
    intro y _ hz
    have h1 := hdf (y : O') y.2
    rw [← hderiv y, hz] at h1
    change (0 : ℝ) = -1 at h1
    norm_num at h1
  let _ := DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace interiorSeamModel hf'' hr''
  let _ : IsManifold 𝓘(ℝ, MorseModel 2) ∞ {y : R // f'' y = c} :=
    DifferentialGeometry.Manifold.RegularLevel.levelIsManifold interiorSeamModel hf'' hr''
  let pR : S → R := fun z => ⟨pO z, hKR (mem_range_self z)⟩
  have hpR : ContMDiff IS interiorSeamModel ∞ pR :=
    (DifferentialGeometry.Manifold.contMDiff_subtypeVal_comp_iff R pR).mp hpO
  let pL : S → {y : R // f'' y = c} := fun z => ⟨pR z, hlev z⟩
  have hpL : ContMDiff IS 𝓘(ℝ, MorseModel 2) ∞ pL :=
    DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_factor interiorSeamModel hf'' hr'' hpR
      (fun z => hlev z)
  have hincl := DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_inclusion
    interiorSeamModel hf'' hr''
  have hvalR : ContMDiff interiorSeamModel W.model ∞ (fun y : R => ((y : O') : W.Carrier)) :=
    (contMDiff_val_interiorSeamModel W U).comp contMDiff_subtype_val
  have himm : ∀ z, Injective (mfderiv IS 𝓘(ℝ, MorseModel 2) pL z) := by
    intro z
    have hP : Injective (mfderiv IS W.model param z) :=
      (hparam.isImmersion.isImmersionAt z).mfderiv_injective (by simp)
    have hfac : param = (fun y : R => ((y : O') : W.Carrier)) ∘ Subtype.val ∘ pL := rfl
    have hc1 := mfderiv_comp z (((hvalR.comp hincl) (pL z)).mdifferentiableAt (by simp))
      ((hpL z).mdifferentiableAt (by simp))
    rw [hfac] at hP
    change Injective (mfderiv IS W.model
      (((fun y : R => ((y : O') : W.Carrier)) ∘ Subtype.val) ∘ pL) z) at hP
    rw [hc1] at hP
    exact Injective.of_comp hP
  have hdim' : Module.finrank ℝ ES = Module.finrank ℝ (MorseModel 2) := by
    rw [hdim]
    simp [MorseModel]
  have hopen := DifferentialGeometry.Topology.Manifold.isOpenEmbedding_of_injective_immersion
    pL hpL (fun z₁ z₂ h => hparam.isEmbedding.injective
      (congrArg (fun y : {y : R // f'' y = c} => ((y.1 : O') : W.Carrier)) h)) himm hdim'
  obtain ⟨G, hG, hGeq⟩ := isOpen_induced_iff.mp hopen.isOpen_range
  refine ⟨Subtype.val '' (Subtype.val '' G : Set O'),
    O'.isOpen.isOpenMap_subtype_val _ (R.isOpen.isOpenMap_subtype_val _ hG), ?_, ?_⟩
  · rintro x ⟨z, rfl⟩
    have hz : pL z ∈ Subtype.val ⁻¹' G := by
      rw [hGeq]
      exact mem_range_self z
    exact ⟨(pR z : O'), ⟨pR z, hz, rfl⟩, rfl⟩
  · rintro x ⟨⟨_, ⟨g, hgG, rfl⟩, rfl⟩, -⟩ hx
    have hgL : (⟨g, hx⟩ : {y : R // f'' y = c}) ∈ Subtype.val ⁻¹' G := hgG
    rw [hGeq] at hgL
    obtain ⟨z, hz⟩ := hgL
    exact ⟨z, congrArg (fun y : {y : R // f'' y = c} => ((y.1 : O') : W.Carrier)) hz⟩

end Isolation

section Frozen

/-- The closure sphere is nonempty. -/
instance closureSphere_nonempty_ASMB2 : Nonempty ClosureSphere.{u} :=
  ⟨ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩⟩

/-- The signed collar source as a product set. -/
theorem univ_prod_Ioo_eq_signedCollarSource :
    (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (Torus × ℝ)) = signedCollarSource := by
  ext p
  simp [signedCollarSource]

/-- **B2-interior, torus seam.** A compact connected component `Σ` of a regular interior level,
with an actual torus parametrization, gets a signed two-sided collar whose source is exactly
`signedCollarSource`, inside any prescribed neighbourhood, with `f (seam (t, s)) = c + δ s`.
Kernel: `RegularLevel/Collar/ManifoldSmooth.lean:17` on the boundaryless open submanifold `U`. -/
theorem exists_torusSeam_of_regular_level (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (param : Torus → W.Carrier) (hparam : IsSmoothEmbedding torusModel W.model ∞ param)
    (hSU : range param ⊆ U) (hlev : ∀ t, f (param t) = c)
    (hreg : ∀ t, mfderiv W.model 𝓘(ℝ, ℝ) f (param t) ≠ 0)
    (hiso : ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ range param ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ U, f x = c → x ∈ range param)
    (V : Set W.Carrier) (hV : IsOpen V) (hSV : range param ⊆ V) :
    ∃ (δ : ℝ) (_ : 0 < δ) (S : TorusSeam W),
      S.collar.target ⊆ V ∩ U ∧ (∀ t, S.collar (t, 0) = param t) ∧
      ∀ p ∈ signedCollarSource, f (S.collar p) = c + δ * p.2 := by
  obtain ⟨V₀, hV₀, hSV₀, hiso⟩ := hiso
  let O : TopologicalSpace.Opens W.Carrier := ⟨V ∩ V₀ ∩ U, (hV.inter hV₀).inter U.isOpen⟩
  have hOsub : (W.pieceInterior O : Set W.Carrier) ⊆ V ∩ V₀ ∩ U := fun x hx => hx.1
  have hSO : range param ⊆ W.pieceInterior O :=
    fun x hx => ⟨⟨⟨hSV hx, hSV₀ hx⟩, hSU hx⟩, hU (hSU hx)⟩
  obtain ⟨δ, hδ, Φ, hsrc, htgt, hzero, hval⟩ := exists_signedCollar_of_isolated_level W O f c
    (hf.mono fun x hx => (hOsub hx).2) param hparam hSO hlev
    (fun x hx hfx => hiso x ⟨(hOsub hx).1.2, (hOsub hx).2⟩ hfx) hreg
  have hsrc' : Φ.source = signedCollarSource := hsrc.trans univ_prod_Ioo_eq_signedCollarSource
  refine ⟨δ, hδ, ⟨Φ, hsrc', fun y hy => (htgt hy).2⟩,
    fun y hy => ⟨(hOsub (htgt hy)).1.1, (hOsub (htgt hy)).2⟩, hzero, fun p hp => ?_⟩
  exact hval p (hsrc'.symm ▸ hp)

/-- **B2-interior, sphere seam.** Same with `ClosureSphere` (`MixedBoundary.lean:26–41`). -/
theorem exists_sphereSeam_of_regular_level (W : CompactCarrier.{u})
    (U : TopologicalSpace.Opens W.Carrier) (hU : (U : Set W.Carrier) ⊆ W.interior)
    (f : W.Carrier → ℝ) (c : ℝ) (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f U)
    (param : ClosureSphere.{u} → W.Carrier) (hparam : IsSmoothEmbedding (𝓡 2) W.model ∞ param)
    (hSU : range param ⊆ U) (hlev : ∀ z, f (param z) = c)
    (hreg : ∀ z, mfderiv W.model 𝓘(ℝ, ℝ) f (param z) ≠ 0)
    (V : Set W.Carrier) (hV : IsOpen V) (hSV : range param ⊆ V) :
    ∃ (δ : ℝ) (_ : 0 < δ) (S : SphereSeam W),
      S.collar.target ⊆ V ∩ U ∧ (∀ z, S.collar (z, 0) = param z) ∧
      ∀ p ∈ sphereSignedCollarSource, f (S.collar p) = c + δ * p.2 := by
  have hUU : (W.pieceInterior U : Set W.Carrier) = U :=
    Set.inter_eq_left.mpr hU
  have hSU' : range param ⊆ W.pieceInterior U := fun x hx => ⟨hSU hx, hU (hSU hx)⟩
  obtain ⟨V₀, hV₀, hSV₀, hiso⟩ := exists_isolating_open_of_regular_level (by simp) W U f c
    (hf.mono fun x hx => hx.1) param hparam hSU' hlev hreg
  let O : TopologicalSpace.Opens W.Carrier := ⟨V ∩ V₀ ∩ U, (hV.inter hV₀).inter U.isOpen⟩
  have hOsub : (W.pieceInterior O : Set W.Carrier) ⊆ V ∩ V₀ ∩ U := fun x hx => hx.1
  have hSO : range param ⊆ W.pieceInterior O :=
    fun x hx => ⟨⟨⟨hSV hx, hSV₀ hx⟩, hSU hx⟩, hU (hSU hx)⟩
  obtain ⟨δ, hδ, Φ, hsrc, htgt, hzero, hval⟩ := exists_signedCollar_of_isolated_level W O f c
    (hf.mono fun x hx => (hOsub hx).2) param hparam hSO hlev
    (fun x hx hfx => hiso x ⟨(hOsub hx).1.2, hUU.symm ▸ (hOsub hx).2⟩ hfx) hreg
  refine ⟨δ, hδ, ⟨Φ, hsrc, fun y hy => (htgt hy).2⟩,
    fun y hy => ⟨(hOsub (htgt hy)).1.1, (hOsub (htgt hy)).2⟩, hzero, fun p hp => ?_⟩
  exact hval p (hsrc.symm ▸ hp)

end Frozen

end GC.GraphManifold.Assembly
