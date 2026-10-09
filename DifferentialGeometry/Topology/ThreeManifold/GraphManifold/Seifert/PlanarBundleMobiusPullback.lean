import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobiusCover
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundle
import DifferentialGeometry.Topology.Manifold.CoveringAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas

/-!
# The pulled-back circle fibration over the annulus

Chapter 6, lane MD5, tier T4 of the P1 Morse-decomposition plan, second file (the first is
`SF/PlanarBundleMobiusCover.lean`). For a circle fibration `F` whose base carries a smooth
embedding `E` onto `mobiusModel`, the fibre product `PullTotal F hrange` of the double cover
`cover : annulusSurface → F.base` and the projection is a compact carrier `pullCarrier F hE hrange`:
its projection `pullProj` to `C` is a local homeomorphism (`isLocalHomeomorph_pullProj`; on the
sheet over a half annulus it is inverted through `localSection`), so `C`'s atlas lifts by
`Manifold.coveringChartedSpace` and `C`'s orientation pulls back
(`Manifold.manifoldOrientationPullback`). Maps into it are smooth when their composite with
`pullProj` is (`contMDiffAt_pull_of`, through the smooth sheet inverses). The first factor is a
circle fibration `pullFibration F hE hrange` over `annulusSurface`, whose chart over a half annulus
`pullNbhd x₀` is the chart of `F` at `cover x₀` read through the fibre product (`pullTriv`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

namespace MobiusCover

theorem dir_mem_sheet (x : annulusSurface.{u}.Carrier) : x ∈ sheet (dir (annEmb x)) := by
  have hx := ne_zero_of_mem_annulus (annEmb_mem x)
  change 0 < (annEmb x * conj (dir (annEmb x))).re
  rw [dir, Complex.real_smul, map_mul, Complex.conj_ofReal, mul_left_comm, Complex.mul_conj,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  have h := norm_pos_iff.mpr hx
  have h2 := Complex.normSq_pos.mpr hx
  positivity

theorem norm_dir_annEmb (x : annulusSurface.{u}.Carrier) : ‖dir (annEmb x)‖ = 1 :=
  norm_dir (ne_zero_of_mem_annulus (annEmb_mem x))

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
  (hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E) (hrange : range E = mobiusModel)

abbrev PullTotal : Type u :=
  {q : annulusSurface.{u}.Carrier × U // cover hrange q.1 = F.projection q.2}

def pullProj (q : PullTotal F hrange) : C.Carrier := q.val.2.val

def pullTarget (z₀ : ℂ) : Set C.Carrier :=
  Subtype.val '' (F.projection ⁻¹' (cover.{u} hrange '' sheet z₀))

include hE in
theorem isOpen_pullTarget (z₀ : ℂ) : IsOpen (pullTarget F hrange z₀) :=
  U.isOpen.isOpenMap_subtype_val _
    ((isOpen_cover_image_sheet hE hrange z₀).preimage F.projection.continuous)

def pullSheet (z₀ : ℂ) : Set (PullTotal F hrange) := {q | q.val.1 ∈ sheet z₀}

theorem isOpen_pullSheet (z₀ : ℂ) : IsOpen (pullSheet F hrange z₀) :=
  (isOpen_sheet z₀).preimage (continuous_fst.comp continuous_subtype_val)

theorem mem_pullTarget {z₀ : ℂ} {x : C.Carrier} (hx : x ∈ pullTarget F hrange z₀) :
    ∃ h : x ∈ U, F.projection ⟨x, h⟩ ∈ cover.{u} hrange '' sheet z₀ := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y.2, hy⟩

def pullSheetHomeomorph {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) :
    pullSheet F hrange z₀ ≃ₜ pullTarget F hrange z₀ where
  toFun q := ⟨pullProj F hrange q.val, q.val.val.2, by
    exact ⟨q.val.val.1, q.2, q.val.2⟩, rfl⟩
  invFun x := ⟨⟨(localSection (E := E) z₀ (F.projection ⟨x.val, (mem_pullTarget F hrange x.2).1⟩),
      ⟨x.val, (mem_pullTarget F hrange x.2).1⟩),
      cover_localSection hrange hz₀ (mem_pullTarget F hrange x.2).2⟩,
    localSection_mem hrange hz₀ (mem_pullTarget F hrange x.2).2⟩
  left_inv q := by
    obtain ⟨⟨⟨w, y⟩, hq⟩, hw⟩ := q
    have hw' : w ∈ sheet z₀ := hw
    apply Subtype.ext
    apply Subtype.ext
    change (localSection (E := E) z₀ (F.projection y), y) = (w, y)
    rw [← hq, localSection_cover hrange hz₀ hw']
  right_inv x := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.comp (continuous_snd.comp
      (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    have hU : Continuous fun x : pullTarget F hrange z₀ =>
        (⟨x.val, (mem_pullTarget F hrange x.2).1⟩ : U) :=
      continuous_subtype_val.subtype_mk _
    have hL : Continuous fun x : pullTarget F hrange z₀ =>
        localSection (E := E) z₀ (F.projection ⟨x.val, (mem_pullTarget F hrange x.2).1⟩) :=
      (contMDiffOn_localSection hE hrange hz₀).continuousOn.comp_continuous
        (F.projection.continuous.comp hU) fun x => (mem_pullTarget F hrange x.2).2
    exact ((hL.prodMk hU).subtype_mk _).subtype_mk _

include hE in
theorem isLocalHomeomorph_pullProj : IsLocalHomeomorph (pullProj F hrange) := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr fun q₀ => ?_
  set z₀ := dir (annEmb q₀.val.1)
  have hz₀ : ‖z₀‖ = 1 := norm_dir_annEmb _
  refine ⟨pullSheet F hrange z₀, (isOpen_pullSheet F hrange z₀).mem_nhds (dir_mem_sheet _), ?_⟩
  have h : (pullSheet F hrange z₀).domRestrict (pullProj F hrange) =
      Subtype.val ∘ pullSheetHomeomorph F hE hrange hz₀ := rfl
  rw [h]
  exact (isOpen_pullTarget F hE hrange z₀).isOpenEmbedding_subtypeVal.comp
    (pullSheetHomeomorph F hE hrange hz₀).isOpenEmbedding

include hE in
theorem compactSpace_pullTotal : CompactSpace (PullTotal F hrange) := by
  have hU : CompactSpace U := by
    have h := CircleFibration.isCompact_preimage F (K := univ) isClosed_univ
    rw [preimage_univ] at h
    exact isCompact_univ_iff.mp h
  exact isCompact_iff_compactSpace.mp (isClosed_eq ((continuous_cover hE hrange).comp
    continuous_fst) (F.projection.continuous.comp continuous_snd)).isCompact

theorem bijective_mfderiv_of_isLocalHomeomorph {H X Y : Type*} [TopologicalSpace H]
    {EH : Type*} [NormedAddCommGroup EH] [NormedSpace ℝ EH] {I : ModelWithCorners ℝ EH H}
    [TopologicalSpace X] [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] {p : X → Y}
    (hp : IsLocalHomeomorph p) (x : X) :
    letI := Manifold.coveringChartedSpace (H := H) hp
    Function.Bijective (mfderiv I I p x) := by
  let := Manifold.coveringChartedSpace (H := H) hp
  let := Manifold.covering_isManifold hp I
  obtain ⟨e, he⟩ :=
    ((Manifold.covering_projection_isLocalDiffeomorph hp I) x).isInvertible_mfderiv (by simp)
  rw [← he]
  exact e.bijective

def pullCarrier : CompactCarrier.{u} where
  kind := C.kind
  Carrier := PullTotal F hrange
  charts := Manifold.coveringChartedSpace (H := C.kind.Space)
    (isLocalHomeomorph_pullProj F hE hrange)
  smooth := Manifold.covering_isManifold (isLocalHomeomorph_pullProj F hE hrange) C.model
  compact := compactSpace_pullTotal F hE hrange
  secondCountable := inferInstanceAs (SecondCountableTopology
    ({q | cover hrange q.1 = F.projection q.2} : Set (annulusSurface.{u}.Carrier × U)))
  orientation := by
    letI := Manifold.coveringChartedSpace (H := C.kind.Space)
      (isLocalHomeomorph_pullProj F hE hrange)
    letI := Manifold.covering_isManifold (isLocalHomeomorph_pullProj F hE hrange) C.model
    exact Manifold.manifoldOrientationPullback C.model C.model (finrank_euclideanSpace_fin)
      (pullProj F hrange) (Manifold.covering_projection_contMDiff _ C.model)
      (bijective_mfderiv_of_isLocalHomeomorph (isLocalHomeomorph_pullProj F hE hrange))
      C.orientation

theorem pullCarrier_model : (pullCarrier F hE hrange).model = C.model := rfl

theorem contMDiff_pullProj :
    ContMDiff (pullCarrier F hE hrange).model C.model ∞
      (fun q : (pullCarrier F hE hrange).Carrier => pullProj F hrange q) :=
  Manifold.covering_projection_contMDiff (isLocalHomeomorph_pullProj F hE hrange) C.model

theorem contMDiff_pullSnd :
    ContMDiff (pullCarrier F hE hrange).model C.model ∞
      (fun q : (pullCarrier F hE hrange).Carrier => (q.val.2 : U)) :=
  (ContMDiff.subtypeVal_comp_iff U _).mp (contMDiff_pullProj F hE hrange)

theorem contMDiff_pullFst :
    ContMDiff (pullCarrier F hE hrange).model (SurfaceModel.model annulusSurface.{u}.kind) ∞
      (fun q : (pullCarrier F hE hrange).Carrier => q.val.1) := by
  intro q₀
  set z₀ := dir (annEmb q₀.val.1)
  have hz₀ : ‖z₀‖ = 1 := norm_dir_annEmb _
  have hq₀ : q₀.val.1 ∈ sheet z₀ := dir_mem_sheet _
  have hb : F.projection q₀.val.2 ∈ cover.{u} hrange '' sheet z₀ := ⟨q₀.val.1, hq₀, q₀.2⟩
  have hπ : ContMDiffAt (pullCarrier F hE hrange).model (SurfaceModel.model F.base.kind) ∞
      (fun q : (pullCarrier F hE hrange).Carrier => F.projection q.val.2) q₀ :=
    (F.smooth.comp (contMDiff_pullSnd F hE hrange)).contMDiffAt
  have hL := (contMDiffAt_localSection hE hrange hz₀ hb).comp q₀ hπ
  refine hL.congr_of_eventuallyEq ?_
  filter_upwards [(isOpen_pullSheet F hrange z₀).mem_nhds hq₀] with q hq
  change q.val.1 = localSection (E := E) z₀ (F.projection q.val.2)
  rw [← q.2, localSection_cover hrange hz₀ hq]

theorem contMDiffAt_pull_of {X : Type*} [TopologicalSpace X] {EX HX : Type*}
    [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
    {J : ModelWithCorners ℝ EX HX} [ChartedSpace HX X]
    {f : X → (pullCarrier F hE hrange).Carrier} {x : X} (hf : ContinuousAt f x)
    (hpf : ContMDiffAt J C.model ∞ (fun y => pullProj F hrange (f y)) x) :
    ContMDiffAt J (pullCarrier F hE hrange).model ∞ f x := by
  set hl := isLocalHomeomorph_pullProj F hE hrange
  let := Manifold.coveringChartedSpace (H := C.kind.Space) hl
  let := Manifold.covering_isManifold hl C.model
  set e := hl.localInverseAt (f x)
  have he : (e.symm : (pullCarrier F hE hrange).Carrier → C.Carrier) = pullProj F hrange :=
    hl.localInverseAt_symm (f x)
  have hs := Manifold.covering_sheetInverse_contMDiff hl C.model e.symm (fun y _ => by
    rw [he])
  have hmem : pullProj F hrange (f x) ∈ e.source := hl.apply_self_mem_localInverseAt_source
  have hev : f =ᶠ[𝓝 x] fun y => e (pullProj F hrange (f y)) := by
    filter_upwards [hf (e.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with y hy
    have h1 := e.right_inv hy
    rw [he] at h1
    exact h1.symm
  exact ((hs.contMDiffAt (e.symm.open_target.mem_nhds hmem)).comp x hpf).congr_of_eventuallyEq
    hev

def pullProjection :
    C(↥(⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier),
      annulusSurface.{u}.Carrier) :=
  ⟨fun q => q.val.val.1, (continuous_fst.comp continuous_subtype_val).comp continuous_subtype_val⟩

def pullNbhd (x₀ : annulusSurface.{u}.Carrier) :
    TopologicalSpace.Opens annulusSurface.{u}.Carrier :=
  ⟨sheet (dir (annEmb x₀)) ∩
      cover hrange ⁻¹' (F.neighborhood (cover hrange x₀) : Set F.base.Carrier),
    (isOpen_sheet _).inter ((F.neighborhood _).isOpen.preimage (continuous_cover hE hrange))⟩

theorem mem_pullNbhd (x₀ : annulusSurface.{u}.Carrier) : x₀ ∈ pullNbhd F hE hrange x₀ :=
  ⟨dir_mem_sheet x₀, F.mem_neighborhood _⟩

theorem projection_mem_neighborhood (x₀ : annulusSurface.{u}.Carrier)
    (q : TopologicalSpace.Opens.comap (pullProjection F hE hrange) (pullNbhd F hE hrange x₀)) :
    q.val.val.val.2 ∈ TopologicalSpace.Opens.comap F.projection
      (F.neighborhood (cover hrange x₀)) := by
  rw [TopologicalSpace.Opens.mem_comap, ← q.val.val.2]
  have h : q.val.val.val.1 ∈ pullNbhd F hE hrange x₀ := q.2
  exact h.2

theorem cover_eq_projection_symm (x₀ : annulusSurface.{u}.Carrier)
    (p : pullNbhd F hE hrange x₀ × Circle) :
    cover hrange p.1.val = F.projection ((F.trivialization (cover hrange x₀)).symm
      (⟨cover hrange p.1.val, p.1.2.2⟩, p.2)).val := by
  rw [← F.projection_trivialization, Diffeomorph.apply_symm_apply]

def pullTriv (x₀ : annulusSurface.{u}.Carrier) :
    TopologicalSpace.Opens.comap (pullProjection F hE hrange) (pullNbhd F hE hrange x₀)
      ≃ₘ⟮(pullCarrier F hE hrange).model,
        (SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)⟯
      (pullNbhd F hE hrange x₀ × Circle) where
  toFun q := (⟨q.val.val.val.1, TopologicalSpace.Opens.mem_comap.mp q.2⟩,
    (F.trivialization (cover hrange x₀) ⟨q.val.val.val.2, projection_mem_neighborhood F hE hrange
      x₀ q⟩).2)
  invFun p := ⟨⟨⟨(p.1.val, ((F.trivialization (cover hrange x₀)).symm
      (⟨cover hrange p.1.val, p.1.2.2⟩, p.2)).val), cover_eq_projection_symm F hE hrange x₀ p⟩,
    trivial⟩, TopologicalSpace.Opens.mem_comap.mpr p.1.2⟩
  left_inv q := by
    obtain ⟨⟨⟨⟨w, y⟩, hq⟩, -⟩, hw⟩ := q
    have hw' : w ∈ pullNbhd F hE hrange x₀ := hw
    have hy : y ∈ TopologicalSpace.Opens.comap F.projection
        (F.neighborhood (cover hrange x₀)) := by
      rw [TopologicalSpace.Opens.mem_comap, ← hq]
      exact hw'.2
    have h1 : (⟨cover hrange w, hw'.2⟩ : F.neighborhood (cover hrange x₀)) =
        ((F.trivialization (cover hrange x₀)) ⟨y, hy⟩).1 :=
      Subtype.ext (by rw [F.projection_trivialization]; exact hq)
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (w, ((F.trivialization (cover hrange x₀)).symm (⟨cover hrange w, hw'.2⟩,
      ((F.trivialization (cover hrange x₀)) ⟨y, hy⟩).2)).val) = (w, y)
    rw [h1, Prod.mk.eta, Diffeomorph.symm_apply_apply]
  right_inv p := by
    apply Prod.ext
    · rfl
    · change ((F.trivialization (cover hrange x₀))
        ⟨((F.trivialization (cover hrange x₀)).symm (⟨cover hrange p.1.val, p.1.2.2⟩, p.2)).val,
          _⟩).2 = p.2
      rw [Subtype.coe_eta, Diffeomorph.apply_symm_apply]
  contMDiff_toFun := by
    refine ContMDiff.prodMk ?_ ?_
    · apply (ContMDiff.subtypeVal_comp_iff (pullNbhd F hE hrange x₀) _).mp
      exact (contMDiff_pullFst F hE hrange).comp
        (contMDiff_subtype_val.comp contMDiff_subtype_val)
    · refine contMDiff_snd.comp ((F.trivialization (cover hrange x₀)).contMDiff.comp ?_)
      apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact (contMDiff_pullSnd F hE hrange).comp
        (contMDiff_subtype_val.comp contMDiff_subtype_val)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have hN : ContMDiff ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
        (SurfaceModel.model F.base.kind) ∞
        (fun p : pullNbhd F hE hrange x₀ × Circle =>
          (⟨cover hrange p.1.val, p.1.2.2⟩ : F.neighborhood (cover hrange x₀))) := by
      apply (ContMDiff.subtypeVal_comp_iff _ _).mp
      exact (contMDiff_cover hE hrange).comp (contMDiff_subtype_val.comp contMDiff_fst)
    have hT : ContMDiff ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) C.model ∞
        (fun p : pullNbhd F hE hrange x₀ × Circle => ((F.trivialization (cover hrange x₀)).symm
          (⟨cover hrange p.1.val, p.1.2.2⟩, p.2)).val.val) :=
      contMDiff_subtype_val.comp (contMDiff_subtype_val.comp
        ((F.trivialization (cover hrange x₀)).symm.contMDiff.comp (hN.prodMk contMDiff_snd)))
    intro p
    refine contMDiffAt_pull_of F hE hrange ?_ (hT p)
    refine Continuous.continuousAt ?_
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp ((F.trivialization (cover hrange x₀)).symm.continuous.comp
        (hN.continuous.prodMk continuous_snd)))

abbrev pullFibration : CircleFibration (pullCarrier F hE hrange) ⊤ where
  base := annulusSurface.{u}
  projection := pullProjection F hE hrange
  surjective x := by
    obtain ⟨y, hy⟩ := F.surjective (cover hrange x)
    exact ⟨⟨⟨(x, y), hy.symm⟩, trivial⟩, rfl⟩
  smooth := (contMDiff_pullFst F hE hrange).comp contMDiff_subtype_val
  neighborhood := pullNbhd F hE hrange
  mem_neighborhood := mem_pullNbhd F hE hrange
  trivialization := pullTriv F hE hrange
  projection_trivialization _ _ := rfl

end MobiusCover

end GC.Seifert
