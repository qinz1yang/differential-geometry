import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionLevelTorus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionLevelCircles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRoundedRegionInteriorCollar

/-!
# FC42 packet T3, part 3: every boundary torus of the rounded circle region is an embedded torus

For the component `c` of the base level `Λ = {rounding = 0}` (part 2), the level torus
`T_c = val '' proj⁻¹(Γ_c)` is the image of a smooth torus embedding into `W`
(`exists_levelTorus_param`). Route (review 42 §4.4): on the open set `O_c = val '' proj⁻¹(G_c)` of the
interior of `W` (with `G_c` isolating `Γ_c` in the base level) with the boundaryless recharted interior
model of B2, the level `{rounding ∘ proj = 0}` is exactly `T_c`; the submersion to the circle is the
projection followed by the circle chart of `Γ_c` (its derivative is onto: the trivializations give
local sections); its fibres are the circle fibres; the orientation is `W.orientation` restricted
(`exists_smoothOrientation_interiorSeam`). Part 1 (`exists_torus_embedding_of_oriented_level`) then
gives the torus.

* `exists_smoothOrientation_interiorSeam`: `W.orientation` on an open subset of the interior, for
  the recharted interior model;
* `exists_isolating_open_levelTorus`: an open set of `W` around `T_c` in which the zero level of the
  rounded function is exactly `T_c` (the `hiso` input of B2);
* `exists_levelTorus_param`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- `W.orientation` on an open subset of the interior, for the recharted interior model. -/
theorem exists_smoothOrientation_interiorSeam (W : CompactCarrier.{u})
    (O : TopologicalSpace.Opens W.Carrier) :
    letI := interiorSeamCharts W O
    haveI := interiorSeamCharts_isManifold W O
    Nonempty (SmoothOrientation interiorSeamModel (W.pieceInterior O)) := by
  let _ := interiorSeamCharts W O
  have hM3 : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    interiorSeamCharts_isManifold W O
  have hemb := isSmoothEmbedding_val_interiorSeamModel W O
  have hfin : Module.finrank ℝ (MorseModel 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    simp [MorseModel]
  have hbij : ∀ x, Bijective (mfderiv interiorSeamModel W.model
      (Subtype.val : W.pieceInterior O → W.Carrier) x) := fun x => by
    have hinj := (hemb.isImmersion.isImmersionAt x).mfderiv_injective (by simp)
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩
  have h3 : Module.finrank ℝ (MorseModel 3) = 3 := by simp [MorseModel]
  let O3 := DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback interiorSeamModel
    W.model h3 Subtype.val hemb.contMDiff hbij W.orientation
  exact ⟨DifferentialGeometry.Topology.Manifold.smoothOrientationOfManifoldOrientation
    interiorSeamModel
    (cast (congrArg (fun k => ManifoldOrientation interiorSeamModel (W.pieceInterior O) k) h3.symm)
      O3)⟩

namespace CircleRegion

variable {W : CompactCarrier.{u}} (R : CircleRegion W)

/-- The open set `val '' proj⁻¹(G)` of `W` over an open set `G` of the base. -/
def projOpens (G : Set R.Base) (hG : IsOpen G) : TopologicalSpace.Opens W.Carrier :=
  ⟨Subtype.val '' (R.proj ⁻¹' G), R.domain.isOpen.isOpenMap_subtype_val _ (hG.preimage R.proj.continuous)⟩

theorem projOpens_subset_domain (G : Set R.Base) (hG : IsOpen G) :
    (R.projOpens G hG : Set W.Carrier) ⊆ R.domain := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem proj_mem_of_mem_projOpens {G : Set R.Base} {hG : IsOpen G} {x : R.domain}
    (hx : (x : W.Carrier) ∈ R.projOpens G hG) : R.proj x ∈ G := by
  obtain ⟨z, hz, hzx⟩ := hx
  have : z = x := Subtype.ext hzx
  rw [← this]
  exact hz

/-- An open set of `W` around `T_c` in which the zero level of the rounded function is `T_c`. -/
theorem exists_isolating_open_levelTorus (c : ConnectedComponents R.BaseLevel) :
    ∃ V₀ : Set W.Carrier, IsOpen V₀ ∧ R.levelTorus c ⊆ V₀ ∧
      ∀ x ∈ V₀ ∩ R.domain, R.roundedFunction x = 0 → x ∈ R.levelTorus c := by
  obtain ⟨G, hG, hGeq⟩ := R.exists_isOpen_inter_level_eq_levelCircle c
  refine ⟨R.projOpens G hG, (R.projOpens G hG).isOpen, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [← hGeq] at hy
    exact hy.1
  · rintro x ⟨hxO, hxd⟩ h0
    have hG' := R.proj_mem_of_mem_projOpens (x := ⟨x, hxd⟩) hxO
    have hl : R.rounding (R.proj ⟨x, hxd⟩) = 0 := (R.roundedFunction_apply ⟨x, hxd⟩).symm.trans h0
    refine ⟨⟨x, hxd⟩, ?_, rfl⟩
    rw [← hGeq]
    exact ⟨hG', hl⟩

/-- **The level torus with a two-sided collar.** Every level torus `T_c` of the rounded circle
region is the zero section of a B2 torus seam whose collar lies in any prescribed open
neighbourhood `V` of `T_c` inside the domain, with `rounding ∘ proj (seam (t, s)) = δ s` (negative
side in the rounded region). The zero section is a smooth torus embedding into the recharted
interior (oriented level, B2-param). -/
theorem exists_levelTorus_seam (c : ConnectedComponents R.BaseLevel) (V : Set W.Carrier)
    (hV : IsOpen V) (hTV : R.levelTorus c ⊆ V) :
    ∃ (δ : ℝ) (_ : 0 < δ) (T : TorusSeam W), T.collar.target ⊆ V ∩ R.domain ∧
      range (fun t => T.collar (t, 0)) = R.levelTorus c ∧
      ∀ p ∈ signedCollarSource, R.roundedFunction (T.collar p) = δ * p.2 := by
  classical
  obtain ⟨G, hG, hGeq⟩ := R.exists_isOpen_inter_level_eq_levelCircle c
  set O := R.projOpens G hG ⊓ ⟨V, hV⟩ with hOdef
  have hOdom : (O : Set W.Carrier) ⊆ R.domain := fun x hx =>
    R.projOpens_subset_domain G hG hx.1
  have hOV : (O : Set W.Carrier) ⊆ V := fun x hx => hx.2
  let _ := interiorSeamCharts W O
  have hM3 : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (W.pieceInterior O) :=
    interiorSeamCharts_isManifold W O
  have hMdom : ∀ y : W.pieceInterior O, (y : W.Carrier) ∈ R.domain := fun y => hOdom y.2.1
  let dom : W.pieceInterior O → R.domain := fun y => ⟨y.1, hMdom y⟩
  have hdom : ContMDiff interiorSeamModel W.model ∞ dom :=
    (ContMDiff.subtypeVal_comp_iff R.domain dom).mp (contMDiff_val_interiorSeamModel W O)
  let F : W.pieceInterior O → ℝ := fun y => R.roundedFunction y
  have hfat : ∀ y : W.pieceInterior O, ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ R.roundedFunction y :=
    fun y => (R.contMDiffOn_roundedFunction y.1 (hMdom y)).contMDiffAt
      (R.domain.isOpen.mem_nhds (hMdom y))
  have hF : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞ F :=
    fun y => (hfat y).comp y (contMDiff_val_interiorSeamModel W O y)
  have hFr : ∀ y, F y = 0 → mfderiv interiorSeamModel 𝓘(ℝ, ℝ) F y ≠ 0 := fun y hy =>
    mfderiv_interiorSeamModel_ne_zero W O y (hfat y) (R.roundedFunction_regular y.1 (hMdom y) hy)
  have hFeq : ∀ y, F y = R.rounding (R.proj (dom y)) := fun y => R.roundedFunction_apply (dom y)
  have hGdom : ∀ y : W.pieceInterior O, R.proj (dom y) ∈ G := fun y =>
    R.proj_mem_of_mem_projOpens (x := dom y) y.2.1.1
  -- the level is the level torus
  have hlev : ∀ y : W.pieceInterior O, F y = 0 → R.proj (dom y) ∈ R.levelCircle c := by
    intro y hy
    rw [← hGeq]
    exact ⟨hGdom y, (hFeq y).symm.trans hy⟩
  have hmemM : ∀ x : R.domain, R.proj x ∈ R.levelCircle c → (x : W.Carrier) ∈ W.pieceInterior O :=
    fun x hx => ⟨⟨⟨x, (hGeq ▸ hx : R.proj x ∈ G ∩ {b | R.rounding b = 0}).1, rfl⟩,
      hTV ⟨x, hx, rfl⟩⟩, R.domain_interior x.2⟩
  have hFzero : ∀ x : R.domain, R.proj x ∈ R.levelCircle c → R.roundedFunction x = 0 :=
    fun x hx => (R.roundedFunction_apply x).trans (R.levelCircle_subset_level c hx)
  have himage : Subtype.val '' {y : W.pieceInterior O | F y = 0} = R.levelTorus c := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨dom y, hlev y hy, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hmemM z hz⟩, hFzero z hz, rfl⟩
  have hK : IsCompact {y : W.pieceInterior O | F y = 0} := by
    rw [Subtype.isCompact_iff, himage]
    exact R.isCompact_levelTorus c
  -- the circle chart of `Γ_c`
  let _ := R.baseLevelCharts
  have hLm := R.baseLevel_isManifold
  obtain ⟨D⟩ := R.nonempty_circle_diffeomorph_baseLevelComponent c
  have hqmem : ∀ y : {y : W.pieceInterior O // F y = 0},
      (⟨R.proj (dom y.1), (hFeq y.1).symm.trans y.2⟩ : R.BaseLevel) ∈ R.baseLevelComponent c := by
    intro y
    obtain ⟨b', hb', hb'eq⟩ := hlev y.1 y.2
    have : b' = ⟨R.proj (dom y.1), (hFeq y.1).symm.trans y.2⟩ := Subtype.ext hb'eq
    rw [← this]
    exact hb'
  let q : {y : W.pieceInterior O // F y = 0} → R.baseLevelComponent c := fun y =>
    ⟨⟨R.proj (dom y.1), (hFeq y.1).symm.trans y.2⟩, hqmem y⟩
  let p : {y : W.pieceInterior O // F y = 0} → Circle := fun y => D.symm (q y)
  let _ := DifferentialGeometry.Manifold.RegularLevel.levelChartedSpace (m := 2) interiorSeamModel
    hF hFr
  have hS := DifferentialGeometry.Manifold.RegularLevel.levelIsManifold (m := 2) interiorSeamModel
    hF hFr
  have hincl := DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_inclusion (m := 2)
    interiorSeamModel hF hFr
  have hq : ContMDiff 𝓘(ℝ, MorseModel 2) 𝓘(ℝ, BaseLevelModel) ∞ q := by
    refine (ContMDiff.subtypeVal_comp_iff (R.baseLevelComponent c) q).mp ?_
    refine contMDiff_baseLevel_iff.mpr ?_
    exact R.proj_smooth.comp (hdom.comp hincl)
  have hp : ContMDiff 𝓘(ℝ, MorseModel 2) (𝓡 1) ∞ p := D.symm.contMDiff.comp hq
  -- the derivative of `q` is onto: local sections from the trivializations
  have hsubq : ∀ y, Surjective (mfderiv 𝓘(ℝ, MorseModel 2) 𝓘(ℝ, BaseLevelModel) q y) := by
    intro y
    set b0 := R.proj (dom y.1) with hb0
    set T := R.trivialization b0
    have hy0 : dom y.1 ∈ TopologicalSpace.Opens.comap R.proj (R.neighborhood b0) :=
      R.mem_neighborhood b0
    set θ0 := (T ⟨dom y.1, hy0⟩).2
    let N0 : TopologicalSpace.Opens (R.baseLevelComponent c) :=
      ⟨{l | ((l : R.BaseLevel) : R.Base) ∈ R.neighborhood b0},
        (R.neighborhood b0).isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)⟩
    let s0 : N0 → TopologicalSpace.Opens.comap R.proj (R.neighborhood b0) := fun l =>
      T.symm (⟨((l.1 : R.BaseLevel) : R.Base), l.2⟩, θ0)
    have hs0proj : ∀ l : N0, R.proj (s0 l).1 = ((l.1 : R.BaseLevel) : R.Base) := fun l =>
      R.proj_trivialization_symm b0 _
    have hs0circ : ∀ l : N0, R.proj (s0 l).1 ∈ R.levelCircle c := fun l => by
      rw [hs0proj]
      exact ⟨l.1.1, l.1.2, rfl⟩
    let σ' : N0 → W.pieceInterior O := fun l => ⟨(s0 l).1.1, hmemM (s0 l).1 (hs0circ l)⟩
    have hσ'F : ∀ l, F (σ' l) = 0 := fun l => hFzero (s0 l).1 (hs0circ l)
    let σ : N0 → {y : W.pieceInterior O // F y = 0} := fun l => ⟨σ' l, hσ'F l⟩
    have hg : ContMDiff 𝓘(ℝ, BaseLevelModel) W.model ∞ (fun l : N0 => ((s0 l).1 : W.Carrier)) := by
      have hN : ContMDiff 𝓘(ℝ, BaseLevelModel) ((𝓡 2).prod (𝓡 1)) ∞
          (fun l : N0 => ((⟨((l.1 : R.BaseLevel) : R.Base), l.2⟩ : R.neighborhood b0), θ0)) := by
        refine ContMDiff.prodMk ?_ contMDiff_const
        refine (ContMDiff.subtypeVal_comp_iff (R.neighborhood b0) _).mp ?_
        exact (R.contMDiff_baseLevel_val.comp contMDiff_subtype_val).comp contMDiff_subtype_val
      exact (contMDiff_subtype_val.comp contMDiff_subtype_val).comp (T.symm.contMDiff.comp hN)
    have hσ' : ContMDiff 𝓘(ℝ, BaseLevelModel) interiorSeamModel ∞ σ' :=
      contMDiff_codRestrict_interiorSeamModel W O hg (fun l => hmemM (s0 l).1 (hs0circ l))
    have hσ : ContMDiff 𝓘(ℝ, BaseLevelModel) 𝓘(ℝ, MorseModel 2) ∞ σ :=
      DifferentialGeometry.Manifold.RegularLevel.contMDiff_level_factor (m := 2) interiorSeamModel
        hF hFr hσ' hσ'F
    have hqσ : q ∘ σ = (Subtype.val : N0 → R.baseLevelComponent c) := by
      funext l
      apply Subtype.ext
      apply Subtype.ext
      exact hs0proj l
    let l0 : N0 := ⟨q y, R.mem_neighborhood b0⟩
    have hσy : σ l0 = y := by
      have hT : T ⟨dom y.1, hy0⟩ = (⟨b0, R.mem_neighborhood b0⟩, θ0) :=
        Prod.ext (Subtype.ext (R.projection_trivialization b0 _)) rfl
      have hs : s0 l0 = ⟨dom y.1, hy0⟩ := by
        change T.symm (⟨b0, R.mem_neighborhood b0⟩, θ0) = ⟨dom y.1, hy0⟩
        rw [← hT, Diffeomorph.symm_apply_apply]
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : TopologicalSpace.Opens.comap R.proj (R.neighborhood b0) =>
        ((z.1 : R.domain) : W.Carrier)) hs
    have hsurj : Surjective (mfderiv 𝓘(ℝ, MorseModel 2) 𝓘(ℝ, BaseLevelModel) q (σ l0)) := by
      intro v
      have hd := mfderiv_comp l0 (hq.mdifferentiableAt (by simp) (x := σ l0))
        (hσ.mdifferentiableAt (by simp) (x := l0))
      have h1 := congrArg (fun L => L v) hd
      have h2 := congrArg (fun g : N0 → R.baseLevelComponent c =>
        (mfderiv 𝓘(ℝ, BaseLevelModel) 𝓘(ℝ, BaseLevelModel) g l0 v : BaseLevelModel)) hqσ
      have h3 := DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓘(ℝ, BaseLevelModel)) N0 l0 v
      refine ⟨mfderiv 𝓘(ℝ, BaseLevelModel) 𝓘(ℝ, MorseModel 2) σ l0 v, ?_⟩
      exact h1.symm.trans (h2.trans h3)
    rw [hσy] at hsurj
    exact hsurj
  have hsub : ∀ y, Surjective (mfderiv 𝓘(ℝ, MorseModel 2) (𝓡 1) p y) := by
    intro y w
    have hd := mfderiv_comp y (D.symm.contMDiff.mdifferentiableAt (by simp) (x := q y))
      (hq.mdifferentiableAt (by simp) (x := y))
    obtain ⟨u, hu⟩ := (D.symm.mfderivToContinuousLinearEquiv (by simp) (q y)).surjective w
    obtain ⟨v, hv⟩ := hsubq y u
    refine ⟨v, ?_⟩
    have h1 := congrArg (fun L => L v) hd
    refine h1.trans ?_
    change mfderiv 𝓘(ℝ, BaseLevelModel) (𝓡 1) D.symm (q y)
      (mfderiv 𝓘(ℝ, MorseModel 2) 𝓘(ℝ, BaseLevelModel) q y v) = w
    rw [hv]
    exact hu
  -- the fibres of `p` are the circle fibres
  have hfib : ∀ z, IsConnected (p ⁻¹' {z}) := by
    intro z
    set b : R.Base := (((D z : R.baseLevelComponent c) : R.BaseLevel) : R.Base) with hbdef
    have hbcirc : b ∈ R.levelCircle c := ⟨(D z).1, (D z).2, rfl⟩
    let ι3 : {y : W.pieceInterior O // F y = 0} → W.Carrier := fun y => y.1.1
    have hind : Topology.IsInducing ι3 :=
      Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
    have himg : ι3 '' (p ⁻¹' {z}) = Subtype.val '' (R.proj ⁻¹' {b}) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨dom y.1, ?_, rfl⟩
        have hqy : q y = D z := by
          have h' : D (p y) = D z := congrArg D hy
          rwa [show D (p y) = q y from D.apply_symm_apply (q y)] at h'
        exact congrArg (fun w : R.baseLevelComponent c => ((w : R.BaseLevel) : R.Base)) hqy
      · rintro ⟨w, hw, rfl⟩
        have hwb : R.proj w = b := hw
        have hwc : R.proj w ∈ R.levelCircle c := by
          rw [hwb]
          exact hbcirc
        refine ⟨⟨⟨w, hmemM w hwc⟩, hFzero w hwc⟩, ?_, rfl⟩
        have hqw : q ⟨⟨w, hmemM w hwc⟩, hFzero w hwc⟩ = D z := Subtype.ext (Subtype.ext hwb)
        change D.symm (q ⟨⟨w, hmemM w hwc⟩, hFzero w hwc⟩) = z
        rw [hqw, D.symm_apply_apply]
    have hconn : IsConnected (Subtype.val '' (R.proj ⁻¹' {b})) :=
      (R.isConnected_proj_fibre b).image _ continuous_subtype_val.continuousOn
    rw [← himg] at hconn
    obtain ⟨_, y, hy, -⟩ := hconn.nonempty
    exact ⟨⟨y, hy⟩, hind.isPreconnected_image.mp hconn.isPreconnected⟩
  obtain ⟨oM⟩ := exists_smoothOrientation_interiorSeam W O
  obtain ⟨e, he, hre, -⟩ := exists_torus_embedding_of_oriented_level interiorSeamModel oM hF hFr hK
    p hp hsub hfib
  have hce : ∀ t, R.roundedFunction (e t) = 0 := fun t => by
    have h : e t ∈ range e := mem_range_self t
    rw [hre] at h
    exact h
  have hlevO : ∀ x : W.pieceInterior O, R.roundedFunction x = 0 → x ∈ range e := fun x hx => by
    rw [hre]
    exact hx
  obtain ⟨δ, hδ, T, hT, hzero, hval⟩ := exists_torusSeam_of_interior_level W O R.roundedFunction 0
    (R.contMDiffOn_roundedFunction.mono fun x hx => hOdom hx.1) e he hce hlevO
    (fun t => R.roundedFunction_regular _ (hMdom (e t)) (hce t))
  refine ⟨δ, hδ, T, fun x hx => ⟨hOV (hT hx).1, hOdom (hT hx).1⟩, ?_, fun p hp => ?_⟩
  · have hfun : (fun t => T.collar (t, 0)) = Subtype.val ∘ e := funext hzero
    rw [hfun, range_comp, hre, himage]
  · rw [hval p hp, zero_add]

end CircleRegion

end GC.GraphManifold.Assembly
