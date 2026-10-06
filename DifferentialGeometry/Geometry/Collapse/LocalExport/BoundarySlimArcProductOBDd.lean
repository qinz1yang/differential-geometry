import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySlimStandardFibreOBDd

/-!
# The slim interval product over a base arc, in `W` (lane S-BD2d, suffix `_OBDd`), group G10b

Lane O-BD1 (by S-BD2d), hlift, `SlimCutPieces74`. Over `W°` (interior atlas) the kernel
`exists_standard_surface_interval_product_EFE` applies to the slim stage
(`exists_slimSubmersion_OBDd`) and a standard whole fibre at `γ 0` (`exists_standardFibre_OBDd`);
carried to `W` by the inclusion `val : W° → W` (a local diffeomorphism) the product is a smooth
injective map `F × [0, 1] → W` with injective differential, over `γ`, onto the whole preimage
`X₃ ∩ f₃⁻¹(γ [0, 1])` of the arc and onto the whole end fibres.

* `BoundaryGaf02ChainE.image_val_preimage_slimF_OBDd`: `val '' (f₃⁻¹ S) = X₃ ∩ f₃⁻¹ S` over `B₃`;
* `BoundaryGaf02ChainE.exists_arcProduct_OBDd`: the product over ANY smooth embedded base arc
  `γ` of `B₃`, sphere or torus (the shape of `SphereArcExit74.F` / `TorusArcExit74.F`).
-/


set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    θ W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- Over `B₃` the `val`-image of a preimage of `f₃ ∘ val` is `X₃ ∩ f₃⁻¹ S`. -/
theorem image_val_preimage_slimF_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    {Sset : Set (BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))}
    (hS : Sset ⊆ dec.bases.base 2) :
    Subtype.val '' (C.slimF_OBDd ⁻¹' Sset : Set (W.pieceInterior ⊤)) =
      dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' Sset := by
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨C.mem_source_of_stageMap_mem_base_OBDd dec (hS hx), hx⟩
  · rintro ⟨hp, hpS⟩
    exact ⟨⟨p, C.source_two_subset_pieceInterior_OBDd dec hp⟩, hpS, rfl⟩

include C in
/-- **The interval product carried from `W°` to `W`** (generic fibre model). -/
theorem arcProduct_inW_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x)
    (γ : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)) {EF HF : Type} [NormedAddCommGroup EF]
    [NormedSpace ℝ EF] [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} {F : Type}
    [TopologicalSpace F] [ChartedSpace HF F]
    {F₀ : StandardWholeSurfaceFibre_EFE P IF F (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE P γ F₀) :
    ∃ m : F × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff (IF.prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
      (∀ z, Injective (mfderiv (IF.prod (𝓡∂ 1)) W.model m z)) ∧
      (∀ z, C.toChain.stageMap 2 (m z) = γ.toFun z.2) ∧
      range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ.toFun '' Icc 0 1) ∧
      ∀ b, range (fun z => m (z, iccEnd b)) =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ.toFun (iccEnd b)} := by
  have hloc := isLocalDiffeomorph_pieceInterior_val W ⊤
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  have hPf : P.toFun = C.slimF_OBDd := funext hP
  have hγB : ∀ t ∈ Icc (0 : ℝ) 1, γ.toFun t ∈ dec.bases.base 2 := fun t ht => γ.mapsTo ht
  refine ⟨fun z => (Wp.map z).1, hloc.contMDiff.comp Wp.smooth,
    Subtype.val_injective.comp Wp.injective, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · exact injective_mfderiv_comp_OBDd (hloc.contMDiff.mdifferentiableAt hn)
      (Wp.smooth.mdifferentiableAt hn) (injective_mfderiv_of_isLocalDiffeomorphAt_OBDd (hloc _))
      (Wp.fullRank z)
  · have h1 := Wp.proj_eq z
    rw [hP] at h1
    exact h1
  · have h1 : range (fun z => (Wp.map z).1) = Subtype.val '' range Wp.map := by
      rw [← range_comp]
      rfl
    rw [h1, Wp.range_eq, hPf, C.image_val_preimage_slimF_OBDd dec]
    rintro _ ⟨t, ht, rfl⟩
    exact hγB t ht
  · intro b
    have h1 : range (fun z => (Wp.map (z, iccEnd b)).1) =
        Subtype.val '' range (fun z => Wp.map (z, iccEnd b)) := by
      rw [← range_comp]
      rfl
    rw [h1]
    have hmem : γ.toFun (iccEnd b) ∈ dec.bases.base 2 := hγB _ (iccEnd b).2
    have h2 : range (fun z => Wp.map (z, iccEnd b)) = P.toFun ⁻¹' {γ.toFun (iccEnd b)} := by
      cases b
      · have h3 : (fun z => Wp.map (z, iccEnd false)) = F₀.emb :=
          funext fun x => Wp.start_eq x
        rw [h3]
        exact F₀.range_eq
      · exact Wp.end_range
    rw [h2, hPf, C.image_val_preimage_slimF_OBDd dec (singleton_subset_iff.2 hmem)]

include C in
/-- **The sphere / torus interval product over a base arc, in `W`.** -/
theorem exists_arcProduct_OBDd (dec : BoundaryActualDecompositionV2b C.toChain)
    (P : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) (W.pieceInterior ⊤)
      (dec.bases.base 2) (dec.bases.base 2))
    (hP : ∀ x, P.toFun x = C.slimF_OBDd x)
    (γ : SmoothEmbeddedBaseArc_EFE (dec.bases.base 2)) :
    (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
      (∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model m z)) ∧
      (∀ z, C.toChain.stageMap 2 (m z) = γ.toFun z.2) ∧
      range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ.toFun '' Icc 0 1) ∧
      ∀ b, range (fun z => m (z, iccEnd b)) =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ.toFun (iccEnd b)}) ∨
    (∃ m : Torus × Icc (0 : ℝ) 1 → W.Carrier,
      ContMDiff (torusModel.prod (𝓡∂ 1)) W.model ∞ m ∧ Injective m ∧
      (∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model m z)) ∧
      (∀ z, C.toChain.stageMap 2 (m z) = γ.toFun z.2) ∧
      range m = dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' (γ.toFun '' Icc 0 1) ∧
      ∀ b, range (fun z => m (z, iccEnd b)) =
        dec.bases.source 2 ∩ C.toChain.stageMap 2 ⁻¹' {γ.toFun (iccEnd b)}) := by
  have hγ0 : γ.toFun 0 ∈ dec.bases.base 2 := γ.mapsTo (left_mem_Icc.2 zero_le_one)
  rcases C.exists_standardFibre_OBDd dec P hP hγ0 with hF | hF
  · obtain ⟨F₀⟩ := hF
    obtain ⟨Wp⟩ := exists_standard_surface_interval_product_EFE P γ F₀
    exact Or.inl (C.arcProduct_inW_OBDd dec P hP γ Wp)
  · obtain ⟨F₀⟩ := hF
    obtain ⟨Wp⟩ := exists_standard_surface_interval_product_EFE P γ F₀
    exact Or.inr (C.arcProduct_inW_OBDd dec P hP γ Wp)

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
