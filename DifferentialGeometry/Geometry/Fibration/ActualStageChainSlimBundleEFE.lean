import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimBaseDomain
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0507Slim
import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE

/-!
# ZSP04, closed side: the slim bundle structure (S0) on the chain (draft 74 §5.2 D, D74-10)

Lane C14-EDP-FDCf (successor of C14-EDP-FDCe; interfaces FROZEN in
`build-logs/resume/state-C14-EDP-FDCe.md`). Blueprint `master207B.tex`, ZSP04 (B:6531–6595):
"over each arc component of `D₃` the slim piece is `I × S²` or `I × T²`". Kernel:
`Topology/Ehresmann/SurfaceIntervalProductEFE.lean`
(`exists_standard_surface_interval_product_EFE`).

* `Gaf02ChainEJA.slimSubmersion_EFE`: `f₃ = π₃ ∘ E` as a `ProperSmoothSurfaceSubmersion_EFE` over
  the closed slim atlas `slimAtlas_ZSP35` (G10). Regions: the marked chart set of `i` cut by the
  (full-norm) GAF47 ratio piece of `i` or by the complement of the (compact) image of `f₃`; over
  the image the region is the ratio piece, where GAF-C's `gaf07_slim_submersion_GAFC` gives the
  submersion of `g_i = κ_i ∘ f₃`; off the image the submersion clause is vacuous.
* `Gaf02ChainEJA.standard_whole_fibre_EFE` (final family): every whole fibre over `Bs` is a
  `StandardWholeSurfaceFibre_EFE` of `ClosureSphere` or `Torus` (GAF-C's
  `gaf07_slim_whole_fibre_standard_GAFC`, SLIM-STD).
* `Gaf02ChainEJA.slim_arc_product_EFE`: over every smooth regular embedded base arc in `Bs`, the
  whole preimage is `S² × I` or `T² × I` (`WholeSurfaceIntervalProduct_EFE`).
* `Gaf02ChainEJA.zsp04_bundle_EFE`: ZSP04's `K₃, D₃ = K₃ ∩ C₃` (G15) with the interval products over
  every ARC of `D₃` and over every proper sub-arc of every LOOP of `D₃` (the global mapping torus
  with its monodromy and E4a–c wait on D74-12; not assumed).

Consumer: `zsp04_bundle_C14Z_EFE`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

section Submersion

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {cadj : ℝ}

/-- The submersion region of the slim chart `i`: the marked chart set of `i` cut by the GAF47
ratio piece of `i` or by the complement of the image of `f₃`. -/
def slimRegion_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (i : P.slim.finite_centres.toFinset) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  markedCondition_BPRE (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
      (gafSlimMarker P.toLocalChartFamily P.zero i) (ρ i.1) (10 ^ 5 * Δ) ∩
    ({w | 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
        (.inr (.inl i)) w ∧
      ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w‖ <
        4 * (10 ^ 5 * Δ) * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
          (.inr (.inl i)) w} ∪ (range C.slimMap_ZSP35)ᶜ)

theorem isOpen_slimRegion_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (i : P.slim.finite_centres.toFinset) : IsOpen (C.slimRegion_EFE i) := by
  refine (isOpen_markedCondition_BPRE _ _ _ _).inter (IsOpen.union ?_ ?_)
  · rw [ofPred_and]
    exact (isOpen_lt continuous_const
      (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous).inter
      (isOpen_lt (continuous_norm.comp
        (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous)
        (continuous_const.mul
          (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous))
  · exact (isCompact_range C.continuous_slimMap_ZSP35).isClosed.isOpen_compl

/-- `f₃ = π₃ ∘ E` is smooth. -/
theorem contMDiff_slimMap_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∞
      C.slimMap_ZSP35 :=
  (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.contDiff.comp_contMDiff
    C.toChain.stage_smooth.2.2

/-- **`f₃` as a proper smooth surface submersion over the closed slim atlas** (draft 74 §5.2 D,
`ProperSmoothSurfaceSubmersion74`; base `Bs = W₃ ∩ R₃`, atlas `slimAtlas_ZSP35`). -/
def slimSubmersion_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    ProperSmoothSurfaceSubmersion_EFE 𝓘(ℝ, E3) X P.slim.finite_centres.toFinset
      C.slimBs_ZSP35 where
  toFun := C.slimMap_ZSP35
  smooth := C.contMDiff_slimMap_EFE
  isOpen_source := C.isOpen_slimSource_ZSP35
  proper Kc hKc _ := (C.toChain.gaf07_proper_G47 2 C.slimBs_ZSP35).2 Kc hKc
  atlas := C.slimAtlas_ZSP35
  region := C.slimRegion_EFE
  isOpen_region := C.isOpen_slimRegion_EFE
  region_cover := by
    intro w hw
    by_cases hwr : w ∈ range C.slimMap_ZSP35
    · obtain ⟨p, rfl⟩ := hwr
      obtain ⟨i, hi⟩ := mem_iUnion.mp hw.2
      obtain ⟨hY, -⟩ := C.toChain.gaf07_slim_submersion_GAFC C.c_two_lt i p hi.1 hi.2
      exact mem_iUnion.mpr ⟨i, (C.slim_param_coord_ZSP35 i hY).1.2, Or.inl hi⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (C.toChain.finalBase_slim_cover_BAS hw.1)
      exact mem_iUnion.mpr ⟨j, hj, Or.inr hwr⟩
  region_piece := by
    intro i w hw
    obtain ⟨hb, hψ⟩ := (C.slimParam_spec_ZSP35 i).2.2 w ⟨hw.2.1, hw.1.1⟩
    refine ⟨_, ⟨hb, ?_⟩, hψ⟩
    change C.slimParam_ZSP35 i _ ∈ gaf07SlimRatio_G47 P.toLocalChartPackets
    rw [hψ]
    exact hw.2.2
  submersion := by
    intro i p hp
    have hratio : 9 / 10 * ρ i.1 <
          blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
            (C.slimMap_ZSP35 p) ∧
        ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
            (C.slimMap_ZSP35 p)‖ <
          4 * (10 ^ 5 * Δ) *
            blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inr (.inl i)) (C.slimMap_ZSP35 p) := by
      rcases hp.1.2 with h | h
      · exact h
      · exact absurd (mem_range_self p) h
    obtain ⟨-, hsurj⟩ :=
      C.toChain.gaf07_slim_submersion_GAFC C.c_two_lt i p hratio.1 hratio.2
    have hfun : (fun y => C.slimAtlas_ZSP35.coord i (C.slimMap_ZSP35 y)) =
        C.toChain.gaf07SlimCoord_GAFC i :=
      funext fun q => Gaf02ChainE.slim_retained_coord_eq_GAFC (P := P) i _
    change Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
      (fun y => C.slimAtlas_ZSP35.coord i (C.slimMap_ZSP35 y)) p)
    rw [hfun]
    exact hsurj

theorem slimSubmersion_toFun_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    C.slimSubmersion_EFE.toFun = C.slimMap_ZSP35 :=
  rfl

theorem slimSubmersion_atlas_EFE (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) :
    C.slimSubmersion_EFE.atlas = C.slimAtlas_ZSP35 :=
  rfl

end Submersion

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Every whole slim fibre over `Bs` is standard** (SLIM-STD on the final family, `K ≥ 5`): it is
a `StandardWholeSurfaceFibre_EFE` of the standard `ClosureSphere` or of the standard `Torus`. -/
theorem standard_whole_fibre_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.slimBs_ZSP35) :
    Nonempty (StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0} w) ∨
      Nonempty (StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus w) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hw.2
  obtain ⟨-, hstd⟩ := C.gaf07_slim_whole_fibre_standard_GAFC hK oM w hw.1 i hi.1 hi.2
  rcases hstd with ⟨f, hf, hfr⟩ | ⟨f, hf, hfr⟩
  · exact Or.inl ⟨⟨f, hf, hfr⟩⟩
  · exact Or.inr ⟨⟨f, hf, hfr⟩⟩

/-- **The slim piece over a base arc is `S² × I` or `T² × I`** (D74-10 on the chain): over every
smooth regular embedded base arc `a` in `Bs` there is a standard whole fibre `F₀` over `a 0` and a
whole interval product `F × [0, 1] → M` over `a` starting at `F₀`. -/
theorem slim_arc_product_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) (a : SmoothEmbeddedBaseArc_EFE C.slimBs_ZSP35) :
    (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
        (a.toFun 0), Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE a F₀)) ∨
      (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus (a.toFun 0),
        Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE a F₀)) := by
  rcases C.standard_whole_fibre_EFE hK (a.mapsTo (left_mem_Icc.mpr zero_le_one)) with h | h
  · obtain ⟨F₀⟩ := h
    exact Or.inl ⟨F₀, exists_standard_surface_interval_product_EFE _ a F₀⟩
  · obtain ⟨F₀⟩ := h
    exact Or.inr ⟨F₀, exists_standard_surface_interval_product_EFE _ a F₀⟩

/-- **ZSP04, the slim bundle structure over `D₃`** (B:6531–6595, draft 74 §5.2 D, D74-10): ZSP04's
`K₃, D₃ = K₃ ∩ C₃` (G15: (SK), compact smooth one-dimensional domains) such that the whole
preimage of every ARC of `D₃` is `S² × I` or `T² × I` (a whole interval product starting at a
standard whole fibre), and the same over every proper sub-arc `s ↦ loop j (t₀ + ℓ s)`, `0 < ℓ < 1`,
of every LOOP of `D₃` (local products; the global mapping torus waits on D74-12). -/
theorem zsp04_bundle_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      (∀ k : Fin D₃.m,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus (D₃.arc k 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE (D₃.arc_EFE k) F₀))) ∧
      ∀ j : Fin D₃.l, ∀ t₀ ℓ : ℝ, ∀ hℓ : ℓ ∈ Ioo (0 : ℝ) 1,
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0}
            ((D₃.loopArc_EFE j t₀ ℓ hℓ).toFun 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE
            (D₃.loopArc_EFE j t₀ ℓ hℓ) F₀)) ∨
        (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus
            ((D₃.loopArc_EFE j t₀ ℓ hℓ).toFun 0),
          Nonempty (WholeSurfaceIntervalProduct_EFE C.slimSubmersion_EFE
            (D₃.loopArc_EFE j t₀ ℓ hℓ) F₀)) := by
  obtain ⟨K₃, D₃, hD, hKs, -⟩ := C.zsp04_D3_ZSP35 hεr
  exact ⟨K₃, D₃, hD, hKs, fun k => C.slim_arc_product_EFE hK (D₃.arc_EFE k),
    fun j t₀ ℓ hℓ => C.slim_arc_product_EFE hK (D₃.loopArc_EFE j t₀ ℓ hℓ)⟩

end Final

end Gaf02ChainEJA

section Consumer

/-- **Consumer: the slim interval products over `D₃` on the final family**, unpacked: for every arc
`k` of ZSP04's `D₃ = K₃ ∩ C₃` the whole preimage `f₃⁻¹(arc k [0, 1])` is the range of a smooth
injective map `F × [0, 1] → M` with injective differential (`F = ClosureSphere` or `Torus`) and
`f₃ ∘ map = arc k ∘ pr₂`. -/
theorem zsp04_bundle_C14Z_EFE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      ∀ k : Fin D₃.m,
        (∃ m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X,
          ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, E3) m z)) ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m = C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) ∨
        (∃ m : Torus × Icc (0 : ℝ) 1 → X,
          ContMDiff (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, E3) ∞ m ∧ Injective m ∧
          (∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, E3) m z)) ∧
          (∀ z, C.slimMap_ZSP35 (m z) = D₃.arc k z.2) ∧
          range m = C.slimMap_ZSP35 ⁻¹' (D₃.arc k '' Icc 0 1)) := by
  obtain ⟨K₃, D₃, hD, -, harc, -⟩ := C.zsp04_bundle_EFE hεr hK
  refine ⟨K₃, D₃, hD, fun k => ?_⟩
  rcases harc k with ⟨F₀, ⟨W⟩⟩ | ⟨F₀, ⟨W⟩⟩
  · exact Or.inl ⟨W.map, W.smooth, W.injective, W.fullRank, W.proj_eq, W.range_eq⟩
  · exact Or.inr ⟨W.map, W.smooth, W.injective, W.fullRank, W.proj_eq, W.range_eq⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
