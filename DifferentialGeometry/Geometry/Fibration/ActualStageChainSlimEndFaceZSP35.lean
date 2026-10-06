import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimFullRowZSP35
import DifferentialGeometry.Topology.Ehresmann.ArcEndDefiningFunctionZSP35

/-!
# ZSP05, free ends: smooth faces of the slim piece and of `M₂`, with whole-tube collars

Lane S-ZSP04, group G20. Blueprint `master207B.tex`, ZSP05 (B:6597–6640): "At a different boundary
component of `M^slim`, the boundary lies inside `int_M M₁` and is a full regular fibre. Its product
collar cuts off one side and leaves the other as the smooth boundary of `M₂`."

For the `K₃, D₃` of ZSP04 and every FREE arc end `y` of `D₃` (`y ∈ int C₃`, i.e. the new faces of
`M₂`): an open `U ⊆ M₁` containing the WHOLE fibre `f₃⁻¹(y)`, missing the fibres over the other
arc ends, and a function `h` smooth on `U` with onto differential at every point of `U` such that

* `{h = 0} ∩ U = f₃⁻¹(y)` and this fibre is a standard `S²` / `T²` (embedded closed surface),
* `M^slim ∩ U = {h ≤ 0} ∩ U` (the piece side),
* `M₂ ∩ U = {h ≥ 0} ∩ U` for `M₂ = M₁ ∖ int_{M₁} M^slim` (the smooth side of `M₂`).

These are the fields `endNear / endFn_smooth / endFn_regular / endFn_level / endFn_eq` of draft
74's `SlimPiecesV2` in `X`-form. Kernel: `Topology/Ehresmann/ArcEndDefiningFunctionZSP35.lean`.
`free_end_M2_ZSP35` is the pure side computation; `slim_free_end_tube_ZSP35` the tube inside `M₁`;
`zsp05_free_end_faces_ZSP35` the row; consumer `zsp05_free_end_faces_C14Z_ZSP35`.
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

section Side

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} [I.Boundaryless] {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M]

/-- **The smooth side of `M₂` at a regular face**: if `U ⊆ M₁` is open, `h` is smooth on `U` with
onto differential and `S ∩ U = {h ≤ 0} ∩ U`, then `(M₁ ∖ int_{M₁} S) ∩ U = {h ≥ 0} ∩ U`. -/
theorem free_end_M2_ZSP35 {M₁ S U : Set M} {h : M → ℝ} (hU : IsOpen U) (hUM : U ⊆ M₁)
    (hh : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ h U) (hs : ∀ x ∈ U, Surjective (mfderiv I 𝓘(ℝ, ℝ) h x))
    (hS : S ∩ U = {x | x ∈ U ∧ h x ≤ 0}) :
    (M₁ \ Subtype.val '' interior (Subtype.val ⁻¹' S : Set M₁)) ∩ U = {x | x ∈ U ∧ 0 ≤ h x} := by
  ext x
  constructor
  · rintro ⟨⟨hxM, hxr⟩, hxU⟩
    refine ⟨hxU, ?_⟩
    by_contra hneg
    have hlt : h x < 0 := lt_of_not_ge hneg
    apply hxr
    have hOo : IsOpen (U ∩ h ⁻¹' Iio 0) :=
      hh.continuousOn.isOpen_inter_preimage hU (isOpen_Iio (a := (0 : ℝ)))
    refine mem_image_interior_preimage_val_iff.mpr ⟨hxM, U ∩ h ⁻¹' Iio 0, hOo, ⟨hxU, hlt⟩, ?_⟩
    rintro y ⟨⟨hyU, hy⟩, -⟩
    have : y ∈ {x | x ∈ U ∧ h x ≤ 0} := ⟨hyU, (le_of_lt hy)⟩
    rw [← hS] at this
    exact this.1
  · rintro ⟨hxU, hx0⟩
    refine ⟨⟨hUM hxU, fun hxr => ?_⟩, hxU⟩
    obtain ⟨-, O, hO, hxO, hOM⟩ := mem_image_interior_preimage_val_iff.mp hxr
    have hOS : ∀ y, y ∈ O → y ∈ U → h y ≤ 0 := by
      intro y hyO hyU
      have : y ∈ S ∩ U := ⟨hOM ⟨hyO, hUM hyU⟩, hyU⟩
      rw [hS] at this
      exact this.2
    rcases hx0.lt_or_eq with hpos | hzero
    · exact absurd (hOS x hxO hxU) (not_le.mpr hpos)
    · have hne : mfderiv I 𝓘(ℝ, ℝ) h x ≠ 0 := by
        intro h0
        let w : ℝ := 1
        obtain ⟨v, hv⟩ := hs x hxU w
        rw [h0, zero_apply] at hv
        have h01 : (0 : ℝ) = 1 := hv
        exact zero_ne_one h01
      have hcl := mem_closure_pos_of_mfderiv_ne_zero_ZSP35 (I := I) hne
      rw [mem_closure_iff_nhds] at hcl
      obtain ⟨y, hyN, hyp⟩ := hcl (O ∩ U) (inter_mem (hO.mem_nhds hxO) (hU.mem_nhds hxU))
      have := hOS y hyN.1 hyN.2
      have hyp' : h x < h y := hyp
      linarith

end Side

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

namespace Gaf02ChainEJA

section Final

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The tube over a free arc end, inside `M₁`**: the kernel tube
(`exists_arc_end_tube_ZSP35`) for the proper submersion `f₃`, with the extra open set `G ∋ y`,
`G ∩ Bs ⊆ C₃`, so that the tube lies in `M₁` (saturation `M₁ ∩ f₃⁻¹(Bs) = f₃⁻¹(C₃) ∩ f₃⁻¹(Bs)`). -/
theorem slim_free_end_tube_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hy : ∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1)
    (hyC : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) :
    ∃ (U : Set X) (h : X → ℝ), IsOpen U ∧ C.slimMap_ZSP35 ⁻¹' {y} ⊆ U ∧
      U ⊆ (interior C.zeroUnion_ZSP35)ᶜ ∧
      Disjoint U (C.slimMap_ZSP35 ⁻¹'
        ((⋃ k : Fin D₃.m, ({D₃.arc k 0, D₃.arc k 1} :
          Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) \ {y})) ∧
      ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ h U ∧
      (∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) h x)) ∧
      {x | x ∈ U ∧ h x = 0} = C.slimMap_ZSP35 ⁻¹' {y} ∧
      U ∩ C.slimMap_ZSP35 ⁻¹' D₃.carrier = {x | x ∈ U ∧ h x ≤ 0} := by
  obtain ⟨hsat, -⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨-, G, hG, hyG, hGC⟩ := mem_image_interior_preimage_val_iff.mp hyC
  obtain ⟨U, h, hUo, hfU, hUB, hUE, hh, hsurj, hlev, hside⟩ :=
    exists_arc_end_tube_ZSP35 (P := C.slimSubmersion_EFE) D₃ hy hG hyG
  refine ⟨U, h, hUo, hfU, ?_, hUE, hh, hsurj, hlev, hside⟩
  intro x hx
  have hx' := hUB hx
  have hxB : C.slimMap_ZSP35 x ∈ C.slimBs_ZSP35 := hx'.2
  have hxC : C.slimMap_ZSP35 x ∈ C.slimC3_ZSP35 := hGC ⟨hx'.1, hx'.2⟩
  have : x ∈ C.slimMap_ZSP35 ⁻¹' C.slimBs_ZSP35 ∩ C.slimMap_ZSP35 ⁻¹' C.slimC3_ZSP35 :=
    ⟨hxB, hxC⟩
  rw [← hsat] at this
  exact this.1

/-- **ZSP05, the free faces of `M^slim` and `M₂` with whole-tube collars** (B:6597–6640): for the
`K₃, D₃ = K₃ ∩ C₃` of ZSP04 and every free arc end `y ∈ int C₃` of `D₃`: an open `U ⊆ M₁` over a
neighbourhood of `y` containing the whole fibre `f₃⁻¹(y)` (a standard `S²` or `T²`) and missing the
fibres over the other arc ends, and a regular defining function `h` on `U` (onto differential) with
`{h = 0} ∩ U = f₃⁻¹(y)`, `M^slim ∩ U = {h ≤ 0} ∩ U` and
`(M₁ ∖ int_{M₁} M^slim) ∩ U = {h ≥ 0} ∩ U`. -/
theorem zsp05_free_end_faces_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.slimPiece_ZSP35 K₃.carrier = C.slimMap_ZSP35 ⁻¹' D₃.carrier ∧
      ∀ (k : Fin D₃.m) (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (y = D₃.arc k 0 ∨ y = D₃.arc k 1) →
        y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) →
        (∃ (U : Set X) (h : X → ℝ), IsOpen U ∧ C.slimMap_ZSP35 ⁻¹' {y} ⊆ U ∧
          U ⊆ (interior C.zeroUnion_ZSP35)ᶜ ∧
          Disjoint U (C.slimMap_ZSP35 ⁻¹'
            ((⋃ k : Fin D₃.m, ({D₃.arc k 0, D₃.arc k 1} :
              Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))) \ {y})) ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ h U ∧
          (∀ x ∈ U, Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) h x)) ∧
          {x | x ∈ U ∧ h x = 0} = C.slimMap_ZSP35 ⁻¹' {y} ∧
          C.slimPiece_ZSP35 K₃.carrier ∩ U = {x | x ∈ U ∧ h x ≤ 0} ∧
          ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
            (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
              Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∩ U = {x | x ∈ U ∧ 0 ≤ h x}) ∧
        ((∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0} y,
            range F₀.emb = C.slimMap_ZSP35 ⁻¹' {y}) ∨
          (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus y,
            range F₀.emb = C.slimMap_ZSP35 ⁻¹' {y})) := by
  obtain ⟨K₃, D₃, hD, hKs, hKF, hDreg, -⟩ := C.zsp04_D3_ZSP35 hεr
  obtain ⟨hSD, -⟩ := C.slim_piece_facts_ZSP35 hεr K₃ D₃ hD hKs hKF hDreg
  refine ⟨K₃, D₃, hD, hSD, fun k y hyk hyC => ⟨?_, ?_⟩⟩
  · obtain ⟨U, h, hUo, hfU, hUM, hUE, hh, hsurj, hlev, hside⟩ :=
      C.slim_free_end_tube_ZSP35 hεr D₃ ⟨k, hyk⟩ hyC
    have hS : C.slimPiece_ZSP35 K₃.carrier ∩ U = {x | x ∈ U ∧ h x ≤ 0} := by
      rw [hSD, inter_comm]
      exact hside
    exact ⟨U, h, hUo, hfU, hUM, hUE, hh, hsurj, hlev, hS,
      free_end_M2_ZSP35 hUo hUM hh hsurj hS⟩
  · have hyD : y ∈ D₃.carrier := by
      rw [D₃.carrier_eq]
      rcases hyk with rfl | rfl
      · exact Or.inl (mem_iUnion.mpr ⟨k, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
      · exact Or.inl (mem_iUnion.mpr ⟨k, 1, ⟨zero_le_one, le_rfl⟩, rfl⟩)
    rcases C.standard_whole_fibre_EFE hK (D₃.subset_base hyD) with h | h
    · obtain ⟨F₀⟩ := h
      exact Or.inl ⟨F₀, F₀.range_eq⟩
    · obtain ⟨F₀⟩ := h
      exact Or.inr ⟨F₀, F₀.range_eq⟩

end Final

end Gaf02ChainEJA

section Consumer

/-- **Consumer: `M₂` is a smooth domain along the new faces** on the final family: for the
`K₃, D₃` of ZSP04, every point `x` of the whole fibre over a free arc end `y ∈ int C₃` of `D₃`
has an open neighbourhood `U` and a function `h`, smooth on `U` with `dh ≠ 0` at the zero level
`f₃⁻¹(y) ∩ U`, such that `M₂ ∩ U = {h ≥ 0} ∩ U`; and that fibre is a standard `S²` or `T²`. -/
theorem zsp05_free_end_faces_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (hK : 5 ≤ K) :
    ∃ K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      ∀ (k : Fin D₃.m) (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)),
        (y = D₃.arc k 0 ∨ y = D₃.arc k 1) →
        y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) →
        (∀ x ∈ C.slimMap_ZSP35 ⁻¹' {y}, ∃ (U : Set X) (h : X → ℝ), IsOpen U ∧ x ∈ U ∧
          ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ h U ∧
          (∀ z ∈ U, h z = 0 → mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) h z ≠ 0) ∧
          ((interior C.zeroUnion_ZSP35)ᶜ \ Subtype.val '' interior
            (Subtype.val ⁻¹' C.slimPiece_ZSP35 K₃.carrier :
              Set ↥(interior C.zeroUnion_ZSP35)ᶜ)) ∩ U = {z | z ∈ U ∧ 0 ≤ h z}) ∧
        ((∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE (𝓡 2) ClosureSphere.{0} y,
            range F₀.emb = C.slimMap_ZSP35 ⁻¹' {y}) ∨
          (∃ F₀ : StandardWholeSurfaceFibre_EFE C.slimSubmersion_EFE torusModel Torus y,
            range F₀.emb = C.slimMap_ZSP35 ⁻¹' {y})) := by
  obtain ⟨K₃, D₃, hD, -, hall⟩ := C.zsp05_free_end_faces_ZSP35 hεr hK
  refine ⟨K₃, D₃, hD, fun k y hyk hyC => ?_⟩
  obtain ⟨⟨U, h, hUo, hfU, -, -, hh, hsurj, -, -, hM₂⟩, hfib⟩ := hall k y hyk hyC
  refine ⟨fun x hx => ⟨U, h, hUo, hfU hx, hh, fun z hz _ => ?_, hM₂⟩, hfib⟩
  intro h0
  let w : ℝ := 1
  obtain ⟨v, hv⟩ := hsurj z hz w
  rw [h0, zero_apply] at hv
  have h01 : (0 : ℝ) = 1 := hv
  exact zero_ne_one h01

end Consumer

end DifferentialGeometry.Geometry.Collapse
