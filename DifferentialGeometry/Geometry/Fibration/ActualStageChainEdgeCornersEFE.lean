import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRowFacesEFE

/-!
# EDP05: the horizontal face package and the row, group G11

Lane S-EDP-FDC4, group G11. Blueprint `master207B.tex`, EDP05 (B:7040–7090). On the final-family
chain `C : Gaf02ChainEJA …` with ZSP04's `K₃, D₃`, the smooth stage bases `A` and `hcpt`:

* `edge_horizontal_face_EFE` (**the descended defining function of the horizontal face at an
  endpoint `c₀` of `C₂`**, B:7067–7084): an open `N ∋ ι c₀` of the block space and `hh` smooth on
  `N` with `z ∈ M₂ ↔ hh(π₂E z) ≥ 0` over the WHOLE open set `{π₂E ∈ N}` (a neighbourhood of the
  whole disk over `c₀`), `hh(ι c₀) = 0`; `b = hh ∘ ι` has `db(c₀) ≠ 0` on `B₂`, `C₂ ∩ {ι ∈ N} =
  {b ≥ 0}`; the ambient `F = hh ∘ π₂E` is regular at EVERY point of the source over `c₀`; and at
  every such point with `T = 4Δ` the differentials of `F` and `T` are independent (the corner
  `H ∩ V_e`, B:7052, B:7081–7084);
* `edge_disk_in_face_EFE` (B:7053, "every horizontal disk lies in an actual zero or slim
  boundary"): the whole disk over an endpoint of `C₂` lies in ONE face of `∂M₂` — a zero face
  (`∂Z_k` with `f₃ ∉ K₃`) or a slim fibre `f₃⁻¹(y)` over a free end `y` of `D₃` — and in `∂M₂`;
* `edge_edgeSet_frontier_EFE`: `M^edge ∩ ∂M₂ = ⋃_{c ∈ ∂C₂} disk(c)`;
* `edp05_row_EFE`: the row (type_of% conjunction with G9's `edgeRow_EFE`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}


namespace Gaf02ChainE

variable {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **The horizontal face package, raw form** (generic in `M₂`): from the descended defining
function `hh` over `{π₂E ∈ N}` and a base point `f₂ x₁` with `d(hh ∘ ι) ≠ 0`: (1)
`C₂ ∩ {ι ∈ N} = {hh ∘ ι ≥ 0}` (every fibre over `B₂` is a nonempty disk); (2) `F = hh ∘ π₂E` is
regular at every point of the source over `f₂ x₁`; (3) at such a point with `T = 4Δ` the
differentials of `hh ∘ ι ∘ f₂` and of `T` are independent. -/
theorem edge_face_package_raw_EFE (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (hΔ2 : 2 ≤ Δ) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) (M₂ : Set X)
    {N : Set (BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))} (hN : IsOpen N)
    {hh : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) → ℝ}
    (hhN : ContDiffOn ℝ ∞ hh N)
    (hdef : ∀ y : X, Ĉ.edgeBlockProj_EFE y ∈ N → (y ∈ M₂ ↔ 0 ≤ hh (Ĉ.edgeBlockProj_EFE y)))
    (hne : ∀ cc : Ĉ.edgeBaseOpens_EFE, ∃ w : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE w = cc ∧
      Ĉ.edgeHeight_EFE w ≤ 4 * Δ)
    (x₁ : Ĉ.edgeSource_EFE) (hx₁N : Ĉ.edgeBlockProj_EFE x₁.1 ∈ N) :
    let _ := A.edgeChartedSpace1
    mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x₁) ≠ 0 →
    (Ĉ.edgeProj_EFE '' {x : Ĉ.edgeSource_EFE | (x : X) ∈ M₂ ∧ Ĉ.edgeHeight_EFE x ≤ 4 * Δ} ∩
        (Ĉ.edgeValB_EFE ⁻¹' N) =
      {cc | cc ∈ Ĉ.edgeValB_EFE ⁻¹' N ∧ 0 ≤ hh (Ĉ.edgeValB_EFE cc)}) ∧
    ∀ x : Ĉ.edgeSource_EFE, Ĉ.edgeProj_EFE x = Ĉ.edgeProj_EFE x₁ →
      mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => hh (Ĉ.edgeBlockProj_EFE y)) x.1 ≠ 0 ∧
      (Ĉ.edgeHeight_EFE x = 4 * Δ →
        Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
          (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
            ((fun cc => hh (Ĉ.edgeValB_EFE cc)) ∘ Ĉ.edgeProj_EFE) x v,
            mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) Ĉ.edgeHeight_EFE x v))) := by
  intro _ hdb
  refine ⟨?_, fun x hx => ?_⟩
  · ext cc
    constructor
    · rintro ⟨⟨w, ⟨hwM, -⟩, rfl⟩, hcc⟩
      exact ⟨hcc, (hdef w.1 hcc).mp hwM⟩
    · rintro ⟨hcc, hnn⟩
      obtain ⟨w, hw1, hw2⟩ := hne cc
      have h1 : Ĉ.edgeBlockProj_EFE w.1 = Ĉ.edgeValB_EFE cc := by
        rw [← Ĉ.edgeValB_edgeProj_EFE w, hw1]
      have hwM : (w : X) ∈ M₂ := (hdef w.1 (h1 ▸ hcc)).mpr (h1 ▸ hnn)
      exact ⟨⟨w, ⟨hwM, hw2⟩, hw1⟩, hcc⟩
  · have hblk : Ĉ.edgeBlockProj_EFE x.1 = Ĉ.edgeBlockProj_EFE x₁.1 := by
      rw [← Ĉ.edgeValB_edgeProj_EFE x, ← Ĉ.edgeValB_edgeProj_EFE x₁, hx]
    have hxN : Ĉ.edgeBlockProj_EFE x.1 ∈ N := by
      rw [hblk]
      exact hx₁N
    obtain ⟨hbsm, hFcomp⟩ := Ĉ.edge_descended_mfderiv_EFE A hN hhN
      (F := fun y => hh (Ĉ.edgeBlockProj_EFE y)) (fun _ => rfl) x hxN
    have hdb' : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc))
        (Ĉ.edgeProj_EFE x) ≠ 0 := by
      rw [hx]
      exact hdb
    refine ⟨?_, fun hT => ?_⟩
    · rw [hFcomp]
      intro hc0
      apply hdb'
      ext w
      obtain ⟨v, hv⟩ := Ĉ.edge_proj_submersion_EFE A x w
      have h1 : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (Ĉ.edgeValB_EFE cc)) (Ĉ.edgeProj_EFE x)
          (mfderiv 𝓘(ℝ, E3) (𝓡 1) Ĉ.edgeProj_EFE x v) = 0 := congrArg (fun Lm => Lm v) hc0
      rw [hv] at h1
      exact h1
    · exact Ĉ.edge_corner_independence_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 x hT _
        (hbsm.mdifferentiableAt (by simp)) hdb'

end Gaf02ChainE

namespace Gaf02ChainEJA

section Corners

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **Regular descended defining function at a point of `∂M₂`**: at a source point `x₁` with
`x₁ ∈ ∂M₂` there are `N ∋ π₂E x₁` and `hh` smooth on `N` with `z ∈ M₂ ↔ hh(π₂E z) ≥ 0` over
`{π₂E ∈ N}`, `hh(π₂E x₁) = 0` and `d(hh ∘ ι)(f₂ x₁) ≠ 0` on `B₂`. -/
theorem edge_regular_data_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (x₁ : C.edgeSource_EFE) (hx₁F : (x₁ : X) ∈ frontier (edgeM2_EFE C K₃)) :
    let _ := A.edgeChartedSpace1
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.edgeBlockProj_EFE x₁.1 ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiffOn ℝ ∞ hh N ∧ hh (C.edgeBlockProj_EFE x₁.1) = 0 ∧
        (∀ y : X, C.edgeBlockProj_EFE y ∈ N →
          (y ∈ edgeM2_EFE C K₃ ↔ 0 ≤ hh (C.edgeBlockProj_EFE y))) ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (C.edgeValB_EFE cc)) (C.edgeProj_EFE x₁) ≠ 0 := by
  intro _
  have hdat := C.edge_face_data_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hx₁F
  obtain ⟨N, hN, hx₁N, hh, hhN, hdef, F, hF, hFne, hFeq⟩ := hdat.2
  have hzero := eq_zero_of_mem_frontier_of_descended_EFE
    C.toGaf02ChainE.continuous_edgeBlockProj_EFE hN hhN.continuousOn hdef hx₁F hdat.1 hx₁N
  exact ⟨N, hN, hx₁N, hh, hhN, hzero, hdef,
    (C.toGaf02ChainE.edge_regular_face_base_EFE A _ hN hhN hdef hFeq x₁ hx₁N hFne hzero).1⟩

/-- **The descended defining function of the horizontal face at an endpoint of `C₂`** (see the
module docstring). -/
theorem edge_horizontal_face_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}))
    {c₀ : C.edgeBaseOpens_EFE} (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃)) :
    let _ := A.edgeChartedSpace1
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.edgeValB_EFE c₀ ∈ N ∧
      ∃ hh : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → ℝ,
        ContDiffOn ℝ ∞ hh N ∧ hh (C.edgeValB_EFE c₀) = 0 ∧
        (∀ y : X, C.edgeBlockProj_EFE y ∈ N →
          (y ∈ edgeM2_EFE C K₃ ↔ 0 ≤ hh (C.edgeBlockProj_EFE y))) ∧
        mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun cc => hh (C.edgeValB_EFE cc)) c₀ ≠ 0 ∧
        (edgeC2_EFE C K₃) ∩ (C.edgeValB_EFE ⁻¹' N) =
          {cc | cc ∈ C.edgeValB_EFE ⁻¹' N ∧ 0 ≤ hh (C.edgeValB_EFE cc)} ∧
        ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ →
          mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => hh (C.edgeBlockProj_EFE y)) x.1 ≠ 0 ∧
          (C.edgeHeight_EFE x = 4 * Δ →
            Function.Surjective (fun v : TangentSpace 𝓘(ℝ, E3) (x : X) =>
              (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
                ((fun cc => hh (C.edgeValB_EFE cc)) ∘ C.edgeProj_EFE) x v,
                mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) C.edgeHeight_EFE x v))) := by
  intro _
  have hproj := C.edgeProj_contMDiff_EFE A
  have hdisk : ∀ cc : C.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X, Continuous φ ∧
      range φ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ} := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 cc
    exact ⟨φ, hφ.isEmbedding.continuous, hr⟩
  have hne : ∀ cc : C.edgeBaseOpens_EFE, ∃ w : C.edgeSource_EFE, C.edgeProj_EFE w = cc ∧
      C.edgeHeight_EFE w ≤ 4 * Δ := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := hdisk cc
    obtain ⟨-, y, hy⟩ := isPreconnected_range_closedCell_EFE hφ
    rw [hr] at hy
    obtain ⟨w, ⟨hw1, hw2⟩, -⟩ := hy
    exact ⟨w, hw1, hw2⟩
  obtain ⟨x₁, hx₁c, hx₁T, hx₁F⟩ := C.toGaf02ChainE.edgeBase_frontier_facePoint_EFE hΔ2 hdisk
    hproj.continuous hcpt hc₀
  subst hx₁c
  obtain ⟨N, hN, hx₁N, hh, hhN, hzero, hdef, hdb⟩ :=
    C.edge_regular_data_EFE A hεr K₃ D₃ hD hKs hKF hDreg hdD x₁ hx₁F
  have hpk := C.toGaf02ChainE.edge_face_package_raw_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 _ hN hhN
    hdef hne x₁ hx₁N hdb
  have hvx : C.edgeValB_EFE (C.edgeProj_EFE x₁) = C.edgeBlockProj_EFE x₁.1 :=
    C.toGaf02ChainE.edgeValB_edgeProj_EFE x₁
  exact ⟨N, hN, hvx ▸ hx₁N, hh, hhN, hvx ▸ hzero, hdef, hdb, hpk.1, hpk.2⟩

/-- **EDP05, "every horizontal disk lies in an actual zero or slim boundary"** (B:7053): the
whole disk over an endpoint `c₀` of `C₂` lies in `∂M₂` and in ONE face of it: a zero face
(`∂Z_k` with `f₃ ∉ K₃`) or a slim fibre `f₃⁻¹(y)` over a free end `y` of `D₃`. -/
theorem edge_disk_in_face_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ}))
    {c₀ : C.edgeBaseOpens_EFE} (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃)) :
    let _ := A.edgeChartedSpace1
    ((∃ k : P.zero.finite_centres.toFinset, ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ →
        C.edgeHeight_EFE x ≤ 4 * Δ →
        (x : X) ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∧
          C.slimMap_ZSP35 x.1 ∉ K₃.carrier) ∨
      (∃ y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
        (∃ k : Fin D₃.m, y = D₃.arc k 0 ∨ y = D₃.arc k 1) ∧
        y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35) ∧
        ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ → C.edgeHeight_EFE x ≤ 4 * Δ →
          C.slimMap_ZSP35 x.1 = y)) ∧
    ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ → C.edgeHeight_EFE x ≤ 4 * Δ →
      (x : X) ∈ frontier (edgeM2_EFE C K₃) := by
  intro _
  have hproj := C.edgeProj_contMDiff_EFE A
  have hdisk : ∀ cc : C.edgeBaseOpens_EFE, ∃ φ : ClosedCell 2 → X, Continuous φ ∧
      range φ = Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = cc ∧
        C.edgeHeight_EFE x ≤ 4 * Δ} := fun cc => by
    obtain ⟨φ, hφ, hr⟩ := C.toGaf02ChainE.edgeProj_disk_EFE hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc
      hγc1 hβc1 cc
    exact ⟨φ, hφ.isEmbedding.continuous, hr⟩
  obtain ⟨x₁, hx₁c, hx₁T, hx₁F⟩ := C.toGaf02ChainE.edgeBase_frontier_facePoint_EFE hΔ2 hdisk
    hproj.continuous hcpt hc₀
  have hblk : ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ →
      C.edgeBlockProj_EFE x.1 = C.edgeBlockProj_EFE x₁.1 := fun x hx => by
    rw [← C.toGaf02ChainE.edgeValB_edgeProj_EFE x, ← C.toGaf02ChainE.edgeValB_edgeProj_EFE x₁,
      hx, hx₁c]
  have hsl : ∀ z : X, C.slimMap_ZSP35 z = (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.edgeBlockProj_EFE z) := fun z =>
    (gafStageQ_two_starProjection_one_EFE P.toLocalChartFamily P.zero _).symm
  have hslx : ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ →
      C.slimMap_ZSP35 x.1 = C.slimMap_ZSP35 x₁.1 := fun x hx => by
    rw [hsl, hsl, hblk x hx]
  have hfr : ∀ x : C.edgeSource_EFE, C.edgeProj_EFE x = c₀ → C.edgeHeight_EFE x ≤ 4 * Δ →
      (x : X) ∈ frontier (edgeM2_EFE C K₃) := fun x hx hxT => by
    have hH := C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs
      hKF hDreg hdD hcpt
    have : (x : X) ∈ Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ ∧
        C.edgeProj_EFE x ∈ frontier (edgeC2_EFE C K₃)} := ⟨x, ⟨hxT, hx ▸ hc₀⟩, rfl⟩
    rw [← hH] at this
    exact this.1
  refine ⟨?_, hfr⟩
  rcases C.frontier_cutM2_cases_EFE hεr K₃ D₃ hD hKs hKF hDreg hdD hx₁F with
    ⟨k, hk, hK⟩ | ⟨y, hy, hyC, hxy⟩
  · left
    refine ⟨k, fun x hx hxT => ⟨?_, ?_⟩⟩
    · exact (C.toGaf02ChainE.edge_zero_fibre_subset_M2_EFE hεr K₃.carrier k hk hK
        (hblk x hx)).1
    · rw [hslx x hx]
      exact hK
  · right
    exact ⟨y, hy, hyC, fun x hx hxT => (hslx x hx).trans hxy⟩

/-- **`M^edge ∩ ∂M₂ = ⋃_{c ∈ ∂C₂} disk(c)`** (EDP05's `H`, in the form `g3` of the junction facts;
`∂M₂ ⊆ M₂` and `X₂ = {T ≤ 4Δ}`). -/
theorem edge_edgeSet_frontier_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    let _ := A.edgeChartedSpace1
    frontier (edgeM2_EFE C K₃) ∩
        Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ} =
      ⋃ c ∈ frontier (edgeC2_EFE C K₃),
        Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x = c ∧
          C.edgeHeight_EFE x ≤ 4 * Δ} := by
  intro _
  rw [C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
    hDreg hdD hcpt]
  ext y
  simp only [mem_iUnion, mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, ⟨hxT, hxf⟩, rfl⟩
    exact ⟨C.edgeProj_EFE x, hxf, x, ⟨rfl, hxT⟩, rfl⟩
  · rintro ⟨c, hcf, x, ⟨hxc, hxT⟩, rfl⟩
    exact ⟨x, ⟨hxT, hxc ▸ hcf⟩, rfl⟩

/-- **The whole EDP05 row on the actual chain** (blueprint B:7040–7090): (1) `C₂` compact smooth
domain with defining functions, saturation `M₂ ∩ X₂ = f₂⁻¹(C₂) ∩ X₂` (`edgeCompactDomain_EFE`);
(2) the proper whole-disk bundle data over `B₂` with rank two (`edgeBundleData_EFE`); (3) the faces
(EF): horizontal `∂M₂ ∩ X₂ = f₂⁻¹(∂C₂)` and vertical `M₂ ∩ ∂X₂` (`edge_frontier_H_EFE`,
`edge_vertical_V_EFE`, `edge_edgeSet_frontier_EFE`); (4) every horizontal disk lies in one zero or
slim face (`edge_disk_in_face_EFE`); (5) at every endpoint of `C₂` the descended defining function
`b ∘ f₂` with `db ≠ 0` and, at `H ∩ V_e`, independent from `dT` (`edge_horizontal_face_EFE`). -/
theorem edp05_row_EFE
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hεr : εr < 1 / 2) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (K₃ D₃ : SmoothCompactOneDomain_BCF C.slimBs_ZSP35)
    (hD : D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35)
    (hKs : C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
      Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
    (hKF : Disjoint (K₃.carrier \
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35)
    (hDreg : D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)))
    (hdD : D₃.carrier \ Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
      ((K₃.carrier \ Subtype.val '' interior
            (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
          Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
        (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
          C.slimFacePoints_ZSP35))
    (hcpt : IsCompact (edgeM2_EFE C K₃ ∩
      Subtype.val '' {x : C.edgeSource_EFE | C.edgeHeight_EFE x ≤ 4 * Δ})) :
    type_of% (C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edgeBundleData_EFE A hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1) ∧
    type_of% (C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edge_vertical_V_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD
      hKs hKF hDreg hdD hcpt) ∧
    type_of% (C.edge_edgeSet_frontier_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃
      hD hKs hKF hDreg hdD hcpt) ∧
    (∀ (c₀ : C.edgeBaseOpens_EFE) (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃)),
      type_of% (C.edge_disk_in_face_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃
        hD hKs hKF hDreg hdD hcpt hc₀)) ∧
    (∀ (c₀ : C.edgeBaseOpens_EFE) (hc₀ : c₀ ∈ frontier (edgeC2_EFE C K₃)),
      type_of% (C.edge_horizontal_face_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃
        D₃ hD hKs hKF hDreg hdD hcpt hc₀)) :=
  ⟨C.edgeCompactDomain_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edgeBundleData_EFE A hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1,
    C.edge_frontier_H_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edge_vertical_V_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs hKF
      hDreg hdD hcpt,
    C.edge_edgeSet_frontier_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃ hD hKs
      hKF hDreg hdD hcpt,
    fun _ hc₀ => C.edge_disk_in_face_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃ D₃
      hD hKs hKF hDreg hdD hcpt hc₀,
    fun _ hc₀ => C.edge_horizontal_face_EFE A hεr hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1 K₃
      D₃ hD hKs hKF hDreg hdD hcpt hc₀⟩

end Corners

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
