import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimEFE
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeRimRelIntJN74
import DifferentialGeometry.Topology.Manifold.LinearChartMaps74

/-!
# Draft 74, the rim base is smooth (field `rimBase_smooth` of `JunctionRimFacts74`), chain level

Lane S-JUNCTIONS (by S-JUNCTIONS3), G14 (suffix `_JN74`). On the final-family chain, with no section
of a submersion and no boundary model (the chain space has model `𝓘(ℝ, E3)`):

* `exists_edge_functional_JN74`: a linear functional `ℓ` of the block space with
  `d(ℓ ∘ ι)(c) ≠ 0` at a given point `c` of the edge base (`ι` is a smooth immersion);
* `rim_chart_JN74`: at a rim point `x₀ ∈ X₁`, `(T − 4Δ, ℓ ∘ π₂E)` descends to the circle base
  on the WHOLE preimage of a patch (`circle_descent_EFE`) and is a local chart `Φ` of `B₁` at
  `π₁E x₀` (rank two: `edge_corner_rank_raw_EFE`; `edp06_base_chart_EFE`);
* `rim_local_chart_JN74`: tube lemma (properness of the edge projection on sublevels,
  `edge_proper_EFE`) + EDP06's equality `rim = whole circle fibre`: there is an open `U₀ ∋ π₂E x₀`
  such that every rim point `y` over `U₀` lies in `X₁`, over the chart domain, with
  `Φ (π₁E y) = (0, ℓ (ι (π₂E y)))`;
* **`rimBase_contMDiffOn_JN74`**: a map `rb` of the edge base into the circle base sending the rim
  over a point of `S₂` (a rim point in `X₁` over each point of `S₂`) to its circle-base image is
  smooth on `S₂`: locally `rb = Φ.symm ∘ (c ↦ (0, ℓ (ι c)))`.
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

/-- **A linear functional with `d(ℓ ∘ ι) ≠ 0` on the edge base at a given point** (`ι` is a smooth
immersion of the base into the block space). -/
theorem exists_edge_functional_JN74 (Ĉ : Gaf02ChainE L Kj Ξ Γ S eg c cw)
    (A : SmoothStageBasesOn74 Ĉ.toChain) (cc : Ĉ.edgeBaseOpens_EFE) :
    let _ := A.edgeChartedSpace1
    ∃ ℓ : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) →L[ℝ] ℝ,
      mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun c' => ℓ (Ĉ.edgeValB_EFE c')) cc ≠ 0 := by
  intro _
  have hA := A.edge_isManifold1
  have hinj := hA.2.2 cc.1
  have hmd : MDifferentiableAt (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily
      L.zero => ℝ²)) (Subtype.val : Ĉ.toChain.finalBase_BAS 1 → _) cc.1 :=
    (hA.2.1.mdifferentiable (by simp)) cc.1
  have hval : mfderiv (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      Ĉ.edgeValB_EFE cc = mfderiv (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily
        L.zero => ℝ²)) (Subtype.val : Ĉ.toChain.finalBase_BAS 1 → _) cc.1 :=
    mfderiv_comp_subtype_val_R74 (I := 𝓡 1) Ĉ.edgeBaseOpens_EFE (f := Subtype.val)
      (g := Ĉ.edgeValB_EFE) (fun _ => rfl) cc hmd
  have hinj' : Function.Injective (mfderiv (𝓡 1)
      𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²)) Ĉ.edgeValB_EFE cc) := by
    rw [hval]
    exact hinj
  obtain ⟨v', hv'⟩ : ∃ v : EuclideanSpace ℝ (Fin 1), v ≠ 0 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  let v : TangentSpace (𝓡 1) cc := v'
  have hv : v ≠ 0 := hv'
  let w : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) :=
    mfderiv (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
      Ĉ.edgeValB_EFE cc v
  have hw' : w ≠ 0 := fun h0 => hv (hinj' (h0.trans (map_zero _).symm))
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ w (norm_ne_zero_iff.mpr hw')
  refine ⟨ℓ, fun h0 => ?_⟩
  have hcomp : mfderiv (𝓡 1) 𝓘(ℝ, ℝ) (fun c' => ℓ (Ĉ.edgeValB_EFE c')) cc =
      ℓ.comp (mfderiv (𝓡 1) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
        Ĉ.edgeValB_EFE cc) := by
    have h2 : mfderiv 𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
        𝓘(ℝ, ℝ) ℓ (Ĉ.edgeValB_EFE cc) = ℓ := by
      rw [mfderiv_eq_fderiv]
      exact ℓ.fderiv
    have h1 := mfderiv_comp (I := 𝓡 1) cc (ℓ.mdifferentiableAt (x := Ĉ.edgeValB_EFE cc))
      (((Ĉ.contMDiff_edgeValB_EFE A) cc).mdifferentiableAt (by simp))
    refine h1.trans ?_
    exact congrArg (fun M' : BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²) →L[ℝ]
      ℝ => M'.comp (mfderiv (𝓡 1)
        𝓘(ℝ, BlockSpace (fun _ : CGPTag L.toLocalChartFamily L.zero => ℝ²))
        Ĉ.edgeValB_EFE cc)) h2
  have h6 := hcomp.symm.trans h0
  have h5 : ℓ w = 0 := by
    have := congrArg (fun L : TangentSpace (𝓡 1) cc →L[ℝ] TangentSpace 𝓘(ℝ, ℝ)
      (ℓ (Ĉ.edgeValB_EFE cc)) => L v) h6
    exact this
  rw [hℓ] at h5
  exact hw' (norm_eq_zero.mp (by exact_mod_cast h5))

end Gaf02ChainE

namespace Gaf02ChainEJA

section RimChart

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The rim chart at a rim point over a point of the edge base** (D74-14 layer 2, with the
ambient linear functional `ℓ` in place of EDP05's face function): at a rim point `x₀ ∈ X₁` the
pair `(T − 4Δ, ℓ ∘ π₂E)` descends to the circle base on the WHOLE preimage of a patch and is a
local chart `Φ` of `B₁` at `π₁E x₀`. -/
theorem rim_chart_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (x₀ : C.edgeSource_EFE) (hT : C.edgeHeight_EFE x₀ = 4 * Δ)
    (hX₁ : (x₀ : X) ∈ C.circleDomain_EFE) :
    let _ := A.edgeChartedSpace1
    let _ := A.circleChartedSpace
    ∃ (ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ)
      (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ × ℝ) C.circleBaseOpens_EFE (ℝ × ℝ) ∞),
      C.circleProj_EFE ⟨x₀.1, hX₁⟩ ∈ Φ.source ∧
      ∀ y : C.circleDomain_EFE, C.circleProj_EFE y ∈ Φ.source →
        (y : X) ∈ C.edgeSource_EFE ∧
        Φ (C.circleProj_EFE y) = (C.edgeHeightGlobal_EFE y.1 - 4 * Δ,
          ℓ (C.edgeBlockProj_EFE y.1)) := by
  intro _ _
  obtain ⟨ℓ, hℓ⟩ := C.toGaf02ChainE.exists_edge_functional_JN74 A (C.edgeProj_EFE x₀)
  have hN : IsOpen (Set.univ : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero =>
    ℝ²))) := isOpen_univ
  have hhN : ContDiffOn ℝ ∞ ℓ (Set.univ : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily
    P.zero => ℝ²))) := ℓ.contDiff.contDiffOn
  have hfib := C.edge_rim_fibre_in_source_EFE hβ hd hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
    x₀ hT hX₁
  obtain ⟨V, hxV, Tb, hb', hTb, hhb, hdes, hTc, hbc⟩ := C.circle_descent_EFE A hN hhN ⟨x₀.1, hX₁⟩
    (mem_univ _) hfib
  have hrank := C.toGaf02ChainE.edge_corner_rank_raw_EFE A hΔ2 hc hϑ hε0 hε hγc hγc1 hβc1 hN hhN
    x₀ (mem_univ _) hT hℓ
  obtain ⟨Φ, hΦx, hΦV, hΦ⟩ := C.edp06_base_chart_EFE A hN hhN ⟨x₀.1, hX₁⟩ (mem_univ _) V hxV Tb
    hb' hTb hhb hdes hrank
  refine ⟨ℓ, Φ, hΦx, fun y hy => ?_⟩
  obtain ⟨hysrc, -, h1, h2⟩ := hdes y (hΦV hy)
  refine ⟨hysrc, ?_⟩
  rw [hΦ _ hy]
  exact Prod.ext h1.symm h2.symm


/-- **The rim near a rim point of `X₁` is a smooth family of whole circle fibres**: with the chart
`Φ` and the functional `ℓ` of `rim_chart_JN74`, there is an open `U₀ ∋ π₂E x₀` of the edge base such
that every rim point `y` over `U₀` lies in `X₁`, over the chart domain, and
`Φ (π₁E y) = (0, ℓ (ι (π₂E y)))` (tube lemma for the proper edge projection and EDP06's equality
of the rim with the whole circle fibre). -/
theorem rim_local_chart_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (x₀ : C.edgeSource_EFE) (hT : C.edgeHeight_EFE x₀ = 4 * Δ)
    (hX₁ : (x₀ : X) ∈ C.circleDomain_EFE) :
    let _ := A.edgeChartedSpace1
    let _ := A.circleChartedSpace
    ∃ (ℓ : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) →L[ℝ] ℝ)
      (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ²) 𝓘(ℝ, ℝ × ℝ) C.circleBaseOpens_EFE (ℝ × ℝ) ∞)
      (U₀ : Set C.edgeBaseOpens_EFE), IsOpen U₀ ∧ C.edgeProj_EFE x₀ ∈ U₀ ∧
      C.circleProj_EFE ⟨x₀.1, hX₁⟩ ∈ Φ.source ∧
      ∀ y : C.edgeSource_EFE, C.edgeProj_EFE y ∈ U₀ → C.edgeHeight_EFE y = 4 * Δ →
        ∃ hy : (y : X) ∈ C.circleDomain_EFE, C.circleProj_EFE ⟨y.1, hy⟩ ∈ Φ.source ∧
          Φ (C.circleProj_EFE ⟨y.1, hy⟩) = (0, ℓ (C.edgeValB_EFE (C.edgeProj_EFE y))) := by
  intro _ _
  obtain ⟨ℓ, Φ, hΦx, hΦ⟩ := C.rim_chart_JN74 A hβ hd hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
    x₀ hT hX₁
  have hπ0 : ∀ w, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection w = w :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  -- the open set of points over the chart domain
  let O₁ : Set X := Subtype.val '' (C.circleProj_EFE ⁻¹' Φ.source)
  have hO₁ : IsOpen O₁ :=
    C.circleDomain_EFE.isOpen.isOpenMap_subtype_val _
      (Φ.open_source.preimage C.circleProj_continuous_EFE)
  have hfibre : ∀ y : C.edgeSource_EFE, C.edgeProj_EFE y = C.edgeProj_EFE x₀ →
      C.edgeHeight_EFE y = 4 * Δ → (y : X) ∈ O₁ := by
    intro y hy1 hy2
    have hq1 : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E y.1) =
        (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x₀.1) :=
      congrArg (fun v : C.edgeBaseOpens_EFE =>
        ((v : C.toChain.finalBase_BAS 1) : BlockSpace (fun _ : CGPTag P.toLocalChartFamily
          P.zero => ℝ²))) hy1
    have hX₁' : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x₀.1) ∈
        C.toChain.circleBase_BAS := by
      have h := C.circleDomain_eq_EFE hβ hd
      have hq : (x₀ : X) ∈ (C.circleDomain_EFE : Set X) := hX₁
      rw [h] at hq
      exact hq
    have hrim := C.edp06_rim_eq_whole_fibre_EFE hβ hd hΔ2 hc hϑ hε0 hε hμ hτ hσc hb hγc hγc1 hβc1
      (q₀ := x₀.1) (C.toGaf02ChainE.edgeSource_mem_EFE x₀.2).2 hT hX₁'
    have hy : (y : X) ∈ {x | (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
          (C.toChain.E x) = (gafStageQ P.toLocalChartFamily P.zero 1).starProjection
            (C.toChain.E x₀.1) ∧ EuclideanSpace.proj (0 : Fin 2) (gafHeightVector
          P.toLocalChartFamily P.zero (C.toChain.E x)) / C.toChain.scale x = 4 * Δ} :=
      ⟨hq1, hy2⟩
    rw [hrim] at hy
    have hy0 : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y.1) =
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x₀.1) := hy
    have hE : C.toChain.E y.1 = C.toChain.E x₀.1 := by rwa [hπ0, hπ0] at hy0
    have hyX : (y : X) ∈ C.circleDomain_EFE := by
      obtain ⟨h1, h2⟩ := C.circleDomain_mem_EFE hX₁
      refine C.mem_circleDomain_of_EFE ?_ ?_
      · rw [hE]
        exact h1
      · rw [hE]
        exact h2
    refine ⟨⟨y.1, hyX⟩, ?_, rfl⟩
    have : C.circleProj_EFE ⟨y.1, hyX⟩ = C.circleProj_EFE ⟨x₀.1, hX₁⟩ :=
      Subtype.ext (Subtype.ext (by
        change (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y.1) =
          (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x₀.1)
        exact hy0))
    rw [mem_preimage, this]
    exact hΦx
  -- tube lemma
  have : LocallyCompactSpace C.edgeBaseOpens_EFE :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 1)) C.edgeBaseOpens_EFE
  obtain ⟨Kc, hKcc, hKc⟩ := exists_compact_mem_nhds (C.edgeProj_EFE x₀)
  have hQ := C.toGaf02ChainE.edge_proper_EFE hΔ2 A Kc hKcc
  have hZ : IsCompact (Subtype.val '' {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ Kc ∧
      C.edgeHeight_EFE x ≤ 4 * Δ} ∩ ({x | C.edgeHeightGlobal_EFE x = 4 * Δ} ∩ O₁ᶜ)) :=
    hQ.inter_right ((isClosed_eq C.toGaf02ChainE.continuous_edgeHeightGlobal_EFE
      continuous_const).inter hO₁.isClosed_compl)
  have hW : IsCompact (C.edgeBlockProj_EFE '' (Subtype.val '' {x : C.edgeSource_EFE |
      C.edgeProj_EFE x ∈ Kc ∧ C.edgeHeight_EFE x ≤ 4 * Δ} ∩
        ({x | C.edgeHeightGlobal_EFE x = 4 * Δ} ∩ O₁ᶜ))) :=
    hZ.image C.toGaf02ChainE.continuous_edgeBlockProj_EFE
  refine ⟨ℓ, Φ, interior Kc ∩ C.edgeValB_EFE ⁻¹' (C.edgeBlockProj_EFE '' (Subtype.val ''
    {x : C.edgeSource_EFE | C.edgeProj_EFE x ∈ Kc ∧ C.edgeHeight_EFE x ≤ 4 * Δ} ∩
      ({x | C.edgeHeightGlobal_EFE x = 4 * Δ} ∩ O₁ᶜ)))ᶜ, ?_, ⟨mem_interior_iff_mem_nhds.mpr hKc,
    ?_⟩, hΦx, ?_⟩
  · exact isOpen_interior.inter (hW.isClosed.isOpen_compl.preimage
      (C.contMDiff_edgeValB_EFE A).continuous)
  · rintro ⟨z, ⟨⟨z', ⟨hz'K, hz'T⟩, rfl⟩, hzTT, hzO⟩, hzw⟩
    refine hzO (hfibre z' ?_ hzTT)
    apply Subtype.ext
    apply Subtype.ext
    have h1 := hzw
    rw [← C.edgeValB_edgeProj_EFE z', C.edgeValB_edgeProj_EFE x₀] at h1
    change (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E z'.1) =
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (C.toChain.E x₀.1)
    exact h1
  · rintro y ⟨hyK, hyW⟩ hyT
    have hyO : (y : X) ∈ O₁ := by
      by_contra hnot
      apply hyW
      refine ⟨y.1, ⟨⟨y, ⟨interior_subset hyK, hyT.le⟩, rfl⟩, hyT, hnot⟩, ?_⟩
      exact (C.edgeValB_edgeProj_EFE y).symm
    obtain ⟨w, hw, hwy⟩ := hyO
    have hy : (y : X) ∈ C.circleDomain_EFE := hwy ▸ w.2
    have hyw : C.circleProj_EFE ⟨y.1, hy⟩ = C.circleProj_EFE w :=
      congrArg C.circleProj_EFE (Subtype.ext hwy.symm)
    have hsrc : C.circleProj_EFE ⟨y.1, hy⟩ ∈ Φ.source := by
      rw [hyw]
      exact hw
    have hΦy := (hΦ ⟨y.1, hy⟩ hsrc).2
    refine ⟨hy, hsrc, ?_⟩
    refine hΦy.trans ?_
    have hT' : C.edgeHeightGlobal_EFE y.1 = 4 * Δ := hyT
    rw [hT', sub_self, ← C.edgeValB_edgeProj_EFE y]


/-- **The rim base is smooth** (chain level, field `rimBase_smooth` of `JunctionRimFacts74` before
transport): a map `rb` of the edge base into the circle base which sends every rim point over a
point of `S₂` (and in `X₁`) to its circle-base image, is smooth on `S₂`, provided over every point
of `S₂` there is a rim point in `X₁`. Locally `rb = Φ.symm ∘ (c ↦ (0, ℓ (ι c)))` for the rim chart
`Φ` (`rim_local_chart_JN74`). -/
theorem rimBase_contMDiffOn_JN74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (A : SmoothStageBasesOn74 C.toChain)
    (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10) (hΔ2 : 2 ≤ Δ)
    (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000)
    (S₂ : Set C.edgeBaseOpens_EFE) (rb : C.edgeBaseOpens_EFE → C.circleBaseOpens_EFE)
    (hrb : ∀ y : C.edgeSource_EFE, C.edgeProj_EFE y ∈ S₂ → C.edgeHeight_EFE y = 4 * Δ →
      ∀ hy : (y : X) ∈ C.circleDomain_EFE, C.circleProj_EFE ⟨y.1, hy⟩ = rb (C.edgeProj_EFE y))
    (hX₁ : ∀ cc ∈ S₂, ∃ y : C.edgeSource_EFE, C.edgeProj_EFE y = cc ∧
      C.edgeHeight_EFE y = 4 * Δ ∧ (y : X) ∈ C.circleDomain_EFE) :
    let _ := A.edgeChartedSpace1
    let _ := A.circleChartedSpace
    ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ²) ∞ rb S₂ := by
  intro _ _
  refine contMDiffOn_of_locally_contMDiffOn fun cc hcc => ?_
  obtain ⟨x₀, hx₀c, hx₀T, hx₀X⟩ := hX₁ cc hcc
  obtain ⟨ℓ, Φ, U₀, hU₀, hx₀U, hΦx, hlocal⟩ := C.rim_local_chart_JN74 A hβ hd hΔ2 hc hϑ hε0 hε hμ
    hτ hσc hb hγc hγc1 hβc1 x₀ hx₀T hx₀X
  refine ⟨U₀, hU₀, hx₀c ▸ hx₀U, ?_⟩
  have hval := C.contMDiff_edgeValB_EFE A
  have hg : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun c' : C.edgeBaseOpens_EFE => ((0 : ℝ), ℓ (C.edgeValB_EFE c'))) :=
    contMDiff_const.prodMk_space (ℓ.contDiff.contMDiff.comp hval)
  have hmaps : ∀ c' ∈ S₂ ∩ U₀, ∃ y : C.edgeSource_EFE, C.edgeProj_EFE y = c' ∧
      C.edgeHeight_EFE y = 4 * Δ ∧ ∃ hy : (y : X) ∈ C.circleDomain_EFE,
        C.circleProj_EFE ⟨y.1, hy⟩ ∈ Φ.source ∧
          Φ (C.circleProj_EFE ⟨y.1, hy⟩) = (0, ℓ (C.edgeValB_EFE c')) := by
    intro c' hc'
    obtain ⟨y, hyc, hyT, -⟩ := hX₁ c' hc'.1
    obtain ⟨hy, hys, hyΦ⟩ := hlocal y (hyc ▸ hc'.2) hyT
    exact ⟨y, hyc, hyT, hy, hys, hyc ▸ hyΦ⟩
  have hrbeq : ∀ c' ∈ S₂ ∩ U₀, rb c' = Φ.symm (0, ℓ (C.edgeValB_EFE c')) ∧
      (0, ℓ (C.edgeValB_EFE c')) ∈ Φ.target := by
    intro c' hc'
    obtain ⟨y, hyc, hyT, hy, hys, hyΦ⟩ := hmaps c' hc'
    have hrbc : rb c' = C.circleProj_EFE ⟨y.1, hy⟩ := by
      rw [← hyc]
      exact (hrb y (hyc ▸ hc'.1) hyT hy).symm
    rw [hrbc]
    refine ⟨?_, ?_⟩
    · rw [← hyΦ]
      exact (Φ.left_inv hys).symm
    · rw [← hyΦ]
      exact Φ.map_source hys
  have hsymm : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ²) ∞ Φ.symm Φ.target := Φ.symm.contMDiffOn
  have hcomp : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ²) ∞
      (fun c' => Φ.symm (0, ℓ (C.edgeValB_EFE c'))) (S₂ ∩ U₀) :=
    hsymm.comp hg.contMDiffOn (fun c' hc' => (hrbeq c' hc').2)
  exact hcomp.congr fun c' hc' => (hrbeq c' hc').1

end RimChart

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
