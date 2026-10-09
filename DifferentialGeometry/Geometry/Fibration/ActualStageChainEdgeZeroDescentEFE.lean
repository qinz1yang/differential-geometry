import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroBaseDomains
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdgeBaseExactEDP23
import DifferentialGeometry.Geometry.Fibration.ActualStageChainCutChoice

/-!
# EDP05, zero faces: the descended defining identity on the edge stage

Lane S-EDP-FDC2, group G4 (EDP05, zero-face half; draft 74 D74-11 / D74-14 layers 1–2).
Blueprint `master207B.tex`, EDP05 (B:7040–7090): "Near a horizontal face, an ambient defining
function for `M₂` descends to a smooth function `b` on the edge base. For a zero face it is the
retained ratio in (ZF)." The binding of ZSP03's kernel (`zsp03_local_domain_ZSP35`, lane
C14-ZSP35d) to the EDGE stage:

* `gafStageTags_two_subset_one_EFE`, `gafStageQ_two_starProjection_one_EFE`: `Q₃ ≤ Q₂`, so
  `π₃E = π_{2,3} ∘ π₂E` (EDP05's "its constant `π₂E` makes `π₃E` constant");
* `Gaf02ChainE.zero_face_pointwise_gen_EFE`, `zero_face_pointwise_EFE`: ZSP03 pointwise (not only
  on images) for any stage `st`: near the stage image of `q ∈ ∂Z_k`, `y ∈ M₁ ↔ b_k(π_stE y) ≥ 0`
  for every `y` with `π_stE y ∈ N` (whole fibres lie in the defining neighbourhood);
* `Gaf02ChainE.frontier_zspDomain_subset_M1_EFE`;
* `Gaf02ChainE.edge_zero_fibre_subset_M2_EFE`: the whole `π₂E`-fibre through a zero-face point
  `q` with `f₃ q ∉ K` lies in `∂Z_k` and in `M₂ = M₁ ∖ int_{M₁} M^slim(K)` (face saturation);
* `Gaf02ChainE.edge_zero_face_M2_local_EFE`: for a closed slim base set `K` and such `q`, an open
  `N ∋ π₂E q` with `y ∈ M₂ ↔ b_k(π₂E y) ≥ 0` for all `y` with `π₂E y ∈ N` (the descended
  defining identity of `M₂` along the zero face).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

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
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The third stage target lies inside the second: `Q₃ ≤ Q₂` (slim and zero blocks inside slim,
edge and zero blocks), as tag sets. -/
theorem gafStageTags_two_subset_one_EFE :
    gafStageTags L Z 2 ⊆ gafStageTags L Z 1 := by
  intro t ht
  have h3 : t ∈ cgpQ3Tags L Z := ht
  have h3' : cgpInQ3 L Z t = true := (Finset.mem_filter.mp h3).2
  show t ∈ cgpQ2Tags L Z
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ t, ?_⟩
  rcases t with _ | _ | _ | _ | _ <;> simp_all [cgpInQ2, cgpInQ3]

/-- **`π₃E = π_{2,3} ∘ π₂E`**: projecting the second-stage image to the third target gives the
third-stage image (`Q₃ ≤ Q₂`). -/
theorem gafStageQ_two_starProjection_one_EFE (y : BlockSpace (fun _ : CGPTag L Z => ℝ²)) :
    (gafStageQ L Z 2).starProjection ((gafStageQ L Z 1).starProjection y) =
      (gafStageQ L Z 2).starProjection y := by
  classical
  rw [gafStageQ_starProjection, gafStageQ_starProjection]
  have h := blockRestrict_comp (V := fun _ : CGPTag L Z => ℝ²) (gafStageTags L Z 1)
    (gafStageTags L Z 2)
  rw [Finset.inter_eq_right.mpr (gafStageTags_two_subset_one_EFE L Z)] at h
  exact congrArg (fun A => A y) h


section Zero

namespace Gaf02ChainE

variable {Lmax τ γ vs ζ Λz : ℝ} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- **ZSP03, pointwise, for a stage map `f`** (generic form of `zsp03_local_domain_ZSP35` without
the base set `B`): if the whole fibre of the continuous `f` through the face point `q ∈ ∂Z_k`
lies in `∂Z_k` and `b_k ∘ f` is the zero ratio, then there is an open `N ∋ f q` such that a
point `y` with `f y ∈ N` lies in `M₁ = (int Z)ᶜ` exactly when `b_k(f y) ≥ 0`. -/
theorem zero_face_pointwise_gen_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hf : Continuous f)
    (k : P.zero.finite_centres.toFinset) {q : X}
    (hfib : ∀ y, f y = f q → y ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))
    (hbase : ∀ y, zspBaseFun_ZSP35 P k (f y) =
      ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      f q ∈ N ∧ ∀ y : X, f y ∈ N →
        (y ∈ (interior Ĉ.zeroUnion_ZSP35)ᶜ ↔ 0 ≤ zspBaseFun_ZSP35 P k (f y)) := by
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := fun k =>
    (Ĉ.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, -⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
    hclk (fun k k' hkk => Ĉ.zsp02_disjoint_ZSP35 hεr hkk)
  have hfr := (Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  -- the defining neighbourhood of the face, away from the other zero domains
  obtain ⟨Vn, hVn⟩ : ∃ Vn : Set X, Vn = O ∩ ⋂ l ∈ ({k}ᶜ : Set P.zero.finite_centres.toFinset),
      (zspDomain_ZSP35 P.toLocalChartFamily P.zero l Ĉ.E)ᶜ := ⟨_, rfl⟩
  have hVo : IsOpen Vn := by
    rw [hVn]
    exact hO.inter ((toFinite _).isOpen_biInter fun l _ =>
      (Ĉ.zsp02_domain_ZSP35 hεr l).1.isClosed.isOpen_compl)
  have hfibV : ∀ y, f y = f q → y ∈ Vn := by
    intro y hy
    have hyF := hfib y hy
    rw [hVn]
    refine ⟨hFO (hfr ▸ hyF), mem_iInter₂.mpr fun l hl => ?_⟩
    exact Set.disjoint_left.mp (Ĉ.zsp02_disjoint_ZSP35 hεr (Ne.symm (show l ≠ k from hl)))
      ((hclk k).frontier_subset hyF)
  have hGc : IsClosed (f '' Vnᶜ) := (hVo.isClosed_compl.isCompact.image hf).isClosed
  refine ⟨(f '' Vnᶜ)ᶜ, hGc.isOpen_compl, fun ⟨y, hy, hyq⟩ => hy (hfibV y hyq), ?_⟩
  intro y hyN
  have hyV : y ∈ Vn := by
    by_contra hyV
    exact hyN ⟨y, hyV, rfl⟩
  -- the open set `{r_k < 0} ∩ O` lies in `Z_k`
  have hrc : ContinuousOn (fun z => ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) O := fun z hz =>
    ((hOprop z hz).2.1.continuousAt).continuousWithinAt
  have hopen := hrc.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  rw [hVn] at hyV
  constructor
  · intro hyM
    by_contra hneg
    push Not at hneg
    have hry : ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 < 0 := by
      rw [← hbase y]
      exact hneg
    have hyint : y ∈ interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := by
      rw [mem_interior]
      exact ⟨_, fun z hz => ((hOprop z hz.1).2.2).mpr (le_of_lt hz.2), hopen, hyV.1, hry⟩
    exact hyM (interior_mono (Ĉ.zspDomain_subset_zeroUnion_ZSP35 k) hyint)
  · intro hpos hyi
    have hry : 0 ≤ ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 := by
      rw [← hbase y]
      exact hpos
    obtain ⟨l, hl⟩ := mem_iUnion.mp (interior_subset hyi)
    have hlk : l = k := by
      by_contra hlk
      exact (mem_iInter₂.mp hyV.2 l hlk) hl
    rw [hlk] at hl
    have hyZ := ((hOprop y hyV.1).2.2).mp hl
    have hr0 : ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 = 0 := le_antisymm hyZ hry
    have hv := (hOprop y hyV.1).1
    have hv0 : 0 < (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
    have hyF : y ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E := by
      refine ⟨by nlinarith, ?_⟩
      rw [sub_eq_zero, div_eq_iff hv0.ne'] at hr0
      exact hr0
    exact hfrk k (hfr ▸ hyF) hyi

/-- **ZSP03 at the stage `st`, pointwise** (whole fibres in the defining neighbourhood): near the
stage image of a zero-face point `q ∈ ∂Z_k`, a point `y` with `π_stE y ∈ N` lies in `M₁ = (int Z)ᶜ`
exactly when `b_k(π_stE y) ≥ 0`. -/
theorem zero_face_pointwise_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (st : Fin 3) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.toChain.E q) ∈ N ∧
      ∀ y : X, (gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.toChain.E y) ∈ N →
        (y ∈ (interior Ĉ.zeroUnion_ZSP35)ᶜ ↔ 0 ≤ zspBaseFun_ZSP35 P k
          ((gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.toChain.E y))) :=
  Ĉ.zero_face_pointwise_gen_EFE hεr
    ((gafStageQ P.toLocalChartFamily P.zero st).starProjection.continuous.comp
      Ĉ.toChain.stage_smooth.2.2.continuous) k
    (fun _ hy => Ĉ.zsp03_whole_fibre_ZSP35 hεr st k hq hy)
    (Ĉ.toChain.zero_base_function_ZSP35 st k).1

/-- **Frontier points of `Z_k` lie in `M₁`** (they are outside `int Z`). -/
theorem frontier_zspDomain_subset_M1_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) :
    frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ⊆ Ĉ.cutM1_R74 := by
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := fun k =>
    (Ĉ.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, -⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
    hclk (fun k k' hkk => Ĉ.zsp02_disjoint_ZSP35 hεr hkk)
  exact hfrk k

/-- **The whole second-stage fibre through a zero-face point of `M₂`-type lies in `M₂`**: if
`q ∈ ∂Z_k` and `f₃(q) ∉ K` (the slim base set), then every `y` with `π₂E y = π₂E q` lies in
`∂Z_k` and in `M₂ = M₁ ∖ int_{M₁} M^slim(K)` (its `f₃`-image `π_{2,3}(π₂E q) = f₃ q` is outside
`K`, hence `y ∉ M^slim`). -/
theorem edge_zero_fibre_subset_M2_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)))
    (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))
    (hK : Ĉ.slimMap_ZSP35 q ∉ Kb) {y : X}
    (hy : (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y) =
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q)) :
    y ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧ y ∈ Ĉ.cutM2_R74 Kb := by
  have hyF : y ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) :=
    Ĉ.zsp03_whole_fibre_ZSP35 hεr 1 k hq hy
  refine ⟨hyF, Ĉ.frontier_zspDomain_subset_M1_EFE hεr k hyF, ?_⟩
  rintro ⟨z, hz, hzy⟩
  have hzs' : z ∈ (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 Kb : Set Ĉ.cutM1_R74) := interior_subset hz
  have hzs : (z : X) ∈ Ĉ.slimPiece_ZSP35 Kb := hzs'
  have h3 : Ĉ.slimMap_ZSP35 y ∈ Kb := by
    rw [← hzy]
    exact hzs.1
  apply hK
  have : Ĉ.slimMap_ZSP35 y = Ĉ.slimMap_ZSP35 q := by
    change (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (Ĉ.toChain.E y) =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (Ĉ.toChain.E q)
    rw [← gafStageQ_two_starProjection_one_EFE, hy, gafStageQ_two_starProjection_one_EFE]
  rwa [this] at h3

/-- **`M₂ = M₁` near a zero face whose `f₃`-image is outside `K`**: for a closed slim base set `K`,
`q ∈ ∂Z_k` with `f₃ q ∉ K` there is an open `N ∋ π₂E q` such that `y` with `π₂E y ∈ N` lies in
`M₂ = M₁ ∖ int_{M₁} M^slim(K)` exactly when `b_k(π₂E y) ≥ 0` (EDP05's local description of `M₂`
along a zero face, pointwise on whole fibres). -/
theorem edge_zero_face_M2_local_EFE (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (hKc : IsClosed Kb) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))
    (hK : Ĉ.slimMap_ZSP35 q ∉ Kb) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q) ∈ N ∧
      ∀ y : X, (gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y) ∈ N →
        (y ∈ Ĉ.cutM2_R74 Kb ↔ 0 ≤ zspBaseFun_ZSP35 P k
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y))) := by
  obtain ⟨N, hNo, hqN, hN⟩ := Ĉ.zero_face_pointwise_EFE hεr 1 k hq
  have hQ3 : ∀ w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²),
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection w) =
      (gafStageQ P.toLocalChartFamily P.zero 2).starProjection w :=
    gafStageQ_two_starProjection_one_EFE P.toLocalChartFamily P.zero
  have hQc : Continuous (gafStageQ P.toLocalChartFamily P.zero 2).starProjection :=
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.continuous
  refine ⟨N ∩ (gafStageQ P.toLocalChartFamily P.zero 2).starProjection ⁻¹' Kbᶜ,
    hNo.inter (hKc.isOpen_compl.preimage hQc), ⟨hqN, ?_⟩, fun y hy => ?_⟩
  · change (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E q)) ∉ Kb
    rw [hQ3]
    exact hK
  · have hyK : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (Ĉ.toChain.E y) ∉ Kb := by
      have h : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          ((gafStageQ P.toLocalChartFamily P.zero 1).starProjection (Ĉ.toChain.E y)) ∉ Kb :=
        hy.2
      rwa [hQ3] at h
    rw [← hN y hy.1]
    constructor
    · exact fun h => h.1
    · intro hM1
      refine ⟨hM1, ?_⟩
      rintro ⟨z, hz, hzy⟩
      have hzs' : z ∈ (Subtype.val ⁻¹' Ĉ.slimPiece_ZSP35 Kb : Set Ĉ.cutM1_R74) :=
        interior_subset hz
      have hzs : (z : X) ∈ Ĉ.slimPiece_ZSP35 Kb := hzs'
      apply hyK
      rw [← hzy]
      exact hzs.1

end Gaf02ChainE

end Zero

end DifferentialGeometry.Geometry.Collapse
