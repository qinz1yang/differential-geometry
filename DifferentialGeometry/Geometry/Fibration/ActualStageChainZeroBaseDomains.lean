import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimPieceFaces
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle

/-!
# ZSP03: `C_j = {b_k ≥ 0}` near every zero face, and the circle-stage descended differential

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP03 (B:6486–6489, 6510–6515: "Near a boundary point
use the smooth base function `b_i = u_i/v_i − .4` … Submersion charts give exactly `C_j = {b_i ≥ 0}`
locally"), for the circle stage `j = 1` (base `B₁ = W₁ ∩ R₁`, 2-dimensional) and the slim stage
`j = 3` (`Bs = W₃ ∩ R₃`, G10–G13).

* `Gaf02ChainE.zsp03_local_domain_ZSP35` (any stage `st`, any base set `B` covered by the image):
  around `f_st(q)`, `q ∈ ∂Z_k`, a point `w ∈ B` lies in `C = f_st(M₁ ∩ f_st⁻¹B)` iff `b_k(w) ≥ 0`
  (properness keeps nearby whole fibres in the defining neighbourhood of `∂Z_k`).
* `Gaf02ChainEJA.zsp03_slim_local_domain_ZSP35`, `zsp03_circle_local_domain_ZSP35`: the two
  instances (`C₃` of G11; `C₁ = f₁(M₁ ∩ X₁)` of G6).
* generic `fderiv_ne_zero_of_eventuallyEq_comp_ZSP35`; circle charts `Gaf02ChainE.circleParam_ZSP35`
  (`finalBase_circle_chart_BAS`), `circle_param_coord_ZSP35` (`ψ_i ∘ g_i = f₁` on `Y_i`);
  `Gaf02ChainEJA.zsp03_circle_face_chart_ZSP35`: at a face point over `R₁` the descended
  `b_k ∘ ψ_i` (two variables) vanishes with NONZERO differential at `g_i(q)`.

Consumer: `zsp03_base_domains_C14Z_ZSP35`.
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

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Descent of a nonzero differential through a factorization** (several variables): if
`r = h ∘ g` near `p`, `g` is differentiable at `p`, `h` at `g p`, and `dr(p) ≠ 0`, then
`dh(g p) ≠ 0`. -/
theorem fderiv_ne_zero_of_eventuallyEq_comp_ZSP35 {r : M → ℝ} {g : M → F} {h : F → ℝ} {p : M}
    (hr : r =ᶠ[𝓝 p] h ∘ g) (hg : MDifferentiableAt I 𝓘(ℝ, F) g p)
    (hh : DifferentiableAt ℝ h (g p)) (hne : mfderiv I 𝓘(ℝ, ℝ) r p ≠ 0) :
    fderiv ℝ h (g p) ≠ 0 := by
  intro h0
  have hh' : HasMFDerivAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) h (g p) 0 := by
    have := hh.hasFDerivAt.hasMFDerivAt
    rw [h0] at this
    exact this
  have hc := (hh'.comp p hg.hasMFDerivAt).congr_of_eventuallyEq hr
  apply hne
  rw [hc.mfderiv]
  ext v
  rfl

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz}

/-- Each zero domain lies in the zero region. -/
theorem zspDomain_subset_zeroUnion_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (k : P.zero.finite_centres.toFinset) :
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E ⊆ C.zeroUnion_ZSP35 :=
  subset_iUnion (fun l : P.zero.finite_centres.toFinset =>
    zspDomain_ZSP35 P.toLocalChartFamily P.zero l C.E) k

/-- **ZSP03's local domain equation** (B:6510–6515), for a stage map `f` (continuous; `b_k ∘ f`
is ZSP02's `r_k`; the whole fibre through the face point `q ∈ ∂Z_k` lies in `∂Z_k`) and a base
set `B` covered by `f(M)`: there is an open `N ∋ f(q)` such that a point `w ∈ N ∩ B` lies in
`f(M₁ ∩ f⁻¹B)` exactly when `b_k(w) ≥ 0`. -/
theorem zsp03_local_domain_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    {f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)} (hf : Continuous f)
    {B : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    (honto : ∀ w ∈ B, ∃ p, f p = w) (k : P.zero.finite_centres.toFinset) {q : X}
    (hfib : ∀ y, f y = f q → y ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))
    (hbase : ∀ y, zspBaseFun_ZSP35 P k (f y) =
      ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      f q ∈ N ∧ ∀ w ∈ N ∩ B,
        (w ∈ f '' ((interior C.zeroUnion_ZSP35)ᶜ ∩ f ⁻¹' B) ↔ 0 ≤ zspBaseFun_ZSP35 P k w) := by
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, -⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.zsp02_disjoint_ZSP35 hεr hkk)
  have hfr := (C.zsp02_domain_ZSP35 hεr k).2.2.1
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, -⟩ := C.zsp02_domain_ZSP35 hεr k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  -- the defining neighbourhood of the face, away from the other zero domains
  obtain ⟨Vn, hVn⟩ : ∃ Vn : Set X, Vn = O ∩ ⋂ l ∈ ({k}ᶜ : Set P.zero.finite_centres.toFinset),
      (zspDomain_ZSP35 P.toLocalChartFamily P.zero l C.E)ᶜ := ⟨_, rfl⟩
  have hVo : IsOpen Vn := by
    rw [hVn]
    exact hO.inter ((toFinite _).isOpen_biInter fun l _ =>
      (C.zsp02_domain_ZSP35 hεr l).1.isClosed.isOpen_compl)
  have hfibV : ∀ y, f y = f q → y ∈ Vn := by
    intro y hy
    have hyF := hfib y hy
    rw [hVn]
    refine ⟨hFO (hfr ▸ hyF), mem_iInter₂.mpr fun l hl => ?_⟩
    exact Set.disjoint_left.mp (C.zsp02_disjoint_ZSP35 hεr (Ne.symm (show l ≠ k from hl)))
      ((hclk k).frontier_subset hyF)
  have hGc : IsClosed (f '' Vnᶜ) := (hVo.isClosed_compl.isCompact.image hf).isClosed
  refine ⟨(f '' Vnᶜ)ᶜ, hGc.isOpen_compl, fun ⟨y, hy, hyq⟩ => hy (hfibV y hyq), ?_⟩
  rintro w ⟨hwN, hwB⟩
  have hfibw : ∀ y, f y = w → y ∈ Vn := fun y hy => by
    by_contra hyV
    exact hwN ⟨y, hyV, hy⟩
  -- the open set `{r_k < 0} ∩ O` lies in `Z_k`
  have hrc : ContinuousOn (fun z => ((C.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) O := fun z hz =>
    ((hOprop z hz).2.1.continuousAt).continuousWithinAt
  have hopen := hrc.isOpen_inter_preimage hO (isOpen_Iio (a := (0 : ℝ)))
  constructor
  · rintro ⟨y, ⟨hyM, -⟩, hyw⟩
    by_contra hneg
    push Not at hneg
    have hyV := hfibw y hyw
    rw [hVn] at hyV
    have hry : ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 < 0 := by
      rw [← hbase y, hyw]
      exact hneg
    have hyint : y ∈ interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
      rw [mem_interior]
      exact ⟨_, fun z hz => ((hOprop z hz.1).2.2).mpr (le_of_lt hz.2), hopen, hyV.1, hry⟩
    exact hyM (interior_mono (C.zspDomain_subset_zeroUnion_ZSP35 k) hyint)
  · intro hpos
    obtain ⟨y, hyw⟩ := honto w hwB
    have hyV := hfibw y hyw
    rw [hVn] at hyV
    have hry : 0 ≤ ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 := by
      rw [← hbase y, hyw]
      exact hpos
    refine ⟨y, ⟨fun hyi => ?_, by rw [mem_preimage, hyw]; exact hwB⟩, hyw⟩
    obtain ⟨l, hl⟩ := mem_iUnion.mp (interior_subset hyi)
    have hlk : l = k := by
      by_contra hlk
      exact (mem_iInter₂.mp hyV.2 l hlk) hl
    rw [hlk] at hl
    have hyZ := ((hOprop y hyV.1).2.2).mp hl
    have hr0 : ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 = 0 := le_antisymm hyZ hry
    -- then `y` is a face point, not an interior point of `Z`
    have hv := (hOprop y hyV.1).1
    have hv0 : 0 < (C.E y (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
    have hyF : y ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E := by
      refine ⟨by nlinarith, ?_⟩
      rw [sub_eq_zero, div_eq_iff hv0.ne'] at hr0
      exact hr0
    exact hfrk k (hfr ▸ hyF) hyi

/-- The chart `ψ_i` of `W₁` (`finalBase_circle_chart_BAS`, chosen). -/
def circleParam_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) :
    ℝ² → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) :=
  Classical.choose (C.toChain.finalBase_circle_chart_BAS C.rough i)

/-- On `Y_i` (`B(c_i, 200ρ_i)`, `‖η_i‖ < 5`), `g_i = R_i⁻¹u_i(π₁E)` lies in `B(0, 5.5)` and
`ψ_i ∘ g_i = π₁E`. -/
theorem circle_param_coord_ZSP35 (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {y : X}
    (hy : y ∈ gaf07CircleY_GAFC P.toLocalChartPackets i) :
    C.toChain.gaf07CircleCoord_GAFC i y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
      C.circleParam_ZSP35 i (C.toChain.gaf07CircleCoord_GAFC i y) =
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y) := by
  obtain ⟨-, -, hout⟩ := Classical.choose_spec (C.toChain.finalBase_circle_chart_BAS C.rough i)
  have hV := C.toChain.circle_mem_patch_of_domain5_BAS i hy.1 hy.2
  have hff := C.toChain.final_factor_BAS 0 y
  have hW : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y) ∈
      C.toChain.finalBase_BAS 0 ∩ markedCondition_BPRE (gafCircleVector P.toLocalChartPackets i)
        (gafCircleMarker P.toLocalChartPackets i) (ρ i.1) 1 := by
    rw [hff]
    refine ⟨⟨_, mem_iUnion.mpr ⟨i, hV⟩, rfl⟩, ?_, ?_⟩
    · rw [(C.toChain.theta_retains_circle_BAS i _).2]
      exact hV.2.1
    · rw [(C.toChain.theta_retains_circle_BAS i _).1]
      exact hV.2.2
  exact hout _ hW

end Gaf02ChainE

namespace Gaf02ChainEJA

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {cadj : ℝ}

/-- **ZSP03, slim stage: `C₃ = {b_k ≥ 0}` near every zero face** (B:6510–6515). -/
theorem zsp03_slim_local_domain_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.slimMap_ZSP35 q ∈ N ∧
      ∀ w ∈ N ∩ C.slimBs_ZSP35, (w ∈ C.slimC3_ZSP35 ↔ 0 ≤ zspBaseFun_ZSP35 P k w) :=
  C.toGaf02ChainE.zsp03_local_domain_ZSP35 hεr C.continuous_slimMap_ZSP35
    (fun w hw => C.toGaf02ChainE.gaf07_slim_onto_GAFC w hw.1) k
    (fun _ hy => C.toGaf02ChainE.zsp03_whole_fibre_ZSP35 hεr 2 k hq hy)
    (C.baseFun_slimMap_ZSP35 k)

/-- **ZSP03, circle stage: `C₁ = {b_k ≥ 0}` near every zero face** (B:6510–6515), with
`B₁ = W₁ ∩ R₁` and `C₁ = π₁E(M₁ ∩ X₁)` (G6's `C₁`). -/
theorem zsp03_circle_local_domain_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)) :
    ∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q) ∈ N ∧
      ∀ w ∈ N ∩ (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets),
        (w ∈ (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
            (C.toChain.E p)) '' ((interior C.zeroUnion_ZSP35)ᶜ ∩
              (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
                (C.toChain.E p)) ⁻¹'
                  (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets)) ↔
          0 ≤ zspBaseFun_ZSP35 P k w) :=
  C.toGaf02ChainE.zsp03_local_domain_ZSP35 hεr
    ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection.continuous.comp
      C.toChain.stage_smooth.2.2.continuous)
    (fun w hw => C.toGaf02ChainE.gaf07_circle_onto_GAFC w hw.1) k
    (fun _ hy => C.toGaf02ChainE.zsp03_whole_fibre_ZSP35 hεr 0 k hq hy)
    (C.toChain.zero_base_function_ZSP35 0 k).1

/-- **ZSP03, circle stage: the boundary equation descends with nonzero differential on `B₁`**
(B:6510–6515): at a face point `q ∈ ∂Z_k` with `π₁E(q)` in the ratio set `R₁` there is a circle
chart `i` with `q ∈ Y_i`, `ψ_i ∘ g_i = π₁E` on `Y_i`, and the two-variable function `b_k ∘ ψ_i`
vanishes at `g_i(q)` with NONZERO differential there. -/
theorem zsp03_circle_face_chart_ZSP35 (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) {q : X}
    (hqF : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E)
    (hqR : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q) ∈
      gaf07CircleRatio_G47 P.toLocalChartPackets) :
    ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
      q ∈ gaf07CircleY_GAFC P.toLocalChartPackets i ∧
      (∀ y ∈ gaf07CircleY_GAFC P.toLocalChartPackets i,
        C.toChain.gaf07CircleCoord_GAFC i y ∈ ball (0 : ℝ²) (11 / 2 * 1) ∧
        C.circleParam_ZSP35 i (C.toChain.gaf07CircleCoord_GAFC i y) =
          (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y)) ∧
      DifferentiableAt ℝ (fun t => zspBaseFun_ZSP35 P k (C.circleParam_ZSP35 i t))
        (C.toChain.gaf07CircleCoord_GAFC i q) ∧
      fderiv ℝ (fun t => zspBaseFun_ZSP35 P k (C.circleParam_ZSP35 i t))
        (C.toChain.gaf07CircleCoord_GAFC i q) ≠ 0 ∧
      zspBaseFun_ZSP35 P k (C.circleParam_ZSP35 i (C.toChain.gaf07CircleCoord_GAFC i q)) = 0 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hqR
  have hπ : ∀ y, (gafStageQ P.toLocalChartFamily P.zero 0).starProjection y = y :=
    gafStageQ_zero_starProjection_BAS P.toLocalChartPackets
  have h1 : (1 - (1 : ℝ)) • cgpGlobalMap P.toLocalChartFamily P.zero q +
      (1 : ℝ) • C.toChain.E q = C.toChain.E q := by
    rw [sub_self, zero_smul, zero_add, one_smul]
  have hm := hi.1
  have hr := hi.2
  rw [hπ] at hm hr
  obtain ⟨hqb, hqη, -⟩ := C.toChain.gaf06_circle_G47 C.c_two_lt i q 1 ⟨zero_le_one, le_rfl⟩
    (by rw [h1]; exact hm) (by rw [h1]; exact hr.le)
  have hY : q ∈ gaf07CircleY_GAFC P.toLocalChartPackets i := ⟨hqb, by linarith⟩
  have hloc := fun y (hy : y ∈ gaf07CircleY_GAFC P.toLocalChartPackets i) =>
    C.toGaf02ChainE.circle_param_coord_ZSP35 i hy
  obtain ⟨-, -, -, -, -, -, O, hO, hFO, hOprop, hdne⟩ := C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hvq : 0 < (C.E q (.inr (.inr (.inr (.inl k))))).snd := by
    have := (hOprop q (hFO hqF)).1
    nlinarith
  have hbase : ∀ y, zspBaseFun_ZSP35 P k
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E y)) =
      ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
        (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 :=
    (C.toChain.zero_base_function_ZSP35 0 k).1
  have hfq := (hloc q hY).2
  have hzero : zspBaseFun_ZSP35 P k
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q)) = 0 := by
    rw [hbase q, hqF.2, mul_div_assoc, div_self hvq.ne', mul_one, sub_self]
  have hbk : ContDiffAt ℝ ∞ (zspBaseFun_ZSP35 P k)
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q)) := by
    refine zero_base_function_smooth_ZSP35 _ _ ?_
    rw [gafStageQ_starProjection_zeroTag_GAF8 P 0 k]
    exact hvq.ne'
  have hψ : DifferentiableAt ℝ (C.circleParam_ZSP35 i) (C.toChain.gaf07CircleCoord_GAFC i q) :=
    (((Classical.choose_spec (C.toChain.finalBase_circle_chart_BAS C.rough i)).1).contDiffAt
      (isOpen_ball.mem_nhds (hloc q hY).1)).differentiableAt (by simp)
  have hh : DifferentiableAt ℝ (fun t => zspBaseFun_ZSP35 P k (C.circleParam_ZSP35 i t))
      (C.toChain.gaf07CircleCoord_GAFC i q) := by
    have hb' : DifferentiableAt ℝ (zspBaseFun_ZSP35 P k)
        (C.circleParam_ZSP35 i (C.toChain.gaf07CircleCoord_GAFC i q)) := by
      rw [hfq]
      exact hbk.differentiableAt (by simp)
    exact hb'.comp _ hψ
  have heq : (fun y => ((C.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
      (C.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) =ᶠ[𝓝 q]
      (fun t => zspBaseFun_ZSP35 P k (C.circleParam_ZSP35 i t)) ∘
        C.toChain.gaf07CircleCoord_GAFC i := by
    filter_upwards [(isOpen_gaf07CircleY_GAFC P.toLocalChartPackets i).mem_nhds hY] with y hy
    exact ((congrArg (zspBaseFun_ZSP35 P k) (hloc y hy).2).trans (hbase y)).symm
  have hg : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) q :=
    (((((ρ i.1)⁻¹ • blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i)).comp (gafStageQ P.toLocalChartFamily P.zero 0).starProjection).contDiff
        |>.comp_contMDiff C.toChain.stage_smooth.2.2) q).mdifferentiableAt (by simp)
  refine ⟨i, hY, hloc, hh, fderiv_ne_zero_of_eventuallyEq_comp_ZSP35 heq hg hh (hdne q hqF), ?_⟩
  rw [hfq]
  exact hzero

end Gaf02ChainEJA

/-- **Consumer: ZSP03's base domains on the final family** (chain with (JA) on the `C14`
projection): near every zero-face point, `C₃ = {b_k ≥ 0}` in `Bs` and `C₁ = {b_k ≥ 0}` in
`B₁ = W₁ ∩ R₁`; over `R₁`, the descended `b_k` has nonzero differential in a circle chart. -/
theorem zsp03_base_domains_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) {q : X}
    (hq : q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)) :
    (∃ N : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen N ∧
      C.slimMap_ZSP35 q ∈ N ∧ ∀ w ∈ N ∩ C.slimBs_ZSP35,
        (w ∈ C.slimC3_ZSP35 ↔
          0 ≤ zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k w)) ∧
    ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E q) ∈
        gaf07CircleRatio_G47 P.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets →
      ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset,
        q ∈ gaf07CircleY_GAFC
          P.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets i ∧
        fderiv ℝ (fun t => zspBaseFun_ZSP35 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k
          (C.circleParam_ZSP35 i t)) (C.toChain.gaf07CircleCoord_GAFC i q) ≠ 0) := by
  have hfr := (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1
  refine ⟨C.zsp03_slim_local_domain_ZSP35 hεr k hq, fun hR => ?_⟩
  obtain ⟨i, hY, -, -, hne, -⟩ := C.zsp03_circle_face_chart_ZSP35 hεr k (hfr ▸ hq) hR
  exact ⟨i, hY, hne⟩

end DifferentialGeometry.Geometry.Collapse
