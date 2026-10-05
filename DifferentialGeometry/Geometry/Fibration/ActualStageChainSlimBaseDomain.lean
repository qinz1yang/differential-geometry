import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroBaseDomains

/-!
# ZSP04: `D₃ = K₃ ∩ C₃` is a compact smooth one-dimensional domain (arcs and loops)

Lane C14-ZSP35d. Blueprint `master207B.tex`, ZSP04 (B:6541–6544: "`D₃` is a compact one-manifold
with boundary"; B:6577–6582: "no isolated endpoint or double boundary constraint occurs"), on the
closed slim atlas of G10 and the shared kernel of lane B-BCF134 (half charts, `HalfChart_BCF`,
`exists_smoothCompactOneDomain_BCF`).

* generic: `halfChartRestrict_ZSP35` (a half chart of `T` restricted by an open `O` with
  `O ∩ Bs ⊆ A` is a half chart of `T ∩ A`); `exists_sign_halfline_ZSP35` (a `C¹` function with a
  simple zero is, after a sign `σ = ±1`, nonnegative exactly on a half line near the zero).
* `Gaf02ChainEJA.exists_face_halfChart_ZSP35`: at a face point `y ∈ F₃ ∩ int_{Bs} T` the set
  `T ∩ C₃` has a half chart (read through the simple zero of the descended `b_k`).
* `Gaf02ChainEJA.zsp04_D3_ZSP35` (final family): compact smooth one-dimensional domains
  `K₃, D₃ ⊆ Bs` (finitely many smooth regular arcs and loops each) with `D₃ = K₃ ∩ C₃`, (SK)
  (slab image and `F₃` in `int K₃`), `∂K₃ ∩ F₃ = ∅`, and `∂D₃ = (∂K₃ ∩ int C₃) ⊔ (int K₃ ∩ F₃)`.

Consumer: `zsp04_D3_C14Z_ZSP35`.
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

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **Restricting a half chart**: a half chart `d` of `T`, cut down by an open `Oc` with
`Oc ∩ Bs ⊆ A`, is a half chart of `T ∩ A` (open set `d.O ∩ Oc`). -/
def halfChartRestrict_ZSP35 {Bs T A : Set H}
    (d : DifferentialGeometry.Topology.HalfChart_BCF Bs T) {Oc : Set H} (hOc : IsOpen Oc)
    (hOcA : Oc ∩ Bs ⊆ A) : DifferentialGeometry.Topology.HalfChart_BCF Bs (T ∩ A) :=
  { d with
    V := d.V ∩ (d.W ∩ d.π ⁻¹' Oc)
    O := d.O ∩ Oc
    isOpen_V := d.isOpen_V.inter (d.smooth.continuousOn.isOpen_inter_preimage d.isOpen_W hOc)
    V_subset := fun _ ht => ht.2.1
    isOpen_O := d.isOpen_O.inter hOc
    inter_eq := by
      ext z
      constructor
      · rintro ⟨⟨hzT, -⟩, hzO, hzOc⟩
        have hz : z ∈ T ∩ d.O := ⟨hzT, hzO⟩
        rw [d.inter_eq] at hz
        obtain ⟨t, ⟨htV, ht0⟩, rfl⟩ := hz
        exact ⟨t, ⟨⟨htV, d.V_subset htV, hzOc⟩, ht0⟩, rfl⟩
      · rintro ⟨t, ⟨⟨htV, htW, htOc⟩, ht0⟩, rfl⟩
        have hz : d.π t ∈ T ∩ d.O := by
          rw [d.inter_eq]
          exact ⟨t, ⟨htV, ht0⟩, rfl⟩
        exact ⟨⟨hz.1, hOcA ⟨htOc, d.mem t htW⟩⟩, hz.2, htOc⟩ }

theorem halfChartRestrict_O_ZSP35 {Bs T A : Set H}
    (d : DifferentialGeometry.Topology.HalfChart_BCF Bs T) {Oc : Set H} (hOc : IsOpen Oc)
    (hOcA : Oc ∩ Bs ⊆ A) : (halfChartRestrict_ZSP35 d hOc hOcA).O = d.O ∩ Oc := rfl

end Generic

/-- **A simple zero is a sign change onto a half line**: if `g` is `C¹` on an open `U ∋ t₀`,
`g t₀ = 0` and `g'(t₀) ≠ 0`, there are `σ = ±1` and `δ > 0` with `(t₀ − δ, t₀ + δ) ⊆ U` and, for
`|t| < δ`, `g(t₀ + σt) ≥ 0 ⟺ t ≥ 0`. -/
theorem exists_sign_halfline_ZSP35 {g : ℝ → ℝ} {t₀ : ℝ} {U : Set ℝ} (hU : IsOpen U)
    (ht₀ : t₀ ∈ U) (hg : ContDiffOn ℝ 1 g U) (h0 : g t₀ = 0) (hne : deriv g t₀ ≠ 0) :
    ∃ σ δ : ℝ, σ * σ = 1 ∧ 0 < δ ∧ Ioo (t₀ - δ) (t₀ + δ) ⊆ U ∧
      ∀ t ∈ Ioo (-δ) δ, (0 ≤ g (t₀ + σ * t) ↔ 0 ≤ t) := by
  have hdc : ContinuousOn (deriv g) U := hg.continuousOn_deriv_of_isOpen hU le_rfl
  have hgc : ContinuousOn g U := hg.continuousOn
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- negative derivative: `σ = -1`
    have hset : U ∩ deriv g ⁻¹' Iio 0 ∈ 𝓝 t₀ :=
      (hdc.isOpen_inter_preimage hU isOpen_Iio).mem_nhds ⟨ht₀, hneg⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hset
    have hsub : Ioo (t₀ - δ) (t₀ + δ) ⊆ U ∩ deriv g ⁻¹' Iio 0 := fun t ht =>
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    have hanti : StrictAntiOn g (Ioo (t₀ - δ) (t₀ + δ)) := by
      refine strictAntiOn_of_deriv_neg (convex_Ioo _ _) (hgc.mono fun t ht => (hsub ht).1) ?_
      intro t ht
      rw [interior_Ioo] at ht
      exact (hsub ht).2
    refine ⟨-1, δ, by norm_num, hδ, fun t ht => (hsub ht).1, fun t ht => ?_⟩
    have hmem : t₀ + -1 * t ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmem₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
    have hle := hanti.le_iff_ge hmem₀ hmem
    rw [h0] at hle
    rw [hle]
    constructor <;> intro h <;> linarith
  · have hset : U ∩ deriv g ⁻¹' Ioi 0 ∈ 𝓝 t₀ :=
      (hdc.isOpen_inter_preimage hU isOpen_Ioi).mem_nhds ⟨ht₀, hpos⟩
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hset
    have hsub : Ioo (t₀ - δ) (t₀ + δ) ⊆ U ∩ deriv g ⁻¹' Ioi 0 := fun t ht =>
      hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    have hmono : StrictMonoOn g (Ioo (t₀ - δ) (t₀ + δ)) := by
      refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hgc.mono fun t ht => (hsub ht).1) ?_
      intro t ht
      rw [interior_Ioo] at ht
      exact (hsub ht).2
    refine ⟨1, δ, by norm_num, hδ, fun t ht => (hsub ht).1, fun t ht => ?_⟩
    have hmem : t₀ + 1 * t ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmem₀ : t₀ ∈ Ioo (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
    have hle := hmono.le_iff_le hmem₀ hmem
    rw [h0] at hle
    rw [hle]
    constructor <;> intro h <;> linarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **A half chart of `T ∩ C₃` at a face point** (B:6577–6582): if `y ∈ F₃` lies in the relative
interior of `T ⊆ Bs`, then `T ∩ C₃` has a half chart whose open set contains `y` (the slim chart
read with the sign of the descended `b_k`'s derivative). -/
theorem exists_face_halfChart_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) {Tb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))}
    {y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hyF : y ∈ C.slimFacePoints_ZSP35)
    (hyT : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' Tb : Set C.slimBs_ZSP35)) :
    ∃ d : DifferentialGeometry.Topology.HalfChart_BCF C.slimBs_ZSP35 (Tb ∩ C.slimC3_ZSP35),
      y ∈ d.O := by
  obtain ⟨k, q, ⟨hqF, hqU⟩, rfl⟩ := mem_iUnion.mp hyF
  have hfr := (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).2.2.1
  have hqF' : q ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k C.E := hfr ▸ hqF
  obtain ⟨i, hY, hloc, -, hne, h0⟩ := C.slim_face_chart_ZSP35 hεr k hqF' hqU
  obtain ⟨N, hN, hqN, hNdom⟩ := C.zsp03_slim_local_domain_ZSP35 hεr k hqF
  obtain ⟨-, OT, hOT, hyOT, hOTT⟩ :=
    DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hyT
  obtain ⟨G, hG, hGB⟩ := C.slimAtlas_ZSP35.piece_relOpen i
  set t₀ := C.toChain.gaf07SlimCoord_GAFC i q with ht₀
  have hψq : C.slimParam_ZSP35 i t₀ = C.slimMap_ZSP35 q := (hloc q hY).2
  have hψs := (C.slimParam_spec_ZSP35 i).1
  -- the open parameter set where everything is defined and smooth
  set U : Set ℝ := C.slimAtlas_ZSP35.dom i ∩ C.slimParam_ZSP35 i ⁻¹'
    (G ∩ OT ∩ N ∩ {w | (w (.inr (.inr (.inr (.inl k))))).snd ≠ 0}) with hU
  have hvopen : IsOpen {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) |
      (w (.inr (.inr (.inr (.inl k))))).snd ≠ 0} :=
    isOpen_ne_fun (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inr (.inr (.inr (.inl k))))).continuous continuous_const
  have hUo : IsOpen U := (C.slimAtlas_ZSP35.continuousOn_param_BCF i).isOpen_inter_preimage
    (C.slimAtlas_ZSP35.isOpen_dom i) (((hG.inter hOT).inter hN).inter hvopen)
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, -, -, -, -, -, O, -, hFO, hOprop, -⟩ := C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k
  have hvq : (C.slimMap_ZSP35 q (.inr (.inr (.inr (.inl k))))).snd ≠ 0 := by
    change ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E q)
      (.inr (.inr (.inr (.inl k))))).snd ≠ 0
    rw [gafStageQ_starProjection_zeroTag_GAF8 P.toLocalChartPacketsC14D.toLocalChartPacketsC14 2 k]
    have := (hOprop q (hFO hqF')).1
    change (C.E q (.inr (.inr (.inr (.inl k))))).snd ≠ 0
    nlinarith
  have hdom : t₀ ∈ C.slimAtlas_ZSP35.dom i := by
    refine ⟨(hloc q hY).1, ?_⟩
    change C.slimParam_ZSP35 i t₀ ∈
      gaf07SlimRatio_G47 P.toLocalChartPacketsC14D.toLocalChartPacketsC14.toLocalChartPackets
    rw [hψq]
    exact hqU.2
  have hqG : C.slimMap_ZSP35 q ∈ G := by
    have : C.slimParam_ZSP35 i t₀ ∈ G ∩ C.slimBs_ZSP35 := by
      rw [hGB]
      exact ⟨t₀, hdom, rfl⟩
    rw [hψq] at this
    exact this.1
  have ht₀U : t₀ ∈ U := ⟨hdom, by rw [mem_preimage, hψq]; exact ⟨⟨⟨hqG, hyOT⟩, hqN⟩, hvq⟩⟩
  -- the descended function is smooth on `U`
  have hsm : ContDiffOn ℝ 1 (fun t => zspBaseFun_ZSP35
      P.toLocalChartPacketsC14D.toLocalChartPacketsC14 k (C.slimParam_ZSP35 i t)) U := by
    intro t ht
    have hb := zero_base_function_smooth_ZSP35 (.inr (.inr (.inr (.inl k))) :
      CGPTag P.toLocalChartFamily P.zero) (C.slimParam_ZSP35 i t) ht.2.2
    have hψt : ContDiffAt ℝ ∞ (C.slimParam_ZSP35 i) t :=
      hψs.contDiffAt (isOpen_ball.mem_nhds ht.1.1)
    exact ((hb.comp t hψt).of_le (by simp)).contDiffWithinAt
  obtain ⟨σ, δ', hσ, hδ', hIooU, hsign⟩ := exists_sign_halfline_ZSP35 hUo ht₀U hsm h0 hne
  have hσ' : σ = 1 ∨ σ = -1 := by
    have : (σ - 1) * (σ + 1) = 0 := by linear_combination hσ
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hC3B := (C.zsp03_slim_saturated_ZSP35 hεr).2.1
  refine ⟨C.slimAtlas_ZSP35.halfChart_BCF i σ t₀ hσ (Ioo (-δ') δ')
    (G ∩ OT ∩ N ∩ C.slimAtlas_ZSP35.coord i ⁻¹' Ioo (t₀ - δ') (t₀ + δ')) isOpen_Ioo ?_ ?_ ?_,
    ⟨⟨⟨hqG, hyOT⟩, hqN⟩, ?_⟩⟩
  · intro t ht
    refine (hIooU ?_).1
    rcases hσ' with rfl | rfl
    · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · exact ((hG.inter hOT).inter hN).inter
      ((C.slimAtlas_ZSP35.coord i).continuous.isOpen_preimage _ isOpen_Ioo)
  · ext z
    constructor
    · rintro ⟨⟨hzT, hzC⟩, ⟨⟨hzG, hzOT⟩, hzN⟩, hzco⟩
      have hzB : z ∈ C.slimBs_ZSP35 := hC3B hzC
      have hz : z ∈ G ∩ C.slimBs_ZSP35 := ⟨hzG, hzB⟩
      rw [hGB] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      have hco : C.slimAtlas_ZSP35.coord i (C.slimAtlas_ZSP35.param i u) = u :=
        C.slimAtlas_ZSP35.coord_param i u hu
      rw [mem_preimage, hco] at hzco
      have hb := (hNdom _ ⟨hzN, hzB⟩).mp hzC
      refine ⟨σ * (u - t₀), ⟨?_, ?_⟩, ?_⟩
      · rcases hσ' with rfl | rfl
        · exact ⟨by linarith [hzco.1], by linarith [hzco.2]⟩
        · exact ⟨by linarith [hzco.2], by linarith [hzco.1]⟩
      · have ht : σ * (u - t₀) ∈ Ioo (-δ') δ' := by
          rcases hσ' with rfl | rfl
          · exact ⟨by linarith [hzco.1], by linarith [hzco.2]⟩
          · exact ⟨by linarith [hzco.2], by linarith [hzco.1]⟩
        refine (hsign _ ht).mp ?_
        have he : t₀ + σ * (σ * (u - t₀)) = u := by linear_combination (u - t₀) * hσ
        rw [he]
        exact hb
      · change C.slimAtlas_ZSP35.param i (t₀ + σ * (σ * (u - t₀))) = C.slimAtlas_ZSP35.param i u
        congr 1
        linear_combination (u - t₀) * hσ
    · rintro ⟨t, ⟨ht, ht0⟩, rfl⟩
      have hs : t₀ + σ * t ∈ Ioo (t₀ - δ') (t₀ + δ') := by
        rcases hσ' with rfl | rfl
        · exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
      have hsU := hIooU hs
      have hpB : C.slimAtlas_ZSP35.param i (t₀ + σ * t) ∈ C.slimBs_ZSP35 :=
        C.slimAtlas_ZSP35.param_mem_BCF hsU.1
      obtain ⟨⟨⟨hpG, hpOT⟩, hpN⟩, -⟩ := hsU.2
      refine ⟨⟨hOTT ⟨hpOT, hpB⟩, (hNdom _ ⟨hpN, hpB⟩).mpr ((hsign t ht).mpr ht0)⟩,
        ⟨⟨hpG, hpOT⟩, hpN⟩, ?_⟩
      rw [mem_preimage, C.slimAtlas_ZSP35.coord_param i _ hsU.1]
      exact hs
  · change C.slimAtlas_ZSP35.coord i (C.slimMap_ZSP35 q) ∈ Ioo (t₀ - δ') (t₀ + δ')
    have hc : C.slimAtlas_ZSP35.coord i (C.slimParam_ZSP35 i t₀) = t₀ :=
      C.slimAtlas_ZSP35.coord_param i t₀ hdom
    rw [← hψq, hc]
    exact ⟨by linarith, by linarith⟩

/-- **ZSP04: `K₃` and `D₃ = K₃ ∩ C₃` as compact smooth one-dimensional domains** (B:6531–6582,
D74-9): there are `K₃, D₃ : SmoothCompactOneDomain_BCF Bs` (finitely many smooth regular arcs and
loops each) with `D₃ = K₃ ∩ C₃`, (SK) `f(⋃ slabs) ∪ F₃ ⊆ int_{Bs} K₃`, `∂K₃ ∩ F₃ = ∅`, `D₃`
regular, and `∂D₃ = (∂K₃ ∩ int C₃) ⊔ (int K₃ ∩ F₃)` (`F₃ = ∂C₃`). -/
theorem zsp04_D3_ZSP35
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ∪ C.slimFacePoints_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      Disjoint (K₃.carrier \
          Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35))
        C.slimFacePoints_ZSP35 ∧
      D₃.carrier ⊆ closure (Subtype.val '' interior
        (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35)) ∧
      D₃.carrier \ Subtype.val '' interior (Subtype.val ⁻¹' D₃.carrier : Set C.slimBs_ZSP35) =
        ((K₃.carrier \
              Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35)) ∩
            Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 : Set C.slimBs_ZSP35)) ∪
          (Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∩
            C.slimFacePoints_ZSP35) := by
  obtain ⟨-, hC3B, -, -, hfront⟩ := C.zsp03_slim_saturated_ZSP35 hεr
  obtain ⟨-, hbd⟩ := C.zsp03_slim_boundary_eq_ZSP35 hεr
  obtain ⟨-, hI, -⟩ := C.toChain.zsp04_slab_image_ZSP35
  have hFfin := (C.zsp03_slim_face_points_ZSP35 hεr).2
  have hFB : C.slimFacePoints_ZSP35 ⊆ C.slimBs_ZSP35 := by
    intro w hw
    obtain ⟨k, p, ⟨-, hpU⟩, rfl⟩ := mem_iUnion.mp hw
    exact hpU
  obtain ⟨n, c', a, b', hab, hgen, hcpt, hTB, hcov, hreg⟩ :=
    C.slimAtlas_ZSP35.exists_cover_union_generic_BCF (hI.union hFfin.isCompact)
      (union_subset C.slimSlabImage_subset_slimBs_ZSP35 hFB) hFfin
      (C.zsp03_slim_regular_ZSP35 hεr) (hfront.trans subset_union_right)
  set Tb := ⋃ r, C.slimAtlas_ZSP35.param (c' r) '' Icc (a r) (b' r) with hTb
  -- half charts of `K₃ = Tb`
  have hch : ∀ y : Tb, ∃ d : DifferentialGeometry.Topology.HalfChart_BCF C.slimBs_ZSP35 Tb,
      (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈ d.O := fun y =>
    C.slimAtlas_ZSP35.exists_halfChart_of_cover_BCF (fun r => ⟨(hab r).1, (hab r).2.1⟩) hgen y.2
  choose ch hch using hch
  obtain ⟨K₃, hK₃⟩ := DifferentialGeometry.Topology.exists_smoothCompactOneDomain_BCF ⟨ch, hch⟩ hcpt
  -- `∂Tb ∩ F₃ = ∅`
  have hKF : Disjoint (Tb \ Subtype.val '' interior (Subtype.val ⁻¹' Tb : Set C.slimBs_ZSP35))
      C.slimFacePoints_ZSP35 := by
    rw [Set.disjoint_left]
    rintro y ⟨hyT, hyI⟩ hyF
    obtain ⟨r, t, ht, rfl⟩ := mem_iUnion.mp hyT
    by_cases hto : t ∈ Ioo (a r) (b' r)
    · exact hyI (C.slimAtlas_ZSP35.image_Ioo_subset_relInterior_BCF (hab r).2.1
        (subset_iUnion (fun r => C.slimAtlas_ZSP35.param (c' r) '' Icc (a r) (b' r)) r)
        ⟨t, hto, rfl⟩)
    · have hend : t = a r ∨ t = b' r := by
        by_contra h
        push Not at h
        exact hto ⟨lt_of_le_of_ne ht.1 (Ne.symm h.1), lt_of_le_of_ne ht.2 h.2⟩
      rcases hend with rfl | rfl
      · exact (hab r).2.2.1 hyF
      · exact (hab r).2.2.2 hyF
  -- half charts of `D₃ = Tb ∩ C₃`
  have hch' : ∀ y : ↥(Tb ∩ C.slimC3_ZSP35),
      ∃ d : DifferentialGeometry.Topology.HalfChart_BCF C.slimBs_ZSP35 (Tb ∩ C.slimC3_ZSP35),
        (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) ∈ d.O := by
    rintro ⟨y, hyT, hyC⟩
    by_cases hyi : y ∈ Subtype.val '' interior (Subtype.val ⁻¹' C.slimC3_ZSP35 :
        Set C.slimBs_ZSP35)
    · obtain ⟨-, Oc, hOc, hyOc, hOcC⟩ :=
        DifferentialGeometry.Topology.mem_image_interior_preimage_val_iff.mp hyi
      obtain ⟨d, hyd⟩ := C.slimAtlas_ZSP35.exists_halfChart_of_cover_BCF
        (fun r => ⟨(hab r).1, (hab r).2.1⟩) hgen hyT
      exact ⟨halfChartRestrict_ZSP35 d hOc hOcC, hyd, hyOc⟩
    · have hyF : y ∈ C.slimFacePoints_ZSP35 := hbd ▸ ⟨hyC, hyi⟩
      exact C.exists_face_halfChart_ZSP35 hεr hyF (hcov (Or.inr hyF))
  choose ch' hch' using hch'
  obtain ⟨hSeq, hSc, -, himg, -⟩ := C.slimPiece_spec_ZSP35 hεr hcpt hTB
    (subset_union_right.trans hcov) hreg
  have hDc : IsCompact (Tb ∩ C.slimC3_ZSP35) := by
    rw [← himg]
    exact hSc.image C.continuous_slimMap_ZSP35
  obtain ⟨D₃, hD₃⟩ := DifferentialGeometry.Topology.exists_smoothCompactOneDomain_BCF
    ⟨ch', hch'⟩ hDc
  obtain ⟨h1, -, -, -⟩ := C.zsp04_SF_ZSP35 hεr hcpt hTB hKF
  rw [hbd] at h1
  refine ⟨K₃, D₃, by rw [hD₃, hK₃], hK₃ ▸ hcov, hK₃ ▸ hKF, hD₃ ▸ hreg, ?_⟩
  rw [hD₃, hK₃]
  exact h1

end Gaf02ChainEJA

/-- **Consumer: `D₃` on the final family** — compact smooth one-dimensional domains `K₃ ⊇ D₃`
(arcs and loops) with `D₃ = K₃ ∩ C₃`, the slab image in `int K₃`, and the boundary of `D₃` split
into the free ends `∂K₃ ∩ int C₃` and the shared zero-face points `int K₃ ∩ F₃`. -/
theorem zsp04_D3_C14Z_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hεr : εr < 1 / 2) :
    ∃ K₃ D₃ : DifferentialGeometry.Topology.SmoothCompactOneDomain_BCF C.slimBs_ZSP35,
      D₃.carrier = K₃.carrier ∩ C.slimC3_ZSP35 ∧
      C.toChain.slimSlabImage_ZSP35 ⊆
        Subtype.val '' interior (Subtype.val ⁻¹' K₃.carrier : Set C.slimBs_ZSP35) ∧
      IsCompact D₃.carrier := by
  obtain ⟨K₃, D₃, hD, hKs, -⟩ := C.zsp04_D3_ZSP35 hεr
  exact ⟨K₃, D₃, hD, subset_union_left.trans hKs, D₃.isCompact_carrier_BCF⟩

end DifferentialGeometry.Geometry.Collapse
