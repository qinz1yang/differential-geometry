import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomains
import DifferentialGeometry.Geometry.Fibration.ActualStageChainZeroFaces
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Circle

/-!
# ZSP03 / ZSP05 on `Gaf02ChainE`: saturated zero faces, circle-stage descent, closed zero pieces

Lane C14-ZSP35b. Blueprint `master207B.tex`, ZSP03 (`prop:fibration-zero-faces-saturated`,
B:6481–6529) and ZSP05 (`prop:fibration-zero-slim-complement-faces`, B:6597–6642), with ZSP02's
domains `Z_k` (`zspDomain_ZSP35`, faces `∂Z_k =` (ZF)).

* `frontier_disjoint_iUnion_ZSP35`: for finitely many pairwise disjoint closed sets the frontier of
  each lies outside the interior of the union and `∂(⋃ Z_k) = ⋃ ∂Z_k`.
* ZSP03 clause 1, every stage `j = 1, 2, 3`: `Gaf02ChainE.zsp03_face_saturated_ZSP35`
  (`π_jE p = π_jE q ⇒ (p ∈ ∂Z_k ↔ q ∈ ∂Z_k)`), `Gaf02ChainE.zsp03_whole_fibre_ZSP35` (a WHOLE fibre
  meeting `∂Z_k` lies in `∂Z_k`).
* ZSP03 on the CIRCLE stage (`j = 1`, with C14-GAF-C's connected whole fibres over `B₁ = W₁ ∩ R₁`,
  on `Gaf02ChainEJA` with TCP01's `β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`):
  `Gaf02ChainEJA.zsp03_circle_fibre_ZSP35` (each whole fibre over `B₁` lies in `int Z` or in
  `M₁ = M ∖ int Z`, and inside `∂Z_k` once it meets it),
      `Gaf02ChainEJA.zsp03_circle_saturated_ZSP35`
  (`M₁ ∩ X₁` saturated, `= X₁ ∩ (π₁E)⁻¹(C₁)` with `C₁ = π₁E(M₁ ∩ X₁)` closed in `B₁`).
* ZSP05, zero part of "a closed connected zero component is the whole carrier":
  `Gaf02ChainE.zsp05_closed_zero_component_ZSP35` (`∂Z_k = ∅ ↔ Z_k = M`, final family).

NOT here: `C_j` as a smooth domain of `B_j` with the descended boundary equation of nonzero
differential (needs `W_j`'s manifold structure and the submersion onto it), the slim stage
`j = 3` (whole connected slim fibres) and the edge stage `j = 2`, ZSP04's `K₃`, `D₃`, `M^slim`,
ZSP05's `(RC)` / `(RF)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- For a finite family of pairwise disjoint closed sets, the frontier of each lies outside the
interior of the union, and the frontier of the union is the union of the frontiers. -/
theorem frontier_disjoint_iUnion_ZSP35 {Y ι : Type*} [TopologicalSpace Y] [Finite ι]
    (Zs : ι → Set Y) (hcl : ∀ i, IsClosed (Zs i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) :
    (∀ i, frontier (Zs i) ⊆ (interior (⋃ i, Zs i))ᶜ) ∧
    frontier (⋃ i, Zs i) = ⋃ i, frontier (Zs i) := by
  classical
  have hint : ∀ i, ∀ x ∈ Zs i, x ∈ interior (⋃ j, Zs j) → x ∈ interior (Zs i) := by
    intro i x hx hint
    have hU : (⋂ j ∈ ({i}ᶜ : Set ι), (Zs j)ᶜ) ∈ 𝓝 x := by
      refine (biInter_mem (toFinite _)).mpr fun j hj => (hcl j).isOpen_compl.mem_nhds ?_
      exact Set.disjoint_left.mp (hdisj i j (Ne.symm hj)) hx
    rw [mem_interior_iff_mem_nhds] at hint ⊢
    filter_upwards [hint, hU] with y hy hyU
    obtain ⟨j, hj⟩ := mem_iUnion.mp hy
    by_cases hji : j = i
    · exact hji ▸ hj
    · exact absurd hj (mem_iInter₂.mp hyU j hji)
  have hfr : ∀ i, frontier (Zs i) ⊆ (interior (⋃ i, Zs i))ᶜ := by
    intro i x hx hxi
    rw [(hcl i).frontier_eq] at hx
    exact hx.2 (hint i x hx.1 hxi)
  refine ⟨hfr, Subset.antisymm ?_ ?_⟩
  · intro x hx
    rw [(isClosed_iUnion_of_finite hcl).frontier_eq] at hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    refine mem_iUnion.mpr ⟨i, ?_⟩
    rw [(hcl i).frontier_eq]
    exact ⟨hi, fun hxi => hx.2 (interior_mono (subset_iUnion Zs i) hxi)⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [(isClosed_iUnion_of_finite hcl).frontier_eq]
    rw [(hcl i).frontier_eq] at hi
    exact ⟨subset_iUnion Zs i hi.1, hfr i ((hcl i).frontier_eq ▸ hi)⟩

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **ZSP03, zero faces are saturated** (B:6484–6485, 6499–6501): for every stage `j = 1, 2, 3`,
`π_jE p = π_jE q` gives `p ∈ ∂Z_k ↔ q ∈ ∂Z_k` (`∂Z_k` is ZSP02's (ZF) set and every `Q_j` retains
the zero block). -/
theorem Gaf02ChainE.zsp03_face_saturated_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} {Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw} (hεr : εr < 1 / 2) (st : Fin 3)
    {k : P.zero.finite_centres.toFinset} {p q : X}
    (hpq : (gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.E p) =
      (gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.E q)) :
    p ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ↔
      q ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := by
  rw [(Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1]
  exact (Ĉ.toChain.zero_face_saturated_ZSP35 st k hpq).2.1

/-- **ZSP03, whole fibres meeting a zero face** (B:6484–6485): every WHOLE fibre of `π_jE`
(`j = 1, 2, 3`) meeting `∂Z_k` lies in `∂Z_k`. -/
theorem Gaf02ChainE.zsp03_whole_fibre_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2) (st : Fin 3)
    (k : P.zero.finite_centres.toFinset) {p : X}
    (hp : p ∈ frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) :
    (fun q => (gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.E q)) ⁻¹'
        {(gafStageQ P.toLocalChartFamily P.zero st).starProjection (Ĉ.E p)} ⊆
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := fun _ hq =>
  (Gaf02ChainE.zsp03_face_saturated_ZSP35 (Ĉ := Ĉ) (k := k) hεr st
    (show _ = _ from hq.symm)).mp hp

/-- **ZSP03 on the circle stage: whole fibres do not cross the zero region** (B:6503–6507), on a
chain with GAF01's (JA) and TCP01's range (`β₂ ≤ 10⁻⁷`, `γ + β₂ < 1/10`, the numeric inputs of
GAF07's circle stage): for `w ∈ B₁ = W₁ ∩ R₁` the WHOLE fibre `F = (π₁E)⁻¹(w)` (connected,
C14-GAF-C) lies in `int Z` or in `M₁ = M ∖ int Z` (`Z = ⋃_k Z_k`), and if it meets `∂Z_k` it lies
in `∂Z_k`. -/
theorem Gaf02ChainEJA.zsp03_circle_fibre_ZSP35 {cadj : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hβ : β 2 ≤ 1 / 10000000)
    (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2)
    {w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)}
    (hw : w ∈ C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) :
    ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ⊆
        interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∨
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ⊆
        (interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ) ∧
    ∀ k : P.zero.finite_centres.toFinset,
      ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ∩
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)).Nonempty →
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ⊆
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
  have hclk : ∀ k : P.zero.finite_centres.toFinset,
      IsClosed (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := fun k =>
    (C.toGaf02ChainE.zsp02_domain_ZSP35 hεr k).1.isClosed
  obtain ⟨hfrk, hfrU⟩ := frontier_disjoint_iUnion_ZSP35
    (fun k : P.zero.finite_centres.toFinset => zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
    hclk (fun k k' hkk => C.toGaf02ChainE.zsp02_disjoint_ZSP35 hεr hkk)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hw.2
  have hcon : IsConnected
      ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w}) :=
    (Gaf02ChainE.gaf07_circle_whole_fibre_GAFC C.toGaf02ChainE C.c_two_lt hβ hd w hw.1 i hi.1
        hi.2).2.2.2
  have hsat : ∀ k : P.zero.finite_centres.toFinset,
      ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ∩
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)).Nonempty →
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ⊆
          frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := by
    rintro k ⟨p, hpF, hp⟩ q hq
    have hpq : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p) =
        (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E q) :=
      (show _ = w from hpF).trans (show _ = w from hq).symm
    exact (Gaf02ChainE.zsp03_face_saturated_ZSP35 (Ĉ := C.toGaf02ChainE) (k := k) hεr 0
      hpq).mp hp
  refine ⟨?_, hsat⟩
  by_cases hmeet : ∃ k : P.zero.finite_centres.toFinset,
      ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ∩
        frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)).Nonempty
  · obtain ⟨k, hk⟩ := hmeet
    exact Or.inr ((hsat k hk).trans (hfrk k))
  · push Not at hmeet
    have hF : (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' {w} ⊆
        interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) ∪
        (closure (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ := by
      intro x hx
      by_cases hxi : x ∈ interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E)
      · exact Or.inl hxi
      · refine Or.inr fun hxc => ?_
        have hxf : x ∈ frontier (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E) := ⟨hxc, hxi⟩
        rw [hfrU] at hxf
        obtain ⟨k, hk⟩ := mem_iUnion.mp hxf
        have hne := hmeet k
        rw [Set.eq_empty_iff_forall_notMem] at hne
        exact hne x ⟨hx, hk⟩
    rcases IsPreconnected.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
        (disjoint_compl_right_iff_subset.mpr interior_subset_closure) hF hcon.isPreconnected with
      h | h
    · exact Or.inl h
    · exact Or.inr (h.trans (compl_subset_compl.mpr interior_subset_closure))

/-- **ZSP03 on the circle stage: `M₁ ∩ X₁` is saturated and descends to a relatively closed
`C₁ ⊆ B₁`** (B:6486–6489, 6503–6509; consumer of `zsp03_circle_fibre_ZSP35`): with
`M₁ = M ∖ int Z`, `X₁ = (π₁E)⁻¹(B₁)` and `C₁ = π₁E(M₁ ∩ X₁)`: points of `X₁` in one fibre are
together in or out of `M₁`; `M₁ ∩ X₁ = X₁ ∩ (π₁E)⁻¹(C₁)`; `C₁` is closed in `B₁` (properness of
the whole restriction). (The smooth-domain structure of `C₁` needs `W₁`'s manifold structure.) -/
theorem Gaf02ChainEJA.zsp03_circle_saturated_ZSP35 {cadj : ℝ}
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (C : Gaf02ChainEJA P Kj Ξ Γ S eg c cw cadj) (hβ : β 2 ≤ 1 / 10000000)
    (hd : γ + β 2 < 1 / 10) (hεr : εr < 1 / 2) :
    (∀ p q : X, (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p ∈
        (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) → (fun p =>
            (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p = (fun p =>
                (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) q →
      (p ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ ↔ q ∈ (interior (⋃ k :
              P.zero.finite_centres.toFinset,
                  zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ)) ∧
    (interior (⋃ k : P.zero.finite_centres.toFinset,
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ ∩ (fun p => (gafStageQ
            P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' (C.toChain.finalBase_BAS 0
                ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) =
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹'
          (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) ∩ (fun p =>
              (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹' ((fun p =>
                  (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) '' ((interior
                      (⋃ k : P.zero.finite_centres.toFinset,
                          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ ∩ (fun p =>
                              (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p))
                                  ⁻¹' (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47
                                      P.toLocalChartPackets))) ∧
    IsClosed ((↑) ⁻¹' ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p))
        '' ((interior (⋃ k : P.zero.finite_centres.toFinset,
            zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ ∩ (fun p => (gafStageQ
                P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹'
                    (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets))) :
                        Set ↥(C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47
                            P.toLocalChartPackets)) := by
  have hsat : ∀ p q : X,
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p ∈
          (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) → (fun p =>
              (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p = (fun p =>
                  (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) q →
      (p ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ ↔ q ∈ (interior (⋃ k :
              P.zero.finite_centres.toFinset,
                  zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ) := by
    intro p q hp hpq
    have hpF : p ∈ (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹'
        {(fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p} := rfl
    have hqF : q ∈ (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) ⁻¹'
        {(fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.E p)) p} := hpq.symm
    rcases (C.zsp03_circle_fibre_ZSP35 hβ hd hεr hp).1 with h | h
    · exact ⟨fun h' => absurd (h hpF) h', fun h' => absurd (h hqF) h'⟩
    · exact ⟨fun _ => h hqF, fun _ => h hpF⟩
  refine ⟨hsat, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨hp, hpX⟩
      exact ⟨hpX, p, ⟨hp, hpX⟩, rfl⟩
    · rintro ⟨hpX, q, ⟨hq, hqX⟩, hqp⟩
      exact ⟨(hsat q p hqX hqp).mp hq, hpX⟩
  · have hprop := (C.toChain.gaf07_proper_G47 0 (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47
      P.toLocalChartPackets)).1
    have hcl : IsClosed {x : (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.E p)) ⁻¹' (C.toChain.finalBase_BAS 0 ∩ gaf07CircleRatio_G47 P.toLocalChartPackets) | (x
            : X) ∈ (interior (⋃ k : P.zero.finite_centres.toFinset,
                zspDomain_ZSP35 P.toLocalChartFamily P.zero k C.E))ᶜ} :=
      isOpen_interior.isClosed_compl.preimage continuous_subtype_val
    convert hprop.isClosedMap _ hcl using 1
    ext ⟨w, hw⟩
    constructor
    · rintro ⟨p, ⟨hp, hpX⟩, hpw⟩
      exact ⟨⟨p, hpX⟩, hp, Subtype.ext hpw⟩
    · rintro ⟨⟨p, hpX⟩, hp, hpw⟩
      exact ⟨p, ⟨hp, hpX⟩, congrArg Subtype.val hpw⟩

/-- **ZSP05, a closed zero component is the whole carrier** (B:6616–6617, zero part): on the final
family, an adjusted zero domain has empty boundary exactly when it is all of `M`. -/
theorem Gaf02ChainE.zsp05_closed_zero_component_ZSP35 {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    {Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw}
    (hεr : εr < 1 / 2) {k : P.zero.finite_centres.toFinset} :
    frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) = ∅ ↔
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ := by
  constructor
  · intro h0
    rw [(Ĉ.zsp02_domain_ZSP35 hεr k).2.2.1] at h0
    rcases (Ĉ.zsp02_types_ZSP35 hεr k).2.2.1 with ⟨-, hu⟩ | ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩
    · exact hu
    · obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E3)) (r := 1)).mpr zero_le_one
      exact (Set.eq_empty_iff_forall_notMem.mp h0 _ (e1.symm ⟨x, hx⟩).2).elim
    · exact (Set.eq_empty_iff_forall_notMem.mp h0 _ (e1.symm (0, 0)).2).elim
  · intro hu
    rw [hu, frontier_univ]

end DifferentialGeometry.Geometry.Collapse
