import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesStandard

/-!
# FC35, the zero-domain extraction, on `Gaf02ChainE` over the complete closed family

Lane C14-ROWS-S. Blueprint `master207B.tex`, FC35 (`found:fibration-zero-extraction`,
B:6216–6236). ZSP02 (B:6374) defines its domains "exactly with FC35's core branch", so FC35 is
ZSP02's strong row `Gaf02ChainE.zsp02_row_strong_ZSP35` read clause by clause; the only new step
is the model clause "diffeomorphic to the corresponding LC80 models": the LPA05/LFR54 type
predicate of the original sublevel `{η_k ≤ .4}` (an ambient partial diffeomorphism onto the disc
core of the selected model, or the whole closed model) is transported to `Z_k` itself along the
ambient diffeomorphism `Ψ` of (ZH) (`zeroSublevelType_image_RWS`).

* `partialDiffeomorph_image_diffeomorph_RWS`, `pointSoulCoreSublevel_image_RWS`,
  `circleSoulCoreSublevel_image_RWS`, `projectiveSoulCoreSublevel_image_RWS`,
  `kleinSoulCoreSublevel_image_RWS`, `compactModelSublevel_image_RWS`,
  `zeroSublevelType_image_RWS`: the type predicates are invariant under ambient diffeomorphisms.
* `Gaf02ChainE.fc35_row_RWS`: FC35's row (every clause; `e ≤ 1/1000` is KL 14.4's small-error
  restriction used for the radii `.38`, `.42`).

Consumer: `Gaf02ChainE.fc35_centre_mem_interior_RWS` (each centre is interior to its zero domain,
on the producer's bound `εr < 1/4`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

section Transport

variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [TopologicalSpace N]
  [ChartedSpace E3 N]

/-- Precomposing a partial diffeomorphism with the inverse of an ambient diffeomorphism `Ψ`:
`Ψ '' A` lies in the new source and has the same image as `A`. -/
theorem partialDiffeomorph_image_diffeomorph_RWS (Ψ : M ≃ₘ⟮I3, I3⟯ M)
    (Ψ' : PartialDiffeomorph I3 I3 M N ∞) {A : Set M} (hA : A ⊆ Ψ'.source) :
    Ψ '' A ⊆ (Ψ.symm.toPartialDiffeomorph.trans Ψ').source ∧
      (Ψ.symm.toPartialDiffeomorph.trans Ψ') '' (Ψ '' A) = Ψ' '' A := by
  have hap : ∀ a, (Ψ.symm.toPartialDiffeomorph.trans Ψ') (Ψ a) = Ψ' a := fun a => by
    change Ψ' (Ψ.symm (Ψ a)) = Ψ' a
    rw [Ψ.symm_apply_apply]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    change Ψ.symm (Ψ a) ∈ Ψ'.source
    rw [Ψ.symm_apply_apply]
    exact hA ha
  · rw [image_image]
    exact image_congr fun a _ => hap a

/-- `D³` cores are invariant under ambient diffeomorphisms. -/
theorem pointSoulCoreSublevel_image_RWS (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M}
    (h : PointSoulCoreSublevel N A) : PointSoulCoreSublevel N (Ψ '' A) := by
  obtain ⟨F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀, hT₀, Ψ', hs, hi, hr⟩ := h
  obtain ⟨hs', hi'⟩ := partialDiffeomorph_image_diffeomorph_RWS Ψ Ψ' hs
  exact ⟨F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀, hT₀,
    Ψ.symm.toPartialDiffeomorph.trans Ψ', hs', hi'.trans hi, hr⟩

/-- Solid-torus cores are invariant under ambient diffeomorphisms. -/
theorem circleSoulCoreSublevel_image_RWS (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M}
    (h : CircleSoulCoreSublevel N A) : CircleSoulCoreSublevel N (Ψ '' A) := by
  obtain ⟨F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀, hT₀, Ψ', hs, hi, hr⟩ := h
  obtain ⟨hs', hi'⟩ := partialDiffeomorph_image_diffeomorph_RWS Ψ Ψ' hs
  exact ⟨F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀, hT₀,
    Ψ.symm.toPartialDiffeomorph.trans Ψ', hs', hi'.trans hi, hr⟩

/-- `ℝP³ ∖ int D³` cores are invariant under ambient diffeomorphisms. -/
theorem projectiveSoulCoreSublevel_image_RWS (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M}
    (h : ProjectiveSoulCoreSublevel N A) : ProjectiveSoulCoreSublevel N (Ψ '' A) := by
  obtain ⟨B, j1, j2, j3, j4, j5, j6, F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀,
    hT₀, Ψ', hs, hi, hr⟩ := h
  obtain ⟨hs', hi'⟩ := partialDiffeomorph_image_diffeomorph_RWS Ψ Ψ' hs
  exact ⟨B, j1, j2, j3, j4, j5, j6, F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀,
    hT₀, Ψ.symm.toPartialDiffeomorph.trans Ψ', hs', hi'.trans hi, hr⟩

/-- `D(o(K))` cores are invariant under ambient diffeomorphisms. -/
theorem kleinSoulCoreSublevel_image_RWS (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M}
    (h : KleinSoulCoreSublevel N A) : KleinSoulCoreSublevel N (Ψ '' A) := by
  obtain ⟨B, j1, j2, j3, j4, j5, j6, F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀,
    hT₀, Ψ', hs, hi, hr⟩ := h
  obtain ⟨hs', hi'⟩ := partialDiffeomorph_image_diffeomorph_RWS Ψ Ψ' hs
  exact ⟨B, j1, j2, j3, j4, j5, j6, F, i1, i2, i3, V, i4, i5, i6, i7, i8, i9, i10, D, hd, T₀,
    hT₀, Ψ.symm.toPartialDiffeomorph.trans Ψ', hs', hi'.trans hi, hr⟩

/-- The closed-model alternative is invariant under ambient diffeomorphisms. -/
theorem compactModelSublevel_image_RWS [IsManifold I3 ∞ M] {oM : ManifoldOrientation I3 M 3}
    (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M} (h : CompactModelSublevel oM N A) :
    CompactModelSublevel oM N (Ψ '' A) := by
  obtain ⟨hA, hrest⟩ := h
  refine ⟨?_, hrest⟩
  rw [hA]
  exact image_univ_of_surjective Ψ.surjective

/-- **The LPA05/LFR54 type of a zero sublevel is invariant under ambient diffeomorphisms**: the
five alternatives (closed model of LFR53's four types, `D³`, solid torus, `ℝP³ ∖ int D³`,
`D(o(K))`) of `A` hold for `Ψ '' A`, with the same model `N`. -/
theorem zeroSublevelType_image_RWS [IsManifold I3 ∞ M] {oM : ManifoldOrientation I3 M 3}
    (Ψ : M ≃ₘ⟮I3, I3⟯ M) {A : Set M}
    (h : CompactModelSublevel oM N A ∨ PointSoulCoreSublevel N A ∨ CircleSoulCoreSublevel N A ∨
      ProjectiveSoulCoreSublevel N A ∨ KleinSoulCoreSublevel N A) :
    CompactModelSublevel oM N (Ψ '' A) ∨ PointSoulCoreSublevel N (Ψ '' A) ∨
      CircleSoulCoreSublevel N (Ψ '' A) ∨ ProjectiveSoulCoreSublevel N (Ψ '' A) ∨
      KleinSoulCoreSublevel N (Ψ '' A) := by
  rcases h with h | h | h | h | h
  · exact Or.inl (compactModelSublevel_image_RWS Ψ h)
  · exact Or.inr (Or.inl (pointSoulCoreSublevel_image_RWS Ψ h))
  · exact Or.inr (Or.inr (Or.inl (circleSoulCoreSublevel_image_RWS Ψ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (projectiveSoulCoreSublevel_image_RWS Ψ h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (kleinSoulCoreSublevel_image_RWS Ψ h))))

end Transport

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
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}

/-- **FC35, the zero-domain extraction** (B:6216–6236), on a chain `Ĉ` over the complete closed
family, `E = Ĉ.E`, with LC29's radial bound `εr < 1/2` and KL 14.4's small-error restriction
`e ≤ 1/1000`. For every zero index `k` (centre `c_k = p_k`, radius `R_k`, zero block
`(x'_k, x''_k) = (u_k, v_k)` of `E`):
1. `Z_k` is the core ball `B(p_k, .35R_k)` together with the adjusted marker sublevel
   `x''_k ≥ .9R_k`, `x'_k/x''_k ≤ .4`;
2. `Z_k` is compact, and distinct `Z_k` are disjoint;
3. smooth boundary: `∂Z_k = E⁻¹{x''_k ≥ .9R_k, x'_k = .4x''_k}`, near it `x''_k > .99R_k` and
   `x'_k/x''_k − .4` is a smooth defining function of `Z_k` with nonzero differential on `∂Z_k`;
   `∂Z_k` is empty (`Z_k = M`) or the image of a smooth embedding of `S²` or `T²`;
4. diffeomorphic to the corresponding LC80 model: an ambient diffeomorphism carries the selected
   original sublevel `{η_k ≤ .4}` onto `Z_k` (its level onto `∂Z_k`), and `Z_k` itself is the
   whole closed model (LFR53 type) or is carried by an ambient partial diffeomorphism onto the
   disc core of the selected model `P.N` that is `D³`, a solid torus, `ℝP³ ∖ int D³` (twisted
   interval bundle over `ℝP²`) or `D(o(K))` (twisted interval bundle over the Klein bottle);
5. `B̄(p_k, .38R_k) ⊆ int Z_k` and `Z_k ⊆ B(p_k, .42R_k)`. -/
theorem Gaf02ChainE.fc35_row_RWS
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (he : e ≤ 1 / 1000) (k : P.zero.finite_centres.toFinset) :
    zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E =
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
            (35 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∪
          {p | 9 / 10 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius ≤
              (Ĉ.E p (.inr (.inr (.inr (.inl k))))).snd ∧
            ((Ĉ.E p (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
              (Ĉ.E p (.inr (.inr (.inr (.inl k))))).snd ≤ 2 / 5} ∧
      IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∀ k' : P.zero.finite_centres.toFinset, k ≠ k' →
        Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E)) ∧
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) =
        zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      (∃ O : Set X, IsOpen O ∧ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆ O ∧
        (∀ z ∈ O, 99 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius <
            (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd ∧
          ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
            (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
              (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ∧
          (z ∈ zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ↔
            ((Ĉ.E z (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
              (Ĉ.E z (.inr (.inr (.inr (.inl k))))).snd - 2 / 5 ≤ 0)) ∧
        ∀ z ∈ zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E, mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ)
          (fun y => ((Ĉ.E y (.inr (.inr (.inr (.inl k))))).fst : ℝ²) 0 /
            (Ĉ.E y (.inr (.inr (.inr (.inl k))))).snd - 2 / 5) z ≠ 0) ∧
      ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
        (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
      (∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
          zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (CompactModelSublevel oM (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        PointSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        CircleSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        ProjectiveSoulCoreSublevel
          (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        KleinSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (38 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (42 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) := by
  obtain ⟨⟨hrow, hdisj, hZB⟩, hstd⟩ := Ĉ.zsp02_row_strong_ZSP35 hεr
  obtain ⟨hcpt, ⟨Ψ, hΨ1, hΨ2⟩, hfr, -, -, hdef, htype, -⟩ := hrow k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  refine ⟨?_, hcpt, fun k' hkk => hdisj k k' hkk, hfr, hdef, hstd k, ⟨Ψ, hΨ1, hΨ2⟩, ?_,
    (hZB he k).1, (hZB he k).2⟩
  · unfold zspDomain_ZSP35
    congr 1
    ext p
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      have hv : 0 < (Ĉ.E p (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
      exact ⟨h1, (div_le_iff₀ hv).mpr h2⟩
    · rintro ⟨h1, h2⟩
      have hv : 0 < (Ĉ.E p (.inr (.inr (.inr (.inl k))))).snd := by nlinarith
      exact ⟨h1, (div_le_iff₀ hv).mp h2⟩
  · rw [← hΨ1]
    exact zeroSublevelType_image_RWS Ψ htype

/-- **Consumer: the centre of every zero domain is interior to it** (FC35's `.38` ball), with the
producer's radial bound `εr < 1/4` and `e ≤ 1/1000`; distinct zero domains are disjoint. -/
theorem Gaf02ChainE.fc35_centre_mem_interior_RWS
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 4) (he : e ≤ 1 / 1000) (k : P.zero.finite_centres.toFinset) :
    (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ∈
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      ∀ k' : P.zero.finite_centres.toFinset, k ≠ k' →
        (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ∉
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E := by
  obtain ⟨-, -, hdisj, -, -, -, -, -, h38, -⟩ := Ĉ.fc35_row_RWS (by linarith) he k
  have hR := (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hc : (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ∈
      interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) :=
    h38 (mem_closedBall_self (by positivity))
  exact ⟨hc, fun k' hkk hk' =>
    Set.disjoint_left.mp (hdisj k' hkk) (interior_subset hc) hk'⟩

end DifferentialGeometry.Geometry.Collapse
