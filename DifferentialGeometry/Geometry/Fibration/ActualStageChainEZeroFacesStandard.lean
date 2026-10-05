import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroDomains
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroFacesStandard

/-!
# ZSP02 on `Gaf02ChainE`: the adjusted zero faces with standard smooth parametrizations

Lane C14-ZSP35b, review 70 D70-5 (d) and D70-7. Strong form of the face-type clause of
`Gaf02ChainE.zsp02_types_ZSP35` (homeomorphism types, kept): the adjusted face
`∂Z_k = E⁻¹{v_k ≥ .9R_k, u_k = .4v_k}` is empty with `Z_k = M`, or the exact image of a smooth
embedding of the standard `S² = ClosureSphere` or `T² = Circle × Circle`. It is the ambient
diffeomorphism of (ZH) composed with the original face's parametrization, which restricts the
SELECTED LFR54 core model (`LocalChartPacketsC14Z.zero_face_standard_param_ZSP35`).

* `Gaf02ChainE.zsp02_face_standard_param_ZSP35`;
* `Gaf02ChainE.zsp02_row_strong_ZSP35`: ZSP02's row (`zsp02_row_ZSP35`) together with the standard
  smooth face parametrizations.

Consumer: `zsp02_faces_standard_C14Z_ZSP35` (the nonempty faces of distinct zero domains are
disjoint images of smooth embeddings of `S²` or `T²`).
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

/-- **ZSP02's adjusted faces, standard smooth parametrization** (D70-5 (d)): for every zero index
`k`, `∂Z_k = E⁻¹{v_k ≥ .9R_k, u_k = .4v_k}` is empty with `Z_k = M`, or the exact image of a smooth
embedding `ClosureSphere.{0} → M`, or of a smooth embedding `Torus → M`. -/
theorem Gaf02ChainE.zsp02_face_standard_param_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) :
    (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
      (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
        range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
      (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
        range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) := by
  have hk := (Set.Finite.mem_toFinset _).mp k.2
  have ha : (2 / 5 : ℝ) ∈ Icc (1 / 5 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  obtain ⟨-, ⟨Ψ, hΨ1, hΨ2⟩, -⟩ := Ĉ.zsp02_domain_ZSP35 hεr k
  rcases P.zero_face_standard_param_ZSP35 hk ha with ⟨hu, he⟩ | ⟨f, hf, hr⟩ | ⟨f, hf, hr⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [← hΨ2, he, image_empty]
    · rw [← hΨ1, hu]
      exact image_univ_of_surjective (f := (Ψ : X → X)) Ψ.surjective
  · refine Or.inr (Or.inl ⟨Ψ ∘ f,
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp _ _ f hf Ψ, ?_⟩)
    rw [range_comp, hr, hΨ2]
  · refine Or.inr (Or.inr ⟨Ψ ∘ f,
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_comp _ _ f hf Ψ, ?_⟩)
    rw [range_comp, hr, hΨ2]

/-- **ZSP02, the whole row in the strong form** (D70-7): `Gaf02ChainE.zsp02_row_ZSP35` (every
clause) together with the standard smooth parametrization of every adjusted face
(`Gaf02ChainE.zsp02_face_standard_param_ZSP35`). -/
theorem Gaf02ChainE.zsp02_row_strong_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    (    (∀ k : P.zero.finite_centres.toFinset,
      IsCompact (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      (∃ Ψ : X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X,
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
        Ψ '' {z | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
          zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      frontier (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) =
        zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          ((381 / 1000 - e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          ((402 / 1000 + e) * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∧
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
      (CompactModelSublevel oM (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        PointSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        CircleSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        ProjectiveSoulCoreSublevel
          (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5} ∨
        KleinSoulCoreSublevel (P.N (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).model)
          {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
      Nonempty (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
        {x | (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ≤ 2 / 5}) ∧
      ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
        Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ≃ₜ
          (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E).Nonempty →
        IsCompact (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
        IsConnected (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E))) ∧
    (∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspDomain_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E)) ∧
    (e ≤ 1 / 1000 → ∀ k : P.zero.finite_centres.toFinset,
      closedBall (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (38 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
        interior (zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∧
      zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ⊆
        ball (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
          (42 / 100 * (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius))) ∧
    ∀ k : P.zero.finite_centres.toFinset,
      (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
          zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
        (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) :=
  ⟨Ĉ.zsp02_row_ZSP35 hεr, fun k => Ĉ.zsp02_face_standard_param_ZSP35 hεr k⟩

/-- **Consumer: the standard zero faces of a chain on the final family.** Every nonempty adjusted
face is the exact image of a smooth embedding of `S²` or `T²`, and the faces of distinct zero
domains are disjoint. -/
theorem zsp02_faces_standard_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) :
    (∀ k : P.zero.finite_centres.toFinset,
      (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E).Nonempty →
        (∃ e : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
        (∃ e : Torus → X, IsSmoothEmbedding torusModel I3 ∞ e ∧
          range e = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
    ∀ k k' : P.zero.finite_centres.toFinset, k ≠ k' →
      Disjoint (zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)
        (zspFace_ZSP35 P.toLocalChartFamily P.zero k' Ĉ.E) := by
  obtain ⟨⟨hrow, hdisj, -⟩, hstd⟩ := Ĉ.zsp02_row_strong_ZSP35 hεr
  refine ⟨fun k hne => ?_, fun k k' hkk => ?_⟩
  · rcases hstd k with ⟨he, -⟩ | h | h
    · rw [he] at hne
      exact absurd hne not_nonempty_empty
    · exact Or.inl h
    · exact Or.inr h
  · rw [← (hrow k).2.2.1, ← (hrow k').2.2.1]
    exact (hdisj k k' hkk).mono ((hrow k).1.isClosed.frontier_subset)
      ((hrow k').1.isClosed.frontier_subset)

end DifferentialGeometry.Geometry.Collapse
