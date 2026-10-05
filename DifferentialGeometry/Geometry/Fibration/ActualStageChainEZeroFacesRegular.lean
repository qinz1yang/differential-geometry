import DifferentialGeometry.Geometry.Fibration.ActualStageChainEZeroFacesStandard
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceModelMatch

/-!
# Zero faces on the final family and the chain: regular-level structure and model match

Lane C14-ZSP35b; review 70 D70-5 (b), (c), (d).

* (c) `LocalChartPacketsC14Z.zero_face_model_boundary_ZSP35`: for every zero centre `c` and
  `a ∈ [1/5, 2]`, `{η_c ≤ a} = univ` (compact model), or an ambient partial diffeomorphism `Ψ` into
  the SELECTED model `N_c = P.N (zero c).model` carries `{η_c ≤ a}` onto a closed disc core
  `{r ≤ T₀}` of that model and the face `{η_c = a}` exactly onto its boundary level `{r = T₀}`
  (`r` the norm of the soul bundle of the selected model; kernel:
  `…SoulCoreSublevel.frontier_model_boundary_ZSP35`).
* (b) `Gaf02ChainE.zsp02_defining_global_ZSP35`: ZSP02's global defining function
  `H = ψ(η_k) + χ(η_k)(q − η_k)` of the adjusted zero domain is smooth on `M` and regular at `.4`,
  `Z_k = {H ≤ .4}`, `∂Z_k = {H = .4}`; and every standard smooth parametrization of the face is a
  DIFFEOMORPHISM onto `{H = .4}` with its natural `regularFiberChartedSpace`.

Consumer: `zsp02_face_defining_C14Z_ZSP35` (final family: strong face parametrization together
with the global defining function, nonzero differential on the face).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Topology.Manifold

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

/-- **The original zero faces are the boundaries of the SELECTED model's disc cores** (D70-5 (c),
final family): for `a ∈ [1/5, 2]`, `{η_c ≤ a} = univ`, or an ambient partial diffeomorphism into
the selected model `P.N (zero c).model` carries `{η_c ≤ a}` onto a disc core `{r ≤ T₀}` and the face
`{η_c = a}` exactly onto its boundary level `{r = T₀}`. -/
theorem LocalChartPacketsC14Z.zero_face_model_boundary_ZSP35
    (P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM) {c : X} (hc : c ∈ P.zero.centres) {a : ℝ} (ha : a ∈ Icc (1 / 5 : ℝ) 2) :
    {x | (P.zero.zero c hc).radial x ≤ a} = univ ∨
    ∃ Ψ : PartialDiffeomorph I3 I3 X (P.N (P.zero.zero c hc).model) ∞,
      ∃ r : P.N (P.zero.zero c hc).model → ℝ, ∃ T₀ : ℝ, 0 < T₀ ∧ Continuous r ∧
        {x | (P.zero.zero c hc).radial x ≤ a} ⊆ Ψ.source ∧
        Ψ '' {x | (P.zero.zero c hc).radial x ≤ a} = {y | r y ≤ T₀} ∧
        Ψ '' {x | (P.zero.zero c hc).radial x = a} = {y | r y = T₀} := by
  have hfr := (P.zero_sublevel_regular_FAMZ hc ha).1
  have hA := P.isClosed_zero_sublevel_FAMZ hc a
  rcases P.zero_sublevel_types c hc a ha with h | h | h | h | h
  · exact Or.inl h.1
  all_goals right
  · obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, hfA, -⟩ :=
      h.frontier_model_boundary_ZSP35 hA
    exact ⟨Ψ, _, T₀, hT₀, continuous_discCoreRadius_of_isContMDiffRiemannianBundle D, hAs, hΨA,
      hfr ▸ hfA⟩
  · obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, hfA, -⟩ :=
      h.frontier_model_boundary_ZSP35 hA
    exact ⟨Ψ, _, T₀, hT₀, continuous_discCoreRadius_of_isContMDiffRiemannianBundle D, hAs, hΨA,
      hfr ▸ hfA⟩
  · obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
      hT₀, Ψ, hAs, hΨA, hfA, -⟩ := h.frontier_model_boundary_ZSP35 hA
    exact ⟨Ψ, _, T₀, hT₀, continuous_discCoreRadius_of_isContMDiffRiemannianBundle D, hAs, hΨA,
      hfr ▸ hfA⟩
  · obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀,
      hT₀, Ψ, hAs, hΨA, hfA, -⟩ := h.frontier_model_boundary_ZSP35 hA
    exact ⟨Ψ, _, T₀, hT₀, continuous_discCoreRadius_of_isContMDiffRiemannianBundle D, hAs, hΨA,
      hfr ▸ hfA⟩

/-- **ZSP02's adjusted faces and the natural regular-level structure** (D70-5 (b)): the global
defining function `H = ψ(η_k) + χ(η_k)(q − η_k)` (`q = ℓ ∘ E + .4`) of the adjusted zero domain is
smooth on `M` and regular at `.4`, `Z_k = {H ≤ .4}`, `∂Z_k = {H = .4}`, and EVERY smooth embedding
of the standard `S²` (resp. `T²`) onto `∂Z_k` corestricts to a DIFFEOMORPHISM onto `{H = .4}` with
its natural `regularFiberChartedSpace`. -/
theorem Gaf02ChainE.zsp02_defining_global_ZSP35
    {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T
      V vs ζ Λz} (Ĉ : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hεr : εr < 1 / 2)
    (k : P.zero.finite_centres.toFinset) :
    ∃ (hH : ContMDiff I3 𝓘(ℝ,
        ℝ) ∞ (fun z => (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp
            k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))))
      (hreg : ∀ x, (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E x) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)) = 2 / 5 →
        Surjective (mfderiv I3 𝓘(ℝ,
            ℝ) (fun z => (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp
                k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) x)),
      {z | (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) ≤ 2 / 5} =
                  zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      {z | (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) = 2 / 5} =
                  zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      (∀ f : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ f →
        range f = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E →
          letI := regularFiberChartedSpace (fun z => (zspPsi_ZSP35 ((P.zero.zero k.1
              ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) (2 / 5) hH hreg
          ∃ Θ : Diffeomorph (𝓡 2) 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)
            GC.GraphManifold.ClosureSphere.{0} {z : X // (zspPsi_ZSP35 ((P.zero.zero k.1
                ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) = 2 / 5} ∞,
            ∀ t, (Θ t).val = f t) ∧
      (∀ f : Torus → X, IsSmoothEmbedding torusModel I3 ∞ f →
        range f = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E →
          letI := regularFiberChartedSpace (fun z => (zspPsi_ZSP35 ((P.zero.zero k.1
              ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) (2 / 5) hH hreg
          ∃ Θ : Diffeomorph torusModel 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)
            Torus {z : X // (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp
                k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) = 2 / 5} ∞,
            ∀ t, (Θ t).val = f t) := by
  obtain ⟨hf, hF, hδ₀, hZE, ⟨Hd, hHd, hder⟩, he⟩ := Ĉ.zsp02_inputs_ZSP35
  have hH := (contMDiff_zspH0_ZSP35 P.zero k).add
    (contMDiff_zspK_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hf)
  have heq : (fun z =>
      zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        1 * (zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
            (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) =
      fun z => (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z)) := by
    funext z
    rw [one_mul]
  have hreg : ∀ x, (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E x) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x)) = 2 / 5 →
      Surjective (mfderiv I3 𝓘(ℝ,
          ℝ) (fun z => (zspPsi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp
              k.2)).radial z) +
          zspChi_ZSP35 ((P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
            (zspQCLM_ZSP35 P.toLocalChartFamily P.zero k (Ĉ.E z) + 2 / 5 -
              (P.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) x) := fun x hx =>
                  by
    have h1 := zsp_level_transversal_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hf hF hδ₀ (hZE k)
      hHd hder hεr (τ := 1) ⟨zero_le_one, le_rfl⟩ (p := x) (by rw [one_mul]; exact hx)
    rw [heq] at h1
    exact h1
  obtain ⟨hsub, hlev⟩ := zsp_sublevel_eq_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E hδ₀ (hZE k) he
  have hd2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) =
      Module.finrank ℝ (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) := by simp
  have hdt : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) := by simp
  exact ⟨hH, hreg, hsub, hlev,
    fun f hfe hr => regularLevel_diffeomorph_of_param_ZSP35 _ (2 / 5) hH hreg hfe
      (hr.trans hlev.symm) hd2,
    fun f hfe hr => regularLevel_diffeomorph_of_param_ZSP35 _ (2 / 5) hH hreg hfe
      (hr.trans hlev.symm) hdt⟩


/-- **Consumer: the strong zero faces of a chain on the final family with their defining function.**
Every adjusted face is empty (`Z_k = M`) or the exact image of a smooth embedding of `S²` or `T²`,
and the global defining function of `Z_k` is smooth with nonzero differential on the face. -/
theorem zsp02_face_defining_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (Ĉ : Gaf02ChainE P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw)
    (hεr : εr < 1 / 2) (k : P.zero.finite_centres.toFinset) :
    ((zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = ∅ ∧
        zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E = univ) ∨
      (∃ f : GC.GraphManifold.ClosureSphere.{0} → X, IsSmoothEmbedding (𝓡 2) I3 ∞ f ∧
        range f = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E) ∨
      (∃ f : Torus → X, IsSmoothEmbedding torusModel I3 ∞ f ∧
        range f = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E)) ∧
    ∃ H : X → ℝ, ContMDiff I3 𝓘(ℝ, ℝ) ∞ H ∧
      {z | H z ≤ 2 / 5} = zspDomain_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      {z | H z = 2 / 5} = zspFace_ZSP35 P.toLocalChartFamily P.zero k Ĉ.E ∧
      ∀ x, H x = 2 / 5 → mfderiv I3 𝓘(ℝ, ℝ) H x ≠ 0 := by
  obtain ⟨hH, hreg, hsub, hlev, -, -⟩ := Ĉ.zsp02_defining_global_ZSP35 hεr k
  refine ⟨Ĉ.zsp02_face_standard_param_ZSP35 hεr k, _, hH, hsub, hlev, fun x hx h0 => ?_⟩
  obtain ⟨v, hv⟩ := hreg x hx 1
  rw [h0] at hv
  exact absurd (show (0 : ℝ) = 1 from hv) zero_ne_one

end DifferentialGeometry.Geometry.Collapse
