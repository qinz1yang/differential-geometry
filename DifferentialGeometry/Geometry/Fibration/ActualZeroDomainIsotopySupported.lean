import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainIsotopy
import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.RegularSublevelIsotopy

/-!
# ZSP02, the SUPPORTED isotopy: identity off a compact part of the zero ball

Lane C14-ZSP35c. Blueprint `master207B.tex`, ZSP02 (B:6374–6479), strengthened as the boundary
carrier version needs it (B:9532–9544, B:10537: the isotopy is extended by the identity near
`∂M`; review 72 D72-2: the flow fixes every original zero ball). The earlier kernel
`zsp02_kernel_ZSP35` gives only ONE diffeomorphism (FC34b's band transport, no support control).
Here the same family (ZH) `h_τ = ψ(η_k) + τχ(η_k)(q − η_k)` is followed by the tree's Kernel C
(`DifferentialGeometry.Analysis.ODE.exists_isotopy_regularSublevel_smooth`, the compactly
supported flow of a time lift) applied to the moving LEVEL `{h_{s(t)} = .4}` (`s` =
`Real.smoothTransition`); its levels lie in `|η_k − .4| < 1/500`, so the flow is the identity off
a compact subset of the thin annulus `{.39 < η_k < .41}`. The sublevels follow from the levels by
a clopen argument along the isotopy (`image_sublevel_of_level_isotopy_ZSP35`).

* `level_sign_of_isotopy_ZSP35`, `image_sublevel_of_level_isotopy_ZSP35` (generic, topological);
* `zsp02_supported_isotopy_kernel_ZSP35`: for every `f` with ZSP01's (ZE) and the derivative bound
  (the hypotheses of `zsp02_kernel_ZSP35`): a jointly smooth `Φ : ℝ → X ≃ₘ X`, `Φ 0 = id`, the
  identity off a compact `K' ⊆ {.39 < η_k < .41}`, `Φ 1 {η_k ≤ .4} = Z_k`,
  `Φ 1 {η_k = .4} =` (ZF), and in metric form the identity on `B̄(c_k, (.39 − e)R_k)` and off
  `B(c_k, (.41 + e)R_k)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {M : Type*} [TopologicalSpace M]

/-- **The sign of a moving function along an isotopy that carries its zero level** (generic): if
`Φ` is jointly continuous, `Φ 0 = id`, every `Φ t` injective, and `Φ t` carries the zero level of
`Ψ (0, ·)` onto that of `Ψ (t, ·)`, then along every orbit `Ψ (t, Φ t x)` vanishes exactly when
`Ψ (0, x)` does, and is negative exactly when `Ψ (0, x)` is (the set of negative times is
clopen in `ℝ`). -/
theorem level_sign_of_isotopy_ZSP35 (Ψ : ℝ × M → ℝ) (hΨ : Continuous Ψ) (Φ : ℝ → M → M)
    (hΦ : Continuous fun q : ℝ × M => Φ q.1 q.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hinj : ∀ t, Injective (Φ t))
    (hlev : ∀ t, Φ t '' {x | Ψ (0, x) = 0} = {x | Ψ (t, x) = 0}) (t : ℝ) (x : M) :
    (Ψ (t, Φ t x) = 0 ↔ Ψ (0, x) = 0) ∧ (Ψ (t, Φ t x) < 0 ↔ Ψ (0, x) < 0) := by
  have hzero : ∀ σ, Ψ (σ, Φ σ x) = 0 ↔ Ψ (0, x) = 0 := by
    intro σ
    constructor
    · intro h
      have hm : Φ σ x ∈ Φ σ '' {x | Ψ (0, x) = 0} := by
        rw [hlev σ]
        exact h
      obtain ⟨y, hy, hyx⟩ := hm
      rw [← hinj σ hyx]
      exact hy
    · intro h
      have hm : Φ σ x ∈ Φ σ '' {x | Ψ (0, x) = 0} := mem_image_of_mem _ h
      rw [hlev σ] at hm
      exact hm
  refine ⟨hzero t, ?_⟩
  by_cases h0 : Ψ (0, x) = 0
  · rw [(hzero t).mpr h0, h0]
  have hc : Continuous fun σ : ℝ => Ψ (σ, Φ σ x) :=
    hΨ.comp (continuous_id.prodMk (hΦ.comp (continuous_id.prodMk continuous_const)))
  have heq : {σ : ℝ | Ψ (σ, Φ σ x) < 0} = {σ : ℝ | Ψ (σ, Φ σ x) ≤ 0} := by
    ext σ
    exact ⟨fun h => show Ψ (σ, Φ σ x) ≤ 0 from le_of_lt h,
      fun h => lt_of_le_of_ne h fun h' => h0 ((hzero σ).mp h')⟩
  have hA : IsClopen {σ : ℝ | Ψ (σ, Φ σ x) < 0} := by
    refine ⟨?_, isOpen_lt hc continuous_const⟩
    rw [heq]
    exact isClosed_le hc continuous_const
  have h00 : (Ψ (0, Φ 0 x) < 0 ↔ Ψ (0, x) < 0) := by rw [hΦ0]
  rcases isClopen_iff.mp hA with h | h
  · have ht : t ∉ {σ : ℝ | Ψ (σ, Φ σ x) < 0} := by
      rw [h]
      exact notMem_empty t
    have h0' : (0 : ℝ) ∉ {σ : ℝ | Ψ (σ, Φ σ x) < 0} := by
      rw [h]
      exact notMem_empty 0
    exact iff_of_false ht (fun hx => h0' (h00.mpr hx))
  · have ht : t ∈ {σ : ℝ | Ψ (σ, Φ σ x) < 0} := by
      rw [h]
      exact mem_univ t
    have h0' : (0 : ℝ) ∈ {σ : ℝ | Ψ (σ, Φ σ x) < 0} := by
      rw [h]
      exact mem_univ 0
    exact iff_of_true ht (h00.mp h0')

/-- **Sublevels follow levels along an isotopy** (generic): under the hypotheses of
`level_sign_of_isotopy_ZSP35` and surjectivity of every `Φ t`, `Φ t` carries the closed sublevel
`{Ψ (0, ·) ≤ 0}` onto `{Ψ (t, ·) ≤ 0}`. -/
theorem image_sublevel_of_level_isotopy_ZSP35 (Ψ : ℝ × M → ℝ) (hΨ : Continuous Ψ)
    (Φ : ℝ → M → M) (hΦ : Continuous fun q : ℝ × M => Φ q.1 q.2) (hΦ0 : ∀ x, Φ 0 x = x)
    (hinj : ∀ t, Injective (Φ t)) (hsurj : ∀ t, Surjective (Φ t))
    (hlev : ∀ t, Φ t '' {x | Ψ (0, x) = 0} = {x | Ψ (t, x) = 0}) (t : ℝ) :
    Φ t '' {x | Ψ (0, x) ≤ 0} = {x | Ψ (t, x) ≤ 0} := by
  have hle : ∀ x, Ψ (t, Φ t x) ≤ 0 ↔ Ψ (0, x) ≤ 0 := by
    intro x
    obtain ⟨h1, h2⟩ := level_sign_of_isotopy_ZSP35 Ψ hΨ Φ hΦ hΦ0 hinj hlev t x
    rw [le_iff_lt_or_eq, le_iff_lt_or_eq, h1, h2]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hle x).mpr hx
  · intro hy
    obtain ⟨x, rfl⟩ := hsurj t y
    exact ⟨x, (hle x).mp hy, rfl⟩

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The moving level function of (ZH) along `s = Real.smoothTransition`:
`(t, x) ↦ h_{s(t)}(x) − .4` with `h_τ = ψ(η_k) + τχ(η_k)(q − η_k)`, `q = ℓ ∘ f + .4`. -/
def zspIsoFamily_ZSP35 (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) : ℝ × X → ℝ :=
  fun q => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) +
    Real.smoothTransition q.1 *
      (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) *
        (zspQCLM_ZSP35 L Z k (f q.2) + 2 / 5 -
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2)) - 2 / 5

/-- **ZSP02, the supported isotopy (kernel form)**: under the hypotheses of `zsp02_kernel_ZSP35`
there are a compact `K'` inside the thin annulus `{.39 < η_k < .41}` and a jointly smooth family
`Φ : ℝ → X ≃ₘ X` of diffeomorphisms with `Φ 0 = id`, `Φ t = id` off `K'` for every `t`,
`Φ 1 {η_k ≤ .4} = Z_k` and `Φ 1 {η_k = .4} =` (ZF). -/
theorem zsp02_supported_isotopy_kernel_ZSP35
    (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
    (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) ∞ (cgpGlobalMap L Z))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) (he : e < 1 / 40) :
    ∃ (K' : Set X) (Φ : ℝ → X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X),
      IsCompact K' ∧
      (∀ x ∈ K', 39 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) ∞ (fun q : ℝ × X => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      Φ 1 '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35 L Z k f ∧
      Φ 1 '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        zspFace_ZSP35 L Z k f := by
  obtain ⟨hηc, -, -, -, -⟩ := zsp_radial_facts_ZSP35 Z k
  obtain ⟨hsub, hlev1⟩ := zsp_sublevel_eq_ZSP35 L Z k f hδ₀ hZE he
  have hh0 := contMDiff_zspH0_ZSP35 Z k
  have hk := contMDiff_zspK_ZSP35 L Z k f hf
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, ℝ) ∞ (zspIsoFamily_ZSP35 L Z k f) :=
    ((hh0.comp contMDiff_snd).add
      ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).mul
        (hk.comp contMDiff_snd))).sub contMDiff_const
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ × X => (1 : ℝ)) :=
    contMDiff_const
  have hτ : ∀ t : ℝ, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hlevq : ∀ q : ℝ × X, zspIsoFamily_ZSP35 L Z k f q = 0 →
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) +
        Real.smoothTransition q.1 *
          (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) *
            (zspQCLM_ZSP35 L Z k (f q.2) + 2 / 5 -
              (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2)) = 2 / 5 := by
    intro q hq
    unfold zspIsoFamily_ZSP35 at hq
    linarith
  -- the moving level lies in the thin annulus
  have hloc : ∀ q : ℝ × X, zspIsoFamily_ZSP35 L Z k f q = 0 →
      |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2 - 2 / 5| < 1 / 500 := by
    intro q hq
    refine zsp_level_location_ZSP35 (hτ q.1) (fun h1 h2 => ?_) (hlevq q hq)
    have hqc := zsp_q_close_ZSP35 L Z k f hZE (p := q.2) ⟨by linarith, by linarith⟩
    linarith
  have htrans : ∀ q : ℝ × X, zspIsoFamily_ZSP35 L Z k f q = 0 →
      0 ≤ (fun _ : ℝ × X => (1 : ℝ)) q →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => zspIsoFamily_ZSP35 L Z k f (q.1, y)) q.2) := by
    rintro q hq -
    have hsurj := zsp_level_transversal_ZSP35 L Z k f hf hF hδ₀ hZE hHd hder hεr (hτ q.1)
      (hlevq q hq)
    have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
        zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          Real.smoothTransition q.1 *
            (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) q.2 :=
      ((hh0.add (contMDiff_const.mul hk)) q.2).mdifferentiableAt (by simp)
    have hm := (hd.hasMFDerivAt.sub (hasMFDerivAt_const (I := 𝓘(ℝ, E3)) (I' := 𝓘(ℝ, ℝ))
      (2 / 5 : ℝ) q.2)).mfderiv
    have heq : (fun y => zspIsoFamily_ZSP35 L Z k f (q.1, y)) = (fun z =>
        zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          Real.smoothTransition q.1 *
            (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) -
        fun _ => (2 / 5 : ℝ) := rfl
    rw [heq, hm]
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    refine ⟨v, ?_⟩
    exact (sub_zero _).trans hv
  have hS : IsCompact ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Icc (398 / 1000 : ℝ) (402 / 1000)) := (isClosed_Icc.preimage hηc).isCompact
  have hN : IsOpen ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Ioo (39 / 100 : ℝ) (41 / 100)) := isOpen_Ioo.preimage hηc
  have hSN : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Icc (398 / 1000 : ℝ) (402 / 1000) ⊆
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
        Ioo (39 / 100 : ℝ) (41 / 100) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hWS : ∀ q : ℝ × X, zspIsoFamily_ZSP35 L Z k f q = 0 →
      0 ≤ (fun _ : ℝ × X => (1 : ℝ)) q →
      q.2 ∈ (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
        Icc (398 / 1000 : ℝ) (402 / 1000) := by
    rintro q hq -
    obtain ⟨h1, h2⟩ := abs_lt.mp (hloc q hq)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨K', Φ₂, hK', hK'N, hΦs, hΦ0, hΦid, hΦW, -⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_isotopy_regularSublevel_smooth hΨ hB htrans
      (fun q _ h1 => absurd h1 one_ne_zero) hS hWS hN hSN
  have hΦc : Continuous fun q : ℝ × X => Φ₂ 0 q.1 q.2 :=
    (hΦs.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd)).continuous
  have hΦ0' : ∀ x, Φ₂ 0 0 x = x := fun x => by rw [hΦ0]; rfl
  have hlevt : ∀ t, Φ₂ 0 t '' {x | zspIsoFamily_ZSP35 L Z k f (0, x) = 0} =
      {x | zspIsoFamily_ZSP35 L Z k f (t, x) = 0} := by
    intro t
    have h := hΦW 0 t
    simp only [zero_le_one, and_true] at h
    exact h
  have hsubt := image_sublevel_of_level_isotopy_ZSP35 (zspIsoFamily_ZSP35 L Z k f) hΨ.continuous
    (fun t => Φ₂ 0 t) hΦc hΦ0' (fun t => (Φ₂ 0 t).injective) (fun t => (Φ₂ 0 t).surjective)
    hlevt 1
  have hs0 : ∀ x, zspIsoFamily_ZSP35 L Z k f (0, x) =
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) - 2 / 5 := by
    intro x
    simp only [zspIsoFamily_ZSP35, Real.smoothTransition.zero, zero_mul, add_zero]
  have hs1 : ∀ x, zspIsoFamily_ZSP35 L Z k f (1, x) =
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) *
          (zspQCLM_ZSP35 L Z k (f x) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) - 2 / 5 := by
    intro x
    simp only [zspIsoFamily_ZSP35, Real.smoothTransition.one, one_mul]
  refine ⟨K', fun t => Φ₂ 0 t, hK', fun x hx => hK'N hx,
    hΦs.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd),
    hΦ0', fun t x hx => hΦid 0 t x hx, ?_, ?_⟩
  · rw [← hsub]
    have h1 : {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        {x | zspIsoFamily_ZSP35 L Z k f (0, x) ≤ 0} := by
      ext x
      simp only [mem_ofPred_eq, hs0, sub_nonpos]
      exact zspPsi_le_iff_ZSP35.symm
    have h2 : {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) ≤ 2 / 5} =
        {x | zspIsoFamily_ZSP35 L Z k f (1, x) ≤ 0} := by
      ext x
      simp only [mem_ofPred_eq, hs1, sub_nonpos]
    rw [h1, h2]
    exact hsubt
  · rw [← hlev1]
    have h1 : {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        {x | zspIsoFamily_ZSP35 L Z k f (0, x) = 0} := by
      ext x
      simp only [mem_ofPred_eq, hs0, sub_eq_zero]
      exact zspPsi_eq_iff_ZSP35.symm
    have h2 : {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35 L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) = 2 / 5} =
        {x | zspIsoFamily_ZSP35 L Z k f (1, x) = 0} := by
      ext x
      simp only [mem_ofPred_eq, hs1, sub_eq_zero]
    rw [h1, h2]
    exact hlevt 1

end DifferentialGeometry.Geometry.Collapse
