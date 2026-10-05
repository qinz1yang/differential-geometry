import DifferentialGeometry.Geometry.Fibration.ActualZeroDomainIsotopySupported
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainIsotopyBGR

/-!
# ZSP02 on the boundary family (lane B-BCG-ROWS): ZSP02 supported isotopy (Kernel C) with the thin annulus compactness as input

GENERATED from `DifferentialGeometry/Geometry/Fibration/ActualZeroDomainIsotopySupported.lean` by `build-logs/scratch/B-BCG-ROWSb/gen_zsp02.py` (engine B-PORT-A's
`portlib2.py`). Closed family → boundary family (`LocalPacketsOnB`, `ZeroModelFamilyOn`, complete
σ-compact carrier); every ported declaration `x` ↦ `x_BGR`.
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

end Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}
  {Lmax τ γ vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The moving level function of (ZH) along `s = Real.smoothTransition`:
`(t, x) ↦ h_{s(t)}(x) − .4` with `h_τ = ψ(η_k) + τχ(η_k)(q − η_k)`, `q = ℓ ∘ f + .4`. -/
def zspIsoFamily_ZSP35_BGR (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) : ℝ × X → ℝ :=
  fun q => zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) +
    Real.smoothTransition q.1 *
      (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) *
        (zspQCLM_ZSP35_BGR L Z k (f q.2) + 2 / 5 -
          (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2)) - 2 / 5

/-- **ZSP02, the supported isotopy (kernel form)**: under the hypotheses of `zsp02_kernel_ZSP35`
there are a compact `K'` inside the thin annulus `{.39 < η_k < .41}` and a jointly smooth family
`Φ : ℝ → X ≃ₘ X` of diffeomorphisms with `Φ 0 = id`, `Φ t = id` off `K'` for every `t`,
`Φ 1 {η_k ≤ .4} = Z_k` and `Φ 1 {η_k = .4} =` (ZF). -/
theorem zsp02_supported_isotopy_kernel_ZSP35_BGR
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (k : Z.finite_centres.toFinset)
    (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞ f)
    (hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞ (cgpGlobalMap_BAUGP L Z))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100) (hder : ∀ p (W : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p W - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP L Z) p W‖ ≤
        Hd * Real.sqrt (g.inner p W W))
    (hεr : εr < 1 / 2) (he : e < 1 / 40)
    (hS : IsCompact ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Icc (398 / 1000 : ℝ) (402 / 1000))) :
    ∃ (K' : Set X) (Φ : ℝ → X ≃ₘ⟮𝓘(ℝ, E3), 𝓘(ℝ, E3)⟯ X),
      IsCompact K' ∧
      (∀ x ∈ K', 39 / 100 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x ∧
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x < 41 / 100) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, E3) ∞ (fun q : ℝ × X => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      Φ 1 '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        zspDomain_ZSP35_BGR L Z k f ∧
      Φ 1 '' {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        zspFace_ZSP35_BGR L Z k f := by
  obtain ⟨hηc, -, -, -, -⟩ := zsp_radial_facts_ZSP35_BGR Z k
  obtain ⟨hsub, hlev1⟩ := zsp_sublevel_eq_ZSP35_BGR L Z k f hδ₀ hZE he
  have hh0 := contMDiff_zspH0_ZSP35_BGR Z k
  have hk := contMDiff_zspK_ZSP35_BGR L Z k f hf
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, ℝ) ∞ (zspIsoFamily_ZSP35_BGR L Z k f) :=
    ((hh0.comp contMDiff_snd).add
      ((Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst).mul
        (hk.comp contMDiff_snd))).sub contMDiff_const
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E3)) 𝓘(ℝ, ℝ) ∞ (fun _ : ℝ × X => (1 : ℝ)) :=
    contMDiff_const
  have hτ : ∀ t : ℝ, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hlevq : ∀ q : ℝ × X, zspIsoFamily_ZSP35_BGR L Z k f q = 0 →
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) +
        Real.smoothTransition q.1 *
          (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2) *
            (zspQCLM_ZSP35_BGR L Z k (f q.2) + 2 / 5 -
              (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2)) = 2 / 5 := by
    intro q hq
    unfold zspIsoFamily_ZSP35_BGR at hq
    linarith
  -- the moving level lies in the thin annulus
  have hloc : ∀ q : ℝ × X, zspIsoFamily_ZSP35_BGR L Z k f q = 0 →
      |(Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial q.2 - 2 / 5| < 1 / 500 := by
    intro q hq
    refine zsp_level_location_ZSP35 (hτ q.1) (fun h1 h2 => ?_) (hlevq q hq)
    have hqc := zsp_q_close_ZSP35_BGR L Z k f hZE (p := q.2) ⟨by linarith, by linarith⟩
    linarith
  have htrans : ∀ q : ℝ × X, zspIsoFamily_ZSP35_BGR L Z k f q = 0 →
      0 ≤ (fun _ : ℝ × X => (1 : ℝ)) q →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun y => zspIsoFamily_ZSP35_BGR L Z k f (q.1, y)) q.2) := by
    rintro q hq -
    have hsurj := zsp_level_transversal_ZSP35_BGR L Z k f hf hF hδ₀ hZE hHd hder hεr (hτ q.1)
      (hlevq q hq)
    have hd : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (fun z =>
        zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          Real.smoothTransition q.1 *
            (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35_BGR L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) q.2 :=
      ((hh0.add (contMDiff_const.mul hk)) q.2).mdifferentiableAt (by simp)
    have hm := (hd.hasMFDerivAt.sub (hasMFDerivAt_const (I := 𝓘(ℝ, E3)) (I' := 𝓘(ℝ, ℝ))
      (2 / 5 : ℝ) q.2)).mfderiv
    have heq : (fun y => zspIsoFamily_ZSP35_BGR L Z k f (q.1, y)) = (fun z =>
        zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
          Real.smoothTransition q.1 *
            (zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
              (zspQCLM_ZSP35_BGR L Z k (f z) + 2 / 5 -
                (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z))) -
        fun _ => (2 / 5 : ℝ) := rfl
    rw [heq, hm]
    intro y
    obtain ⟨v, hv⟩ := hsurj y
    refine ⟨v, ?_⟩
    exact (sub_zero _).trans hv
  have hN : IsOpen ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Ioo (39 / 100 : ℝ) (41 / 100)) := isOpen_Ioo.preimage hηc
  have hSN : (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
      Icc (398 / 1000 : ℝ) (402 / 1000) ⊆
      (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial ⁻¹'
        Ioo (39 / 100 : ℝ) (41 / 100) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hWS : ∀ q : ℝ × X, zspIsoFamily_ZSP35_BGR L Z k f q = 0 →
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
  have hlevt : ∀ t, Φ₂ 0 t '' {x | zspIsoFamily_ZSP35_BGR L Z k f (0, x) = 0} =
      {x | zspIsoFamily_ZSP35_BGR L Z k f (t, x) = 0} := by
    intro t
    have h := hΦW 0 t
    simp only [zero_le_one, and_true] at h
    exact h
  have hsubt := image_sublevel_of_level_isotopy_ZSP35 (zspIsoFamily_ZSP35_BGR L Z k f) hΨ.continuous
    (fun t => Φ₂ 0 t) hΦc hΦ0' (fun t => (Φ₂ 0 t).injective) (fun t => (Φ₂ 0 t).surjective)
    hlevt 1
  have hs0 : ∀ x, zspIsoFamily_ZSP35_BGR L Z k f (0, x) =
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) - 2 / 5 := by
    intro x
    simp only [zspIsoFamily_ZSP35_BGR, Real.smoothTransition.zero, zero_mul, add_zero]
  have hs1 : ∀ x, zspIsoFamily_ZSP35_BGR L Z k f (1, x) =
      zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) *
          (zspQCLM_ZSP35_BGR L Z k (f x) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial x) - 2 / 5 := by
    intro x
    simp only [zspIsoFamily_ZSP35_BGR, Real.smoothTransition.one, one_mul]
  refine ⟨K', fun t => Φ₂ 0 t, hK', fun x hx => hK'N hx,
    hΦs.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd),
    hΦ0', fun t x hx => hΦid 0 t x hx, ?_, ?_⟩
  · rw [← hsub]
    have h1 : {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ≤ 2 / 5} =
        {x | zspIsoFamily_ZSP35_BGR L Z k f (0, x) ≤ 0} := by
      ext x
      simp only [mem_ofPred_eq, hs0, sub_nonpos]
      exact zspPsi_le_iff_ZSP35.symm
    have h2 : {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35_BGR L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) ≤ 2 / 5} =
        {x | zspIsoFamily_ZSP35_BGR L Z k f (1, x) ≤ 0} := by
      ext x
      simp only [mem_ofPred_eq, hs1, sub_nonpos]
    rw [h1, h2]
    exact hsubt
  · rw [← hlev1]
    have h1 : {z | (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z = 2 / 5} =
        {x | zspIsoFamily_ZSP35_BGR L Z k f (0, x) = 0} := by
      ext x
      simp only [mem_ofPred_eq, hs0, sub_eq_zero]
      exact zspPsi_eq_iff_ZSP35.symm
    have h2 : {z | zspPsi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) +
        zspChi_ZSP35 ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) *
          (zspQCLM_ZSP35_BGR L Z k (f z) + 2 / 5 -
            (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z) = 2 / 5} =
        {x | zspIsoFamily_ZSP35_BGR L Z k f (1, x) = 0} := by
      ext x
      simp only [mem_ofPred_eq, hs1, sub_eq_zero]
    rw [h1, h2]
    exact hlevt 1


end DifferentialGeometry.Geometry.Collapse
