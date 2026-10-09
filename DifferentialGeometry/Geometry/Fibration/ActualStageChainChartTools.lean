import DifferentialGeometry.Geometry.Fibration.ActualStageChainRoughData
import DifferentialGeometry.Geometry.Fibration.GenericMarkedPatchChart
import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinatePPCoframe

/-!
# GAF02 BASES: shared tools for CGP06–CGP07 on the chain (circle / edge / slim charts)

Blueprint `master207B.tex`, CGP06 (B:4130), CGP07 (B:4176); external draft 59 §4, third to fifth
steps (D59-5); review 66 §5.4 (D66-7). Stage-independent pieces used by the per-stage chart modules
(`ActualStageChainChartCircle`, and the edge / slim ones):

* `clm_fderiv_of_left_inverse_BAS`: `π ∘ Φ = id` ⇒ `π ∘ DΦ = id` (the rough graph's own block).
* `retained_coordinate_of_pp_rescaled_BAS`: the plane's (PP) data at ONE reference `i` (onto `L`,
  normal error, orthogonal lower bound) and the rough graph's derivative error at the designated
  chart `j` give CGP06's `‖v‖ ≤ 2Ω‖π v‖` on `L` (bounded preimages rescaled from `ρ_i` to `ρ_j`;
  kernel `retained_coordinate_lower_bound_of_pp_BAS`).
* `exists_ball_extension_BAS`: a continuous map on an open ball extended to the whole space.
* `cfs15_hgraph_BAS`: a CFS15 output's local graph in CGP07's `hgraph` form at a cloud point.
* `Gaf02Chain.os_small_BAS`: GAF01's (OS) gives `8e_st(1 + Ω) ≤ 1`.
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

/-- `π ∘ Φ = id` gives `π ∘ DΦ = id`. -/
theorem clm_fderiv_of_left_inverse_BAS {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (pr : H →L[ℝ] E) {Φ : E → H} {a : E}
    (hΦ : DifferentiableAt ℝ Φ a) (hid : ∀ b, pr (Φ b) = b) (y : E) :
    pr (fderiv ℝ Φ a y) = y := by
  have h1 : HasFDerivAt (fun b => pr (Φ b)) (pr.comp (fderiv ℝ Φ a)) a :=
    pr.hasFDerivAt.comp a hΦ.hasFDerivAt
  have hfun : (fun b => pr (Φ b)) = fun b => b := funext hid
  rw [hfun] at h1
  have h2 := h1.unique (hasFDerivAt_id a)
  exact congrArg (fun L : E →L[ℝ] E => L y) h2


/-- **(PP) at a reference `i` ⇒ bounded preimages at the reference `j`, and CGP06's bound.** `A` is
the original derivative at the preimage, `ci = ρ(c_i)`, `cj = ρ(c_j)` the two reference scales; the
plane's (PP) data at `i` (onto `L`, normal error `e`, lower bound on the `Bf`-orthogonal complement
of the kernel), the rough graph's derivative error at `j` (`Tm = DΦ_j`, `pr Tm = I`, `‖Tm‖ ≤ Ω`,
`Aη = Dη_j`) and `8e(1+Ω) ≤ 1` give `‖v‖ ≤ 2Ω‖pr v‖` on `L`. -/
theorem retained_coordinate_of_pp_rescaled_BAS {V H E : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [FiniteDimensional ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : V →L[ℝ] H) (Bf : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hBpos : ∀ v, v ≠ 0 → 0 < Bf v v)
    (L : Submodule ℝ H) {ci cj e Ω : ℝ} (hci : 0 < ci) (hcj : 0 < cj) (he : 0 ≤ e)
    (hsurj : Surjective (L.orthogonalProjectionOnto.comp (ci⁻¹ • A)))
    (hnorm : ∀ v, ‖ci⁻¹ • A v - (L.orthogonalProjectionOnto.comp (ci⁻¹ • A) v : H)‖ ≤
      e * Real.sqrt (ci⁻¹ ^ 2 * Bf v v))
    (hlow : ∀ v, (∀ k, L.orthogonalProjectionOnto.comp (ci⁻¹ • A) k = 0 → Bf v k = 0) →
      1 / 2 * Real.sqrt (ci⁻¹ ^ 2 * Bf v v) ≤ ‖L.orthogonalProjectionOnto.comp (ci⁻¹ • A) v‖)
    (pr : H →L[ℝ] E) (hpr : ‖pr‖ ≤ 1) (Tm : E →L[ℝ] H) (hprT : ∀ y, pr (Tm y) = y)
    (hT : ∀ y, ‖Tm y‖ ≤ Ω * ‖y‖) (Aη : V →L[ℝ] E)
    (hrough : ∀ w, ‖cj⁻¹ • A w - Tm (Aη w)‖ ≤ e * Real.sqrt (cj⁻¹ ^ 2 * Bf w w))
    (hΩ : 1 ≤ Ω) (hsmall : 8 * e * (1 + Ω) ≤ 1) :
    ∀ v ∈ L, ‖v‖ ≤ 2 * Ω * ‖pr v‖ := by
  have hbp := exists_bounded_preimage_BAS Bf hBpos
    ((L.orthogonalProjectionOnto.comp (ci⁻¹ • A) : V →L[ℝ] L) : V →ₗ[ℝ] L) hsurj
    (fun w => Real.sqrt (ci⁻¹ ^ 2 * Bf w w)) (fun w hw => by
      have h := hlow w hw
      rw [ContinuousLinearMap.coe_coe]
      linarith)
  have hpre : ∀ v ∈ (L : Set H), ∃ w, ‖(cj⁻¹ • (A : V →ₗ[ℝ] H)) w - v‖ ≤ 2 * e * ‖v‖ ∧
      Real.sqrt (cj⁻¹ ^ 2 * Bf w w) ≤ 2 * ‖v‖ := by
    intro v hv
    obtain ⟨w', hw', hN'⟩ := hbp ⟨v, hv⟩
    have hPw : ((L.orthogonalProjectionOnto.comp (ci⁻¹ • A)) w' : H) = v := by
      have h := congrArg Subtype.val hw'
      exact h
    have hv' : ‖(⟨v, hv⟩ : L)‖ = ‖v‖ := rfl
    rw [hv'] at hN'
    refine ⟨(cj / ci) • w', ?_, ?_⟩
    · have hD : (cj⁻¹ • (A : V →ₗ[ℝ] H)) ((cj / ci) • w') = ci⁻¹ • A w' := by
        rw [LinearMap.smul_apply, map_smul, ContinuousLinearMap.coe_coe, smul_smul]
        congr 1
        field_simp
      rw [hD]
      have h1 := hnorm w'
      rw [hPw] at h1
      nlinarith
    · have hg : Bf ((cj / ci) • w') ((cj / ci) • w') = (cj / ci) ^ 2 * Bf w' w' := by
        rw [LinearMap.map_smul₂, map_smul, smul_eq_mul, smul_eq_mul]
        ring
      have hsc : cj⁻¹ ^ 2 * ((cj / ci) ^ 2 * Bf w' w') = ci⁻¹ ^ 2 * Bf w' w' := by
        field_simp
      rw [hg, hsc]
      exact hN'
  intro v hv
  refine retained_coordinate_lower_bound_of_pp_BAS (fun w => Real.sqrt (cj⁻¹ ^ 2 * Bf w w)) pr hpr
    Tm hprT hT (cj⁻¹ • (A : V →ₗ[ℝ] H)) (Aη : V →ₗ[ℝ] E) (fun w => ?_) (L : Set H) hpre hΩ he
    hsmall v hv
  rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe]
  exact hrough w

/-- Extension of a continuous map on an open ball to the whole space (`dite`), continuous on the
ball and equal to the map there. -/
theorem exists_ball_extension_BAS {E Y : Type*} [NormedAddCommGroup E] [TopologicalSpace Y]
    {r : ℝ} (y₀ : Y) (sec : ball (0 : E) r → Y) (hsec : Continuous sec) :
    ∃ secE : E → Y, ContinuousOn secE (ball 0 r) ∧
      ∀ b (hb : b ∈ ball (0 : E) r), secE b = sec ⟨b, hb⟩ := by
  classical
  refine ⟨fun b => if hb : b ∈ ball (0 : E) r then sec ⟨b, hb⟩ else y₀, ?_, fun b hb => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert hsec using 1
    funext b
    exact dite_eq_left b.2
  · exact dite_eq_left hb

/-- **The local graph of a CFS15 output in CGP07's `hgraph` form** at a cloud point `x`: with a
retained-coordinate lower bound `m` on `P x` (CGP06) above the native slope `ε/3` and
`dim P x = dim E`, the output's graph `g x` over `B(0, 4ε⁻¹r_x)` describes `Z ∩ B(x, 3ε⁻¹r_x)`. -/
theorem cfs15_hgraph_BAS {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [NormedAddCommGroup E] [NormedSpace ℝ E] {k K : ℕ} {ε cw : ℝ} {S T : Set H} {r : H → ℝ}
    {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) (u : H →L[ℝ] E) (x : S)
    {m : ℝ} (hm : ∀ v ∈ P x, m * ‖v‖ ≤ ‖u v‖) (hεm : ε / 3 < m)
    (hdim : Module.finrank ℝ (P x) = Module.finrank ℝ E) :
    ∃ (R₀ m' sl : ℝ) (L : Submodule ℝ H) (g : L → Lᗮ), (∀ v' ∈ L, m' * ‖v'‖ ≤ ‖u v'‖) ∧
      sl < m' ∧ Module.finrank ℝ L = Module.finrank ℝ E ∧ ContDiffOn ℝ ∞ g (ball 0 R₀) ∧
      (∀ t ∈ ball (0 : L) R₀, ‖fderiv ℝ g t‖ ≤ sl) ∧
      O.Z ∩ ball (x : H) (3 * ε⁻¹ * r x) =
        {z | ∃ t ∈ ball (0 : L) R₀, z = (x : H) + orthogonalCoordinateSum L (t, g t)} ∩
          ball (x : H) (3 * ε⁻¹ * r x) := by
  have hr : 0 < r x := O.radius_pos x x.2
  refine ⟨4 * ε⁻¹ * r x, m, ε / 3, P x, O.g x, hm, hεm, hdim, O.graph_smooth x,
    fun t ht => norm_fderiv_le_of_iteratedFDeriv_one_BPRE (O.g x) hr
      (O.graph_jets x t ht 1 (by omega)), O.graph_eq x⟩

variable {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

namespace Gaf02Chain


variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- (OS) gives the kernel's smallness `8e₀(1 + Ω) ≤ 1`. -/
theorem os_small_BAS {C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw}
    (R : Gaf02RoughData C) (st : Fin 3) : 8 * eg st * (1 + gafGraphOmega_BAS) ≤ 1 := by
  have hΩ := one_le_gafGraphOmega_BAS
  have he : 0 ≤ eg st := (C.numbers.1 st).2.2.2
  have h := (R.os st).2.2
  rw [lt_div_iff₀ (by positivity)] at h
  nlinarith [mul_nonneg he (sub_nonneg.mpr hΩ)]

end Gaf02Chain

end DifferentialGeometry.Geometry.Collapse
