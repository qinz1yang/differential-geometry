import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictECBCF2K

/-!
# BCF02, step five: closedness of the edge piece at open base endpoints (kernel)

External draft 61 §6.2, step five; review 68 A3 (D68-4) and the ENTRY premise of A5 (D68-6);
blueprint `master207B.tex`, FDC02 (B:7246–7283), GAF06 (B:6008–6040), EDP02's height step
(B:6800–6820).

The closedness argument is written, as review 68 §2.6 asks, as a FINITE UNION of closed sets: with
`m_i = v_i ∘ π₂ ∘ E`, `w_i = u_i ∘ π₂ ∘ E`, `R_i = ρ_i`,
`P_e = ⋃_{i ∈ I_e^B} C_i`, `C_i = M₂ ∩ V ∩ {m_i = R_i} ∩ {|w_i| ≤ 4ΔR_i}`,
where `⊆` is the base description of `P_e` and `⊇` is the re-entry: a point of `C_i` satisfies, by
the limit inputs below, the ORIGINAL hypotheses of (Repl_∂), whose strict replacement index puts it
back into `P_e` through the (ENTRY) premise (strict coordinates at some `j` ⟹ `x ∈ P_e`; an honest
premise of the kernel, to be discharged by the actual BASES binding — never `q ∈ X₂` as a premise).

* `isClosed_marker_union_BCF2K` (topological kernel, any space): finite index set, `m_i, w_i`
  continuous on the closed set `M`, `V` closed, base + re-entry ⟹ `P = ⋃ C_i` and `P` closed;
  `isCompact_marker_union_BCF2K`: `M` compact ⟹ `P` compact.
* `bcf02_marker_division_BCF2K` (A3's (LIM)): `m = R`, the (ERR) errors on both block entries,
  `|w| ≤ 4ΔR`, `ε = c₃ρ_q/R < 1`, `ε(1 + 4.01Δ) ≤ .01Δ` ⟹ `|1 − ζ| < ε`, `|ηζ| < 4Δ + ε`, `ζ > 0`,
  `|η| < 4.01Δ` (division by `ζ` only after the denominator is controlled).
* `bcf02_lim_budget_BCF2K`: `ρ_q ≤ 1.01R`, `c₃ ≤ 1/1000`, `Δ ≥ 2` ⟹ (LIM) (`1.001c₃ < Δ` is NOT
  used).
* `bcf02_height_EZ_BCF2K` (EZ, scalar): with the SAME chain's scale slot `s` and `E'` block value
  `A` (`T = A/s`): `s ≤ (1 + c₃)ρ`, `|A − ρtκ| < c₃ρ`, `κ > 1 − β`, `T ≤ 4Δ` ⟹ `t < 4.01Δ`
  (`s` is never replaced by `ρ`).
* `LocalPacketsOnB.bcf02_limit_inputs_BCF2K`: at a point with `m_i = R_i`, `|w_i| ≤ 4ΔR_i`, (AM0),
  (ERR): `ζ_i > 0` (AM0 first), `d(q, i) ≤ 14ΔR_i` (closed-support localization
  `tsupport_edgeB_cutoff_subset_BAUGA`), `q ∈ U_i`, `|η_i(q)| < 4.01Δ` (LIM). No `q ∈ B₂ / W₂`.
* `LocalPacketsOnBFRZ.bcf02_isClosed_edgePiece_BCF2K`: on the final boundary family over
  `(W°, d_ĝ)`, with EGP04's early constants: the edge piece `P` described by (base) and (ENTRY)
  inside closed `M₂, V` (`M₂`'s original-coordinate consequences, (EZ) at marker points of `V`) is
  the finite union, closed, and compact when `M₂` is.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ## The finite-union closedness kernel (review 68 §2.6) -/

/-- **Closedness as a finite union** (topological kernel): for a finite index set `I`, functions
`m_i, w_i` continuous on a closed set `M`, a closed set `V`, and a set `P` with the base description
(`x ∈ P` ⟹ `x ∈ M ∩ V` and `m_i(x) = R_i`, `|w_i(x)| < cR_i` for some `i ∈ I`) and the re-entry
(`x ∈ M ∩ V`, `m_i(x) = R_i`, `|w_i(x)| ≤ cR_i` ⟹ `x ∈ P`), `P` is the finite union of the closed
sets `M ∩ V ∩ {m_i = R_i} ∩ {|w_i| ≤ cR_i}`; in particular `P` is closed. -/
theorem isClosed_marker_union_BCF2K {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) {M V P : Set X} (hM : IsClosed M) (hV : IsClosed V) {m w : ι → X → ℝ}
    {R : ι → ℝ} {c : ℝ} (hm : ∀ i ∈ I, ContinuousOn (m i) M) (hw : ∀ i ∈ I, ContinuousOn (w i) M)
    (hbase : ∀ x ∈ P, x ∈ M ∧ x ∈ V ∧ ∃ i ∈ I, m i x = R i ∧ |w i x| < c * R i)
    (hre : ∀ x ∈ M, x ∈ V → ∀ i ∈ I, m i x = R i → |w i x| ≤ c * R i → x ∈ P) :
    P = ⋃ i ∈ I, M ∩ V ∩ {x | m i x = R i} ∩ {x | |w i x| ≤ c * R i} ∧ IsClosed P := by
  have heq : P = ⋃ i ∈ I, M ∩ V ∩ {x | m i x = R i} ∩ {x | |w i x| ≤ c * R i} := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, exists_prop]
    constructor
    · intro hx
      obtain ⟨hxM, hxV, i, hi, hmi, hwi⟩ := hbase x hx
      exact ⟨i, hi, ⟨⟨hxM, hxV⟩, hmi⟩, hwi.le⟩
    · rintro ⟨i, hi, ⟨⟨hxM, hxV⟩, hmi⟩, hwi⟩
      exact hre x hxM hxV i hi hmi hwi
  refine ⟨heq, ?_⟩
  rw [heq]
  refine hI.isClosed_biUnion fun i hi => ?_
  have h1 : IsClosed (M ∩ m i ⁻¹' {R i}) :=
    (hm i hi).preimage_isClosed_of_isClosed hM isClosed_singleton
  have h2 : IsClosed (M ∩ (fun x => |w i x|) ⁻¹' Iic (c * R i)) :=
    (continuous_abs.comp_continuousOn (hw i hi)).preimage_isClosed_of_isClosed hM isClosed_Iic
  have hset : M ∩ V ∩ {x | m i x = R i} ∩ {x | |w i x| ≤ c * R i} =
      (M ∩ m i ⁻¹' {R i}) ∩ (M ∩ (fun x => |w i x|) ⁻¹' Iic (c * R i)) ∩ V := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_singleton_iff, mem_Iic]
    tauto
  rw [hset]
  exact (h1.inter h2).inter hV

/-- **Compactness of the finite union**: under the hypotheses of `isClosed_marker_union_BCF2K`, a
compact `M` makes `P` compact (closed in the compact `M`; not "a closed subset of an open base"). -/
theorem isCompact_marker_union_BCF2K {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) {M V P : Set X} (hMc : IsCompact M) (hM : IsClosed M) (hV : IsClosed V)
    {m w : ι → X → ℝ} {R : ι → ℝ} {c : ℝ} (hm : ∀ i ∈ I, ContinuousOn (m i) M)
    (hw : ∀ i ∈ I, ContinuousOn (w i) M)
    (hbase : ∀ x ∈ P, x ∈ M ∧ x ∈ V ∧ ∃ i ∈ I, m i x = R i ∧ |w i x| < c * R i)
    (hre : ∀ x ∈ M, x ∈ V → ∀ i ∈ I, m i x = R i → |w i x| ≤ c * R i → x ∈ P) :
    IsCompact P :=
  hMc.of_isClosed_subset (isClosed_marker_union_BCF2K hI hM hV hm hw hbase hre).2
    fun x hx => (hbase x hx).1

/-! ## Scalar kernels: (LIM), its budget, (EZ) -/

/-- **The marker-division estimate (LIM)** (review 68, A3): a block with exact marker `m = R`,
errors `|m − Rζ| < c₃ρ_q`, `|w − Rηζ| < c₃ρ_q` and weak vector bound `|w| ≤ 4ΔR`; with
`ε = c₃ρ_q/R`, `ε < 1` and `ε(1 + 4.01Δ) ≤ .01Δ`: `|1 − ζ| < ε`, `|ηζ| < 4Δ + ε`, `ζ > 0` and
`|η| < 4.01Δ`. -/
theorem bcf02_marker_division_BCF2K {Δ R ρq c₃ η ζ m w : ℝ} (hΔ : 0 < Δ) (hR : 0 < R)
    (hm : m = R) (hv : |m - R * ζ| < c₃ * ρq) (hu : |w - R * (η * ζ)| < c₃ * ρq)
    (hw : |w| ≤ 4 * Δ * R) (hlim1 : c₃ * ρq / R < 1)
    (hlim2 : c₃ * ρq / R * (1 + 401 / 100 * Δ) ≤ Δ / 100) :
    |1 - ζ| < c₃ * ρq / R ∧ |η * ζ| < 4 * Δ + c₃ * ρq / R ∧ 0 < ζ ∧ |η| < 401 / 100 * Δ := by
  set ε := c₃ * ρq / R with hε
  have hεR : ε * R = c₃ * ρq := by rw [hε]; field_simp
  have h1 : |1 - ζ| < ε := by
    have he : m - R * ζ = R * (1 - ζ) := by rw [hm]; ring
    rw [he, abs_mul, abs_of_pos hR] at hv
    by_contra h
    push Not at h
    nlinarith
  have h2 : |η * ζ| < 4 * Δ + ε := by
    have h3 := abs_sub_abs_le_abs_sub (R * (η * ζ)) w
    rw [abs_sub_comm, abs_mul, abs_of_pos hR] at h3
    by_contra h
    push Not at h
    nlinarith
  have hζ : 1 - ε < ζ := by linarith [(abs_lt.mp h1).2]
  have hζ0 : 0 < ζ := by linarith
  refine ⟨h1, h2, hζ0, ?_⟩
  rw [abs_mul, abs_of_pos hζ0] at h2
  -- `|η|ζ < 4Δ + ε ≤ 4.01Δ(1 − ε) < 4.01Δζ`
  have h4 : 4 * Δ + ε ≤ 401 / 100 * Δ * (1 - ε) := by nlinarith
  have h5 : 401 / 100 * Δ * (1 - ε) < 401 / 100 * Δ * ζ := by
    have := mul_lt_mul_of_pos_left hζ (by positivity : (0 : ℝ) < 401 / 100 * Δ)
    linarith
  by_contra h
  push Not at h
  have h6 : 401 / 100 * Δ * ζ ≤ |η| * ζ := mul_le_mul_of_nonneg_right h hζ0.le
  linarith

/-- **The budget for (LIM)** (review 68, A3): `ρ_q ≤ 1.01R` (from the closed-support localization
`d(q, i) ≤ 14ΔR_i` and slow variation), `c₃ ≤ 1/1000`, `Δ ≥ 2` give `ε = c₃ρ_q/R < 1` and
`ε(1 + 4.01Δ) ≤ .01Δ`. -/
theorem bcf02_lim_budget_BCF2K {Δ R ρq c₃ : ℝ} (hΔ : 2 ≤ Δ) (hR : 0 < R) (hρq : 0 < ρq)
    (hρ : ρq ≤ 101 / 100 * R) (hc₃ : c₃ ≤ 1 / 1000) :
    c₃ * ρq / R < 1 ∧ c₃ * ρq / R * (1 + 401 / 100 * Δ) ≤ Δ / 100 := by
  have hε : c₃ * ρq / R ≤ 101 / 100000 := by
    rw [div_le_iff₀ hR]
    rcases le_or_gt 0 c₃ with h | h
    · have h1 : c₃ * ρq ≤ c₃ * (101 / 100 * R) := mul_le_mul_of_nonneg_left hρ h
      have h2 : c₃ * (101 / 100 * R) ≤ 1 / 1000 * (101 / 100 * R) :=
        mul_le_mul_of_nonneg_right hc₃ (by positivity)
      linarith
    · have h1 : c₃ * ρq < 0 := mul_neg_of_neg_of_pos h hρq
      have h2 : 0 < 101 / 100000 * R := by positivity
      linarith
  refine ⟨by linarith, ?_⟩
  have hpos : 0 ≤ 1 + 401 / 100 * Δ := by linarith
  have h1 : c₃ * ρq / R * (1 + 401 / 100 * Δ) ≤ 101 / 100000 * (1 + 401 / 100 * Δ) :=
    mul_le_mul_of_nonneg_right hε hpos
  linarith

/-- **The height estimate (EZ), scalar form** (review 68, A3): with the SAME chain's scale slot `s`
and `E'` block value `A` (`T = A/s`), `0 < s ≤ (1 + c₃)ρ`, `|A − ρtκ| < c₃ρ` (the original
weak-edge vector `ρtκ`, `κ = h(t/Δ)χ(Σζ)`), `κ > 1 − β`, `t ≥ 0`, `β, c₃ ≤ 1/1000`, `Δ ≥ 1` and
`T ≤ 4Δ` give `t < 4.01Δ`. -/
theorem bcf02_height_EZ_BCF2K {Δ ρx s A t κ c₃ β : ℝ} (hΔ : 1 ≤ Δ) (hρ : 0 < ρx) (hs : 0 < s)
    (hsρ : s ≤ (1 + c₃) * ρx) (hA : |A - ρx * t * κ| < c₃ * ρx) (ht : 0 ≤ t) (hκ : 1 - β < κ)
    (hβ : β ≤ 1 / 1000) (hc₃ : c₃ ≤ 1 / 1000) (hT : A / s ≤ 4 * Δ) : t < 401 / 100 * Δ := by
  have hAs : A ≤ 4 * Δ * s := (div_le_iff₀ hs).mp hT
  have h1 : 4 * Δ * s ≤ 4 * Δ * ((1 + c₃) * ρx) :=
    mul_le_mul_of_nonneg_left hsρ (by positivity)
  have h2 : ρx * t * κ < A + c₃ * ρx := by linarith [(abs_lt.mp hA).1]
  have h3 : ρx * (t * κ) < ρx * (4 * Δ * (1 + c₃) + c₃) := by nlinarith
  have h4 : t * κ < 4 * Δ * (1 + c₃) + c₃ := lt_of_mul_lt_mul_left h3 hρ.le
  have h5 : t * (999 / 1000) ≤ t * κ := mul_le_mul_of_nonneg_left (by linarith) ht
  have h6 : 4 * Δ * c₃ ≤ 4 * Δ * (1 / 1000) := mul_le_mul_of_nonneg_left hc₃ (by positivity)
  by_contra h
  push Not at h
  have h7 : 401 / 100 * Δ * (999 / 1000) ≤ t * (999 / 1000) :=
    mul_le_mul_of_nonneg_right h (by norm_num)
  linarith

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **FDC02's limit inputs on the revised edge charts** (GAF06 with `≤ 4Δ`, review 68 A3): at a
point `q` where the final edge block of `i` has the exact marker `v_i(π₂E q) = ρ_i` and the WEAK
vector bound `|u_i(π₂E q)| ≤ 4Δρ_i`, with (ERR) on both entries and (AM0) at `(i, q)`: (AM0) first
gives `ζ_i(q) > 0`; the closed-support localization gives `d(q, i) ≤ 14Δρ_i`, so `q ∈ U_i`; slow
variation gives `ρ(q) ≤ 1.01ρ_i`, the (LIM) budget, and the marker division `|η_i(q)| < 4.01Δ`
(`Δ ≥ 2`, `100ΔΛ ≤ 10⁻⁸`, `μ, τ ≤ 1/100`, `c₃ ≤ 1/1000`). No `q ∈ B₂ / W₂` is assumed. -/
theorem LocalPacketsOnB.bcf02_limit_inputs_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {Y : Type} (E : X → Y) (π₂ : Y → Y) (u v : X → Y → ℝ) {c₃ : ℝ}
    (hΔ : 2 ≤ Δ) (hΛ : 0 ≤ Λ) (hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hc₃ : c₃ ≤ 1 / 1000) {i : X} (hi : i ∈ F.edgeB.centres) {q : X}
    (hERRu : |u i (π₂ (E q)) -
      ρ i * (F.edgeB.coord_BAUGA i q * F.edgeB.cutoff_BAUGA i q)| < c₃ * ρ q)
    (hERRv : |v i (π₂ (E q)) - ρ i * F.edgeB.cutoff_BAUGA i q| < c₃ * ρ q)
    (hAM0 : F.edgeB.cutoff_BAUGA i q = 0 → |v i (π₂ (E q))| ≤ ρ i / 32)
    (hm : v i (π₂ (E q)) = ρ i) (hw : |u i (π₂ (E q))| ≤ 4 * Δ * ρ i) :
    0 < F.edgeB.cutoff_BAUGA i q ∧ dist q i ≤ 14 * Δ * ρ i ∧ q ∈ ball i (100 * Δ * ρ i) ∧
      |F.edgeB.coord_BAUGA i q| < 401 / 100 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hri := hρ i
  have hrq := hρ q
  -- (AM0) first: the original cutoff is positive
  have hζ0 : F.edgeB.cutoff_BAUGA i q ≠ 0 := by
    intro h0
    have h := hAM0 h0
    rw [hm, abs_of_pos hri] at h
    linarith
  have hζ : 0 < F.edgeB.cutoff_BAUGA i q :=
    lt_of_le_of_ne (F.edgeB.cutoff_mem_Icc_BAUGA hΔ0 i q).1 (Ne.symm hζ0)
  -- the closed-support localization recovers the chart domain
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by linarith
  obtain ⟨hsupp, -, -⟩ := F.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ0 hμ hτ hΔΛ hi
  have hqi : dist q i ≤ 14 * Δ * ρ i :=
    mem_closedBall.mp (hsupp (subset_tsupport _ (Function.mem_support.mpr hζ0)))
  have hball : q ∈ ball i (100 * Δ * ρ i) := by
    rw [mem_ball]
    have := mul_pos hΔ0 hri
    linarith
  -- slow variation: `ρ(q) ≤ 1.01ρ_i`
  have hρq : ρ q ≤ 101 / 100 * ρ i := by
    have h1 := F.lipschitz_scale.dist_le_mul q i
    rw [Real.coe_toNNReal _ hΛ, Real.dist_eq] at h1
    have h2 : Λ * dist q i ≤ Λ * (14 * Δ * ρ i) := mul_le_mul_of_nonneg_left hqi hΛ
    have h3 : Δ * Λ * ρ i ≤ 1 / 10 ^ 10 * ρ i :=
      mul_le_mul_of_nonneg_right (by linarith) hri.le
    have h4 : Λ * (14 * Δ * ρ i) = 14 * (Δ * Λ * ρ i) := by ring
    linarith [(abs_le.mp h1).2]
  obtain ⟨hl1, hl2⟩ := bcf02_lim_budget_BCF2K hΔ hri hrq hρq hc₃
  obtain ⟨-, -, -, hη⟩ := bcf02_marker_division_BCF2K hΔ0 hri hm hERRv hERRu hw hl1 hl2
  exact ⟨hζ, hqi, hball, hη⟩

end Generic

/-! ## The closedness of the edge piece on the final boundary family -/

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **BCF02, step five: the edge piece is closed (and compact)** — kernel on the final boundary
family over `(W°, d_ĝ)`. For `Δ ≥ 2`, EGP04's early constants `σ, η` (depending on `Δ` only) exist
such that: for every final family with the step-one–three bounds, `c₃ ≤ 1/1000` and EGP04's tail
requests, every map `E` with (ERR) on both entries of the edge blocks, (FM) and (AM0), and closed
sets `M₂, V` (the blocks `m_i = v_i ∘ π₂ ∘ E`, `w_i = u_i ∘ π₂ ∘ E` continuous on `M₂`; `M₂`'s
original-coordinate consequences `D ≥ 35`, outside the `.38`-zero balls and the slim regions; (EZ)
at the marker points of `V`), a set `P` with the base description (`x ∈ P` ⟹ `x ∈ M₂ ∩ V`,
`m_i(x) = ρ_i`, `|w_i(x)| < 4Δρ_i` for some `i ∈ I_e^B`) and (ENTRY) (`x ∈ M₂ ∩ V`, `m_j(x) = ρ_j`,
`|w_j(x)| < 3Δρ_j` for some `j` ⟹ `x ∈ P`) is the finite union
`⋃_i M₂ ∩ V ∩ {m_i = ρ_i} ∩ {|w_i| ≤ 4Δρ_i}`, closed, and compact when `M₂` is. -/
theorem LocalPacketsOnBFRZ.bcf02_isClosed_edgePiece_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
    ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
    ∀ {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz c₃ : ℝ},
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 → c₃ ≤ 1 / 1000 →
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 →
      1000000 * Δ * Λ < 1 / 100000 → μ * Δ < 1 / 10000 →
    ∀ (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3),
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      {Y : Type} (E : W.pieceInterior ⊤ → Y) (π₂ : Y → Y) (u v : W.pieceInterior ⊤ → Y → ℝ),
      (∀ j ∈ F.edgeB.centres, ∀ x, |u j (π₂ (E x)) -
        ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x)| < c₃ * ρ x) →
      (∀ j ∈ F.edgeB.centres, ∀ x, |v j (π₂ (E x)) - ρ j * F.edgeB.cutoff_BAUGA j x| < c₃ * ρ x) →
      (∀ j ∈ F.edgeB.centres, ∀ x, dist x j < 100 * Δ * ρ j →
        |F.edgeB.coord_BAUGA j x| < 6 * Δ → F.edgeB.smoothing x / ρ x < 6 * Δ →
          v j (π₂ (E x)) = ρ j) →
      (∀ j ∈ F.edgeB.centres, ∀ x, F.edgeB.cutoff_BAUGA j x = 0 →
        |v j (π₂ (E x))| ≤ ρ j / 32) →
    ∀ (M₂ Vh P : Set (W.pieceInterior ⊤)), IsClosed M₂ → IsClosed Vh →
      (∀ j ∈ F.edgeB.centres, ContinuousOn (fun x => v j (π₂ (E x))) M₂) →
      (∀ j ∈ F.edgeB.centres, ContinuousOn (fun x => u j (π₂ (E x))) M₂) →
      (∀ q ∈ M₂, ENNReal.ofReal 35 ≤ distanceToBoundary W g q ∧
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) ∧
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|)) →
      (∀ x ∈ Vh, ∀ i ∈ F.edgeB.centres, v i (π₂ (E x)) = ρ i →
        |u i (π₂ (E x))| ≤ 4 * Δ * ρ i → F.edgeB.smoothing x / ρ x < 401 / 100 * Δ) →
      (∀ x ∈ P, x ∈ M₂ ∧ x ∈ Vh ∧ ∃ i ∈ F.edgeB.centres, v i (π₂ (E x)) = ρ i ∧
        |u i (π₂ (E x))| < 4 * Δ * ρ i) →
      (∀ x ∈ M₂, x ∈ Vh → (∃ j ∈ F.edgeB.centres, v j (π₂ (E x)) = ρ j ∧
        |u j (π₂ (E x))| < 3 * Δ * ρ j) → x ∈ P) →
      P = ⋃ i ∈ F.edgeB.centres, M₂ ∩ Vh ∩ {x | v i (π₂ (E x)) = ρ i} ∩
          {x | |u i (π₂ (E x))| ≤ 4 * Δ * ρ i} ∧
        IsClosed P ∧ (IsCompact M₂ → IsCompact P) := by
  obtain ⟨σ, hσ, hσ1, η, hη, hR⟩ := LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro W _ g ĝ hle ρ hρ n hbcp Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz c₃
    hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hc₃ hσL hbη h3b hbH hLΛ hμΔ oM
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F Y E π₂ u v hERRu hERRv hFM hAM0 M₂ Vh P hM hV hmc hwc hM₂ hEZ hbase hentry
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hre : ∀ x ∈ M₂, x ∈ Vh → ∀ i ∈ F.edgeB.centres, v i (π₂ (E x)) = ρ i →
      |u i (π₂ (E x))| ≤ 4 * Δ * ρ i → x ∈ P := by
    intro x hx hxV i hi hmi hwi
    obtain ⟨-, -, hball, hηi⟩ := F.toLocalPacketsOnB.bcf02_limit_inputs_BCF2K E π₂ u v hΔ hΛ hlam
      (by linarith) (by linarith) hc₃ hi (hERRu i hi x) (hERRv i hi x) (hAM0 i hi x) hmi hwi
    have ht := hEZ x hxV i hi hmi hwi
    obtain ⟨h35, hZ, hS⟩ := hM₂ x hx
    obtain ⟨j, hj, -, -, hvj, huj⟩ := hR W g ĝ hle ρ hρ hbcp hΛ hμ hτ hσc hn hT hσs hσs1 hb hs
      hβ2 (by linarith) hσL hbη h3b hbH hLΛ hμΔ oM F E π₂ u v hERRu hFM i hi x hball hηi.le
      ht.le h35 hZ hS
    refine hentry x hx hxV ⟨j, hj, hvj, ?_⟩
    rw [div_lt_iff₀ (hρ j)] at huj
    linarith
  obtain ⟨heq, hcl⟩ := isClosed_marker_union_BCF2K F.edgeB.finite_centres hM hV hmc hwc hbase hre
  exact ⟨heq, hcl, fun hMc => isCompact_marker_union_BCF2K F.edgeB.finite_centres hMc hM hV hmc
    hwc hbase hre⟩

end Carrier

end DifferentialGeometry.Geometry.Collapse
