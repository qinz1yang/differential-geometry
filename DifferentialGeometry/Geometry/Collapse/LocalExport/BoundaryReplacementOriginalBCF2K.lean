import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementStrictECBCF2KApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorCompletion

/-!
# BCF02: the E-free replacement and the edge piece through the BASES localization (kernel)

Lane BCF2-K, group G5a (toward the frozen `bcf02_pieces_BCF02`, compactness of `P_e`). The BASES
exit of the boundary chain (`BoundaryGaf02Bases`) states EDP02's (ELoc) — every point of `X₂` lies
in an ORIGINAL domain `{q ∈ U_i, |η_i| < 4.01Δ, t_B < 4.01Δ}` — so the closedness of the edge piece
can be run in ORIGINAL coordinates (the closed-side route of FDC02,
`fdc02_limit_original_inputs_C14`): the limit inequalities are weak, the E-free part of (Repl_∂)
returns a strict original index `j` (`|η_j| < 2Δ`), and an (ENTRY) clause of the BASES exit (EDP02's
threshold-5 step: an original point with `|η_j| ≤ 3.5Δ`, `t_B < 5Δ` and `T ≤ 4Δ` lies in `X₂`) puts
the limit back into the piece. The final-coordinate route (review 68 A3: AM0, LIM, EZ) is the one
the BASES producer uses to prove (ELoc) itself (`LocalPacketsOnB.bcf02_limit_inputs_BCF2K`).

* `isClosed_of_finite_cover_BCF2K` (topological): `P` described by a finite family of closed sets
  inside closed `M ∩ V` (base) with re-entry ⟹ `P` closed.
* `LocalPacketsOnB.isClosed_edgeOriginalDomain_BCF2K`: `{d(·, i) ≤ cρ_i, |η_i| ≤ a, t_B ≤ a}` is
  closed (`η_i` Lipschitz, `edgeB.smoothing` Lipschitz, `ρ` Lipschitz).
* `LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K`: the E-free (Repl_∂) on the final family
  (EGP04 instantiated): `∃ j ∈ I_e^B, q ∈ U_j, |η_j(q)| < 2Δ, ζ_j(q) = 1`.
* `LocalPacketsOnBFRZ.bcf02_isCompact_edgePiece_localized_BCF2K`: on `(W°, d_ĝ)`, a set `P` inside
  closed `M₂ ∩ V` with (ELoc) and (ENTRY), `M₂` with its original-coordinate consequences, is closed
  and compact (`M₂ ⊆ {D ≥ 35}`, compact by `isCompact_le_distanceToBoundary_BDRY1`).
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

/-- **Closedness from a finite closed cover with re-entry** (topological kernel): a finite index
set `I`, closed sets `M`, `V`, `A_i`, and a set `P` with the base description (`x ∈ P` ⟹
`x ∈ M ∩ V ∩ A_i` for some `i ∈ I`) and the re-entry (`x ∈ M ∩ V ∩ A_i` ⟹ `x ∈ P`):
`P = ⋃_i M ∩ V ∩ A_i` is closed. -/
theorem isClosed_of_finite_cover_BCF2K {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) {M V P : Set X} {A : ι → Set X} (hM : IsClosed M) (hV : IsClosed V)
    (hA : ∀ i ∈ I, IsClosed (A i)) (hbase : ∀ x ∈ P, x ∈ M ∧ x ∈ V ∧ ∃ i ∈ I, x ∈ A i)
    (hre : ∀ x ∈ M, x ∈ V → ∀ i ∈ I, x ∈ A i → x ∈ P) :
    P = ⋃ i ∈ I, M ∩ V ∩ A i ∧ IsClosed P := by
  have heq : P = ⋃ i ∈ I, M ∩ V ∩ A i := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨hxM, hxV, i, hi, hxA⟩ := hbase x hx
      exact ⟨i, hi, ⟨hxM, hxV⟩, hxA⟩
    · rintro ⟨i, hi, ⟨hxM, hxV⟩, hxA⟩
      exact hre x hxM hxV i hi hxA
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hI.isClosed_biUnion fun i hi => (hM.inter hV).inter (hA i hi)

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **The original edge domain is closed**: for a revised edge centre `i`,
`{p | d(p, i) ≤ cρ_i, |η_i(p)| ≤ a, t_B(p) ≤ a}` is closed. -/
theorem LocalPacketsOnB.isClosed_edgeOriginalDomain_BCF2K
    (F : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      U₁ U₂ Ue₁ Ue₂) {i : X} (hi : i ∈ F.edgeB.centres) (a c : ℝ) :
    IsClosed {p : X | dist p i ≤ c * ρ i ∧ |F.edgeB.coord_BAUGA i p| ≤ a ∧
      F.edgeB.smoothing p / ρ p ≤ a} := by
  have hc0 : 0 ≤ max (1 + σc) 0 / ρ i := div_nonneg (le_max_right _ _) (hρ i).le
  have hL : LipschitzWith (Real.toNNReal (max (1 + σc) 0 / ρ i)) (F.edgeB.coord_BAUGA i) :=
    LipschitzWith.of_dist_le_mul fun y z => by
      rw [Real.coe_toNNReal _ hc0, Real.dist_eq]
      exact F.edgeB.coord_lipschitz_BCF2K hi y z
  have hη : Continuous (F.edgeB.coord_BAUGA i) := hL.continuous
  have ht : Continuous fun p => F.edgeB.smoothing p / ρ p :=
    F.edgeB.lipschitz_smoothing.continuous.div F.lipschitz_scale.continuous fun p => (hρ p).ne'
  refine (isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
    ((isClosed_le (continuous_abs.comp hη) continuous_const).inter
      (isClosed_le ht continuous_const))

end Generic

section Carrier

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **The E-free strict replacement (Repl_∂) on the final boundary family**: for `Δ ≥ 2`, EGP04's
early constants `σ, η`; on every final family with the step-one–three bounds and EGP04's tail
requests, a point `q` with `D(q) ≥ 35`, outside the `.38`-zero balls and the slim regions, `q ∈
U_i`, `|η_i(q)| ≤ 4.01Δ`, `t(q) ≤ 4.01Δ` has a revised centre `j` with `q ∈ U_j`, `|η_j(q)| < 2Δ`
and `ζ_j(q) = 1` (G4's theorem on the unadjusted blocks; no map `E` enters). -/
theorem LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
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
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ},
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 →
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
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM),
      ∀ i : W.pieceInterior ⊤, i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        ∃ j ∈ F.edgeB.centres, q ∈ ball j (100 * Δ * ρ j) ∧
          |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧ F.edgeB.cutoff_BAUGA j q = 1 := by
  obtain ⟨σ, hσ, hσ1, η, hη, hR⟩ := LocalPacketsOnBFRZ.bcf02_strict_replacement_BCF2K hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro W _ g ĝ hle ρ hρ n hbcp Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ oM
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F i hi q hq hηq htq hq35 hZ hS
  have hΔ0 : 0 < Δ := by linarith
  obtain ⟨hERR, hFM⟩ := F.toLocalPacketsOnB.trivialChain_err_fm_BCF2K hΔ0
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨j, hj, hηj, hζj, -, -⟩ := hR W g ĝ hle ρ hρ hbcp (c₃ := 1) hΛ hμ hτ hσc hn hT hσs
    hσs1 hb hs hβ2 (by linarith) hσL hbη h3b hbH hLΛ hμΔ oM F
    (fun (x j : W.pieceInterior ⊤) => (ρ j * (F.edgeB.coord_BAUGA j x * F.edgeB.cutoff_BAUGA j x),
      ρ j * F.edgeB.cutoff_BAUGA j x)) id
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).1)
    (fun (j : W.pieceInterior ⊤) (y : W.pieceInterior ⊤ → ℝ × ℝ) => (y j).2) hERR hFM i hi q hq
    hηq htq hq35 hZ hS
  have hne : F.edgeB.cutoff_BAUGA j q ≠ 0 := by rw [hζj]; norm_num
  obtain ⟨-, hball, -, -⟩ := F.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ0 hne
  have hrj := hρ j
  refine ⟨j, hj, ?_, hηj, hζj⟩
  have h := (inv_mul_lt_iff₀ hrj).mp hball
  rw [mem_ball]
  linarith

/-- **The edge piece through the BASES localization is closed and compact** (kernel on
`(W°, d_ĝ)`). For `Δ ≥ 2`, EGP04's early constants `σ, η`; on every final family with the
step-one–three bounds and EGP04's tail requests: for closed `M₂, V ⊆ W°`, `M₂` with its
original-coordinate consequences, and `P` with (ELoc) (`x ∈ P` ⟹ `x ∈ M₂ ∩ V` and `x ∈ U_i`,
`|η_i(x)| < 4.01Δ`, `t(x) < 4.01Δ` for some `i ∈ I_e^B`) and (ENTRY) (`x ∈ M₂ ∩ V`, `x ∈ U_j`,
`|η_j(x)| ≤ 3.5Δ`, `t(x) < 5Δ` ⟹ `x ∈ P`): `P` is the finite union `⋃_i M₂ ∩ V ∩ {d(·, i) ≤ 6Δρ_i,
|η_i| ≤ 4.01Δ, t ≤ 4.01Δ}`, closed and compact. -/
theorem LocalPacketsOnBFRZ.bcf02_isCompact_edgePiece_localized_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
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
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ},
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 →
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
      (M₂ Vt P : Set (W.pieceInterior ⊤)), IsClosed M₂ → IsClosed Vt →
      (∀ q ∈ M₂, ENNReal.ofReal 35 ≤ distanceToBoundary W g q ∧
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) ∧
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|)) →
      (∀ x ∈ P, x ∈ M₂ ∧ x ∈ Vt ∧ ∃ i ∈ F.edgeB.centres, dist x i < 100 * Δ * ρ i ∧
        |F.edgeB.coord_BAUGA i x| < 401 / 100 * Δ ∧ F.edgeB.smoothing x / ρ x < 401 / 100 * Δ) →
      (∀ x ∈ M₂, x ∈ Vt → ∀ j ∈ F.edgeB.centres, dist x j < 100 * Δ * ρ j →
        |F.edgeB.coord_BAUGA j x| ≤ 7 / 2 * Δ → F.edgeB.smoothing x / ρ x < 5 * Δ → x ∈ P) →
      P = ⋃ i ∈ F.edgeB.centres, M₂ ∩ Vt ∩ {p | dist p i ≤ 6 * Δ * ρ i ∧
          |F.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
            F.edgeB.smoothing p / ρ p ≤ 401 / 100 * Δ} ∧
        IsClosed P ∧ IsCompact P := by
  obtain ⟨σ, hσ, hσ1, η, hη, hR⟩ := LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro W _ g ĝ hle ρ hρ n hbcp Λ β σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ hμΔ oM
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F M₂ Vt P hM hV hM₂ hloc hentry
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  have hbase : ∀ x ∈ P, x ∈ M₂ ∧ x ∈ Vt ∧ ∃ i ∈ F.edgeB.centres,
      x ∈ {p | dist p i ≤ 6 * Δ * ρ i ∧ |F.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        F.edgeB.smoothing p / ρ p ≤ 401 / 100 * Δ} := by
    intro x hx
    obtain ⟨hxM, hxV, i, hi, hxi, hηi, hti⟩ := hloc x hx
    have henc := (F.toLocalPacketsOnB.edgeB_enclosure_BCF2K hΔ0 hμ hτ hlam hi (a := 401 / 100)
      (by norm_num) (by norm_num) (mem_ball.mpr hxi) hηi.le hti.le).2 (by norm_num)
    exact ⟨hxM, hxV, i, hi, henc.le, hηi.le, hti.le⟩
  have hre : ∀ x ∈ M₂, x ∈ Vt → ∀ i ∈ F.edgeB.centres,
      x ∈ {p | dist p i ≤ 6 * Δ * ρ i ∧ |F.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        F.edgeB.smoothing p / ρ p ≤ 401 / 100 * Δ} → x ∈ P := by
    rintro x hxM hxV i hi ⟨hxi, hηi, hti⟩
    have hri := hρ i
    have hxi' : dist x i < 100 * Δ * ρ i := by nlinarith
    obtain ⟨h35, hZ, hS⟩ := hM₂ x hxM
    obtain ⟨j, hj, hxj, hηj, -⟩ := hR W g ĝ hle ρ hρ hbcp hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2
      hσL hbη h3b hbH hLΛ hμΔ oM F i hi x hxi' hηi hti h35 hZ hS
    exact hentry x hxM hxV j hj hxj (by linarith) (by linarith)
  obtain ⟨heq, hcl⟩ := isClosed_of_finite_cover_BCF2K F.edgeB.finite_centres hM hV
    (fun i hi => F.toLocalPacketsOnB.isClosed_edgeOriginalDomain_BCF2K hi _ _) hbase hre
  refine ⟨heq, hcl, ?_⟩
  have hK := isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num : (0 : ℝ) < 35)
  exact hK.of_isClosed_subset hcl fun x hx => (hM₂ x (hloc x hx).1).1

end Carrier

end DifferentialGeometry.Geometry.Collapse
