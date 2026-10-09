import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroProducerV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFamilyIdx

/-!
# The boundary zero producer v2, index-corrected (lane BDRY-IDX2)

`eventually_zeroModelFamilyOn_certified_boundary_BZ1_IDX2` is lane BZ-1's
`eventually_zeroModelFamilyOn_certified_boundary_BZ1` (same conclusion, same proof) for a sequence
at the ratios `boundaryCounterexampleRatio δ₀ (n + 1)` — exactly BBR03's counterexample sequence
(`exists_boundary_counterexample_sequence_of_no_threshold`). The accepted statement takes the
sequence at `boundaryCounterexampleRatio δ₀ n`, which is `0` at `n = 0`, where
`NearlyCuspidalBoundary … 0` is empty: that hypothesis cannot be supplied. The joint witnesses come
from BDRY-IDX's `lpa02_total_witnesses_boundary_BDRY3_IDX`; the index `n` of every per-member call
stays the real parameter `α = n` (`δ_{n+1}·16n⁴ ≤ 1`), via the tail lemma
`boundaryCounterexampleRatio_tail_succ_BZ1_IDX2`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Hyperbolic
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- The successor ratio on the tail `3 ≤ n`, `6408 + 1000/b² ≤ n` (lane BDRY-IDX2):
`boundaryCounterexampleRatio_tail_BZ1` with the ratio `δ_{n+1}` and the index `n`. -/
theorem boundaryCounterexampleRatio_tail_succ_BZ1_IDX2 {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {b : ℝ}
    (hb : 0 < b) {n : ℕ} (hn3 : (3 : ℝ) ≤ n) (hnM : 6408 + 1000 / b ^ 2 ≤ n) :
    1 ≤ n ∧ 0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) ∧
      boundaryCounterexampleRatio δ₀ (n + 1) * (16 * (n : ℝ) ^ 4) ≤ 1 ∧
      boundaryCounterexampleRatio δ₀ (n + 1) ≤ 1 / 6408 ∧
      boundaryCounterexampleRatio δ₀ (n + 1) ≤ b ^ 2 / 1000 := by
  have h := boundaryCounterexampleRatio_tail_BZ1 hδ₀ hb hn3 hnM
  have hle := boundaryCounterexampleRatio_succ_le_IDX δ₀ h.1
  exact ⟨h.1, (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le,
    boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n, hle.trans h.2.2.2.1, hle.trans h.2.2.2.2⟩

/-- **The boundary zero producer v2 on the completion, index-corrected** (lane BDRY-IDX2):
BZ-1's producer v2 for a sequence at `boundaryCounterexampleRatio δ₀ (n + 1)` (BBR03's
sequence). Text of BZ-1: The statement of
`eventually_zeroModelFamilyOn_boundary_BDRY3` with (1) the requested cap: after `β₁ < ζ < 1` and
`cap > 0`, the constants `εr < min (1/4) cap`, `δ'`, `Λ' ≥ max ζ⁻¹ β₁⁻¹` come first (`εr` is no
longer a later parameter); (2) on the tail, ONE regional zero family `F` on `((W n)°, d_ĝ)` for
every admissible scale, together with, for the SAME `F`: LC62's local comparison, the enlarged
curvature `sec_ĝ ≥ -(1/60)² r_c⁻²` on `B(c, 400 r_c)`, X82's exact-coordinate shell splitting and
LC73's ζ-adapted tests of the stored radial functions for every `λ ≥ Λ'`. -/
theorem eventually_zeroModelFamilyOn_certified_boundary_BZ1_IDX2 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → ∀ {ζ cap : ℝ}, β 1 < ζ → ζ < 1 → 0 < cap →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ εr < cap ∧ 0 < δ' ∧ 0 < Λ' ∧ ζ⁻¹ ≤ Λ' ∧
        (β 1)⁻¹ ≤ Λ' ∧
      ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤))
        (hcomp : ∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)),
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          ∃ F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
          -- A3: LC62 on the selected balls
          (∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
            T / 20 ≤ (F.zero c hc).radius / ρ q) ∧
          -- A6: the enlarged zero curvature of the completion
          (∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
            SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2))) ∧
          -- A5: X82 on the closed shell, exact distance coordinate
          (∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (Fk : @KleinerLottApprox ((W n).pieceInterior ⊤)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : (W n).pieceInterior ⊤, (@KleinerLottApprox.toFun ((W n).pieceInterior ⊤)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                  ((inducedMetricSpace (ĝ n)).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) Fk x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))) ∧
          -- A5: LC73, ζ-adapted tests of the stored radial function, every ratio `λ ≥ Λ'`
          ∀ c (hc : c ∈ F.centres), ∀ q, (F.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (F.zero c hc).radius →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let R := (F.zero c hc).radius
            let hR : 0 < R := (F.zero c hc).radius_pos
            let η := (F.zero c hc).radial
            let mr := (inducedMetricSpace (ĝ n)).rescale R⁻¹ (inv_pos.mpr hR)
            let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (ĝ n)
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale
              (m := inducedMetricSpace (ĝ n)) (ĝ n) (inducedMetricSpace_hmetric (ĝ n)) hR
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              (((inducedMetricSpace (ĝ n)).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
                (riemannianMetricComplete_iff_inducedMetricSpace.mp (hcomp n)))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η x - η q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (κ.toFun x).fst = lam *
                  (@dist ((W n).pieceInterior ⊤) mr.toDist c x -
                    @dist ((W n).pieceInterior ⊤) mr.toDist c q)) ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
                  intrinsicGeodesic h hEnorm x u (dist x y) = y →
                  |mvfderiv (I := I3) ψ x u -
                    ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ := by
  obtain ⟨δ1, hδ1, htot⟩ := lpa02_total_witnesses_boundary_BDRY3_IDX
  obtain ⟨δ2, hδ2, hcand0⟩ := ofReal_ten_lt_of_near_zero_stratum_BDRY3
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA β hβ hβ1 ζ cap hβζ hζone hcap
  obtain ⟨δs, Λs, hδs, hΛs, hsel⟩ := exists_selected_zero_family_envelope_loc_BZ1 (E := E3)
    (H := E3) (I := I3) finrank_euclideanSpace_fin hβ hβ1
  obtain ⟨δ₃, Λ₃, hδ₃, hΛ₃, h82⟩ := ZeroModelFamilyOn.shell_split_BZ1 hβ hβ1
  obtain ⟨ε₄, δ₄, Λ₄, hε₄, -, hδ₄, hΛ₄, h73⟩ := ZeroModelFamilyOn.adapted_BZ1 hβ hβζ hζone
  -- the requested cap enters here, before the joint witness and `V`
  set εr : ℝ := min (min ε₄ (1 / 8)) (cap / 2) with hεrdef
  have hεr0 : 0 < εr := lt_min (lt_min hε₄ (by norm_num)) (half_pos hcap)
  have hεr8 : εr ≤ 1 / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hεr4 : εr ≤ ε₄ := (min_le_left _ _).trans (min_le_left _ _)
  have hεrcap : εr < cap := (min_le_right _ _).trans_lt (half_lt_self hcap)
  set δ' : ℝ := min δs (min δ₃ δ₄) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδs (lt_min hδ₃ hδ₄)
  set Λ' : ℝ := max (max Λs (max Λ₃ Λ₄)) (max ζ⁻¹ (β 1)⁻¹) with hΛ'def
  have hΛs' : Λs ≤ Λ' := (le_max_left _ _).trans (le_max_left _ _)
  have hΛ₃' : Λ₃ ≤ Λ' := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hΛ₄' : Λ₄ ≤ Λ' := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
  have hζΛ : ζ⁻¹ ≤ Λ' := (le_max_left _ _).trans (le_max_right _ _)
  have hβΛ : (β 1)⁻¹ ≤ Λ' := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨εr, δ', Λ', hεr0, by linarith, hεrcap, hδ'0, hΛs.trans_le hΛs', hζΛ, hβΛ, ?_⟩
  intro T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq hle
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := htot K hK A hA hΛ hw hwc (εr := εr) (δ' := δ') (e := e)
    (T := T) hεr0 (by linarith) hδ'0 he he1 hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ
    hcomp heq
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hw'0 : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hw'c : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < euclideanThreeUnitBallVolume := by
    have h1 : 1 ≤ 1 + 2 * Λ⁻¹ := by have := inv_pos.mpr hΛ; linarith
    have h2 : 1 ≤ 2 * (1 + 2 * Λ⁻¹) ^ 3 := by nlinarith [one_le_pow₀ (n := 3) h1]
    calc w / (2 * (1 + 2 * Λ⁻¹) ^ 3) ≤ w := div_le_self hw.le h2
      _ < euclideanThreeUnitBallVolume := hwc
  set Rβ : ℝ := 1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹| with hRβ
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_ge_atTop (6408 + 1000 / β 1 ^ 2), hnR.eventually_gt_atTop (13 * V / 75),
    hnR.eventually_ge_atTop (32 * Rβ)] with n hn hn3 hnw hnM hnV hn32
  let instM_BZ1 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  intro ρ hρ hρc hρw hsmall
  -- the boundary ratio on the tail
  obtain ⟨h1, hδn0, hδn16, hδ6408, hδβ⟩ :=
    boundaryCounterexampleRatio_tail_succ_BZ1_IDX2 hδ₀ hβ hn3 hnM
  have hn0 : (0 : ℝ) < n := by linarith
  have hnw' : (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (inv_le_comm₀ hn0 hw'0).mpr hnw
  set Z : Set ((W n).pieceInterior ⊤) :=
    {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x} ∩
      scaledSplittingStratum.{0, 0} (fun x => ρ x) (fun x => hρ x) β 0 with hZdef
  have h510 : ENNReal.ofReal 5 < ENNReal.ofReal 10 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hU1 : ∀ v z, z ∈ Z → dist v z < V * ρ v →
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) v := fun v z hz hvz =>
    hcand0 (W n) (g n) K _ (by omega) hδn0 ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans
      (hδ₀S.trans (min_le_right _ _))) (B n) (hcoll n) (hder n) hA (ĝ n) (heq n) (hle n) hβ hβ1
      hδβ hδ6408 hn3 hδn16 hnw' hw'c (by linarith) (by linarith) hn32 ρ hρ (fun p => (hρw p).le)
      hsmall v z hz.1 hz.2 hvz
  by_cases hE : ∃ p₀ : (W n).pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p₀
  swap
  · -- no eligible point: the empty family (every certificate is vacuous)
    refine ⟨fun _ => E3, fun _ => E3, fun _ => inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => 0, {
        centres := ∅
        finite_centres := finite_empty
        centres_subset := empty_subset _
        zero := fun i hi => (notMem_empty i hi).elim
        zero_center := fun i hi => (notMem_empty i hi).elim
        radius_mem := fun i hi => (notMem_empty i hi).elim
        disjoint := fun i hi => (notMem_empty i hi).elim
        meets_stratum := fun i hi => (notMem_empty i hi).elim
        covers_stratum := fun x hx => (hE ⟨x, h510.trans hx.1⟩).elim
        one_end := fun i hi => (notMem_empty i hi).elim }, fun c hc => (notMem_empty c hc).elim,
      fun c hc => (notMem_empty c hc).elim, fun c hc => (notMem_empty c hc).elim,
      fun c hc => (notMem_empty c hc).elim⟩
  obtain ⟨p₀, hp₀⟩ := hE
  choose s hsI hs N mN q hprop hfour hseg C mC o hRCD hCp hcone Ns tNs cNs hNs hhom hwit
    using hn ρ hρ (fun p => (hρw p).le) ⟨p₀, hp₀⟩
  -- the models: the smooth `Ns` with the pulled-back limit metric
  let mNs : ∀ p, MetricSpace (Ns p) := fun p => @homeomorphComapMetric _ _ (tNs p) (mN p) (hhom p)
  have hmod := fun p => @homeomorphComapMetric_model_clauses (Ns p) (N p) (C p) (tNs p) (mN p)
    (hprop p) (mC p) (hhom p) (q p) (o p) (hfour p) (hseg p) (hcone p)
  have instNsP_BZ1 : ∀ p, @ProperSpace (Ns p) (mNs p).toPseudoMetricSpace :=
    fun p => (hmod p).2.1
  have instCP_BZ1 : ∀ p, @ProperSpace (C p) (mC p).toPseudoMetricSpace := hCp
  -- the radii `s(p) ρ(p)` and their global bounds (`W_n` compact)
  let r : (W n).pieceInterior ⊤ → ℝ := fun p => s p * ρ p
  have hlower : ∀ p : (W n).pieceInterior ⊤, T * ρ p ≤ r p := fun p =>
    mul_le_mul_of_nonneg_right (hsI p).1 (hρ p).le
  have instNE_BZ1 : Nonempty (W n).Carrier := ⟨p₀.val⟩
  obtain ⟨pmin, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hρc.continuousOn
  obtain ⟨pmax, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρc.continuousOn
  have hrlow : ∀ p, T * ρ pmin ≤ r p := fun p =>
    (mul_le_mul_of_nonneg_left (hmin (mem_univ p.val)) hT.le).trans (hlower p)
  have hrV : ∀ p, r p ≤ V * ρ p := fun p => mul_le_mul_of_nonneg_right (hsI p).2 (hρ p).le
  have hrup : ∀ p, r p ≤ V * ρ pmax := fun p =>
    (hrV p).trans (mul_le_mul_of_nonneg_left (hmax (mem_univ p.val)) (by linarith))
  -- the compact candidate envelope: the `V ρ_max`-thickening of `{D ≥ 10}`
  have instP_BZ1 : ProperSpace ((W n).pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete (hcomp n)
  have hKc := isCompact_le_distanceToBoundary_BDRY1 (W n) (g n) (by norm_num : (0 : ℝ) < 10)
  have hS : TotallyBounded (cthickening (V * ρ pmax)
      {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 10 ≤ distanceToBoundary (W n) (g n) x}) :=
    hKc.cthickening.totallyBounded
  have hSZ : ∀ v, (ball v (r v) ∩ Z).Nonempty → v ∈ cthickening (V * ρ pmax)
      {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 10 ≤ distanceToBoundary (W n) (g n) x} := by
    rintro v ⟨z, hz1, hz2⟩
    have hz10 : ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) z := hz2.1
    refine mem_cthickening_of_dist_le v z _ _ (show ENNReal.ofReal 10 ≤
      distanceToBoundary (W n) (g n) z from hz10.le) ?_
    have := mem_ball.mp hz1
    rw [dist_comm]
    linarith [hrup v]
  have hcand : ∀ v, (ball v (r v) ∩ Z).Nonempty →
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) v := by
    rintro v ⟨z, hz1, hz2⟩
    refine hU1 v z hz2 ?_
    have := mem_ball.mp hz1
    rw [dist_comm]
    linarith [hrV v]
  -- ONE selection on the envelope (LC66 + LC77 + LC62 on the complete carrier)
  obtain ⟨J, hfin, hdisj, hmeet, hlocJ, himp⟩ := hsel ((W n).pieceInterior ⊤) (ĝ n) (hcomp n) Ns
    C (mN := mNs) (mC := mC) (fun p => (hhom p).symm (q p)) o (fun p => (hRCD p).some)
    (fun _ => δ) r (fun x => ρ x) (fun x => hρ x) hT
    ((mul_le_mul_of_nonneg_left hΛs' (by norm_num)).trans hTΛ) hlower (mul_pos hT (hρ pmin))
    hrlow hrup Z _ hS (fun x hx => hx.2) hSZ
  have hJU : ∀ i ∈ J, ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) i :=
    fun i hi => hcand i (hmeet i hi)
  have hJ5 : ∀ i ∈ J, ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) i :=
    fun i hi => h510.trans (hJU i hi)
  obtain ⟨hcover, hend⟩ := himp fun i hi => ⟨fun y hy => (hwit i (hJ5 i hi)).1 y (by
    rw [inducedMetricSpace_ball (ĝ n)]; exact hy), (hmod i).2.2.1, (hmod i).2.2.2.1,
    (hmod i).2.2.2.2, hδδ'.trans_le (min_le_left _ _), (hwit i (hJ5 i hi)).2.1⟩
  let F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x) (fun x => hρ x) β Ns
      C o δ εr e T V {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
      {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x} :=
    { centres := J
      finite_centres := hfin
      centres_subset := fun i hi => hJU i hi
      zero := fun c hc =>
        { center := c
          radius := r c
          radius_pos := mul_pos (hs c) (hρ c)
          model := c
          coneMap := ((hwit c (hJ5 c hc)).2.1).some
          radial := ((hwit c (hJ5 c hc)).2.2.1).choose
          radial_spec := ((hwit c (hJ5 c hc)).2.2.1).choose_spec
          modelChart := fun ρ' h => ((hwit c (hJ5 c hc)).2.2.2 ρ' h).choose
          modelChart_source := fun ρ' h => ((hwit c (hJ5 c hc)).2.2.2 ρ' h).choose_spec.1
          modelChart_target := fun ρ' h => ((hwit c (hJ5 c hc)).2.2.2 ρ' h).choose_spec.2 }
      zero_center := fun _ _ => rfl
      radius_mem := fun c _ => ⟨hlower c, hrV c⟩
      disjoint := fun _ hi _ hj hij => hdisj hi hj hij
      meets_stratum := fun c hc => (hmeet c hc).mono (inter_subset_inter_right _ inter_subset_right)
      covers_stratum := fun _ hx => hcover hx
      one_end := fun c hc => hend c hc }
  -- the certificates on THIS family
  have hlocF : ∀ c (hc : c ∈ F.centres), ∀ q, dist c q ≤ 10 * (F.zero c hc).radius →
      T / 20 ≤ (F.zero c hc).radius / ρ q := fun c hc q hq => hlocJ c hc q hq
  have hbufF : ∀ c (hc : c ∈ F.centres), ∀ y ∈ ball c (400 * (F.zero c hc).radius),
      SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * ((F.zero c hc).radius)⁻¹ ^ 2)) :=
    fun c hc => (hwit c (hJ5 c hc)).1
  have hRCDF : ∀ c (hc : c ∈ F.centres), Nonempty (RadialConeData (o (F.zero c hc).model)) :=
    fun c _ => hRCD c
  have hT20 : Λ' ≤ T / 20 := by linarith
  refine ⟨Ns, C, mNs, cNs, mC, o, F, hlocF, hbufF, ?_, ?_⟩
  · exact h82 ((W n).pieceInterior ⊤) (ĝ n) (hcomp n) (fun x => ρ x) (fun x => hρ x) F
      (hδδ'.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hRCDF hbufF
      (fun c hc q hq => (hΛ₃'.trans hT20).trans (hlocF c hc q hq))
  · intro c hc q hq1 hq2 lam hlam hΛlam
    exact h73 ((W n).pieceInterior ⊤) (ĝ n) (hcomp n) (fun x => ρ x) (fun x => hρ x) F
      (hδδ'.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hεr4 hRCDF hbufF c hc q hq1
      hq2 lam hlam (hΛ₄'.trans hΛlam)

end DifferentialGeometry.Geometry.Collapse
