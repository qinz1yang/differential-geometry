import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05LocalComparisonCappedWitness
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeKernel

/-!
# LPA05 (capped) keeping the sublevel types of the SAME zero family (lane C14-FAM-Z, layer 1)

External review 53, §4.1 (A-Z) and dispositions-task53: the final closed family must carry, for
every zero centre `i` of ITS zero family and every `a ∈ [1/5, 2]`, the type of the actual radial
sublevel `{η_i ≤ a}` (`CompactModelSublevel ∨ PointSoulCoreSublevel ∨ CircleSoulCoreSublevel ∨
ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel`), KEPT at the joint zero selection — never taken
from a second `∃ Z`. Only three layers carry the zero family (lane FC39-WIT): this capped LPA05, the
C14 producer and the C14D producer.

`lpa05_selected_zero_packets_capped_FAMZ`: the statement of `lpa05_selected_zero_packets_capped_WIT`
(every clause verbatim, the same tail) with one more clause on the returned zero family. The proof
is the accepted one (generated from `LPA05LocalComparisonCappedWitness.lean` by
`build-logs/scratch/C14-FAM-Z/gen_l1.py`) with two changes:
* the ONE LPA02 call is `lpa02_uniform_joint_zero_witnesses_withCarrierMetric` (the same witnesses
  together with the core coordinate `u`, the carrier of every actual sublevel of the SAME radial
  function, and the classification of the model; it needs `ε ≤ 1/64`, so `ε` gets one more
  `min … (1/64)` — the statement only asks `ε < 1/4`, `ε < cap`);
* the exported joint witness `Lpa02WitnessV2` and the selection `Lpa02WitnessAtV2` are projections
  of these witnesses (drop `u`, the carrier and the classification), and the types of the selected
  family follow from the same choice by `zero_sublevel_types_of_carrier_FAMZ`.

Consumer: `lpa05_selected_zero_packets_capped_WIT_of_FAMZ` (the `_WIT` statement follows).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LPA05 (capped) exporting the joint witness, the selection AND the sublevel types of the
same zero family.** The statement of `lpa05_selected_zero_packets_capped_WIT` (every clause
verbatim, the same tail) with one more clause on the returned zero family `Z`: for every orientation
`oX` of the member, every selected centre `c` and every `a ∈ [1/5, 2]`, the actual sublevel
`{η_c ≤ a}` of the SAME radial function is `CompactModelSublevel oX ∨ PointSoulCoreSublevel ∨
CircleSoulCoreSublevel ∨ ProjectiveSoulCoreSublevel ∨ KleinSoulCoreSublevel` of its model. The ONE
LPA02 call is `lpa02_uniform_joint_zero_witnesses_withCarrierMetric`; the joint witness and the
selection are projections of its witnesses, the types come from the same choice. -/
theorem lpa05_selected_zero_packets_capped_FAMZ
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ ε < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
      [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      Lpa02WitnessV2 (g i) K Λ w ε e T V δ ∧
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∃ (N C : X i → Type) (mN : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (mC : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        (∀ b, ProperSpace (N b) ∧ ProperSpace (C b) ∧ Nonempty (RadialConeData (o b)) ∧
          (∃ n : N b, ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ hR : 0 < R,
            Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR))
              (mC b) n (o b) δ₁)) ∧
          ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N'),
            letI := mN'
            letI := cN'
            ∃ (_ : IsManifold I3 ∞ N') (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3
                (TangentSpace I3 : N' → Type _)),
              ConnectedSpace N' ∧
              (letI : RiemannianBundle (fun x : N' => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
               IsRiemannianManifold I3 N') ∧
              (∀ (x : N') (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
              Nonempty (N b ≃ᵢ N')) ∧
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          (∀ c (hc : c ∈ Z.centres), ∃ t ∈ Icc T V, ∃ ht : 0 < t,
            (Z.zero c hc).radius = t * ρ c ∧
              Lpa02WitnessAtV2 (g i) K ε e δ c (ρ c) t (hρ c) ht) ∧
          (∀ oX : ManifoldOrientation (𝓡 3) (X i) 3, ∀ c (hc : c ∈ Z.centres),
            ∀ a ∈ Icc (1 / 5 : ℝ) 2,
            CompactModelSublevel oX (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
            PointSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
            CircleSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
            ProjectiveSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a} ∨
            KleinSoulCoreSublevel (N (Z.zero c hc).model) {x | (Z.zero c hc).radial x ≤ a}) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, dist c q ≤ 10 * (Z.zero c hc).radius →
            T / 20 ≤ (Z.zero c hc).radius / ρ q) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ y ∈ ball c (400 * (Z.zero c hc).radius),
            SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * ((Z.zero c hc).radius)⁻¹ ^ 2))) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            @HasEuclideanSplitting.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1
              (β 1) ∧
            @splittingRank.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≠ 0) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (F : @KleinerLottApprox (X i)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : X i, (@KleinerLottApprox.toFun (X i)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                  ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let R := (Z.zero c hc).radius
            let hR : 0 < R := (Z.zero c hc).radius_pos
            let η := (Z.zero c hc).radial
            let mr := (mX i).rescale R⁻¹ (inv_pos.mpr hR)
            let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i)
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i)
              (hmetric i) hR
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              (((mX i).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
                (@complete_of_compact (X i) (mX i).toUniformSpace _))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η x - η q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (κ.toFun x).fst = lam *
                  (@dist (X i) mr.toDist c x - @dist (X i) mr.toDist c q)) ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
                  intrinsicGeodesic h hEnorm x u (dist x y) = y →
                  |mvfderiv (I := I3) ψ x u -
                    ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ) ∧
          ∃ L : ℝ, 0 ≤ L ∧
            (∀ c (hc : c ∈ Z.centres),
              let φc : X i → ℝ := fun x => annularCutoff cutoffProfile ((Z.zero c hc).radial x)
              let gr := scaleMetric (((Z.zero c hc).radius)⁻¹ ^ 2)
                (pow_pos (inv_pos.mpr (Z.zero c hc).radius_pos) 2) (g i)
              ContMDiff I3 𝓘(ℝ, ℝ) ∞ φc ∧ (∀ x, φc x ∈ Icc (0 : ℝ) 1) ∧
              (∀ x, (Z.zero c hc).radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) → φc x = 1) ∧
              tsupport φc ⊆ {x | (1 / 5 - e) * (Z.zero c hc).radius < dist x c ∧
                dist x c < (9 / 10 + e) * (Z.zero c hc).radius} ∧
              tsupport φc ⊆ ball c (Z.zero c hc).radius ∧ HasCompactSupport φc ∧
              (∀ q, Real.sqrt (gr.inner q (gradFun gr φc q) (gradFun gr φc q)) ≤ L * (1 + ε)) ∧
              ball c ((Z.zero c hc).radius / 10) ⊆ {x | (Z.zero c hc).radial x < 1 / 5}) ∧
            ∀ c (hc : c ∈ Z.centres) c' (hc' : c' ∈ Z.centres), c ≠ c' →
              Disjoint (tsupport fun x => annularCutoff cutoffProfile ((Z.zero c hc).radial x))
                (tsupport fun x => annularCutoff cutoffProfile ((Z.zero c' hc').radial x)) := by
  have instNZ_LPA02 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨εa, δa, Λa, hεa, hεa4, hδa, hΛa, hAl⟩ :=
    exists_selected_zero_packets_of_aligned_metric.{0, 0} (E := E3) (H := E3) (I := I3)
      (finrank_euclideanSpace_fin) hβ hβone hβζ hζone
  obtain ⟨ε₄, δ₄, Λ₄, hε₄, -, hδ₄, -, h73⟩ :=
    selected_center_adapted_coordinate_of_original_buffer.{0, 0} (E := E3) (H := E3) (I := I3)
      hβ hβζ hζone
  have hεpos : 0 < min (min εa ε₄) (min (cap / 2) (1 / 64)) :=
    lt_min (lt_min hεa hε₄) (lt_min (half_pos hcap) (by norm_num))
  have hεa' : min (min εa ε₄) (min (cap / 2) (1 / 64)) ≤ εa :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hε₄' : min (min εa ε₄) (min (cap / 2) (1 / 64)) ≤ ε₄ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hε4 : min (min εa ε₄) (min (cap / 2) (1 / 64)) < 1 / 4 := hεa'.trans_lt hεa4
  have hεcap : min (min εa ε₄) (min (cap / 2) (1 / 64)) < cap :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hcap)
  have hε64 : min (min εa ε₄) (min (cap / 2) (1 / 64)) ≤ 1 / 64 :=
    (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (min εa ε₄) (min (cap / 2) (1 / 64)), min δa δ₄, max Λa Λ₄, hεpos, hε4, hεcap,
    lt_min hδa hδ₄, lt_max_of_lt_left hΛa, ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder Λ w hΛ hw hwc
  obtain ⟨V, hTV, δ, hδ0, hδδ', hW⟩ := lpa02_uniform_joint_zero_witnesses_withCarrierMetric g
    hmetric hα hstand K hK A hA hder hΛ hw hwc (ε := min (min εa ε₄) (min (cap / 2) (1 / 64)))
    (δ' := min δa δ₄) (e := e) (T := T) hεpos hε64 (lt_min hδa hδ₄) he he1
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi
  refine ⟨?_, ?_⟩
  · delta Lpa02WitnessV2
    intro p r hr hrw
    obtain ⟨s, hsI, hs, hWs⟩ := hi p r hr hrw
    refine ⟨s, hsI, hs, ?_⟩
    delta Lpa02WitnessAtV2
    obtain ⟨N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, hRCD, hCp,
      hcone, Ns, tNs, cNs, hNs, hhom, uc, hbuf, hKL, ⟨F, -, hF⟩, hball, -⟩ := hWs
    exact ⟨N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, hRCD, hCp,
      hcone, Ns, tNs, cNs, hNs, hhom, hbuf, hKL, ⟨F, hF⟩, hball⟩
  intro ρ hρ hρc hρw
  rcases isEmpty_or_nonempty (X i) with hX | ⟨⟨p₀⟩⟩
  · refine ⟨fun _ => E3, fun _ => E3, fun _ => inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => inferInstance, fun _ => 0, fun b => (hX.false b).elim, ?_⟩
    exact ⟨{ centres := ∅
             finite_centres := finite_empty
             zero := fun c => (hX.false c).elim
             zero_center := fun c => (hX.false c).elim
             radius_mem := fun c => (hX.false c).elim
             disjoint := fun c => (hX.false c).elim
             meets_stratum := fun c => (hX.false c).elim
             covers_stratum := fun c => (hX.false c).elim
             one_end := fun c => (hX.false c).elim },
      fun c => (hX.false c).elim, fun _ c => (hX.false c).elim,
      fun c => (hX.false c).elim, fun c => (hX.false c).elim, fun c => (hX.false c).elim,
      fun c => (hX.false c).elim,
      fun c => (hX.false c).elim, 0, le_rfl, fun c => (hX.false c).elim,
      fun c => (hX.false c).elim⟩
  have instConn_LPA02 : ConnectedSpace (X i) :=
    connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
  choose s hsI hs hWs using fun p => hi p (ρ p) (hρ p) (hρw p)
  have hWAt : ∀ p, Lpa02WitnessAtV2 (g i) K (min (min εa ε₄) (min (cap / 2) (1 / 64))) e δ p
      (ρ p) (s p) (hρ p) (hs p) := by
    intro p
    delta Lpa02WitnessAtV2
    obtain ⟨N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, hRCD, hCp,
      hcone, Ns, tNs, cNs, hNs, hhom, uc, hbuf, hKL, ⟨F, -, hF⟩, hball, -⟩ := hWs p
    exact ⟨N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, hRCD, hCp,
      hcone, Ns, tNs, cNs, hNs, hhom, hbuf, hKL, ⟨F, hF⟩, hball⟩
  choose N mN cN hMN G q hprop hconn hRiem hsecG hfour hseg C mC o hRCD hCp hcone Ns tNs
    cNs hNs hhom u hbuf hKL hη hball hcases using fun p => hWs p
  -- the radial functions and their smooth open sets, fixed once at every point
  let r : X i → ℝ := fun p => s p * ρ p
  have hr : ∀ p, 0 < r p := fun p => mul_pos (hs p) (hρ p)
  have hlower : ∀ p, T * ρ p ≤ r p := fun p => mul_le_mul_of_nonneg_right (hsI p).1 (hρ p).le
  have hupper : ∀ p, r p ≤ V * ρ p := fun p => mul_le_mul_of_nonneg_right (hsI p).2 (hρ p).le
  let η : X i → X i → ℝ := fun p => (hη p).choose
  have hηs : ∀ p, _ := fun p => (hη p).choose_spec.2
  have hcorep : ∀ p, _ := fun p => (hη p).choose_spec.1
  choose O hO using fun p => (hηs p).2.2.2.2.2.2.2.2.2.2.1
  have hrad : ∀ p, _ := fun p => radial_original_clauses_of_rescaled (I := I3) (m := mX i) (hr p)
    (hηs p).2.1 (hηs p).2.2.2.2.1
  have hclose : ∀ p x, |η p x - (r p)⁻¹ * dist x p| < e := by
    intro p x
    have h := (hηs p).2.2.1 x
    have heq : |η p x - (r p)⁻¹ * dist x p| = |η p x - @Metric.infDist (X i)
        ((mX i).rescale (r p)⁻¹ (inv_pos.mpr (hr p))).toPseudoMetricSpace x {p}| := by
      rw [@Metric.infDist_singleton (X i)
        ((mX i).rescale (r p)⁻¹ (inv_pos.mpr (hr p))).toPseudoMetricSpace]
      rfl
    rw [heq]
    exact h
  -- the models: the smooth `Ns` with the pulled-back limit metric
  let mNs : ∀ p, MetricSpace (Ns p) := fun p => @homeomorphComapMetric _ _ (tNs p) (mN p) (hhom p)
  have hmod := fun p => @homeomorphComapMetric_model_clauses (Ns p) (N p) (C p) (tNs p) (mN p)
    (hprop p) (mC p) (hhom p) (q p) (o p) (hfour p) (hseg p) (hcone p)
  have instNsP_LPA02 : ∀ p, @ProperSpace (Ns p) (mNs p).toPseudoMetricSpace := fun p => (hmod p).2.1
  -- LCP04 (aligned) on ONE selection
  obtain ⟨J, hfin, hdisj, hmeet, hloc, himp⟩ := hAl (X i) (g i) (mX i) (hmetric i) Ns C (mN := mNs)
    (mC := mC) (fun p => (hhom p).symm (q p)) o (fun p => (hRCD p).some) (fun _ => δ) η r ρ hρc
    hρ hT ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hTΛ) hTV hlower
    hupper
  obtain ⟨hshell, hcover, hcoord, hend⟩ := himp fun j _ => ⟨hbuf j, (hmod j).2.2.1,
    (hmod j).2.2.2.1, (hmod j).2.2.2.2, hδδ'.trans_le (min_le_left _ _), hKL j, (hrad j).1,
    fun x y => ((hrad j).2 x y).trans (mul_le_mul_of_nonneg_right hεa'
      (mul_nonneg (inv_nonneg.mpr (hr j).le) dist_nonneg))⟩
  -- LPA06's zero cutoffs on the same selection
  obtain ⟨L, hL0, hcut, hcutdisj⟩ := selected_zero_cutoffs (I := I3) (g i) J r hr hdisj η O
    hεpos.le he1 (fun j _ => @LipschitzWith.continuous (X i) ℝ
      ((mX i).rescale (r j)⁻¹ (inv_pos.mpr (hr j))).toPseudoEMetricSpace _ _ _ (hηs j).1)
    (fun j _ => (hO j).1)
    (fun j _ => (hO j).2.2.1)
    (fun j _ x hx => (hO j).2.1 ⟨hx.1, hx.2.trans (by norm_num)⟩) (fun j _ x => hclose j x)
    (fun j _ q' hq' => ((hηs j).2.2.2.2.2.2.2.1 q'
      ((hηs j).2.2.2.2.2.2.2.2.2.1 ⟨hq'.1, hq'.2.trans (by norm_num)⟩)).2)
  refine ⟨Ns, C, mNs, cNs, hNs, mC, o, fun b => ⟨(hmod b).2.1, hCp b, hRCD b,
    ⟨(hhom b).symm (q b), (hmod b).2.2.2.2⟩, N b, mN b, cN b, hMN b, G b, hconn b, hRiem b,
    hsecG b, ⟨{ toEquiv := (hhom b).toEquiv, isometry_toFun := (hmod b).1 }⟩⟩, ?_⟩
  let Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β Ns C o δ
      (min (min εa ε₄) (min (cap / 2) (1 / 64))) e T V :=
    { centres := J
      finite_centres := hfin
      zero := fun c _ =>
        { center := c
          radius := r c
          radius_pos := hr c
          model := c
          coneMap := (hKL c).some
          radial := η c
          radial_spec := hηs c
          modelChart := fun ρ' h => (hball c ρ' h).choose
          modelChart_source := fun ρ' h => (hball c ρ' h).choose_spec.1
          modelChart_target := fun ρ' h => (hball c ρ' h).choose_spec.2 }
      zero_center := fun _ _ => rfl
      radius_mem := fun c _ => ⟨hlower c, hupper c⟩
      disjoint := fun _ hc _ hc' hcc' => hdisj hc hc' hcc'
      meets_stratum := fun c hc => hmeet c hc
      covers_stratum := fun _ hq => hcover hq
      one_end := fun c hc => hend c hc }
  refine ⟨Z, fun c _ => ⟨s c, hsI c, hs c, rfl, hWAt c⟩,
    fun oX => zero_sublevel_types_of_carrier_FAMZ (hmetric i) oX Z (K := K) (by omega) u
      (fun b => instNsP_LPA02 b) hcases (fun c _ a ha => hcorep c a ha),
    fun c hc q hq => (hloc c hc q hq).2, fun c _ => hbuf c, fun c hc => hshell c hc,
    fun c hc => hcoord c hc, ?_, L, hL0,
    fun c hc => hcut c hc, fun c hc c' hc' hcc' => hcutdisj hc hc' hcc'⟩
  intro c hc q' hq1 hq2 lam hlam hΛ'
  exact h73 (X i) (g i) (hmetric i) c (r c) (hr c) (hbuf c) (C c) (o c) (hRCD c).some (hKL c).some
    (hδδ'.trans_le (min_le_right _ _)) (η c) (hrad c).1
    (fun x y => ((hrad c).2 x y).trans (mul_le_mul_of_nonneg_right hε₄'
      (mul_nonneg (inv_nonneg.mpr (hr c).le) dist_nonneg)))
    q' hq1 hq2 lam hlam ((le_max_right _ _).trans hΛ')


/-- **Consumer: the `_WIT` statement follows.** `lpa05_selected_zero_packets_capped_FAMZ` implies
the statement of `lpa05_selected_zero_packets_capped_WIT` (drop the type clause). -/
theorem lpa05_selected_zero_packets_capped_WIT_of_FAMZ
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ ε < cap ∧ 0 < δ' ∧ 0 < Λ' ∧
    ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
    ∀ (X : ℕ → Type) [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
      [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
      (g : ∀ i, SmoothRiemannianMetric I3 (X i))
      (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
      (α : ℕ → ℝ), Tendsto α atTop atTop →
      (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
        curvatureRadius (g i) p) →
    ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ → ℝ),
      (∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) →
      (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
        ∀ C, 0 < C → C < α i → ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
          curvatureDerivativeNorm (g i) k y ≤
            A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
    ∀ (Λ w : ℝ), 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop,
      Lpa02WitnessV2 (g i) K Λ w ε e T V δ ∧
      ∀ (ρ : X i → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
      ∃ (N C : X i → Type) (mN : ∀ b, MetricSpace (N b)) (_ : ∀ b, ChartedSpace E3 (N b))
        (_ : ∀ b, IsManifold I3 ∞ (N b)) (mC : ∀ b, MetricSpace (C b)) (o : ∀ b, C b),
        (∀ b, ProperSpace (N b) ∧ ProperSpace (C b) ∧ Nonempty (RadialConeData (o b)) ∧
          (∃ n : N b, ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ hR : 0 < R,
            Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR))
              (mC b) n (o b) δ₁)) ∧
          ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N'),
            letI := mN'
            letI := cN'
            ∃ (_ : IsManifold I3 ∞ N') (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3
                (TangentSpace I3 : N' → Type _)),
              ConnectedSpace N' ∧
              (letI : RiemannianBundle (fun x : N' => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
               IsRiemannianManifold I3 N') ∧
              (∀ (x : N') (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
              Nonempty (N b ≃ᵢ N')) ∧
        ∃ Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V,
          (∀ c (hc : c ∈ Z.centres), ∃ t ∈ Icc T V, ∃ ht : 0 < t,
            (Z.zero c hc).radius = t * ρ c ∧
              Lpa02WitnessAtV2 (g i) K ε e δ c (ρ c) t (hρ c) ht) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, dist c q ≤ 10 * (Z.zero c hc).radius →
            T / 20 ≤ (Z.zero c hc).radius / ρ q) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ y ∈ ball c (400 * (Z.zero c hc).radius),
            SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * ((Z.zero c hc).radius)⁻¹ ^ 2))) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            @HasEuclideanSplitting.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q 1
              (β 1) ∧
            @splittingRank.{0, 0} (X i) ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q β 3 ≠ 0) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
              ∃ (z : Zf) (F : @KleinerLottApprox (X i)
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : X i, (@KleinerLottApprox.toFun (X i)
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Zf))
                  ((mX i).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist c x - dist c q)))) ∧
          (∀ c (hc : c ∈ Z.centres), ∀ q, (Z.zero c hc).radius / 10 ≤ dist c q →
            dist c q ≤ 10 * (Z.zero c hc).radius →
            ∀ (lam : ℝ) (hlam : 0 < lam), Λ' ≤ lam →
            let R := (Z.zero c hc).radius
            let hR : 0 < R := (Z.zero c hc).radius_pos
            let η := (Z.zero c hc).radial
            let mr := (mX i).rescale R⁻¹ (inv_pos.mpr hR)
            let gr := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g i)
            let hmr := riemannianEDistOf_scaleMetric_inv_sq_eq_rescale (m := mX i) (g i)
              (hmetric i) hR
            let := mr.rescale lam hlam
            letI := (mr.rescale_completeSpace_iff lam hlam).mpr
              (((mX i).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr
                (@complete_of_compact (X i) (mX i).toUniformSpace _))
            letI := radialScaledBundle gr lam hlam
            letI := radialScaledContinuous gr lam hlam
            letI := radialScaledManifold (m := mr) gr hmr lam hlam
            let h := scaleMetric (lam ^ 2) (pow_pos hlam 2) gr
            let ψ := fun x => lam * (η x - η q)
            ∃ hEnorm : IsMetricNorm h,
              ∃ (Zf : Type) (mZ : MetricSpace Zf), letI := mZ
                ∃ (z : Zf) (κ : KleinerLottApprox q (WithLp.toLp 2 ((0 : ℝ), z)) (β 1)),
                (∀ x, (κ.toFun x).fst = lam *
                  (@dist (X i) mr.toDist c x - @dist (X i) mr.toDist c q)) ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ψ (ball q 1) ∧ ψ q = 0 ∧
                (∀ x ∈ ball q 1, ∀ y ∈ ball q 1, |ψ x - ψ y| ≤ (1 + ζ) * dist x y) ∧
                (∀ x ∈ ball q 1, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
                (∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' ball q 1) ≤ ζ) ∧
                ∀ x ∈ ball q 1, ∀ y ∈ ball q ζ⁻¹, 1 < dist x y →
                  ∀ u : TangentSpace I3 x, h.inner x u u = 1 →
                  intrinsicGeodesic h hEnorm x u (dist x y) = y →
                  |mvfderiv (I := I3) ψ x u -
                    ((κ.toFun y).fst - (κ.toFun x).fst) / dist x y| < ζ) ∧
          ∃ L : ℝ, 0 ≤ L ∧
            (∀ c (hc : c ∈ Z.centres),
              let φc : X i → ℝ := fun x => annularCutoff cutoffProfile ((Z.zero c hc).radial x)
              let gr := scaleMetric (((Z.zero c hc).radius)⁻¹ ^ 2)
                (pow_pos (inv_pos.mpr (Z.zero c hc).radius_pos) 2) (g i)
              ContMDiff I3 𝓘(ℝ, ℝ) ∞ φc ∧ (∀ x, φc x ∈ Icc (0 : ℝ) 1) ∧
              (∀ x, (Z.zero c hc).radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) → φc x = 1) ∧
              tsupport φc ⊆ {x | (1 / 5 - e) * (Z.zero c hc).radius < dist x c ∧
                dist x c < (9 / 10 + e) * (Z.zero c hc).radius} ∧
              tsupport φc ⊆ ball c (Z.zero c hc).radius ∧ HasCompactSupport φc ∧
              (∀ q, Real.sqrt (gr.inner q (gradFun gr φc q) (gradFun gr φc q)) ≤ L * (1 + ε)) ∧
              ball c ((Z.zero c hc).radius / 10) ⊆ {x | (Z.zero c hc).radial x < 1 / 5}) ∧
            ∀ c (hc : c ∈ Z.centres) c' (hc' : c' ∈ Z.centres), c ≠ c' →
              Disjoint (tsupport fun x => annularCutoff cutoffProfile ((Z.zero c hc).radial x))
                (tsupport fun x => annularCutoff cutoffProfile ((Z.zero c' hc').radial x)) := by
  obtain ⟨ε, δ', Λ', hε, hε4, hεcap, hδ', hΛ', h⟩ :=
    lpa05_selected_zero_packets_capped_FAMZ hβ hβone hβζ hζone hcap
  refine ⟨ε, δ', Λ', hε, hε4, hεcap, hδ', hΛ', ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder Λ w hΛ hw hwc
  obtain ⟨V, hTV, δ, hδ0, hδδ', h⟩ := h T hT hTΛ e he he1 X g hmetric α hα hstand K hK A hA hder Λ w
    hΛ hw hwc
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [h] with i hi
  refine ⟨hi.1, fun ρ hρ hρc hρw => ?_⟩
  obtain ⟨N, C, mN, cN, hN, mC, o, hmod, Z, hsel, -, hZ⟩ := hi.2 ρ hρ hρc hρw
  exact ⟨N, C, mN, cN, hN, mC, o, hmod, Z, hsel, hZ⟩

end DifferentialGeometry.Geometry.Collapse
