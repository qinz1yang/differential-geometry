import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05ModelMetric
import DifferentialGeometry.Geometry.Collapse.ZeroPacketCutoffFamily
import DifferentialGeometry.Geometry.Collapse.LocalExport.ZeroModelBall

/-!
# LPA05 (row): the selected zero packets keep all their witnesses

Frozen blueprint master207A, LPA05 (A:30548): "Use LPA04's single assignment and tail. At every
center fix ONCE one LPA02 witness with `r(p) = s(p) ρ(p)`, `s(p) ∈ [T, V]`. LC80 then produces its
finite disjoint zero-ball family, tenth-radius cover, prescribed annular adapted coordinates and
same-model at-most-one-end conclusions. [...] its open distance balls retain LC61's smooth
identifications. No continuity of the chosen pointwise witnesses is required."

`lpa05_selected_zero_packets_with_witnesses`: LCP04's constants (aligned form,
`exists_selected_zero_packets_of_aligned_metric`) and LC73's (`selected_center_adapted_coordinate_of_original_buffer`)
are fixed after `β 1 < ζ < 1` (the reordered chain's step 12); then `T ≥ 20 Λ'`, `e`, LPA01's
standing data, and LPA02's `V` LAST. On one tail, for EVERY continuous positive scale `ρ` below
LPA01's bound `2 r_p(w')` (in particular the tail's OWN modified scale, chosen after the tail), the
witnesses of LPA02 are fixed ONCE at every point (`choose`, no continuity), and ONE LC64 selection
carries:
* an LC87 zero-model family `ZeroModelFamily I3 (X i) (g i) ρ hρ β N C o δ ε e T V` (radii
  `s(p) ρ(p) ∈ [Tρ, Vρ]`, disjoint balls meeting the zero stratum, tenth-radius cover, Kleiner–Lott
  `δ`-maps, the ORIGINAL LC67 radial functions, LC61's ball identifications `B(c, ρ' r_c) ≃ N_c`,
  and at most one end of every model);
* the models: `N_b` is the SMOOTH model `Ns` of LPA02 with the metric of the `C^{K-1}` limit
  pulled back (`homeomorphComapMetric`): proper, with its cone `(C_b, o_b)` (proper, radial cone
  data, Kleiner–Lott maps from every blow-down) and ISOMETRIC to a complete connected nonnegatively
  curved `C^{K-1}` Riemannian three-manifold;
* at every centre: the original buffer, LC66's shell splitting, X82's original radial coordinate,
  LC73's prescribed annular adapted coordinate from the SAME radial function at every shell point
  and every `λ ≥ Λ'`, and LPA06's LC31 cutoffs (one `L`, supports strictly inside the selected
  balls, pairwise disjoint supports).

The sublevel types (LFR54) are not part of this statement: the LFR54 classification is not
available (state-LPA02.md, G3).
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

/-- **LPA05 (row).** After `β 1 < ζ < 1`: constants `ε, δ', Λ'`; then for `T ≥ 20 Λ'`,
`0 < e < 1/40` and LPA01's standing data (`10 ≤ K`) there are `V ≥ T` (last), one cone error
`δ < δ'` and a tail on which, for EVERY continuous positive scale `ρ ≤ 2 r_p(w')`, the LPA02
witnesses fixed once at every point give one LC87 zero-model family at `ρ` (models: the smooth
LPA02 models with the pulled-back limit metric, isometric to complete nonnegative `C^{K-1}`
manifolds) with, at every selected centre, the original buffer, LC66's shell splitting, X82's
original radial coordinate, LC73's adapted coordinates from the SAME radial function, and LPA06's
zero cutoffs with pairwise disjoint supports. -/
theorem lpa05_selected_zero_packets_with_witnesses
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
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
  have hεpos : 0 < min εa ε₄ := lt_min hεa hε₄
  refine ⟨min εa ε₄, min δa δ₄, max Λa Λ₄, hεpos, (min_le_left _ _).trans_lt hεa4,
    lt_min hδa hδ₄, lt_max_of_lt_left hΛa, ?_⟩
  intro T hT hTΛ e he he1 X mX _ _ _ g hmetric α hα hstand K hK A hA hder Λ w hΛ hw hwc
  obtain ⟨V, hTV, δ, hδ0, hδδ', hW⟩ := lpa02_uniform_joint_zero_witnesses g hmetric hα hstand K
    hK A hA hder hΛ hw hwc (ε := min εa ε₄) (δ' := min δa δ₄) (e := e) (T := T) hεpos
    (by linarith [min_le_left εa ε₄]) (lt_min hδa hδ₄) he he1
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hW] with i hi ρ hρ hρc hρw
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
      fun c => (hX.false c).elim, fun c => (hX.false c).elim, fun c => (hX.false c).elim,
      fun c => (hX.false c).elim, 0, le_rfl, fun c => (hX.false c).elim,
      fun c => (hX.false c).elim⟩
  have instConn_LPA02 : ConnectedSpace (X i) :=
    connectedSpace_of_aligned_metric (g i) (hmetric i) p₀
  choose s hsI hs N mN cN hMN G q hprop hconn hRiem hsecG hfour hseg C mC o hRCD hCp hcone Ns tNs
    cNs hNs hhom hbuf hKL hη hball using fun p => hi p (ρ p) (hρ p) (hρw p)
  -- the radial functions and their smooth open sets, fixed once at every point
  let r : X i → ℝ := fun p => s p * ρ p
  have hr : ∀ p, 0 < r p := fun p => mul_pos (hs p) (hρ p)
  have hlower : ∀ p, T * ρ p ≤ r p := fun p => mul_le_mul_of_nonneg_right (hsI p).1 (hρ p).le
  have hupper : ∀ p, r p ≤ V * ρ p := fun p => mul_le_mul_of_nonneg_right (hsI p).2 (hρ p).le
  let η : X i → X i → ℝ := fun p => (hη p).choose
  have hηs : ∀ p, _ := fun p => (hη p).choose_spec
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
  obtain ⟨J, hfin, hdisj, hmeet, -, himp⟩ := hAl (X i) (g i) (mX i) (hmetric i) Ns C (mN := mNs)
    (mC := mC) (fun p => (hhom p).symm (q p)) o (fun p => (hRCD p).some) (fun _ => δ) η r ρ hρc
    hρ hT ((mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)).trans hTΛ) hTV hlower
    hupper
  obtain ⟨hshell, hcover, hcoord, hend⟩ := himp fun j _ => ⟨hbuf j, (hmod j).2.2.1,
    (hmod j).2.2.2.1, (hmod j).2.2.2.2, hδδ'.trans_le (min_le_left _ _), hKL j, (hrad j).1,
    fun x y => ((hrad j).2 x y).trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (mul_nonneg (inv_nonneg.mpr (hr j).le) dist_nonneg))⟩
  -- LPA06's zero cutoffs on the same selection
  obtain ⟨L, hL0, hcut, hcutdisj⟩ := selected_zero_cutoffs (I := I3) (g i) J r hr hdisj η O
    hεpos.le he1 (fun j _ => @LipschitzWith.continuous (X i) ℝ
      ((mX i).rescale (r j)⁻¹ (inv_pos.mpr (hr j))).toPseudoEMetricSpace _ _ _ (hηs j).1) (fun j _ => (hO j).1)
    (fun j _ => (hO j).2.2.1)
    (fun j _ x hx => (hO j).2.1 ⟨hx.1, hx.2.trans (by norm_num)⟩) (fun j _ x => hclose j x)
    (fun j _ q' hq' => ((hηs j).2.2.2.2.2.2.2.1 q'
      ((hηs j).2.2.2.2.2.2.2.2.2.1 ⟨hq'.1, hq'.2.trans (by norm_num)⟩)).2)
  refine ⟨Ns, C, mNs, cNs, hNs, mC, o, fun b => ⟨(hmod b).2.1, hCp b, hRCD b,
    ⟨(hhom b).symm (q b), (hmod b).2.2.2.2⟩, N b, mN b, cN b, hMN b, G b, hconn b, hRiem b,
    hsecG b, ⟨{ toEquiv := (hhom b).toEquiv, isometry_toFun := (hmod b).1 }⟩⟩, ?_⟩
  let Z : ZeroModelFamily I3 (X i) (g i) ρ hρ β Ns C o δ (min εa ε₄) e T V :=
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
  refine ⟨Z, fun c _ => hbuf c, fun c hc => hshell c hc, fun c hc => hcoord c hc, ?_, L, hL0,
    fun c hc => hcut c hc, fun c hc c' hc' hcc' => hcutdisj hc hc' hcc'⟩
  intro c hc q' hq1 hq2 lam hlam hΛ'
  exact h73 (X i) (g i) (hmetric i) c (r c) (hr c) (hbuf c) (C c) (o c) (hRCD c).some (hKL c).some
    (hδδ'.trans_le (min_le_right _ _)) (η c) (hrad c).1
    (fun x y => ((hrad c).2 x y).trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (mul_nonneg (inv_nonneg.mpr (hr c).le) dist_nonneg)))
    q' hq1 hq2 lam hlam ((le_max_right _ _).trans hΛ')

end DifferentialGeometry.Geometry.Collapse
