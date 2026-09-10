import Batteries.Tactic.Alias
import DifferentialGeometry.Analysis.Calculus.SecondDerivative
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Geometry.Curvature.CompactPositive
import DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import DifferentialGeometry.Geometry.Comparison.Variation.RadialCurvatureEstimate
import DifferentialGeometry.Geometry.Comparison.Variation.CurveEnergy
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Riemannian.Variation
open Poincare.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [BoundarylessManifold I M] [T2Space (TangentBundle I M)]

private def variationHalfEnergy
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s : ℝ) : ℝ :=
  (1 / 2 : ℝ) * curveEnergy (I := I) g (fun t : ℝ ↦ f s t) 0 L

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space (TangentBundle I M)] in
private lemma variationHalfEnergy_differentiable
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hf : IsSmoothVariation (I := I) f) :
    Differentiable ℝ (variationHalfEnergy (I := I) g f L) := by
  intro s
  exact ((curveEnergy_hasDerivAt (I := I) (M := M) g f hf 0 L s).const_mul
    (1 / 2 : ℝ)).differentiableAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space (TangentBundle I M)] in
private lemma riemannianEDistOf_sq_le_variation_energy
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L s : ℝ)
    (hf : IsSmoothVariation (I := I) f) (hL : 0 ≤ L) :
    (riemannianEDistOf (I := I) g (f s 0) (f s L)).toReal ^ 2 ≤
      L * curveEnergy (I := I) g (fun t : ℝ ↦ f s t) 0 L := by
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) (fun t : ℝ ↦ f s t) := by
      have hincl : ContMDiff 𝓘(ℝ, ℝ)
          (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
          (fun t : ℝ ↦ (s, t)) := contMDiff_const.prodMk contMDiff_id
      exact (hf : ContMDiff _ _ _ _).comp hincl
  have hcontinuous : Continuous (fun t : ℝ ↦ speedSq (I := I) g f s t) := by
      exact (speedSq_contDiff (I := I) (M := M) g f hf).continuous.comp
        (continuous_const.prodMk continuous_id)
  simpa only [sub_zero] using
    riemannianEDistOf_toReal_sq_le_curveEnergy (I := I) g hL
      (hsmooth.of_le (by norm_num)).contMDiffOn
      hcontinuous.continuousOn.integrableOn_Icc

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [T2Space (TangentBundle I M)] in
private lemma variationHalfEnergy_zero_eq
    (g : SmoothRiemannianMetric I M) (f : ℝ → ℝ → M) (L : ℝ)
    (hL : 0 ≤ L)
    (hunit : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (f 0 t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ)) = 1) :
    variationHalfEnergy (I := I) g f L 0 = L / 2 := by
  have henergy : curveEnergy (I := I) g (fun t : ℝ ↦ f 0 t) 0 L = L := by
    change (∫ t in (0 : ℝ)..L,
      g.inner (f 0 t)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ f 0 u) t (1 : ℝ))) = L
    calc
      _ = ∫ _t in (0 : ℝ)..L, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact hunit t (by simpa only [Set.uIcc_of_le hL] using ht)
      _ = L := by simp
  rw [variationHalfEnergy, henergy]
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem farPoint_noLocalMin_of_geodesicAt
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (C : Set M) (hCne : C.Nonempty) (hCcompact : IsCompact C) :
    ∃ D : Set M,
      IsCompact D ∧ C ⊆ D ∧
      ∀ q : M, q ∉ D → ∀ alpha : ℝ → M,
        IsGeodesicAt (I := I) g alpha 0 →
        alpha 0 ∈ C →
        g.inner (alpha 0)
          (mfderiv 𝓘(ℝ, ℝ) I alpha 0 (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I alpha 0 (1 : ℝ)) = 1 →
        ¬ IsLocalMin
          (fun s : ℝ ↦
            (riemannianEDistOf (I := I) g q (alpha s)).toReal) 0 := by
  classical
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hpositive : 0 < Module.finrank ℝ E :=
    lt_of_lt_of_le (by norm_num) hdim
  let : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt hpositive⟩
  let : ProperSpace M :=
    properSpace_riemMetric_of_complete_metric (I := I) (M := M) g hcomplete
  let hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v ↦ tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨_hKcompact, kappa, hkappa, hmargin⟩ :=
    compact_curvature_margin (I := I) g hcomplete hsec hdim C hCcompact hCne
  let R : ℝ := max 2 (4 / kappa) + 1
  let D : Set M := Metric.cthickening R C
  have hRtwo : 2 < R := by
    dsimp only [R]
    linarith [le_max_left (2 : ℝ) (4 / kappa)]
  have hRkappa : 4 / kappa < R := by
    dsimp only [R]
    linarith [le_max_right (2 : ℝ) (4 / kappa)]
  refine ⟨D, hCcompact.cthickening, Metric.self_subset_cthickening C, ?_⟩
  intro q hq alpha halphaGeodesic halphaC halphaUnit halphaMin
  let x : M := alpha 0
  have hxC : x ∈ C := halphaC
  have hqFar : R < dist q x := by
    apply lt_of_not_ge
    intro hdist
    apply hq
    exact Metric.mem_cthickening_of_dist_le q x R C hxC hdist
  let L : ℝ := (riemannianEDistOf (I := I) g q x).toReal
  have hdistL : dist q x = L := by
    rw [riemMetric_dist_eq (I := I) (M := M) q x]
    dsimp only [L]
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
  have hRL : R < L := by rwa [← hdistL]
  have hLtwo : 2 < L := hRtwo.trans hRL
  have hLpos : 0 < L := lt_trans (by norm_num) hLtwo
  have hkappaL : 4 / kappa < L := hRkappa.trans hRL
  have hfin : riemannianEDistOf (I := I) g q x ≠ (⊤ : ENNReal) := by
    rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm]
    exact riemannianEDist_ne_top (I := I) q x
  obtain ⟨v, hvExp, hvNorm⟩ :=
    minExp_of_complete_metric (I := I) (M := M) g hcomplete q x hfin
  have hvNormL : Real.sqrt (g.inner q v v) = L := by
    exact hvNorm.trans (by
      dsimp only [L]
      rw [riemannianEDistOf_eq_riemannianEDist (I := I) g hEnorm])
  have hvInner : g.inner q v v = L ^ 2 := by
    rw [← Real.sq_sqrt (gInner_self_nonneg (I := I) g q v), hvNormL]
  let w : TangentSpace I q := L⁻¹ • v
  have hwUnit : g.inner q w w = 1 := by
    dsimp only [w]
    rw [gInner_smul_self (I := I) g q L⁻¹ v, hvInner]
    rw [← mul_pow, inv_mul_cancel₀ hLpos.ne', one_pow]
  have hLw : L • w = v := by
    dsimp only [w]
    rw [smul_smul, mul_inv_cancel₀ hLpos.ne', one_smul]
  let gamma : ℝ → M := intrinsicGeodesic (I := I) g hEnorm q w
  have hgammaSmooth : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma := by
    exact intrinsicGeodesic_contMDiff (I := I) g hEnorm q w
  have hgammaGeodesic : IsGeodesic (I := I) g gamma :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm q w
  have hgammaZero : gamma 0 = q :=
    intrinsicGeodesic_zero (I := I) g hEnorm q w
  have hgammaL : gamma L = x := by
    change intrinsicGeodesic (I := I) g hEnorm q w L = x
    calc
      intrinsicGeodesic (I := I) g hEnorm q w L =
          expMapIntrinsic (I := I) g hEnorm q (L • w) := by
        rw [expMapIntrinsic_def]
        exact (intrinsicGeodesic_smul (I := I) g hEnorm q w L).symm
      _ = expMapIntrinsic (I := I) g hEnorm q v := by rw [hLw]
      _ = x := hvExp
  have hgammaUnit : ∀ t : ℝ,
      g.inner (gamma t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) = 1 := by
    intro t
    exact (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm q w t).trans hwUnit
  let vL : TangentSpace I (gamma L) :=
    (mfderiv 𝓘(ℝ, ℝ) I alpha 0 (1 : ℝ) : E)
  have hvLUnit : g.inner (gamma L) vL vL = 1 := by
    rw [hgammaL]
    exact halphaUnit
  have halphaZero : alpha 0 = gamma L := by
    rw [hgammaL]
  have halphaVelocity :
      (mfderiv 𝓘(ℝ, ℝ) I alpha 0 (1 : ℝ) : E) = vL := rfl
  obtain ⟨V⟩ := exists_radialEndpointVariation
    (I := I) g gamma alpha L hLpos hgammaSmooth
      (hgammaGeodesic.isGeodesicOn (Set.Icc 0 L))
      (fun t _ht ↦ hgammaUnit t) vL hvLUnit halphaGeodesic
      halphaZero halphaVelocity
  let energy : ℝ → ℝ := variationHalfEnergy (I := I) g V.variation L
  have henergyZero : energy 0 = L / 2 := by
    exact variationHalfEnergy_zero_eq (I := I) g V.variation L hLpos.le
      V.centralUnitSpeed
  have hvariationInitial (s : ℝ) : V.variation s 0 = q := by
    calc
      V.variation s 0 = V.variation 0 0 := V.fixedInitial s
      _ = V.baseCurve 0 := V.central 0
      _ = gamma 0 := V.agrees 0 ⟨le_rfl, hLpos.le⟩
      _ = q := hgammaZero
  have henergyMin : IsLocalMin energy 0 := by
    filter_upwards [halphaMin, V.terminalGerm] with s hdistance hterminal
    have hdistanceLower : L ≤
        (riemannianEDistOf (I := I) g q (alpha s)).toReal := by
      simpa only [x, L] using hdistance
    have hbound := riemannianEDistOf_sq_le_variation_energy
      (I := I) g V.variation L s V.smooth hLpos.le
    rw [hvariationInitial s, hterminal] at hbound
    have hdistanceNonneg :
        0 ≤ (riemannianEDistOf (I := I) g q (alpha s)).toReal :=
      ENNReal.toReal_nonneg
    have hcurveEnergy : L ≤
        curveEnergy (I := I) g (fun t : ℝ ↦ V.variation s t) 0 L := by
      nlinarith
    rw [henergyZero]
    dsimp only [energy, variationHalfEnergy]
    nlinarith
  have henergyDifferentiable : Differentiable ℝ energy :=
    variationHalfEnergy_differentiable (I := I) g V.variation L V.smooth
  have hsecondNonneg : 0 ≤ deriv (deriv energy) 0 :=
    second_derivative_nonneg_of_isLocalMin henergyMin henergyDifferentiable
  have hfirst := firstVariation_curveEnergy_geodesic_fixedInitial
    (I := I) (M := M) g (fun t : ℝ ↦ V.variation 0 t)
      V.variation L V.smooth hLpos V.centralGeodesic
      (fun _t ↦ rfl) V.fixedInitial V.centralUnitSpeed
  have hfirstHalf : HasDerivAt energy
      (g.inner (V.variation 0 L)
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation u L) 0 (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation 0 u) L (1 : ℝ))) 0 := by
    change HasDerivAt
      (fun s : ℝ ↦ (1 / 2 : ℝ) *
        curveEnergy (I := I) g (fun t : ℝ ↦ V.variation s t) 0 L) _ 0
    convert hfirst.const_mul (1 / 2 : ℝ) using 1
    all_goals first | rfl | ring
  have hpairZero : g.inner (V.variation 0 L)
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation u L) 0 (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation 0 u) L (1 : ℝ)) = 0 := by
    rw [← hfirstHalf.deriv]
    exact henergyMin.deriv_eq_zero
  have hcentralEq : (fun t : ℝ ↦ V.variation 0 t) = V.baseCurve :=
    funext V.central
  have hterminalVelocity :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation u L) 0 (1 : ℝ) : E) =
        (V.parallelField L : E) := by
    rw [V.terminalGerm.mfderiv_eq]
    exact V.parallelTerminalVelocity.symm
  have hcentralVelocity :
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation 0 u) L (1 : ℝ) : E) =
        (mfderiv 𝓘(ℝ, ℝ) I gamma L (1 : ℝ) : E) := by
    rw [hcentralEq, (V.agreesGerm L ⟨hLpos.le, le_rfl⟩).mfderiv_eq]
    rfl
  have hperpTerminal : g.inner (gamma L) (V.parallelField L)
      (mfderiv 𝓘(ℝ, ℝ) I gamma L (1 : ℝ)) = 0 := by
    change g.inner (V.variation 0 L)
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation u L) 0 (1 : ℝ) : E)
      (mfderiv 𝓘(ℝ, ℝ) I (fun u : ℝ ↦ V.variation 0 u) L (1 : ℝ) : E) = 0 at hpairZero
    rw [hterminalVelocity, hcentralVelocity] at hpairZero
    rw [V.central L, V.agrees L ⟨hLpos.le, le_rfl⟩] at hpairZero
    exact hpairZero
  have hperp : ∀ t ∈ Set.Icc (0 : ℝ) L,
      g.inner (gamma t) (V.parallelField t)
        (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) = 0 := by
    intro t ht
    exact (V.parallel_inner_velocity_eq_terminal
      hgammaSmooth hgammaGeodesic t ht).trans hperpTerminal
  have hnonnegative := hsec.toNonnegative (I := I)
  have hcurvNonneg : ∀ t ∈ Set.Icc (0 : ℝ) L,
      0 ≤ g.inner (V.variation 0 t)
        ((riemannOp (LeviCivita (I := I) g) (V.variation 0 t))
          (V.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ)))
        (V.parallelField t) := by
    intro t _ht
    have hnonneg : 0 ≤ g.inner (V.variation 0 t) (V.parallelField t : E)
        ((riemannOp (LeviCivita (I := I) g) (V.variation 0 t))
          (V.parallelField t : E)
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ) : E)
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ) : E)) :=
      riemann_contraction_nonneg hnonnegative _ _ _
    exact hnonneg.trans_eq (g.symm (V.variation 0 t) _ _)
  have hcurvLower : ∀ t ∈ Set.Icc (L - 1) L,
      kappa ≤ g.inner (V.variation 0 t)
        ((riemannOp (LeviCivita (I := I) g) (V.variation 0 t))
          (V.parallelField t)
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
          (mfderiv 𝓘(ℝ, ℝ) I
            (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ)))
        (V.parallelField t) := by
    intro t ht
    have htFull : t ∈ Set.Icc (0 : ℝ) L := ⟨by linarith [ht.1, hLtwo], ht.2⟩
    have hsegment := intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm q w (s := t) (t := L) ht.2
    have hsegmentReal : dist (gamma t) (gamma L) ≤ L - t := by
      have hleftFinite : riemannianEDist I (gamma t) (gamma L) ≠ ⊤ :=
        riemannianEDist_ne_top (I := I) (gamma t) (gamma L)
      have hrightFinite : ENNReal.ofReal
          (Real.sqrt (g.inner q w w) * (L - t)) ≠ ⊤ := ENNReal.ofReal_ne_top
      have hreal := (ENNReal.toReal_le_toReal hleftFinite hrightFinite).2 hsegment
      rw [riemMetric_dist_eq (I := I) (M := M) (gamma t) (gamma L)]
      simpa only [hwUnit, Real.sqrt_one, one_mul,
        ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)] using hreal
    have hpointC : gamma t ∈ Metric.cthickening 1 C := by
      apply Metric.mem_cthickening_of_dist_le (gamma t) x 1 C hxC
      rw [← hgammaL]
      exact hsegmentReal.trans (by linarith [ht.1])
    have hPunit : g.inner (V.variation 0 t)
        (V.parallelField t) (V.parallelField t) = 1 := by
      rw [V.central t]
      exact V.parallelUnit t htFull
    have hTunit : g.inner (V.variation 0 t)
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ)) = 1 :=
      V.centralUnitSpeed t htFull
    have hcentralVelocityAt :
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ) : E) =
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ) : E) := by
      rw [hcentralEq, (V.agreesGerm t htFull).mfderiv_eq]
      rfl
    have hPT : g.inner (V.variation 0 t) (V.parallelField t)
        (mfderiv 𝓘(ℝ, ℝ) I
          (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ)) = 0 := by
      rw [hcentralVelocityAt]
      rw [V.central t, V.agrees t htFull]
      exact hperp t htFull
    have hbase : V.variation 0 t ∈ Metric.cthickening 1 C := by
      rw [V.central t, V.agrees t htFull]
      exact hpointC
    have hbound := hmargin (V.variation 0 t) hbase
      (V.parallelField t)
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
      hPunit hTunit hPT
    rw [rm04_eq_inner_riem (I := I) (M := M) g (V.variation 0 t)
      (V.parallelField t)
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) I
        (fun u : ℝ ↦ V.variation 0 u) t (1 : ℝ))
      (V.parallelField t)] at hbound
    exact hbound.trans_eq (g.symm (V.variation 0 t) _ _)
  have hsecondUpper : deriv (deriv energy) 0 ≤ 1 / L - kappa / 4 := by
    change deriv
      (fun s : ℝ ↦ deriv
        (fun r : ℝ ↦ (1 / 2 : ℝ) *
          curveEnergy (I := I) g (fun t : ℝ ↦ V.variation r t) 0 L) s) 0 ≤
      1 / L - kappa / 4
    exact V.secondVariation_half_energy_le_inv_sub_quarter
      hkappa hLtwo hcurvNonneg hcurvLower
  have hstrict : 1 / L - kappa / 4 < 0 := by
    have hcross : 4 < kappa * L := by
      have := (div_lt_iff₀ hkappa).mp hkappaL
      nlinarith
    have hinv : 1 / L < kappa / 4 := by
      exact (div_lt_div_iff₀ hLpos (by norm_num : (0 : ℝ) < 4)).2 (by
        nlinarith)
    linarith
  have : deriv (deriv energy) 0 < 0 :=
    lt_of_le_of_lt hsecondUpper hstrict
  exact (not_lt_of_ge hsecondNonneg) this

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem farPoint_noLocalMin_distance
    [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (C : Set M) (hCne : C.Nonempty) (hCcompact : IsCompact C) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun x : M ↦ TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M :=
      (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ∃ D : Set M,
      IsCompact D ∧ C ⊆ D ∧
      ∀ q : M, q ∉ D → ∀ alpha : ℝ → M,
        isUnitSpeedGeodesicGermIn (I := I) g C alpha →
        ¬ IsLocalMin (fun s : ℝ ↦ dist q (alpha s)) 0 := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M :=
    (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  let : MetricSpace M := riemMetricSpace (I := I) (M := M)
  obtain ⟨D, hDcompact, hCD, hD⟩ :=
    farPoint_noLocalMin_of_geodesicAt (I := I) g hcomplete hsec hdim
      C hCne hCcompact
  refine ⟨D, hDcompact, hCD, ?_⟩
  intro q hq alpha halpha
  obtain ⟨epsilon, hepsilon, hgeodesicAtZero, _hsmooth, _hgeodesicOn,
    hunit, hmaps⟩ := halpha
  have hzero : (0 : ℝ) ∈ Set.Ioo (-epsilon) epsilon := by
    exact ⟨by linarith, hepsilon⟩
  have hcanonical : ∀ s : ℝ,
      dist q (alpha s) =
        (riemannianEDistOf (I := I) g q (alpha s)).toReal := by
    intro s
    rw [riemMetric_dist_eq (I := I) (M := M) q (alpha s)]
    rw [← riemannianEDistOf_eq_riemannianEDist (I := I) g]
    exact fun x v ↦
      tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  intro hlocal
  apply hD q hq alpha hgeodesicAtZero (hmaps hzero) (hunit 0 hzero)
  simpa only [hcanonical] using hlocal

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

alias farPoint_noLocalMin_of_geodesicAt := DifferentialGeometry.Geometry.farPoint_noLocalMin_of_geodesicAt
alias farPoint_noLocalMin_distance := DifferentialGeometry.Geometry.farPoint_noLocalMin_distance

end Poincare.Geometry
