import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.JacobiLocal
import DifferentialGeometry.Geometry.Comparison.Volume.Radial.Gram
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Filter Set Bundle
open scoped ContDiff Manifold Matrix.Norms.Elementwise Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

private noncomputable def familyCoeffMap
    {ι : Type*} [Fintype ι] (v : ι → E) :
    EuclideanSpace ℝ ι →ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  (toEuclidean (E := E)).toLinearEquiv.toLinearMap.comp
    ((Fintype.linearCombination ℝ v).comp
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap)

omit [NeZero (Module.finrank ℝ E)] in
private lemma familyCoeffMap_apply
    {ι : Type*} [Fintype ι] (v : ι → E)
    (c : EuclideanSpace ℝ ι) :
    familyCoeffMap (E := E) v c =
      toEuclidean (E := E) (∑ i, c i • v i) := by
  change toEuclidean (E := E) (∑ i, c i • v i) =
    toEuclidean (E := E) (∑ i, c i • v i)
  rfl

omit [NeZero (Module.finrank ℝ E)] in
private lemma exists_coeff_ge
    {ι : Type*} [Fintype ι]
    (v : ι → E) (hv : LinearIndependent ℝ v) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ c : EuclideanSpace ℝ ι, ‖c‖ = 1 →
        δ ≤ ‖familyCoeffMap (E := E) v c‖ := by
  have hinj : Function.Injective (familyCoeffMap (E := E) v) := by
    intro c d hcd
    apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).injective
    apply hv.fintypeLinearCombination_injective
    apply (toEuclidean (E := E)).injective
    exact hcd
  rcases (familyCoeffMap (E := E) v).injective_iff_antilipschitz.mp hinj with
    ⟨K, _hK, hanti⟩
  refine ⟨1 / ((K : ℝ) + 1), by positivity, ?_⟩
  intro c hc
  have hdist := hanti.le_mul_dist c 0
  have hone : 1 ≤ (K : ℝ) * ‖familyCoeffMap (E := E) v c‖ := by
    simpa only [dist_zero_right, hc, map_zero, norm_zero] using hdist
  have hK_le : (K : ℝ) ≤ (K : ℝ) + 1 := by linarith
  have hone' : 1 ≤ ((K : ℝ) + 1) * ‖familyCoeffMap (E := E) v c‖ :=
    hone.trans (mul_le_mul_of_nonneg_right hK_le (norm_nonneg _))
  exact (div_le_iff₀ (by positivity : 0 < (K : ℝ) + 1)).2 (by
    simpa only [one_mul, mul_comm] using hone')

omit [NeZero (Module.finrank ℝ E)] in
private lemma chartCoeff_sum
    (w : E) :
    (∑ i, (toEuclidean (E := E) w) i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) = w := by
  let b :=
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
  have hsum :
      toEuclidean (E := E) w =
        ∑ i, (toEuclidean (E := E) w) i •
          EuclideanSpace.single i (1 : ℝ) := by
    simpa [b, EuclideanSpace.basisFun_apply] using
      (b.sum_repr (toEuclidean (E := E) w)).symm
  calc
    (∑ i, (toEuclidean (E := E) w) i • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) =
        (toEuclidean (E := E)).symm
          (∑ i, (toEuclidean (E := E) w) i •
            EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
      simp only [map_smul, DifferentialGeometry.Tensor.Coordinates.chartModelBasis_apply]
    _ = (toEuclidean (E := E)).symm (toEuclidean (E := E) w) :=
      congrArg (toEuclidean (E := E)).symm hsum.symm
    _ = w := (toEuclidean (E := E)).symm_apply_apply w

omit [NeZero (Module.finrank ℝ E)] in
private lemma abs_quad_sub_le
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (c : EuclideanSpace ℝ ι) (hc : ‖c‖ = 1) :
    |dotProduct (⇑c) (Matrix.mulVec (A - B) (⇑c))| ≤
      (Fintype.card ι : ℝ) ^ 2 * ‖A - B‖ := by
  classical
  have hc_le (i : ι) : |c i| ≤ 1 := by
    rw [← Real.norm_eq_abs, ← hc]
    exact PiLp.norm_apply_le c i
  have hentry (i j : ι) : |(A - B) i j| ≤ ‖A - B‖ := by
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm ((A - B) i) j).trans
      (norm_le_pi_norm (A - B) i)
  have hexpand :
      dotProduct (⇑c) (Matrix.mulVec (A - B) (⇑c)) =
        ∑ i, ∑ j, c i * ((A - B) i j * c j) := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  rw [hexpand]
  calc
    |∑ i, ∑ j, c i * ((A - B) i j * c j)| ≤
        ∑ i, |∑ j, c i * ((A - B) i j * c j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |c i * ((A - B) i j * c j)| := by
      exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖A - B‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_mul]
      rw [← mul_assoc]
      have hpair : |c i| * |(A - B) i j| ≤ 1 * ‖A - B‖ :=
        mul_le_mul (hc_le i) (hentry i j) (abs_nonneg _) zero_le_one
      exact (mul_le_mul hpair (hc_le j) (abs_nonneg _)
        (mul_nonneg zero_le_one (norm_nonneg _))).trans_eq (by ring)
    _ = (Fintype.card ι : ℝ) ^ 2 * ‖A - B‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

omit [NeZero (Module.finrank ℝ E)] in
private lemma quad_sub
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (c : ι → ℝ) :
    dotProduct c (Matrix.mulVec (A - B) c) =
      dotProduct c (Matrix.mulVec A c) -
        dotProduct c (Matrix.mulVec B c) := by
  classical
  simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum :
      ∑ j, (A i j - B i j) * c j =
        (∑ j, A i j * c j) - ∑ j, B i j * c j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  ring

omit [T2Space M]
  [SigmaCompactSpace M] in
theorem exists_radial_base
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ∀ d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖d‖ = 1 →
          B ^ 2 ≤
            g.inner (radialCurve (I := I) g p x t)
              (radialJacobiField (I := I) g p (t • x)
                (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1)
              (radialJacobiField (I := I) g p (t • x)
                (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1) := by
  classical
  let n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := NeZero.pos n
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨B₀, hB₀, hunit⟩ := exists_unitCoeff_ge (I := I) g p
  let ε : ℝ := B₀ ^ 2 / (2 * (n : ℝ) ^ 2)
  have hε : 0 < ε := by
    dsimp only [ε]
    positivity
  let A₀ := normalGramMatrix (I := I) g p 0
  have hclose0 : ∀ᶠ y in 𝓝 (0 : E),
      normalGramMatrix (I := I) g p y ∈ Metric.ball A₀ ε :=
    (normalGram_contAt (I := I) g p)
      (Metric.ball_mem_nhds A₀ hε)
  have htx : Tendsto (fun t : ℝ => t • x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hc0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    change Tendsto (fun t : ℝ => t • x) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 (0 : E))
    exact hc0.mono_left inf_le_left
  have hclose : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      normalGramMatrix (I := I) g p (t • x) ∈ Metric.ball A₀ ε :=
    htx.eventually hclose0
  have hsrc : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t • x ∈ (expMapDiffeo (I := I) g p).source :=
    htx.eventually ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have hrad : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖t • x‖ < expMapC2Radius (I := I) g p := by
    have hball := htx.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hzeroRad : ‖(0 : E)‖ < expMapC2Radius (I := I) g p := by
    simpa using expMapC2Radius_pos (I := I) g p
  have hzeroSource : (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
    zero_mem_expMapDiffeo_source (I := I) g p
  have hbaseQuad
      (d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      dotProduct (⇑d) (Matrix.mulVec A₀ (⇑d)) =
        g.inner p (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
          (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
    dsimp only [A₀]
    rw [normalGram_radialMat (I := I) g p hzeroSource hzeroRad]
    rw [radialJacobiGram_quadratic (I := I) g p]
    have hpoint :
        (expMap (I := I) g p
          (show TangentSpace I p from (0 : E)) : M) = p :=
      expMap_zero (I := I) g p
    rw [hpoint]
    have hJzero (j : Fin (Module.finrank ℝ E)) :
        radialJacobiField (I := I) g p 0 ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1 =
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j := by
      rw [radialJacobi_one (I := I) g p 0 _ hzeroRad]
      simp only [tangentSpaceModelContinuousLinearEquiv_symm_apply]
      rw [mfderiv_expMap_at_zero (I := I) g p]
      rfl
    simp_rw [hJzero]
    rfl
  have hscale : (n : ℝ) ^ 2 * ε = B₀ ^ 2 / 2 := by
    dsimp only [ε]
    field_simp [ne_of_gt hnR]
  refine ⟨B₀ / 2, div_pos hB₀ (by norm_num), ?_⟩
  filter_upwards [hclose, hsrc, hrad] with t hcloseT hsrcT hradT
  intro d hd
  let A := normalGramMatrix (I := I) g p (t • x)
  have hnorm : ‖A - A₀‖ < ε := by
    simpa only [A, Metric.mem_ball, dist_eq_norm] using hcloseT
  have hpert := abs_quad_sub_le A A₀ d hd
  have hpertN :
      |dotProduct (⇑d) (Matrix.mulVec (A - A₀) (⇑d))| ≤
        (n : ℝ) ^ 2 * ‖A - A₀‖ := by
    simpa only [Fintype.card_fin, n] using hpert
  have hpert' :
      |dotProduct (⇑d) (Matrix.mulVec A (⇑d)) -
          dotProduct (⇑d) (Matrix.mulVec A₀ (⇑d))| < B₀ ^ 2 / 2 := by
    rw [← quad_sub A A₀ (⇑d)]
    exact hpertN.trans_lt
      ((mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos hnR)).trans_eq hscale)
  have hbaseNonneg : 0 ≤
      g.inner p (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
        (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) := by
    have hself (w : E) : 0 ≤ g.inner p w w := by
      by_cases hw : w = 0
      · subst w
        have hz : g.inner p (0 : E) = (0 : E →L[ℝ] ℝ) :=
          (g.inner p).map_zero
        have hz' : g.inner p (0 : E) (0 : E) = 0 := by
          calc
            g.inner p (0 : E) (0 : E) = (0 : E →L[ℝ] ℝ) (0 : E) :=
              congrArg (fun L : E →L[ℝ] ℝ => L (0 : E)) hz
            _ = 0 := rfl
        exact hz'.ge
      · exact (g.pos p w hw).le
    exact hself _
  have hbaseLower : B₀ ^ 2 ≤
      dotProduct (⇑d) (Matrix.mulVec A₀ (⇑d)) := by
    rw [hbaseQuad d]
    have hsqrt := hunit d hd
    nlinarith [Real.sq_sqrt hbaseNonneg]
  have hquadLower : (B₀ / 2) ^ 2 ≤
      dotProduct (⇑d) (Matrix.mulVec A (⇑d)) := by
    rcases abs_lt.mp hpert' with ⟨hlo, _⟩
    nlinarith [sq_pos_of_pos hB₀]
  have hAt : dotProduct (⇑d) (Matrix.mulVec A (⇑d)) =
      g.inner (radialCurve (I := I) g p x t)
        (radialJacobiField (I := I) g p (t • x)
          (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1)
        (radialJacobiField (I := I) g p (t • x)
          (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1) := by
    dsimp only [A]
    rw [normalGram_radialMat (I := I) g p hsrcT hradT]
    rw [radialJacobiGram_quadratic (I := I) g p]
    change g.inner (radialCurve (I := I) g p x t)
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1)
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1) = _
    have hsum :
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) 1) =
          radialJacobiField (I := I) g p (t • x)
            (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1 :=
      (radialJacobi_one_sum (I := I) g p (t • x) (⇑d) hradT).symm
    exact congrArg
      (fun z => g.inner (radialCurve (I := I) g p x t) z z) hsum
  rwa [hAt] at hquadLower

omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialRatio_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (v : ι → E)
    (q B : ℝ) (hq : 0 ≤ q) (hB : 0 < B)
    (hv : LinearIndependent ℝ v)
    (hone : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ c : EuclideanSpace ℝ ι, ‖c‖ = 1 →
        B ^ 2 ≤
          g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p (t • x)
              (∑ i, c i • v i) 1)
            (radialJacobiField (I := I) g p (t • x)
              (∑ i, c i • v i) 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g (radialCurve (I := I) g p x)
            (fun i => radialJacobiField (I := I) g p x (v i)) t /
          hyperbolicDensity q (Fintype.card ι) t := by
  have htx : Tendsto (fun t : ℝ => t • x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hc0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    change Tendsto (fun t : ℝ => t • x) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 (0 : E))
    exact hc0.mono_left inf_le_left
  have hsrc : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t • x ∈ (expMapDiffeo (I := I) g p).source := by
    exact htx.eventually ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have hrad : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖t • x‖ < expMapC2Radius (I := I) g p := by
    have hball := htx.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hLI : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      LinearIndependent ℝ fun i =>
        radialJacobiField (I := I) g p x (v i) t := by
    filter_upwards [hsrc, hrad, self_mem_nhdsWithin] with t htsrc htrad ht
    change 0 < t at ht
    exact radialJacobi_li (I := I) g p x hv ht.ne' htsrc htrad
  have hdir : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ c : EuclideanSpace ℝ ι, ‖c‖ = 1 →
        (B * t) ^ 2 ≤
          g.inner (radialCurve (I := I) g p x t)
            (∑ i, c i • radialJacobiField (I := I) g p x (v i) t)
            (∑ i, c i • radialJacobiField (I := I) g p x (v i) t) := by
    filter_upwards [hone, hrad, self_mem_nhdsWithin] with t honeT htrad ht
    change 0 < t at ht
    intro c hc
    let J := radialJacobiField (I := I) g p (t • x) (∑ i, c i • v i) 1
    have hsum :
        (∑ i, c i • radialJacobiField (I := I) g p x (v i) t) = t • J := by
      rw [← radialJacobi_sum_at (I := I) g p x v (⇑c) t htrad]
      rw [radialJacobi_scale (I := I) g p x (∑ i, c i • v i) t]
      dsimp only [J]
      rw [radialJacobi_one_smul (I := I) g p (t • x)
        (∑ i, c i • v i) t htrad]
    have hscale_aux (z : TangentSpace I (radialCurve (I := I) g p x t)) :
        g.inner (radialCurve (I := I) g p x t) (t • z) (t • z) =
          t ^ 2 * g.inner (radialCurve (I := I) g p x t) z z := by
      rw [map_smul (g.inner _), smul_apply,
        map_smul (g.inner _ z), smul_eq_mul, smul_eq_mul]
      ring
    have hscale : g.inner (radialCurve (I := I) g p x t) (t • J) (t • J) =
        t ^ 2 * g.inner (radialCurve (I := I) g p x t) J J := hscale_aux J
    calc
      (B * t) ^ 2 ≤
          g.inner (radialCurve (I := I) g p x t) (t • J) (t • J) := by
            rw [hscale]
            calc
              (B * t) ^ 2 = t ^ 2 * B ^ 2 := by ring
              _ ≤ t ^ 2 * g.inner (radialCurve (I := I) g p x t) J J :=
                mul_le_mul_of_nonneg_left (honeT c hc) (sq_nonneg t)
      _ = g.inner (radialCurve (I := I) g p x t)
          (∑ i, c i • radialJacobiField (I := I) g p x (v i) t)
          (∑ i, c i • radialJacobiField (I := I) g p x (v i) t) := by
            exact (congrArg (fun z =>
              g.inner (radialCurve (I := I) g p x t) z z) hsum).symm
  exact denRatio_ge_of_dir (I := I) g (radialCurve (I := I) g p x)
    (fun i => radialJacobiField (I := I) g p x (v i)) q B hq hB hLI hdir

omit [T2Space M]
  [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem radialRatio_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (v : ι → E)
    (q B : ℝ) (hq : 0 ≤ q) (hB : 0 < B)
    (hv : LinearIndependent ℝ v)
    (hbase : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖d‖ = 1 →
        B ^ 2 ≤
          g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p (t • x)
              (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1)
            (radialJacobiField (I := I) g p (t • x)
              (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g (radialCurve (I := I) g p x)
            (fun i => radialJacobiField (I := I) g p x (v i)) t /
          hyperbolicDensity q (Fintype.card ι) t := by
  rcases exists_coeff_ge (E := E) v hv with ⟨δ, hδ, hcoeff⟩
  have htx : Tendsto (fun t : ℝ => t • x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hc0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    change Tendsto (fun t : ℝ => t • x) (𝓝 0 ⊓ 𝓟 (Ioi 0)) (𝓝 (0 : E))
    exact hc0.mono_left inf_le_left
  have hrad : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖t • x‖ < expMapC2Radius (I := I) g p := by
    have hball := htx.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hone : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ c : EuclideanSpace ℝ ι, ‖c‖ = 1 →
        (δ * B) ^ 2 ≤
          g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p (t • x)
              (∑ i, c i • v i) 1)
            (radialJacobiField (I := I) g p (t • x)
              (∑ i, c i • v i) 1) := by
    filter_upwards [hbase, hrad] with t hbaseT htrad
    intro c hc
    let w : E := ∑ i, c i • v i
    let d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      familyCoeffMap (E := E) v c
    have hdge : δ ≤ ‖d‖ := by
      exact hcoeff c hc
    have hdpos : 0 < ‖d‖ := hδ.trans_le hdge
    let u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := ‖d‖⁻¹ • d
    have hu : ‖u‖ = 1 := by
      dsimp only [u]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hdpos)]
      exact inv_mul_cancel₀ hdpos.ne'
    let z : E := ∑ j, u j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j
    have hd : d = toEuclidean (E := E) w := by
      simpa only [d, w] using familyCoeffMap_apply (E := E) v c
    have hdsum : (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) = w := by
      rw [hd]
      exact chartCoeff_sum (E := E) w
    have hdu : d = ‖d‖ • u := by
      dsimp only [u]
      rw [smul_smul]
      simp only [mul_inv_cancel₀ hdpos.ne', one_smul]
    have hsumdu :
        (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) = ‖d‖ • z := by
      calc
        (∑ j, d j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
            ∑ j, (‖d‖ • u) j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j :=
          congrArg (fun a : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ j, a j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) hdu
        _ = ‖d‖ • z := by
          dsimp only [z]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          change (‖d‖ * u j) • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j =
            ‖d‖ • (u j • (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
          rw [mul_smul]
    have hw : w = ‖d‖ • z := by
      rw [← hdsum]
      exact hsumdu
    have hmodel : B ^ 2 ≤
        g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p (t • x) z 1)
          (radialJacobiField (I := I) g p (t • x) z 1) := by
      exact hbaseT u hu
    have hJ :
        radialJacobiField (I := I) g p (t • x) w 1 =
          ‖d‖ • radialJacobiField (I := I) g p (t • x) z 1 := by
      rw [hw]
      exact radialJacobi_one_smul (I := I) g p (t • x) z ‖d‖ htrad
    have hscale :
        g.inner (radialCurve (I := I) g p x t)
            (‖d‖ • radialJacobiField (I := I) g p (t • x) z 1)
            (‖d‖ • radialJacobiField (I := I) g p (t • x) z 1) =
          ‖d‖ ^ 2 *
            g.inner (radialCurve (I := I) g p x t)
              (radialJacobiField (I := I) g p (t • x) z 1)
              (radialJacobiField (I := I) g p (t • x) z 1) := by
      have hscale_aux
          (y : TangentSpace I (radialCurve (I := I) g p x t)) :
          g.inner (radialCurve (I := I) g p x t) (‖d‖ • y) (‖d‖ • y) =
            ‖d‖ ^ 2 * g.inner (radialCurve (I := I) g p x t) y y := by
        rw [map_smul (g.inner _), smul_apply,
          map_smul (g.inner _ y), smul_eq_mul, smul_eq_mul]
        ring
      exact hscale_aux (radialJacobiField (I := I) g p (t • x) z 1)
    have hδsq : δ ^ 2 ≤ ‖d‖ ^ 2 :=
      (sq_le_sq₀ hδ.le (norm_nonneg d)).2 hdge
    calc
      (δ * B) ^ 2 = δ ^ 2 * B ^ 2 := by ring
      _ ≤ ‖d‖ ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_right hδsq (sq_nonneg B)
      _ ≤ ‖d‖ ^ 2 *
          g.inner (radialCurve (I := I) g p x t)
            (radialJacobiField (I := I) g p (t • x) z 1)
            (radialJacobiField (I := I) g p (t • x) z 1) :=
        mul_le_mul_of_nonneg_left hmodel (sq_nonneg ‖d‖)
      _ = g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p (t • x) w 1)
          (radialJacobiField (I := I) g p (t • x) w 1) := by
        rw [hJ, hscale]
      _ = g.inner (radialCurve (I := I) g p x t)
          (radialJacobiField (I := I) g p (t • x)
            (∑ i, c i • v i) 1)
          (radialJacobiField (I := I) g p (t • x)
            (∑ i, c i • v i) 1) := by rfl
  exact radialRatio_ge (I := I) g p x v q (δ * B) hq (mul_pos hδ hB) hv hone

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem curveMean_radialJacobiField_le_hyperbolicMeanCurv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (hu : u ≠ 0)
    (v : ι → E) (hv : LinearIndependent ℝ v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (q L : ℝ) (hq : 0 ≤ q)
    (hdom : ∀ t ∈ Ioo (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun x : E => expMap (I := I) g p (show TangentSpace I p from x)) (t • u)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    ∀ t ∈ Ioo (0 : ℝ) L,
      curveMean (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (v i)) t ≤
      hyperbolicMeanCurv (q * Real.sqrt (g.inner p u u)) (Module.finrank ℝ E - 1) t := by
  by_cases hd0 : Module.finrank ℝ E - 1 = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (hcard.trans hd0)
    intro t ht
    simp [curveMean, Matrix.trace, hyperbolicMeanCurv, hd0]
  have hd : 0 < Module.finrank ℝ E - 1 := Nat.pos_of_ne_zero hd0
  have : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let γ := radialCurve (I := I) g p u
  let V : ι → ∀ t, TangentSpace I (γ t) := fun i => radialJacobiField (I := I) g p u (v i)
  let a : ℝ := Real.sqrt (g.inner p u u)
  have ha : 0 < a := Real.sqrt_pos.mpr (g.pos p u hu)
  have hγ t (ht : t ∈ Ioo (0 : ℝ) L) : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t :=
    ((contMDiffAt_expMap (I := I) g p (hdom t ht)).comp t
      (contMDiff_id.smul (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun _ : ℝ => u))).contMDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hspeed t (ht : t ∈ Ioo (0 : ℝ) L) :
      g.inner (γ t) (curveVelocity (I := I) γ t) (curveVelocity (I := I) γ t) = a ^ 2 :=
    (inner_curveVelocity_expMap_smul (I := I) g p u (hdom t ht)).trans
      (Real.sq_sqrt (g.pos p u hu).le).symm
  have hVperp t (ht : t ∈ Ioo (0 : ℝ) L) i :
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    have h := inner_curveVelocity_radialJacobiField (I := I) g p u (v i) (hdom t ht)
    dsimp only at h
    rw [hperp i, mul_zero] at h
    exact h
  have hDVperp t (ht : t ∈ Ioo (0 : ℝ) L) i :
      g.inner (γ t) (curveVelocity (I := I) γ t) (covDerivAlong (I := I) g γ (V i) t) = 0 :=
    (inner_curveVelocity_covDerivAlong_radialJacobiField (I := I) g p u (v i)
      (hdom t ht)).trans (hperp i)
  have hVdiff t (ht : t ∈ Ioo (0 : ℝ) L) i :
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t :=
    differentiableAt_chartRep_radialJacobiField (I := I) g p u (v i) (hdom t ht)
  have hDVdiff t (ht : t ∈ Ioo (0 : ℝ) L) i :
      DifferentiableAt ℝ (chartRepAt (I := I) γ (covDerivAlong (I := I) g γ (V i)) t) t :=
    differentiableAt_chartRep_covDerivAlong_radialJacobiField (I := I) g p u (v i) (hdom t ht)
  have hLI t (ht : t ∈ Ioo (0 : ℝ) L) : LinearIndependent ℝ (fun i => V i t) :=
    linearIndependent_radialJacobiField (I := I) g p u hv ht.1.ne' (hdom t ht) (hinj t ht)
  have hW t (ht : t ∈ Ioo (0 : ℝ) L) i j :
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 :=
    jacobiWronskian_radialJacobiField_eq_zero (I := I) g p u (v i) (v j) (hdom t ht)
  have hJ t (ht : t ∈ Ioo (0 : ℝ) L) i : IsJacobiAt (I := I) g γ (V i) t :=
    isJacobiAt_radialJacobiField (I := I) g p u (v i) (hdom t ht)
  have hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity (q * a) (Module.finrank ℝ E - 1) t := by
    simpa only [hcard] using!
      (exists_pos_eventually_le_curveDensity_radialJacobiField_div_hyperbolicDensity (I := I)
        g p u v (q * a) hv)
  exact curveMean_le_on (I := I) (n := 1) le_rfl g γ V q a L hq ha hcard hd hγ hspeed
    hVperp hDVperp hVdiff hDVdiff hLI hW hJ hRic hRatioLower

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem antitoneOn_curveDensity_radialJacobiField_div_hyperbolicDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (hu : u ≠ 0)
    (v : ι → E) (hv : LinearIndependent ℝ v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (q L : ℝ) (hq : 0 ≤ q)
    (hdom : ∀ t ∈ Ioo (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun x : E => expMap (I := I) g p (show TangentSpace I p from x)) (t • u)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (v i)) t /
          hyperbolicDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  let γ := radialCurve (I := I) g p u
  let V : ι → ∀ t, TangentSpace I (γ t) := fun i => radialJacobiField (I := I) g p u (v i)
  have hγ t (ht : t ∈ Ioo (0 : ℝ) L) : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t :=
    ((contMDiffAt_expMap (I := I) g p (hdom t ht)).comp t
      (contMDiff_id.smul (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun _ : ℝ => u))).contMDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hVdiff t (ht : t ∈ Ioo (0 : ℝ) L) i :
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t :=
    differentiableAt_chartRep_radialJacobiField (I := I) g p u (v i) (hdom t ht)
  have hLI t (ht : t ∈ Ioo (0 : ℝ) L) : LinearIndependent ℝ (fun i => V i t) :=
    linearIndependent_radialJacobiField (I := I) g p u hv ht.1.ne' (hdom t ht) (hinj t ht)
  have hW t (ht : t ∈ Ioo (0 : ℝ) L) i j :
      jacobiWronskian (I := I) g γ (V i) (V j) t = 0 :=
    jacobiWronskian_radialJacobiField_eq_zero (I := I) g p u (v i) (v j) (hdom t ht)
  exact curveRatio_anti (I := I) (n := 1) le_rfl g γ V
    (q * Real.sqrt (g.inner p u u)) L (Module.finrank ℝ E - 1)
    (mul_nonneg hq (Real.sqrt_nonneg _)) hγ hVdiff hLI hW
    (curveMean_radialJacobiField_le_hyperbolicMeanCurv (I := I) g p u hu v hv hperp
      hcard q L hq hdom hinj hRic)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem curveDensity_radialJacobiField_le_mul_hyperbolicDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) (hu : u ≠ 0)
    (v : ι → E) (hv : LinearIndependent ℝ v)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (q L : ℝ) (hq : 0 ≤ q)
    (hdom : ∀ t ∈ Ioo (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun x : E => expMap (I := I) g p (show TangentSpace I p from x)) (t • u)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    ∀ t ∈ Ioo (0 : ℝ) L,
      curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (v i)) t ≤
      curveDensity (I := I) g (fun _ : ℝ => p)
        (fun i (_ : ℝ) => (show TangentSpace I p from v i)) 0 *
      hyperbolicDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank ℝ E - 1) t := by
  let γ := radialCurve (I := I) g p u
  let V : ι → ∀ t, TangentSpace I (γ t) := fun i => radialJacobiField (I := I) g p u (v i)
  let R : ℝ → ℝ := fun t => curveDensity (I := I) g γ V t /
    hyperbolicDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank ℝ E - 1) t
  let D : ℝ := curveDensity (I := I) g (fun _ : ℝ => p)
    (fun i (_ : ℝ) => (show TangentSpace I p from v i)) 0
  have hlim : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 D) := by
    simpa only [hcard] using!
      (tendsto_curveDensity_radialJacobiField_div_hyperbolicDensity
        (I := I) g p u v (q * Real.sqrt (g.inner p u u)))
  have hanti : AntitoneOn R (Ioo (0 : ℝ) L) :=
    antitoneOn_curveDensity_radialJacobiField_div_hyperbolicDensity (I := I)
      g p u hu v hv hperp hcard q L hq hdom hinj hRic
  intro t ht
  have hupper : ∀ᶠ s in 𝓝[>] (0 : ℝ), R t ≤ R s := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds ht.1).filter_mono inf_le_left]
      with s hs hst
    exact hanti ⟨hs, hst.trans ht.2⟩ ht hst.le
  have hle : R t ≤ D := ge_of_tendsto hlim hupper
  exact (div_le_iff₀ (hyperbolicDensity_pos
    (mul_nonneg hq (Real.sqrt_nonneg _)) ht.1)).mp hle

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
theorem exists_radius_radialJacobiField_comparison
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : E) (v : ι → E) (q b : ℝ),
      ‖x‖ < r →
      x ≠ 0 →
      LinearIndependent ℝ v →
      (∀ i, g.inner p x (v i) = 0) →
      0 ≤ q → b ≤ 1 →
      Fintype.card ι = Module.finrank ℝ E - 1 →
      RicciBoundedBelow (I := I) g
        (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
      (∀ t ∈ Ioo (0 : ℝ) b,
          curveMean (I := I) g (radialCurve (I := I) g p x)
              (fun i => radialJacobiField (I := I) g p x (v i)) t ≤
            hyperbolicMeanCurv (q * Real.sqrt (g.inner p x x))
              (Module.finrank ℝ E - 1) t) ∧
        AntitoneOn
          (fun t =>
            curveDensity (I := I) g (radialCurve (I := I) g p x)
                (fun i => radialJacobiField (I := I) g p x (v i)) t /
              hyperbolicDensity (q * Real.sqrt (g.inner p x x))
                (Module.finrank ℝ E - 1) t)
          (Ioo (0 : ℝ) b) := by
  refine ⟨expMapC2Radius (I := I) g p, expMapC2Radius_pos (I := I) g p, ?_⟩
  intro x v q b hx hxne hv hperp hq hb hcard hRic
  have hsmall t (ht : t ∈ Ioo (0 : ℝ) b) :
      ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    exact (mul_le_mul_of_nonneg_right (ht.2.le.trans hb) (norm_nonneg x)).trans_lt
      (by simpa only [one_mul] using hx)
  have hdom t (ht : t ∈ Ioo (0 : ℝ) b) :=
    mem_expDomain_of_norm_lt_radius (I := I) g p (hsmall t ht)
  have hinj t (ht : t ∈ Ioo (0 : ℝ) b) :
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun y : E => expMap (I := I) g p (show TangentSpace I p from y)) (t • x)) := by
    have hsrc := mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p (hsmall t ht)
    rw [← expDiffeo_mfderiv (I := I) g p hsrc]
    have hlocal := PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(ℝ, E)) (J := I) (n := 1) (expMapDiffeo (I := I) g p) hsrc
    exact (hlocal.mfderivToContinuousLinearEquiv (by norm_num)).injective
  have hRicγ t (_ht : t ∈ Ioo (0 : ℝ) b) :=
    hRic (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
  exact ⟨curveMean_radialJacobiField_le_hyperbolicMeanCurv (I := I)
      g p x hxne v hv hperp hcard q b hq hdom hinj hRicγ,
    antitoneOn_curveDensity_radialJacobiField_div_hyperbolicDensity (I := I)
      g p x hxne v hv hperp hcard q b hq hdom hinj hRicγ⟩


omit [NeZero (Module.finrank ℝ E)] in
omit [T2Space M] [SigmaCompactSpace M] in
theorem normalRatio_anti
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (B : Module.Basis (Option ι) ℝ E)
    (hBu : B none = u)
    (hperp : ∀ i : ι, g.inner p u (B (some i)) = 0)
    (q : ℝ) {b : ℝ}
    (hsrc : MapsTo (fun r : ℝ => r • u) (Ioo (0 : ℝ) b)
      (expMapDiffeo (I := I) g p).source)
    (hrad : ∀ r ∈ Ioo (0 : ℝ) b,
      ‖r • u‖ < expMapC2Radius (I := I) g p)
    (hcurve : AntitoneOn
      (fun r =>
        curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r /
          hyperbolicDensity q (Fintype.card ι) r)
      (Ioo (0 : ℝ) b)) :
    AntitoneOn
      (fun r =>
        r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) /
          hyperbolicDensity q (Fintype.card ι) r)
      (Ioo (0 : ℝ) b) := by
  obtain ⟨c, hc, _hcval, hdensity⟩ :=
    normalDensity_curve (I := I) g p u B hBu hperp hsrc hrad
  intro r hr s hs hrs
  calc
    s ^ Fintype.card ι * normalChartDensity (I := I) g p (s • u) /
          hyperbolicDensity q (Fintype.card ι) s =
        c * (curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) s /
          hyperbolicDensity q (Fintype.card ι) s) := by
      rw [hdensity s hs]
      ring
    _ ≤ c * (curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r /
          hyperbolicDensity q (Fintype.card ι) r) :=
      mul_le_mul_of_nonneg_left (hcurve hr hs hrs) hc.le
    _ = r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) /
          hyperbolicDensity q (Fintype.card ι) r := by
      rw [hdensity r hr]
      ring

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
