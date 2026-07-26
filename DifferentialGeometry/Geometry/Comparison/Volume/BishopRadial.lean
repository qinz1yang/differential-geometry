import DifferentialGeometry.Geometry.Comparison.Volume.BishopJacobi
import DifferentialGeometry.Geometry.Comparison.Volume.RadialGram

/-!
# Radial input for Bishop comparison

This file transfers endpoint lower bounds for scaled radial Jacobi fields to
the positive pole-density ratio required by the Jacobi Bishop comparison.
-/

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
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma familyCoeffMap_apply
    {ι : Type*} [Fintype ι] (v : ι → E)
    (c : EuclideanSpace ℝ ι) :
    familyCoeffMap (E := E) v c =
      toEuclidean (E := E) (∑ i, c i • v i) := by
  change toEuclidean (E := E) (∑ i, c i • v i) =
    toEuclidean (E := E) (∑ i, c i • v i)
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
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
    simpa only [familyCoeffMap_apply] using hcd
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
private lemma chartCoeff_sum
    (w : E) :
    (∑ i, (toEuclidean (E := E) w) i • (chartModelBasis E) i) = w := by
  let b :=
    (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis
  have hsum :
      toEuclidean (E := E) w =
        ∑ i, (toEuclidean (E := E) w) i •
          EuclideanSpace.single i (1 : ℝ) := by
    simpa [b, EuclideanSpace.basisFun_apply] using
      (b.sum_repr (toEuclidean (E := E) w)).symm
  calc
    (∑ i, (toEuclidean (E := E) w) i • (chartModelBasis E) i) =
        (toEuclidean (E := E)).symm
          (∑ i, (toEuclidean (E := E) w) i •
            EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
      simp only [map_smul, chartModelBasis_apply]
    _ = (toEuclidean (E := E)).symm (toEuclidean (E := E) w) :=
      congrArg (toEuclidean (E := E)).symm hsum.symm
    _ = w := (toEuclidean (E := E)).symm_apply_apply w

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
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

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
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

/-- Endpoint radial Jacobi fields in every unit chart direction retain a
uniform positive length for launch points tending to the pole. -/
theorem exists_radial_base
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) :
    ∃ B : ℝ, 0 < B ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        ∀ d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)), ‖d‖ = 1 →
          B ^ 2 ≤
            g.inner (radialCurve (I := I) g p x t)
              (radialJacobiField (I := I) g p (t • x)
                (∑ j, d j • (chartModelBasis E) j) 1)
              (radialJacobiField (I := I) g p (t • x)
                (∑ j, d j • (chartModelBasis E) j) 1) := by
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
    simpa using hc0.mono_left inf_le_left
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
  have hzeroSrc : (0 : E) ∈ (expMapDiffeo (I := I) g p).source :=
    zero_mem_expMapDiffeo_source (I := I) g p
  have hbaseQuad
      (d : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
      dotProduct (⇑d) (Matrix.mulVec A₀ (⇑d)) =
        g.inner p (∑ j, d j • (chartModelBasis E) j)
          (∑ j, d j • (chartModelBasis E) j) := by
    dsimp only [A₀]
    rw [normalGram_radialMat (I := I) g p hzeroSrc hzeroRad]
    rw [radialJacobiGram_quadratic (I := I) g p]
    have hpoint :
        (expMap (I := I) g p
          (show TangentSpace I p from (0 : E)) : M) = p :=
      expMap_zero (I := I) g p
    rw [hpoint]
    have hJzero (j : Fin (Module.finrank ℝ E)) :
        radialJacobiField (I := I) g p 0 ((chartModelBasis E) j) 1 =
          (chartModelBasis E) j := by
      rw [radialJacobi_one (I := I) g p 0 _ hzeroRad]
      simpa using congrArg
        (fun L : E →L[ℝ] TangentSpace I p => L ((chartModelBasis E) j))
        (mfderiv_expMap_at_zero (I := I) g p)
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
      g.inner p (∑ j, d j • (chartModelBasis E) j)
        (∑ j, d j • (chartModelBasis E) j) := by
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
          (∑ j, d j • (chartModelBasis E) j) 1)
        (radialJacobiField (I := I) g p (t • x)
          (∑ j, d j • (chartModelBasis E) j) 1) := by
    dsimp only [A]
    rw [normalGram_radialMat (I := I) g p hsrcT hradT]
    rw [radialJacobiGram_quadratic (I := I) g p]
    change g.inner (radialCurve (I := I) g p x t)
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((chartModelBasis E) i) 1)
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((chartModelBasis E) i) 1) = _
    have hsum :
        (∑ i, d i • radialJacobiField (I := I) g p (t • x)
          ((chartModelBasis E) i) 1) =
          radialJacobiField (I := I) g p (t • x)
            (∑ j, d j • (chartModelBasis E) j) 1 :=
      (radialJacobi_one_sum (I := I) g p (t • x) (⇑d) hradT).symm
    exact congrArg
      (fun z => g.inner (radialCurve (I := I) g p x t) z z) hsum
  rwa [hAt] at hquadLower

/-- A radial Jacobi field launched orthogonally to the radial direction remains
orthogonal to the radial velocity while the exponential map is in its `C²`
range. -/
lemma radialJacobi_perp
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (htx : ‖t • x‖ < expMapC2Radius (I := I) g p)
    (hxw : g.inner p x w = 0) :
    g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (radialJacobiField (I := I) g p x w t) = 0 := by
  let L := mfderiv 𝓘(ℝ, E) I
    (fun z : E => (expMap (I := I) g p
      (show TangentSpace I p from z) : M)) (t • x)
  have hvel : curveVelocity (I := I) (radialCurve (I := I) g p x) t = L x := by
    simpa only [curveVelocity, radialCurve, L] using
      mfderiv_exp_radial (I := I) g p x t htx
  have hJ : radialJacobiField (I := I) g p x w t = L (t • w) := by
    simpa only [L] using radialJacobi_at (I := I) g p x w t htx
  have horth : g.inner p (t • x) w = 0 := by
    have hmap := congrArg (fun A : E →L[ℝ] ℝ => A w) ((g.inner p).map_smul t x)
    calc
      g.inner p (t • x) w = (t • g.inner p x) w := hmap
      _ = t * g.inner p x w := rfl
      _ = 0 := by rw [hxw, mul_zero]
  have hgauss := (gauss_lemma_pullback (I := I) g p
    (mem_expDomain_of_norm_lt_radius (I := I) g p htx) htx).2 horth
  rw [hvel, hJ]
  calc
    g.inner (radialCurve (I := I) g p x t) (L x) (L (t • w)) =
        g.inner (radialCurve (I := I) g p x t) (L (t • x)) (L w) := by
      have hLw : L (t • w) = t • L w := L.map_smul t w
      have hLx : L (t • x) = t • L x := L.map_smul t x
      rw [hLw, hLx]
      have hleft := (g.inner (radialCurve (I := I) g p x t) (L x)).map_smul t (L w)
      have hright := congrArg (fun A : _ →L[ℝ] ℝ => A (L w))
        ((g.inner (radialCurve (I := I) g p x t)).map_smul t (L x))
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hleft.trans hright.symm
    _ = 0 := by simpa only [radialCurve, L] using hgauss

/-- The first covariant derivative of a transverse radial Jacobi field is also
orthogonal to the radial velocity. -/
lemma radialJacobi_dperp
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (hx : ‖x‖ < expMapC2Radius (I := I) g p)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hxw : g.inner p x w = 0)
    (hJdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t) t) :
    g.inner (radialCurve (I := I) g p x t)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
      (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x w) t) = 0 := by
  let γ := radialCurve (I := I) g p x
  let J := radialJacobiField (I := I) g p x w
  have htx : ‖t • x‖ < expMapC2Radius (I := I) g p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    calc
      t * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht.2.le (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hx
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t := by
    simpa only [γ, radialCurve] using
      radialCurve_contMDiffAt2 (I := I) g p x t htx
  have hgeo : HasGeodesicEquationAt (I := I) g γ t := by
    simpa only [γ, radialCurve] using radial_geo_at (I := I) g p x hx t ht
  have hvelDiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ (curveVelocity (I := I) γ) t) t := by
    simpa only [curveVelocity, chartRepAt] using
      MFDerivAlongCurve.velocity_coord_diff (I := I) γ t hγ
  have hinner := inner_deriv_at (I := I) (n := (2 : WithTop ℕ∞))
    (by norm_num) g γ (curveVelocity (I := I) γ) J t hγ hvelDiff (by
      simpa only [γ, J] using hJdiff)
  have hsmul : Continuous (fun s : ℝ => s • x) :=
    continuous_id.smul continuous_const
  have hmem : t • x ∈ Metric.ball (0 : E) (expMapC2Radius (I := I) g p) := by
    simpa only [Metric.mem_ball, dist_zero_right] using htx
  have hsmall : ∀ᶠ s in 𝓝 t, ‖s • x‖ < expMapC2Radius (I := I) g p := by
    have hev := hsmul.continuousAt.eventually (Metric.isOpen_ball.mem_nhds hmem)
    simpa only [Metric.mem_ball, dist_zero_right] using hev
  have hzeroEv :
      (fun s : ℝ => g.inner (γ s) (curveVelocity (I := I) γ s) (J s)) =ᶠ[𝓝 t]
        (fun _ : ℝ => 0) := by
    filter_upwards [hsmall] with s hs
    simpa only [γ, J] using radialJacobi_perp (I := I) g p x w hs hxw
  have hzero : HasDerivAt
      (fun s : ℝ => g.inner (γ s) (curveVelocity (I := I) γ s) (J s)) 0 t :=
    (hasDerivAt_const (x := t) (c := (0 : ℝ))).congr_of_eventuallyEq hzeroEv
  have hvelZero : covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 := by
    simpa only [curveVelocity] using
      covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
        (I := I) g γ t hγ hgeo
  have huniq := hinner.unique hzero
  simp only [hvelZero, map_zero, ContinuousLinearMap.zero_apply, zero_add] at huniq
  simpa only [γ, J] using huniq

/-- A uniform endpoint lower bound for the scaled radial family gives the
positive density-ratio input at the pole. -/
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
          hypDensity q (Fintype.card ι) t := by
  have htx : Tendsto (fun t : ℝ => t • x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hc0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    simpa using hc0.mono_left inf_le_left
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
      calc
        (∑ i, c i • radialJacobiField (I := I) g p x (v i) t) =
            radialJacobiField (I := I) g p x (∑ i, c i • v i) t :=
          (radialJacobi_sum_at (I := I) g p x v (⇑c) t htrad).symm
        _ = radialJacobiField (I := I) g p (t • x)
            (t • ∑ i, c i • v i) 1 :=
          radialJacobi_scale (I := I) g p x (∑ i, c i • v i) t
        _ = t • J := by
          dsimp only [J]
          rw [radialJacobi_one_smul (I := I) g p (t • x)
            (∑ i, c i • v i) t htrad]
    have hscale_aux (z : TangentSpace I (radialCurve (I := I) g p x t)) :
        g.inner (radialCurve (I := I) g p x t) (t • z) (t • z) =
          t ^ 2 * g.inner (radialCurve (I := I) g p x t) z z := by
      rw [map_smul (g.inner _), ContinuousLinearMap.smul_apply,
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

/-- A unit-direction endpoint lower bound for the full chart model basis gives
the positive pole-density ratio for any linearly independent finite family.

The loss is exactly the positive lower bound of the finite-dimensional
coefficient map from the supplied family to the chart model basis. -/
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
              (∑ j, d j • (chartModelBasis E) j) 1)
            (radialJacobiField (I := I) g p (t • x)
              (∑ j, d j • (chartModelBasis E) j) 1)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g (radialCurve (I := I) g p x)
            (fun i => radialJacobiField (I := I) g p x (v i)) t /
          hypDensity q (Fintype.card ι) t := by
  rcases exists_coeff_ge (E := E) v hv with ⟨δ, hδ, hcoeff⟩
  have htx : Tendsto (fun t : ℝ => t • x) (𝓝[>] (0 : ℝ)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun t : ℝ => t • x) :=
      continuous_id.smul continuous_const
    have hc0 : Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto
    simpa using hc0.mono_left inf_le_left
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
    let z : E := ∑ j, u j • (chartModelBasis E) j
    have hd : d = toEuclidean (E := E) w := by
      simpa only [d, w] using familyCoeffMap_apply (E := E) v c
    have hdsum : (∑ j, d j • (chartModelBasis E) j) = w := by
      rw [hd]
      exact chartCoeff_sum (E := E) w
    have hdu : d = ‖d‖ • u := by
      dsimp only [u]
      rw [smul_smul]
      simp only [mul_inv_cancel₀ hdpos.ne', one_smul]
    have hsumdu :
        (∑ j, d j • (chartModelBasis E) j) = ‖d‖ • z := by
      calc
        (∑ j, d j • (chartModelBasis E) j) =
            ∑ j, (‖d‖ • u) j • (chartModelBasis E) j :=
          congrArg (fun a : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) =>
            ∑ j, a j • (chartModelBasis E) j) hdu
        _ = ‖d‖ • z := by
          dsimp only [z]
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          change (‖d‖ * u j) • (chartModelBasis E) j =
            ‖d‖ • (u j • (chartModelBasis E) j)
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
        rw [map_smul (g.inner _), ContinuousLinearMap.smul_apply,
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

/-- The radial density ratio has a positive pole lower bound for every linearly
independent finite family, with no extra endpoint assumption. -/
theorem radialRatio_auto
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (v : ι → E)
    (q : ℝ) (hq : 0 ≤ q) (hv : LinearIndependent ℝ v) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g (radialCurve (I := I) g p x)
            (fun i => radialJacobiField (I := I) g p x (v i)) t /
          hypDensity q (Fintype.card ι) t := by
  obtain ⟨B, hB, hbase⟩ := exists_radial_base (I := I) g p x
  exact radialRatio_basis (I := I) g p x v q B hq hB hv hbase

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- On one common normal-coordinate radius, every nonzero radial direction and
small linearly independent transverse family satisfies the Bishop mean-curvature
comparison and radial density-ratio monotonicity under the Ricci lower bound. -/
theorem exists_radial_cmp
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : E) (v : ι → E) (q b : ℝ),
      ‖x‖ < r →
      (∀ i, ‖v i‖ < r) →
      x ≠ 0 →
      LinearIndependent ℝ v →
      (∀ i, g.inner p x (v i) = 0) →
      0 ≤ q → 0 < b → b < 1 →
      Fintype.card ι = Module.finrank ℝ E - 1 →
      0 < Module.finrank ℝ E - 1 →
      RicciBoundedBelow (I := I) g
        (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
      (∀ t ∈ Ioo (0 : ℝ) b,
          curveMean (I := I) g (radialCurve (I := I) g p x)
              (fun i => radialJacobiField (I := I) g p x (v i)) t ≤
            hypMeanCurv (q * Real.sqrt (g.inner p x x))
              (Module.finrank ℝ E - 1) t) ∧
        AntitoneOn
          (fun t =>
            curveDensity (I := I) g (radialCurve (I := I) g p x)
                (fun i => radialJacobiField (I := I) g p x (v i)) t /
              hypDensity (q * Real.sqrt (g.inner p x x))
                (Module.finrank ℝ E - 1) t)
          (Ioo (0 : ℝ) b) := by
  obtain ⟨rd, hrd, hdiff⟩ := exists_radialJacobi_diff (I := I) g p
  obtain ⟨rj, hrj, hJac⟩ := exists_jacobi_Ioo (I := I) g p
  obtain ⟨rw, hrw, hW⟩ := radial_wronsk_zero (I := I) g hEnorm p
  let re : ℝ := expMapC2Radius (I := I) g p
  let r : ℝ := min rw (min rd (min rj re))
  have hre : 0 < re := expMapC2Radius_pos (I := I) g p
  have hr : 0 < r := by
    dsimp only [r, re]
    exact lt_min hrw (lt_min hrd (lt_min hrj hre))
  refine ⟨r, hr, ?_⟩
  intro x v q b hx hvsmall hxne hv hperp hq hb hb1 hcard hd hRic
  have hr_rw : r ≤ rw := min_le_left _ _
  have hr_rd : r ≤ rd := (min_le_right _ _).trans (min_le_left _ _)
  have hr_rj : r ≤ rj :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr_re : r ≤ re :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hxw : ‖x‖ < rw := hx.trans_le hr_rw
  have hxd : ‖x‖ < rd := hx.trans_le hr_rd
  have hxj : ‖x‖ < rj := hx.trans_le hr_rj
  have hxe : ‖x‖ < expMapC2Radius (I := I) g p := by
    simpa only [re] using hx.trans_le hr_re
  have hvw : ∀ i, ‖v i‖ < rw := fun i => (hvsmall i).trans_le hr_rw
  have hvd : ∀ i, ‖v i‖ < rd := fun i => (hvsmall i).trans_le hr_rd
  have hvj : ∀ i, ‖v i‖ < rj := fun i => (hvsmall i).trans_le hr_rj
  have htx : ∀ t ∈ Ioo (0 : ℝ) b,
      ‖t • x‖ < expMapC2Radius (I := I) g p := by
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
    calc
      t * ‖x‖ ≤ 1 * ‖x‖ :=
        mul_le_mul_of_nonneg_right (ht.2.trans hb1).le (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < expMapC2Radius (I := I) g p := hxe
  let a : ℝ := Real.sqrt (g.inner p x x)
  have hinner : 0 < g.inner p x x := g.pos p x hxne
  have ha : 0 < a := by
    simpa only [a] using Real.sqrt_pos.2 hinner
  have hγ : ∀ t ∈ Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞)
        (radialCurve (I := I) g p x) t := by
    intro t ht
    simpa only [radialCurve] using
      radialCurve_contMDiffAt2 (I := I) g p x t (htx t ht)
  have hspeed : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t) = a ^ 2 := by
    intro t ht
    rw [radial_speed_sq_eq (I := I) g p x hxe
      ⟨ht.1, ht.2.trans hb1⟩]
    exact (Real.sq_sqrt hinner.le).symm
  have hVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (radialJacobiField (I := I) g p x (v i) t) = 0 := by
    intro t ht i
    exact radialJacobi_perp (I := I) g p x (v i) (htx t ht) (hperp i)
  have hVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (v i)) t) t := by
    intro t ht i
    exact (hdiff x (v i) hxd (hvd i) hb1.le).1 t ⟨ht.1.le, ht.2.le⟩
  have hDVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) (radialCurve (I := I) g p x)
          (fun s => covDerivAlong (I := I) g
            (radialCurve (I := I) g p x)
            (radialJacobiField (I := I) g p x (v i)) s) t) t := by
    intro t ht i
    exact (hdiff x (v i) hxd (hvd i) hb1.le).2 t ⟨ht.1.le, ht.2.le⟩
  have hDVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (covDerivAlong (I := I) g (radialCurve (I := I) g p x)
          (radialJacobiField (I := I) g p x (v i)) t) = 0 := by
    intro t ht i
    exact radialJacobi_dperp (I := I) g p x (v i) hxe
      ⟨ht.1, ht.2.trans hb1⟩ (hperp i) (hVdiff t ht i)
  have hLI : ∀ t ∈ Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i =>
        radialJacobiField (I := I) g p x (v i) t := by
    intro t ht
    exact radialJacobi_li (I := I) g p x hv ht.1.ne'
      (mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p (htx t ht))
      (htx t ht)
  have hWronsk : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (v i))
        (radialJacobiField (I := I) g p x (v j)) t = 0 := by
    intro t ht i j
    exact hW x (v i) (v j) hxw (hvw i) (hvw j) hb hb1 t
      ⟨ht.1.le, ht.2.le⟩
  have hJacobi : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g (radialCurve (I := I) g p x)
        (radialJacobiField (I := I) g p x (v i)) t := by
    intro t ht i
    exact hJac x (v i) hxj (hvj i) hb1.le t ht
  have hRatio : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g (radialCurve (I := I) g p x)
              (fun i => radialJacobiField (I := I) g p x (v i)) t /
            hypDensity (q * a) (Module.finrank ℝ E - 1) t := by
    obtain ⟨C, hC, hratio⟩ :=
      radialRatio_auto (I := I) g p x v (q * a) (mul_nonneg hq ha.le) hv
    refine ⟨C, hC, ?_⟩
    simpa only [hcard] using hratio
  have hmean := curveMean_le_hyp (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g (radialCurve (I := I) g p x)
    (fun i => radialJacobiField (I := I) g p x (v i)) q a b
    hq ha hcard hd hγ hspeed hVperp hDVperp hVdiff hDVdiff hLI
    hWronsk hJacobi hRic hRatio
  refine ⟨?_, ?_⟩
  · simpa only [a] using hmean
  · simpa only [a] using
      curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
        g (radialCurve (I := I) g p x)
        (fun i => radialJacobiField (I := I) g p x (v i))
        (q * a) b (Module.finrank ℝ E - 1) (mul_nonneg hq ha.le)
        hγ hVdiff hLI hWronsk hmean

/-- Antitonicity of a transverse radial-Jacobi density ratio transfers to the
corresponding normal-coordinate density ratio. -/
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
          hypDensity q (Fintype.card ι) r)
      (Ioo (0 : ℝ) b)) :
    AntitoneOn
      (fun r =>
        r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) /
          hypDensity q (Fintype.card ι) r)
      (Ioo (0 : ℝ) b) := by
  obtain ⟨c, hc, hdensity⟩ :=
    normalDensity_curve (I := I) g p u B hBu hperp hsrc hrad
  intro r hr s hs hrs
  calc
    s ^ Fintype.card ι * normalChartDensity (I := I) g p (s • u) /
          hypDensity q (Fintype.card ι) s =
        c * (curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) s /
          hypDensity q (Fintype.card ι) s) := by
      rw [hdensity s hs]
      ring
    _ ≤ c * (curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i : ι => radialJacobiField (I := I) g p u (B (some i))) r /
          hypDensity q (Fintype.card ι) r) :=
      mul_le_mul_of_nonneg_left (hcurve hr hs hrs) hc.le
    _ = r ^ Fintype.card ι * normalChartDensity (I := I) g p (r • u) /
          hypDensity q (Fintype.card ι) r := by
      rw [hdensity r hr]
      ring

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Mean-curvature projection of `exists_radial_cmp`. -/
theorem exists_radial_mean
    [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) :
    ∃ r : ℝ, 0 < r ∧ ∀ (x : E) (v : ι → E) (q b : ℝ),
      ‖x‖ < r →
      (∀ i, ‖v i‖ < r) →
      x ≠ 0 →
      LinearIndependent ℝ v →
      (∀ i, g.inner p x (v i) = 0) →
      0 ≤ q → 0 < b → b < 1 →
      Fintype.card ι = Module.finrank ℝ E - 1 →
      0 < Module.finrank ℝ E - 1 →
      RicciBoundedBelow (I := I) g
        (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)) →
      ∀ t ∈ Ioo (0 : ℝ) b,
        curveMean (I := I) g (radialCurve (I := I) g p x)
            (fun i => radialJacobiField (I := I) g p x (v i)) t ≤
          hypMeanCurv (q * Real.sqrt (g.inner p x x))
            (Module.finrank ℝ E - 1) t := by
  obtain ⟨r, hr, hcmp⟩ := exists_radial_cmp (I := I) (ι := ι) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro x v q b hx hvsmall hxne hv hperp hq hb hb1 hcard hd hRic
  exact (hcmp x v q b hx hvsmall hxne hv hperp hq hb hb1 hcard hd hRic).1

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
