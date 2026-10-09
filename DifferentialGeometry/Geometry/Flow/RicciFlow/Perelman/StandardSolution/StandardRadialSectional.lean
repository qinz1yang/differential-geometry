import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricReference
import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingOpenTarget
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Embedding.CompactFrontier
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.Metric.Scaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderSliceConvergence
import DifferentialGeometry.Geometry.Curvature.RadialSphere
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinderSectional
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

set_option autoImplicit false
noncomputable section
open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev C := S2 × ℝ
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_uniform_standard_radial_sphere_tangent_sectional_lower_bound
    {theta : ℝ} (htheta : 0 ≤ theta) (htheta1 : theta < 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 theta →
      ∀ r : ℝ, R ≤ r → ∃ f : S2 → E3,
        IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
        frontier (Metric.closedBall (0 : E3) r) = range f ∧
        ∀ (z : S2) (u v : TangentSpace (𝓡 2) z),
          (1 / 16 : ℝ) *
            ((S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z u) *
              (S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z v) -
              ((S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)) ^ 2) ≤
            metricRm04StandardAt (S.val.metric t) (f z)
              (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)
              (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z u) := by
  classical
  let P (S : StandardSolution) (t r : ℝ) : Prop :=
    ∃ f : S2 → E3, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
      frontier (Metric.closedBall (0 : E3) r) = range f ∧
      ∀ (z : S2) (u v : TangentSpace (𝓡 2) z),
        (1 / 16 : ℝ) *
          ((S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z u) *
            (S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z v) -
            ((S.val.metric t).inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)) ^ 2) ≤
          metricRm04StandardAt (S.val.metric t) (f z)
            (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)
            (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z u)
  change ∃ R : ℝ, 0 < R ∧ ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 theta →
    ∀ r : ℝ, R ≤ r → P S t r
  by_contra hnot
  have hbad (n : ℕ) : ∃ (S : StandardSolution) (t r : ℝ),
      t ∈ Icc 0 theta ∧ (n : ℝ) + 1 ≤ r ∧ ¬ P S t r := by
    by_contra h
    apply hnot
    refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
    intro S t ht r hr
    exact not_not.mp fun hn => h ⟨S, t, r, ht, hr, hn⟩
  choose S time r htime hr hfail using hbad
  have hrpos (n : ℕ) : 0 < r n := (by positivity : (0 : ℝ) < (n : ℝ) + 1).trans_le (hr n)
  let x (n : ℕ) : E3 := r n • (Geometry.Neck.spherePoint : E3)
  have hxnorm (n : ℕ) : ‖x n‖ = r n := by
    simp only [x, norm_smul, Real.norm_eq_abs, abs_of_pos (hrpos n), norm_eq_of_mem_sphere, mul_one]
  have hescape : Tendsto (fun n =>
      (riemannianEDistOf ((S n).val.metric 0) 0 (x n)).toReal) atTop atTop := by
    have hrinf : Tendsto r atTop atTop := tendsto_atTop_mono
      (fun n : ℕ => (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith).trans (hr n))
      tendsto_natCast_atTop_atTop
    apply hrinf.congr'
    filter_upwards with n
    rw [(S n).val.initial, StandardCap.distance_zero, hxnorm]
  obtain ⟨t, ht, sigma, hsigma, htlim⟩ := isCompact_Icc.tendsto_subseq htime
  let tau := (theta + 1) / 2
  have htau : 0 < tau := by dsimp [tau]; linarith
  have htau1 : tau < 1 := by dsimp [tau]; linarith
  have hthetau : theta ≤ tau := by dsimp [tau]; linarith
  obtain ⟨psi, G, F, hpsi, hconv, hpolar, hlocal⟩ :=
    exists_standard_cylinder_metric_subsequence_at_tendsto_time htau htau1
      (S ∘ sigma) (x ∘ sigma) (time ∘ sigma)
      (fun n => ⟨(htime (sigma n)).1, (htime (sigma n)).2.trans hthetau⟩) htlim
      (hescape.comp hsigma.tendsto_atTop)
  let K : Set C := univ ×ˢ ({0} : Set ℝ)
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hcp := (hconv K hK 2).change_reference hK (shrinkingCylinderMetric (E := E3) t)
  obtain ⟨N, hN⟩ := hcp (1 / 1000) (by norm_num)
  have hsec : ∀ᶠ n in atTop, ∀ (z : S2) (u v : TangentSpace (𝓡 2) z),
      (1 / 16 : ℝ) * ((G n).inner (z, 0) (u, 0) (u, 0) *
        (G n).inner (z, 0) (v, 0) (v, 0) - ((G n).inner (z, 0) (u, 0) (v, 0)) ^ 2) ≤
      metricRm04StandardAt (G n) (z, 0) (u, 0) (v, 0) (v, 0) (u, 0) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    intro z u v
    apply metricRm04_shrinkingCylinder_horizontal_lower_bound_of_small_metric_derivatives
      ht.1 (ht.2.trans_lt htheta1) (G n) (z, 0) (le_refl (1 / 1000)) _ u v
    intro j hj
    exact (derivNorm_le_sup hK hj (G n) _ _ (by exact ⟨mem_univ z, rfl⟩)).trans (hN n hn).le
  obtain ⟨n, hnlocal, hnsec⟩ := ((hlocal K hK).and hsec).exists
  obtain ⟨U, hU, hKU, hUF, hmetric⟩ := hnlocal
  have hradial (z : S2) : F n (z, 0) = r (sigma (psi n)) •
      pointedInitialRotation (x (sigma (psi n))) z.val := by
    simpa only [Function.comp_apply, hxnorm, add_zero] using hpolar n (z, 0)
  have hout := isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart
    (F n) (⟨U, hU⟩ : TopologicalSpace.Opens C) hUF
    (fun z => hKU (show (z, (0 : ℝ)) ∈ K from ⟨mem_univ z, rfl⟩))
    (G n) ((S (sigma (psi n))).val.metric (time (sigma (psi n))))
    (fun z v w => hmetric z.val z.property v w) hnsec (hrpos (sigma (psi n)))
    (pointedInitialRotation (x (sigma (psi n)))) hradial
  exact hfail (sigma (psi n)) ⟨(fun z => F n (z, 0)), hout⟩


open TopologicalSpace DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Connection
open scoped ENNReal BigOperators
private local instance (U : Opens E3) : SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)

theorem exists_uniform_standard_radial_sphere_tangent_sectional_lower_bound_of_metric_close
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 θ → ∀ r : ℝ, R ≤ r →
      ∀ (U : Opens E3), frontier (Metric.closedBall (0 : E3) r) ⊆ U →
      ∀ g : SmoothRiemannianMetric (𝓡 3) U,
      (∀ x : U, x.val ∈ frontier (Metric.closedBall (0 : E3) r) → ∀ j ≤ 2,
        metricDerivNorm j g ((S.val.metric t).restrictOpen U)
          (StandardCap.metric.restrictOpen U) x ≤ ε) →
      ∃ f : S2 → U, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
        frontier (Metric.closedBall (0 : E3) r) = range (Subtype.val ∘ f) ∧
        ∀ (z : S2) (u v : TangentSpace (𝓡 2) z),
          (1 / 128 : ℝ) *
            (g.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z u) *
              g.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z v) -
              (g.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)) ^ 2) ≤
            metricRm04StandardAt g (f z)
              (mfderiv (𝓡 2) (𝓡 3) f z u) (mfderiv (𝓡 2) (𝓡 3) f z v)
              (mfderiv (𝓡 2) (𝓡 3) f z v) (mfderiv (𝓡 2) (𝓡 3) f z u) := by
  obtain ⟨R, hR, hradial⟩ :=
    exists_uniform_standard_radial_sphere_tangent_sectional_lower_bound hθ hθ1
  obtain ⟨D, hD, hreference⟩ := exists_uniform_standard_metric_deriv_norm_reference_bound θ hθ hθ1 2
  have hlt : ENNReal.ofReal θ < uniformStandardLifetime := by
    rw [uniformStandardLifetime_eq_one]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr hθ1
  obtain ⟨_, K, hK, hRm⟩ := uniformStandardLifetime_slab θ hθ hlt
  let δ := (64 * (360 + K))⁻¹
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp only [δ]
    have hh : (2 : ℝ) ≤ 64 * (360 + K) := by linarith
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num) hh)
  have hδbudget : δ * (360 + K) + 4 * (1 / 128 : ℝ) ≤ 1 / 16 := by
    have heq : δ * (360 + K) = 1 / 64 := by
      dsimp only [δ]
      field_simp
    rw [heq]
    norm_num
  let ε := δ / (3 * (D + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  refine ⟨R, ε, hR, hε, ?_⟩
  intro S t ht r hr U hball g hclose
  obtain ⟨f₀, hf₀, hfront, hsec⟩ := hradial S t ht r hr
  have hmem (z : S2) : f₀ z ∈ U := hball (hfront.symm ▸ mem_range_self z)
  let f : S2 → U := fun z => ⟨f₀ z, hmem z⟩
  have hf : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f :=
    DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen (𝓡 2) (𝓡 3) U f hf₀
  have hd (z : S2) : mfderiv (𝓡 2) (𝓡 3) f z = mfderiv (𝓡 2) (𝓡 3) f₀ z :=
    (DifferentialGeometry.mfderiv_subtypeVal_comp f z).symm
  refine ⟨f, hf, hfront, ?_⟩
  intro z u v
  let G := (S.val.metric t).restrictOpen U
  have hcp (j : ℕ) (hj : j ≤ 2) : metricDerivNorm j g G G (f z) ≤ δ := by
    have hb := hreference U S t ht g G j hj (f z)
    have hs : (∑ k ∈ Finset.range 3, metricDerivNorm k g G
        (StandardCap.metric.restrictOpen U) (f z)) ≤ 3 * ε := by
      calc
        _ ≤ ∑ _k ∈ Finset.range 3, ε := Finset.sum_le_sum fun k hk =>
          hclose (f z) (hfront.symm ▸ mem_range_self z) k (by have := Finset.mem_range.mp hk; omega)
        _ = _ := by norm_num
    have heq : 3 * (D + 1) * ε = δ := by
      dsimp only [ε]
      exact mul_div_cancel₀ δ (by positivity)
    exact hb.trans ((mul_le_mul_of_nonneg_left hs hD).trans (by nlinarith))
  have hmodel (a b c : TangentSpace (𝓡 3) (f z)) :
      Real.sqrt (G.inner (f z) (riemannOp (LeviCivita G) (f z) a b c)
        (riemannOp (LeviCivita G) (f z) a b c)) ≤
      K * Real.sqrt (G.inner (f z) a a) * Real.sqrt (G.inner (f z) b b) *
        Real.sqrt (G.inner (f z) c c) := by
    have hriem := riemannOp_restrictOpen (S.val.metric t) U (f z) a b c
    simp only [mfderiv_subtype_val_apply] at hriem
    change Real.sqrt ((S.val.metric t).inner (f₀ z) _ _) ≤ _
    rw [hriem]
    simp only [G, SmoothRiemannianMetric.restrictOpen_inner]
    exact (sqrt_inner_riemannOp_le (S.val.metric t) (f₀ z) a b c).trans
      (by gcongr; exact hRm S t ht (f₀ z))
  have hsec' (a b : TangentSpace (𝓡 2) z) :
      (1 / 16 : ℝ) *
        (G.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z a) (mfderiv (𝓡 2) (𝓡 3) f z a) *
          G.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z b) (mfderiv (𝓡 2) (𝓡 3) f z b) -
          (G.inner (f z) (mfderiv (𝓡 2) (𝓡 3) f z a) (mfderiv (𝓡 2) (𝓡 3) f z b)) ^ 2) ≤
        metricRm04StandardAt G (f z) (mfderiv (𝓡 2) (𝓡 3) f z a)
          (mfderiv (𝓡 2) (𝓡 3) f z b) (mfderiv (𝓡 2) (𝓡 3) f z b)
          (mfderiv (𝓡 2) (𝓡 3) f z a) := by
    dsimp only [G]
    rw [metricRm04StandardAt_restrictOpen]
    simp only [mfderiv_subtype_val_apply, hd]
    exact hsec z a b
  exact metricRm04StandardAt_lower_bound_on_range_of_small_metric_derivatives g G (f z)
    (mfderiv (𝓡 2) (𝓡 3) f z).toLinearMap
    (Perelman.KappaSolutions.immersionAt_mfderiv_injective (hf.isImmersion.isImmersionAt z))
    hδhalf (by norm_num) hcp hmodel hsec' hδbudget u v


theorem exists_uniform_standard_radial_image_frontier_tangent_sectional_lower_bound_of_metric_close
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ R ε : ℝ, 0 < R ∧ 0 < ε ∧
      ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 θ → ∀ r : ℝ, R ≤ r →
      ∀ (U : Opens E3), Metric.closedBall (0 : E3) r ⊆ U →
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
        (g : SmoothRiemannianMetric (𝓡 3) M) (Ψ : U → M)
        (hΨ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Ψ), Function.Injective Ψ →
      ∀ (q : ℝ) (hq : 0 < q),
      (∀ x : U, x.val ∈ frontier (Metric.closedBall (0 : E3) r) → ∀ j ≤ 2,
        metricDerivNorm j (localPullMetric (scaleMetric q hq g) Ψ hΨ)
          ((S.val.metric t).restrictOpen U) (StandardCap.metric.restrictOpen U) x ≤ ε) →
      ∃ f : S2 → U, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f ∧
        frontier (Metric.closedBall (0 : E3) r) = range (Subtype.val ∘ f) ∧
        IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (Ψ ∘ f) ∧
        frontier (Ψ '' {x : U | x.val ∈ Metric.closedBall (0 : E3) r}) = range (Ψ ∘ f) ∧
        ∀ (z : S2) (u v : TangentSpace (𝓡 2) z),
          (q / 128) *
            (g.inner ((Ψ ∘ f) z) (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z u)
                (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z u) *
              g.inner ((Ψ ∘ f) z) (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z v)
                (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z v) -
              (g.inner ((Ψ ∘ f) z) (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z u)
                (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z v)) ^ 2) ≤
            metricRm04StandardAt g ((Ψ ∘ f) z)
              (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z u) (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z v)
              (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z v) (mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z u) := by
  obtain ⟨R, ε, hR, hε, hboundary⟩ :=
    exists_uniform_standard_radial_sphere_tangent_sectional_lower_bound_of_metric_close θ hθ hθ1
  refine ⟨R, ε, hR, hε, ?_⟩
  intro S t ht r hr U hball M _ _ _ _ g Ψ hΨ hinj q hq hclose
  obtain ⟨f, hf, hfront, hsec⟩ := hboundary S t ht r hr U
    (fun _ hy => hball (Metric.isClosed_closedBall.frontier_subset hy))
    (localPullMetric (scaleMetric q hq g) Ψ hΨ) hclose
  have hΨopen := hΨ.isLocalHomeomorph.isOpenEmbedding_of_injective hinj
  have hΨsmooth := Perelman.KappaSolutions.localDiffeomorph_isSmoothEmbedding_of_injective hΨ hinj
  refine ⟨f, hf, hfront, hΨsmooth.comp hf (by simp), ?_, ?_⟩
  · have hcompact : IsCompact {x : U | x.val ∈ Metric.closedBall (0 : E3) r} :=
      _root_.Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall (0 : E3) r)
        (fun x hx => ⟨⟨x, hball hx⟩, rfl⟩)
    rw [← DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
      hΨopen hcompact]
    have hprefront : frontier {x : U | x.val ∈ Metric.closedBall (0 : E3) r} = range f := by
      have hp := U.isOpenEmbedding'.isOpenMap.preimage_frontier_eq_frontier_preimage
        continuous_subtype_val (Metric.closedBall (0 : E3) r)
      change frontier ((Subtype.val : U → E3) ⁻¹' Metric.closedBall (0 : E3) r) = range f
      rw [← hp, hfront]
      ext x
      simp only [mem_preimage, mem_range, Function.comp_apply]
      exact ⟨fun ⟨z, hz⟩ => ⟨z, Subtype.ext hz⟩, fun ⟨z, hz⟩ => ⟨z, congrArg Subtype.val hz⟩⟩
    rw [hprefront, ← range_comp]
  · intro z u v
    have hder (a : TangentSpace (𝓡 2) z) :
        mfderiv (𝓡 2) (𝓡 3) (Ψ ∘ f) z a =
          mfderiv (𝓡 3) (𝓡 3) Ψ (f z) (mfderiv (𝓡 2) (𝓡 3) f z a) := by
      rw [mfderiv_comp z (hΨ.contMDiff.mdifferentiableAt (by simp))
        (hf.contMDiff.mdifferentiableAt (by simp))]
      rfl
    have hh := hsec z u v
    rw [metricRm04StandardAt_localPullMetric, metricRmStandard_scale] at hh
    simp only [localPullMetric_inner, scaleMetric_inner] at hh
    simp only [hder, Function.comp_apply]
    apply (mul_le_mul_iff_left₀ hq).mp
    convert hh using 1 <;> ring


end DifferentialGeometry.PDE.RicciFlow
