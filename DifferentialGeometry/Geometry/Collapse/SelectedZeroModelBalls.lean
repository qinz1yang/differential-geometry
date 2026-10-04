import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScaleModel
import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelInputs
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.BufferedRadialFunctionAtScale

/-!
# LC80 item 2 at a fixed index: the LC58 data at every point, in LCP04's shape (GAP D)

Master207A, LC80 (A:24719), item 2: "the SAME radius, nonnegative model, cone and radial function at
each index, with the prescribed core/interior identification". Lane LC5X's GAP C
(`exists_uniform_scale_interval_joint_witnesses`) already has no sequence in its conclusion: for
`α > α₀` and EVERY `p ∈ M^α` one `s ∈ [T, V]` and one model `b` carry, at the scale `s ρ_α(p)`, a
Kleiner–Lott map to `(C_b, o_b)` and the open-ball identification `B(p, ρ' s ρ_α(p)) ≃ N_b`.

`exists_uniform_scale_zero_model_data` adds, at the SAME `p`, `s`, `b`, LCP04's remaining
selected-center inputs, with LCP04's thresholds fixed FIRST (quantifier order of LC80 and LC73):
* the original buffer `sec_g ≥ -(1/60)² (s ρ)⁻²` on `B(p, 400 s ρ)` (obligation (iii),
  `eventually_original_buffer_of_sequential_curvature`, from the curvature component of LC58's
  hypothesis);
* the cone error `δ < δ'` (obligation (iv));
* the radial function: LC67's choice at the scale `s ρ_α(p)` built from the SAME Kleiner–Lott map,
  with every LC30 clause, the buffered window `{3/40 ≤ d ≤ 11}` that LCP04 needs, and LC31's cutoff
  (obligation (i), `exists_buffered_radial_cutoff_at_scale`).
The model clauses (obligation (ii)) depend on `b` only (`model_lcp04_clauses_of_sectional_nonneg`).
The composition with LCP04's selection is the consumer
`exists_selected_zero_packets_with_model_balls`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC80 item 2 at a fixed index (GAP D).** Under LC58's sequential hypothesis (as in
`exists_uniform_scale_interval_joint_witnesses`), for thresholds `0 < ε < 1`, `δ' > 0` fixed
first, every `0 < e < 1/40` and `T`: there are `V ≥ T`, one cone error `0 < δ < δ'` and `α₀` such
that for `α > α₀` every `p ∈ M^α` has `s ∈ [T, V]` and a model `b` with, at the scale `s ρ_α(p)`:
the original buffer on `B(p, 400 s ρ_α(p))`; a Kleiner–Lott `δ`-map to `(C_b, o_b)`; an LC67
radial function (all LC30 clauses, smooth near `{3/40 ≤ d ≤ 11}`) with LC31's cutoff; and for every
`ρ' ∈ [1/5, 2]` a diffeomorphism of `B(p, ρ' s ρ_α(p))` onto `N_b`. -/
theorem exists_uniform_scale_zero_model_data {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1)
    {M : ℕ → Type} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, SigmaCompactSpace (M α)] [∀ α, ConnectedSpace (M α)]
    [hMc : ∀ α, CompleteSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type} {N C : ι → Type} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)]
    [∀ b, IsManifold I ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, ConnectedSpace (N b)]
    [∀ b, RiemannianBundle (fun x : N b => TangentSpace I x)] [∀ b, IsRiemannianManifold I (N b)]
    [∀ b, CompleteSpace (N b)]
    [∀ b, IsContinuousRiemannianBundle E (fun x : N b => TangentSpace I x)]
    [∀ b, T2Space (TangentBundle I (N b))] [mC : ∀ b, MetricSpace (C b)]
    (gN : ∀ b, SmoothRiemannianMetric I (N b)) (hgN : ∀ b, IsMetricNorm (I := I) (gN b))
    (hsecN : ∀ b x, SectionalBoundedBelowAt (gN b) x 0)
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        (∃ jm : ∀ j, PartialDiffeomorph I I (N b) (M (a (k j))) ∞, (∀ j, jm j (n b) = z (k j)) ∧
          ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ l,
            ((⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)) :
              Set (N b)) ⊆ (jm (l + i₀)).source,
            ∀ K : Set (⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)),
              IsCompact K → MetricCPConvergenceOn K 1
                (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i₀)) _ (hsub l)
                  (scaleMetric ((ρ (a (k (l + i₀))) (z (k (l + i₀))))⁻¹ ^ 2)
                    (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k (l + i₀))))))
                ((gN b).restrictOpen _) ((gN b).restrictOpen _)) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {ε δ' e T : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hδ' : 0 < δ') (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ s ∈ Icc T V, ∃ hs : 0 < s, ∃ b : ι,
        (∀ y ∈ Metric.ball p (400 * (s * ρ α p)),
          SectionalBoundedBelowAt (g α) y (-((1 / 60) ^ 2 * (s * ρ α p)⁻¹ ^ 2))) ∧
        Nonempty (@KleinerLottApprox (M α) (C b)
          ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b)
          p (o b) δ) ∧
        (letI := (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
        let gR := scaleMetric ((s * ρ α p)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)
        ∃ F : M α → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          (∃ O : Set (M α), IsOpen O ∧ {x : M α | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) ∧
          (∀ x, |F x - Metric.infDist x {p}| < e) ∧
          (∀ x, x ∉ {x : M α | 1 / 20 < dist x p ∧ dist x p < 20} →
            F x = Metric.infDist x {p}) ∧
          (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
            ε * dist x y) ∧
          (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
          (∀ q ∈ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
            1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ∧
              Real.sqrt (gR.inner q (gradFun gR F q) (gradFun gR F q)) ≤ 1 + ε) ∧
          (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
          F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
          (∃ O' : Set (M α), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q ∈ O', gradFun gR F q ≠ 0) ∧
          ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
            ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
            (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
            (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
            tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
              {x : M α | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
            ∀ q, Real.sqrt (gR.inner q (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)
              (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε)) ∧
        ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I I (M α) (N b) ∞,
          Ψ.source = Metric.ball p (ρ' * (s * ρ α p)) ∧ Ψ.target = univ := by
  obtain ⟨δ, hδ0, hδ1, hδδ', hδr⟩ := exists_coneError_below_thresholds hε hδ'
  obtain ⟨V, hTV, α₀, hGC⟩ := exists_uniform_scale_interval_joint_witnesses hdim g hmetric ρ hρ
    gN hgN hsecN n o Hc hcone hmodel (T := T) hδ0 hδ1 hε hε1 he he1
  obtain ⟨α₁, hbuf⟩ := eventually_original_buffer_of_sequential_curvature g ρ hρ
    (fun a ha z => by
      obtain ⟨-, k, hk, -, -, Hb, hHb, hsec⟩ := hmodel a ha z
      exact ⟨k, hk, Hb, hHb, hsec⟩) V
  refine ⟨V, hTV, δ, hδ0, hδδ', max α₀ α₁, fun α hα p => ?_⟩
  obtain ⟨s, hsI, hs, b, ⟨φ⟩, -, h3⟩ := hGC α ((le_max_left _ _).trans_lt hα) p
  have hsec := hbuf α ((le_max_right _ _).trans_lt hα) p s hs hsI.2
  exact ⟨s, hsI, hs, b, hsec, ⟨φ⟩,
    exists_buffered_radial_cutoff_at_scale (g α) (hmetric α) (mul_pos hs (hρ α p)) φ (Hc b) hsec
      hε hε1 hδr he he1, h3⟩

end DifferentialGeometry.Geometry.Collapse
