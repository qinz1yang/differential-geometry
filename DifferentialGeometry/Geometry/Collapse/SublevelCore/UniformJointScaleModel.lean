import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallModelTypeJoint
import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScaleConeRadial

/-!
# LC58 binding with all three LC57 conclusions (GAP C)

Master207A, A:23194 (LC58). LC58's hypothesis "every normalized pointed sequence
`(M^{α_i}, ρ_{α_i}(p_i)^{-2} g^{α_i}, p_i)` has a subsequence carrying ONE LC56 package" enters
UNBUNDLED: the models `(N_b, g_b, n_b)` (complete, connected, `sec ≥ 0`, compact or not) carry
their LC21 cone packages, and along every sequence some subsequence has a model `b` with
(1) pointed convergence of the normalized sources, (2) A1 maps `N_b ⇀ M^{α}` sending `n_b` to the
chosen points with per-radius `C¹` convergence of the pullbacks of the normalized tensors, and
(4) the normalized curvature bounds.

Conclusion (LC58 for the three LC57 conclusions with ONE model, ONE scale): there are `V ≥ T` and
`α₀` such that for every `α > α₀` and every `p ∈ M^α` some `s ∈ [T, V]` and one model `b` give,
at the scale `s ρ_α(p)`: (1) a Kleiner–Lott `δ`-map to `(C_b, o_b)`; (2) an LC30 function with all
its clauses and LC31's cutoff; (3) for every `ρ' ∈ [1/5, 2]` a diffeomorphism of the open ball
`B(p, ρ' s ρ_α(p))` onto the model `N_b` (LC61's smooth model type, which for a noncompact model
encodes the LC37 packet through LC51/LC55/LC60, and for a compact model the global diffeomorphism).

Proof: the LC58 kernel; on the extracted subsequence, LC57 (1)–(2) for normalized sources
(`exists_scale_eventually_normalized_cone_radial_witnesses`) and
`exists_scale_eventually_open_ball_model_type_joint` on the normalized family (rescaled instances
passed by name), at one common scale `R ≥ T`.
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

/-- **LC58 binding with all three LC57 conclusions** (master207A, A:23194). Under LC58's
sequential hypothesis (unbundled LC56 packages of the normalized sources, either model branch),
every `0 < δ < 1`, `0 < ε < 1`, `0 < e < 1/40`, `T` admit `V ≥ T` and `α₀` such that for
`α > α₀` and every `p ∈ M^α` one `s ∈ [T, V]` and one model `b` give, at the scale `s ρ_α(p)`, a
Kleiner–Lott `δ`-map to `(C_b, o_b)`, an LC30 function with LC31's cutoff, and every open ball
`B(p, ρ' s ρ_α(p))`, `ρ' ∈ [1/5, 2]`, diffeomorphic to `N_b`. -/
theorem exists_uniform_scale_interval_joint_witnesses {mdim : ℕ}
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
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α, ∃ s ∈ Icc T V,
      ∃ hs : 0 < s, ∃ b : ι,
        Nonempty (@KleinerLottApprox (M α) (C b)
          ((mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))) (mC b)
          p (o b) δ) ∧
        (letI := (mM α).rescale (s * ρ α p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ α p)))
        let gR := scaleMetric ((s * ρ α p)⁻¹ ^ 2)
          (pow_pos (inv_pos.mpr (mul_pos hs (hρ α p))) 2) (g α)
        ∃ F : M α → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
          (∃ O : Set (M α), IsOpen O ∧ {x : M α | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O ∧
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
  refine exists_uniform_scale_interval_of_eventual_witnesses (X := M) _ T ?_
  intro a ha z
  obtain ⟨b, k, hk, hGH, ⟨jm, hjn, hA1⟩, Hb, hHb, hsec⟩ := hmodel a ha z
  obtain ⟨R₁, hR₁, h12⟩ := exists_scale_eventually_normalized_cone_radial_witnesses
    (M := fun j => M (a (k j))) (fun j => g (a (k j))) (fun j => hmetric (a (k j)))
    (fun j => ρ (a (k j)) (z (k j))) (fun j => hρ _ _) hGH (Hc b) (hcone b) Hb hHb hsec
    hδ hδ1 hε hε1 he he1
  have hGH' : @PointedGHConverges (fun j => M (a (k j)))
      (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
      (N b) (mN b) (fun j => jm j (n b)) (n b) := by
    have hf : (fun j => jm j (n b)) = fun j => z (k j) := funext hjn
    rw [hf]
    exact hGH
  obtain ⟨R₂, -, h3⟩ := exists_scale_eventually_open_ball_model_type_joint
    (M := fun j => M (a (k j)))
    (mM := fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
    (rbM := fun j => radialScaledBundle (g (a (k j))) (ρ (a (k j)) (z (k j)))⁻¹
      (inv_pos.mpr (hρ _ _)))
    (rmM := fun j => radialScaledManifold (m := mM (a (k j))) (g (a (k j))) (hmetric _)
      (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
    (hMc := fun j => ((mM (a (k j))).rescale_completeSpace_iff (ρ (a (k j)) (z (k j)))⁻¹
      (inv_pos.mpr (hρ _ _))).mpr (hMc _))
    (crM := fun j => radialScaledContinuous (g (a (k j))) (ρ (a (k j)) (z (k j)))⁻¹
      (inv_pos.mpr (hρ _ _)))
    hdim (gN b) (hgN b) (hsecN b) (n b) (Hc b) (hcone b)
    (fun j => scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρ _ _)) 2)
      (g (a (k j))))
    (fun j => isMetricNorm_of_riemannianBundle _) jm hGH' hA1 Hb hHb
    (fun i y hy => hsec i y (hjn i ▸ hy))
  set R : ℝ := max (max R₁ R₂) T with hRdef
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR2 : R₂ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR : 0 < R := lt_of_lt_of_le hR₁ hR1
  refine ⟨k, hk, R, le_max_right _ _, ?_⟩
  filter_upwards [h12 R hR hR1, h3 R hR2] with j h12j h3j
  refine ⟨hR, b, h12j.1, h12j.2, fun ρ' hρ' => ?_⟩
  obtain ⟨Ψ, hΨs, hΨt⟩ := h3j ρ' hρ'
  refine ⟨Ψ, hΨs.trans ?_, hΨt⟩
  have hball := MetricSpace.rescale_ball (mM (a (k j))) (ρ (a (k j)) (z (k j)))⁻¹
    (inv_pos.mpr (hρ _ _)) (z (k j)) (ρ' * (R * ρ (a (k j)) (z (k j))))
  rw [show (ρ (a (k j)) (z (k j)))⁻¹ * (ρ' * (R * ρ (a (k j)) (z (k j)))) = ρ' * R by
    field_simp [(hρ (a (k j)) (z (k j))).ne']] at hball
  rw [hjn j]
  exact hball

end DifferentialGeometry.Geometry.Collapse
