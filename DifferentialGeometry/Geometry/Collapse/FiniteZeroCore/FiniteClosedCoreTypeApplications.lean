import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.FiniteClosedCoreType

/-!
# The actual sublevels are disc cores (consumer of the closed LC38)

`exists_scale_eventually_sublevel_onto_disc_core`: in carrier coordinates, for every scale
`R ≥ R₀`, one tail has, for every admissible radial function `η` of `(M_i, R⁻¹ d)` and every
`ρ ∈ [1/5, 2]`, a radius `T > 0` and an ambient partial diffeomorphism carrying the actual sublevel
`{η ≤ ρ}` onto the disc core `D_T = {‖(D⁻¹ x).2‖ ≤ T}`; in particular `{η ≤ ρ}` is compact. This is
the form in which the zero-model identifications of the disc cores (LFR54 pieces, stated on
`D_T` with `discCoreChartedSpace`) reach the source sublevels.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Manifold
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **The actual sublevels are disc cores.** In the setting of
`exists_scale_eventually_closed_disc_core_type_finite`: for every `R ≥ R₀` one tail has, for every
admissible radial function `η` of `(M_i, R⁻¹ d)` and every `ρ ∈ [1/5, 2]`, some `T > 0` and an
ambient partial diffeomorphism carrying `{η ≤ ρ}` onto the disc core `D_T`; the sublevel is
compact. -/
theorem exists_scale_eventually_sublevel_onto_disc_core
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (gSeq i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball n R, ∀ y ∈ ball n R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i n) a ⊆ (j i : N → M i) '' ball n b)
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {HB : Type} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {B : Type} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
    {Vb : B → Type} [TopologicalSpace (TotalSpace F Vb)]
    [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
    [FiberBundle F Vb] [VectorBundle ℝ F Vb] [IsContMDiffRiemannianBundle IB ∞ F Vb]
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) N ∞)
    (W : (x : N) → TangentSpace I x)
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I N)))
    {A₂ ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hWB : ∀ x, G.inner x (W x) (W x) ≤ 4)
    (hWdir : ∀ x, A₂ ≤ dist n x → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (W x) v ≤ -(1 / 4))
    (hdu : ∀ y, ℓ < ‖(D.symm y).2‖ →
      mvfderiv (I := I) (fun y' => ‖(D.symm y').2‖) y (W y) = 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      ∀ᶠ i in atTop, ∀ (η : M i → ℝ) (eη : ℝ), eη < 1 / 40 →
        (letI := (mM i).rescale R⁻¹ (inv_pos.mpr hR)
        (∀ x, |η x - dist (j i n) x| < eη) ∧
          LipschitzWith (1 / 64 : ℝ≥0) (fun x => η x - dist (j i n) x) ∧
          ∃ Wi : Set (M i), IsOpen Wi ∧
            (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ η Wi) →
        ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T : ℝ, 0 < T ∧
          ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
            {y | η y ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {y | η y ≤ ρ} = {x | ‖(D.symm x).2‖ ≤ T} ∧
            IsCompact {y | η y ≤ ρ} := by
  obtain ⟨R₀, hR₀, h⟩ := exists_scale_eventually_closed_disc_core_type_finite hr G hGnorm n gSeq
    hSeqNorm j hexh hconv hdist hcover D W hW hℓ hWB hWdir hdu
  refine ⟨R₀, hR₀, fun R hR hRR => ?_⟩
  obtain ⟨T₁, hT₁, hfin⟩ := h R hR hRR
  filter_upwards [hfin] with i hi η eη heη hηc ρ hρ
  obtain ⟨Ψ, hΨs, hΨi⟩ := hi η eη heη hηc ρ hρ (((ℓ + 1) + T₁) / 2) ⟨by linarith, by linarith⟩
  refine ⟨((ℓ + 1) + T₁) / 2, by linarith, Ψ, hΨs, hΨi, ?_⟩
  -- compactness: the inverse of `Ψ` maps the compact disc core onto the sublevel
  have hcpt : IsCompact {x : N | ‖(D.symm x).2‖ ≤ ((ℓ + 1) + T₁) / 2} :=
    (bundle_disc_core_data D).2.1 _
  have htgt : {x : N | ‖(D.symm x).2‖ ≤ ((ℓ + 1) + T₁) / 2} ⊆ Ψ.target := by
    rw [← hΨi]
    exact (Ψ.toPartialEquiv.image_source_eq_target ▸ image_mono hΨs)
  have hsymm : Ψ.symm '' {x : N | ‖(D.symm x).2‖ ≤ ((ℓ + 1) + T₁) / 2} = {y | η y ≤ ρ} := by
    rw [← hΨi, ← image_comp]
    refine (image_congr fun y hy => Ψ.toPartialEquiv.left_inv (hΨs hy)).trans (image_id _)
  rw [← hsymm]
  exact hcpt.image_of_continuousOn (Ψ.symm.contMDiffOn.continuousOn.mono htgt)

end DifferentialGeometry.Geometry.Collapse
