import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketWithCarrier
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# LPA02 with the carrier and the matching closed cores

`lpa02_uniform_joint_zero_witnesses` (row LPA02) exports the smooth type of the OPEN distance balls.
External review 43 (§3) asks for the relative compact core packet of the SAME selection: the same
radial function, its ACTUAL closed sublevels `A_ρ = {η ≤ ρ}`, their pulled-back model domains and
the identification with the soul disc bundle. `lpa02_uniform_joint_zero_witnesses_withCarrier` keeps
LPA02's quantifier order (one tail, then every point `p` and radius `r`, then the scale `s`) and
adds, for the SAME witnesses:

* a core coordinate `u : Ns → ℝ` of the smooth model `Ns`;
* inside the SAME LC67 radial function `F` (the one LPA02 selects at the scale `s r`): for every
  `ρ ∈ [1/5, 2]` a level `T > 0` and an ambient partial diffeomorphism `Ψ : X ⇀ Ns` with
  `{F ≤ ρ} ⊆ dom Ψ` and `Ψ '' {F ≤ ρ} = {u ≤ T}` (`Ψ⁻¹` is the isotopy-modified comparison map
  `j̃ = j ∘ K₁⁻¹` of the closed LC38, `eventually_closed_core_of_pulled_core`);
* the type of `u`: the model is compact and `u = 0` (then `{F ≤ ρ}` is the whole source and
  `{u ≤ T} = Ns`), or `u` is the fibre radius of a smooth Riemannian soul bundle
  `D : TotalSpace F V ≃ Ns` over `Fin 0 → ℝ` (rank 3), `AddCircle 1` (rank 2) or a compact connected
  surface on `𝓡 2` with a metric of `sec ≥ 0` (rank 1), as in
  `lfr49_finite_model_ball_type_all_scales_withCarrier`.

The cone error and the Lipschitz tolerance of the radial function satisfy `ε ≤ 1/64` (the closed
LC38 margin `4 ε < 1/8`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The selected radial function is admissible for the closed LC38.** LC67's clauses (LC30
closeness `< e`, `ε`-Lipschitz error with `ε ≤ 1/64`, smooth near `{3/40 ≤ d ≤ 11}`) give the
closeness, the `(1/64)`-Lipschitz error and the smoothness near `{1/10 ≤ d(p, ·) ≤ 10}` required by
`exists_scale_eventually_sublevel_onto_disc_core`. -/
theorem radial_admissible_of_buffered_clauses {E H : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [m : MetricSpace M] [ChartedSpace H M] {p : M} {F : M → ℝ} {ε e : ℝ} (hε64 : ε ≤ 1 / 64)
    (hO : ∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hclose : ∀ x, |F x - Metric.infDist x {p}| < e)
    (hdiff : ∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
      ε * dist x y) :
    (∀ x, |F x - dist p x| < e) ∧ LipschitzWith (1 / 64 : ℝ≥0) (fun x => F x - dist p x) ∧
      ∃ Wi : Set M, IsOpen Wi ∧ (∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F Wi := by
  obtain ⟨O, hO, hCO, hFO⟩ := hO
  refine ⟨fun x => ?_, LipschitzWith.of_dist_le_mul fun x y => ?_, O, hO, fun x h1 h2 => ?_, hFO⟩
  · have h := hclose x
    rwa [Metric.infDist_singleton, dist_comm] at h
  · have h := hdiff x y
    rw [Metric.infDist_singleton, Metric.infDist_singleton, dist_comm x p, dist_comm y p] at h
    rw [Real.dist_eq]
    have hd : 0 ≤ dist x y := dist_nonneg
    have h64 : ((1 / 64 : ℝ≥0) : ℝ) = 1 / 64 := by norm_num
    rw [h64]
    nlinarith
  · rw [dist_comm] at h1 h2
    exact hCO ⟨by linarith, by linarith⟩

/-- **Admissibility under a composed rescaling.** The closed-LC38 admissibility of a radial
function for the metric `c d` passes to the composed rescaling `b (a d)` when `c = b a`. -/
theorem closedCore_admissible_rescale_mul {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M]
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c) (hc : c = b * a) {p : M}
    {ηs : M → ℝ} {eη : ℝ}
    (h : letI := mM.rescale c hc0
      (∀ x, |ηs x - dist p x| < eη) ∧
        LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist p x) ∧
        ∃ Wi : Set M, IsOpen Wi ∧
          (∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ Wi) ∧
          ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) :
    letI := (mM.rescale a ha).rescale b hb
    (∀ x, |ηs x - dist p x| < eη) ∧
      LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist p x) ∧
      ∃ Wi : Set M, IsOpen Wi ∧
        (∀ x, 1 / 10 ≤ dist p x → dist p x ≤ 10 → x ∈ Wi) ∧
        ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi := by
  obtain ⟨h1, h2, Wi, hW1, hW2, hW3⟩ := h
  have hbac : ∀ t : ℝ, b * (a * t) = c * t := fun t => by rw [hc, mul_assoc]
  have hdist : ∀ x y : M, @dist M ((mM.rescale a ha).rescale b hb).toDist x y =
      @dist M (mM.rescale c hc0).toDist x y := fun x y => hbac _
  have k1 : ∀ x, |ηs x - @dist M ((mM.rescale a ha).rescale b hb).toDist p x| < eη := by
    intro x
    rw [hdist]
    exact h1 x
  have k2 : @LipschitzWith M ℝ ((mM.rescale a ha).rescale b hb).toPseudoEMetricSpace _
      (1 / 64 : ℝ≥0) (fun x => ηs x - @dist M ((mM.rescale a ha).rescale b hb).toDist p x) := by
    refine @LipschitzWith.of_dist_le_mul M ℝ ((mM.rescale a ha).rescale b hb).toPseudoMetricSpace
      _ _ _ fun x y => ?_
    have h2xy := @LipschitzWith.dist_le_mul M ℝ (mM.rescale c hc0).toPseudoMetricSpace _ _ _ h2 x y
    simp only [hdist]
    exact h2xy
  have k3 : ∀ x, 1 / 10 ≤ @dist M ((mM.rescale a ha).rescale b hb).toDist p x →
      @dist M ((mM.rescale a ha).rescale b hb).toDist p x ≤ 10 → x ∈ Wi := by
    intro x hx1 hx2
    rw [hdist] at hx1 hx2
    exact hW2 x hx1 hx2
  exact ⟨k1, k2, Wi, hW1, k3, hW3⟩

/-- **LPA02 with the carrier and the matching closed cores.** For LPA01's standing data
(`10 ≤ K`) and LC57's ranges (`0 < ε ≤ 1/64`, `δ' > 0`, `0 < e < 1/40`, `T`) fixed first: `V ≥ T`,
one cone error `0 < δ < δ'` and one tail on which every point `p` and every radius
`0 < r ≤ 2 r_p(w')` have a scale `s ∈ [T, V]` with LPA02's witnesses (model, cone, smooth `Ns`,
buffer, Kleiner–Lott map, LC67 radial function `F` with LC31's cutoff, open-ball types) AND a core
coordinate `u` of `Ns` such that every actual sublevel `{F ≤ ρ}`, `ρ ∈ [1/5, 2]`, of the SAME `F` is
carried by an ambient partial diffeomorphism onto a core `{u ≤ T}`, `u` being `0` on a compact model
or the fibre radius of the soul bundle (point, circle or `𝓡 2`-surface base with `sec ≥ 0`). -/
theorem lpa02_uniform_joint_zero_witnesses_withCarrier
    {X : ℕ → Type} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3)
    {ε δ' e T : ℝ} (hε : 0 < ε) (hε64 : ε ≤ 1 / 64) (hδ' : 0 < δ') (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ i in atTop, ∀ (p : X i) (r : ℝ) (hr : 0 < r),
      r ≤ 2 * firstVolumeScale (g i) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
      ∃ s ∈ Icc T V, ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI := mN
        letI := cN
        ∃ (_ : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
          ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
            (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N) (u : Ns → ℝ),
            (∀ y ∈ Metric.ball p (400 * (s * r)),
              SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
            Nonempty (@KleinerLottApprox (X i) C
              ((mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC p o δ) ∧
            (letI := (mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))
            let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2) (g i)
            ∃ F : X i → ℝ,
              (∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
                  {x | F x ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {x | F x ≤ ρ} = {y | u y ≤ T₀}) ∧
              LipschitzWith (Real.toNNReal (1 + ε)) F ∧
              (∃ O : Set (X i), IsOpen O ∧ {x : X i | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
              (∀ x, |F x - Metric.infDist x {p}| < e) ∧
              (∀ x, x ∉ {x : X i | 1 / 20 < dist x p ∧ dist x p < 20} →
                F x = Metric.infDist x {p}) ∧
              (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
                ε * dist x y) ∧
              (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
              (∀ q' ∈ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
                1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                  Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
              (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
              F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : X i | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
              (∃ O' : Set (X i), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
              ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
                (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
                (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
                tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                  {x : X i | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
                ∀ q', Real.sqrt (gR.inner q'
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                  (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L * (1 + ε)) ∧
            (∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
              Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ) ∧
            ((CompactSpace Ns ∧ ∀ y, u y = 0) ∨
             (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
                (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
                (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 3 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
             (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
                (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
                (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 2 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
             ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
                (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
                (_ : ConnectedSpace B)
                (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : B → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
                (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
                (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 1 ∧ (∀ x, u x = ‖(D.symm x).2‖) ∧
                ∃ nB : ℕ∞ω, 2 ≤ nB ∧
                  ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
                    ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂) := by
  have instNZ_LPA02 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨δ, hδ0, hδ1, hδδ', hδr⟩ := exists_coneError_below_thresholds hε hδ'
  have hε1 : ε < 1 := by linarith
  -- the LC58 kernel on the pairs `(p, r)` with `0 < r ≤ 2 r_p(w')`
  obtain ⟨V, hTV, α₀, hGC⟩ := exists_uniform_scale_interval_of_eventual_witnesses
    (X := fun i => {pr : X i × ℝ //
      0 < pr.2 ∧ pr.2 ≤ 2 * firstVolumeScale (g i) pr.1 (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))})
    (fun i y s => ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI := mN
        letI := cN
        ∃ (_ : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
        ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
          (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N) (u : Ns → ℝ),
          Nonempty (@KleinerLottApprox (X i) C
            ((mX i).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.1))) mC y.1.1 o δ) ∧
          (∀ (ηs : X i → ℝ) (eη : ℝ), eη < 1 / 40 →
            (letI := (mX i).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.1))
            (∀ x, |ηs x - dist y.1.1 x| < eη) ∧
              LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist y.1.1 x) ∧
              ∃ Wi : Set (X i), IsOpen Wi ∧
                (∀ x, 1 / 10 ≤ dist y.1.1 x → dist y.1.1 x ≤ 10 → x ∈ Wi) ∧
                ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
            ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
              ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
                {x | ηs x ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {x | ηs x ≤ ρ} = {y | u y ≤ T₀}) ∧
          (∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
            Ψ.source = Metric.ball y.1.1 (ρ' * (s * y.1.2)) ∧ Ψ.target = univ) ∧
          ((CompactSpace Ns ∧ ∀ y, u y = 0) ∨
           (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
              (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
              (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 3 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
           (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
              (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
              (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 2 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
           ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
              (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
              (_ : ConnectedSpace B)
              (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : B → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
              (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
              (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 1 ∧ (∀ x, u x = ‖(D.symm x).2‖) ∧
              ∃ nB : ℕ∞ω, 2 ≤ nB ∧
                ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
                  ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂)) T
    (by
      intro a ha z
      -- LPA02, first paragraph: LFR14's hypotheses for the normalized sequence
      obtain ⟨hmetric', hv0, hvol', hcurv', hη, hL, hsec'⟩ :=
        lpa02_normalized_sequence_hypotheses (finrank_euclideanSpace_fin) g hmetric hα hstand K A
          hA hder hΛ hw hwc a ha (fun j => (z j).1.1) (fun j => (z j).1.2) (fun j => (z j).2.1)
          (fun j => (z j).2.2)
      -- LFR49 (T0′ with its carrier) on the rescaled sources
      obtain ⟨k, hk, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, C, mC, o, ⟨Hc⟩, hCp,
          hcone, Ns, tNs, cNs, hNs, hhom, R₃, hR₃, h3, hcar⟩ :=
        @lfr49_finite_model_ball_type_all_scales_withCarrier K hK 1 _ one_pos hv0
          (fun R => (2 : ℝ) ^ (K + 2) * A (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
          (fun j => X (a j))
          (fun j => (mX (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.1))
          (fun j => (inferInstance : ChartedSpace E3 (X (a j))))
          (fun j => (inferInstance : IsManifold I3 ∞ (X (a j))))
          (fun j => (inferInstance : SigmaCompactSpace (X (a j))))
          (fun j => ((mX (a j)).rescale_completeSpace_iff _ _).mpr inferInstance)
          (fun j => connectedSpace_of_aligned_metric (g (a j)) (hmetric (a j)) (z j).1.1)
          (fun j => normalizedCenterMetric (g (a j)) ((z j).1.2) (z j).2.1) hmetric'
          (fun j => (z j).1.1) hvol' hcurv' _ _ hη hL hsec'
      -- the model clauses: four-point comparison and segments
      let instRB_LPA02 : RiemannianBundle (fun x : N => TangentSpace I3 x) :=
        ⟨G.toRiemannianMetric⟩
      have instRM_LPA02 : IsRiemannianManifold I3 N := hRiem
      have hGnorm : ∀ (x : N) (u : TangentSpace I3 x),
          ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x u u)) := by
        intro x u
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        rfl
      have hn : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ K - 1 by omega)
      have hfour : fourPointComparison 0 (univ : Set N) :=
        DifferentialGeometry.Geometry.FiniteComparison.fourPointComparison_zero_univ_finite G hn
          hGnorm hsecG
      have hseg : ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
          f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂ :=
        fun x y => Metric.exists_metric_segment_of_approximate_midpoints
          (DifferentialGeometry.Geometry.FiniteComparison.approximate_midpoints_finite G hn hGnorm)
          x y
      -- LFR49 step 1 along `k`, in the `scaleMetric` form of LC57
      obtain ⟨Hb, hHb, hsecM⟩ := @exists_curvature_scale_along_of_eventual (fun j => X (a j))
        (fun j => (mX (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.1))
        (fun j => (inferInstance : ChartedSpace E3 (X (a j))))
        (fun j => (inferInstance : IsManifold I3 ∞ (X (a j))))
        (fun j => normalizedCenterMetric (g (a j)) ((z j).1.2) (z j).2.1) hmetric'
        (fun j => (z j).1.1) _ _ hη hL hsec' k hk
      have hsecS : ∀ j, ∀ y ∈ @Metric.ball (X (a (k j)))
          ((mX (a (k j))).rescale ((z (k j)).1.2)⁻¹
            (inv_pos.mpr (z (k j)).2.1)).toPseudoMetricSpace ((z (k j)).1.1) (Hb j),
          SectionalBoundedBelowAt (scaleMetric (((z (k j)).1.2)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (z (k j)).2.1) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)) := by
        intro j y hy
        rw [← normalizedCenterMetric_eq_scaleMetric]
        exact hsecM j y hy
      -- LC57 (1): Kleiner–Lott maps at every large scale
      obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_normalized_cone_radial_witnesses
        (M := fun j => X (a (k j))) (fun j => g (a (k j))) (fun j => hmetric (a (k j)))
        (fun j => (z (k j)).1.2) (fun j => (z (k j)).2.1) hGH Hc hcone Hb hHb hsecS
        hδ0 hδ1 hε hε1 he he1
      -- the core coordinate and the closed cores at every large scale, in the `(R r)⁻¹` form
      have key : ∃ u : Ns → ℝ, ∃ R₄ : ℝ, 0 < R₄ ∧
          (∀ R : ℝ, ∀ hR : 0 < R, R₄ ≤ R → ∀ᶠ j in atTop,
            ∀ (ηs : X (a (k j)) → ℝ) (eη : ℝ), eη < 1 / 40 →
              (letI := (mX (a (k j))).rescale (R * (z (k j)).1.2)⁻¹ (inv_pos.mpr (mul_pos hR (z (k j)).2.1))
              (∀ x, |ηs x - dist (z (k j)).1.1 x| < eη) ∧
                LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist (z (k j)).1.1 x) ∧
                ∃ Wi : Set (X (a (k j))), IsOpen Wi ∧
                  (∀ x, 1 / 10 ≤ dist (z (k j)).1.1 x → dist (z (k j)).1.1 x ≤ 10 → x ∈ Wi) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
              ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 (X (a (k j))) Ns ∞,
                  {x | ηs x ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {x | ηs x ≤ ρ} = {y | u y ≤ T₀}) ∧
          ((CompactSpace Ns ∧ ∀ y, u y = 0) ∨
           (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
              (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
              (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 3 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
           (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
              (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
              (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 2 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
           ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
              (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
              (_ : ConnectedSpace B)
              (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
              (_ : FiniteDimensional ℝ F) (V : B → Type)
              (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
              (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
              (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
              (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
              (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
              Module.finrank ℝ F = 1 ∧ (∀ x, u x = ‖(D.symm x).2‖) ∧
              ∃ nB : ℕ∞ω, 2 ≤ nB ∧
                ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
                  ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂) := by
        rcases hcar with ⟨hcNs, hdiam⟩ | ⟨u, hclosed, hcases⟩
        · refine ⟨fun _ => 0, 10 * R₃, by positivity, fun R hR hRR => ?_, Or.inl ⟨hcNs, fun _ => rfl⟩⟩
          filter_upwards [hdiam, h3 R (by linarith)] with j hj h3j ηs eη heη hηs ρ hρ
          obtain ⟨Ψ, hΨs, hΨt⟩ := h3j (1 / 5) ⟨le_rfl, by norm_num⟩
          have hsrc : Ψ.source = univ := by
            rw [hΨs]
            apply eq_univ_of_forall
            intro x
            have h1 : ((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < R₃ := hj x
            change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < 1 / 5 * R
            rw [dist_comm]
            linarith
          have hsub : {x | ηs x ≤ ρ} = univ := by
            apply eq_univ_of_forall
            intro x
            have h1 : ((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < R₃ := hj x
            have h2 : |ηs x - (R * (z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x| < eη := hηs.1 x
            have h3' : (R * (z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < 1 / 10 := by
              rw [mul_inv, mul_assoc]
              calc R⁻¹ * (((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x) < R⁻¹ * R₃ :=
                    mul_lt_mul_of_pos_left h1 (inv_pos.mpr hR)
                _ ≤ 1 / 10 := by
                  rw [inv_mul_le_iff₀ hR]
                  linarith
            have h4 := (abs_lt.mp h2).2
            change ηs x ≤ ρ
            linarith [hρ.1]
          refine ⟨1, one_pos, Ψ, by rw [hsub, hsrc], ?_⟩
          rw [hsub, ← hsrc, Ψ.toPartialEquiv.image_source_eq_target, hΨt]
          exact (eq_univ_of_forall fun y => show (0 : ℝ) ≤ 1 by norm_num).symm
        · refine ⟨u, R₃, hR₃, fun R hR hRR => ?_, Or.inr hcases⟩
          filter_upwards [hclosed R hR hRR] with j hj ηs eη heη hηs ρ hρ
          exact hj ηs eη heη (closedCore_admissible_rescale_mul (inv_pos.mpr (z (k j)).2.1)
            (inv_pos.mpr hR) (inv_pos.mpr (mul_pos hR (z (k j)).2.1)) (mul_inv R _) hηs) ρ hρ
      obtain ⟨u, R₄, hR₄, hcore, hcases⟩ := key
      have hR0 : R₀ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_left _ _).trans (le_max_left _ _)
      have hR4 : R₄ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_right _ _).trans (le_max_left _ _)
      have hR3 : R₃ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_left _ _).trans (le_max_right _ _)
      have hRT : T ≤ max (max R₀ R₄) (max R₃ T) := (le_max_right _ _).trans (le_max_right _ _)
      have hR : 0 < max (max R₀ R₄) (max R₃ T) := hR₀.trans_le hR0
      refine ⟨k, hk, max (max R₀ R₄) (max R₃ T), hRT, ?_⟩
      filter_upwards [hall _ hR hR0, hcore _ hR hR4, h3 _ hR3] with j hj1 hjc hj3
      refine ⟨hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, ⟨Hc⟩,
        hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, hj1.1, hjc, fun ρ' hρ' => ?_, hcases⟩
      obtain ⟨Ψ, hΨs, hΨt⟩ := hj3 ρ' hρ'
      refine ⟨Ψ, ?_, hΨt⟩
      rw [hΨs]
      ext x
      change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < ρ' * max (max R₀ R₄) (max R₃ T) ↔
        dist x (z (k j)).1.1 < ρ' * (max (max R₀ R₄) (max R₃ T) * (z (k j)).1.2)
      rw [inv_mul_lt_iff₀ (z (k j)).2.1]
      have hcomm : (z (k j)).1.2 * (ρ' * max (max R₀ R₄) (max R₃ T)) =
          ρ' * (max (max R₀ R₄) (max R₃ T) * (z (k j)).1.2) := by ring
      rw [hcomm])
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [eventually_gt_atTop α₀,
    eventually_simultaneous_analytic_data (finrank_euclideanSpace_fin) g hmetric hα hstand K A hA
      hder hΛ hw hwc,
    hα.eventually_gt_atTop (1600 * V)] with i hiα hdata hαV p r hr hrv
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
      ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, ⟨φ⟩, hcore, h3, hcases⟩ :=
    hGC i hiα ⟨(p, r), hr, hrv⟩
  -- the original buffer from LPA01's normalized curvature clause (`α > 1600 V`)
  have hbuf : ∀ y ∈ Metric.ball p (400 * (s * r)),
      SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2)) := by
    intro y hy
    have hsV : s ≤ V := hsI.2
    have hαs : 1600 * s < α i := by linarith
    have hy' : y ∈ riemannianBallOf (normalizedCenterMetric (g i) r hr) p (α i / 4) := by
      change riemannianEDistOf (normalizedCenterMetric (g i) r hr) p y < ENNReal.ofReal (α i / 4)
      rw [riemannianEDistOf_normalizedCenterMetric (g i) (hmetric i) hr, MetricSpace.rescale_dist]
      have hd : dist p y < 400 * (s * r) := by rw [dist_comm]; exact Metric.mem_ball.mp hy
      have hlt : r⁻¹ * dist p y < α i / 4 := by
        rw [inv_mul_lt_iff₀ hr]
        nlinarith
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt
    have h := (hdata.2.2.2 p r hr hrv).2.2.1 y hy'
    rw [normalizedCenterMetric_eq_scaleMetric, sectionalBoundedBelowAt_scaleMetric_iff] at h
    refine h.mono ?_
    have h60 : 60 * s ≤ α i / 4 := by linarith
    have hsq : ((α i / 4) ^ 2)⁻¹ ≤ ((60 * s) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h60 2)
    have hid : (1 / 60) ^ 2 * (s * r)⁻¹ ^ 2 = ((60 * s) ^ 2)⁻¹ * r⁻¹ ^ 2 := by
      ring
    rw [hid, neg_mul, neg_le_neg_iff]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  -- LC67 + LC31 at the scale `s r`: the selected radial function
  obtain ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub, hO', L, hL0, hL, hc1,
      hc2, hc3, hc4, hc5⟩ :=
    exists_buffered_radial_cutoff_at_scale (g i) (hmetric i) (mul_pos hs hr) φ Hc hbuf hε hε1 hδr
      he he1
  have hadm := radial_admissible_of_buffered_clauses (I := I3)
    (m := (mX i).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) hε64 hFO hclose hdiff
  exact ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
    ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, hbuf, ⟨φ⟩,
    ⟨F, fun ρ hρ => hcore F e he1 hadm ρ hρ, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad,
      hrng, hsub, hO', L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩, h3, hcases⟩

end DifferentialGeometry.Geometry.Collapse
