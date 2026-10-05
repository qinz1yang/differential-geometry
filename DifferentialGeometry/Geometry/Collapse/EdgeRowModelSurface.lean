import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EdgeCoreGlobalSmoothingUniform
import DifferentialGeometry.Geometry.Collapse.EdgeModelGradientClauseApplications
import DifferentialGeometry.Geometry.Collapse.EdgeRowModelChart

/-!
# LFR28 row, model side, stage 2: the model surface data on the rescaled carrier

Blueprint 207A, LFR28 (A:27223), proof step 1 ("Use the construction in LFR24's proof: LFR02 gives
a model smoothing `G` of `r` with GLOBAL value error `μΔ` and gradient error `10⁻⁸` on its collar.
Use the SAME profile to put `H_N = Δψ(G/Δ)`. Its whole `4Δ` sublevel is the compact smooth disk
there.") on the carrier `S` of the limit's surface factor, rescaled by `Δ⁻¹`.

* `edgeRowModelSurface_of_rescaled` (kernel, the ambient metric is the rescaled one): LFR24 with the
  global smoothing exported and the UNIFORM threshold (`finiteSurface_edge_model_core_global_uniform`)
  for an endpoint model `q` of error `δ ≤ εm²/24000000`, together with what the vector conditions of
  `edgeRowSlab_disk_bundle_of_estimates` need near the level `h = 4`: the model identity
  `dG_N(dΘ(a, Y)) = Δ dh(Y)` for `G_N = Δ F ∘ (Θ⁻¹ ·).2` and a `κ`-unit direction `Y` with
  `Δ dh(Y) ≥ 1/2` (where `κΔ = Δ⁻² κ`); the compact window `[-Δ/100, Δ/100] × {h ≤ 4.01}`.
* `edgeRowModelSurface` (binding, original metric on `S`): R2 (`exists_rescaled_carrier_metric`), the
  kernel on `(S, Δ⁻¹ d, κΔ)` with the endpoint model `q = e_W ∘ ψ / Δ` of I7(a)'s unit form, and B7
  (`edgeModel_gradient_clause_of_rescaled_carrier`): the model gradient clause `hGgrad` of (LFR28.4)
  for `G_N` and the global value error `|G_N - r| < μΔ` of (LFR28.5).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- `h = ψ ∘ F ≥ 39/10` forces `F ≥ 39/10` and `h = F` (the profile is `≤ 2` below `2`). -/
theorem le_of_le_edgeModelCore {Z : Type*} {F : Z → ℝ} {x : Z} {c : ℝ} (hc : 2 < c)
    (hx : c ≤ edgeModelCore F x) : c ≤ F x := by
  by_cases hF : F x ≤ 2
  · have h2 := edgeSublevelProfile_le_two hF
    change c ≤ edgeSublevelProfile (F x) at hx
    linarith
  · push Not at hF
    have h1 := edgeSublevelProfile_eq_self hF.le
    change c ≤ edgeSublevelProfile (F x) at hx
    linarith

/-- **LFR28 row, model side (kernel, rescaled carrier).** -/
theorem edgeRowModelSurface_of_rescaled
    {S : Type} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    [CompleteSpace S] [ConnectedSpace S]
    (o : ManifoldOrientation (𝓡 2) S 2) {k : ℕ∞} (hk : 3 ≤ k)
    (κΔ : ContMDiffRiemannianMetric (𝓡 2) ((k : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : S → Type _))
    (hnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κΔ.inner x w w)))
    (hsec : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κΔ.sectionalCurvature x v w)
    {n' : ℕ∞ω} (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    {Δ : ℝ} (hΔ : 0 < Δ)
    (hκΔ : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), κΔ.inner x v w = Δ⁻¹ ^ 2 * κ.inner x v w)
    {N : Type} [TopologicalSpace N] [ChartedSpace E3 N] {m : WithTop ℕ∞} (hm : m ≠ 0)
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N m)
    {εm : ℝ} (hεm : 0 < εm) (hεm1 : εm < 1 / 100) (s₀ : S) (q : S → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδε : δ ≤ εm ^ 2 / 24000000) (hq0 : q s₀ = 0) (hqnn : ∀ y ∈ closedBall s₀ 10, 0 ≤ q y)
    (hqdist : ∀ y ∈ closedBall s₀ 10, ∀ y' ∈ closedBall s₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hqdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall s₀ 10, |q y - t| ≤ δ)
    {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ < 1 / 100) :
    ∃ (FS h : S → ℝ) (OF Wh : Set S) (b : ClosedCell 2 → S),
      Continuous FS ∧ (∀ s, |FS s - dist s s₀| < μ) ∧
      IsOpen OF ∧ {x | 3 / 4 ≤ dist x s₀ ∧ dist x s₀ ≤ 91 / 10} ⊆ OF ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ FS OF ∧
      (∀ x ∈ OF, ∀ v ∈ κΔ.finiteMinimizingDirectionsTo ({s₀} : Set S) x,
        ∀ w : TangentSpace (𝓡 2) x,
          |mvfderiv (𝓡 2) FS x w + κΔ.inner x v w| ≤ εm / 25 * Real.sqrt (κΔ.inner x w w)) ∧
      h = edgeModelCore FS ∧
      IsOpen Wh ∧ closedBall s₀ 9 ⊆ Wh ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh ∧
      (∀ x, dist x s₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0) ∧
      IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧ range b = {x | dist x s₀ < 9 ∧ h x ≤ 4} ∧
      IsCompact (Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s s₀ < 9 ∧ h s ≤ 401 / 100}) ∧
      (∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 → ∀ (t a : ℝ) (Y : E2),
        mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) (Θ (t, s))
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) (a, Y)) =
            Δ * mvfderiv (𝓡 2) h s Y) ∧
      (∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 →
        ∃ Y : E2, κ.inner s Y Y ≤ 1 ∧ 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h s Y) := by
  have hr2 : 2 ≤ k := le_trans (by norm_num) hk
  obtain ⟨FS, hFc, hFr, ⟨OF, hOFo, hOF, hFs, hgrad⟩, h, hhdef, ⟨Wh, hWo, hW9, hWs⟩, -, -, hcol,
      hsub, -, h4, -⟩ :=
    finiteSurface_edge_model_core_global_uniform o κΔ hk hnorm hsec hεm hεm1 s₀ q δ hδ hδε hq0
      hqnn hqdist hqdense μ hμ hμ1
  obtain ⟨-, -, -, b, hb, hbr, -⟩ := hsub 4 ⟨by norm_num, by norm_num⟩
  obtain ⟨hcpt, -⟩ := hsub (401 / 100) ⟨by norm_num, by norm_num⟩
  -- `h ≥ 39/10` puts the point on the collar `r ≥ 2.1`
  have hcollar : ∀ s : S, 39 / 10 ≤ h s → 21 / 10 ≤ dist s s₀ := by
    intro s hs
    rw [hhdef] at hs
    have hF := le_of_le_edgeModelCore (by norm_num) hs
    have h1 := (abs_lt.mp (hFr s)).2
    linarith
  refine ⟨FS, h, OF, Wh, b, hFc, hFr, hOFo, hOF, hFs, hgrad, hhdef, hWo, hW9, hWs, h4, hb, hbr,
    isCompact_Icc.prod hcpt, fun s hs9 hs hs' t a Y => ?_, fun s hs9 hs hs' => ?_⟩
  · have h21 := hcollar s hs
    have hsOF : s ∈ OF := hOF ⟨by linarith, by linarith⟩
    have hFd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) FS s :=
      ((hFs s hsOF).contMDiffAt (hOFo.mem_nhds hsOF)).mdifferentiableAt (by simp)
    have hd := mvfderiv_snd_comp_symm_mfderiv hm Θ Δ (t, s) hFd (a, Y)
    rw [hd, hhdef, mvfderiv_edgeModelCore_eq hFc hμ1.le hFr h21]
  · have h21 := hcollar s hs
    obtain ⟨-, hg⟩ := hcol s h21 hs9.le
    obtain ⟨v, hv⟩ := (κΔ.finiteMinimizingDirectionsTo_nonempty_isCompact hr2 hnorm
      isClosed_singleton (singleton_nonempty s₀) s).1
    have hv1 : κΔ.inner s v v = 1 := hv.1
    have hgv := hg v hv v
    rw [hv1, Real.sqrt_one, mul_one] at hgv
    have hκv : κ.inner s v v = Δ ^ 2 := by
      have h1 := hκΔ s v v
      rw [hv1] at h1
      have hΔ2 : Δ⁻¹ ^ 2 * Δ ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hΔ.ne', one_pow]
      have h2 : κ.inner s v v = Δ ^ 2 * (Δ⁻¹ ^ 2 * κ.inner s v v) := by
        rw [← mul_assoc, mul_comm (Δ ^ 2), hΔ2, one_mul]
      rw [h2, ← h1, mul_one]
    refine ⟨-(Δ⁻¹ • v), ?_, ?_⟩
    · have hexp : κ.inner s (-(Δ⁻¹ • v)) (-(Δ⁻¹ • v)) = Δ⁻¹ ^ 2 * κ.inner s v v := by
        rw [ContinuousLinearMap.map_neg₂, ContinuousLinearMap.map_smul₂, map_neg, map_smul,
          smul_eq_mul, smul_eq_mul]
        ring
      rw [hexp, hκv, ← mul_pow, inv_mul_cancel₀ hΔ.ne', one_pow]
    · have hlin : mvfderiv (𝓡 2) h s (-(Δ⁻¹ • v)) = -(Δ⁻¹ * mvfderiv (𝓡 2) h s v) := by
        rw [map_neg, map_smul, smul_eq_mul]
      rw [hlin]
      have hmul : Δ * -(Δ⁻¹ * mvfderiv (𝓡 2) h s v) = -mvfderiv (𝓡 2) h s v := by
        field_simp
      rw [hmul]
      have := (abs_le.mp hgv).2
      linarith

/-- **LFR28 row, model side (binding).** R2 + the kernel on the rescaled carrier with the endpoint
model `q = e_W ∘ ψ / Δ` (I7(a), unit form) + B7: the model data of the vector conditions on
`(S, Δ⁻¹ d)`, the model gradient clause `hGgrad` of (LFR28.4) and the global value error of
`G_N = Δ F ∘ (Θ⁻¹ ·).2` (the input `hG` of (LFR28.5)). -/
theorem edgeRowModelSurface {N W S : Type} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [CompleteSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) N]
    [MetricSpace W] [mS : MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [CompleteSpace S] [ConnectedSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {k : ℕ} (hk : 3 ≤ k)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (κ : ContMDiffRiemannianMetric (𝓡 2) (((k : ℕ∞) : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _))
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (hκsec : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w)
    (o : ManifoldOrientation (𝓡 2) S 2) (e : N ≃ᵢ WithLp 2 (ℝ × W)) (ψ : S ≃ᵢ W)
    {m : WithTop ℕ∞} (hm : 2 ≤ m) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N m)
    (he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, ψ p.2))
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    {Δ : ℝ} (hΔ : 0 < Δ) (w₀ : W) (eW : W → ℝ)
    {εm δ μ : ℝ} (hεm : 0 < εm) (hεm1 : εm < 1 / 100) (hδ : 0 < δ)
    (hδε : δ ≤ εm ^ 2 / 24000000) (hμ : 0 < μ) (hμ1 : μ < 1 / 100)
    (heW0 : eW w₀ = 0) (heWnn : ∀ w, dist w w₀ / Δ ≤ 10 → 0 ≤ eW w / Δ)
    (heWdist : ∀ w w', dist w w₀ / Δ ≤ 10 → dist w' w₀ / Δ ≤ 10 →
      |dist (eW w / Δ) (eW w' / Δ) - dist w w' / Δ| ≤ δ)
    (heWdense : ∀ s ∈ Icc (0 : ℝ) 10, ∃ w, dist w w₀ / Δ ≤ 10 ∧ |eW w / Δ - s| ≤ δ) :
    ∃ (s₀ : S) (FS h : S → ℝ) (Wh : Set S) (b : ClosedCell 2 → S), ψ s₀ = w₀ ∧
      h = edgeModelCore FS ∧
      (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ);
        IsOpen Wh ∧ closedBall s₀ 9 ⊆ Wh ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh ∧
        (∀ x, dist x s₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0) ∧
        IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b ∧
        range b = {x | dist x s₀ < 9 ∧ h x ≤ 4} ∧
        IsCompact (Icc (-(Δ / 100)) (Δ / 100) ×ˢ
          {s : S | dist s s₀ < 9 ∧ h s ≤ 401 / 100}) ∧
        (∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 → ∀ (t a : ℝ) (Y : E2),
          mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) (Θ (t, s))
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) (a, Y)) =
              Δ * mvfderiv (𝓡 2) h s Y) ∧
        (∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 →
          ∃ Y : E2, κ.inner s Y Y ≤ 1 ∧ 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h s Y)) ∧
      (∀ x : N, |(e x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (e x).snd w₀ →
        dist (e x).snd w₀ ≤ 13 / 2 * Δ →
        ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {z | z.snd = w₀}) x,
          ∀ X : TangentSpace 𝓘(ℝ, E3) x,
            |mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) x X + G.inner x v X| ≤
              εm / 25 * Real.sqrt (G.inner x X X)) ∧
      ∀ x : N, |Δ * FS (Θ.symm x).2 - dist (e x).snd w₀| < μ * Δ := by
  have hΔi : 0 < Δ⁻¹ := inv_pos.mpr hΔ
  have hk' : (3 : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast hk
  have hk2 : (2 : ℕ∞) ≤ (k : ℕ∞) := le_trans (by norm_num) hk'
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    exact absurd hm (by norm_num)
  obtain ⟨κΔ, hκΔ, hsecΔ, htrans, -, hpkg⟩ := exists_rescaled_carrier_metric κ hκnorm hκsec hΔ
  obtain ⟨hRiemR, hcR, hnR⟩ := hpkg
  have hψw : ψ (ψ.symm w₀) = w₀ := ψ.apply_symm_apply w₀
  have hdR : ∀ y y' : S, @dist S (mS.rescale Δ⁻¹ hΔi).toDist y y' = dist (ψ y) (ψ y') / Δ := by
    intro y y'
    rw [MetricSpace.rescale_dist, ψ.dist_eq, div_eq_inv_mul]
  have hdR0 : ∀ y : S, @dist S (mS.rescale Δ⁻¹ hΔi).toDist y (ψ.symm w₀) = dist (ψ y) w₀ / Δ := by
    intro y
    rw [hdR, hψw]
  set s₀ : S := ψ.symm w₀ with hs₀def
  set q : S → ℝ := fun s => eW (ψ s) / Δ with hqdef
  have hq0 : q s₀ = 0 := by
    change eW (ψ (ψ.symm w₀)) / Δ = 0
    rw [ψ.apply_symm_apply, heW0, zero_div]
  have hqnn : ∀ y, @dist S (mS.rescale Δ⁻¹ hΔi).toDist y s₀ ≤ 10 → 0 ≤ q y := fun y hy =>
    heWnn (ψ y) (by rw [hdR0] at hy; exact hy)
  have hqdist : ∀ y, @dist S (mS.rescale Δ⁻¹ hΔi).toDist y s₀ ≤ 10 →
      ∀ y', @dist S (mS.rescale Δ⁻¹ hΔi).toDist y' s₀ ≤ 10 →
      |dist (q y) (q y') - @dist S (mS.rescale Δ⁻¹ hΔi).toDist y y'| ≤ δ := by
    intro y hy y' hy'
    rw [hdR0] at hy hy'
    rw [hdR]
    exact heWdist (ψ y) (ψ y') hy hy'
  have hqdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y, @dist S (mS.rescale Δ⁻¹ hΔi).toDist y s₀ ≤ 10 ∧
      |q y - t| ≤ δ := by
    intro t ht
    obtain ⟨w, hw, hwt⟩ := heWdense t ht
    refine ⟨ψ.symm w, ?_, ?_⟩
    · rw [hdR0, ψ.apply_symm_apply]
      exact hw
    · simp only [hqdef, ψ.apply_symm_apply]
      exact hwt
  obtain ⟨FS, h, OF, Wh, b, hFc, hFr, hOFo, hOF, hFs, hgrad, hhdef, hWo, hW9, hWs, h4, hb, hbr,
      hQ, hGN, hdir⟩ :=
    letI := mS.rescale Δ⁻¹ hΔi
    letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κΔ.toRiemannianMetric⟩
    haveI := hRiemR
    haveI := hcR
    edgeRowModelSurface_of_rescaled o hk' κΔ hnR hsecΔ κ hΔ hκΔ hm0 Θ hεm hεm1 s₀ q hδ hδε hq0
      (fun y hy => hqnn y hy) (fun y hy y' hy' => hqdist y hy y' hy')
      (fun t ht => by
        obtain ⟨y, hy, hyt⟩ := hqdense t ht
        exact ⟨y, hy, hyt⟩) hμ hμ1
  have hB7 := edgeModel_gradient_clause_of_rescaled_carrier G hk2 hGnorm κ κΔ hk2 hκnorm e ψ hm Θ he
    hpull hΔ hκΔ htrans s₀ (by positivity : (0 : ℝ) ≤ εm / 25) hOFo hOF hFs hgrad
  rw [hψw] at hB7
  refine ⟨s₀, FS, h, Wh, b, hψw, hhdef, ⟨hWo, hW9, hWs, h4, hb, hbr, hQ, hGN, hdir⟩, hB7, fun x => ?_⟩
  set p : ℝ × S := Θ.symm x with hp
  have hx : x = Θ p := (Θ.apply_symm_apply x).symm
  have hsnd : (e x).snd = ψ p.2 := by
    rw [hx, he]
    rfl
  have hFp := hFr p.2
  rw [hdR0] at hFp
  rw [hsnd]
  have hrw : Δ * FS p.2 - dist (ψ p.2) w₀ = Δ * (FS p.2 - dist (ψ p.2) w₀ / Δ) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hΔ, mul_comm μ Δ]
  exact mul_lt_mul_of_pos_left hFp hΔ

end DifferentialGeometry.Geometry.Collapse
