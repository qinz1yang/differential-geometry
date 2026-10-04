import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftJacobiField
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftRiccatiApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftBound
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelTransportApplications
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteParallelSliceApplications

/-!
# S3-SHIFT: the transverse shift in any dimension (lane CMS3-SHIFT, group G3)

* `transverseSpeedSq_le_one_of_parallel`: for a complete `C^(r+1)` metric (`r ≥ 2`) with `sec ≥ 0`, a
  unit-speed geodesic `γ`, a field `ξ` parallel along `γ` with `|ξ(t₀)| = 1`, and `sec ≤ Λ` along the
  transverse geodesic `h ↦ α(t₀, h)` on `[0, ρ]`, `Λ ρ² ≤ 1/4`: the transverse speed
  `|∂ₜ α(t₀, h)|² ≤ 1` on `[0, ρ]`.
  Route: frame coordinates `j_i = g(J, e_i)` of the Jacobi field `J = ∂ₜα` in a `g`-parallel
  ORTHONORMAL frame `e_i` along the transverse geodesic (S3-PT.a) satisfy `j'' = −R j`, `j'(0) = 0`, with
  `R_ik = Rm(e_k, σ', σ', e_i)` symmetric, `≥ 0` and `≤ Λ`; the matrix Riccati kernel (G1) gives
  `|j| ≤ |j(0)| = 1`.
* `exists_transverse_shift_lipschitz` (frozen name): the binding; `ρ` depends on `x, L` only.
  Deviation (a strengthening, CMS-J precedent): the unused instance `[NeZero (finrank ℝ E)]` is dropped;
  the verbatim frozen statement is an `example` in `TransverseShiftGeneralApplications.lean`.
* `exists_transverse_shift_lipschitz_prefix`: the same, and the field `ξ` (parallel transport of `w`)
  stays tangent to every totally geodesic `C^k` slice `Z` (`k ≥ 3`) containing a prefix `γ([0, T])`
  when `w` is tangent to `Z` (S3-PT.b, `exists_parallel_mem_sliceTangent`'s proof route); this is the
  tangency the REL kernel consumes.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.MetricKoszul (raisedKoszulOp)
open DifferentialGeometry.Analysis (coefficientRm04)

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance continuousDualEquiv_CMS3SHIFTg : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

local instance bilinNormedGroup_CMS3SHIFTg : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance bilinNormedSpace_CMS3SHIFTg : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- The coefficient curvature of `C²` coefficients is jointly continuous. -/
theorem continuousAt_coefficientRm04_comp {b : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hb : ContDiffOn ℝ 2 b U) (hsymm : ∀ y ∈ U, ∀ u v : E, b y u v = b y v u)
    (hco : ∀ y ∈ U, IsCoercive (b y)) {x X Y Z W : ℝ → E} {h₀ : ℝ} (hx : ContinuousAt x h₀)
    (hxU : x h₀ ∈ U) (hX : ContinuousAt X h₀) (hY : ContinuousAt Y h₀) (hZ : ContinuousAt Z h₀)
    (hW : ContinuousAt W h₀) :
    ContinuousAt (fun h => coefficientRm04 b (x h) (X h) (Y h) (Z h) (W h)) h₀ := by
  have hΓ : ContDiffOn ℝ 1
      (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) U :=
    MetricKoszul.raisedKoszulOp_contDiffOn (hb.of_le (by norm_num))
      (hb.fderiv_of_isOpen hU (by norm_num)) hco
  have hC : ContinuousAt (Geometry.Connection.connectionFormCurvatureCLM
      (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E))) (x h₀) :=
    (Geometry.Connection.connectionFormCurvatureCLM_contDiffAt (n := 0)
      (by simpa using hΓ.contDiffAt (hU.mem_nhds hxU))).continuousAt
  have hev : (fun h => coefficientRm04 b (x h) (X h) (Y h) (Z h) (W h)) =ᶠ[𝓝 h₀]
      fun h => b (x h) (Geometry.Connection.connectionFormCurvatureCLM
        (fun y => (raisedKoszulOp (b y) (fderiv ℝ b y) : E →L[ℝ] E →L[ℝ] E)) (x h) (X h) (Y h)
          (Z h)) (W h) := by
    filter_upwards [hx.preimage_mem_nhds (hU.mem_nhds hxU)] with h hh
    exact DifferentialGeometry.Analysis.coefficientRm04_eq_connectionFormCurvature_of_isOpen hU hb
      hsymm hco hh _ _ _ _
  refine ContinuousAt.congr ?_ hev.symm
  have hbc : ContinuousAt b (x h₀) := hb.continuousOn.continuousAt (hU.mem_nhds hxU)
  exact ((hbc.comp hx).clm_apply ((((hC.comp hx).clm_apply hX).clm_apply hY).clm_apply hZ)).clm_apply
    hW

end Euclidean

section Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

local instance continuousDualEquiv_CMS3SHIFTgm : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- **The transverse speed is at most one** along a parallel field (any dimension). -/
theorem transverseSpeedSq_le_one_of_parallel
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : TangentBundle I M) (hp : g.inner p.proj p.snd p.snd = 1) {ξ : ℝ → E}
    (hξ : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ) (t₀ : ℝ)
    (hξ1 : g.inner (g.geodesicFlow p t₀).proj (ξ t₀) (ξ t₀) = 1) {ρ Λ : ℝ} (hρ : 0 < ρ)
    (hΛ : 0 ≤ Λ) (hΛρ : Λ * ρ ^ 2 ≤ 1 / 4)
    (hK : ∀ h ∈ Icc 0 ρ, ∀ v w : TangentSpace I (transverseShift g p ξ (t₀, h)),
      g.sectionalCurvature (transverseShift g p ξ (t₀, h)) v w ≤ Λ) :
    ∀ h ∈ Icc 0 ρ, transverseSpeedSq g p ξ (t₀, h) ≤ 1 := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  have hV : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t :=
    contMDiffAt_parallel_geodesicFlow hr1 g (fun t => hmem _) hξ
  set p₁ : TangentBundle I M := ⟨(g.geodesicFlow p t₀).proj, ξ t₀⟩ with hp₁
  set n := Module.finrank ℝ E with hn
  obtain ⟨P, hP0, hPpar, hPc, hPiso, -, -⟩ := exists_parallelTransport_geodesicFlow g hr1 hnorm p₁
  obtain ⟨f, hf⟩ := exists_orthonormal_of_pos (g.inner p₁.proj : E →L[ℝ] E →L[ℝ] ℝ)
    (fun u v => g.symm _ u v) (fun v hv => g.pos _ v hv)
  set σ : ℝ → M := fun h => transverseShift g p ξ (t₀, h) with hσ
  set u : ℝ → E := fun h => (g.geodesicFlow p₁ h).snd with hu
  set e : Fin n → ℝ → E := fun i h => P h (f i) with he
  set J : ℝ → E := fun h => transverseJacobi g p ξ (t₀, h) with hJ
  set jW : Fin n → ℝ → ℝ := fun i h => g.inner (σ h) (J h) (e i h) with hjW
  -- the frame is orthonormal
  have hon : ∀ h i k, (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) (e i h) (e k h) =
      if i = k then 1 else 0 := fun h i k => (hPiso h (f i) (f k)).trans (hf i k)
  have hexp : ∀ h (X : E), X = ∑ k, (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) X (e k h) • e k h :=
    fun h X => eq_sum_of_orthonormal _ rfl (fun k => e k h) (hon h) X
  have hpars : ∀ h (X Y : E), (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) X Y =
      ∑ i, (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) X (e i h) *
        (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) Y (e i h) :=
    fun h X Y => apply_eq_sum_of_orthonormal _ rfl (fun k => e k h) (hon h) X Y
  -- the Jacobi equation in frame coordinates
  have hpair := fun i h => hasDerivAt_transverseJacobi_pairing_chart g hr hdom p hV t₀
    (W := e i) (hPpar (f i)) h
  have hd1 : ∀ i h, HasDerivAt (jW i) (deriv (jW i) h) h := fun i h => (hpair i h).1
  have hd2 : ∀ i h, HasDerivAt (deriv (jW i))
      (-(finiteRm04 g (σ h) (J h) (u h) (u h) (e i h))) h := fun i h => (hpair i h).2.1
  have hk0 : ∀ i, deriv (jW i) 0 = 0 := fun i =>
    deriv_transverseJacobi_pairing_zero g hr hdom p hV hξ t₀ (W := e i) (hPpar (f i))
  set Mx : ℝ → Matrix (Fin n) (Fin n) ℝ := fun h => Matrix.of fun i k =>
    finiteRm04 g (σ h) (e k h) (u h) (u h) (e i h) with hMx
  have hRm : ∀ h i, finiteRm04 g (σ h) (J h) (u h) (u h) (e i h) =
      ∑ k, Mx h i k * jW k h := by
    intro h i
    have h1 := congrArg (fun X => finiteRm04 g (σ h) X (u h) (u h) (e i h)) (hexp h (J h))
    refine h1.trans ?_
    rw [finiteRm04_sum_left hr1 g]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hMx, Matrix.of_apply, hjW]
    ring
  -- Euclidean vectors and the operator
  set Eq := EuclideanSpace.equiv (Fin n) ℝ with hEq
  set j : ℝ → EuclideanSpace ℝ (Fin n) := fun h => Eq.symm fun i => jW i h with hj
  set k : ℝ → EuclideanSpace ℝ (Fin n) := fun h => Eq.symm fun i => deriv (jW i) h with hk
  set R : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := fun h =>
    Matrix.toEuclideanCLM (𝕜 := ℝ) (Mx h) with hR
  have hjd : ∀ h, HasDerivAt j (k h) h := fun h =>
    Eq.symm.hasFDerivAt.comp_hasDerivAt h (hasDerivAt_pi.mpr fun i => hd1 i h)
  have hkd : ∀ h, HasDerivAt k (-(R h (j h))) h := by
    intro h
    have h1 := Eq.symm.hasFDerivAt.comp_hasDerivAt h (hasDerivAt_pi.mpr fun i => hd2 i h)
    refine h1.congr_deriv ?_
    ext i
    change -(finiteRm04 g (σ h) (J h) (u h) (u h) (e i h)) =
      -(Matrix.mulVec (Mx h) (fun k => jW k h) i)
    rw [hRm h i]
    rfl
  -- properties of `R`
  have hu1 : ∀ h, g.inner (σ h) (u h) (u h) = 1 := fun h =>
    (g.inner_geodesicFlow_eq hr1 p₁ h (hmem _)).trans hξ1
  set Xf : ℝ → EuclideanSpace ℝ (Fin n) → E := fun h a => ∑ k, a k • e k h with hXf
  have hquad : ∀ h (a : EuclideanSpace ℝ (Fin n)),
      ⟪R h a, a⟫_ℝ = finiteRm04 g (σ h) (Xf h a) (u h) (u h) (Xf h a) := by
    intro h a
    rw [inner_toEuclideanCLM_self_eq_sum, hXf]
    dsimp only
    rw [finiteRm04_sum_left hr1 g, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [finiteRm04_sum_right hr1 g, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hMx, Matrix.of_apply]
    ring
  have hXX : ∀ h (a : EuclideanSpace ℝ (Fin n)), g.inner (σ h) (Xf h a) (Xf h a) = ‖a‖ ^ 2 := by
    intro h a
    have key : ∀ (B : E →L[ℝ] E →L[ℝ] ℝ) (v : Fin n → E),
        (∀ i k, B (v i) (v k) = if i = k then 1 else 0) → ∀ (c : Fin n → ℝ) (i : Fin n),
          B (∑ k, c k • v k) (v i) = c i := by
      intro B v hB c i
      simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul, hB,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hc : ∀ i, (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) (Xf h a) (e i h) = a i := fun i =>
      key _ (fun k => e k h) (hon h) (fun k => a k) i
    change (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) (Xf h a) (Xf h a) = ‖a‖ ^ 2
    rw [hpars h, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Real.norm_eq_abs, sq_abs, sq]
  have hRsa : ∀ h, IsSelfAdjoint (R h) := fun h =>
    isSelfAdjoint_toEuclideanCLM_of_symm fun i k => finiteRm04_jacobi_symm hr1 g _ _ _ _
  have hRpos : ∀ h (a : EuclideanSpace ℝ (Fin n)), 0 ≤ ⟪R h a, a⟫_ℝ := fun h a => by
    rw [hquad]; exact finiteRm04_nonneg_of_sectional hr1 g _ (hsec _) _ _
  have hRbd : ∀ h ∈ Icc 0 ρ, ‖R h‖ ≤ Λ := by
    intro h hh
    refine norm_le_of_inner_self_le hΛ (hRsa h) (hRpos h) fun a => ?_
    rw [hquad]
    have h1 := finiteRm04_le_of_sectional hr1 g (σ h) hΛ (hK h hh) (Xf h a) (u h)
    rwa [hu1 h, mul_one, hXX h a] at h1
  -- continuity of `R`
  have hRc : Continuous R := by
    have hMc : Continuous Mx := by
      refine continuous_pi fun i => continuous_pi fun k => ?_
      refine continuous_iff_continuousAt.mpr fun h₀ => ?_
      set q := σ h₀ with hq
      have hσc : Continuous σ := by
        have h := continuous_geodesicFlow_of_forall_mem hr1 g (p := p₁) (fun t => hmem _)
        exact (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp h
      have hG : ∀ᶠ h in 𝓝 h₀, σ h ∈ (chartAt H q).source :=
        hσc.continuousAt.preimage_mem_nhds ((chartAt H q).open_source.mem_nhds (mem_chart_source H q))
      obtain ⟨hPC, hVC, -, -, -, -⟩ := transverseChart_data g hr hdom p hV (z₀ := (t₀, h₀))
        (mem_chart_source H q)
      have hline : Continuous fun h : ℝ => ((t₀, h) : ℝ × ℝ) := continuous_const.prodMk continuous_id
      have hPosc : ContinuousAt (fun h => transverseChartPos g p ξ q (t₀, h)) h₀ :=
        hPC.continuousAt.comp hline.continuousAt
      have hVelc : ContinuousAt (fun h => transverseChartVel g p ξ q (t₀, h)) h₀ :=
        hVC.continuousAt.comp hline.continuousAt
      have hEc : ∀ m, ContinuousAt (fun h => (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)
          (⟨σ h, e m h⟩ : TangentBundle I M)).2) h₀ := by
        intro m
        have hsrc : (⟨σ h₀, e m h₀⟩ : TangentBundle I M) ∈
            (extChartAt I.tangent (⟨q, 0⟩ : TangentBundle I M)).source := by
          rw [extChartAt_source, TangentBundle.mem_chart_source_iff]
          exact mem_chart_source H q
        have hc : ContinuousAt (fun h => (⟨σ h, e m h⟩ : TangentBundle I M)) h₀ :=
          (hPc (f m)).continuousAt
        exact continuousAt_snd.comp (ContinuousAt.comp (continuousAt_extChartAt' hsrc) hc)
      obtain ⟨-, hbsymm0, -⟩ := chartCoeffFinite_data hr1 g q
        ((extChartAt I q).map_source (mem_extChartAt_source q))
      have hcoef := continuousAt_coefficientRm04_comp (b := chartCoeffFinite g q)
        (isOpen_extChartAt_target q)
        (contDiffOn_chartCoeffFinite g (two_le_coe_add_one hr1) (WithTop.coe_le_coe.mpr le_top) q)
        (fun y _ u v => chartCoeffFinite_symm g q y u v) (fun y hy => isCoercive_chartCoeffFinite g hy)
        hPosc ((extChartAt I q).map_source (mem_extChartAt_source q)) (hEc k) hVelc hVelc (hEc i)
      refine hcoef.congr ?_
      filter_upwards [hG] with h hh
      change coefficientRm04 (chartCoeffFinite g q) (extChartAt I q (σ h)) _ _ _ _ =
        finiteRm04 g (σ h) (e k h) (u h) (u h) (e i h)
      rw [finiteRm04_eq_chart hr1 g hh, extChartAt_tangent_zero_snd_eq_mfderiv (I := I) q hh,
        extChartAt_tangent_zero_snd_eq_mfderiv (I := I) q hh]
      have hv : transverseChartVel g p ξ q (t₀, h) =
          mfderiv I 𝓘(ℝ, E) (extChartAt I q) (σ h) (u h) :=
        extChartAt_tangent_geodesicFlow_snd_eq g p₁ h hh
      rw [hv]
    exact ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional).comp hMc
  -- the kernel
  have hjk := norm_le_of_jacobi_vector (R := R) hρ hΛ hΛρ hRc (fun h _ => hRsa h)
    (fun h _ => hRpos h) hRbd (z := j) (z' := k) (fun h _ => (hjd h).hasDerivWithinAt)
    (fun h _ => (hkd h).hasDerivWithinAt) (by ext i; exact hk0 i)
  -- `|j|² = |J|²`
  have hnormj : ∀ h, ‖j h‖ ^ 2 = transverseSpeedSq g p ξ (t₀, h) := by
    intro h
    rw [transverseSpeedSq_eq_inner_transverseJacobi, EuclideanSpace.norm_sq_eq]
    change ∑ i, ‖jW i h‖ ^ 2 = (g.inner (σ h) : E →L[ℝ] E →L[ℝ] ℝ) (J h) (J h)
    rw [hpars h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs, sq]
  have hj0 : ‖j 0‖ = 1 := by
    have h := hnormj 0
    rw [transverseSpeedSq_zero g hr1 hdom p hp ξ t₀] at h
    have h0 : 0 ≤ ‖j 0‖ := norm_nonneg _
    nlinarith
  intro h hh
  have h1 := hjk h hh
  rw [hj0] at h1
  rw [← hnormj h]
  have h0 : 0 ≤ ‖j h‖ := norm_nonneg _
  nlinarith


/-- **Uniform transverse shift along parallel fields.** `ρ` depends on `x, L` only (a bound `Λ` of
`|sec|` on the compact ball `closedBall x (L + 2)`, `ρ = 1/(2 max(Λ, 1))`); for every unit geodesic
starting within `ρ` of `x` and every parallel field `ξ` of unit length on `[0, L]`, the shifted curves
`t ↦ exp_{γ t}(h ξ t)`, `0 ≤ h < ρ`, are `1`-Lipschitz on `[0, L]`. -/
theorem exists_dist_transverseShift_le_of_parallel
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ ξ : ℝ → E, IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ →
        (∀ t ∈ Icc 0 L, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1) →
        ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
          dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
            (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
              |t₁ - t₂| := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hdom := g.geodesicFlowDomain_eq_univ hr hnorm
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨Λ₀, hΛ₀, hΛ₀b⟩ := g.exists_abs_sectionalCurvature_le_of_isCompact hr
    (isCompact_closedBall x (L + 2))
  set Λ := max Λ₀ 1 with hΛdef
  have hΛ1 : (1 : ℝ) ≤ Λ := le_max_right _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le one_pos hΛ1
  refine ⟨1 / (2 * Λ), by positivity, ?_⟩
  intro p hxp hp ξ hξ hunit h hh t₁ ht₁ t₂ ht₂
  have hρ1 : 1 / (2 * Λ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hΛρ : Λ * (1 / (2 * Λ)) ^ 2 ≤ 1 / 4 := by
    rw [show Λ * (1 / (2 * Λ)) ^ 2 = 1 / (4 * Λ) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have hV : ∀ t, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent r
      (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) t :=
    contMDiffAt_parallel_geodesicFlow hr1 g (fun t => hmem _) hξ
  have hG : ∀ t ∈ Icc 0 L, transverseSpeedSq g p ξ (t, h) ≤ 1 := by
    intro t ht
    refine transverseSpeedSq_le_one_of_parallel g hr hnorm hsec p hp hξ t (hunit t ht)
      (by positivity) hΛpos.le hΛρ ?_ h ⟨hh.1, hh.2.le⟩
    intro h' hh' v w
    have hball : transverseShift g p ξ (t, h') ∈ closedBall x (L + 2) := by
      rw [mem_closedBall, dist_comm]
      have hd := dist_transverseShift_le_add g hr1 hnorm hdom x p hp ht.1 hh'.1 (hunit t ht)
      linarith [ht.2, hh'.2]
    exact (le_abs_self _).trans ((hΛ₀b _ hball v w).trans (le_max_left _ _))
  have hdist := dist_transverseShift_le g hr1 hnorm hdom p (J := univ) (fun t _ => hV t)
    (subset_univ _) hG t₁ ht₁ t₂ ht₂
  have e1 : g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M) =
      transverseShift g p ξ (t₁, h) :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ (ξ t₁) h (hmem _)
  have e2 : g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M) =
      transverseShift g p ξ (t₂, h) :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 _ (ξ t₂) h (hmem _)
  rw [e1, e2]
  exact hdist

/-- **S3-SHIFT binding** (frozen name; `3 ≤ r`, `sec ≥ 0`, ANY dimension; the unused instance
`[NeZero (finrank ℝ E)]` of the frozen statement is dropped). The output shape of CMS-J's
`exists_transverse_shift_lipschitz_dim_two` without `hdim`, with `ξ` the parallel transport of `w`. -/
theorem exists_transverse_shift_lipschitz
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ ∧
          Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) ∧
          (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          ∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤ |t₁ - t₂| := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hr1 : 1 ≤ r := one_le_two.trans hr2
  obtain ⟨ρ, hρ, hb⟩ := exists_dist_transverseShift_le_of_parallel g hr2 hnorm hsec x L
  refine ⟨ρ, hρ, fun p hxp hp w hw hwp => ?_⟩
  obtain ⟨ξ, hξ0, hξpar, hξc, hξu⟩ := exists_parallel_unit_normal_geodesicFlow g hr1 hnorm p w hw hwp
  exact ⟨ξ, hξ0, hξpar, hξc, hξu, hb p hxp hp ξ hξpar fun t _ => (hξu t).1⟩

/-- **S3-SHIFT with prefix tangency** (for the REL kernel). The binding's output, plus: the field `ξ`
(parallel transport of `w`) is tangent to every totally geodesic `C^k` slice `Z` (`k ≥ 3`) along every
prefix `γ([0, T])`, `T ∈ [0, L]`, that lies in `Z`, provided `w` is tangent to `Z` (S3-PT.b). -/
theorem exists_transverse_shift_lipschitz_prefix
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂) (x : M) (L : ℝ) :
    ∃ ρ > 0, ∀ p : TangentBundle I M, dist x p.proj < ρ → g.inner p.proj p.snd p.snd = 1 →
      ∀ w : E, g.inner p.proj w w = 1 → g.inner p.proj w p.snd = 0 →
        ∃ ξ : ℝ → E, ξ 0 = w ∧
          IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ univ ∧
          Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ξ t⟩ : TangentBundle I M)) ∧
          (∀ t, g.inner (g.geodesicFlow p t).proj (ξ t) (ξ t) = 1 ∧
            g.inner (g.geodesicFlow p t).proj (ξ t) (g.geodesicFlow p t).snd = 0) ∧
          (∀ h ∈ Ico 0 ρ, ∀ t₁ ∈ Icc 0 L, ∀ t₂ ∈ Icc 0 L,
            dist (g.expMap (⟨(g.geodesicFlow p t₁).proj, h • ξ t₁⟩ : TangentBundle I M))
              (g.expMap (⟨(g.geodesicFlow p t₂).proj, h • ξ t₂⟩ : TangentBundle I M)) ≤
                |t₁ - t₂|) ∧
          ∀ k : ℕ∞, 3 ≤ k → ∀ (d : ℕ) (Z : Set M), IsEmbeddedSliceOfOrder I (k : ℕ∞ω) d Z →
            IsTotallyGeodesicFinite g Z → ∀ T ∈ Icc 0 L,
              (∀ t ∈ Icc 0 T, (g.geodesicFlow p t).proj ∈ Z) → w ∈ sliceTangent I Z p.proj →
                ∀ t ∈ Icc 0 T, ξ t ∈ sliceTangent I Z (g.geodesicFlow p t).proj := by
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hr1 : 1 ≤ r := one_le_two.trans hr2
  have hdom := g.geodesicFlowDomain_eq_univ hr2 hnorm
  have hmem : ∀ v : TangentBundle I M × ℝ, v ∈ g.geodesicFlowDomain := fun v => by
    rw [hdom]; exact mem_univ v
  obtain ⟨ρ, hρ, hb⟩ := exists_dist_transverseShift_le_of_parallel g hr2 hnorm hsec x L
  refine ⟨ρ, hρ, fun p hxp hp w hw hwp => ?_⟩
  obtain ⟨ξ, hξ0, hξpar, hξc, hξu⟩ := exists_parallel_unit_normal_geodesicFlow g hr1 hnorm p w hw hwp
  refine ⟨ξ, hξ0, hξpar, hξc, hξu, hb p hxp hp ξ hξpar fun t _ => (hξu t).1, ?_⟩
  intro k hk d Z hZ htg T hT hγ hwZ
  have hIcc : IsParallelAlongFinite g (fun t => (g.geodesicFlow p t).proj) ξ (Icc 0 T) := by
    rcases lt_or_ge 0 T with hT0 | hT0
    · refine (isParallelAlongFinite_geodesicFlow_iff hr1 (fun t _ => hmem _)
        (fun t ht => uniqueDiffOn_Icc hT0 t ht)).2 fun t _ q hq => ?_
      exact ((isParallelAlongFinite_geodesicFlow_iff hr1 (fun t _ => hmem _)
        (fun t _ => uniqueDiffWithinAt_univ)).1 hξpar t (mem_univ t) q hq).mono (subset_univ _)
    · have hT' : T = 0 := le_antisymm hT0 hT.1
      rw [hT']
      exact isParallelAlongFinite_Icc_self g _ _ 0
  refine isParallel_mem_sliceTangent_of_totallyGeodesic g hr2 hnorm hk hZ htg p le_rfl hT.1 hγ ξ
    hξc.continuousOn hIcc ?_
  rw [hξ0]
  exact hwZ

end Metric

end DifferentialGeometry.Geometry.FiniteSoul
