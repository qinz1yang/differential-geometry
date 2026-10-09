import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowField
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMonotone
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowInverse
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowGluing
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiskBundle

/-!
# LFR46 restated: the actual finite normal-flow map (lane CMS3-FLOW2, G2)

Blueprint LFR46 (A:28884–28973), frozen as `exists_finite_normalFlowMap` in
`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` §11 and RESTATED by disposition D1 of the
external review (`docs/geometrization/chapter13/out/review-finite-soul-three.md` §12): the frozen form
is false for a degenerate base map (flat `S¹ × ℝ²`, `b(t) = (t − sin(2πt)/(2π), 0)`, see
`NormalFlowRegression`). The restated statement

* takes the BASE inverse contract `hbinv` (so `b` is an embedding);
* uses the SAME normal tube `(ε, ψ)` as S3-TUBE / LFR45 (its clauses are hypotheses), with
  `ℓ + δ < ε` and `δ < ℓ/3`;
* has a profile positive on the outward zone `[ℓ/3, ∞)` and `1` on the seam;
* exhibits the actual hitting time and inverse map (LFR46.3):
  `ι (e⁻¹ x) = ψ x` for `d_S x ≤ ℓ`; for `d_S x ≥ ℓ` the S-HIT hitting time `τ x ≤ 0` of level `ℓ`
  and `e⁻¹ x = ((ℓ − τ x)/ℓ) · e⁻¹(φ_{τ x} x)`, with `τ` of class `C^(r−2)` on `{d_S > ℓ}`.

The field, its flow and the map are ONE choice (`ℓ = ε/2`, `δ = ε/8`): the field is
`exists_normalFlowField`, the flow is S-FLOW, the map is the finite-order radial gluing of the tube
`Φ = exp ∘ ι` (`exists_normalTube_partialDiffeomorph`) and the flow. On the seam the radial normal
geodesics are integral curves of the field (`tubeGradField_radial`), so the two formulas agree on an
open overlap by ODE uniqueness.

Deviations from the frozen hypothesis list (all forced by the restatement or by the unused-argument
linter): `+ hbinv`, `+` the tube `(ε, ψ)` with its clauses; `− [NoncompactSpace M]`,
`− [ConnectedSpace M]`, `− [CompactSpace B]`, `− [T2Space B]` (not used); `b` of class `C^(r−1)` is
not assumed (it follows from `ι` along the zero section).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
  [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]
  [TopologicalSpace B] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- `ι` is fibrewise linear: `ι(s, a w) = (b s, a · ι(s, w))`. -/
theorem iota_smul_tube (ι : TotalSpace F V → TangentBundle I M) {b : B → M}
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (s : B) (a : ℝ) (w : V s) :
    ι ⟨s, a • w⟩ = (⟨b s, a • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M) := by
  obtain ⟨A, hA⟩ := hιlin s
  rw [← mk_snd_eq_of_proj_eq_tube (ι ⟨s, a • w⟩) (hιb _)]
  congr 1
  change (ι ⟨s, a • w⟩).snd = a • (ι ⟨s, w⟩).snd
  rw [hA, hA, map_smul]
  rfl

omit [FiniteDimensional ℝ EB] [IsManifold 𝓘(ℝ, EB) ∞ B] in
/-- **LFR46, restated (D1)** (`3 ≤ r`; ledger: `X`, `φ`, `e`, `τ` of class `C^(r−2)`). -/
theorem exists_finite_normalFlowMap_tube [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty)
    (hout : ∀ q ∉ S, ∃ v : E, g.inner q v v = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q v u < 0)
    {ε : ℝ} (hε : 0 < ε) (ψ : M → TangentBundle I M)
    (hψs : ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε})
    (hψ : ∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
      Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S)
    (hψexp : ∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd))
    (hdS : ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
      {x | 0 < infDist x S ∧ infDist x S < ε})
    (b : B → M) (hbinj : Injective b) (hbS : range b = S)
    (hbinv : ∃ R : M → B, (∀ s, R (b s) = s) ∧
      ∀ x ∈ S, ContMDiffAt I 𝓘(ℝ, EB) ((r - 1 : ℕ∞) : ℕ∞ω) R x)
    (ι : TotalSpace F V → TangentBundle I M)
    (hι : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ι)
    (hιb : ∀ z, (ι z).proj = b z.proj)
    (hιlin : ∀ s : B, ∃ A : V s →L[ℝ] E, ∀ w : V s, @Eq E (ι ⟨s, w⟩).snd (A w))
    (hιnorm : ∀ z : TotalSpace F V, g.inner (ι z).proj (ι z).snd (ι z).snd = ‖z.2‖ ^ 2)
    (hιν : ∀ z, ι z ∈ normalSetFinite g S)
    (hιonto : ∀ v ∈ normalSetFinite g S, ∃ z, ι z = v) (p : M) :
    ∃ (X : (x : M) → TangentSpace I x) (φ : ℝ → M → M) (ℓ A₂ δ : ℝ) (prof : ℝ → ℝ),
      0 < ℓ ∧ 0 < A₂ ∧ 0 < δ ∧ δ < ℓ / 3 ∧ ℓ + δ < ε ∧
      ContMDiff I I.tangent ((r - 2 : ℕ∞) : ℕ∞ω) (fun x => (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, g.inner x (X x) (X x) ≤ 4) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ((r - 2 : ℕ∞) : ℕ∞ω) (fun q : ℝ × M => φ q.1 q.2) ∧
      (∀ x, φ 0 x = x) ∧ (∀ s t x, φ (s + t) x = φ s (φ t x)) ∧
      (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (φ t x)))) ∧
      (∀ q, A₂ ≤ dist p q → ∀ u ∈ g.finiteMinimizingDirectionsTo {p} q,
        g.inner q (X q) u ≤ -(1 / 4)) ∧
      (∀ q, ℓ / 3 ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q, g.inner q (X q) u < 0) ∧
      (∀ q, ℓ - δ < infDist q S → infDist q S < ℓ + δ →
        HasMFDerivAt I 𝓘(ℝ, ℝ) (fun y => infDist y S) q (g.inner q (X q))) ∧
      ContDiff ℝ ∞ prof ∧ (∀ τ ≤ δ, prof τ = 0) ∧ (∀ τ, ℓ - δ ≤ τ → prof τ = 1) ∧
      (∀ τ, ℓ / 3 ≤ τ → 0 < prof τ) ∧
      (∀ x ∈ S, X x = 0) ∧
      ∃ e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I⟯ M,
        (∀ s : B, e ⟨s, 0⟩ = b s) ∧
        (∀ z : TotalSpace F V, ‖z.2‖ ≤ ℓ → e z = g.expMap (ι z)) ∧
        (∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ t : ℝ, ℓ < t → e ⟨s, t • w⟩ = φ (t - ℓ) (e ⟨s, ℓ • w⟩)) ∧
        (∀ (s : B) (w : V s), ‖w‖ = 1 → ∀ τ : ℝ, 0 < τ → ∃ Y : TangentSpace I (e ⟨s, τ • w⟩),
          HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e ⟨s, t • w⟩) τ ((1 : ℝ →L[ℝ] ℝ).smulRight Y) ∧
            X (e ⟨s, τ • w⟩) = prof τ • Y) ∧
        (∀ x, infDist x S ≤ ℓ → ι (e.symm x) = ψ x) ∧
        (∀ x, ℓ ≤ infDist x S →
          hittingTime φ (fun y => infDist y S) x ℓ ≤ 0 ∧
          infDist (φ (hittingTime φ (fun y => infDist y S) x ℓ) x) S = ℓ ∧
          e.symm x = (⟨(e.symm (φ (hittingTime φ (fun y => infDist y S) x ℓ) x)).proj,
            ((ℓ - hittingTime φ (fun y => infDist y S) x ℓ) / ℓ) •
              (e.symm (φ (hittingTime φ (fun y => infDist y S) x ℓ) x)).2⟩ : TotalSpace F V)) ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 2 : ℕ∞) : ℕ∞ω)
          (fun x => hittingTime φ (fun y => infDist y S) x ℓ) {x | ℓ < infDist x S} := by
  classical
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  set n1 : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hn1
  set n2 : ℕ∞ω := ((r - 2 : ℕ∞) : ℕ∞ω) with hn2
  have h21 : n2 ≤ n1 := by
    rw [hn1, hn2]
    exact_mod_cast tsub_le_tsub_left (by norm_num : (1 : ℕ∞) ≤ 2) r
  have h1r2 : (1 : ℕ∞) ≤ r - 2 := by
    induction r using ENat.recTopCoe with
    | top => simp
    | coe k =>
      have : (3 : ℕ) ≤ k := by exact_mod_cast hr
      have h3 : ((k - 2 : ℕ) : ℕ∞) = (k : ℕ∞) - 2 := by simp
      rw [← h3]
      exact_mod_cast (by omega : 1 ≤ k - 2)
  have h1n2 : (1 : ℕ∞ω) ≤ n2 := by rw [hn2]; exact_mod_cast h1r2
  have hdc : Continuous (fun x => infDist x S) := continuous_infDist_pt S
  -- the field (`ℓ = ε/2`, `δ = ε/8`)
  obtain ⟨X, A₂, prof, hA₂, hXs, hX4, hXp, hXout, hXin, hX0, hprofC, hprof0, hprof1, hprofpos,
    -⟩ := exists_normalFlowField g hr2 hnorm hsec hSc hSne hout hε hψs hψ hψexp hdS p
  have hXs2 : ContMDiff I I.tangent n2 (fun x => (⟨x, X x⟩ : TangentBundle I M)) := hXs.of_le h21
  have hXc : Continuous (fun x => (⟨x, X x⟩ : TangentBundle I M)) := hXs.continuous
  -- the flow
  obtain ⟨φ, hφs, hφ0, hφadd, hφder, -, -⟩ := exists_complete_flow_of_bounded_ENat g hnorm
    (n := r - 2) h1r2 X hXs2 (B := 2) (fun x => by have := hX4 x; norm_num; linarith)
  have hφc : Continuous (fun q : ℝ × M => φ q.1 q.2) := hφs.continuous
  -- the seam: the field is the gradient there
  set G : (x : M) → TangentSpace I x := tubeGradField g S ψ with hGdef
  have hseam : ∀ q, 3 * ε / 8 ≤ infDist q S → infDist q S ≤ 5 * ε / 8 → X q = G q := by
    intro q h1 h2
    rw [hXin q (by linarith) h2, hprof1 _ h1, one_smul]
  have hout6 : ∀ q, ε / 6 ≤ infDist q S → ∀ u ∈ g.finiteMinimizingDirectionsTo S q,
      g.inner q (X q) u < 0 := hXout
  have hε6 : 0 < ε / 6 := by positivity
  -- the tube as a partial diffeomorphism, weakened to order `r − 2`
  obtain ⟨Φ₁, hΦsrc, hΦtgt, hΦfun, hΦinv, hΦrad⟩ := exists_normalTube_partialDiffeomorph g hr2
    hnorm hSne hψs hψ hψexp b hbinj hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto
  let Φ : PartialDiffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I (TotalSpace F V) M n2 :=
    { toPartialEquiv := Φ₁.toPartialEquiv
      open_source := Φ₁.open_source
      open_target := Φ₁.open_target
      contMDiffOn_toFun := Φ₁.contMDiffOn_toFun.of_le h21
      contMDiffOn_invFun := Φ₁.contMDiffOn_invFun.of_le h21 }
  -- the fibre length and the scaling
  set L : TotalSpace F V → ℝ := fun z => ‖z.2‖ with hLdef
  have hQ : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞
      (fun z : TotalSpace F V => ⟪z.2, z.2⟫_ℝ) := contMDiff_id.inner_bundle contMDiff_id
  have hLsq : L = fun z => Real.sqrt ⟪z.2, z.2⟫_ℝ := by
    funext z
    simp only [hLdef]
    rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have hLc : Continuous L := by rw [hLsq]; exact hQ.continuous.sqrt
  have hLs : ∀ z, 0 < L z → ContMDiffAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) n2 L z := by
    intro z hz
    have hpos : ⟪z.2, z.2⟫_ℝ ≠ 0 := by
      rw [real_inner_self_eq_norm_sq]
      exact (pow_pos hz 2).ne'
    rw [hLsq]
    exact ContDiffAt.comp_contMDiffAt (f := fun z : TotalSpace F V => ⟪z.2, z.2⟫_ℝ)
      (Real.contDiffAt_sqrt hpos) ((hQ z).of_le (WithTop.coe_le_coe.mpr le_top))
  set scale : ℝ → TotalSpace F V → TotalSpace F V := fun a z => ⟨z.proj, a • z.2⟩ with hscaledef
  have hscale : ContMDiff (𝓘(ℝ, ℝ).prod (𝓘(ℝ, EB).prod 𝓘(ℝ, F))) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) n2
      (fun z : ℝ × TotalSpace F V => scale z.1 z.2) :=
    DifferentialGeometry.Geometry.Collapse.contMDiff_totalSpace_smul.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hone : ∀ z, scale 1 z = z := fun z => by simp only [hscaledef, one_smul]
  have hmul : ∀ a c z, scale a (scale c z) = scale (a * c) z := fun a c z => by
    simp only [hscaledef, smul_smul]
  have hlength : ∀ a, 0 ≤ a → ∀ z, L (scale a z) = a * L z := fun a ha z => by
    simp only [hLdef, hscaledef, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  -- radial normal rays through `Φ`
  have hΦray : ∀ (s : B) (w : V s) (a : ℝ), Φ ⟨s, a • w⟩ =
      g.expMap (⟨b s, a • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M) := fun s w a => by
    change Φ₁ ⟨s, a • w⟩ = _
    rw [hΦfun, iota_smul_tube ι hιb hιlin]
  have hunit : ∀ (s : B) (w : V s), ‖w‖ = 1 →
      (⟨b s, (ι ⟨s, w⟩).snd⟩ : TangentBundle I M) ∈ normalSetFinite g S ∧
        g.inner (b s) (ι ⟨s, w⟩).snd (ι ⟨s, w⟩).snd = 1 := fun s w hw => by
    refine ⟨?_, ?_⟩
    · rw [mk_snd_eq_of_proj_eq_tube (ι ⟨s, w⟩) (hιb _)]
      exact hιν _
    · exact (inner_congr_base_tube g (hιb ⟨s, w⟩) _ _).symm.trans ((hιnorm ⟨s, w⟩).trans
        (by change ‖w‖ ^ 2 = 1; rw [hw, one_pow]))
  -- ODE uniqueness on the seam
  have hX1 : ContMDiff I I.tangent 1 (fun x => (⟨x, X x⟩ : TangentBundle I M)) :=
    hXs2.of_le h1n2
  have hseamflow : ∀ (s₀ : M) (u : TangentSpace I s₀),
      (⟨s₀, u⟩ : TangentBundle I M) ∈ normalSetFinite g S → g.inner s₀ u u = 1 →
      ∀ t ∈ Ioo (3 * ε / 8) (5 * ε / 8),
        g.expMap (⟨s₀, t • u⟩ : TangentBundle I M) =
          φ (t - ε / 2) (g.expMap (⟨s₀, (ε / 2) • u⟩ : TangentBundle I M)) := by
    intro s₀ u hu hu1 t ht
    set c : ℝ → M := fun τ => g.expMap (⟨s₀, τ • u⟩ : TangentBundle I M) with hc
    have hcurve : IsMIntegralCurveOn c X (Ioo (3 * ε / 8) (5 * ε / 8)) := by
      intro τ hτ
      have hτ0 : 0 < τ := by linarith [hτ.1]
      have hτε : τ < ε := by linarith [hτ.2]
      obtain ⟨hd, -, -, hder⟩ := tubeGradField_radial g hr2 hnorm hψexp hu hu1 hτ0 hτε
      have hXc' : X (c τ) = G (c τ) := hseam _ (by rw [hd]; exact hτ.1.le) (by rw [hd]; exact hτ.2.le)
      have h' : HasMFDerivAt 𝓘(ℝ, ℝ) I c τ ((1 : ℝ →L[ℝ] ℝ).smulRight (X (c τ))) := by
        rw [hXc']
        exact hder
      exact h'.hasMFDerivWithinAt
    set y₀ := φ (-(ε / 2)) (c (ε / 2)) with hy₀
    have hflow : IsMIntegralCurveOn (fun τ => φ τ y₀) X (Ioo (3 * ε / 8) (5 * ε / 8)) :=
      fun τ _ => (hφder τ y₀).hasMFDerivWithinAt
    have hℓmem : ε / 2 ∈ Ioo (3 * ε / 8) (5 * ε / 8) := ⟨by linarith, by linarith⟩
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hℓmem hX1 hcurve hflow
      (by
        change c (ε / 2) = φ (ε / 2) (φ (-(ε / 2)) (c (ε / 2)))
        rw [← hφadd, add_neg_cancel, hφ0])
    have h := heq ht
    change c t = φ t (φ (-(ε / 2)) (c (ε / 2))) at h
    change c t = φ (t - ε / 2) (c (ε / 2))
    rw [h, ← hφadd, sub_eq_add_neg]
  have hrad : ∀ z, ε / 2 - ε / 8 < L z → L z < ε / 2 + ε / 8 →
      φ (L z - ε / 2) (Φ (scale (ε / 2 / L z) z)) = Φ z := by
    rintro ⟨s, w⟩ h1 h2
    change ε / 2 - ε / 8 < ‖w‖ at h1
    change ‖w‖ < ε / 2 + ε / 8 at h2
    change φ (‖w‖ - ε / 2) (Φ ⟨s, (ε / 2 / ‖w‖) • w⟩) = Φ ⟨s, w⟩
    have hw0 : 0 < ‖w‖ := by linarith
    set w₁ : V s := ‖w‖⁻¹ • w with hw₁
    have hw₁n : ‖w₁‖ = 1 := by
      rw [hw₁, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw0.ne']
    have hwrep : w = ‖w‖ • w₁ := by rw [hw₁, smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
    have hw2 : (ε / 2 / ‖w‖) • w = (ε / 2) • w₁ := by
      rw [hw₁, smul_smul, div_eq_mul_inv]
    rw [hw2]
    conv_rhs => rw [hwrep]
    rw [hΦray, hΦray]
    obtain ⟨hn, hu1⟩ := hunit s w₁ hw₁n
    exact (hseamflow (b s) _ hn hu1 ‖w‖ ⟨by linarith, by linarith⟩).symm
  -- monotonicity and crossings
  have hinc : ∀ q, ε / 2 ≤ infDist q S → ∀ t : ℝ, 0 < t →
      infDist q S < infDist (φ t q) S := by
    intro q hq t ht
    have h := infDist_flow_lt_of_le g hr2 hnorm hSc hSne X hXc hφc hφ0 hφadd hφder hε6 hout6 q
      (t₀ := 0) (t := t) (by rw [hφ0]; linarith) ht
    rwa [hφ0] at h
  have hcross : ∀ q, ε / 2 ≤ infDist q S → ∃! t : ℝ, infDist (φ t q) S = ε / 2 :=
    fun q hq => existsUnique_flow_infDist_eq g hr2 hnorm hSc hSne X hXc hφc hφ0 hφadd hφder hε6
      hout6 (by linarith) hq
  -- the gluing
  obtain ⟨e, he, heinner, heouter, hτreg⟩ := exists_radial_gluing_diffeomorph_ofOrder L hLc hLs
    scale hscale hone hmul hlength (fun x => infDist x S) hdc (ε := ε) (ℓ := ε / 2) (δ := ε / 8)
    (by positivity) (by positivity) (by linarith) (by linarith) Φ hΦsrc hΦtgt
    (fun z hz => hΦrad z hz) φ hφs hφ0 hφadd hinc hcross hrad
  have hcrossτ : ∀ x, ε / 2 ≤ infDist x S →
      infDist (φ (hittingTime φ (fun y => infDist y S) x (ε / 2)) x) S = ε / 2 := by
    intro x hx
    obtain ⟨t, ht, -⟩ := hcross x hx
    rw [hittingTime_eq_of_infDist_eq g hr2 hnorm hSc hSne X hXc hφc hφ0 hφadd hφder hε6 hout6
      (by linarith) hx ht]
    exact ht
  have heΦ : ∀ z, L z < ε / 2 + ε / 8 → e z = Φ z := by
    intro z hz
    rw [he z]
    split_ifs with h
    · rfl
    · exact hrad z (by linarith [lt_of_not_ge h]) hz
  refine ⟨X, φ, ε / 2, A₂, ε / 8, prof, by positivity, hA₂, by positivity, by linarith,
    by linarith, hXs2, hX4, hφs, hφ0, hφadd, hφder, hXp, fun q hq u hu => hXout q (by linarith) u hu,
    fun q h1 h2 => ?_, hprofC, fun τ hτ => hprof0 τ hτ, fun τ hτ => hprof1 τ (by linarith),
    fun τ hτ => hprofpos τ (by linarith), fun x hx => hX0 x (by rw [infDist_zero_of_mem hx]; positivity),
    e, fun s => ?_, fun z hz => ?_, fun s w hw t ht => ?_, fun s w hw τ hτ => ?_, fun x hx => ?_,
    fun x hx => ?_, ?_⟩
  · -- the gradient clause on the seam
    have hq0 : 0 < infDist q S := by linarith
    have hqε : infDist q S < ε := by linarith
    rw [hseam q (by linarith) (by linarith)]
    exact hasMFDerivAt_infDist_tubeGradField g hr2 hnorm hψ hψexp hdS hq0 hqε
  · -- the zero section
    rw [heΦ _ (by change ‖(0 : V s)‖ < _; rw [norm_zero]; positivity)]
    have h0 : (⟨s, (0 : V s)⟩ : TotalSpace F V) = ⟨s, (0 : ℝ) • (0 : V s)⟩ := by rw [zero_smul]
    rw [h0, hΦray, zero_smul]
    exact g.expMap_zero hr1 (b s)
  · -- the inner formula
    rw [he z, ite_eq_left hz]
    exact hΦfun z
  · -- the ray formula
    have htw : L ⟨s, t • w⟩ = t := by
      change ‖t • w‖ = t
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hℓw : L ⟨s, (ε / 2) • w⟩ = ε / 2 := by
      change ‖(ε / 2) • w‖ = ε / 2
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [he, ite_eq_right (by rw [htw]; linarith), htw, he, ite_eq_left (by rw [hℓw])]
    congr 2
    change (⟨s, (ε / 2 / t) • t • w⟩ : TotalSpace F V) = ⟨s, (ε / 2) • w⟩
    rw [smul_smul, div_mul_cancel₀ _ (by linarith : t ≠ 0)]
  · -- the radial identification of the field
    obtain ⟨hn, hu1⟩ := hunit s w hw
    have hnorm_tw : ∀ t, 0 < t → L ⟨s, t • w⟩ = t := fun t ht => by
      change ‖t • w‖ = t
      rw [norm_smul, hw, mul_one, Real.norm_eq_abs, abs_of_pos ht]
    by_cases hτ5 : τ < ε / 2 + ε / 8
    · -- inside the tube the ray is the unit normal geodesic
      have hτε : τ < ε := by linarith
      obtain ⟨hd₀, -, -, hder⟩ := tubeGradField_radial g hr2 hnorm hψexp hn hu1 hτ hτε
      have hd : infDist (g.expMap (⟨b s, τ • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M)) S = τ := hd₀
      have hev : (fun t : ℝ => e ⟨s, t • w⟩) =ᶠ[𝓝 τ]
          fun t => g.expMap (⟨b s, t • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M) := by
        filter_upwards [Ioo_mem_nhds hτ hτ5] with t ht
        rw [heΦ _ (by rw [hnorm_tw t ht.1]; exact ht.2), hΦray]
      have hpt : e ⟨s, τ • w⟩ = g.expMap (⟨b s, τ • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M) :=
        hev.self_of_nhds
      refine ⟨G (g.expMap (⟨b s, τ • (ι ⟨s, w⟩).snd⟩ : TangentBundle I M)), ?_, ?_⟩
      · have h := hder.congr_of_eventuallyEq hev
        rw [hpt]
        exact h
      · rw [hpt, hXin _ (by rw [hd]; exact hτ) (by rw [hd]; linarith), hd]
    · -- outside, the ray is a flow line
      have hτℓ : ε / 2 < τ := by linarith
      have hev : (fun t : ℝ => e ⟨s, t • w⟩) =ᶠ[𝓝 τ]
          fun t => φ t (φ (-(ε / 2)) (e ⟨s, (ε / 2) • w⟩)) := by
        filter_upwards [Ioi_mem_nhds hτℓ] with t ht
        have ht' : ε / 2 < t := ht
        have htpos : 0 < t := lt_trans (by positivity) ht'
        have htw : L ⟨s, t • w⟩ = t := hnorm_tw t htpos
        have hℓw : L ⟨s, (ε / 2) • w⟩ = ε / 2 := hnorm_tw _ (by positivity)
        rw [← hφadd, he, ite_eq_right (by rw [htw]; exact not_le.mpr ht'), htw, he,
          ite_eq_left (by rw [hℓw])]
        have hsc : scale (ε / 2 / t) ⟨s, t • w⟩ = ⟨s, (ε / 2) • w⟩ := by
          change (⟨s, (ε / 2 / t) • t • w⟩ : TotalSpace F V) = ⟨s, (ε / 2) • w⟩
          rw [smul_smul, div_mul_cancel₀ _ htpos.ne']
        rw [hsc, show t + -(ε / 2) = t - ε / 2 by ring]
      have hpt : e ⟨s, τ • w⟩ = φ τ (φ (-(ε / 2)) (e ⟨s, (ε / 2) • w⟩)) := hev.self_of_nhds
      refine ⟨X (e ⟨s, τ • w⟩), ?_, ?_⟩
      · have h := (hφder τ (φ (-(ε / 2)) (e ⟨s, (ε / 2) • w⟩))).congr_of_eventuallyEq hev
        rw [hpt]
        exact h
      · rw [hprof1 τ (by linarith), one_smul]
  · -- the inner inverse
    rw [heinner x hx]
    exact hΦinv x (by linarith)
  · -- the outer inverse through the actual hitting time
    have hl := hcrossτ x hx
    obtain ⟨hτ0, hsymm⟩ := heouter x hx _ hl
    refine ⟨hτ0, hl, ?_⟩
    rw [hsymm, heinner _ hl.le]
  · -- regularity of the hitting time
    exact hτreg _ hcrossτ

end DifferentialGeometry.Geometry.FiniteSoul
