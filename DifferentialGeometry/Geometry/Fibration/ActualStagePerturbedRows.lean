import DifferentialGeometry.Geometry.Fibration.ActualStageStepApplications
import DifferentialGeometry.Geometry.Fibration.ActualStageSmooth
import DifferentialGeometry.Geometry.Metric.Cfs15StageOutput

/-!
# CFS17 on the actual stage clouds: projection estimates at a perturbed input (whole row)

Blueprint `master207B.tex`, CFS17 (`lem:fibration-perturbed-projection-estimate`, B:2944–3003).
The original cloud is the actual stage cloud `S_st = π_st𝓔⁰(A_st)` (`F = 𝓔⁰ = cgpGlobalMap`), the
radius `Σρ(sel x)` for any selection of preimages, `B = 5/3`; "CFS14 with accuracy `ε`" is a native
output `O : Cfs15StageOutput` on that cloud (its nearest map `P_j = O.ambient`); the adjustment is
`Ψ = adjustmentMap Q_st P_j ψ` (FC31's formula, `0 ≤ ψ ≤ 1`) and `g = Ψ ∘ f`.

* `cfs17_rank_CFSA` (generic, the rank clause): if `x = π_Q F(p) ∈ S`, the prior errors hold at `p`,
  `Π_x π_Q dF_p` is bounded below by `μ` (in the weight `N`, definite on `V`) on a subspace `V` of
  dimension `k`, and `ε(L₀ + H₀) + H₀ < μ`, then `π_Q f(p) ∈ Ω` and the derivative of
  `P_j ∘ π_Q ∘ f` at `p` is ONTO the tangent space `T W` of the native zero set at
  `P_j(π_Q f(p))`, which has dimension `k`.
* `cfs17_row_CFSA` (CFS17 on the actual stage clouds): value `|g − F| ≤ (E + a)ρ`,
  `a = (5/3)εΣ + (1 + ε)E`, derivative `‖dg − dF‖ ≤ ab(L₀ + H₀) + ε(L₀ + H₀) + ν + 2H₀` (pointwise
  along every tangent vector, weight `N`), and at a plateau point `ψ(f p) = 1` the rank clause.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open scoped ContDiff Manifold Topology
open GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners ℝ E' G} {M : Type*} [TopologicalSpace M] [ChartedSpace G M]

/-- The range of the derivative of a native output's ambient nearest map at a point of `Ω` is the
tangent space of the zero set at its nearest point, of dimension `k`. -/
theorem _root_.GC.MetricGeometry.Cfs15StageOutput.range_fderiv_ambient_CFSA {k K : ℕ} {ε cw : ℝ} {S T : Set H}
    {r : H → ℝ} {P : H → Submodule ℝ H} (O : Cfs15StageOutput k K ε cw S T r P) {y : H}
    (hy : y ∈ cfs15Omega_C15 S r) :
    let _ := O.cs
    LinearMap.range (fderiv ℝ O.ambient y).toLinearMap =
        actualZeroSetTangentSpace k O.Z (O.p ⟨y, hy⟩) ∧
      Module.finrank ℝ (actualZeroSetTangentSpace k O.Z (O.p ⟨y, hy⟩)) = k := by
  let _ := O.cs
  have := O.isManifold
  let A : (Fin k → ℝ) →L[ℝ] H :=
    mfderiv 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) (Subtype.val : O.Z → H) (O.p ⟨y, hy⟩)
  let B : H →L[ℝ] (Fin k → ℝ) := mfderiv 𝓘(ℝ, H) 𝓘(ℝ, Fin k → ℝ) O.p ⟨y, hy⟩
  have hchain : mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun z : cfs15Omega_C15 S r => (O.p z : H)) ⟨y, hy⟩ =
      A.comp B := by
    exact mfderiv_comp (⟨y, hy⟩ : cfs15Omega_C15 S r)
      (O.embedding.contMDiff.mdifferentiableAt (by simp))
      (O.p.contMDiff.mdifferentiableAt (by simp))
  have hBsurj : Function.Surjective B :=
    (DifferentialGeometry.Topology.Manifold.isSubmersionAt_iff_surjective_mfderiv
      O.p O.p.contMDiff ⟨y, hy⟩).mp (O.submersion.isSubmersionAt ⟨y, hy⟩)
  refine ⟨?_, ?_⟩
  · rw [O.ambient_fderiv hy, hchain]
    change LinearMap.range (A.toLinearMap.comp B.toLinearMap) = LinearMap.range A.toLinearMap
    exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hBsurj)
  · change Module.finrank ℝ (LinearMap.range A.toLinearMap) = k
    have hAinj : Function.Injective A :=
      O.embedding.isImmersion.mfderiv_injective (by simp) (O.p ⟨y, hy⟩)
    calc _ = Module.finrank ℝ (Fin k → ℝ) := LinearMap.finrank_range_of_inj hAinj
      _ = k := by simp

/-- **CFS17's rank clause** (generic). Let `x = π_Q F(p) ∈ S`, `E ≤ 3Σ/10`, `|f p − F p| ≤ Eρ(p)`,
`|df w| ≤ |dF w| + H₀N(w)` with `|dF w| ≤ L₀N(w)`, and let `Π_x π_Q dF_p` be bounded below by `μ`
on a subspace `V` of dimension `k` on which the weight `N` is definite. If
`ε(L₀ + H₀) + H₀ < μ`, then `y = π_Q f(p) ∈ Ω` and the derivative of `P_j ∘ π_Q ∘ f` at `p`
(`P_j = O.ambient`) has range EQUAL to the `k`-dimensional tangent space of `W` at `P_j(y)`. -/
theorem cfs17_rank_CFSA (Q : Submodule ℝ H) [Q.HasOrthogonalProjection] {k K : ℕ} {ε cw : ℝ}
    {S T : Set H} (sel : H → M) (ρ : M → ℝ) {sg : ℝ} {plane : H → Submodule ℝ H}
    (O : Cfs15StageOutput k K ε cw S T (fun x => sg * ρ (sel x)) plane)
    (F f : M → H) {p : M} {E L₀ H₀ μ : ℝ} (hsg : 0 < sg) (hE : E ≤ 3 * sg / 10) (hρp : 0 < ρ p)
    (hxS : Q.starProjection (F p) ∈ S)
    (hratio : ∀ x ∈ S, ∀ q, Q.starProjection (F q) = x →
      3 / 5 * ρ q ≤ ρ (sel x) ∧ ρ (sel x) ≤ 5 / 3 * ρ q)
    (hprior : ‖f p - F p‖ ≤ E * ρ p) (hf : MDifferentiableAt I 𝓘(ℝ, H) f p)
    (Nw : TangentSpace I p → ℝ)
    (hfirst : ∀ w, ‖mvfderiv I F p w‖ ≤ L₀ * Nw w)
    (hpriorD : ∀ w, ‖mvfderiv I f p w - mvfderiv I F p w‖ ≤ H₀ * Nw w)
    (V : Submodule ℝ (TangentSpace I p)) (hV : Module.finrank ℝ V = k)
    (hVpos : ∀ v ∈ V, v ≠ 0 → 0 < Nw v)
    (hVlow : ∀ v ∈ V, μ * Nw v ≤
      ‖(plane (Q.starProjection (F p))).starProjection (Q.starProjection (mvfderiv I F p v))‖)
    (hgap : ε * (L₀ + H₀) + H₀ < μ) :
    ∃ hy : Q.starProjection (f p) ∈ cfs15Omega_C15 S (fun x => sg * ρ (sel x)),
      let _ := O.cs
      LinearMap.range (mvfderiv I (fun q => O.ambient (Q.starProjection (f q))) p).toLinearMap =
          actualZeroSetTangentSpace k O.Z (O.p ⟨Q.starProjection (f p), hy⟩) ∧
        Module.finrank ℝ (actualZeroSetTangentSpace k O.Z (O.p ⟨Q.starProjection (f p), hy⟩)) = k := by
  have hyball := stage_step_mem_ball_GAF6 Q S sel ρ hsg hE F f hρp hxS hratio hprior
  have hyΩ := mem_cfs15Omega_of_mem_C15 (r := fun x => sg * ρ (sel x)) hxS hyball
  refine ⟨hyΩ, ?_⟩
  let _ := O.cs
  obtain ⟨hTS, hfin⟩ := O.range_fderiv_ambient_CFSA hyΩ
  have hvd := O.ambient_value_deriv hxS hyball
  have hε := O.eps_pos
  have hΨd : DifferentiableAt ℝ (fun z => O.ambient (Q.starProjection z)) (f p) :=
    hvd.2.1.comp (f p) Q.starProjection.differentiableAt
  have hDΨ : fderiv ℝ (fun z => O.ambient (Q.starProjection z)) (f p) =
      (fderiv ℝ O.ambient (Q.starProjection (f p))).comp Q.starProjection :=
    (hvd.2.1.hasFDerivAt.comp (f p) Q.starProjection.hasFDerivAt).fderiv
  have hchain : ∀ w, mvfderiv I (fun q => O.ambient (Q.starProjection (f q))) p w =
      fderiv ℝ O.ambient (Q.starProjection (f p)) (Q.starProjection (mvfderiv I f p w)) := by
    intro w
    have h := mvfderiv_comp_apply_of_differentiableAt_GAF3 (I := I) (f := f)
      (Ψ := fun z => O.ambient (Q.starProjection z)) hf hΨd w
    rw [hDΨ] at h
    exact h
  set Bm := mvfderiv I (fun q => O.ambient (Q.starProjection (f q))) p with hBm
  set Da := fderiv ℝ O.ambient (Q.starProjection (f p)) with hDa
  set Pxp := (plane (Q.starProjection (F p))).starProjection with hPxp
  -- `range Bm ≤ range Da`
  have hle : LinearMap.range Bm.toLinearMap ≤ LinearMap.range Da.toLinearMap := by
    rintro _ ⟨w, rfl⟩
    exact ⟨Q.starProjection (mvfderiv I f p w), (hchain w).symm⟩
  -- injectivity on `V`
  have hinj : ∀ v ∈ V, Bm v = 0 → v = 0 := by
    intro v hv hBv
    by_contra hne
    have hpos := hVpos v hv hne
    have hdiff : Bm v - Pxp (Q.starProjection (mvfderiv I F p v)) =
        (Da - Pxp) (Q.starProjection (mvfderiv I f p v)) +
          Pxp (Q.starProjection (mvfderiv I f p v - mvfderiv I F p v)) := by
      rw [hchain v]
      simp only [sub_apply, map_sub]
      abel
    have h1 : ‖(Da - Pxp) (Q.starProjection (mvfderiv I f p v))‖ ≤
        ε * ‖mvfderiv I f p v‖ :=
      ((Da - Pxp).le_opNorm _).trans (mul_le_mul hvd.2.2
        (Q.norm_starProjection_apply_le _) (norm_nonneg _) hε.le)
    have h2 : ‖Pxp (Q.starProjection (mvfderiv I f p v - mvfderiv I F p v))‖ ≤ H₀ * Nw v :=
      ((plane (Q.starProjection (F p))).norm_starProjection_apply_le _).trans
        ((Q.norm_starProjection_apply_le _).trans (hpriorD v))
    have h3 : ‖mvfderiv I f p v‖ ≤ (L₀ + H₀) * Nw v := by
      have h0 := norm_le_insert' (mvfderiv I f p v) (mvfderiv I F p v)
      have h4 := hfirst v
      have h5 := hpriorD v
      rw [add_mul]
      linarith
    have hlow := hVlow v hv
    have htri := norm_sub_le (Bm v) (Bm v - Pxp (Q.starProjection (mvfderiv I F p v)))
    rw [sub_sub_cancel, hdiff, hBv, norm_zero, zero_add] at htri
    have hadd := norm_add_le ((Da - Pxp) (Q.starProjection (mvfderiv I f p v)))
      (Pxp (Q.starProjection (mvfderiv I f p v - mvfderiv I F p v)))
    have hεb : ε * ‖mvfderiv I f p v‖ ≤ ε * ((L₀ + H₀) * Nw v) :=
      mul_le_mul_of_nonneg_left h3 hε.le
    have hgapN : (ε * (L₀ + H₀) + H₀) * Nw v < μ * Nw v := mul_lt_mul_of_pos_right hgap hpos
    have hexp : (ε * (L₀ + H₀) + H₀) * Nw v = ε * ((L₀ + H₀) * Nw v) + H₀ * Nw v := by ring
    linarith
  -- `finrank (range Bm) ≥ k`
  have hdom : Function.Injective (Bm.toLinearMap.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Subtype.ext (hinj v v.2 hv)
  have hk : k ≤ Module.finrank ℝ (LinearMap.range Bm.toLinearMap) := by
    rw [← hV, ← LinearMap.finrank_range_of_inj hdom]
    exact Submodule.finrank_mono (LinearMap.range_domRestrict_le_range _ _)
  have heq : LinearMap.range Bm.toLinearMap = LinearMap.range Da.toLinearMap :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hTS, hfin]; exact hk)
  exact ⟨heq.trans hTS, hfin⟩

end Generic

section Model

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- **CFS17 on the actual stage clouds** (B:2944). Original cloud `S_st` of `F = 𝓔⁰`, radius
`Σρ(sel x)` (any selection), `B = 5/3`; CFS14 at accuracy `ε` is a native output `O` (nearest map
`P = O.ambient`); `Ψ = adjustmentMap Q_st P ψ` with `0 ≤ ψ ≤ 1`, `g = Ψ ∘ f`. At an original point
`p` with `|f p − F p| ≤ Eρ(p)`, `E ≤ 3Σ/10`, `|dF w| ≤ L₀N(w)`, `|df w − dF w| ≤ H₀N(w)`, and — on the
closed support of `ψ` along `f` — `π_Q F(p) ∈ S_st`, `‖dψ‖ ≤ b/ρ(p)`, `‖(I − Π_x)π_Q dF w‖ ≤ νN(w)`:
`|g p − F p| ≤ (E + a)ρ(p)` with `a = (5/3)εΣ + (1 + ε)E`, and
`|dg w − dF w| ≤ (ab(L₀ + H₀) + ε(L₀ + H₀) + ν + 2H₀)N(w)`. At a plateau point `ψ(f p) = 1`, if
`Π_x π_Q dF_p` has lower bound `μ` on a `k_st`-dimensional `V` (weight definite on `V`) and
`ε(L₀ + H₀) + H₀ < μ`, then `d(P ∘ π_Q ∘ f)_p` is onto the tangent space of `W` at `P(π_Q f(p))`. -/
theorem cfs17_row_CFSA (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ) (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4)
    (st : Fin 3) (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {Kj : ℕ} {εa cw sg : ℝ} (hsg : 0 < sg)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (O : Cfs15StageOutput (gafStageDim st) Kj εa cw (gafCloud L Z st) (gafCloudEnlarged L Z st)
      (fun x => sg * ρ (sel x)) plane)
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1)
    (f : X → BlockSpace (fun _ : CGPTag L Z => ℝ²)) {E bc L₀ H₀ ν : ℝ}
    (hE0 : 0 ≤ E) (hE : E ≤ 3 * sg / 10) (hbc : 0 ≤ bc) (hL₀ : 0 ≤ L₀) (hH₀ : 0 ≤ H₀)
    (hν : 0 ≤ ν) (p : X)
    (hloc : f p ∈ tsupport ψ →
      (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st)
    (hprior : ‖f p - cgpGlobalMap L Z p‖ ≤ E * ρ p)
    (hf : MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag L Z => ℝ²)) f p)
    (hψd : f p ∈ tsupport ψ → DifferentiableAt ℝ ψ (f p) ∧ ‖fderiv ℝ ψ (f p)‖ ≤ bc / ρ p)
    (Nw : TangentSpace 𝓘(ℝ, E3) p → ℝ) (hN : ∀ w, 0 ≤ Nw w)
    (hfirst : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤ L₀ * Nw w)
    (hnormal : (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st → ∀ w,
      ‖(ContinuousLinearMap.id ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)) -
          (plane ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z p))).starProjection)
        ((gafStageQ L Z st).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w))‖ ≤
        ν * Nw w)
    (hpriorD : ∀ w, ‖mvfderiv 𝓘(ℝ, E3) f p w - mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤
      H₀ * Nw w) :
    ‖adjustmentMap (gafStageQ L Z st) O.ambient ψ (f p) - cgpGlobalMap L Z p‖ ≤
        (E + (5 / 3 * εa * sg + (1 + εa) * E)) * ρ p ∧
      (∀ w, ‖mvfderiv 𝓘(ℝ, E3) (adjustmentMap (gafStageQ L Z st) O.ambient ψ ∘ f) p w -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p w‖ ≤
        ((5 / 3 * εa * sg + (1 + εa) * E) * bc * (L₀ + H₀) + εa * (L₀ + H₀) + ν + 2 * H₀) *
          Nw w) ∧
      (ψ (f p) = 1 → ∀ (μ : ℝ) (V : Submodule ℝ (TangentSpace 𝓘(ℝ, E3) p)),
        Module.finrank ℝ V = gafStageDim st → (∀ v ∈ V, v ≠ 0 → 0 < Nw v) →
        (∀ v ∈ V, μ * Nw v ≤
          ‖(plane ((gafStageQ L Z st).starProjection (cgpGlobalMap L Z p))).starProjection
            ((gafStageQ L Z st).starProjection (mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap L Z) p v))‖) →
        εa * (L₀ + H₀) + H₀ < μ →
        ∃ hy : (gafStageQ L Z st).starProjection (f p) ∈
            cfs15Omega_C15 (gafCloud L Z st) (fun x => sg * ρ (sel x)),
          let _ := O.cs
          LinearMap.range (mvfderiv 𝓘(ℝ, E3)
              (fun q => O.ambient ((gafStageQ L Z st).starProjection (f q))) p).toLinearMap =
            actualZeroSetTangentSpace (gafStageDim st) O.Z
              (O.p ⟨(gafStageQ L Z st).starProjection (f p), hy⟩) ∧
          Module.finrank ℝ (actualZeroSetTangentSpace (gafStageDim st) O.Z
            (O.p ⟨(gafStageQ L Z st).starProjection (f p), hy⟩)) = gafStageDim st) := by
  have hεa := O.eps_pos
  have hpst : ∀ x ∈ gafCloud L Z st, ∀ z ∈ ball x (sg * ρ (sel x)),
      ‖O.ambient z - (x + (plane x).starProjection (z - x))‖ ≤ εa * (sg * ρ (sel x)) :=
    fun x hx z hz => (O.ambient_value_deriv hx hz).1
  have hpd : ∀ x ∈ gafCloud L Z st, ∀ z ∈ ball x (sg * ρ (sel x)),
      DifferentiableAt ℝ O.ambient z ∧ ‖fderiv ℝ O.ambient z - (plane x).starProjection‖ ≤ εa :=
    fun x hx z hz => (O.ambient_value_deriv hx hz).2
  refine ⟨gafStage_step_value_GAF5 L Z hΔ hΛ hsmall st sel hsel plane O.ambient ψ hψI hεa.le hsg
      hE0 hE hpst f p hloc hprior,
    (gafStage_step_deriv_GAF5 L Z hΔ hΛ hsmall st sel hsel plane O.ambient ψ hψI hεa.le hsg hE0
      hE hbc hL₀ hH₀ hν hpst hpd f p hloc hprior hf hψd Nw hN hfirst hnormal hpriorD).2, ?_⟩
  intro h1 μ' Vs hV hVpos hVlow hgap
  have hsupp : f p ∈ tsupport ψ :=
    subset_tsupport _ (by rw [Function.mem_support, h1]; exact one_ne_zero)
  exact cfs17_rank_CFSA (gafStageQ L Z st) sel ρ O (cgpGlobalMap L Z) f hsg hE (hρ p)
    (hloc hsupp) (gafCloud_preimage_ratio_two_GAF5 L Z hΔ hΛ hsmall st sel hsel) hprior hf Nw
    hfirst hpriorD Vs hV hVpos hVlow hgap

/-- **Consumer: the first adjustment** (`f = F = 𝓔⁰`, `E = H₀ = 0`): the stage map moves the original
point by at most `(5/3)εΣρ(p)` (CFS17's value bound with no preceding error). -/
theorem cfs17_unperturbed_value_CFSA (hΔ : 1 ≤ Δ) (hΛ : 0 ≤ Λ)
    (hsmall : Λ * (1000000 * Δ) ≤ 1 / 4) (st : Fin 3)
    (sel : BlockSpace (fun _ : CGPTag L Z => ℝ²) → X)
    (hsel : ∀ x ∈ gafCloudEnlarged L Z st, cgpProjMap L Z (gafStageTags L Z st) (sel x) = x)
    {Kj : ℕ} {εa cw sg : ℝ} (hsg : 0 < sg)
    (plane : BlockSpace (fun _ : CGPTag L Z => ℝ²) →
      Submodule ℝ (BlockSpace (fun _ : CGPTag L Z => ℝ²)))
    (O : Cfs15StageOutput (gafStageDim st) Kj εa cw (gafCloud L Z st) (gafCloudEnlarged L Z st)
      (fun x => sg * ρ (sel x)) plane)
    (ψ : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ) (hψI : ∀ y, ψ y ∈ Icc (0 : ℝ) 1) (p : X)
    (hloc : cgpGlobalMap L Z p ∈ tsupport ψ →
      (gafStageQ L Z st).starProjection (cgpGlobalMap L Z p) ∈ gafCloud L Z st) :
    ‖adjustmentMap (gafStageQ L Z st) O.ambient ψ (cgpGlobalMap L Z p) - cgpGlobalMap L Z p‖ ≤
      5 / 3 * εa * sg * ρ p := by
  have hεa := O.eps_pos
  have h := gafStage_step_value_GAF5 L Z hΔ hΛ hsmall st sel hsel plane O.ambient ψ hψI hεa.le hsg
    le_rfl (by positivity) (fun x hx z hz => (O.ambient_value_deriv hx hz).1)
    (cgpGlobalMap L Z) p hloc (by simp)
  have heq : (0 + (5 / 3 * εa * sg + (1 + εa) * 0)) * ρ p = 5 / 3 * εa * sg * ρ p := by ring
  rwa [heq] at h

end Model

end DifferentialGeometry.Geometry.Collapse
