import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.QuasiIsometry_S109
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TransferIsotopyFinal_S15

set_option autoImplicit false

/-! # CH12-S109 G3: speed of the backward isotopy `μ ↦ G μ p` and the assembly `hCX3ext_S109`

Differentiating `E_{clamp r} (G r p) = p` (with `clamp = id` near `[0,1]`) at `r = μ` gives
`dE_μ (∂_μ G) = -∂_t E_t q |_{t = μ}`, the velocity of the geodesic `t ↦ exp_q (t X q)`, whose `g`-speed
is `|X q|_g`; the QI lemma transports this back to `g_q (∂_μ G, ∂_μ G)`. -/

noncomputable section
open scoped Manifold ContDiff Topology ENNReal
open Set Function Bundle Filter Metric

namespace GC.LongTime.Ch12
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.Exponential DifferentialGeometry.Geometry.Hyperbolic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Partial
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- chain rule with partial derivatives: `d/dr F (r, c r) = ∂_t F + ∂_x F · c'`. -/
theorem mfderiv_partial_S109 (F : ℝ × M → M) (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ F)
    (c : ℝ → M) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (μ : ℝ) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun r => F (r, c r)) μ (1 : ℝ) : E) =
      (mfderiv 𝓘(ℝ, ℝ) I (fun t => F (t, c μ)) μ (1 : ℝ) : E) +
      (mfderiv I I (fun x => F (μ, x)) (c μ) (mfderiv 𝓘(ℝ, ℝ) I c μ (1 : ℝ)) : E) := by
  have hFd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I F (μ, c μ) := hF.mdifferentiableAt (by simp)
  have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) I c μ := hc.mdifferentiableAt (by simp)
  -- the graph map and its derivative
  have hg : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r : ℝ => (r, c r)) μ =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) μ).prod (mfderiv 𝓘(ℝ, ℝ) I c μ) :=
    mfderiv_prodMk mdifferentiableAt_id hcd
  have h1 : mfderiv 𝓘(ℝ, ℝ) I (fun r => F (r, c r)) μ =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I F (μ, c μ)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r : ℝ => (r, c r)) μ) :=
    mfderiv_comp μ hFd ((contMDiff_id.prodMk hc : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun r : ℝ => (r, c r))).mdifferentiableAt (by simp))
  -- the two slices
  have hι1 : mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun t : ℝ => (t, c μ)) μ =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (id : ℝ → ℝ) μ).prod (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => c μ) μ) :=
    mfderiv_prodMk mdifferentiableAt_id mdifferentiableAt_const
  have hι2 : mfderiv I (𝓘(ℝ, ℝ).prod I) (fun x : M => (μ, x)) (c μ) =
      (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => μ) (c μ)).prod (mfderiv I I (id : M → M) (c μ)) :=
    mfderiv_prodMk mdifferentiableAt_const mdifferentiableAt_id
  have hc1 : mfderiv 𝓘(ℝ, ℝ) I (fun t => F (t, c μ)) μ =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I F (μ, c μ)).comp
        (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun t : ℝ => (t, c μ)) μ) :=
    mfderiv_comp μ hFd ((contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) ∞
      (fun t : ℝ => (t, c μ))).mdifferentiableAt (by simp))
  have hc2 : mfderiv I I (fun x => F (μ, x)) (c μ) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I F (μ, c μ)).comp
        (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun x : M => (μ, x)) (c μ)) :=
    mfderiv_comp (c μ) hFd ((contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞
      (fun x : M => (μ, x))).mdifferentiableAt (by simp))
  set T := mfderiv (𝓘(ℝ, ℝ).prod I) I F (μ, c μ) with hT
  set v := mfderiv 𝓘(ℝ, ℝ) I c μ (1 : ℝ) with hv
  let a : TangentSpace (𝓘(ℝ, ℝ).prod I) (μ, c μ) := ((1 : ℝ), (0 : TangentSpace I (c μ)))
  let b : TangentSpace (𝓘(ℝ, ℝ).prod I) (μ, c μ) := ((0 : ℝ), v)
  have e1 : (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r : ℝ => (r, c r)) μ) (1 : ℝ) = a + b := by
    rw [hg, mfderiv_id]
    refine Prod.ext ?_ ?_
    · exact (add_zero (1 : ℝ)).symm
    · exact (zero_add v).symm
  have e2 : (mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun t : ℝ => (t, c μ)) μ) (1 : ℝ) = a := by
    rw [hι1, mfderiv_id]
    refine Prod.ext ?_ ?_
    · rfl
    · change (mfderiv 𝓘(ℝ, ℝ) I (fun _ : ℝ => c μ) μ) (1 : ℝ) = (0 : TangentSpace I (c μ))
      rw [mfderiv_const]; rfl
  have e3 : (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun x : M => (μ, x)) (c μ)) v = b := by
    rw [hι2, mfderiv_id]
    refine Prod.ext ?_ ?_
    · change (mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => μ) (c μ)) v = (0 : ℝ)
      rw [mfderiv_const]; rfl
    · rfl
  rw [h1, hc1, hc2]
  change T ((mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun r : ℝ => (r, c r)) μ) (1 : ℝ)) =
    T ((mfderiv 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod I) (fun t : ℝ => (t, c μ)) μ) (1 : ℝ)) +
      T ((mfderiv I (𝓘(ℝ, ℝ).prod I) (fun x : M => (μ, x)) (c μ)) v)
  rw [e1, e2, e3]
  exact T.map_add a b

end Partial

section Speed
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold 𝓘(ℝ, E) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)] [LocallyCompactSpace M]

variable (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hEnorm : IsMetricNorm g)

/-- **Speed bound.**  If `E_μ = exp(μ X)` satisfies the QI inequality with constant `K ≥ 0` and
`X` has pointwise `g`-length `< ε`, the backward isotopy `r ↦ G r p = Ψ r 0 p` (`G` the inverse
family of `E_{clamp r}`) has `g`-speed squared `≤ K ε²` at `μ ∈ [0,1]`. -/
theorem speed_bound_S109 (X : ∀ y : M, TangentSpace 𝓘(ℝ, E) y)
    (hX : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (secBundle_S15 X)) (G : ℝ → M → M)
    (hGs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × M => G q.1 q.2))
    (hG2 : ∀ μ y, scaledExp_S15 g hEnorm X (clamp_S102 μ) (G μ y) = y) {K : ℝ} (hK : 0 ≤ K)
    (hQI : ∀ μ : ℝ, |μ| ≤ 2 → ∀ (q : M) (w : TangentSpace 𝓘(ℝ, E) q),
      g.inner q w w ≤ K * g.inner (scaledExp_S15 g hEnorm X μ q)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q w)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q w))
    {ε : ℝ} (htan : ∀ q, tanLen_S15 g (secBundle_S15 X q) < ε) {μ : ℝ} (hμ : μ ∈ Icc (0 : ℝ) 1)
    (p : M) :
    let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => psi_S109 g hEnorm X G r 0 p) μ
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) μ).symm (1 : ℝ))
    g.inner (psi_S109 g hEnorm X G μ 0 p) v v ≤ K * ε ^ 2 := by
  intro v
  set q := G μ p with hq
  set F : ℝ × M → M := fun z => scaledExp_S15 g hEnorm X z.1 z.2 with hF
  have hFs : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ F :=
    contMDiff_scaledExp_S15 (J := 𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) g hEnorm
      (fun z : ℝ × M => secBundle_S15 X z.2) (fun z => z.1) (hX.comp contMDiff_snd) contMDiff_fst
  have hc : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r => G r p) :=
    hGs.comp (contMDiff_id.prodMk contMDiff_const)
  have hfun : (fun r => psi_S109 g hEnorm X G r 0 p) = fun r => G r p :=
    funext fun r => psi_zero_right_S109 g hEnorm X G r p
  -- `v = d/dr (G r p)` as an element of `E`
  set dv : TangentSpace 𝓘(ℝ, E) q := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => G r p) μ (1 : ℝ) with hdv
  have hvdv : (v : E) = (dv : E) := by
    have := congrArg (fun f : ℝ → M => (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) f μ (1 : ℝ) : E)) hfun
    exact this
  -- differentiate `F (r, G r p) = p`
  have hev : (fun r => F (r, G r p)) =ᶠ[𝓝 μ] fun _ => p := by
    filter_upwards [clamp_eventuallyEq_id_S102 hμ] with r hr
    have h := hG2 r p
    have hr' : clamp_S102 r = r := hr
    rw [hr'] at h
    exact h
  have h0 : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r => F (r, G r p)) μ (1 : ℝ) : E) = 0 := by
    rw [hev.mfderiv_eq, mfderiv_const]; rfl
  have hpart := mfderiv_partial_S109 F hFs (fun r => G r p) hc μ
  rw [h0] at hpart
  have hu : (fun t => F (t, G μ p)) = intrinsicGeodesic g hEnorm q (X q) :=
    funext fun t => scaledExp_eq_geodesic_S15 g hEnorm X t q
  set u : TangentSpace 𝓘(ℝ, E) (intrinsicGeodesic g hEnorm q (X q) μ) :=
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (intrinsicGeodesic g hEnorm q (X q)) μ (1 : ℝ) with hu_def
  have hpart' : (id u : E) +
      (id (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv) : E) = 0 := by
    rw [hu_def, ← hu]
    exact hpart.symm
  have hdE : (id (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv) : E) = -(id u : E) :=
    eq_neg_of_add_eq_zero_right hpart'
  have hnorm2 : g.inner (scaledExp_S15 g hEnorm X μ q)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv) = g.inner q (X q) (X q) := by
    have h1 : g.inner (scaledExp_S15 g hEnorm X μ q)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (scaledExp_S15 g hEnorm X μ) q dv) =
        g.inner (intrinsicGeodesic g hEnorm q (X q) μ) (-(id u : E)) (-(id u : E)) :=
      congrArg₂ (fun (x : M) (w : E) => g.inner x w w) (scaledExp_eq_geodesic_S15 g hEnorm X μ q) hdE
    have h2 : g.inner (intrinsicGeodesic g hEnorm q (X q) μ) (-u) (-u) =
        g.inner (intrinsicGeodesic g hEnorm q (X q) μ) u u := by simp
    refine h1.trans (Eq.trans ?_ (h2.trans (intrinsicGeodesic_speedSq_eq g hEnorm q (X q) μ)))
    rfl
  have hgoal : g.inner (psi_S109 g hEnorm X G μ 0 p) v v = g.inner q dv dv :=
    congrArg₂ (fun (x : M) (w : E) => g.inner x w w) (psi_zero_right_S109 g hEnorm X G μ p) hvdv
  rw [hgoal]
  have hμ2 : |μ| ≤ 2 := abs_le.mpr ⟨by linarith [hμ.1], by linarith [hμ.2]⟩
  refine (hQI μ hμ2 q dv).trans ?_
  rw [hnorm2]
  have h0' : 0 ≤ g.inner q (X q) (X q) := by
    by_cases hz : X q = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  have hsq : g.inner q (X q) (X q) = tanLen_S15 g (secBundle_S15 X q) ^ 2 :=
    (Real.sq_sqrt h0').symm
  rw [hsq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) (htan q).le 2) hK

end Speed

end GC.LongTime.Ch12
