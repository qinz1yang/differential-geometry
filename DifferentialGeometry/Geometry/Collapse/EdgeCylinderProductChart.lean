import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrierNoncompact

/-!
# LFR28 R5: the product chart `Θ = Ψ ∘ (id × φ) : ℝ × S → N` of the model

Blueprint 207A, LFR28 (A:27223), proof step 1: "LFR14–LFR16 give a complete nonnegative product
`N = ℝ × Z`, with `Z` an oriented `C^{K-1}` surface". On the exact splitting `e : N ≃ᵢ ℓ²(ℝ × W)` of
the limit, the product map `Ψ = splittingProductDiffeomorph` (`C^{k+2}`, `ℝ × Z → N`) composed with
the smooth carrier `φ : S ≃ Z` of lane LFR28-B12 (B2,
`surfaceFactor_smoothCarrier(_oriented)_noncompact`) is the chart of the model cylinder:

* `exists_edgeCylinderProductChart`: `Θ` is a `C^{k+2}` diffeomorphism
  `ℝ × S → N` for the model `𝓘(ℝ, ℝ).prod (𝓡 2)`, `e (Θ (t, s)) = (t, (e (φ s)).snd)` (so `Θ`
  carries the time `t` and the surface point to the splitting coordinates), and the pullback
  identity `Θ^*G = dt² + κ` for the carrier metric `κ = φ^* h`. These are exactly the hypotheses
  `he` (with `ψ s = (e (φ s)).snd`) and `hpull` of R1
  (build-logs/scratch/F7-LFR28C/R12Targets.lean), and `Θ` is the `Θ` of B3
  (`exists_edgeCylinder_source_partialDiffeomorph`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance edgeCylinderProductChart_nezero_finrank :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **LFR28 R5.** The product chart `Θ = Ψ ∘ (id × φ)`: a `C^{k+2}` diffeomorphism `ℝ × S → N` with
`e ∘ Θ = (t, (e ∘ φ).snd)` and `Θ^*G = dt² + κ`. -/
theorem exists_edgeCylinderProductChart {N W S : Type} [MetricSpace N] [ChartedSpace E3 N]
    [IsManifold 𝓘(ℝ, E3) ∞ N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
    [IsRiemannianManifold 𝓘(ℝ, E3) N] [CompleteSpace N] [ConnectedSpace N] [MetricSpace W]
    [TopologicalSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S] {k : ℕ}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hk : 2 ≤ (k : ℕ∞))
    (hnorm : ∀ (x : N) (v : TangentSpace 𝓘(ℝ, E3) x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x v v)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (e : N ≃ᵢ WithLp 2 (ℝ × W)) :
    letI := splittingFactorChartedSpace G hk hnorm e
    letI := splittingFactor_isManifold_one G hk hnorm e
    ∀ (φ : S ≃ₜ {x : N // (e x).fst = 0}),
      ContMDiff (𝓡 2) 𝓘(ℝ, P) ((k + 2 : ℕ) : ℕ∞ω) φ →
      ContMDiff 𝓘(ℝ, P) (𝓡 2) ((k + 2 : ℕ) : ℕ∞ω) φ.symm →
      ∀ {n : ℕ∞ω} (κ : ContMDiffRiemannianMetric (𝓡 2) n E2 (TangentSpace (𝓡 2) : S → Type _)),
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x),
        κ.inner x v w = (inducedMetric G hk hnorm e).inner (φ x)
          (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x v) (mfderiv (𝓡 2) 𝓘(ℝ, P) φ x w)) →
      ∃ Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N ((k + 2 : ℕ) : ℕ∞ω),
        (∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, (e (φ p.2 : N)).snd)) ∧
        ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
          G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2 := by
  let _ := splittingFactorChartedSpace G hk hnorm e
  let _ := splittingFactor_isManifold_one G hk hnorm e
  intro φ hφ hφs n κ hκ
  rcases surfaceFactor_of_exactSplitting_noncompact G hk hnorm hsec e with
    ⟨-, -, -, -, -, -, hΨ, hΨs, hpullΨ⟩
  set Ψ := splittingProductDiffeomorph G hk hnorm e with hΨdef
  have hn : (((k : ℕ∞) : ℕ∞ω) + 2) = ((k + 2 : ℕ) : ℕ∞ω) := withTop_natCast_add_two k
  replace hΨ := hΨ.of_le hn.symm.le
  replace hΨs := hΨs.of_le hn.symm.le
  let Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N ((k + 2 : ℕ) : ℕ∞ω) :=
    { toEquiv := (Equiv.prodCongr (Equiv.refl ℝ) φ.toEquiv).trans Ψ.toEquiv
      contMDiff_toFun := hΨ.comp (contMDiff_fst.prodMk (hφ.comp contMDiff_snd))
      contMDiff_invFun := (contMDiff_fst.comp hΨs).prodMk (hφs.comp (contMDiff_snd.comp hΨs)) }
  have hΘ : ∀ p : ℝ × S, Θ p = Ψ (p.1, φ p.2) := fun _ => rfl
  refine ⟨Θ, fun p => ?_, fun p v w => ?_⟩
  · rw [hΘ, hΨdef, splittingProductDiffeomorph_apply, splittingFactorProductEquiv_apply,
      IsometryEquiv.apply_symm_apply]
    rfl
  · -- the derivative of `Θ` through the product map
    have hk1 : ((k + 2 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
    have hφd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, P) φ p.2 := (hφ p.2).mdifferentiableAt hk1
    have hΨd : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) Ψ (p.1, φ p.2) :=
      (hΨ (p.1, φ p.2)).mdifferentiableAt hk1
    have hpr : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P))
        (fun q : ℝ × S => (q.1, φ q.2)) p
        ((ContinuousLinearMap.fst ℝ ℝ E2).prod
          ((mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2).comp (ContinuousLinearMap.snd ℝ ℝ E2))) :=
      (hasMFDerivAt_fst p).prodMk (hφd.hasMFDerivAt.comp p (hasMFDerivAt_snd p))
    have hcomp := hΨd.hasMFDerivAt.comp p hpr
    have hmf : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (fun q : ℝ × S => Ψ (q.1, φ q.2)) p =
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) Ψ (p.1, φ p.2)).comp
          ((ContinuousLinearMap.fst ℝ ℝ E2).prod
            ((mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2).comp (ContinuousLinearMap.snd ℝ ℝ E2))) :=
      hcomp.mfderiv
    have hD : ∀ u : ℝ × E2, mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p u =
        mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) Ψ (p.1, φ p.2)
          ((u.1, mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2 u.2) : ℝ × P) := by
      intro u
      change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (fun q : ℝ × S => Ψ (q.1, φ q.2)) p u = _
      rw [hmf]
      rfl
    rw [hD v, hD w, hΘ]
    refine (hpullΨ (p.1, φ p.2) _ _).trans ?_
    rw [← hκ p.2 v.2 w.2]
    dsimp only
    rw [RCLike.inner_apply, conj_trivial]
    ring

end DifferentialGeometry.Geometry.Collapse
