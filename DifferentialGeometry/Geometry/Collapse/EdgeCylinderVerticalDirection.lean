import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceCarrierNoncompact
import DifferentialGeometry.Geometry.Geodesic.Convergence.FiniteDirectionNeighbourhood

/-!
# LFR28 B4 (vertical): the product chart carries `∂_t` to the vertical minimizing direction

`exists_edgeCylinderProductChart_vertical`: the product chart `Θ = Ψ ∘ (id × φ)` of R5
(`exists_edgeCylinderProductChart`, re-built here with the same construction) with, in addition,
`dΘ_p(1, 0) ∈ G.finiteMinimizingDirectionsTo {e⁻¹(t(Θ p) + ℓ, (e (Θ p)).snd)} (Θ p)` for every
`ℓ > 0`: the unit `G`-direction from `Θ p` to its vertical shift. With LFR18's uniqueness
(`eq_of_mem_finiteMinimizingDirectionsTo_vertical_shift`) this identifies `dΘ(1, 0)` with the vertical
field `V` of (LFR28.3) (F7-DOWN), the input `hVV`/`h3` of B4 (`edgeCylinder_vectors_of_covector_bounds`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.ExactSplitting DifferentialGeometry.Manifold
open DifferentialGeometry.Geometry.Riemannian.Geodesic

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance edgeCylinderVertical_nezero_finrank_LFR28ROW :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- **LFR28 R5.** The product chart `Θ = Ψ ∘ (id × φ)`: a `C^{k+2}` diffeomorphism `ℝ × S → N` with
`e ∘ Θ = (t, (e ∘ φ).snd)` and `Θ^*G = dt² + κ`. -/
theorem exists_edgeCylinderProductChart_vertical {N W S : Type} [MetricSpace N] [ChartedSpace E3 N]
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
        (∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
          G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2) ∧
        ∀ (p : ℝ × S) (ℓ : ℝ), 0 < ℓ →
          mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) ∈
            G.finiteMinimizingDirectionsTo
              {e.symm (WithLp.toLp 2 ((e (Θ p)).fst + ℓ, (e (Θ p)).snd))} (Θ p) := by
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
  have he : ∀ p : ℝ × S, e (Θ p) = WithLp.toLp 2 (p.1, (e (φ p.2 : N)).snd) := by
    intro p
    rw [hΘ, hΨdef, splittingProductDiffeomorph_apply, splittingFactorProductEquiv_apply,
      IsometryEquiv.apply_symm_apply]
    rfl
  have hk1 : ((k + 2 : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k + 2 ≠ 0 by omega)
  -- the derivative of `Θ` through the product map
  have hD : ∀ (p : ℝ × S) (u : ℝ × E2), mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p u =
      mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) Ψ (p.1, φ p.2)
        ((u.1, mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2 u.2) : ℝ × P) := by
    intro p u
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
    change mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (fun q : ℝ × S => Ψ (q.1, φ q.2)) p u = _
    rw [hmf]
    rfl
  have hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2 := by
    intro p v w
    rw [hD p v, hD p w, hΘ]
    refine (hpullΨ (p.1, φ p.2) _ _).trans ?_
    rw [← hκ p.2 v.2 w.2]
    dsimp only
    rw [RCLike.inner_apply, conj_trivial]
    ring
  refine ⟨Θ, he, hpull, fun p ℓ hℓ => ⟨?_, ?_⟩⟩
  · rw [hpull p ((1 : ℝ), (0 : E2)) ((1 : ℝ), (0 : E2))]
    dsimp only
    have hz : κ.inner p.2 (0 : E2) = 0 := (κ.inner p.2).map_zero
    rw [hz]
    change (1 : ℝ) * 1 + 0 = 1
    norm_num
  · rw [Metric.infDist_singleton, dist_vertical_shift e ℓ (Θ p), abs_of_pos hℓ]
    have hfr : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) =
        splittingFrame G e (Ψ (p.1, φ p.2)) (1 : ℝ) := by
      rw [hD p ((1 : ℝ), (0 : E2))]
      have h0 : mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2 (0 : E2) = 0 :=
        (mfderiv (𝓡 2) 𝓘(ℝ, P) φ p.2).map_zero
      dsimp only
      rw [h0]
      exact mfderiv_splittingProductDiffeomorph_fst G hk hnorm e (p.1, φ p.2) (1 : ℝ)
    rw [hfr, hΘ, ← splittingProductDiffeomorph_vertical G hk hnorm e (p.1, φ p.2) (1 : ℝ) ℓ]
    apply Set.mem_singleton_iff.mpr
    apply e.injective
    rw [e.apply_symm_apply, hΨdef, splittingProductDiffeomorph_apply,
      splittingProductDiffeomorph_apply, splittingFactorProductEquiv_apply,
      splittingFactorProductEquiv_apply, e.apply_symm_apply, e.apply_symm_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, smul_eq_mul, mul_one]

end DifferentialGeometry.Geometry.Collapse
