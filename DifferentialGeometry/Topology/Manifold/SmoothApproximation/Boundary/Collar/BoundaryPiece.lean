import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.Construction
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.LocalPiece
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Boundary.Collar.JetBlend

/-!
# The local step of the collar straightening at a boundary point, in collar coordinates

`eventually_injOn_isInvertible_straighten`: at a boundary point `p` of `A`, the straightened maps
`f j = cB ∘ (ret × projIcc) ∘ X j` on the collar `{rA < δ'}`, where
`X j = straightenBlend rA (δ j) (M j) g` blends the model
`M j x = (us j (πA x), 0) + rA x • ws j (πA x)` with the target data `g = (e ∘ πB ∘ h, rB ∘ h)`,
are eventually injective with invertible `mfderiv` on one fixed neighbourhood of `p`.

Coordinates: `κ (y, t) = cA (φ⁻¹ y, t)` on `S = ball y₀ r ×ˢ [0, r)` (`φ` the chart of `∂A` at
`p`). In these coordinates `X j ∘ κ` is the Euclidean blend of `collarJet_close` for the data
`a j = (us j ∘ φ⁻¹, 0)`, `b j = ws j ∘ φ⁻¹` with `G = g ∘ κ`; `Γ = (e ∘ πB, rB)` composed with
`f j` is `P ∘ X j ∘ κ` with `P (v, s) = (e (ret v), s)`; `DG (y₀, 0)` is injective because
`u = e ∘ πB ∘ h` is an immersion of `∂A` and the normal component `w p` of `∂_t G` is positive.
Then `eventually_injOn_isInvertible_of_collarBlend`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.VectorField DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

theorem norm_prod_mk_zero {F : Type*} [NormedAddCommGroup F] (v : F) : ‖(v, (0 : ℝ))‖ = ‖v‖ := by
  simp [Prod.norm_def]

/-- **Local step of the collar straightening at a boundary point.** -/
theorem eventually_injOn_isInvertible_straighten {n : ℕ}
    {A : Type*} [TopologicalSpace A] [ChartedSpace (EuclideanHalfSpace (n + 1)) A]
    [IsManifold (𝓡∂ (n + 1)) ∞ A]
    {B : Type*} [TopologicalSpace B] [ChartedSpace (EuclideanHalfSpace (n + 1)) B]
    [IsManifold (𝓡∂ (n + 1)) ∞ B] {N : ℕ}
    {aA : ℝ} [Fact ((0 : ℝ) < aA)]
    {cA : BoundaryManifold (𝓡∂ (n + 1)) A × Icc (0 : ℝ) aA → A}
    (hcA : ContMDiff ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
      (𝓡∂ (n + 1)) ∞ cA)
    (hcA0 : ∀ p, cA (p, ⟨0, le_rfl, (Fact.out : (0 : ℝ) < aA).le⟩) = p)
    {rA : A → ℝ} (hrA : Continuous rA) (hrA0 : ∀ x, 0 ≤ rA x)
    (hrcA : ∀ q, rA (cA q) = q.2.val)
    {πA : A → BoundaryManifold (𝓡∂ (n + 1)) A} (hπA : ContinuousOn πA {x | rA x < aA})
    (hπcA : ∀ q : BoundaryManifold (𝓡∂ (n + 1)) A × Icc (0 : ℝ) aA, q.2.val < aA → πA (cA q) = q.1)
    (hcπA : ∀ x (hx : rA x < aA), cA (πA x, ⟨rA x, hrA0 x, hx.le⟩) = x)
    {aB : ℝ} [Fact ((0 : ℝ) < aB)]
    {cB : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB → B}
    {rB : B → ℝ} (hrB : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ rB) (hrcB : ∀ q, rB (cB q) = q.2.val)
    {πB : B → BoundaryManifold (𝓡∂ (n + 1)) B}
    (hπB : ContMDiffOn (𝓡∂ (n + 1)) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ πB
      {y | rB y < aB})
    (hπcB : ∀ q : BoundaryManifold (𝓡∂ (n + 1)) B × Icc (0 : ℝ) aB, q.2.val < aB → πB (cB q) = q.1)
    {e : BoundaryManifold (𝓡∂ (n + 1)) B → EuclideanSpace ℝ (Fin N)}
    (he : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      ∞ e)
    {ret : EuclideanSpace ℝ (Fin N) → BoundaryManifold (𝓡∂ (n + 1)) B}
    {U : Set (EuclideanSpace ℝ (Fin N))} (hU : IsOpen U) (heU : range e ⊆ U)
    (hret : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞ ret U)
    (hrete : ∀ q, ret (e q) = q)
    {δ' : ℝ} (hδ' : 0 < δ') (hδ'aA : δ' < aA)
    {g : A → EuclideanSpace ℝ (Fin N) × ℝ}
    (hg : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) 1 g {x | rA x < δ'})
    (hge : ∀ x, rA x < δ' → (g x).1 ∈ range e)
    {u : BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N)}
    (hu : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      1 u)
    (hui : ∀ p, Injective (mfderiv (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u p))
    (hgu : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) A, g p = (u p, 0))
    {w : BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N) × ℝ}
    (hw : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) 1 w)
    (hwg : ∀ p, w p = derivWithin
      (fun t => g (cA (p, projIcc 0 aA (Fact.out : (0 : ℝ) < aA).le t))) (Icc 0 aA) 0)
    (hlam : ∀ p, 0 < (w p).2)
    {δ : ℕ → ℝ} (hδpos : ∀ j, 0 < δ j) (hδlim : Tendsto δ atTop (𝓝 0))
    {us : ℕ → BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N)}
    (hus : ∀ j, ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ (us j))
    (husU : ∀ j p, ‖us j p - u p‖ ≤ δ j / (j + 1))
    (husC : ∀ (p : BoundaryManifold (𝓡∂ (n + 1)) A)
      (K : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)))), IsCompact K →
      K ⊆ (extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).target →
      MapCPConvergenceOn K 1
        (fun j y => us j ((extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).symm y))
        (fun y => u ((extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).symm y)))
    {ws : ℕ → BoundaryManifold (𝓡∂ (n + 1)) A → EuclideanSpace ℝ (Fin N) × ℝ}
    (hws : ∀ j, ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) ∞ (ws j))
    (hwsU : TendstoUniformly ws w atTop)
    (hwsC : ∀ (p : BoundaryManifold (𝓡∂ (n + 1)) A)
      (K : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)))), IsCompact K →
      K ⊆ (extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).target →
      MapCPConvergenceOn K 1
        (fun j y => ws j ((extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).symm y))
        (fun y => w ((extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p).symm y)))
    {M : ℕ → A → EuclideanSpace ℝ (Fin N) × ℝ}
    (hM : ∀ j x, M j x = (us j (πA x), 0) + rA x • ws j (πA x))
    {f : ℕ → A → B} (hf : ∀ j, ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) 1 (f j))
    (hfX : ∀ j x, rA x < δ' → f j x = cB (ret (straightenBlend rA (δ j) (M j) g x).1,
      projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le (straightenBlend rA (δ j) (M j) g x).2))
    (hX2 : ∀ j x, rA x < δ' → (straightenBlend rA (δ j) (M j) g x).2 ∈ Ico 0 aB)
    (p : BoundaryManifold (𝓡∂ (n + 1)) A) :
    ∃ V ∈ 𝓝 (p : A), ∀ᶠ j in atTop,
      InjOn (f j) V ∧ ∀ x ∈ V, (mfderiv (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) x).IsInvertible := by
  have ha : (0 : ℝ) < aA := Fact.out
  set φ := extChartAt (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) p with hφ
  set y₀ : EuclideanSpace ℝ (Fin (n + 1 - 1)) := φ p with hy₀
  set κ : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ → A :=
    fun z => cA (φ.symm z.1, projIcc 0 aA ha.le z.2) with hκ
  set T₀ : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) := φ.target ×ˢ Icc 0 aA with hT₀
  have hκc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (𝓡∂ (n + 1)) ∞ κ T₀ := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) ∞
        (fun z : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ => φ.symm z.1) T₀ :=
      (contMDiffOn_extChartAt_symm p).comp contDiff_fst.contMDiff.contMDiffOn
        (fun z hz => hz.1)
    have h2 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (𝓡∂ 1) ∞
        (fun z : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ => projIcc 0 aA ha.le z.2) T₀ :=
      contMDiffOn_projIcc.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2)
    exact hcA.comp_contMDiffOn (h1.prodMk h2)
  -- the radius and the half-ball region
  have htgt : IsOpen φ.target := isOpen_extChartAt_target (I := (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))) p
  have hy₀t : y₀ ∈ φ.target := mem_extChartAt_target (I := (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1)))) p
  obtain ⟨r₀, hr₀, hr₀t⟩ : ∃ r₀ > 0, closedBall y₀ r₀ ⊆ φ.target := by
    obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp htgt y₀ hy₀t
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεt⟩
  set r := min r₀ δ' with hr
  have hrpos : 0 < r := lt_min hr₀ hδ'
  set S : Set (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) := ball y₀ r ×ˢ Ico 0 r with hS
  have hball_t : ball y₀ r ⊆ φ.target :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (min_le_left _ _))).trans hr₀t
  have hrδ' : r ≤ δ' := min_le_right _ _
  have hST₀ : S ⊆ T₀ := fun z hz =>
    ⟨hball_t hz.1, hz.2.1, (lt_of_lt_of_le hz.2.2 (hrδ'.trans hδ'aA.le)).le⟩
  have hrκ : ∀ z ∈ S, rA (κ z) = z.2 := fun z hz => by
    simp only [hκ, hrcA, projIcc_of_mem _ (hST₀ hz).2]
  have hκδ' : ∀ z ∈ S, rA (κ z) < δ' := fun z hz => by
    rw [hrκ z hz]
    exact lt_of_lt_of_le hz.2.2 hrδ'
  have hπκ : ∀ z ∈ S, πA (κ z) = φ.symm z.1 := fun z hz => by
    refine hπcA _ ?_
    rw [projIcc_of_mem _ (hST₀ hz).2]
    exact lt_of_lt_of_le hz.2.2 (hrδ'.trans hδ'aA.le)
  have hκ0 : ∀ y, κ (y, 0) = (φ.symm y : A) := fun y => by
    simp only [hκ, projIcc_left]
    exact hcA0 _
  have hpp : φ.symm y₀ = p := by simp only [hy₀, hφ, extChartAt_to_inv]
  have hκz₀ : κ (y₀, 0) = p := by rw [hκ0, hpp]
  have hπp : πA p = p := by
    have h1 := hπcA (p, ⟨0, le_rfl, ha.le⟩) ha
    rwa [hcA0] at h1
  -- the target data in coordinates
  set G : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ → EuclideanSpace ℝ (Fin N) × ℝ :=
    fun z => g (κ z) with hG
  have hGS : ContDiffOn ℝ 1 G S := by
    have h := hg.comp ((hκc.of_le (by exact_mod_cast le_top)).mono hST₀)
      (fun z hz => hκδ' z hz)
    exact contMDiffOn_iff_contDiffOn.mp h
  have hSu : UniqueDiffOn ℝ S := isOpen_ball.uniqueDiffOn.prod (uniqueDiffOn_Ico 0 r)
  have hz₀ : ((y₀, 0) : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) ∈ S :=
    ⟨mem_ball_self hrpos, left_mem_Ico.2 hrpos⟩
  set L := fderivWithin ℝ G S (y₀, 0) with hL
  have hGd : HasFDerivWithinAt G L S (y₀, 0) :=
    ((hGS.differentiableOn one_ne_zero) _ hz₀).hasFDerivWithinAt
  -- chart expressions of the boundary data
  have hchart : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ∞}
      {v : BoundaryManifold (𝓡∂ (n + 1)) A → F}, ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, F) m v →
      ContDiffOn ℝ m (fun y => v (φ.symm y)) φ.target := fun hv =>
    contMDiffOn_iff_contDiffOn.mp (hv.comp_contMDiffOn
      ((contMDiffOn_extChartAt_symm (n := ∞) p).of_le (by exact_mod_cast le_top)))
  set uc := fun y => u (φ.symm y) with huc
  have huc1 : ContDiffOn ℝ 1 uc φ.target := hchart hu
  set wc := fun y => w (φ.symm y) with hwc
  have hwc1 : ContDiffOn ℝ 1 wc φ.target := hchart hw
  set D := fderiv ℝ uc y₀ with hD
  have hLinl : L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ) =
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).comp D := by
    have h1 : HasFDerivWithinAt (fun y => G (y, 0))
        (L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ))
        (ball y₀ r) y₀ :=
      HasFDerivWithinAt.comp (g := G) y₀ hGd
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) y₀ (0 : ℝ)).hasFDerivWithinAt
        (fun y hy => ⟨hy, left_mem_Ico.2 hrpos⟩)
    have h1' := h1.hasFDerivAt (isOpen_ball.mem_nhds (mem_ball_self hrpos))
    have h2 : HasFDerivAt (fun y => G (y, 0))
        ((ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).comp D) y₀ := by
      have h3 : HasFDerivAt (fun y => ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ (uc y))
          ((ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).comp D) y₀ :=
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).hasFDerivAt.comp y₀
          ((huc1.differentiableOn one_ne_zero y₀ hy₀t).differentiableAt
            (htgt.mem_nhds hy₀t)).hasFDerivAt
      refine h3.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
      simp only [hG, hκ0, hgu, huc, ContinuousLinearMap.inl_apply]
    exact h1'.unique h2
  have hL01 : L (0, 1) = w p := by
    have hcurve : HasDerivWithinAt (fun t : ℝ => (y₀, t))
        ((0 : EuclideanSpace ℝ (Fin (n + 1 - 1))), (1 : ℝ)) (Ico 0 r) 0 :=
      ((hasDerivAt_const (0 : ℝ) y₀).prodMk (hasDerivAt_id (0 : ℝ))).hasDerivWithinAt
    have hcomp := hGd.comp_hasDerivWithinAt (x := (0 : ℝ)) hcurve
      (fun t ht => ⟨mem_ball_self hrpos, ht⟩)
    have hmem : Ico 0 r ∈ 𝓝[Icc 0 aA] (0 : ℝ) := by
      refine Filter.mem_of_superset (inter_mem_nhdsWithin (Icc 0 aA) (Iio_mem_nhds hrpos)) ?_
      rintro t ⟨ht, ht'⟩
      exact ⟨ht.1, ht'⟩
    have hfun : (fun t => g (cA (p, projIcc 0 aA (Fact.out : (0 : ℝ) < aA).le t))) =
        G ∘ fun t : ℝ => (y₀, t) := by
      funext t
      simp only [hG, hκ, Function.comp_apply, hpp]
    rw [hwg p, hfun]
    exact ((hcomp.mono_of_mem_nhdsWithin hmem).derivWithin
      (uniqueDiffOn_Icc ha 0 (left_mem_Icc.2 ha.le))).symm
  have hDinj : Injective D := by
    have hmf : (mfderiv (HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) u p :
        EuclideanSpace ℝ (Fin (n + 1 - 1)) →L[ℝ] EuclideanSpace ℝ (Fin N)) = D := by
      rw [(hu.mdifferentiableAt one_ne_zero).mfderiv,
        ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
      rfl
    rw [← hmf]
    exact hui p
  have hLv : ∀ v : EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ, L v = (D v.1, 0) + v.2 • w p := by
    intro v
    have h1 : v = ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ v.1 +
        v.2 • ((0 : EuclideanSpace ℝ (Fin (n + 1 - 1))), (1 : ℝ)) := by
      ext <;> simp
    have h2 : L (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ v.1) =
        (D v.1, 0) := by
      have h3 := congrArg (fun T => T v.1) hLinl
      simpa using h3
    conv_lhs => rw [h1]
    rw [map_add, map_smul, h2, hL01]
  have hLinj : Injective L := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hLv] at hv
    have h2 : v.2 * (w p).2 = 0 := by
      have h3 := congrArg Prod.snd hv
      simpa using h3
    have hv2 : v.2 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h (hlam p).ne'
    have h1 : D v.1 = 0 := by
      have h3 := congrArg Prod.fst hv
      simpa [hv2] using h3
    have hv1 : v.1 = 0 := hDinj (by rw [h1, map_zero])
    exact Prod.ext hv1 hv2
  obtain ⟨c, hc, hcL⟩ := exists_pos_mul_norm_le_of_injective hLinj
  -- the projection `P` fixing `G`
  set P : EuclideanSpace ℝ (Fin N) × ℝ → EuclideanSpace ℝ (Fin N) × ℝ :=
    fun ζ => (e (ret ζ.1), ζ.2) with hPdef
  have heret : ContDiffOn ℝ ∞ (fun v => e (ret v)) U :=
    contMDiffOn_iff_contDiffOn.mp (he.comp_contMDiffOn hret)
  have hUo : IsOpen (Prod.fst ⁻¹' U : Set (EuclideanSpace ℝ (Fin N) × ℝ)) :=
    hU.preimage continuous_fst
  have hPc : ContDiffOn ℝ ∞ P (Prod.fst ⁻¹' U) :=
    (heret.comp contDiff_fst.contDiffOn (fun ζ hζ => hζ)).prodMk contDiff_snd.contDiffOn
  have hGz₀U : G (y₀, 0) ∈ Prod.fst ⁻¹' U := heU (hge _ (hκδ' _ hz₀))
  obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.isOpen_iff.mp hUo _ hGz₀U
  have hP : ∀ ζ ∈ ball (G (y₀, 0)) ρ₀, HasFDerivAt P (fderiv ℝ P ζ) ζ := fun ζ hζ =>
    ((hPc.contDiffAt (hUo.mem_nhds (hρ₀U hζ))).differentiableAt (by simp)).hasFDerivAt
  have hP' : ContinuousAt (fderiv ℝ P) (G (y₀, 0)) :=
    ((hPc.contDiffAt (hUo.mem_nhds hGz₀U)).fderiv_right (m := 0) (by simp)).continuousAt
  have hPG : ∀ z ∈ S, P (G z) = G z := by
    intro z hz
    obtain ⟨q, hq⟩ := hge _ (hκδ' z hz)
    simp only [hPdef, hG]
    rw [← hq, hrete, hq]
  have hPL : (fderiv ℝ P (G (y₀, 0))).comp L = L := by
    have h1 : HasFDerivWithinAt (fun z => P (G z)) ((fderiv ℝ P (G (y₀, 0))).comp L) S (y₀, 0) :=
      (hP _ (mem_ball_self hρ₀)).comp_hasFDerivWithinAt (y₀, 0) hGd
    have h2 : HasFDerivWithinAt (fun z => P (G z)) L S (y₀, 0) :=
      hGd.congr (fun z hz => hPG z hz) (hPG _ hz₀)
    exact (hSu _ hz₀).eq h1 h2
  -- the jet data
  have hinl : ∀ T : EuclideanSpace ℝ (Fin (n + 1 - 1)) →L[ℝ] EuclideanSpace ℝ (Fin N),
      ‖(ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).comp T‖ ≤ ‖T‖ := fun T =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => by
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, norm_prod_mk_zero]
      exact T.le_opNorm v
  set a : ℕ → EuclideanSpace ℝ (Fin (n + 1 - 1)) → EuclideanSpace ℝ (Fin N) × ℝ :=
    fun j y => ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ (us j (φ.symm y)) with ha_def
  set a' : ℕ → EuclideanSpace ℝ (Fin (n + 1 - 1)) →
      EuclideanSpace ℝ (Fin (n + 1 - 1)) →L[ℝ] EuclideanSpace ℝ (Fin N) × ℝ :=
    fun j y => (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).comp
      (fderiv ℝ (fun y => us j (φ.symm y)) y) with ha'_def
  set b : ℕ → EuclideanSpace ℝ (Fin (n + 1 - 1)) → EuclideanSpace ℝ (Fin N) × ℝ :=
    fun j y => ws j (φ.symm y) with hb_def
  have husc : ∀ j, ContDiffOn ℝ ∞ (fun y => us j (φ.symm y)) φ.target := fun j => hchart (hus j)
  have hwsc : ∀ j, ContDiffOn ℝ ∞ (b j) φ.target := fun j => hchart (hws j)
  have had : ∀ j, ∀ y ∈ ball y₀ r, HasFDerivAt (a j) (a' j y) y := fun j y hy =>
    (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ).hasFDerivAt.comp y
      (((husc j).differentiableOn (by simp) y (hball_t hy)).differentiableAt
        (htgt.mem_nhds (hball_t hy))).hasFDerivAt
  have hbd : ∀ j, ∀ y ∈ ball y₀ r, HasFDerivAt (b j) (fderiv ℝ (b j) y) y := fun j y hy =>
    (((hwsc j).differentiableOn (by simp) y (hball_t hy)).differentiableAt
      (htgt.mem_nhds (hball_t hy))).hasFDerivAt
  have hha : ∀ ε > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r, ‖a j y - G (y, 0)‖ ≤ ε * δ j := by
    intro ε hε
    obtain ⟨j₁, hj₁⟩ := exists_nat_gt (1 / ε)
    filter_upwards [eventually_ge_atTop j₁] with j hj y _
    have hG0 : G (y, 0) = ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin N)) ℝ (u (φ.symm y)) := by
      simp only [hG, hκ0, hgu, ContinuousLinearMap.inl_apply]
    rw [hG0, ha_def, ← map_sub, ContinuousLinearMap.inl_apply, norm_prod_mk_zero]
    refine (husU j _).trans ?_
    have hj' : (1 : ℝ) / ε < j + 1 := by
      have : (j₁ : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    rw [div_lt_iff₀ hε] at hj'
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hδpos j]
  have hha' : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r',
      ‖a' j y - L.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ)‖ ≤ ε := by
    intro ε hε
    obtain ⟨r', hr', hev⟩ := eventually_norm_fderiv_sub_le_of_mapCPConvergenceOn htgt hr₀ hr₀t
      (husC p _ (isCompact_closedBall y₀ r₀) hr₀t)
      (fun j => (husc j).differentiableOn (by simp)) huc1 ε hε
    refine ⟨r', hr', hev.mono fun j hj y hy => ?_⟩
    rw [hLinl, ha'_def, ← ContinuousLinearMap.comp_sub]
    exact (hinl _).trans (hj y hy)
  have hhb : ∀ ε > 0, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r', ‖b j y - L (0, 1)‖ ≤ ε := by
    intro ε hε
    rw [hL01]
    have hwcont : ContinuousAt wc y₀ := hwc1.continuousOn.continuousAt (htgt.mem_nhds hy₀t)
    obtain ⟨r₁, hr₁, hr₁c⟩ := Metric.continuousAt_iff.mp hwcont (ε / 2) (half_pos hε)
    refine ⟨r₁, hr₁, ?_⟩
    filter_upwards [Metric.tendstoUniformly_iff.mp hwsU (ε / 2) (half_pos hε)] with j hj y hy
    have h1 : ‖ws j (φ.symm y) - w (φ.symm y)‖ ≤ ε / 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact (hj _).le
    have h2 : ‖w (φ.symm y) - w p‖ ≤ ε / 2 := by
      have h3 := (hr₁c (mem_ball.mp hy)).le
      rw [dist_eq_norm] at h3
      simpa only [hwc, hpp] using h3
    calc ‖b j y - w p‖ = ‖(ws j (φ.symm y) - w (φ.symm y)) + (w (φ.symm y) - w p)‖ := by
          rw [hb_def, sub_add_sub_cancel]
      _ ≤ ‖ws j (φ.symm y) - w (φ.symm y)‖ + ‖w (φ.symm y) - w p‖ := norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := add_halves ε
  have hhb' : ∃ C, ∃ r' > 0, ∀ᶠ j in atTop, ∀ y ∈ ball y₀ r', ‖fderiv ℝ (b j) y‖ ≤ C := by
    obtain ⟨r', hr', hev⟩ := eventually_norm_fderiv_sub_le_of_mapCPConvergenceOn htgt hr₀ hr₀t
      (hwsC p _ (isCompact_closedBall y₀ r₀) hr₀t)
      (fun j => (hwsc j).differentiableOn (by simp)) hwc1 1 one_pos
    refine ⟨‖fderiv ℝ wc y₀‖ + 1, r', hr', hev.mono fun j hj y hy => ?_⟩
    have h1 := hj y hy
    calc ‖fderiv ℝ (b j) y‖ = ‖(fderiv ℝ (b j) y - fderiv ℝ wc y₀) + fderiv ℝ wc y₀‖ := by
          rw [sub_add_cancel]
      _ ≤ ‖fderiv ℝ (b j) y - fderiv ℝ wc y₀‖ + ‖fderiv ℝ wc y₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖fderiv ℝ wc y₀‖ := add_le_add h1 le_rfl
      _ = ‖fderiv ℝ wc y₀‖ + 1 := add_comm _ _
  -- the Euclidean blends
  obtain ⟨Cρ, hCρ⟩ := exists_abs_deriv_collarTransition_le
  obtain ⟨X', hXd, hX⟩ := collarJet_close (ρ := collarTransition)
    (contDiff_collarTransition.differentiable (by simp)) hCρ
    (fun t ht => collarTransition_eq_one (by linarith))
    (fun t ht => deriv_collarTransition_eq_zero_of_one_le ht) collarTransition_mem_Icc hrpos hGS
    had hbd hδlim hδpos hha hha' hhb hhb'
  -- the factorisation through `P`
  set Γ : B → EuclideanSpace ℝ (Fin N) × ℝ := fun y => (e (πB y), rB y) with hΓ
  have hXe : ∀ j, ∀ z ∈ S, straightenBlend rA (δ j) (M j) g (κ z) =
      collarBlend collarTransition (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ)
        (δ j) (fun z => a j z.1 + z.2 • b j z.1) G z := by
    intro j z hz
    simp only [straightenBlend, collarBlend, hM, hrκ z hz, hπκ z hz, ha_def, hb_def, hG,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.coe_snd']
  have hfac : ∀ j, ∀ z ∈ S, Γ (f j (κ z)) = P (collarBlend collarTransition
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ)
        (δ j) (fun z => a j z.1 + z.2 • b j z.1) G z) := by
    intro j z hz
    have h2 := hX2 j _ (hκδ' z hz)
    rw [hfX j _ (hκδ' z hz), ← hXe j z hz]
    have h3 : (projIcc 0 aB (Fact.out : (0 : ℝ) < aB).le
        (straightenBlend rA (δ j) (M j) g (κ z)).2).val =
        (straightenBlend rA (δ j) (M j) g (κ z)).2 := by
      rw [projIcc_of_mem _ (Ico_subset_Icc_self h2)]
    simp only [hΓ, hPdef]
    rw [hπcB _ (by rw [h3]; exact h2.2), hrcB, h3]
  have hΓs : ContMDiffOn (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) ∞ Γ {y | rB y < aB} :=
    (he.comp_contMDiffOn hπB).prodMk_space hrB.contMDiffOn
  have hΓd : ∀ j, ∀ z ∈ S, MDifferentiableAt (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ) Γ
      (f j (κ z)) := by
    intro j z hz
    have h2 := hX2 j _ (hκδ' z hz)
    have hlt : rB (f j (κ z)) < aB := by
      rw [hfX j _ (hκδ' z hz), hrcB, projIcc_of_mem _ (Ico_subset_Icc_self h2)]
      exact h2.2
    exact (hΓs.contMDiffAt ((isOpen_lt hrB.continuous continuous_const).mem_nhds hlt)
      ).mdifferentiableAt (by simp)
  -- the parametrisation `κ`
  have hκd : ∀ z ∈ S, MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (𝓡∂ (n + 1)) κ
      S z := fun z hz => ((hκc.mono hST₀) z hz).mdifferentiableWithinAt (by simp)
  have hκn : ∀ r' > 0, κ '' (S ∩ ball (y₀, 0) r') ∈ 𝓝 (κ (y₀, 0)) := by
    intro r' hr'
    set s := min r r' with hs
    have hspos : 0 < s := lt_min hrpos hr'
    have hsa : s < aA := lt_of_le_of_lt ((min_le_left _ _).trans hrδ') hδ'aA
    have hφo : IsOpen (φ.source ∩ φ ⁻¹' ball y₀ s) :=
      (continuousOn_extChartAt p).isOpen_inter_preimage (isOpen_extChartAt_source p) isOpen_ball
    have hVo : IsOpen ({x | rA x < s} ∩ πA ⁻¹' (φ.source ∩ φ ⁻¹' ball y₀ s)) :=
      (hπA.mono fun x (hx : rA x < s) => (lt_trans hx hsa : rA x < aA)).isOpen_inter_preimage
        (isOpen_lt hrA continuous_const) hφo
    have hpV : κ (y₀, 0) ∈ {x | rA x < s} ∩ πA ⁻¹' (φ.source ∩ φ ⁻¹' ball y₀ s) := by
      rw [hκz₀]
      refine ⟨?_, ?_, ?_⟩
      · change rA p < s
        rw [← hcA0 p, hrcA]
        exact hspos
      · rw [hπp]
        exact mem_extChartAt_source p
      · change φ (πA p) ∈ ball y₀ s
        rw [hπp]
        exact mem_ball_self hspos
    refine Filter.mem_of_superset (hVo.mem_nhds hpV) ?_
    rintro x ⟨hx1, hx2, hx3⟩
    have hx1' : rA x < s := hx1
    have hxa : rA x < aA := lt_trans hx1' hsa
    refine ⟨(φ (πA x), rA x), ⟨⟨?_, hrA0 x, lt_of_lt_of_le hx1' (min_le_left _ _)⟩, ?_⟩, ?_⟩
    · exact ball_subset_ball (min_le_left _ _) hx3
    · rw [mem_ball, Prod.dist_eq]
      refine max_lt (lt_of_lt_of_le (mem_ball.mp hx3) (min_le_right _ _)) ?_
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hrA0 x)]
      exact lt_of_lt_of_le hx1' (min_le_right _ _)
    · change cA (φ.symm (φ (πA x)), projIcc 0 aA ha.le (rA x)) = x
      rw [φ.left_inv hx2, projIcc_of_mem _ ⟨hrA0 x, hxa.le⟩]
      exact hcπA x hxa
  -- dimensions
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin,
      Module.finrank_self]
    omega
  have hδ1 : ∀ᶠ j in atTop, δ j ≤ 1 := hδlim.eventually (ge_mem_nhds one_pos)
  have hGc : ContinuousWithinAt G S (y₀, 0) := hGS.continuousOn _ hz₀
  have hfd : ∀ j, ∀ z ∈ S, MDifferentiableAt (𝓡∂ (n + 1)) (𝓡∂ (n + 1)) (f j) (κ z) :=
    fun j z _ => ((hf j) (κ z)).mdifferentiableAt one_ne_zero
  have hconv : Convex ℝ S := (convex_ball y₀ r).prod (convex_Ico 0 r)
  obtain ⟨V, hV, hev⟩ := eventually_injOn_isInvertible_of_collarBlend
    (E₁ := EuclideanSpace ℝ (Fin (n + 1 - 1)) × ℝ) (F := EuclideanSpace ℝ (Fin N) × ℝ)
    (I := 𝓡∂ (n + 1)) (J := 𝓡∂ (n + 1)) (S := S) (z₀ := (y₀, 0)) (κ := κ) (Γ := Γ) (f := f)
    (P := P) (P' := fderiv ℝ P) (G := G) (L := L)
    (X := fun j => collarBlend collarTransition
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin (n + 1 - 1))) ℝ)
      (δ j) (fun z => a j z.1 + z.2 • b j z.1) G) (X' := X') (δ := δ)
    hdim rfl hconv hSu hκd hκn hfd hΓd hρ₀ hP hP' hPL hGc hc hcL hδ1 hXd hX hfac
  rw [hκz₀] at hV
  exact ⟨V, hV, hev⟩

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
