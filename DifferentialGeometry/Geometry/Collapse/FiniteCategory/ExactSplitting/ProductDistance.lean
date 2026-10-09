import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingRow
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.DerivativeAtZero
import DifferentialGeometry.Geometry.Metric.Path.Composition

/-!
# R2: the finite-order product metric on `F × Z` with the product distance

For an exact metric splitting `e : M ≃ᵢ ℓ²(F × Y)` (tiers T1–T3), the finite-order product metric
`du² + h` on `F × Z` (`splittingProductMetric`, of class `C^K`) is a finite-order Riemannian metric
whose Riemannian distance is the `ℓ²` product distance (`splittingProductMetric_riemannianEDist`).
The vertical coordinate field `∂_u = (a, 0)` is carried by the product map to the splitting
frame (`mfderiv_splittingProductDiffeomorph_fst`), and the vertical lines are its geodesics
(`splittingProductDiffeomorph_vertical`).

The cross-model length lemma `riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross` is general.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

section Cross

variable {V E H H' M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ E H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ y : N, ENorm (TangentSpace J y)]
  [∀ y : N, ENormSMulClass ℝ (TangentSpace J y)]

/-- A `C¹` map whose differential preserves the norms does not increase Riemannian distance
(the two manifolds may have different models). -/
theorem riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross (f : M → N) (hf : ContMDiff I J 1 f)
    (hiso : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ) (x y : M) :
    riemannianEDist J (f x) (f y) ≤ riemannianEDist I x y := by
  refine le_of_forall_gt fun c hc => ?_
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hc
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ t :=
    ae_restrict_of_forall_mem measurableSet_Ioo fun t ht =>
      ((hγ t (Ioo_subset_Icc_self ht)).contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt
        one_ne_zero
  have heq : pathELength J (f ∘ γ) 0 1 = pathELength I γ 0 1 :=
    Manifold.pathELength_comp_eq_of_enorm_mfderiv_eq f hdiff
      (ae_of_all _ fun t => (hf (γ t)).mdifferentiableAt one_ne_zero)
      (ae_of_all _ fun t => hiso (γ t) _)
  have hle : riemannianEDist J (f x) (f y) ≤ pathELength J (f ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hf.comp_contMDiffOn hγ) (congrArg f hγ0) (congrArg f hγ1)
      zero_le_one
  rw [heq] at hle
  exact hle.trans_lt hlen

end Cross

section Splitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E H M F Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y] [NeZero (Module.finrank ℝ E)] {r : ℕ∞}

local notation "P" => Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ
local notation "IZ" => 𝓘(ℝ, P)
local notation "IP" => ModelWithCorners.prod (𝓘(ℝ, F)) IZ

omit [CompleteSpace M] in
private theorem one_le_add_two_F7LFR11b : (1 : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 :=
  le_add_left (by norm_num)

theorem splittingProductDiffeomorph_apply
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ p : F × {x : M // (e x).fst = 0},
      splittingProductDiffeomorph g hr hnorm e p = splittingFactorProductEquiv e (toLp 2 p) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro p
  change (splittingProductDiffeomorph g hr hnorm e).toEquiv p = _
  rw [splittingProductDiffeomorph_toEquiv]
  rfl

/-- The product map preserves the norms of `du² + h` and `g`. -/
theorem splittingProductMetric_enorm_mfderiv
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
      ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ (p : F × {x : M // (e x).fst = 0}) (v : TangentSpace IP p),
      ‖mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p v‖ₑ = ‖v‖ₑ := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
    ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
  intro p v
  rw [hnorm, splittingProductDiffeomorph_metric g hr hnorm e p v v,
    ← splittingProductMetric_inner g hr hnorm e p v v, ← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

/-- The inverse product map preserves the norms of `g` and `du² + h`. -/
theorem splittingProductMetric_enorm_mfderiv_symm
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
      ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ (x : M) (w : TangentSpace I x),
      ‖mfderiv I IP (splittingProductDiffeomorph g hr hnorm e).symm x w‖ₑ = ‖w‖ₑ := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  let _ : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
    ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
  intro x w
  let Ψ := splittingProductDiffeomorph g hr hnorm e
  have hr0 : ((r : ℕ∞ω) + 2) ≠ 0 := by simp
  have hcomp : mfderiv IP I Ψ (Ψ.symm x) (mfderiv I IP Ψ.symm x w) = w := by
    have hd := mfderiv_comp x (Ψ.contMDiff.mdifferentiableAt hr0 (x := Ψ.symm x))
      (Ψ.symm.contMDiff.mdifferentiableAt hr0 (x := x))
    have hid : (Ψ : F × {x : M // (e x).fst = 0} → M) ∘ Ψ.symm = id :=
      funext fun y => Ψ.apply_symm_apply y
    rw [hid, mfderiv_id] at hd
    exact (congrArg (fun L => L w) hd).symm
  have h1 := splittingProductMetric_enorm_mfderiv g hr hnorm e (Ψ.symm x)
    (mfderiv I IP Ψ.symm x w)
  rw [← h1, hnorm, hnorm, hcomp]
  congr 2
  exact congrArg (fun y => g.inner y w w) (Ψ.apply_symm_apply x)

/-- **R2.** The Riemannian distance of the finite-order product metric `du² + h` on `F × Z` is
the `ℓ²` product distance. -/
theorem splittingProductMetric_riemannianEDist
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    letI : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
      ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
    ∀ p q : F × {x : M // (e x).fst = 0},
      riemannianEDist IP p q = edist (toLp 2 p) (toLp 2 q) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  let _ : RiemannianBundle (TangentSpace IP : F × {x : M // (e x).fst = 0} → Type _) :=
    ⟨(splittingProductMetric g hr hnorm e).toRiemannianMetric⟩
  intro p q
  let Ψ := splittingProductDiffeomorph g hr hnorm e
  have hΨ : edist (Ψ p) (Ψ q) = edist (toLp 2 p) (toLp 2 q) := by
    rw [splittingProductDiffeomorph_apply g hr hnorm e p,
      splittingProductDiffeomorph_apply g hr hnorm e q]
    exact (splittingFactorProductEquiv e).edist_eq _ _
  have hM : riemannianEDist I (Ψ p) (Ψ q) = edist (toLp 2 p) (toLp 2 q) := by
    rw [← IsRiemannianManifold.out (I := I), hΨ]
  apply le_antisymm
  · have h := riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross (Ψ.symm : M → _)
      (Ψ.symm.contMDiff.of_le one_le_add_two_F7LFR11b)
      (splittingProductMetric_enorm_mfderiv_symm g hr hnorm e) (Ψ p) (Ψ q)
    rw [Ψ.symm_apply_apply, Ψ.symm_apply_apply, hM] at h
    exact h
  · rw [← hM]
    exact riemannianEDist_comp_le_of_enorm_mfderiv_eq_cross (Ψ : _ → M)
      (Ψ.contMDiff.of_le one_le_add_two_F7LFR11b)
      (splittingProductMetric_enorm_mfderiv g hr hnorm e) p q

/-- **R2 (vertical lines).** The vertical lines of `F × Z` are carried to the geodesics of the
splitting frame. -/
theorem splittingProductDiffeomorph_vertical
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (a : F) (s : ℝ),
      splittingProductDiffeomorph g hr hnorm e (p.1 + s • a, p.2) =
        g.expMap (⟨splittingProductDiffeomorph g hr hnorm e p,
          s • splittingFrame g e (splittingProductDiffeomorph g hr hnorm e p) a⟩ :
            TangentBundle I M) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro p a s
  rw [expMap_splittingFrame g hr hnorm e, splittingProductDiffeomorph_apply g hr hnorm e,
    splittingProductDiffeomorph_apply g hr hnorm e, splittingFactorProductEquiv_apply,
    splittingFactorProductEquiv_apply, e.apply_symm_apply]
  rfl

/-- **R2 (the vertical field).** The coordinate field `∂_u = (a, 0)` of `F × Z` is carried by the
product map to the splitting frame. -/
theorem mfderiv_splittingProductDiffeomorph_fst
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (a : F),
      mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p ((a, 0) : F × P) =
        splittingFrame g e (splittingProductDiffeomorph g hr hnorm e p) a := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  intro p a
  let Ψ := splittingProductDiffeomorph g hr hnorm e
  let x := Ψ p
  let w : E := splittingFrame g e x a
  have hr1 : 1 ≤ r := one_le_two.trans hr
  let c : ℝ → F × {x : M // (e x).fst = 0} := fun s => (p.1 + s • a, p.2)
  have hc0 : c 0 = p := by simp [c]
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) (fun s : ℝ => p.1 + s • a) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight a) := by
    have h := (((hasDerivAt_id (0 : ℝ)).smul_const a).const_add p.1).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, ℝ) IZ (fun _ : ℝ => p.2) 0 0 := hasMFDerivAt_const _ _
  have hcd := h1.prodMk h2
  have hΨd : MDifferentiableAt IP I Ψ p := Ψ.contMDiff.mdifferentiableAt (by simp)
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun s : ℝ => s • w) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hexp : HasMFDerivAt 𝓘(ℝ, E) I (fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M))
      ((0 : ℝ) • w) (ContinuousLinearMap.id ℝ E) :=
    (zero_smul ℝ w).symm ▸ g.hasMFDerivAt_expMap_zero hr1 x
  have hcomp1 := mfderiv_comp_of_eq hΨd hcd.mdifferentiableAt hc0
  have hcomp2 := mfderiv_comp_of_eq hexp.mdifferentiableAt hlin.mdifferentiableAt rfl
  have heq : (Ψ : F × {x : M // (e x).fst = 0} → M) ∘ c =
      (fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M)) ∘ (fun s : ℝ => s • w) :=
    funext fun s => splittingProductDiffeomorph_vertical g hr hnorm e p a s
  rw [heq, hcomp2, hcd.mfderiv, hexp.mfderiv, hlin.mfderiv] at hcomp1
  have hu := congrArg (fun L => L 1) hcomp1
  have key : ∀ q : F × {x : M // (e x).fst = 0}, q = p →
      (mfderiv IP I Ψ q ((a, 0) : F × P) : E) = mfderiv IP I Ψ p ((a, 0) : F × P) := by
    rintro q rfl
    rfl
  have hL : ((1 : ℝ →L[ℝ] ℝ).smulRight a).prod (0 : ℝ →L[ℝ] P) 1 = ((a, 0) : F × P) := by
    simp
  have hR : (ContinuousLinearMap.id ℝ E).comp ((1 : ℝ →L[ℝ] ℝ).smulRight w) 1 = w := by
    simp
  change mfderiv IP I Ψ p ((a, 0) : F × P) = w
  rw [← key (c 0) hc0, ← hL, ← hR]
  exact hu.symm

end Splitting

end DifferentialGeometry.Geometry.ExactSplitting
