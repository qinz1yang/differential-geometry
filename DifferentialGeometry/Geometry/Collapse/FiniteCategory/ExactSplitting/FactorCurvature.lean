import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ProductCurvature
import DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.ProductRegularity

/-!
# LFR11 tier T4: the curvature of the zero factor

For an exact metric splitting `e : M ≃ᵢ ℓ²(F × Y)` of a complete Riemannian manifold with a
`C^{r+1}` metric (`r ≥ 2`), the zero factor `Z = {x | (e x).fst = 0}` with its induced metric `h`
has the ambient sectional curvature on its tangent planes:
`h.sectionalCurvature z v w = g.sectionalCurvature z (dι v) (dι w)`
(`inducedMetric_sectionalCurvature_eq`). In particular `sec_g ≥ 0` gives `sec_h ≥ 0`.

Route: the whole product diffeomorphism `Ψ : F × Z → M` of tier T3 pulls `g` back to the product
metric `du² + h`; the finite-order sectional curvature is natural under `Ψ` although the two model
spaces differ (`sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross`, from the cross-space
coefficient transition); in a product chart the curvature of `du² + h` on `Z`-planes is that of
`h` (`coefficientRm04_prod_snd`); and `Ψ (0, ·)` is the inclusion of `Z`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter WithLp Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

section Cross

variable {V E H H' M N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] [TopologicalSpace H'] {I : ModelWithCorners ℝ V H}
  {J : ModelWithCorners ℝ E H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 3 N] {n m : ℕ∞ω}

omit [FiniteDimensional ℝ V] [I.Boundaryless] [J.Boundaryless] [IsManifold I 3 M] in
/-- Chart coefficients of a finite metric along an inverse chart: regularity, symmetry and
coercivity on the chart target. -/
theorem chartCoefficient_properties
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _)) (hm : (2 : ℕ∞ω) ≤ m)
    (ψ : PartialDiffeomorph 𝓘(ℝ, E) J E N 3) :
    ContDiffOn ℝ 2 (fun z => (h.inner (ψ z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
        (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E) (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E)) ψ.source ∧
      (∀ z ∈ ψ.source, ∀ u v : E,
        (h.inner (ψ z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E) u v =
        (h.inner (ψ z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E) v u) ∧
      ∀ z ∈ ψ.source, IsCoercive
        ((h.inner (ψ z) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E)
          (mfderiv 𝓘(ℝ, E) J ψ z : E →L[ℝ] E)) := by
  refine ⟨h.contDiffOn_pullback_inner hm (by norm_num) ψ.open_source ψ.contMDiffOn, ?_, ?_⟩
  · intro z hz u v
    exact h.symm (ψ z) _ _
  · intro z hz
    obtain ⟨L, hL⟩ := (ψ.isLocalDiffeomorphAt _ _ _ hz).isInvertible_mfderiv (by norm_num)
    apply ContinuousLinearMap.isCoercive_of_posDef
    intro v hv
    simp only [ContinuousLinearMap.bilinearComp_apply]
    apply h.pos
    intro h0
    apply hv
    have hLv : L v = 0 := by
      rw [← ContinuousLinearEquiv.coe_coe, hL]
      exact h0
    simpa using congrArg L.symm hLv

/-- **Naturality of the finite-order sectional curvature across model spaces.** -/
theorem sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross
    (g : ContMDiffRiemannianMetric I n V (TangentSpace I : M → Type _))
    (h : ContMDiffRiemannianMetric J m E (TangentSpace J : N → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (hm : (2 : ℕ∞ω) ≤ m)
    (f : PartialDiffeomorph I J M N 3)
    (hmetric : ∀ q ∈ f.source, ∀ v w : TangentSpace I q,
      g.inner q v w = h.inner (f q) (mfderiv I J f q v) (mfderiv I J f q w))
    {p : M} (hp : p ∈ f.source) (v w : TangentSpace I p) :
    g.sectionalCurvature p v w =
      h.sectionalCurvature (f p) (mfderiv I J f p v) (mfderiv I J f p w) := by
  let κ := DifferentialGeometry.PartialDiffeomorph.extChartAt I 3 p
  let ψ := DifferentialGeometry.PartialDiffeomorph.extChartAt J 3 (f p)
  let T := (κ.symm.trans f).trans ψ
  have hκp : p ∈ κ.source := mem_extChartAt_source p
  have hψp : f p ∈ ψ.source := mem_extChartAt_source (f p)
  rw [ContMDiffRiemannianMetric.sectionalCurvature_eq_coefficientSectional g hn κ hκp,
    ContMDiffRiemannianMetric.sectionalCurvature_eq_coefficientSectional h hm ψ hψp]
  have hκpp : κ.symm (κ p) = p := κ.left_inv hκp
  have hTx : κ p ∈ T.source := by
    refine ⟨⟨κ.map_source hκp, ?_⟩, ?_⟩
    · change κ.symm (κ p) ∈ f.source
      rw [hκpp]
      exact hp
    · change f (κ.symm (κ p)) ∈ ψ.source
      rw [hκpp]
      exact hψp
  have hTp : T (κ p) = ψ (f p) := by
    change ψ (f (κ.symm (κ p))) = ψ (f p)
    rw [hκpp]
  have hDT : ∀ u : TangentSpace I p,
      fderiv ℝ T (κ p) (mfderiv I 𝓘(ℝ, V) κ p u) = mfderiv J 𝓘(ℝ, E) ψ (f p)
        (mfderiv I J f p u) := by
    intro u
    have heq : T ∘ κ =ᶠ[𝓝 p] ψ ∘ f := by
      filter_upwards [κ.open_source.mem_nhds hκp] with q hq
      exact congrArg (fun x => ψ (f x)) (κ.left_inv hq)
    have h1 := mfderiv_comp p (T.mdifferentiableAt (by norm_num) hTx)
      (κ.mdifferentiableAt (by norm_num) hκp)
    have h2 := mfderiv_comp p (ψ.mdifferentiableAt (by norm_num) hψp)
      (f.mdifferentiableAt (by norm_num) hp)
    have h3 := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, E))
    rw [h1, h2, mfderiv_eq_fderiv] at h3
    exact congrArg (fun L => L u) h3
  rw [← hDT v, ← hDT w, ← hTp]
  obtain ⟨hc, hcsymm, hcco⟩ := chartCoefficient_properties h hm ψ.symm
  have hTsrc : ∀ y ∈ T.source, κ.symm y ∈ f.source ∧ f (κ.symm y) ∈ ψ.source :=
    fun y hy => ⟨hy.1.2, hy.2⟩
  apply DifferentialGeometry.Analysis.coefficientSectional_transition_cross T.open_source
    ψ.symm.open_source hc hcsymm hcco T.contMDiffOn.contDiffOn
    (fun y hy => ψ.map_source (hTsrc y hy).2)
    (fun y hy => by
      have h1 := (T.isLocalDiffeomorphAt _ _ _ hy).isInvertible_mfderiv (by norm_num)
      rw [mfderiv_eq_fderiv] at h1
      exact h1)
    _ hTx
  intro y hy u u'
  obtain ⟨hyf, hyψ⟩ := hTsrc y hy
  have hTy : ψ.symm (T y) = f (κ.symm y) := ψ.left_inv hyψ
  have hTyt : T y ∈ ψ.symm.source := ψ.map_source hyψ
  have heq : ψ.symm ∘ T =ᶠ[𝓝 y] f ∘ κ.symm := by
    filter_upwards [T.open_source.mem_nhds hy] with y' hy'
    exact ψ.left_inv hy'.2
  have hd1 := mfderiv_comp y (ψ.symm.mdifferentiableAt (by norm_num) hTyt)
    (T.mdifferentiableAt (by norm_num) hy)
  have hd2 := mfderiv_comp y (f.mdifferentiableAt (by norm_num) hyf)
    (κ.symm.mdifferentiableAt (by norm_num) hy.1.1)
  have hd := heq.mfderiv_eq (I := 𝓘(ℝ, V)) (I' := J)
  rw [hd1, hd2, mfderiv_eq_fderiv] at hd
  have hdu : ∀ a : V, mfderiv 𝓘(ℝ, E) J ψ.symm (T y) (fderiv ℝ T y a) =
      mfderiv I J f (κ.symm y) (mfderiv 𝓘(ℝ, V) I κ.symm y a) := fun a =>
    congrArg (fun L => L a) hd
  change g.inner (κ.symm y) (mfderiv 𝓘(ℝ, V) I κ.symm y u) (mfderiv 𝓘(ℝ, V) I κ.symm y u') =
    h.inner (ψ.symm (T y)) (mfderiv 𝓘(ℝ, E) J ψ.symm (T y) (fderiv ℝ T y u))
      (mfderiv 𝓘(ℝ, E) J ψ.symm (T y) (fderiv ℝ T y u'))
  rw [hmetric _ hyf, hdu u, hdu u', hTy]

end Cross

section ProductChart

variable {F P Z : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [TopologicalSpace Z] [ChartedSpace P Z] [IsManifold 𝓘(ℝ, P) 3 Z] {n m : ℕ∞ω}

/-- **Product curvature in a product chart.** For a finite metric `G` on `F × Z` with
`G = du² + h`, the curvature of `G` on planes tangent to `Z` is that of `h`. -/
theorem sectionalCurvature_prod_snd_of_inner
    (h : ContMDiffRiemannianMetric 𝓘(ℝ, P) n P (TangentSpace 𝓘(ℝ, P) : Z → Type _))
    (G : ContMDiffRiemannianMetric (𝓘(ℝ, F).prod 𝓘(ℝ, P)) m (F × P)
      (TangentSpace (𝓘(ℝ, F).prod 𝓘(ℝ, P)) : F × Z → Type _))
    (hn : (2 : ℕ∞ω) ≤ n) (hm : (2 : ℕ∞ω) ≤ m)
    (hG : ∀ (q : F × Z) (v w : TangentSpace (𝓘(ℝ, F).prod 𝓘(ℝ, P)) q),
      G.inner q v w = inner ℝ v.1 w.1 + h.inner q.2 v.2 w.2)
    (u : F) (z : Z) (v w : P) :
    G.sectionalCurvature (u, z) (((0 : F), v) : F × P) (((0 : F), w) : F × P) =
      h.sectionalCurvature z v w := by
  let κ := DifferentialGeometry.PartialDiffeomorph.extChartAt 𝓘(ℝ, P) 3 z
  let χ := DifferentialGeometry.PartialDiffeomorph.extChartAt (𝓘(ℝ, F).prod 𝓘(ℝ, P)) 3 (u, z)
  have hκz : z ∈ κ.source := mem_extChartAt_source z
  have hχz : (u, z) ∈ χ.source := mem_extChartAt_source (u, z)
  refine (ContMDiffRiemannianMetric.sectionalCurvature_eq_coefficientSectional G hm χ hχz
    _ _).trans ((ContMDiffRiemannianMetric.sectionalCurvature_eq_coefficientSectional h hn κ hκz
    _ _).trans ?_).symm
  have hχd : mfderiv (𝓘(ℝ, F).prod 𝓘(ℝ, P)) 𝓘(ℝ, F × P) χ (u, z) =
      ContinuousLinearMap.id ℝ _ := mfderiv_extChartAt_self
  have hκd : mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) κ z = ContinuousLinearMap.id ℝ _ :=
    mfderiv_extChartAt_self
  rw [hχd, hκd]
  have hχsymm : (χ.symm : F × P → F × Z) = fun y => (y.1, κ.symm y.2) := by
    funext y
    change (extChartAt (𝓘(ℝ, F).prod 𝓘(ℝ, P)) (u, z)).symm y =
      (y.1, (extChartAt 𝓘(ℝ, P) z).symm y.2)
    rw [extChartAt_prod, extChartAt_model_space_eq_id]
    rfl
  have hχpt : χ (u, z) = (u, κ z) := by
    change extChartAt (𝓘(ℝ, F).prod 𝓘(ℝ, P)) (u, z) (u, z) = (u, extChartAt 𝓘(ℝ, P) z z)
    rw [extChartAt_prod, extChartAt_model_space_eq_id]
    rfl
  obtain ⟨hc, hcsymm, hcco⟩ := chartCoefficient_properties h hn κ.symm
  have hb : ∀ y : F × P, y.2 ∈ κ.symm.source → ∀ a a' : F × P,
      (G.inner (χ.symm y) : (F × P) →L[ℝ] (F × P) →L[ℝ] ℝ).bilinearComp
          (mfderiv 𝓘(ℝ, F × P) (𝓘(ℝ, F).prod 𝓘(ℝ, P)) χ.symm y : (F × P) →L[ℝ] (F × P))
          (mfderiv 𝓘(ℝ, F × P) (𝓘(ℝ, F).prod 𝓘(ℝ, P)) χ.symm y : (F × P) →L[ℝ] (F × P)) a a' =
        inner ℝ a.1 a'.1 +
          (h.inner (κ.symm y.2) : P →L[ℝ] P →L[ℝ] ℝ).bilinearComp
            (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) κ.symm y.2 : P →L[ℝ] P)
            (mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) κ.symm y.2 : P →L[ℝ] P) a.2 a'.2 := by
    intro y hy a a'
    have hκs : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, P) κ.symm y.2 :=
      κ.symm.mdifferentiableAt (by norm_num) hy
    have hD : ∀ a : F × P, mfderiv 𝓘(ℝ, F × P) (𝓘(ℝ, F).prod 𝓘(ℝ, P)) χ.symm y a =
        (a.1, mfderiv 𝓘(ℝ, P) 𝓘(ℝ, P) κ.symm y.2 a.2) := by
      intro a
      rw [hχsymm]
      have hfst : MDifferentiableAt 𝓘(ℝ, F × P) 𝓘(ℝ, F) (fun y : F × P => y.1) y :=
        (contDiff_fst (𝕜 := ℝ) (E := F) (F := P)).contMDiff.mdifferentiableAt (n := 1)
          one_ne_zero
      have hsn : MDifferentiableAt 𝓘(ℝ, F × P) 𝓘(ℝ, P) (Prod.snd : F × P → P) y :=
        (contDiff_snd (𝕜 := ℝ) (E := F) (F := P)).contMDiff.mdifferentiableAt (n := 1)
          one_ne_zero
      have hsnd : MDifferentiableAt 𝓘(ℝ, F × P) 𝓘(ℝ, P) (fun y : F × P => κ.symm y.2) y :=
        hκs.comp y hsn
      rw [mfderiv_prodMk hfst hsnd,
        show (fun y : F × P => κ.symm y.2) = κ.symm ∘ Prod.snd from rfl,
        mfderiv_comp y hκs hsn, mfderiv_eq_fderiv, mfderiv_eq_fderiv, fderiv_fst, fderiv_snd]
      rfl
    change G.inner (χ.symm y) (mfderiv 𝓘(ℝ, F × P) (𝓘(ℝ, F).prod 𝓘(ℝ, P)) χ.symm y a)
        (mfderiv 𝓘(ℝ, F × P) (𝓘(ℝ, F).prod 𝓘(ℝ, P)) χ.symm y a') = _
    rw [hD a, hD a']
    refine (hG _ _ _).trans ?_
    have hy2 : (χ.symm y).2 = κ.symm y.2 := by rw [hχsymm]
    rw [hy2]
    rfl
  have hzt : (u, κ z).2 ∈ κ.symm.source := κ.map_source hκz
  rw [hχpt]
  exact (Analysis.coefficientSectional_prod_snd κ.symm.open_source hc hcsymm hcco hb hzt v w).symm

end ProductChart

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
private theorem factor_two_le_succ (hr : 2 ≤ r) : (2 : ℕ∞ω) ≤ (r : ℕ∞ω) + 1 := by
  have h : ((2 : ℕ∞) : ℕ∞ω) ≤ ((r + 1 : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr (le_add_right hr)
  simpa only [WithTop.coe_ofNat, WithTop.coe_add, WithTop.coe_one] using h

omit [CompleteSpace M] in
private theorem factor_three_le_add_two (hr : 2 ≤ r) : (3 : ℕ∞ω) ≤ (r : ℕ∞ω) + 2 := by
  have h3 : (3 : ℕ∞) ≤ r + 2 := by
    have h1 : (1 : ℕ∞) ≤ r := le_trans (by norm_num) hr
    calc (3 : ℕ∞) = 1 + 2 := by norm_num
      _ ≤ r + 2 := add_le_add_left h1 2
  have h : ((3 : ℕ∞) : ℕ∞ω) ≤ ((r + 2 : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr h3
  simpa only [WithTop.coe_ofNat, WithTop.coe_add] using h

/-- The ambient curvature through the whole product diffeomorphism of tier T3. -/
theorem splittingProductMetric_sectionalCurvature_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (p : F × {x : M // (e x).fst = 0}) (v w : TangentSpace IP p),
      (splittingProductMetric g hr hnorm e).sectionalCurvature p v w =
        g.sectionalCurvature (splittingProductDiffeomorph g hr hnorm e p)
          (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p v)
          (mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) p w) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  let _ : IsManifold IZ 3 {x : M // (e x).fst = 0} := IsManifold.of_le (factor_three_le_add_two hr)
  intro p v w
  let Ψ := splittingProductDiffeomorph g hr hnorm e
  let f : PartialDiffeomorph IP I (F × {x : M // (e x).fst = 0}) M 3 :=
    DifferentialGeometry.PartialDiffeomorph.ofLE Ψ.toPartialDiffeomorph (factor_three_le_add_two hr)
  exact sectionalCurvature_eq_of_partialDiffeomorph_pullback_cross
    (splittingProductMetric g hr hnorm e) g (factor_two_le_succ hr) (factor_two_le_succ hr) f
    (fun q _ v' w' => (splittingProductMetric_inner g hr hnorm e q v' w').trans
      (splittingProductDiffeomorph_metric g hr hnorm e q v' w').symm)
    (Set.mem_univ p) v w


omit [IsManifold I ∞ M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NeZero (Module.finrank ℝ E)] in
/-- On the zero slice the product map is the inclusion of the zero factor. -/
theorem splittingProductMap_zero (e : M ≃ᵢ WithLp 2 (F × Y)) (z : {x : M // (e x).fst = 0}) :
    splittingProductMap e ((0 : F), z) = z.val := by
  have hz : toLp 2 ((0 : F), (e z.val).snd) = e z.val := by
    obtain ⟨x, hx⟩ := z
    change toLp 2 ((0 : F), (e x).snd) = e x
    rw [← hx]
    rfl
  change e.symm (toLp 2 ((0 : F), (e z.val).snd)) = z.val
  rw [hz, e.symm_apply_apply]

theorem splittingProductDiffeomorph_zero
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (z : {x : M // (e x).fst = 0}) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    splittingProductDiffeomorph g hr hnorm e ((0 : F), z) = z.val := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  have h1 : (splittingProductDiffeomorph g hr hnorm e : F × {x : M // (e x).fst = 0} → M) =
      splittingProductMap e := by
    funext p
    change (splittingProductDiffeomorph g hr hnorm e).toEquiv p = _
    rw [splittingProductDiffeomorph_toEquiv]
    rfl
  rw [h1]
  exact splittingProductMap_zero e z

/-- The differential of the product map on the zero slice is the differential of the inclusion. -/
theorem mfderiv_splittingProductDiffeomorph_zero
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (z : {x : M // (e x).fst = 0}) (v : TangentSpace IZ z),
      mfderiv IP I (splittingProductDiffeomorph g hr hnorm e) ((0 : F), z)
          (((0 : F), v) : F × P) =
        mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z v := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  intro z v
  let Ψ := splittingProductDiffeomorph g hr hnorm e
  let ι₀ : {x : M // (e x).fst = 0} → F × {x : M // (e x).fst = 0} := fun z' => ((0 : F), z')
  have hcomp : (Ψ : F × {x : M // (e x).fst = 0} → M) ∘ ι₀ = Subtype.val :=
    funext fun z' => splittingProductDiffeomorph_zero g hr hnorm e z'
  have hΨ : MDifferentiableAt IP I Ψ (ι₀ z) :=
    Ψ.contMDiff.mdifferentiableAt (by simp)
  have hc : MDifferentiableAt IZ 𝓘(ℝ, F) (fun _ : {x : M // (e x).fst = 0} => (0 : F)) z :=
    mdifferentiableAt_const
  have hi : MDifferentiableAt IZ IZ (id : {x : M // (e x).fst = 0} → _) z :=
    mdifferentiableAt_id
  have hι : MDifferentiableAt IZ IP ι₀ z := hc.prodMk hi
  have hd := mfderiv_comp z hΨ hι
  rw [hcomp] at hd
  rw [hd]
  change mfderiv IP I Ψ (ι₀ z) (((0 : F), v) : F × P) =
    mfderiv IP I Ψ (ι₀ z) (mfderiv IZ IP ι₀ z v)
  congr 1
  rw [show ι₀ = fun z' => ((fun _ : {x : M // (e x).fst = 0} => (0 : F)) z', id z') from rfl,
    mfderiv_prodMk hc hi, mfderiv_const, mfderiv_id]
  rfl

/-- **LFR11 tier T4 (curvature).** The zero factor carries the ambient sectional curvature on
its tangent planes. -/
theorem inducedMetric_sectionalCurvature_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      (inducedMetric g hr hnorm e).sectionalCurvature z v w =
        g.sectionalCurvature z.val
          (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z v)
          (mfderiv IZ I (Subtype.val : {x : M // (e x).fst = 0} → M) z w) := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  let _ : IsManifold IZ ((r : ℕ∞ω) + 2) {x : M // (e x).fst = 0} :=
    splittingFactor_isManifold g hr hnorm e
  let _ : IsManifold IZ 3 {x : M // (e x).fst = 0} := IsManifold.of_le (factor_three_le_add_two hr)
  intro z v w
  have h1 := sectionalCurvature_prod_snd_of_inner (inducedMetric g hr hnorm e)
    (splittingProductMetric g hr hnorm e) (factor_two_le_succ hr) (factor_two_le_succ hr)
    (splittingProductMetric_inner g hr hnorm e) (0 : F) z v w
  have h2 := splittingProductMetric_sectionalCurvature_eq g hr hnorm e ((0 : F), z)
    (((0 : F), v) : F × P) (((0 : F), w) : F × P)
  have key : ∀ p q : M, p = q → ∀ a b : E, g.sectionalCurvature p a b = g.sectionalCurvature q a b :=
    by rintro p q rfl a b; rfl
  refine h1.symm.trans (h2.trans ?_)
  rw [mfderiv_splittingProductDiffeomorph_zero g hr hnorm e z v,
    mfderiv_splittingProductDiffeomorph_zero g hr hnorm e z w]
  exact key _ _ (splittingProductDiffeomorph_zero g hr hnorm e z) _ _

/-- **LFR11 tier T4 (sign).** Nonnegative ambient sectional curvature passes to the zero
factor. -/
theorem inducedMetric_sectionalCurvature_nonneg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (e : M ≃ᵢ WithLp 2 (F × Y))
    (hsec : ∀ (x : M) (v w : TangentSpace I x), 0 ≤ g.sectionalCurvature x v w) :
    letI := splittingFactorChartedSpace g hr hnorm e
    letI := splittingFactor_isManifold_one g hr hnorm e
    ∀ (z : {x : M // (e x).fst = 0}) (v w : TangentSpace IZ z),
      0 ≤ (inducedMetric g hr hnorm e).sectionalCurvature z v w := by
  let _ := splittingFactorChartedSpace g hr hnorm e
  let _ := splittingFactor_isManifold_one g hr hnorm e
  intro z v w
  rw [inducedMetric_sectionalCurvature_eq g hr hnorm e z v w]
  exact hsec _ _ _

end Splitting

end DifferentialGeometry.Geometry.ExactSplitting
