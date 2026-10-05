import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierRechart
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.ChartCoefficientTransfer

/-!
# LFR49 noncompact branch, item (a): chart transfer of the coefficient convergence to a carrier

Frozen blueprint master207A, LFR49 (A:29096): "At this FIXED `R`, restrict LFR48's maps to a
neighborhood of the closed radius-`10R` model ball. LC50's minimizing-direction argument uses only
`C¹` metric convergence … It applies to this `C^{K-5}` metric". The comparison maps `j_i : N → Y_i`
converge in the charts of `N`; read on a carrier `Nc` through a `C^s` diffeomorphism `Φ : Nc ≃ N`
(LFR47's identity of the points), the maps `j_i ∘ Φ` converge in the charts of `Nc` to the
transported metric `Φ^* G`, with the order `m` kept as long as `m + 1 ≤ s` (one derivative of `Φ`
enters the metric coefficients).

* `chartCoeff_eqOn_of_diffeomorph`: on an open set `U` of a chart target of `Nc` whose image lies in
  one chart domain of `N`, the chart coefficients of `Φ^* G` are `τ^*` of those of `G`,
  `τ = chart_N ∘ Φ ∘ chart_Nc⁻¹`;
* `mapCPConvergenceOn_chartCoeff_of_diffeomorph` (kernel): the transfer of the `C^m` convergence;
  pieces are compact subsets of the open overlaps
  `target ∩ (Φ ∘ chart⁻¹)⁻¹ (chart_x.source ∩ ball (Φ y) k)` (`ProperSpace N` gives a common
  regularity tail on `closedBall (Φ y) k`), composed by
  `mapCPConvergenceOn_pullbackMetricCoefficients_comp`;
* `CarrierRechart.mapCPConvergenceOn_chartCoeff`: the kernel on the re-charted carrier, `Φ` the
  identity of the points, `Φ^* G = CarrierRechart.metric`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open GC.MetricGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Chart coefficients through a diffeomorphism.** If `Gc = Φ^* G` for a differentiable
diffeomorphism `Φ : Nc ≃ N`, then on every open set `U` of the target of the extended chart at
`y : Nc` on which `Φ ∘ chart⁻¹` lands in the chart domain at `x : N`, the chart coefficients of
`Gc` are `τ^*` of those of `G`, `τ = chart_x ∘ Φ ∘ chart_y⁻¹`, provided `τ` is differentiable
on `U`. -/
theorem chartCoeff_eqOn_of_diffeomorph
    {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    {Nc : Type*} [TopologicalSpace Nc] [ChartedSpace E Nc] [IsManifold 𝓘(ℝ, E) ∞ Nc]
    {s n nc : ℕ∞ω} (hs : s ≠ 0) (Φ : Nc ≃ₘ^s⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (Gc : ContMDiffRiemannianMetric 𝓘(ℝ, E) nc E (TangentSpace 𝓘(ℝ, E) : Nc → Type _))
    (hGc : ∀ (z : Nc) (v w : TangentSpace 𝓘(ℝ, E) z), Gc.inner z v w =
      G.inner (Φ z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w))
    (y : Nc) (x : N) {U : Set E} (hU : IsOpen U) (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) y).target)
    (hUx : MapsTo (Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm) U (extChartAt 𝓘(ℝ, E) x).source)
    (hτ : DifferentiableOn ℝ
      (extChartAt 𝓘(ℝ, E) x ∘ Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm) U) :
    EqOn (chartCoeff Gc y)
      (fun u =>
        (chartCoeff G x ((extChartAt 𝓘(ℝ, E) x ∘ Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm) u)).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) x ∘ Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm) u)
        (fderiv ℝ (extChartAt 𝓘(ℝ, E) x ∘ Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm) u)) U := by
  intro u hu
  set c := extChartAt 𝓘(ℝ, E) x with hc
  set cy := extChartAt 𝓘(ℝ, E) y with hcy
  set τ := c ∘ Φ ∘ cy.symm with hτdef
  have hcu : Φ (cy.symm u) ∈ c.source := hUx hu
  have hτu : τ u ∈ c.target := c.map_source hcu
  have hcτ : c.symm (τ u) = Φ (cy.symm u) := c.left_inv hcu
  -- `Φ ∘ chart_y⁻¹ = chart_x⁻¹ ∘ τ` near `u`
  have hgerm : (⇑Φ ∘ cy.symm) =ᶠ[𝓝 u] c.symm ∘ τ := by
    filter_upwards [hU.mem_nhds hu] with u' hu'
    exact (c.left_inv (hUx hu')).symm
  have hcyd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) cy.symm u :=
    ((contMDiffOn_extChartAt_symm (n := 1) y).contMDiffAt
      ((isOpen_extChartAt_target y).mem_nhds (hUt hu))).mdifferentiableAt one_ne_zero
  have hcd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (τ u) :=
    ((contMDiffOn_extChartAt_symm (n := 1) x).contMDiffAt
      ((isOpen_extChartAt_target x).mem_nhds hτu)).mdifferentiableAt one_ne_zero
  have hτd : DifferentiableAt ℝ τ u := (hτ u hu).differentiableAt (hU.mem_nhds hu)
  have hd1 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (⇑Φ ∘ cy.symm) u =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (cy.symm u)).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) cy.symm u) :=
    mfderiv_comp u (Φ.mdifferentiable hs (cy.symm u)) hcyd
  have hd2 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (c.symm ∘ τ) u =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (τ u)).comp (fderiv ℝ τ u) := by
    rw [mfderiv_comp u hcd hτd.mdifferentiableAt, mfderiv_eq_fderiv]
    rfl
  have hD : ∀ v : E, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ (cy.symm u) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) cy.symm u v) =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (τ u) (fderiv ℝ τ u v) := by
    intro v
    have h := congrArg (fun T : E →L[ℝ] E => T v) (hgerm.mfderiv_eq.trans hd2)
    rw [hd1] at h
    exact h
  have key : ∀ p p' : N, p = p' → ∀ v w : E, G.inner p v w = G.inner p' v w := by
    rintro p _ rfl v w
    rfl
  ext v w
  rw [chartCoeff_apply, ContinuousLinearMap.bilinearComp_apply, chartCoeff_apply, hGc, hD, hD]
  exact key _ _ hcτ.symm _ _

/-- **Chart transfer of the coefficient convergence along a `C^s` diffeomorphism (kernel).**
Let `N` be proper, `Φ : Nc ≃ N` a `C^s` diffeomorphism, `Gc = Φ^* G`, and `j i : N → Y i` partial
diffeomorphisms of order `k ≥ m + 1` whose sources eventually contain every compact set and whose
pulled-back coefficients converge in `C^m` to the chart coefficients of `G` on the compacts of every
extended chart of `N`. If `m + 1 ≤ s` and `m ≤ n`, then the coefficients of `g i` pulled back along
`j i ∘ Φ ∘ chart⁻¹` converge in `C^m` to the chart coefficients of `Gc` on every compact subset of
every extended chart target of `Nc`. -/
theorem mapCPConvergenceOn_chartCoeff_of_diffeomorph [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    {Nc : Type*} [TopologicalSpace Nc] [ChartedSpace E Nc] [IsManifold 𝓘(ℝ, E) ∞ Nc]
    {m : ℕ} {s n nc : ℕ∞ω} (hms : (m : ℕ∞ω) + 1 ≤ s) (hmn : (m : ℕ∞ω) ≤ n)
    (Φ : Nc ≃ₘ^s⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ N)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (Gc : ContMDiffRiemannianMetric 𝓘(ℝ, E) nc E (TangentSpace 𝓘(ℝ, E) : Nc → Type _))
    (hGc : ∀ (z : Nc) (v w : TangentSpace 𝓘(ℝ, E) z), Gc.inner z v w =
      G.inner (Φ z) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z v) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ z w))
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {k : ℕ∞ω} (hmk : (m : ℕ∞ω) + 1 ≤ k)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) k)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L m
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (y : Nc) {L : Set E} (hL : IsCompact L) (hLt : L ⊆ (extChartAt 𝓘(ℝ, E) y).target) :
    MapCPConvergenceOn L m
      (fun i => pullbackMetricCoefficients (g i)
        ((j i : N → Y i) ∘ Φ ∘ (extChartAt 𝓘(ℝ, E) y).symm))
      (chartCoeff Gc y) := by
  have hm1 : (((m + 1 : ℕ) : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 := by push_cast; rfl
  have hs0 : s ≠ 0 := fun h0 => by
    have h1 : (1 : ℕ∞ω) ≤ s := le_trans le_add_self hms
    rw [h0] at h1
    exact (not_le.mpr zero_lt_one) h1
  have hle : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have : IsManifold 𝓘(ℝ, E) ((m + 1 : ℕ) : ℕ∞ω) N := IsManifold.of_le hle
  have : IsManifold 𝓘(ℝ, E) ((m + 1 : ℕ) : ℕ∞ω) Nc := IsManifold.of_le hle
  set cy := extChartAt 𝓘(ℝ, E) y with hcy
  set p₀ : N := Φ y with hp₀
  -- the open overlaps
  let U : N × ℕ → Set E := fun xk =>
    cy.target ∩ (⇑Φ ∘ cy.symm) ⁻¹' ((extChartAt 𝓘(ℝ, E) xk.1).source ∩ ball p₀ (xk.2 : ℝ))
  have hΦcy : ContinuousOn (⇑Φ ∘ cy.symm) cy.target :=
    Φ.continuous.comp_continuousOn (continuousOn_extChartAt_symm y)
  have hUo : ∀ xk, IsOpen (U xk) := fun xk =>
    hΦcy.isOpen_inter_preimage (isOpen_extChartAt_target y)
      ((isOpen_extChartAt_source xk.1).inter isOpen_ball)
  refine mapCPConvergenceOn_of_isCompact_subset_sUnion (S := range U)
    (by rintro _ ⟨xk, rfl⟩; exact hUo xk) ?_ hL ?_
  · rintro _ ⟨⟨x, r⟩, rfl⟩ Q hQ hQU
    set c := extChartAt 𝓘(ℝ, E) x with hc
    let τ : E → E := c ∘ Φ ∘ cy.symm
    let V : Set E := c.target ∩ c.symm ⁻¹' ball p₀ (r : ℝ)
    have hVo : IsOpen V :=
      (continuousOn_extChartAt_symm x).isOpen_inter_preimage (isOpen_extChartAt_target x)
        isOpen_ball
    have hUx : MapsTo (⇑Φ ∘ cy.symm) (U (x, r)) c.source := fun u hu => hu.2.1
    -- the coordinate change is `C^{m+1}` on the open overlap
    have hτs : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ((m + 1 : ℕ) : ℕ∞ω) τ (U (x, r)) := by
      have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ((m + 1 : ℕ) : ℕ∞ω) (⇑Φ ∘ cy.symm) (U (x, r)) :=
        (Φ.contMDiff.of_le (by rw [hm1]; exact hms)).comp_contMDiffOn
          ((contMDiffOn_extChartAt_symm y).mono inter_subset_left)
      exact (contMDiffOn_extChartAt (x := x)).comp h1
        (fun u hu => by
          have h := hUx hu
          rw [hc, extChartAt_source] at h
          exact h)
    have hτ : ContDiffOn ℝ ((m + 1 : ℕ) : ℕ∞ω) τ (U (x, r)) := contMDiffOn_iff_contDiffOn.mp hτs
    have hτUV : MapsTo τ (U (x, r)) V := by
      intro u hu
      have hcu : Φ (cy.symm u) ∈ c.source := hu.2.1
      refine ⟨c.map_source hcu, ?_⟩
      change c.symm (c (Φ (cy.symm u))) ∈ ball p₀ (r : ℝ)
      rw [c.left_inv hcu]
      exact hu.2.2
    -- the common regularity tail, from the compact `closedBall p₀ r`
    have hf : ∀ᶠ i in atTop, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ((m + 1 : ℕ) : ℕ∞ω)
        ((j i : N → Y i) ∘ c.symm) V := by
      filter_upwards [hexh _ (isCompact_closedBall p₀ (r : ℝ))] with i hi
      exact ((j i).contMDiffOn.of_le (by rw [hm1]; exact hmk)).comp
        ((contMDiffOn_extChartAt_symm x).mono inter_subset_left)
        (fun v hv => hi (ball_subset_closedBall hv.2))
    have hB : ContDiffOn ℝ m (chartCoeff G x) V :=
      (G.contDiffOn_pullback_inner hmn hm1.symm.le (isOpen_extChartAt_target x)
        (contMDiffOn_extChartAt_symm (n := ((m + 1 : ℕ) : ℕ∞ω)) x)).mono inter_subset_left
    have hmain := mapCPConvergenceOn_pullbackMetricCoefficients_comp g
      (fun i => (j i : N → Y i) ∘ c.symm) τ (hUo (x, r)) hVo hτ hτUV hf (chartCoeff G x) hB
      (fun S hS hSV => hconv x S hS (hSV.trans inter_subset_left)) hQ hQU
    refine hmain.congr (hUo (x, r)) hQU (fun i u hu => ?_) ?_
    · -- the maps agree on the open overlap, hence their coefficients agree there
      have hgerm : ((j i : N → Y i) ∘ ⇑Φ ∘ cy.symm) =ᶠ[𝓝 u]
          (((j i : N → Y i) ∘ c.symm) ∘ τ) := by
        filter_upwards [(hUo (x, r)).mem_nhds hu] with u' hu'
        have hr : c.symm (c (Φ (cy.symm u'))) = Φ (cy.symm u') := c.left_inv hu'.2.1
        change j i (Φ (cy.symm u')) = j i (c.symm (c (Φ (cy.symm u'))))
        rw [hr]
      exact pullbackMetricCoefficients_eq_of_eventuallyEq (g i) hgerm
    · exact chartCoeff_eqOn_of_diffeomorph hs0 Φ G Gc hGc y x (hUo (x, r)) inter_subset_left
        hUx (hτ.differentiableOn (by simp))
  · intro u hu
    obtain ⟨r, hr⟩ := exists_nat_gt (dist (Φ (cy.symm u)) p₀)
    exact ⟨U (Φ (cy.symm u), r), ⟨(Φ (cy.symm u), r), rfl⟩, hLt hu,
      mem_extChartAt_source _, mem_ball.mpr hr⟩

/-- **The transfer on the re-charted carrier.** For `N' = CarrierRechart e Λ`, `Φ` the `C^s`
identity of the points and `G' = CarrierRechart.metric`: the coefficients of `g i` pulled back along
`j i ∘ Φ ∘ chart⁻¹` converge in `C^m` to the chart coefficients of `G'` (`m + 1 ≤ s`, `m ≤ n`). -/
theorem CarrierRechart.mapCPConvergenceOn_chartCoeff [FiniteDimensional ℝ E]
    {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd EB F) X]
    [IsManifold (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ X]
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (Λ : (EB × F) ≃L[ℝ] E) {s : ℕ∞} (e : X ≃ₘ^s⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), 𝓘(ℝ, E)⟯ N)
    {m : ℕ} {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hmn : (m : ℕ∞ω) ≤ n) (hms : (m : ℕ∞ω) + 1 ≤ s)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)] (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {k : ℕ∞ω} (hmk : (m : ℕ∞ω) + 1 ≤ k)
    (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) k)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L m
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → Y i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (y : CarrierRechart e.toHomeomorph Λ) {L : Set E} (hL : IsCompact L)
    (hLt : L ⊆ (extChartAt 𝓘(ℝ, E) y).target) :
    MapCPConvergenceOn L m
      (fun i => pullbackMetricCoefficients (g i)
        ((j i : N → Y i) ∘ CarrierRechart.identity Λ e ∘ (extChartAt 𝓘(ℝ, E) y).symm))
      (chartCoeff (CarrierRechart.metric Λ e G hmn hms) y) :=
  mapCPConvergenceOn_chartCoeff_of_diffeomorph hms hmn (CarrierRechart.identity Λ e) G
    (CarrierRechart.metric Λ e G hmn hms) (fun _ _ _ => rfl) g hmk j hexh hconv y hL hLt

end DifferentialGeometry.Geometry.Collapse
