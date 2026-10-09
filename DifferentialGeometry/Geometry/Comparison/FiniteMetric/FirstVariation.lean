import DifferentialGeometry.Geometry.Comparison.FiniteMetric.MinimizingDirections
import Mathlib.Topology.MetricSpace.Sequences
import DifferentialGeometry.Analysis.Calculus.DistanceSmoothing.SeminormMollification

/-!
# First variation of the distance to a closed set for a metric of finite order (CM3.c)
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Analysis.Calculus

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- A curve with velocity `X` at `0`, read in the chart at `γ 0`. -/
theorem hasDerivAt_extChartAt_comp_of_hasMFDerivAt {γ : ℝ → M} {X : E}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) :
    HasDerivAt (fun t => extChartAt I (γ 0) (γ t)) X 0 := by
  have h2 : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I (γ 0)) (γ 0)
      (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ 0)) (γ 0)) :=
    (mdifferentiableAt_extChartAt (mem_chart_source H (γ 0))).hasMFDerivAt
  have h3 : HasFDerivAt (fun t => extChartAt I (γ 0) (γ t))
      (show ℝ →L[ℝ] E from (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ 0)) (γ 0)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight X)) 0 :=
    hasMFDerivAt_iff_hasFDerivAt.mp (h2.comp 0 hγ)
  convert h3.hasDerivAt using 1
  change X = (mfderiv I 𝓘(ℝ, E) (extChartAt I (γ 0)) (γ 0)) (((1 : ℝ →L[ℝ] ℝ).smulRight X) 1)
  rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul, mfderiv_extChartAt_self]
  rfl

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The chord estimate: `N_x(w + δ X) ≤ 1 + η/2 + δ b + δ² g_x(X, X)/2` when `g_x(w, w) ≤ 1 + η`
and `g_x(w, X) ≤ b`. -/
theorem finiteMetricSeminormAt_add_smul_le {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) {w X : E}
    {δ η b : ℝ} (hw : g.inner x w w ≤ 1 + η) (hwX : g.inner x w X ≤ b) (hδ : 0 ≤ δ) :
    finiteMetricSeminormAt g x (w + δ • X) ≤ 1 + η / 2 + δ * b + δ ^ 2 * g.inner x X X / 2 := by
  have hexp : finiteMetricFormAt g x (w + δ • X) (w + δ • X) =
      finiteMetricFormAt g x w w + 2 * δ * finiteMetricFormAt g x w X +
        δ ^ 2 * finiteMetricFormAt g x X X := by
    have hs : finiteMetricFormAt g x X w = finiteMetricFormAt g x w X := g.symm x X w
    simp only [map_add, map_smul, add_apply, smul_apply,
      smul_eq_mul, hs]
    ring
  have hXX : 0 ≤ g.inner x X X := finite_inner_self_nonneg g x X
  have hpos : 0 ≤ finiteMetricFormAt g x (w + δ • X) (w + δ • X) :=
    finite_inner_self_nonneg g x _
  change Real.sqrt (finiteMetricFormAt g x (w + δ • X) (w + δ • X)) ≤ _
  have hw' : finiteMetricFormAt g x w w ≤ 1 + η := hw
  have hwX' : finiteMetricFormAt g x w X ≤ b := hwX
  have hXX' : finiteMetricFormAt g x X X = g.inner x X X := rfl
  rw [Real.sqrt_le_iff]
  have hle : finiteMetricFormAt g x (w + δ • X) (w + δ • X) ≤
      1 + η + 2 * δ * b + δ ^ 2 * g.inner x X X := by
    rw [hexp, hXX']
    nlinarith
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (η / 2 + δ * b + δ ^ 2 * g.inner x X X / 2)]

/-- The arithmetic of the chord estimate (upper half of the first variation). -/
theorem firstVariation_upper_arith {κ s t δ a NX CN e₁ e₂ Nv c m : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hδ : 0 < δ) (hsδ : s * δ = t) (hNv : s * Nv ≤ s - t * a + t * (δ * NX) / 2)
    (hκ1 : 1 < κ) (hκ2 : κ ≤ 2) (hκa : (κ - 1) * (1 + |a| * δ) ≤ m * δ / 4)
    (hδNX : δ * NX ≤ m / 4) (hNX : 0 ≤ NX) (hCN : CN * (e₁ + e₂ / δ) ≤ m / 8)
    (hm : m = c + a) (hmpos : 0 < m) :
    κ * (s * Nv + CN * (e₁ * t + e₂ * s)) - s ≤ t * c := by
  have hB : CN * (e₁ * t + e₂ * s) = t * (CN * (e₁ + e₂ / δ)) := by
    rw [← hsδ]; field_simp
  have hB' : CN * (e₁ * t + e₂ * s) ≤ t * (m / 8) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hCN ht.le
  have hκ0 : 0 ≤ κ := by linarith
  have h1 : κ * (s * Nv + CN * (e₁ * t + e₂ * s)) ≤
      κ * (s - t * a + t * (δ * NX) / 2 + t * (m / 8)) :=
    mul_le_mul_of_nonneg_left (add_le_add hNv hB') hκ0
  have hta : -(t * a) ≤ t * |a| := by
    have := neg_abs_le a
    nlinarith
  have hC1 : (κ - 1) * s - (κ - 1) * t * a ≤ (κ - 1) * (s * (1 + |a| * δ)) := by
    have e : s * (1 + |a| * δ) = s + t * |a| := by rw [← hsδ]; ring
    rw [e]
    have hk : 0 ≤ κ - 1 := by linarith
    have := mul_le_mul_of_nonneg_left hta hk
    nlinarith
  have hC2 : (κ - 1) * (s * (1 + |a| * δ)) ≤ t * (m / 4) := by
    have e : (κ - 1) * (s * (1 + |a| * δ)) = s * ((κ - 1) * (1 + |a| * δ)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hκa hs.le
    have e2 : s * (m * δ / 4) = t * (m / 4) := by rw [← hsδ]; ring
    linarith
  have hD : κ * (t * (δ * NX) / 2) ≤ t * (m / 4) := by
    have h2 : t * (δ * NX) ≤ t * (m / 4) := mul_le_mul_of_nonneg_left hδNX ht.le
    have h3 : 0 ≤ t * (δ * NX) := by positivity
    nlinarith
  have hE : κ * (t * (m / 8)) ≤ t * (m / 4) := by
    have : 0 ≤ t * (m / 8) := by positivity
    nlinarith
  have hF : t * (3 * (m / 4)) ≤ t * m := by nlinarith
  have e : κ * (s - t * a + t * (δ * NX) / 2 + t * (m / 8)) - s =
      ((κ - 1) * s - (κ - 1) * t * a) + κ * (t * (δ * NX) / 2) + κ * (t * (m / 8)) - t * a := by
    ring
  have hc : t * c = t * m - t * a := by rw [hm]; ring
  linarith

/-- The arithmetic of the chord estimate (lower half of the first variation). -/
theorem firstVariation_lower_arith {κ s t δ a η NX CN e₁ e₂ Nv m : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hδ : 0 < δ) (hsδ : s * δ = t)
    (hNv : s * Nv ≤ s * (1 + η / 2) + t * (a + η) + t * (δ * NX) / 2)
    (hκ1 : 1 < κ) (hκ2 : κ ≤ 2) (hκa : (κ - 1) * (1 + |a| * δ) ≤ m * δ / 4)
    (hδNX : δ * NX ≤ m / 4) (hNX : 0 ≤ NX) (hη : 0 ≤ η) (hηδ : η * (1 + 2 * δ) ≤ m * δ / 8)
    (hCN : CN * (e₁ + e₂ / δ) ≤ m / 8) (hmpos : 0 < m) :
    κ * (s * Nv + CN * (e₁ * t + e₂ * s)) - s ≤ t * (a + m) := by
  have hB : CN * (e₁ * t + e₂ * s) = t * (CN * (e₁ + e₂ / δ)) := by
    rw [← hsδ]; field_simp
  have hB' : CN * (e₁ * t + e₂ * s) ≤ t * (m / 8) := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hCN ht.le
  have hκ0 : 0 ≤ κ := by linarith
  have h1 : κ * (s * Nv + CN * (e₁ * t + e₂ * s)) ≤
      κ * (s * (1 + η / 2) + t * (a + η) + t * (δ * NX) / 2 + t * (m / 8)) :=
    mul_le_mul_of_nonneg_left (add_le_add hNv hB') hκ0
  have hk : 0 ≤ κ - 1 := by linarith
  have hC : (κ - 1) * s + (κ - 1) * (t * a) ≤ t * (m / 4) := by
    have hta : t * a ≤ t * |a| := mul_le_mul_of_nonneg_left (le_abs_self a) ht.le
    have e : s * (1 + |a| * δ) = s + t * |a| := by rw [← hsδ]; ring
    have h2 : (κ - 1) * (t * a) ≤ (κ - 1) * (t * |a|) := mul_le_mul_of_nonneg_left hta hk
    have h3 := mul_le_mul_of_nonneg_left hκa hs.le
    have e2 : s * (m * δ / 4) = t * (m / 4) := by rw [← hsδ]; ring
    have e3 : s * ((κ - 1) * (1 + |a| * δ)) = (κ - 1) * s + (κ - 1) * (t * |a|) := by
      rw [← hsδ]; ring
    linarith
  have hE : κ * (s * (η / 2) + t * η) ≤ t * (m / 8) := by
    have h0 : 0 ≤ s * (η / 2) + t * η := by positivity
    have h2 : κ * (s * (η / 2) + t * η) ≤ 2 * (s * (η / 2) + t * η) :=
      mul_le_mul_of_nonneg_right hκ2 h0
    have e : 2 * (s * (η / 2) + t * η) = s * (η * (1 + 2 * δ)) := by rw [← hsδ]; ring
    have h3 := mul_le_mul_of_nonneg_left hηδ hs.le
    have e2 : s * (m * δ / 8) = t * (m / 8) := by rw [← hsδ]; ring
    linarith
  have hD : κ * (t * (δ * NX) / 2) ≤ t * (m / 4) := by
    have h2 : t * (δ * NX) ≤ t * (m / 4) := mul_le_mul_of_nonneg_left hδNX ht.le
    have h3 : 0 ≤ t * (δ * NX) / 2 := by positivity
    have h4 : κ * (t * (δ * NX) / 2) ≤ 2 * (t * (δ * NX) / 2) := mul_le_mul_of_nonneg_right hκ2 h3
    linarith
  have hF : κ * (t * (m / 8)) ≤ t * (m / 4) := by
    have h3 : 0 ≤ t * (m / 8) := by positivity
    have h4 : κ * (t * (m / 8)) ≤ 2 * (t * (m / 8)) := mul_le_mul_of_nonneg_right hκ2 h3
    linarith
  have e : κ * (s * (1 + η / 2) + t * (a + η) + t * (δ * NX) / 2 + t * (m / 8)) - s =
      ((κ - 1) * s + (κ - 1) * (t * a)) + κ * (s * (η / 2) + t * η) + κ * (t * (δ * NX) / 2) +
        κ * (t * (m / 8)) + t * a := by ring
  have hm8 : 0 ≤ t * (m / 8) := by positivity
  nlinarith

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] in
/-- **CM3.c, upper half** (first variation, Dini form), at a named base point `x = γ 0`. -/
theorem eventually_infDist_sub_le_finite_of_eq [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E} {x : M}
    (hγ0 : γ 0 = x) (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : x ∉ S)
    {u : TangentSpace I x} (hu : u ∈ finiteMinimizingDirectionsTo g S x) {c : ℝ}
    (hc : -g.inner x u X < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Metric.infDist (γ t) S - Metric.infDist x S ≤ t * c := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set d := Metric.infDist x S with hd
  have hdpos : 0 < d := (hS.notMem_iff_infDist_pos hSne).1 hx
  set a := g.inner x u X with ha
  set m := c + a with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  set NX := g.inner x X X with hNX
  have hNX0 : 0 ≤ NX := finite_inner_self_nonneg g x X
  set φ := extChartAt I x with hφ
  set N := finiteMetricSeminormAt g x with hN
  set CN := Real.sqrt ‖finiteMetricFormAt g x‖ with hCN
  have hCN0 : 0 ≤ CN := Real.sqrt_nonneg _
  have hNle : ∀ w : E, N w ≤ CN * ‖w‖ := finiteMetricSeminormAt_le_mul_norm g x
  -- parameters
  set δ : ℝ := m / (4 * (NX + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδNX : δ * NX ≤ m / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set κ : ℝ := 1 + min 1 (m * δ / (4 * (1 + |a| * δ))) with hκ
  have hκ1 : 1 < κ := by
    rw [hκ]; have : 0 < min 1 (m * δ / (4 * (1 + |a| * δ))) := lt_min one_pos (by positivity)
    linarith
  have hκ2 : κ ≤ 2 := by rw [hκ]; linarith [min_le_left 1 (m * δ / (4 * (1 + |a| * δ)))]
  have hκa : (κ - 1) * (1 + |a| * δ) ≤ m * δ / 4 := by
    have h1 : κ - 1 ≤ m * δ / (4 * (1 + |a| * δ)) := by
      rw [hκ]; linarith [min_le_right 1 (m * δ / (4 * (1 + |a| * δ)))]
    have h2 : 0 < 1 + |a| * δ := by positivity
    calc (κ - 1) * (1 + |a| * δ) ≤ m * δ / (4 * (1 + |a| * δ)) * (1 + |a| * δ) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = m * δ / 4 := by field_simp
  set ε₁ : ℝ := m / (16 * (CN + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  set ε₂ : ℝ := m * δ / (16 * (CN + 1)) with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  have hCNε : CN * (ε₁ + ε₂ / δ) ≤ m / 8 := by
    have h1 : ε₂ / δ = ε₁ := by rw [hε₂, hε₁]; field_simp
    rw [h1, hε₁]
    have h2 : CN * (m / (16 * (CN + 1)) + m / (16 * (CN + 1))) = m / 8 * (CN / (CN + 1)) := by
      field_simp; ring
    rw [h2]
    have h3 : CN / (CN + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  -- the chart kernels
  obtain ⟨ρ, hρ, hρt, hK1⟩ := exists_ball_dist_chart_symm_le_finite g hnorm x hκ1
  obtain ⟨W, hW, δ₂, hδ₂, hexp⟩ :=
    exists_nhds_chart_geodesicFlow_expansion g hr1 (⟨x, u⟩ : TangentBundle I M) hε₂pos
  have hux : (trivializationAt E (TangentSpace I) x (⟨x, u⟩ : TangentBundle I M)).2 = u :=
    trivializationAt_mk_self_snd x u
  obtain ⟨uE, huE⟩ : ∃ uE : E, uE = u := ⟨u, rfl⟩
  have hux' : (trivializationAt E (TangentSpace I) x (⟨x, u⟩ : TangentBundle I M)).2 = uE :=
    hux.trans huE.symm
  have hγd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt hγ
  rw [hγ0] at hγd
  -- eventual facts for `t`
  have hlo := (hasDerivAt_iff_isLittleO.mp hγd).def hε₁pos
  have hsrc : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ (chartAt H x).source :=
    hγ.continuousAt.preimage_mem_nhds
      ((chartAt H x).open_source.mem_nhds (hγ0 ▸ mem_chart_source H x))
  set L : ℝ := ‖uE‖ + ε₂ + ‖X‖ + ε₁ + 1 with hL
  have hLpos : 0 < L := by positivity
  set t₀ : ℝ := min (δ * min δ₂ (min d (ρ / (2 * L)))) (ρ / (2 * L)) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  filter_upwards [nhdsWithin_le_nhds hlo, nhdsWithin_le_nhds hsrc, Ioo_mem_nhdsGT ht₀pos]
    with t hlot hsrct ht
  obtain ⟨htpos, htlt⟩ := ht
  set s := t / δ with hs
  have hspos : 0 < s := by positivity
  have hsδ : s * δ = t := by rw [hs]; field_simp
  have hsle : s < min δ₂ (min d (ρ / (2 * L))) := by
    rw [hs, div_lt_iff₀ hδpos]; linarith [min_le_left (δ * min δ₂ (min d (ρ / (2 * L))))
      (ρ / (2 * L))]
  have hsδ₂ : s ≤ δ₂ := (hsle.trans_le (min_le_left _ _)).le
  have hsd : s ≤ d := (hsle.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hsρ : s < ρ / (2 * L) := hsle.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htρ : t < ρ / (2 * L) :=
    htlt.trans_le (min_le_right _ _)
  obtain ⟨hdom, -, hexps⟩ := hexp _ (mem_of_mem_nhds hW) s ⟨hspos.le, hsδ₂⟩
  rw [hux'] at hexps
  -- the geodesic point
  set cs := g.expMap (⟨x, s • u⟩ : TangentBundle I M) with hcs
  have hcs' : cs = (g.geodesicFlow (⟨x, u⟩ : TangentBundle I M) s).proj :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 x u s hdom
  have hcsrc : cs ∈ (chartAt H x).source := by
    rw [hcs']
    exact (hexp _ (mem_of_mem_nhds hW) s ⟨hspos.le, hsδ₂⟩).2.1
  -- positions in the chart
  have hγt : ‖φ (γ t) - φ x - t • X‖ ≤ ε₁ * t := by
    have := hlot
    rw [hγ0] at this
    simp only [sub_zero, Real.norm_eq_abs, abs_of_pos htpos] at this
    exact this
  have hcst : ‖φ cs - φ x - s • uE‖ ≤ ε₂ * s := by rw [hcs']; exact hexps
  have hball1 : φ (γ t) ∈ Metric.ball (φ x) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖φ (γ t) - φ x‖ = ‖(φ (γ t) - φ x - t • X) + t • X‖ := by congr 1; abel
      _ ≤ ε₁ * t + t * ‖X‖ := by
          refine (norm_add_le _ _).trans (add_le_add hγt ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      _ ≤ t * L := by
          have h1 : 0 ≤ t * (‖uE‖ + ε₂ + 1) := by positivity
          have e : t * L = ε₁ * t + t * ‖X‖ + t * (‖uE‖ + ε₂ + 1) := by rw [hL]; ring
          linarith
      _ < ρ := by
          have h1 : t * L < ρ / (2 * L) * L := mul_lt_mul_of_pos_right htρ hLpos
          have h2 : ρ / (2 * L) * L = ρ / 2 := by field_simp
          linarith
  have hball2 : φ cs ∈ Metric.ball (φ x) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖φ cs - φ x‖ = ‖(φ cs - φ x - s • uE) + s • uE‖ := by congr 1; abel
      _ ≤ ε₂ * s + s * ‖uE‖ := by
          refine (norm_add_le _ _).trans (add_le_add hcst ?_)
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
      _ ≤ s * L := by
          have h1 : 0 ≤ s * (‖X‖ + ε₁ + 1) := by positivity
          have e : s * L = ε₂ * s + s * ‖uE‖ + s * (‖X‖ + ε₁ + 1) := by rw [hL]; ring
          linarith
      _ < ρ := by
          have h1 : s * L < ρ / (2 * L) * L := mul_lt_mul_of_pos_right hsρ hLpos
          have h2 : ρ / (2 * L) * L = ρ / 2 := by field_simp
          linarith
  have hdist : dist (γ t) cs ≤ κ * N (φ (γ t) - φ cs) := by
    have h := hK1 _ hball1 _ hball2
    rwa [φ.left_inv (by rw [hφ, extChartAt_source]; exact hsrct),
      φ.left_inv (by rw [hφ, extChartAt_source]; exact hcsrc)] at h
  -- the chord
  have hchord : N (uE + δ • (-X)) ≤ 1 + 0 / 2 + δ * (-a) + δ ^ 2 * NX / 2 := by
    have h := finiteMetricSeminormAt_add_smul_le g x (w := uE) (X := -X) (η := 0) (b := -a)
      (by rw [huE, hu.1]; norm_num) (by
        change finiteMetricFormAt g x uE (-X) ≤ -a
        rw [map_neg, huE]; exact le_rfl) hδpos.le
    have hneg : g.inner x (-X) (-X) = NX := by
      change finiteMetricFormAt g x (-X) (-X) = NX
      rw [ContinuousLinearMap.map_neg₂, map_neg, neg_neg]; rfl
    rwa [hneg] at h
  have hdiff : φ (γ t) - φ cs = -(s • (uE + δ • (-X))) + ((φ (γ t) - φ x - t • X) -
      (φ cs - φ x - s • uE)) := by
    rw [smul_add, smul_smul, hsδ]
    simp only [smul_neg]
    abel
  have hNdiff : N (φ (γ t) - φ cs) ≤ s * N (uE + δ • (-X)) + CN * (ε₁ * t + ε₂ * s) := by
    rw [hdiff]
    refine (map_add_le_add N _ _).trans (add_le_add ?_ ?_)
    · rw [map_neg_eq_map, map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hspos]
    · refine (hNle _).trans (mul_le_mul_of_nonneg_left ?_ hCN0)
      exact (norm_sub_le _ _).trans (add_le_add hγt hcst)
  have hinf : Metric.infDist (γ t) S ≤ dist (γ t) cs + (d - s) := by
    have h1 := Metric.infDist_le_infDist_add_dist (x := γ t) (y := cs) (s := S)
    have h2 := (infDist_expMap_smul_le_finite g hr hnorm hu ⟨hspos.le, hsd⟩).1
    linarith
  -- arithmetic
  have hA : s * N (uE + δ • (-X)) ≤ s - t * a + t * (δ * NX) / 2 := by
    have := mul_le_mul_of_nonneg_left hchord hspos.le
    have e1 : s * (1 + 0 / 2 + δ * -a + δ ^ 2 * NX / 2) =
        s - (s * δ) * a + (s * δ) * (δ * NX) / 2 := by ring
    rw [e1, hsδ] at this
    exact this
  have key := firstVariation_upper_arith hspos htpos hδpos hsδ hA hκ1 hκ2 hκa hδNX hNX0 hCNε
    hm hmpos (e₁ := ε₁) (e₂ := ε₂)
  have hκ0 : 0 ≤ κ := by linarith
  have h5 := mul_le_mul_of_nonneg_left hNdiff hκ0
  linarith


/-- **CM3.c, lower half** (first variation, Dini form), at a named base point `x = γ 0`: if
`c < -g(u, X)` for EVERY minimizing direction `u` at `x`, then eventually
`t c ≤ d_S(γ t) - d_S(x)` for `t → 0⁺`. -/
theorem eventually_le_infDist_sub_finite_of_eq [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E} {x : M}
    (hγ0 : γ 0 = x) (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : x ∉ S)
    {c : ℝ} (hc : ∀ u ∈ finiteMinimizingDirectionsTo g S x, c < -g.inner x u X) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t * c ≤ Metric.infDist (γ t) S - Metric.infDist x S := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set d := Metric.infDist x S with hd
  have hdpos : 0 < d := (hS.notMem_iff_infDist_pos hSne).1 hx
  set φ := extChartAt I x with hφ
  set T := trivializationAt E (TangentSpace I) x with hT
  have hbase : ∀ z : M, z ∈ T.baseSet ↔ z ∈ (chartAt H x).source := by
    intro z; rw [hT, TangentBundle.trivializationAt_baseSet]
  set N := finiteMetricSeminormAt g x with hN
  set CN := Real.sqrt ‖finiteMetricFormAt g x‖ with hCN
  have hCN0 : 0 ≤ CN := Real.sqrt_nonneg _
  have hNle : ∀ w : E, N w ≤ CN * ‖w‖ := finiteMetricSeminormAt_le_mul_norm g x
  obtain ⟨c₀, hc₀, hc₀N⟩ := exists_mul_norm_le_finiteMetricSeminormAt g x
  have hγd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt hγ
  rw [hγ0] at hγd
  have hγc : Tendsto γ (𝓝 0) (𝓝 x) := by
    have := hγ.continuousAt.tendsto; rwa [hγ0] at this
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨t, htlim, hbad⟩ := exists_seq_forall_of_frequently hcon
  have htlim0 : Tendsto t atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin htlim
  have htpos : ∀ᶠ n in atTop, t n ∈ Ioi (0 : ℝ) := (tendsto_nhdsWithin_iff.mp htlim).2
  have hgoodz : ∀ᶠ z in 𝓝 x, z ∉ S ∧ (z ∈ (chartAt H x).source ∧ ∀ w : E,
      g.inner x w w ≤ 2 * g.inner z (T.symmL ℝ z w) (T.symmL ℝ z w) ∧
      g.inner z (T.symmL ℝ z w) (T.symmL ℝ z w) ≤ 2 * g.inner x w w) :=
    Filter.Eventually.and (show ∀ᶠ z in 𝓝 x, z ∉ S from hS.isOpen_compl.mem_nhds hx)
      (eventually_finite_chart_metric_comparison g x one_lt_two)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (htpos.and ((hγc.comp htlim0).eventually hgoodz))
  set t' : ℕ → ℝ := fun n => t (n + K) with ht'
  have ht'lim : Tendsto t' atTop (𝓝 0) := htlim0.comp (tendsto_add_atTop_nat K)
  have ht'good : ∀ n, t' n ∈ Ioi (0 : ℝ) ∧ (γ (t' n) ∉ S ∧ (γ (t' n) ∈ (chartAt H x).source ∧
      ∀ w : E, g.inner x w w ≤ 2 * g.inner (γ (t' n)) (T.symmL ℝ (γ (t' n)) w)
        (T.symmL ℝ (γ (t' n)) w) ∧ g.inner (γ (t' n)) (T.symmL ℝ (γ (t' n)) w)
        (T.symmL ℝ (γ (t' n)) w) ≤ 2 * g.inner x w w)) :=
    fun n => hK (n + K) (Nat.le_add_left K n)
  have hne : ∀ n, (finiteMinimizingDirectionsTo g S (γ (t' n))).Nonempty := fun n =>
    (finiteMinimizingDirectionsTo_nonempty_isCompact g hr hnorm hS hSne (γ (t' n))).1
  choose u hu using hne
  set ũ : ℕ → E := fun n => T.continuousLinearMapAt ℝ (γ (t' n)) (u n) with hũ
  have hsymm : ∀ n, T.symmL ℝ (γ (t' n)) (ũ n) = u n := fun n =>
    T.symmL_continuousLinearMapAt ((hbase _).mpr (ht'good n).2.2.1) (u n)
  have hbd : ∀ n, ũ n ∈ Metric.closedBall (0 : E) (Real.sqrt 2 / c₀) := by
    intro n
    have h1 := ((ht'good n).2.2.2 (ũ n)).1
    rw [hsymm n, (hu n).1, mul_one] at h1
    have h2 := hc₀N (ũ n)
    rw [Metric.mem_closedBall, dist_zero_right, le_div_iff₀ hc₀]
    calc ‖ũ n‖ * c₀ = c₀ * ‖ũ n‖ := mul_comm _ _
      _ ≤ N (ũ n) := h2
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
  obtain ⟨uInf, -, ψ, hψ, hψlim⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  set y : ℕ → M := fun n => γ (t' (ψ n)) with hy
  have ht'ψ : Tendsto (fun n => t' (ψ n)) atTop (𝓝 0) := ht'lim.comp hψ.tendsto_atTop
  have hylim : Tendsto y atTop (𝓝 x) := hγc.comp ht'ψ
  have hplim : Tendsto (fun n => (⟨y n, u (ψ n)⟩ : TangentBundle I M)) atTop
      (𝓝 (⟨x, uInf⟩ : TangentBundle I M)) := by
    have hcont : ContinuousAt (fun p : M × E => (⟨p.1, T.symmL ℝ p.1 p.2⟩ : TangentBundle I M))
        (x, uInf) :=
      (continuousOn_trivializationAt_symm (I := I) x).continuousAt
        (prod_mem_nhds ((chartAt H x).open_source.mem_nhds (mem_chart_source H x)) univ_mem)
    have h2 := hcont.tendsto.comp (hylim.prodMk_nhds hψlim)
    have hsx : T.symmL ℝ x uInf = uInf := trivializationAt_symmL_self x uInf
    rw [hsx] at h2
    refine h2.congr fun n => ?_
    simp only [Function.comp_apply]
    rw [hsymm (ψ n)]
  have huInf : uInf ∈ finiteMinimizingDirectionsTo g S x :=
    mem_finiteMinimizingDirectionsTo_of_tendsto g hr hnorm hS
      (p := fun n => (⟨y n, u (ψ n)⟩ : TangentBundle I M)) (fun n => hu (ψ n)) hplim
  -- parameters
  set a := g.inner x uInf X with ha
  set m := -a - c with hm
  have hmpos : 0 < m := by have := hc uInf huInf; rw [hm]; linarith
  set NX := g.inner x X X with hNX
  have hNX0 : 0 ≤ NX := finite_inner_self_nonneg g x X
  set δ : ℝ := m / (4 * (NX + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hδNX : δ * NX ≤ m / 4 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set κ : ℝ := 1 + min 1 (m * δ / (4 * (1 + |a| * δ))) with hκ
  have hκ1 : 1 < κ := by
    rw [hκ]; have : 0 < min 1 (m * δ / (4 * (1 + |a| * δ))) := lt_min one_pos (by positivity)
    linarith
  have hκ2 : κ ≤ 2 := by rw [hκ]; linarith [min_le_left 1 (m * δ / (4 * (1 + |a| * δ)))]
  have hκa : (κ - 1) * (1 + |a| * δ) ≤ m * δ / 4 := by
    have h1 : κ - 1 ≤ m * δ / (4 * (1 + |a| * δ)) := by
      rw [hκ]; linarith [min_le_right 1 (m * δ / (4 * (1 + |a| * δ)))]
    have h2 : 0 < 1 + |a| * δ := by positivity
    calc (κ - 1) * (1 + |a| * δ) ≤ m * δ / (4 * (1 + |a| * δ)) * (1 + |a| * δ) :=
          mul_le_mul_of_nonneg_right h1 h2.le
      _ = m * δ / 4 := by field_simp
  set η : ℝ := m * δ / (8 * (1 + 2 * δ)) with hη
  have hηpos : 0 < η := by positivity
  have hηδ : η * (1 + 2 * δ) ≤ m * δ / 8 := by rw [hη]; field_simp; exact le_rfl
  set ε₁ : ℝ := m / (16 * (CN + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  set ε₂ : ℝ := m * δ / (16 * (CN + 1)) with hε₂
  have hε₂pos : 0 < ε₂ := by positivity
  have hCNε : CN * (ε₁ + ε₂ / δ) ≤ m / 8 := by
    have h1 : ε₂ / δ = ε₁ := by rw [hε₂, hε₁]; field_simp
    rw [h1, hε₁]
    have h2 : CN * (m / (16 * (CN + 1)) + m / (16 * (CN + 1))) = m / 8 * (CN / (CN + 1)) := by
      field_simp; ring
    rw [h2]
    have h3 : CN / (CN + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    nlinarith
  obtain ⟨ρ, hρ, hρt, hK1⟩ := exists_ball_dist_chart_symm_le_finite g hnorm x hκ1
  obtain ⟨W, hW, δ₂, hδ₂, hexp⟩ :=
    exists_nhds_chart_geodesicFlow_expansion g hr1 (⟨x, uInf⟩ : TangentBundle I M) hε₂pos
  set L : ℝ := ‖uInf‖ + 1 + ε₂ + ‖X‖ + ε₁ + 1 with hL
  have hLpos : 0 < L := by positivity
  set t₀ : ℝ := min (δ * min δ₂ (min (d / 2) (ρ / (2 * L)))) (ρ / (2 * L)) with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  -- eventual facts along the subsequence
  have hlo := (hasDerivAt_iff_isLittleO.mp hγd).def hε₁pos
  have hdlim : Tendsto (fun n => Metric.infDist (y n) S) atTop (𝓝 d) :=
    ((Metric.continuous_infDist_pt S).tendsto x).comp hylim
  have hin1 : Tendsto (fun n => g.inner x (ũ (ψ n)) (ũ (ψ n))) atTop (𝓝 (g.inner x uInf uInf)) :=
    ((continuous_finiteMetricFormAt_self g x).tendsto uInf).comp hψlim
  have hin2 : Tendsto (fun n => g.inner x (ũ (ψ n)) X) atTop (𝓝 a) :=
    ((((finiteMetricFormAt g x).flip X).continuous.tendsto uInf).comp hψlim)
  have hnm : Tendsto (fun n => ‖ũ (ψ n)‖) atTop (𝓝 ‖uInf‖) :=
    ((continuous_norm.tendsto uInf).comp hψlim)
  have hu1 : g.inner x uInf uInf = 1 := huInf.1
  have hev : ∀ᶠ n in atTop,
      ‖φ (y n) - φ (γ 0) - (t' (ψ n) - 0) • X‖ ≤ ε₁ * ‖t' (ψ n) - 0‖ ∧ t' (ψ n) < t₀ ∧
      d / 2 < Metric.infDist (y n) S ∧ (⟨y n, u (ψ n)⟩ : TangentBundle I M) ∈ W ∧
      g.inner x (ũ (ψ n)) (ũ (ψ n)) < 1 + η ∧ g.inner x (ũ (ψ n)) X < a + η ∧
      ‖ũ (ψ n)‖ < ‖uInf‖ + 1 := by
    refine (ht'ψ.eventually hlo).and ((ht'ψ.eventually (Iio_mem_nhds ht₀pos)).and
      ((hdlim.eventually (Ioi_mem_nhds (show d / 2 < d by linarith))).and
      ((hplim.eventually hW).and
      ((hin1.eventually (Iio_mem_nhds (show g.inner x uInf uInf < 1 + η by rw [hu1]; linarith))).and
      ((hin2.eventually (Iio_mem_nhds (show a < a + η by linarith))).and
      (hnm.eventually (Iio_mem_nhds (show ‖uInf‖ < ‖uInf‖ + 1 by linarith))))))))
  obtain ⟨n, hlon, htn, hdn, hWn, hg1, hg2, hun⟩ := hev.exists
  rw [hγ0] at hlon
  simp only [sub_zero] at hlon
  -- the point and the chord
  set τ := t' (ψ n) with hτ
  have hτpos : 0 < τ := (ht'good (ψ n)).1
  set s := τ / δ with hs
  have hspos : 0 < s := by positivity
  have hsδ : s * δ = τ := by rw [hs]; field_simp
  have hsle : s < min δ₂ (min (d / 2) (ρ / (2 * L))) := by
    rw [hs, div_lt_iff₀ hδpos]; linarith [min_le_left (δ * min δ₂ (min (d / 2) (ρ / (2 * L))))
      (ρ / (2 * L))]
  have hsδ₂ : s ≤ δ₂ := (hsle.trans_le (min_le_left _ _)).le
  have hsd : s ≤ Metric.infDist (y n) S := by
    have := hsle.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hsρ : s < ρ / (2 * L) := hsle.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hτρ : τ < ρ / (2 * L) := htn.trans_le (min_le_right _ _)
  obtain ⟨hdom, hcsrc0, hexps⟩ := hexp _ hWn s ⟨hspos.le, hsδ₂⟩
  have hTp : (T (⟨y n, u (ψ n)⟩ : TangentBundle I M)).2 = ũ (ψ n) :=
    (T.continuousLinearMapAt_apply_of_mem (R := ℝ) ((hbase _).mpr (ht'good (ψ n)).2.2.1)
      (u (ψ n))).symm
  rw [hTp] at hexps
  set cs := g.expMap (⟨y n, s • u (ψ n)⟩ : TangentBundle I M) with hcs
  have hcs' : cs = (g.geodesicFlow (⟨y n, u (ψ n)⟩ : TangentBundle I M) s).proj :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 (y n) (u (ψ n)) s hdom
  have hcsrc : cs ∈ (chartAt H x).source := by rw [hcs']; exact hcsrc0
  have hcst : ‖φ cs - φ (y n) - s • ũ (ψ n)‖ ≤ ε₂ * s := by rw [hcs']; exact hexps
  have hyt : ‖φ (y n) - φ x - τ • X‖ ≤ ε₁ * τ := by
    rw [Real.norm_eq_abs, abs_of_pos hτpos] at hlon; exact hlon
  have hball0 : φ x ∈ Metric.ball (φ x) ρ := Metric.mem_ball_self hρ
  have hball2 : φ cs ∈ Metric.ball (φ x) ρ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hsplit : φ cs - φ x = (φ cs - φ (y n) - s • ũ (ψ n)) + s • ũ (ψ n) +
        ((φ (y n) - φ x - τ • X) + τ • X) := by abel
    have h1 : ‖s • ũ (ψ n)‖ ≤ s * (‖uInf‖ + 1) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
      exact mul_le_mul_of_nonneg_left hun.le hspos.le
    have h2 : ‖τ • X‖ = τ * ‖X‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτpos]
    have h3 : ‖φ cs - φ x‖ ≤ ε₂ * s + s * (‖uInf‖ + 1) + (ε₁ * τ + τ * ‖X‖) := by
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hcst h1))
        ((norm_add_le _ _).trans (add_le_add hyt h2.le)))
    have h4 : ε₂ * s + s * (‖uInf‖ + 1) + (ε₁ * τ + τ * ‖X‖) ≤ s * L + τ * L := by
      have e : s * L + τ * L = ε₂ * s + s * (‖uInf‖ + 1) + (ε₁ * τ + τ * ‖X‖) +
          s * (‖X‖ + ε₁ + 1) + τ * (‖uInf‖ + 1 + ε₂ + 1) := by rw [hL]; ring
      have p1 : 0 ≤ s * (‖X‖ + ε₁ + 1) := by positivity
      have p2 : 0 ≤ τ * (‖uInf‖ + 1 + ε₂ + 1) := by positivity
      linarith
    have h5 : s * L < ρ / 2 := by
      have := mul_lt_mul_of_pos_right hsρ hLpos
      have e : ρ / (2 * L) * L = ρ / 2 := by field_simp
      linarith
    have h6 : τ * L < ρ / 2 := by
      have := mul_lt_mul_of_pos_right hτρ hLpos
      have e : ρ / (2 * L) * L = ρ / 2 := by field_simp
      linarith
    linarith
  have hdist : dist x cs ≤ κ * N (φ x - φ cs) := by
    have h := hK1 _ hball0 _ hball2
    rwa [φ.left_inv (by rw [hφ, extChartAt_source]; exact mem_chart_source H x),
      φ.left_inv (by rw [hφ, extChartAt_source]; exact hcsrc)] at h
  have hchord : N (ũ (ψ n) + δ • X) ≤ 1 + η / 2 + δ * (a + η) + δ ^ 2 * NX / 2 :=
    finiteMetricSeminormAt_add_smul_le g x hg1.le hg2.le hδpos.le
  have hdiff : φ x - φ cs = -(s • (ũ (ψ n) + δ • X) + ((φ (y n) - φ x - τ • X) +
      (φ cs - φ (y n) - s • ũ (ψ n)))) := by
    rw [smul_add, smul_smul, hsδ]
    abel
  have hNdiff : N (φ x - φ cs) ≤ s * N (ũ (ψ n) + δ • X) + CN * (ε₁ * τ + ε₂ * s) := by
    rw [hdiff, map_neg_eq_map]
    refine (map_add_le_add N _ _).trans (add_le_add ?_ ?_)
    · rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hspos]
    · refine (hNle _).trans (mul_le_mul_of_nonneg_left ?_ hCN0)
      exact (norm_add_le _ _).trans (add_le_add hyt hcst)
  have hA : s * N (ũ (ψ n) + δ • X) ≤ s * (1 + η / 2) + τ * (a + η) + τ * (δ * NX) / 2 := by
    have := mul_le_mul_of_nonneg_left hchord hspos.le
    have e1 : s * (1 + η / 2 + δ * (a + η) + δ ^ 2 * NX / 2) =
        s * (1 + η / 2) + (s * δ) * (a + η) + (s * δ) * (δ * NX) / 2 := by ring
    rw [e1, hsδ] at this
    exact this
  have key := firstVariation_lower_arith hspos hτpos hδpos hsδ hA hκ1 hκ2 hκa hδNX hNX0
    hηpos.le hηδ hCNε hmpos (e₁ := ε₁) (e₂ := ε₂)
  have hκ0 : 0 ≤ κ := by linarith
  have h5 := mul_le_mul_of_nonneg_left hNdiff hκ0
  have hcsS := (infDist_expMap_smul_le_finite g hr hnorm (hu (ψ n)) ⟨hspos.le, hsd⟩).1
  have htri := Metric.infDist_le_infDist_add_dist (x := x) (y := cs) (s := S)
  have hb := hbad (ψ n + K)
  have hτ' : t (ψ n + K) = τ := rfl
  rw [hτ'] at hb
  apply hb
  have hcm : τ * c = -(τ * (a + m)) := by rw [hm]; ring
  change τ * c ≤ Metric.infDist (y n) S - d
  rw [hcm]
  linarith

omit [NeZero (Module.finrank ℝ E)] in
/-- **CM3.c, upper half** (first variation, Dini form). For every minimizing direction `u` at
`γ 0 ∉ S` and every `c > -g(u, X)`, eventually `d_S(γ t) - d_S(γ 0) ≤ t c` for `t → 0⁺`. -/
theorem eventually_infDist_sub_le_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : γ 0 ∉ S)
    {u : TangentSpace I (γ 0)} (hu : u ∈ finiteMinimizingDirectionsTo g S (γ 0)) {c : ℝ}
    (hc : -g.inner (γ 0) u X < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Metric.infDist (γ t) S - Metric.infDist (γ 0) S ≤ t * c :=
  eventually_infDist_sub_le_finite_of_eq g hr hnorm hS hSne rfl hγ hx hu hc

/-- **CM3.c** at a named base point `x = γ 0`. -/
theorem hasDerivWithinAt_infDist_finite_of_eq [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E} {x : M}
    (hγ0 : γ 0 = x) (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : x ∉ S) :
    HasDerivWithinAt (fun t => Metric.infDist (γ t) S)
      (-(sSup ((fun u : E => g.inner x u X) '' finiteMinimizingDirectionsTo g S x))) (Ici 0) 0 := by
  obtain ⟨hne, hcpt⟩ := finiteMinimizingDirectionsTo_nonempty_isCompact g hr hnorm hS hSne x
  set V := finiteMinimizingDirectionsTo g S x with hV
  set f : E → ℝ := fun u => g.inner x u X with hf
  have hfc : Continuous f := ((finiteMetricFormAt g x).flip X).continuous
  have himg : IsCompact (f '' V) := hcpt.image hfc
  obtain ⟨u₀, hu₀, hfu₀⟩ := himg.sSup_mem (hne.image f)
  have hle : ∀ u ∈ V, f u ≤ sSup (f '' V) := fun u hu =>
    le_csSup himg.bddAbove (mem_image_of_mem f hu)
  refine HasDerivWithinAt.Ici_of_Ioi ?_
  have hset : Ioi (0 : ℝ) \ {0} = Ioi 0 := sdiff_singleton_eq_self (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope, hset]
  have hF0 : Metric.infDist (γ 0) S = Metric.infDist x S := by rw [hγ0]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hev := eventually_le_infDist_sub_finite_of_eq g hr hnorm hS hSne hγ0 hγ hx
      (c := (a + -sSup (f '' V)) / 2) (fun u hu => by
        have := hle u hu; change _ < -f u; linarith)
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    have htp : 0 < t := htpos
    rw [slope_def_field, sub_zero, hF0, lt_div_iff₀ htp]
    nlinarith
  · have hev := eventually_infDist_sub_le_finite_of_eq g hr hnorm hS hSne hγ0 hγ hx hu₀
      (c := (b + -sSup (f '' V)) / 2) (by change -f u₀ < _; rw [hfu₀]; linarith)
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htpos
    have htp : 0 < t := htpos
    rw [slope_def_field, sub_zero, hF0, div_lt_iff₀ htp]
    nlinarith

/-- **CM3.c** (frozen form): the right derivative of `t ↦ d_S(γ t)` at `0` is
`-max_{u ∈ V_{γ 0}(S)} g(u, X)`. -/
theorem hasDerivWithinAt_infDist_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : γ 0 ∉ S) :
    HasDerivWithinAt (fun t => Metric.infDist (γ t) S)
      (-(sSup ((fun u : E => g.inner (γ 0) u X) '' finiteMinimizingDirectionsTo g S (γ 0))))
      (Ici 0) 0 :=
  hasDerivWithinAt_infDist_finite_of_eq g hr hnorm hS hSne rfl hγ hx

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] in
/-- A curve run backwards: velocity `-X`. -/
theorem hasMFDerivAt_comp_neg {γ : ℝ → M} {X : E}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => γ (-t)) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (-X)) := by
  have hneg : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => -t) 0 (-(ContinuousLinearMap.id ℝ ℝ)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr (hasFDerivAt_id (0 : ℝ)).neg
  have hγ' : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (-0) ((1 : ℝ →L[ℝ] ℝ).smulRight X) := by
    rwa [neg_zero]
  have h := hγ'.comp 0 hneg
  have e : ((1 : ℝ →L[ℝ] ℝ).smulRight X).comp (-(ContinuousLinearMap.id ℝ ℝ)) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (-X) := by
    ext; simp
  exact h.congr_mfderiv e

/-- **CM3.c, left derivative**: the left derivative of `t ↦ d_S(γ t)` at `0` is
`-min_{u ∈ V_{γ 0}(S)} g(u, X)`. -/
theorem hasDerivWithinAt_Iic_infDist_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : E}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight X)) (hx : γ 0 ∉ S) :
    HasDerivWithinAt (fun t => Metric.infDist (γ t) S)
      (-(sInf ((fun u : E => g.inner (γ 0) u X) '' finiteMinimizingDirectionsTo g S (γ 0))))
      (Iic 0) 0 := by
  have h := hasDerivWithinAt_infDist_finite_of_eq g hr hnorm hS hSne (γ := fun t => γ (-t))
    (by simp only [neg_zero]) (hasMFDerivAt_comp_neg hγ) hx
  set V := finiteMinimizingDirectionsTo g S (γ 0)
  have himg : (fun u : E => g.inner (γ 0) u (-X)) '' V =
      -((fun u : E => g.inner (γ 0) u X) '' V) := by
    ext y
    simp only [Set.mem_neg]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u, hu, ?_⟩
      change finiteMetricFormAt g (γ 0) u X = -(finiteMetricFormAt g (γ 0) u (-X))
      rw [map_neg, neg_neg]
    · rintro ⟨u, hu, hy⟩
      refine ⟨u, hu, ?_⟩
      have hy' : finiteMetricFormAt g (γ 0) u X = -y := hy
      change finiteMetricFormAt g (γ 0) u (-X) = y
      rw [map_neg, hy', neg_neg]
  rw [himg, Real.sSup_neg, neg_neg] at h
  have hneg : HasDerivWithinAt (fun t : ℝ => -t) (-1) (Iic 0) 0 := (hasDerivAt_neg 0).hasDerivWithinAt
  have hmaps : MapsTo (fun t : ℝ => -t) (Iic 0) (Ici 0) := fun t ht => by
    simp only [mem_Iic, mem_Ici] at ht ⊢; linarith
  have h' : HasDerivWithinAt (fun t => Metric.infDist (γ (-t)) S)
      (sInf ((fun u : E => g.inner (γ 0) u X) '' V)) (Ici 0) (-0) := by rwa [neg_zero]
  have hc := h'.scomp 0 hneg hmaps
  convert hc using 1
  · ext t; simp
  · simp

omit [NeZero (Module.finrank ℝ E)] in
/-- **CM3.c, integrated upper bound**: if along `γ` (with velocity `X t`) some minimizing direction
satisfies `-g(u, X t) ≤ B` at every time of `[a, b)`, then `d_S(γ b) - d_S(γ a) ≤ B (b - a)`. -/
theorem infDist_sub_le_of_forall_exists_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : ℝ → E} {a b B : ℝ}
    (hab : a ≤ b) (hγc : ContinuousOn γ (Icc a b))
    (hγ : ∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)))
    (hout : ∀ t ∈ Ico a b, γ t ∉ S)
    (hB : ∀ t ∈ Ico a b, ∃ u ∈ finiteMinimizingDirectionsTo g S (γ t), -g.inner (γ t) u (X t) ≤ B) :
    Metric.infDist (γ b) S - Metric.infDist (γ a) S ≤ B * (b - a) := by
  refine sub_le_mul_sub_of_eventually_increment_le hab
    ((Metric.continuous_infDist_pt S).comp_continuousOn hγc) fun t ht c hc => ?_
  obtain ⟨u, hu, huB⟩ := hB t ht
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ => γ (t + σ)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)) := by
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => t + σ) 0 (1 : ℝ →L[ℝ] ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id (0 : ℝ)).const_add t)
    have hγt : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (t + 0) ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)) := by
      rw [add_zero]; exact hγ t ht
    exact (hγt.comp 0 htr).congr_mfderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hev := eventually_infDist_sub_le_finite_of_eq g hr hnorm hS hSne (γ := fun σ => γ (t + σ))
    (by simp only [add_zero]) hshift (hout t ht) hu (c := c) (by linarith)
  have hmap : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
        have := (continuous_sub_right t).tendsto t
        rwa [sub_self] at this
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mem_Ioi.mpr (sub_pos.mpr (mem_Ioi.mp hs))
  filter_upwards [hmap.eventually hev] with s hs
  simp only [add_sub_cancel] at hs
  change Metric.infDist (γ s) S - Metric.infDist (γ t) S ≤ c * (s - t)
  linarith

/-- **CM3.c, integrated lower bound**: if `B ≤ -g(u, X t)` for EVERY minimizing direction at every
time of `[a, b)`, then `B (b - a) ≤ d_S(γ b) - d_S(γ a)`. -/
theorem le_infDist_sub_of_forall_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {γ : ℝ → M} {X : ℝ → E} {a b B : ℝ}
    (hab : a ≤ b) (hγc : ContinuousOn γ (Icc a b))
    (hγ : ∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)))
    (hout : ∀ t ∈ Ico a b, γ t ∉ S)
    (hB : ∀ t ∈ Ico a b, ∀ u ∈ finiteMinimizingDirectionsTo g S (γ t), B ≤ -g.inner (γ t) u (X t)) :
    B * (b - a) ≤ Metric.infDist (γ b) S - Metric.infDist (γ a) S := by
  have key := sub_le_mul_sub_of_eventually_increment_le (φ := fun t => -Metric.infDist (γ t) S)
    (B := -B) hab ((Metric.continuous_infDist_pt S).comp_continuousOn hγc).neg fun t ht c hc => ?_
  · linarith
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) I (fun σ => γ (t + σ)) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)) := by
    have htr : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => t + σ) 0 (1 : ℝ →L[ℝ] ℝ) :=
      hasMFDerivAt_iff_hasFDerivAt.mpr ((hasFDerivAt_id (0 : ℝ)).const_add t)
    have hγt : HasMFDerivAt 𝓘(ℝ, ℝ) I γ (t + 0) ((1 : ℝ →L[ℝ] ℝ).smulRight (X t)) := by
      rw [add_zero]; exact hγ t ht
    exact (hγt.comp 0 htr).congr_mfderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hev := eventually_le_infDist_sub_finite_of_eq g hr hnorm hS hSne
    (γ := fun σ => γ (t + σ)) (by simp only [add_zero]) hshift (hout t ht) (c := -c)
    (fun u hu => by have := hB t ht u hu; linarith)
  have hmap : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
        have := (continuous_sub_right t).tendsto t
        rwa [sub_self] at this
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mem_Ioi.mpr (sub_pos.mpr (mem_Ioi.mp hs))
  filter_upwards [hmap.eventually hev] with s hs
  simp only [add_sub_cancel] at hs
  linarith

end Bundle.ContMDiffRiemannianMetric
