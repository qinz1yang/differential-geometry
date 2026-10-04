import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ShaveOrthogonalShift
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge

/-!
# S-SHAVE: hinge and foot-point toolkit for the boundary concavity (finite metric)

Lane CMS-B. Helpers for `ShaveConcavity.lean`, for a complete metric `g` of class `C^{r+1}`
(`2 ≤ r`, `hnorm`):

* algebra of `g_x` on model vectors (`shaveInner_*`), stated on `E` so that they rewrite terms built
  from model vectors;
* `dist_sq_le_hinge_finite`: the Euclidean hinge in squared-distance form, both legs minimizing, from
  CM5.b `comparisonAngle_le_arccos_inner_finite` (`sec ≥ 0`);
* `exists_radial_dist_eq`: short radial geodesics are segments (`d(x, exp_x (s e)) = s`, CM1.d);
* `dist_infDist_expMap_smul_of_foot`: along the unit geodesic from `x` to a nearest point of a set
  `B`, `d(x, ·) = t` and `d(·, B) = d(x, B) - t`;
* `inner_eq_zero_of_isLocalMin_dist`: at an interior local minimum of `s ↦ d(z, exp_o (s V))` the
  minimizing direction from `o` to `z` is `g_o`-orthogonal to `V` (via the hinge).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

section Algebra

omit [FiniteDimensional ℝ E] [I.Boundaryless]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

variable {n : ℕ∞ω} (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M)

theorem shaveInner_smul_left (c : ℝ) (a b : E) : g.inner x (c • a) b = c * g.inner x a b := by
  have h : g.inner x (c • a) = c • g.inner x a := (g.inner x).map_smul c a
  rw [h]
  rfl

theorem shaveInner_smul_right (c : ℝ) (a b : E) : g.inner x a (c • b) = c * g.inner x a b :=
  (g.inner x a).map_smul c b

theorem shaveInner_sub_left (a b d : E) : g.inner x (a - b) d = g.inner x a d - g.inner x b d := by
  have h : g.inner x (a - b) = g.inner x a - g.inner x b := (g.inner x).map_sub a b
  rw [h]
  rfl

theorem shaveInner_sub_right (a b d : E) : g.inner x a (b - d) = g.inner x a b - g.inner x a d :=
  (g.inner x a).map_sub b d

theorem shaveInner_symm (a b : E) : g.inner x a b = g.inner x b a := g.symm x a b

end Algebra

/-- **Hinge comparison, squared-distance form** (CM5.b with both legs minimizing). -/
theorem dist_sq_le_hinge_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (o : M) {u v : E} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hu : g.inner o u u = 1) (hv : g.inner o v v = 1)
    (hminA : dist o (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) = a)
    (hminB : dist o (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) = b) :
    dist (g.expMap (⟨o, a • u⟩ : TangentBundle I M)) (g.expMap (⟨o, b • v⟩ : TangentBundle I M)) ^ 2 ≤
      a ^ 2 + b ^ 2 - 2 * a * b * g.inner o u v := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  have : SigmaCompactSpace M := inferInstance
  have h := DifferentialGeometry.Geometry.FiniteComparison.comparisonAngle_le_arccos_inner_finite g
    (one_le_two.trans hr) hnorm o u v ha hb hu hv hminA hminB hsec
  set A := g.expMap (⟨o, a • u⟩ : TangentBundle I M) with hA
  set B := g.expMap (⟨o, b • v⟩ : TangentBundle I M) with hB
  set D := dist A B with hD
  set c := g.inner o u v with hc
  have hcs := DifferentialGeometry.Geometry.Collapse.abs_finite_inner_le g o u v
  rw [hu, hv, Real.sqrt_one, mul_one] at hcs
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcs
  have hupper : D ≤ a + b := by
    have := dist_triangle_left A B o
    linarith
  have hlower : |a - b| ≤ D := by
    have := abs_dist_sub_le A B o
    rwa [dist_comm A o, dist_comm B o, hminA, hminB] at this
  have hk := comparison_cosine_mem_Icc ha hb hlower hupper
  have hcos : c ≤ (a ^ 2 + b ^ 2 - D ^ 2) / (2 * a * b) := by
    have h1 : Real.cos (Real.arccos c) ≤ Real.cos (comparisonAngle a b D) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (comparisonAngle_mem_Icc _ _ _).1 (Real.arccos_le_pi _) h
    rwa [Real.cos_arccos hlo hhi, comparisonAngle, Real.cos_arccos hk.1 hk.2] at h1
  rw [le_div_iff₀ (by positivity)] at hcos
  linarith

omit [CompleteSpace M] in
/-- **Short radial geodesics are segments**: `d(x, exp_x (s e)) = s` for unit `e` and `0 ≤ s < ρ`. -/
theorem exists_radial_dist_eq
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (x : M) :
    ∃ ρ > 0, ∀ e : E, g.inner x e e = 1 → ∀ s ∈ Ico 0 ρ,
      dist x (g.expMap (⟨x, s • e⟩ : TangentBundle I M)) = s := by
  obtain ⟨ρ, hρ, hch⟩ := g.exists_uniform_normal_charts hr hnorm (isCompact_singleton (x := x))
  obtain ⟨φ, hsrc, -, hexp, -, -, hdist⟩ := hch x rfl
  refine ⟨ρ, hρ, fun e he s hs => ?_⟩
  have hsm : g.inner x (s • e) (s • e) = s ^ 2 := by
    rw [shaveInner_smul_left, shaveInner_smul_right, he]; ring
  have hmem : s • e ∈ φ.source := by
    rw [hsrc]
    change g.inner x (s • e) (s • e) < ρ ^ 2
    rw [hsm]
    nlinarith [hs.1, hs.2]
  have h2 : dist x (φ (s • e)) = s := by rw [hdist _ hmem, hsm, Real.sqrt_sq hs.1]
  exact (congrArg (dist x) (hexp _ hmem).2).symm.trans h2

/-- **Along a segment to a nearest point of `B`.** If the unit geodesic from `x` in direction `u`
reaches `B` at time `d(x, B)`, then for `t ∈ [0, d(x, B)]`: `d(x, exp_x (t u)) = t`,
`d(exp_x (t u), B) = d(x, B) - t`, and the geodesic is a segment on `[0, d(x, B)]`. -/
theorem dist_infDist_expMap_smul_of_foot
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {B : Set M} {x : M} {u : E} (hu : g.inner x u u = 1)
    (hfoot : g.expMap (⟨x, infDist x B • u⟩ : TangentBundle I M) ∈ B) :
    (∀ s ∈ Icc 0 (infDist x B), ∀ t ∈ Icc 0 (infDist x B),
      dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
        (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = |s - t|) ∧
    ∀ t ∈ Icc 0 (infDist x B), dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) = t ∧
      infDist (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) B = infDist x B - t := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set l := infDist x B with hl
  have hl0 : 0 ≤ l := infDist_nonneg
  have hlip : ∀ s t : ℝ, dist (g.expMap (⟨x, s • u⟩ : TangentBundle I M))
      (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) ≤ |t - s| := by
    intro s t
    have h := g.dist_expMap_smul_le_of_completeSpace hr1 hnorm (x := x) u s t
    rwa [hu, Real.sqrt_one, one_mul] at h
  have h0 : g.expMap (⟨x, (0 : ℝ) • u⟩ : TangentBundle I M) = x := by
    rw [zero_smul]; exact g.expMap_zero hr1 x
  have hmin : dist x (g.expMap (⟨x, l • u⟩ : TangentBundle I M)) = l := by
    refine le_antisymm ?_ (infDist_le_dist_of_mem hfoot)
    have h := hlip 0 l
    rwa [h0, sub_zero, abs_of_nonneg hl0] at h
  obtain ⟨hrad, hseg⟩ := g.dist_expMap_smul_eq_of_dist_eq hr1 hnorm hu hmin
  refine ⟨hseg, fun t ht => ⟨hrad t ht, le_antisymm ?_ ?_⟩⟩
  · have h1 := infDist_le_dist_of_mem (x := g.expMap (⟨x, t • u⟩ : TangentBundle I M)) hfoot
    rw [hseg t ht l ⟨hl0, le_rfl⟩, abs_of_nonpos (by linarith [ht.2])] at h1
    linarith
  · have h1 : infDist x B ≤ infDist (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) B +
        dist x (g.expMap (⟨x, t • u⟩ : TangentBundle I M)) := infDist_le_infDist_add_dist
    rw [hrad t ht] at h1
    linarith

/-- **First-order condition at an interior local minimum of the distance** (via the hinge): if `W`
is the unit initial vector of a segment of length `d > 0` from `o` to `z`, and
`s ↦ d(z, exp_o (s V))` has a local minimum at `0`, then `g_o(W, V) = 0`. -/
theorem inner_eq_zero_of_isLocalMin_dist [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {o : M} {V W : E} (hV : g.inner o V V = 1) (hW : g.inner o W W = 1) {d : ℝ} (hd : 0 < d)
    (hmin : dist o (g.expMap (⟨o, d • W⟩ : TangentBundle I M)) = d)
    (hloc : ∀ᶠ s in 𝓝 (0 : ℝ), dist (g.expMap (⟨o, d • W⟩ : TangentBundle I M)) o ≤
      dist (g.expMap (⟨o, d • W⟩ : TangentBundle I M)) (g.expMap (⟨o, s • V⟩ : TangentBundle I M))) :
    g.inner o W V = 0 := by
  obtain ⟨ρ, hρ, hrad⟩ := exists_radial_dist_eq g hr hnorm o
  set z := g.expMap (⟨o, d • W⟩ : TangentBundle I M) with hz
  have hzo : dist z o = d := by rw [dist_comm]; exact hmin
  have key : ∀ V' : E, g.inner o V' V' = 1 →
      (∀ᶠ s in 𝓝[>] (0 : ℝ), d ≤ dist z (g.expMap (⟨o, s • V'⟩ : TangentBundle I M))) →
      g.inner o W V' ≤ 0 := by
    intro V' hV' hev
    by_contra hpos
    rw [not_le] at hpos
    have hδ : 0 < min ρ (d * g.inner o W V') := lt_min hρ (mul_pos hd hpos)
    obtain ⟨s, hs, hsI⟩ := (Filter.Eventually.and hev (Ioo_mem_nhdsGT hδ)).exists
    have hs0 : 0 < s := hsI.1
    have hsρ : s < ρ := lt_of_lt_of_le hsI.2 (min_le_left _ _)
    have hsd : s ≤ d * g.inner o W V' := hsI.2.le.trans (min_le_right _ _)
    have hminS := hrad V' hV' s ⟨hs0.le, hsρ⟩
    have hh := dist_sq_le_hinge_finite g hr hnorm hsec o hd hs0 hW hV' hmin hminS
    rw [← hz] at hh
    have h2 : d ^ 2 ≤ dist z (g.expMap (⟨o, s • V'⟩ : TangentBundle I M)) ^ 2 :=
      pow_le_pow_left₀ hd.le hs 2
    nlinarith [mul_pos hd hs0]
  have h1 : g.inner o W V ≤ 0 := by
    refine key V hV ?_
    filter_upwards [nhdsWithin_le_nhds hloc] with s hs
    rwa [hzo] at hs
  have hnegV : g.inner o ((-1 : ℝ) • V) ((-1 : ℝ) • V) = 1 := by
    rw [shaveInner_smul_left, shaveInner_smul_right, hV]; norm_num
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : ℝ))
  have h2 : g.inner o W ((-1 : ℝ) • V) ≤ 0 := by
    refine key _ hnegV ?_
    filter_upwards [nhdsWithin_le_nhds (hneg.eventually hloc)] with s hs
    have hv : (s • ((-1 : ℝ) • V) : E) = (-s) • V := by rw [smul_smul, mul_neg_one]
    have he : g.expMap (⟨o, s • ((-1 : ℝ) • V)⟩ : TangentBundle I M) =
        g.expMap (⟨o, (-s) • V⟩ : TangentBundle I M) :=
      congrArg (fun v : E => g.expMap (⟨o, v⟩ : TangentBundle I M)) hv
    have hs' : d ≤ dist z (g.expMap (⟨o, (-s) • V⟩ : TangentBundle I M)) := hzo ▸ hs
    exact (congrArg (dist z) he).symm ▸ hs'
  rw [shaveInner_smul_right] at h2
  linarith

end DifferentialGeometry.Geometry.FiniteSoul

end
