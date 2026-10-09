import DifferentialGeometry.Geometry.Collapse.RiemannianConeScale
import DifferentialGeometry.Geometry.Collapse.RiemannianConeAtInfinityDimension

/-!
# LC24 with its Riemannian limit models (binding via LC56 item (1))

Blueprint 207A, LC24 (`cor:collapse-kl-metric-cone-scale`, A:20898–20915). The row retains the
sequential smooth compactness input of KL 6.10(3): every pointed sequence at the modified scales
has a subsequence converging to a complete nonnegatively curved Riemannian three-manifold, with
the corresponding pointed Gromov–Hausdorff convergence; it also retains the Tits-cone input LC21
for these limit manifolds. The conclusion is an actual KL `δ`-map from the source at a scale
`r_p^0 ∈ [T ρ_α(p), V ρ_α(p)]` (metric tensor `(r_p^0)⁻² g^α`) to the cone of SUCH a limit
manifold.

The metric form `exists_good_annulus_cone_scale` (`GoodAnnulusConeScaleFull.lean`) produces the
limits as metric spaces and does not identify the cone with the cone of a Riemannian limit. Here
the smooth compactness input enters in the form of LC56's item (1) (A:23046), unbundled as in the
LC58 binding `exists_uniform_scale_interval_cone_radial_witnesses`: the limit models are a family
`(N_b, g_b, n_b)`, `b : ι`, of complete smooth Riemannian manifolds with `sec ≥ 0` whose metric
distance is the `g_b`-length distance, and along every sequence of indices `α_j → ∞` and points
`z_j` some subsequence of the normalized sources `(M^{α_j}, ρ(z_j)⁻² g, z_j)` converges pointedly
to one `(N_b, n_b)`. The proof uses only the Gromov–Hausdorff component (the blueprint proof: "the
retained smooth compactness statement and its GH component give exactly LC23's sequential model
property"); LC56's item (2) (the `C¹` comparison maps) and item (4) (the separate curvature
bounds) are not used, and item (3) (the cone package) is PRODUCED: the Tits-cone input is
discharged by the Riemannian LC21 package `exists_cone_at_infinity_package_of_sectional_nonneg_finrank`
(TITS-T4). The output names the model `b` and the FULL LC21 package of `(N_b, n_b)`: radial cone
data, properness, completeness, segments, nonnegative four-point comparison, `dim_H C ≤ dim N_b`
and Kleiner–Lott maps from every large blow-down of `N_b`.

Deviations (strengthenings): `T > 0` instead of `T > 1`; the dimension three and the
connectedness of the models are not used (the verbatim form is the `example` at the end).

* `exists_good_annulus_riemannian_cone_scale`: LC24 with the Riemannian limit models.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u w z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]

/-- **LC24 with its Riemannian limit models.** Sources `(M^α, g^α)` with positive scales
`ρ_α`; limit models `(N_b, g_b, n_b)`, complete with `sec ≥ 0` (LC56 (1)); along every sequence
of indices and points, a subsequence of the normalized sources converges pointedly to one model.
Then every `0 < δ < 1`, `T > 0` admit `V ≥ T` and `α₀` such that every `α > α₀` and every
`p ∈ M^α` have a scale `r ∈ [T ρ_α(p), V ρ_α(p)]`, a model `b`, the full LC21 package `(C, o)` of
`(N_b, n_b)`, and an actual Kleiner–Lott `δ`-map from the source with metric tensor `r⁻² g^α`
(its metric rescaling `r⁻¹ d`, which realizes that distance) to `(C, o)`. -/
theorem exists_good_annulus_riemannian_cone_scale {M : ℕ → Type u}
    [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)] [∀ α, IsManifold I ∞ (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type w} {N : ι → Type z} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H' (N b)]
    [∀ b, IsManifold I' ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, CompleteSpace (N b)]
    (gN : ∀ b, SmoothRiemannianMetric I' (N b))
    (hmetricN : ∀ b x y, riemannianEDistOf (gN b) x y = ENNReal.ofReal (dist x y))
    (hsecN : ∀ b y, SectionalBoundedBelowAt (gN b) y 0) (n : ∀ b, N b)
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 0 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ r : ℝ, ∃ hr : 0 < r, T * ρ α p ≤ r ∧ r ≤ V * ρ α p ∧ ∃ b : ι,
        ∃ (C : Type z) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
          ProperSpace C ∧ CompleteSpace C ∧
          (∀ a c : C, ∃ f : Icc (0 : ℝ) 1 → C, Continuous f ∧
            f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = c ∧
            ∀ s t, dist (f s) (f t) = dist a c * dist s t) ∧
          fourPointComparison 0 (univ : Set C) ∧ dimH (univ : Set C) ≤ Module.finrank ℝ E' ∧
          (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
            Nonempty (@KleinerLottApprox (N b) C ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) mC
              (n b) o ε)) ∧
          (∀ x y, riemannianEDistOf (scaleMetric (r⁻¹ ^ 2) (pow_pos (inv_pos.mpr hr) 2) (g α))
              x y = ENNReal.ofReal (@dist (M α) ((mM α).rescale r⁻¹ (inv_pos.mpr hr)).toDist x y)) ∧
          Nonempty (@KleinerLottApprox (M α) C ((mM α).rescale r⁻¹ (inv_pos.mpr hr)) mC p o δ) := by
  have hpkg (b : ι) := exists_cone_at_infinity_package_of_sectional_nonneg_finrank
    (gN b) (hmetricN b) (hsecN b) (n b)
  choose C mC o hH hprop hcomp hseg h4 hdim hK using hpkg
  obtain ⟨V, hTV, α₀, h⟩ := exists_riemannian_bounded_cone_scale g hmetric ρ hρ
    (C := C) (mC := mC) n o hmodel hK hδ hδone hT
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨s, hs, hTs, hsV, b, hid, hk⟩ := h α hα p
  have hρp := hρ α p
  exact ⟨s * ρ α p, mul_pos hs hρp, mul_le_mul_of_nonneg_right hTs hρp.le,
    mul_le_mul_of_nonneg_right hsV hρp.le, b, C b, mC b, o b, hH b, hprop b, hcomp b, hseg b,
    h4 b, hdim b, hK b, hid, hk⟩

/-- The row verbatim (A:20898): three-dimensional sources and connected three-dimensional limit
models, `T > 1`, and the smooth compactness input carrying LC56's items (1) and (4) (pointed
convergence to a complete connected model with `sec ≥ 0`, and separate curvature bounds
`sec ≥ -H_j⁻²` on the normalized `H_j`-balls with `H_j → ∞`). The theorem above uses neither the
dimensions, nor the connectedness, nor item (4). -/
example [FiniteDimensional ℝ E] {M : ℕ → Type u} [mM : ∀ α, MetricSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [Fact (Module.finrank ℝ E = 3)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (hmetric : ∀ α a b, riemannianEDistOf (g α) a b = ENNReal.ofReal (dist a b))
    (ρ : ∀ α, M α → ℝ) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type w} {N : ι → Type z} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H' (N b)]
    [∀ b, IsManifold I' ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, CompleteSpace (N b)]
    [∀ b, ConnectedSpace (N b)] [Fact (Module.finrank ℝ E' = 3)]
    (gN : ∀ b, SmoothRiemannianMetric I' (N b))
    (hmetricN : ∀ b x y, riemannianEDistOf (gN b) x y = ENNReal.ofReal (dist x y))
    (hsecN : ∀ b y, SectionalBoundedBelowAt (gN b) y 0) (n : ∀ b, N b)
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹ (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((mM (a (k j))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {δ T : ℝ} (hδ : 0 < δ) (hδone : δ < 1) (hT : 1 < T) :
    ∃ V : ℝ, T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α → ∀ p : M α,
      ∃ r : ℝ, ∃ hr : 0 < r, T * ρ α p ≤ r ∧ r ≤ V * ρ α p ∧ ∃ b : ι,
        ∃ (C : Type z) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
          (∀ ε : ℝ, 0 < ε → ε < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
            Nonempty (@KleinerLottApprox (N b) C ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) mC
              (n b) o ε)) ∧
          Nonempty (@KleinerLottApprox (M α) C ((mM α).rescale r⁻¹ (inv_pos.mpr hr)) mC p o δ) := by
  obtain ⟨V, hTV, α₀, h⟩ := exists_good_annulus_riemannian_cone_scale g hmetric ρ hρ gN hmetricN
    hsecN n (fun a ha z => by
      obtain ⟨b, k, hk, hGH, -⟩ := hmodel a ha z
      exact ⟨b, k, hk, hGH⟩) hδ hδone (by linarith)
  refine ⟨V, hTV, α₀, fun α hα p => ?_⟩
  obtain ⟨r, hr, hTr, hrV, b, C, mC, o, hH, -, -, -, -, -, hK, -, hk⟩ := h α hα p
  exact ⟨r, hr, hTr, hrV, b, C, mC, o, hH, hK, hk⟩

end DifferentialGeometry.Geometry.Collapse
