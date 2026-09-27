import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapComparisonTransport
import DifferentialGeometry.Geometry.Neck.SpatialTolerance

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P] {g : SmoothRiemannianMetric I3 P}

private theorem two_le_ceil_inv_two_mul {alpha : ℝ} (ha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) : 2 ≤ ⌈(2 * alpha)⁻¹⌉₊ := by
  have h1 : (1 : ℝ) < (2 * alpha)⁻¹ := (one_lt_inv₀ (by linarith)).mpr (by linarith)
  have h2 : 1 < ⌈(2 * alpha)⁻¹⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h1)
  omega

theorem SpatialNeck.exists_transport_tolerance_of_metricComparisonOn {alpha : ℝ} {p : P}
    (nk : SpatialNeck g (neckModelTolerance alpha) p) (ha : 0 < alpha)
    (hsmall : 2 * alpha < 1 / 11) (U : TopologicalSpace.Opens P)
    (hout : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ U) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
        [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
        (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
        MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} ⌈(2 * alpha)⁻¹⌉₊ delta →
        ∃ nk' : SpatialNeck g' (2 * alpha) (F p), nk'.map = nk.map.trans F := by
  set q := metricScalarAt g p
  have hq : 0 < q := nk.Q_pos
  set order := ⌈(2 * alpha)⁻¹⌉₊
  set target := neckSourceTolerance alpha
  have ht : 0 < target := neckSourceTolerance_pos ha
  set n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  set B : ℝ := (∑ a ∈ Finset.range (order + 1), Real.sqrt (q⁻¹ ^ (a + 2))) + 1
  have hBsum : 0 ≤ ∑ a ∈ Finset.range (order + 1), Real.sqrt (q⁻¹ ^ (a + 2)) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hB : 0 < B := by linarith
  have hweight (a : ℕ) (ha : a ≤ order) : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ B := by
    have h0 := Finset.single_le_sum (fun b (_ : b ∈ Finset.range (order + 1)) =>
      Real.sqrt_nonneg (q⁻¹ ^ (b + 2))) (Finset.mem_range.mpr (by omega : a < order + 1))
    linarith
  set eta := min (q / 2) (q * target / (2 * (n + 1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  obtain ⟨delta₁, hdelta₁, hscalar⟩ :=
    exists_tolerance_abs_metricScalarAt_sub_lt (fun _ => g) 0 p heta
  have hd₂ : 0 < target / (4 * q * B) := by positivity
  refine ⟨min delta₁ (target / (4 * q * B)), lt_min hdelta₁ hd₂, ?_⟩
  intro N _ _ _ _ _ g' F hUF C
  have hp : p ∈ U := by
    have h0 := hout (nk.center, 0) ⟨trivial, neg_neg_of_pos (inv_pos.mpr ha), inv_pos.mpr ha⟩
    rwa [nk.center_eq] at h0
  have hclose := hscalar N (C.mono (subset_refl _) le_rfl (min_le_left _ _)) U hUF
    (subset_refl _) rfl (two_le_ceil_inv_two_mul ha hsmall) hp
  set c := metricScalarAt g' (F p)
  change |c - q| < eta at hclose
  have hlow := (abs_lt.mp hclose).1
  have hupp := (abs_lt.mp hclose).2
  have hetaq : eta ≤ q / 2 := min_le_left _ _
  have hc : 0 < c := by linarith
  have hc2 : c ≤ 2 * q := by linarith
  have hratio : |c / q - 1| * n ≤ target / 2 := by
    have he : c / q - 1 = (c - q) / q := by field_simp
    rw [he, abs_div, abs_of_pos hq]
    have h1 : |c - q| / q ≤ target / (2 * (n + 1)) := by
      rw [div_le_iff₀ hq]
      have h2 := hclose.le.trans (min_le_right (q / 2) (q * target / (2 * (n + 1))))
      calc |c - q| ≤ q * target / (2 * (n + 1)) := h2
        _ = target / (2 * (n + 1)) * q := by ring
    calc |c - q| / q * n ≤ target / (2 * (n + 1)) * n :=
          mul_le_mul_of_nonneg_right h1 hn
      _ ≤ target / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have hcmp := C.staticRescale (t := 0) rfl q c hq hc ht.le (fun a ha' => by
    have hdel : min delta₁ (target / (4 * q * B)) ≤ target / (4 * q * B) := min_le_right _ _
    have h1 : Real.sqrt (q⁻¹ ^ (a + 2)) * c * min delta₁ (target / (4 * q * B)) ≤
        B * (2 * q) * (target / (4 * q * B)) :=
      mul_le_mul (mul_le_mul (hweight a ha') hc2 hc.le hB.le) hdel (lt_min hdelta₁ hd₂).le
        (by positivity)
    have h2 : B * (2 * q) * (target / (4 * q * B)) = target / 2 := by field_simp; ring
    linarith)
  exact nk.exists_transport_of_local_comparisons hc F hcmp ha hsmall ht.le le_rfl le_rfl rfl
    hout hUF

theorem SpatialLocalCap.exists_deep_transport_tolerance_of_metricComparisonOn
    {alpha eps rho R margin : ℝ} {x : P} {W : Set P} (L : SpatialLocalCap g eps x W)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (heps : eps ≤ neckModelTolerance alpha)
    (U : TopologicalSpace.Opens P) (hWU : W ⊆ U) (hWc : IsCompact W)
    (hout : ∀ i, ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, (L.chain.necks i).map y ∈ U)
    (hQ : 0 < metricScalarAt g x) (hmargin : 0 < margin) (hrho : 0 ≤ rho)
    (hroom : 3 * rho < R) (hcpt : IsCompact (riemannianClosedBallOf g x R))
    (hball : riemannianClosedBallOf g x R ⊆ U)
    (htube : L.tube ⊆ riemannianClosedBallOf g x rho)
    (hdeep : ∀ y ∈ L.tube, 10000 / Real.sqrt (metricScalarAt g x) + margin ≤ metricDistance g x y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
        [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
        (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
        MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} ⌈(2 * alpha)⁻¹⌉₊ delta →
        ∃ L' : SpatialLocalCap g' (2 * alpha) (F x) (F '' W),
          L'.tubeMap = L.tubeMap.trans F ∧ L'.tube = F '' L.tube ∧
          ∀ y ∈ L'.tube,
            10000 / Real.sqrt (metricScalarAt g' (F x)) ≤ metricDistance g' (F x) y := by
  have hmodel : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  have htr := fun i : Fin L.chain.count =>
    ((L.chain.necks i).mono heps hmodel).exists_transport_tolerance_of_metricComparisonOn
      ha hsmall U (hout i)
  choose delta hdelta htr using htr
  obtain ⟨deltaD, hdeltaD, hdepth⟩ := exists_tolerance_depth_image_of_metricComparisonOn
    (fun _ => g) 0 x hmargin hQ hrho hroom hcpt htube hdeep
  have hne : (Finset.univ : Finset (Fin L.chain.count)).Nonempty :=
    ⟨⟨0, L.chain.count_pos⟩, Finset.mem_univ _⟩
  have hmin : 0 < Finset.univ.inf' hne delta :=
    (Finset.lt_inf'_iff hne).mpr fun i _ => hdelta i
  refine ⟨min (Finset.univ.inf' hne delta) deltaD, lt_min hmin hdeltaD, ?_⟩
  intro N _ _ _ _ _ g' F hUF C
  have hneck : ∀ i, ∃ nk' : SpatialNeck g' (2 * alpha) (F (L.chain.centers i)),
      nk'.map = (L.chain.necks i).map.trans F := fun i =>
    htr i N g' F hUF (C.mono (subset_refl _) le_rfl
      ((min_le_left _ _).trans (Finset.inf'_le _ (Finset.mem_univ i))))
  choose necks hmap using hneck
  have htubeF : L.tube ⊆ F.source :=
    ((subset_union_right.trans L.union_eq.ge).trans hWU).trans hUF
  let chain := L.chain.transport F htubeF necks hmap
  refine ⟨L.pushforward F (hWU.trans hUF) hWc chain,
    L.pushforward_tubeMap F (hWU.trans hUF) hWc chain,
    L.pushforward_tube F (hWU.trans hUF) hWc chain, ?_⟩
  have hd := hdepth N (g := fun _ => g') (F := F) (U := U) (times := {0})
    (order := ⌈(2 * alpha)⁻¹⌉₊) (C.mono (subset_refl _) le_rfl (min_le_right _ _)) hball hUF
    (mem_singleton 0) (two_le_ceil_inv_two_mul ha hsmall)
  rw [L.pushforward_tube F (hWU.trans hUF) hWc chain]
  exact hd

theorem SpatialCanonicalAlternative.exists_transport_tolerance_of_metricComparisonOn
    {alpha eps C rho R margin : ℝ} {x : P} {W : Set P}
    (A : SpatialCanonicalAlternative g eps C x W)
    (hshape : (∃ n, A = .neck n) ∨ ∃ c d, A = .cap c d)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (heps : eps ≤ neckModelTolerance alpha)
    (U : TopologicalSpace.Opens P) (hWU : W ⊆ U) (hWc : IsCompact W)
    (hQ : 0 < metricScalarAt g x)
    (hneck : ∀ n, A = .neck n → ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, n.neck.map y ∈ U)
    (hcap : ∀ c d, A = .cap c d →
      (∀ i, ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, (c.chain.necks i).map y ∈ U) ∧
      0 < margin ∧ 0 ≤ rho ∧ 3 * rho < R ∧ IsCompact (riemannianClosedBallOf g x R) ∧
      riemannianClosedBallOf g x R ⊆ U ∧ c.tube ⊆ riemannianClosedBallOf g x rho ∧
      ∀ y ∈ c.tube, 10000 / Real.sqrt (metricScalarAt g x) + margin ≤ metricDistance g x y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
        [T2Space N] [SigmaCompactSpace N] (g' : SmoothRiemannianMetric I3 N)
        (F : PartialDiffeomorph I3 I3 P N ∞), (U : Set P) ⊆ F.source →
        MetricComparisonOn (fun _ => g) (fun _ => g') F U {0} ⌈(2 * alpha)⁻¹⌉₊ delta →
        Nonempty (SpatialCanonicalAlternative g' (2 * alpha) C (F x) (F '' W)) := by
  rcases hshape with ⟨n, rfl⟩ | ⟨c, d, rfl⟩
  · have hmodel : neckModelTolerance alpha < 1 / 11 :=
      (neckModelTolerance_le alpha).trans_lt (by linarith)
    obtain ⟨delta, hdelta, htr⟩ :=
      (n.neck.mono heps hmodel).exists_transport_tolerance_of_metricComparisonOn ha hsmall U
        (hneck n rfl)
    refine ⟨delta, hdelta, ?_⟩
    intro N _ _ _ _ _ g' F hUF Cmp
    obtain ⟨nk', hmap⟩ := htr N g' F hUF Cmp
    have hWF : W ⊆ F.source := hWU.trans hUF
    have hc : IsCompact (F '' W) :=
      hWc.image_of_continuousOn (F.contMDiffOn_toFun.continuousOn.mono hWF)
    refine ⟨.neck { neck := nk', region_eq := ?_, boundary_eq := ?_ }⟩
    · rw [hmap, partialDiffeomorph_image_trans]
      exact congrArg (fun s => F '' s) n.region_eq
    · rw [← partialDiffeomorph_image_frontier_of_subset_source F hWF hWc.isClosed hc.isClosed,
        hmap, partialDiffeomorph_image_trans]
      exact congrArg (fun s => F '' s) n.boundary_eq
  · obtain ⟨hout, hmargin, hrho, hroom, hcpt, hball, htube, hdeep⟩ := hcap c d rfl
    obtain ⟨delta, hdelta, htr⟩ := c.exists_deep_transport_tolerance_of_metricComparisonOn ha
      hsmall heps U hWU hWc hout hQ hmargin hrho hroom hcpt hball htube hdeep
    refine ⟨delta, hdelta, ?_⟩
    intro N _ _ _ _ _ g' F hUF Cmp
    obtain ⟨L', -, -, hdeep'⟩ := htr N g' F hUF Cmp
    exact ⟨.cap L' hdeep'⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
