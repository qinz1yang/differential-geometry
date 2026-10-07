import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70C1Neck_O48

/-!
# CH12-S116, group 1: CAP-EX, ray continuity and positive / round exclusion (`[FROZEN] CH12-S116`)

Abstract sequence setting: `N k` (the slice carriers), `g k`, `y k`, `φ k : LM → N k`, limit `(LM, gL)`,
isometric ray `γ` (`riemannianEDistOf gL (γ s) (γ s') = |s - s'|`).

* `ray_continuousOn_S116`: an isometric ray is continuous for the manifold topology
  (`PseudoEMetricSpace.ofRiemannianMetric`).
* `path_data_S116`: LIMP v2 (scalar + *radial* clause on `γ '' [0, t']`, `K ⊆ src k` eventually)
  gives eventual control of continuity, scalar ratios and radial distances along `φ k ∘ γ`.
* `preconnected_meets_frontier_S116`, `edist_sep_S116`: separator inequality for the Riemannian
  distance (a near-minimal path from outside `C` to `interior C` crosses `frontier C`), used by the
  cap exclusion (`¬ cap`) in `HANDOVER`.
* `noWhole_eventually_S116`: `φ k ∘ γ |[t, t']` is connected, so if `R_L(γ t') > C2 (R_L(γ t) + 1) + 1`
  the witness at `φ k (γ t)` is not a whole-component alternative (positive / round).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open Bundle
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace GC.LongTime.Ch12

universe u

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- An isometric ray is continuous for the manifold topology. -/
theorem ray_continuousOn_S116 {LM : Type u} [TopologicalSpace LM] [ChartedSpace ThreeSpace LM]
    [IsManifold ThreeModel ∞ LM] [T2Space LM] (gL : SmoothRiemannianMetric ThreeModel LM)
    {γ : ℝ → LM} {ρ : ℝ}
    (hγ : ∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
      riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) :
    ContinuousOn γ (Ico (0 : ℝ) ρ) := by
  let _ : LocallyCompactSpace LM :=
    Manifold.locallyCompact_of_finiteDimensional (M := LM) ThreeModel
  let _ : Bundle.RiemannianBundle (TangentSpace I3 : LM → Type _) :=
    ⟨gL.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle ThreeSpace (TangentSpace I3 : LM → Type _) :=
    ⟨gL.inner, gL.contMDiff.continuous, fun _ _ _ => rfl⟩
  let _ : PseudoEMetricSpace LM := PseudoEMetricSpace.ofRiemannianMetric ThreeModel LM
  have hiso : Isometry (fun t : Ico (0 : ℝ) ρ => γ t) := by
    intro a b
    have h := hγ a a.2 b b.2
    change riemannianEDistOf gL (γ a) (γ b) = _
    rw [h, Subtype.edist_eq, edist_dist, Real.dist_eq]
  have hc : Continuous (fun t : Ico (0 : ℝ) ρ => γ t) := hiso.continuous
  exact continuousOn_iff_continuous_domRestrict.mpr hc

/-- A preconnected set meeting `interior C` and the complement of `closure C` meets `frontier C`. -/
theorem preconnected_meets_frontier_S116 {X : Type*} [TopologicalSpace X] {S C : Set X}
    (hS : IsPreconnected S) {a b : X} (haS : a ∈ S) (hbS : b ∈ S) (ha : a ∈ interior C)
    (hb : b ∉ closure C) : ∃ x ∈ S, x ∈ frontier C := by
  by_contra h
  push Not at h
  have hsub : S ⊆ interior C ∪ (closure C)ᶜ := fun x hx => by
    by_cases hxi : x ∈ interior C
    · exact Or.inl hxi
    · exact Or.inr fun hxc => h x hx ⟨hxc, hxi⟩
  obtain ⟨x, -, hx1, hx2⟩ := hS _ _ isOpen_interior isClosed_closure.isOpen_compl hsub
    ⟨a, haS, ha⟩ ⟨b, hbS, hb⟩
  exact hx2 (interior_subset.trans subset_closure hx1)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
/-- **Separator inequality.**  A near-minimal path from `y ∉ closure C` to `p ∈ interior C` crosses
`frontier C` (Mathlib `exists_lt_of_riemannianEDist_lt`, `riemannianEDist_le_pathELength`,
`pathELength_add`): for every `r > d(y,p)` there is `a ∈ frontier C` with `d(y,a) + d(a,p) < r`. -/
theorem edist_sep_S116 {N : Type*} [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N] (g : SmoothRiemannianMetric ThreeModel N) {C : Set N} {y p : N}
    (hy : y ∉ closure C) (hp : p ∈ interior C) {r : ℝ≥0∞}
    (hr : riemannianEDistOf g y p < r) :
    ∃ a ∈ frontier C, riemannianEDistOf g y a + riemannianEDistOf g a p < r := by
  let _ : RiemannianBundle (TangentSpace I3 : N → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨c, hc0, hc1, hcs, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt (I := I3) hr
  have hpre : IsPreconnected (c '' Icc (0 : ℝ) 1) :=
    isPreconnected_Icc.image _ hcs.continuousOn
  obtain ⟨-, ⟨τ, hτ, rfl⟩, hτf⟩ := preconnected_meets_frontier_S116 hpre
    ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ (by rw [hc1]; exact hp)
    (by rw [hc0]; exact hy)
  refine ⟨c τ, hτf, ?_⟩
  have h1 : riemannianEDistOf g y (c τ) ≤ Manifold.pathELength I3 c 0 τ :=
    Manifold.riemannianEDist_le_pathELength (hcs.mono (Icc_subset_Icc le_rfl hτ.2)) hc0 rfl hτ.1
  have h2 : riemannianEDistOf g (c τ) p ≤ Manifold.pathELength I3 c τ 1 :=
    Manifold.riemannianEDist_le_pathELength (hcs.mono (Icc_subset_Icc hτ.1 le_rfl)) rfl hc1 hτ.2
  calc riemannianEDistOf g y (c τ) + riemannianEDistOf g (c τ) p
      ≤ Manifold.pathELength I3 c 0 τ + Manifold.pathELength I3 c τ 1 := add_le_add h1 h2
    _ = Manifold.pathELength I3 c 0 1 := Manifold.pathELength_add hτ.1 hτ.2
    _ < r := hlen

variable {N : ℕ → Type u} [∀ k, TopologicalSpace (N k)] [∀ k, ChartedSpace ThreeSpace (N k)]
  [∀ k, IsManifold ThreeModel ∞ (N k)]
  {LM : Type u} [TopologicalSpace LM] [ChartedSpace ThreeSpace LM] [IsManifold ThreeModel ∞ LM]

/-- Eventual control along `φ k ∘ γ` on `[0, t']` from LIMP v2 (`[FROZEN v2] CH12-O55 LIMP`):
continuity (`K ⊆ src k` eventually, `φ k` continuous on `src k`), scalar ratios, and the *radial*
distance `√R(y k) · d(y k, φ k (γ s)) ≈ s` (no pair clause is used). -/
theorem path_data_S116 (g : ∀ k, SmoothRiemannianMetric ThreeModel (N k)) (y : ∀ k, N k)
    (hy : Tendsto (fun k => metricScalarAt (g k) (y k)) atTop atTop)
    (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (φ : ∀ k, LM → N k)
    (src : ℕ → Set LM) (hsrc : ∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k)
    (hφ : ∀ k, ContinuousOn (φ k) (src k))
    (hconv : ∀ K : Set LM, IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, ∀ x ∈ K,
      |metricScalarAt (g k) (φ k x) / metricScalarAt (g k) (y k) - metricScalarAt gL x| < e ∧
      |Real.sqrt (metricScalarAt (g k) (y k)) *
          (riemannianEDistOf (g k) (y k) (φ k x)).toReal -
        (riemannianEDistOf gL x₀ x).toReal| < e)
    {γ : ℝ → LM} {t' : ℝ} (hx₀ : γ 0 = x₀) (hγc : ContinuousOn γ (Icc (0 : ℝ) t'))
    (hγd : ∀ s ∈ Icc (0 : ℝ) t', ∀ s' ∈ Icc (0 : ℝ) t',
      riemannianEDistOf gL (γ s) (γ s') = ENNReal.ofReal |s - s'|)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ k in atTop, 0 < metricScalarAt (g k) (y k) ∧
      ContinuousOn (fun s => φ k (γ s)) (Icc (0 : ℝ) t') ∧
      (∀ s ∈ Icc (0 : ℝ) t', |metricScalarAt (g k) (φ k (γ s)) / metricScalarAt (g k) (y k) -
        metricScalarAt gL (γ s)| < e) ∧
      ∀ s ∈ Icc (0 : ℝ) t',
        |(Real.sqrt (metricScalarAt (g k) (y k)) *
          (riemannianEDistOf (g k) (y k) (φ k (γ s))).toReal) - s| < e := by
  have hK : IsCompact (γ '' Icc (0 : ℝ) t') := isCompact_Icc.image_of_continuousOn hγc
  filter_upwards [hconv _ hK e he, hy.eventually_gt_atTop 0, hsrc _ hK] with k hk hpos hks
  refine ⟨hpos, ((hφ k).mono hks).comp hγc (fun s hs => ⟨s, hs, rfl⟩),
    fun s hs => (hk (γ s) ⟨s, hs, rfl⟩).1, fun s hs => ?_⟩
  have h := (hk (γ s) ⟨s, hs, rfl⟩).2
  rwa [← hx₀, hγd 0 ⟨le_rfl, hs.1.trans hs.2⟩ s hs, zero_sub, abs_neg,
    abs_of_nonneg hs.1, ENNReal.toReal_ofReal hs.1] at h

/-- **Positive / round exclusion.**  If `R_L(γ t') > C2 (R_L(γ t) + 1) + 1`, then for large `k` no
witness at `φ k (γ t)` is a whole-component alternative: the connected curve `φ k ∘ γ |[t, t']`
would stay in the whole component `= W.domain`, where `R ≤ C2 R(φ k (γ t))`. -/
theorem noWhole_eventually_S116 [∀ k, T2Space (N k)] [∀ k, SigmaCompactSpace (N k)]
    (g : ∀ k, SmoothRiemannianMetric ThreeModel (N k)) (y : ∀ k, N k)
    (hy : Tendsto (fun k => metricScalarAt (g k) (y k)) atTop atTop)
    (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (φ : ∀ k, LM → N k)
    (src : ℕ → Set LM) (hsrc : ∀ K : Set LM, IsCompact K → ∀ᶠ k in atTop, K ⊆ src k)
    (hφ : ∀ k, ContinuousOn (φ k) (src k))
    (hconv : ∀ K : Set LM, IsCompact K → ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, ∀ x ∈ K,
      |metricScalarAt (g k) (φ k x) / metricScalarAt (g k) (y k) - metricScalarAt gL x| < e ∧
      |Real.sqrt (metricScalarAt (g k) (y k)) *
          (riemannianEDistOf (g k) (y k) (φ k x)).toReal -
        (riemannianEDistOf gL x₀ x).toReal| < e)
    {γ : ℝ → LM} {t t' : ℝ} (hx₀ : γ 0 = x₀) (ht : 0 ≤ t) (htt' : t ≤ t')
    (hγc : ContinuousOn γ (Icc (0 : ℝ) t'))
    (hγd : ∀ s ∈ Icc (0 : ℝ) t', ∀ s' ∈ Icc (0 : ℝ) t',
      riemannianEDistOf gL (γ s) (γ s') = ENNReal.ofReal |s - s'|)
    (ε C1 C2 : ℝ)
    (hbig : C2 * (metricScalarAt gL (γ t) + 1) + 1 < metricScalarAt gL (γ t')) :
    ∀ᶠ k in atTop, ∀ W : SpatialCanonicalWitness (g k) ε C1 C2 (φ k (γ t)),
      ¬ W.alternative.isWholeComponent := by
  filter_upwards [path_data_S116 g y hy gL x₀ φ src hsrc hφ hconv hx₀ hγc hγd one_pos] with k hk
  obtain ⟨hpos, hσ, hratio, -⟩ := hk
  intro W hW
  have hC2 : 0 < C2 := lt_of_lt_of_le one_pos W.one_le_comparison_constant
  have hp := (abs_lt.mp (hratio t ⟨ht, htt'⟩)).2
  have hq := (abs_lt.mp (hratio t' ⟨ht.trans htt', le_rfl⟩)).1
  have hp' : metricScalarAt (g k) (φ k (γ t)) <
      (metricScalarAt gL (γ t) + 1) * metricScalarAt (g k) (y k) :=
    (div_lt_iff₀ hpos).mp (by linarith)
  have hq' : (metricScalarAt gL (γ t) + 1) * C2 * metricScalarAt (g k) (y k) <
      metricScalarAt (g k) (φ k (γ t')) := by
    have h1 : C2 * (metricScalarAt gL (γ t) + 1) < metricScalarAt (g k) (φ k (γ t')) /
        metricScalarAt (g k) (y k) := by linarith
    have h2 := (lt_div_iff₀ hpos).mp h1
    linarith
  have hmem : φ k (γ t') ∈ connectedComponent (φ k (γ t)) :=
    (isPreconnected_Icc.image _ (hσ.mono (Icc_subset_Icc ht le_rfl))).subset_connectedComponent
      ⟨t, ⟨le_rfl, htt'⟩, rfl⟩ ⟨t', ⟨htt', le_rfl⟩, rfl⟩
  have hD := W.alternative.eq_connectedComponent_of_isWholeComponent hW
  have hle := (W.scalar_bounds _ (hD ▸ hmem)).2
  nlinarith [mul_lt_mul_of_pos_left hp' hC2]

end GC.LongTime.Ch12
