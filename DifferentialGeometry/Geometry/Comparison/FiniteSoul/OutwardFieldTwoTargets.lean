import DifferentialGeometry.Geometry.Comparison.FiniteSoul.OutwardFieldDirection
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.OutwardPatch
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# POINT: a bounded smooth field outward for a point and a compact set, finite-order metric
(lane CMS3-FLOW, G2)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.9, §3 "POINT", §4 §11;
frozen statement `exists_outward_field_two_targets_finite`
(`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean` §11), confirmed by the external review (§12).
Finite LC52 + LC53 without the LC21 cone.

Route: the finite LC52 (`exists_common_outward_direction_finite`) gives unit vectors with margin
`−1/2` against both direction families far out; S-PATCH (`exists_contMDiff_outward_field`, CMS-H) for the
union of the two (closed) direction families on `{d(p, ·) ≥ A₁}` gives one smooth field `V` with
`g(V, V) < 4` and margin `< −1/4` there; a smooth cutoff vanishing on `B̄(p, A₀)` and equal to `1` on
`{d(p, ·) ≥ A₁}` gives the field `Xf = χ V`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The union of the minimizing-direction families of `{p}` and of a closed `S` is closed in `TM`. -/
theorem mem_union_finiteMinimizingDirectionsTo_of_tendsto
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {S : Set M} (hS : IsClosed S) (pk : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    (hk : ∀ k, (pk k).snd ∈ g.finiteMinimizingDirectionsTo {p} (pk k).proj ∪
      g.finiteMinimizingDirectionsTo S (pk k).proj)
    (hlim : Tendsto pk atTop (𝓝 pInf)) :
    pInf.snd ∈ g.finiteMinimizingDirectionsTo {p} pInf.proj ∪
      g.finiteMinimizingDirectionsTo S pInf.proj := by
  by_cases h1 : ∃ᶠ k in atTop, (pk k).snd ∈ g.finiteMinimizingDirectionsTo {p} (pk k).proj
  · obtain ⟨φ, hφ, hφk⟩ := extraction_of_frequently_atTop h1
    exact Or.inl (g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm isClosed_singleton hφk
      (hlim.comp hφ.tendsto_atTop))
  · have h2 : ∀ᶠ k in atTop, (pk k).snd ∈ g.finiteMinimizingDirectionsTo S (pk k).proj := by
      rw [not_frequently] at h1
      filter_upwards [h1] with k hk'
      exact (hk k).resolve_left hk'
    obtain ⟨φ, hφ, hφk⟩ := extraction_of_eventually_atTop h2
    exact Or.inr (g.mem_finiteMinimizingDirectionsTo_of_tendsto hr hnorm hS hφk
      (hlim.comp hφ.tendsto_atTop))

/-- **POINT** (finite LC52 + LC53; `2 ≤ r`, `sec ≥ 0`). A smooth field, zero near `p`, with norm `< 2` and
margin `−1/4` against all minimizing directions to `p` AND to the compact `S` far out. Route: W3-F5b's
two-hinge real kernel (no cone) + finite hinge (CMS-B `dist_sq_le_hinge_finite`) + S-PATCH (CMS-H). -/
theorem exists_outward_field_two_targets_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    (p : M) {S : Set M} (hSc : IsCompact S) :
    ∃ A₀ A₁ : ℝ, 0 < A₀ ∧ A₀ < A₁ ∧ S ⊆ ball p A₀ ∧ ∃ Xf : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x => (⟨x, Xf x⟩ : TangentBundle I M)) ∧
      (∀ q, g.inner q (Xf q) (Xf q) < 4) ∧ (∀ q, dist p q ≤ A₀ → Xf q = 0) ∧
      ∀ q, A₁ ≤ dist p q →
        ∀ v ∈ g.finiteMinimizingDirectionsTo {p} q ∪ g.finiteMinimizingDirectionsTo S q,
          g.inner q (Xf q) v ≤ -(1 / 4) := by
  classical
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨A, hA, hout⟩ := exists_common_outward_direction_finite g hr hnorm hsec p hSc
  obtain ⟨D, hD⟩ := hSc.isBounded.subset_closedBall p
  set A₀ : ℝ := max A (D + 1) with hA₀def
  set A₁ : ℝ := A₀ + 1 with hA₁def
  have hA₀ : 0 < A₀ := lt_max_of_lt_left hA
  have hAA₀ : A ≤ A₀ := le_max_left _ _
  have hA₀₁ : A₀ < A₁ := by rw [hA₁def]; linarith
  have hSball : S ⊆ ball p A₀ := by
    intro s hs
    have := hD hs
    rw [mem_closedBall] at this
    rw [mem_ball]
    linarith [le_max_right A (D + 1)]
  set Afar : Set M := {q | A₁ ≤ dist p q} with hAfar
  have hAfarc : IsClosed Afar := isClosed_le continuous_const (continuous_const.dist continuous_id)
  -- pointwise outward unit vectors far out
  set v : (x : M) → TangentSpace I x := fun x =>
    if h : A ≤ dist p x then Classical.choose (hout x h) else 0 with hvdef
  have hvspec : ∀ x, A ≤ dist p x → g.inner x (v x) (v x) = 1 ∧
      ∀ u ∈ g.finiteMinimizingDirectionsTo {p} x ∪ g.finiteMinimizingDirectionsTo S x,
        g.inner x (v x) u < -(1 / 2) := by
    intro x hx
    have h := Classical.choose_spec (hout x hx)
    have hv : v x = Classical.choose (hout x hx) := by
      rw [hvdef]
      simp only [hx, ↓reduceDIte]
      rfl
    rw [hv]
    exact h
  have hfar : ∀ x ∈ Afar, A ≤ dist p x := fun x hx =>
    hAA₀.trans (hA₀₁.le.trans hx)
  obtain ⟨V, hVs, hVR, O, -, hAO, hVout⟩ := exists_contMDiff_outward_field g
    (fun x => g.finiteMinimizingDirectionsTo {p} x ∪ g.finiteMinimizingDirectionsTo S x)
    (fun x u hu => by rcases hu with hu | hu <;> exact hu.1.le)
    (mem_union_finiteMinimizingDirectionsTo_of_tendsto g hr hnorm p hSc.isClosed)
    hAfarc (R := 2) (c := 1 / 4) two_pos v
    (fun x hx => by rw [(hvspec x (hfar x hx)).1]; norm_num)
    (fun x hx u hu => ((hvspec x (hfar x hx)).2 u hu).trans (by norm_num))
  -- the cutoff
  have hdisj : Disjoint (closedBall p A₀) Afar := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [mem_closedBall, dist_comm] at hx
    change A₁ ≤ dist p x at hx'
    linarith
  obtain ⟨χ, hχ0, hχ1, hχI⟩ := exists_contMDiffMap_zero_one_of_isClosed I (n := ⊤)
    isClosed_closedBall hAfarc hdisj
  set Xf : (x : M) → TangentSpace I x := fun x => χ x • V x with hXf
  refine ⟨A₀, A₁, hA₀, hA₀₁, hSball, Xf, ?_, fun q => ?_, fun q hq => ?_, fun q hq u hu => ?_⟩
  · exact ContMDiff.smul_section (f := fun x => χ x) (s := V) χ.contMDiff hVs
  · change g.inner q (χ q • V q) (χ q • V q) < 4
    rw [DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self]
    have h0 := DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g q (V q)
    have hR := hVR q
    obtain ⟨hc0, hc1⟩ := hχI q
    have hsq : χ q ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · have h : χ q = 0 := hχ0 (by rw [mem_closedBall, dist_comm]; exact hq)
    change χ q • V q = 0
    rw [h, zero_smul]
  · have h : χ q = 1 := hχ1 hq
    change g.inner q (χ q • V q) u ≤ -(1 / 4)
    rw [h, one_smul]
    exact (hVout q (hAO hq) u hu).le

end DifferentialGeometry.Geometry.FiniteSoul
