import DifferentialGeometry.Topology.Manifold.ChartPatch.FiniteCover
import DifferentialGeometry.Topology.UniformConvergence.Chart
import DifferentialGeometry.Topology.Manifold.CompactCoreEmbedding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficientConvergence
import DifferentialGeometry.Analysis.Calculus.MapConvergence.FiniteInjectivity
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.LocalDiffeomorph

/-!
# LFR14, interface I-STAGE: comparison maps on one compact buffer

Blueprint LFR14 (master207A.tex:25869), step 4 ("Constructing actual maps on each compact
buffer", A:25988) and the embedding part of step 5, on one compact buffer. The input is the limit
chart data of steps 1–3 (interface I-LIM): order-`K` limit chart parametrizations `σ a` of the
limit `N`, smooth source charts `d a i`, convex buffers `D a`, `C^K` transition convergence,
`C^{K-1}` coefficient limits `b a`, and pointed ball approximations `F i` with chart capture.

* `eventually_abs_dist_sub_dist_lt_of_pointedBallApprox`: maps captured in the approximation
  balls with `F i ∘ f i → id` uniformly have distortion `→ 0`.
* `eventually_isLocalDiffeomorphOn_and_injOn_of_chart_convergence`: on a convex chart piece,
  `C¹` chart convergence to the identity gives eventual local diffeomorphisms (I-LOCDIFF) that are
  injective (`MapCPConvergenceOn.eventually_injOn`).
* `eventually_exists_partialDiffeomorph_of_chart_cover_convergence`: eventual partial
  diffeomorphisms with a prescribed relatively compact open source (D's compact-core embedding).
* `exists_stage_comparison_maps`: the frozen interface I-STAGE
  (`build-logs/scratch/D-LFR14/Interfaces.lean:197`) without the unused instance
  `[ProperSpace N]`; the verbatim frozen statement is the `example` at the end of the file.
  Route: patching (`exists_contMDiffOn_with_chart_convergence_on_finite_union`), metric clause
  (`pullbackMetricCoefficients_comp_mapCP_convergence_of_chart_convergence`), capture and
  `qᵢ ∘ Fmᵢ → id` (`eventually_mapsTo_and_tendstoUniformlyOn_of_chart_cover`), distortion,
  embeddings.
* `exists_stage_comparison_maps_of_isCompact`: consumer form over a compact set covered by the
  chart targets.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry GC.MetricGeometry

/-- **Distortion of comparison maps.** If `f i` maps `C` into the ball where the pointed ball
approximation `F i` is defined, and `F i ∘ f i → id` uniformly on `C`, then the distortion of
`f i` on `C` tends to zero. -/
theorem eventually_abs_dist_sub_dist_lt_of_pointedBallApprox
    {X : Type*} [MetricSpace X] {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)]
    {p : ∀ i, Y i} {q : X} {R ε : ℕ → ℝ} (F : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0)) (f : ∀ i, X → Y i) {C : Set X}
    (hmaps : ∀ᶠ i in atTop, MapsTo (f i) C (closedBall (p i) (R i)))
    (hconv : TendstoUniformlyOn (fun i x => (F i).extendToWholeSpace (f i x)) id atTop C)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in atTop, ∀ x ∈ C, ∀ y ∈ C, |dist (f i x) (f i y) - dist x y| < η := by
  have hη3 : 0 < η / 3 := by positivity
  have hεη : ∀ᶠ i in atTop, ε i < η / 3 := hε.eventually (gt_mem_nhds hη3)
  have hunif := Metric.tendstoUniformlyOn_iff.mp hconv (η / 3) hη3
  filter_upwards [hmaps, hεη, hunif] with i hmi hεi hui x hx y hy
  have hxR : dist (f i x) (p i) ≤ R i := mem_closedBall.mp (hmi hx)
  have hyR : dist (f i y) (p i) ≤ R i := mem_closedBall.mp (hmi hy)
  have hdist := (F i).distortion ⟨f i x, hxR⟩ ⟨f i y, hyR⟩
  rw [← (F i).extendToWholeSpace_apply (f i x) hxR,
    ← (F i).extendToWholeSpace_apply (f i y) hyR] at hdist
  have hx' := hui x hx
  have hy' := hui y hy
  simp only [id_eq] at hx' hy'
  have htri := dist_dist_dist_le x y ((F i).extendToWholeSpace (f i x))
    ((F i).extendToWholeSpace (f i y))
  rw [Real.dist_eq] at htri
  rw [abs_lt] at hdist ⊢
  constructor
  · nlinarith [abs_lt.mp (lt_of_le_of_lt htri (add_lt_add hx' hy'))]
  · nlinarith [abs_lt.mp (lt_of_le_of_lt htri (add_lt_add hx' hy'))]

section Embedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Local diffeomorphism and injectivity on a convex chart piece.** If the chart
representation `(d i)⁻¹ ∘ Fᵢ ∘ σ` of `C^K` maps (`1 ≤ K`) converges to the identity in `C¹` on a
convex set `L ⊆ σ.source ∩ σ⁻¹ W` with eventual chart capture, then eventually `Fᵢ` is a `C^K`
local diffeomorphism at every point of `σ '' L` and injective on `σ '' L`. -/
theorem eventually_isLocalDiffeomorphOn_and_injOn_of_chart_convergence
    {X : Type*} [TopologicalSpace X] [ChartedSpace E X]
    {K : ℕ} (hK : 1 ≤ K)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    (σ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) K)
    (F : ∀ i, X → Y i) {W : Set X} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    {L : Set E} (hLconv : Convex ℝ L) (hLW : L ⊆ σ.source ∩ σ ⁻¹' W)
    (hcap : ∀ᶠ i in atTop, MapsTo (F i ∘ σ) L (d i).target)
    (hcoord : MapCPConvergenceOn L 1 (fun i x => (d i).symm (F i (σ x))) id) :
    ∀ᶠ i in atTop, IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) (σ '' L) ∧
      InjOn (F i) (σ '' L) := by
  have hK0 : ((K : ℕ) : ℕ∞ω) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hK
  have hdiff : ∀ᶠ i in atTop, ∀ z ∈ L,
      DifferentiableAt ℝ (fun x => (d i).symm (F i (σ x))) z := by
    filter_upwards [hcap] with i hi z hz
    have hσz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K σ z :=
      σ.contMDiffOn_toFun.contMDiffAt (σ.open_source.mem_nhds (hLW hz).1)
    have hFz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) (σ z) :=
      (hF i).contMDiffAt (hW.mem_nhds (hLW hz).2)
    have hdz : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) K (d i).symm (F i (σ z)) :=
      (d i).contMDiffOn_invFun.contMDiffAt ((d i).open_target.mem_nhds (hi hz))
    exact mdifferentiableAt_iff_differentiableAt.mp
      ((hdz.comp z (hFz.comp z hσz)).mdifferentiableAt hK0)
  have hinj := MapCPConvergenceOn.eventually_injOn hcoord hLconv hdiff
  filter_upwards [eventually_isLocalDiffeomorphOn_of_chart_convergence hK σ d F hW hF hLW hcap
    hcoord, hinj] with i hloc hi
  refine ⟨hloc, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  rw [hi hx hy (by simp only [hxy])]

/-- **Embeddings on a relatively compact open set.** Let `Fᵢ` be `C^K` on an open `W` covered by
the targets of chart parametrizations `σ a`, with eventual capture and `C¹` convergence to the
identity of `(d a i)⁻¹ ∘ Fᵢ ∘ σ a` on compacts of `σ a⁻¹ W`, and let `qᵢ ∘ Fᵢ → id` uniformly on
the compact closure of an open `O ⊆ W`. Then eventually `Fᵢ` is a `C^K` partial diffeomorphism
with source `O`. -/
theorem eventually_exists_partialDiffeomorph_of_chart_cover_convergence
    {X : Type*} [MetricSpace X] [ChartedSpace E X] [Nonempty X]
    {K : ℕ} (hK : 1 ≤ K)
    {Y : ℕ → Type*} [∀ i, TopologicalSpace (Y i)] [∀ i, ChartedSpace E (Y i)] {α : Type*}
    (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E X K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) K)
    (F : ∀ i, X → Y i) {W : Set X} (hW : IsOpen W)
    (hF : ∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) W)
    (hcover : W ⊆ ⋃ a, (σ a).target)
    (hcoord : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
      (∀ᶠ i in atTop, MapsTo (F i ∘ σ a) L (d a i).target) ∧
      MapCPConvergenceOn L 1 (fun i x => (d a i).symm (F i (σ a x))) id)
    (q : ∀ i, Y i → X) {O : Set X} (hO : IsOpen O) (hOc : IsCompact (closure O))
    (hOW : closure O ⊆ W)
    (hconv : TendstoUniformlyOn (fun i x => q i (F i x)) id atTop (closure O)) :
    ∀ᶠ i in atTop, ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) X (Y i) K,
      e.source = O ∧ (e : X → Y i) = F i := by
  have hlocal : ∀ x ∈ closure O, ∃ V ∈ 𝓝 x, ∀ᶠ i in atTop,
      IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (F i) V ∧ InjOn (F i) V := by
    intro x hx
    obtain ⟨a, hxa⟩ := mem_iUnion.mp (hcover (hOW hx))
    set u : E := (σ a).symm x with hu
    have hus : u ∈ (σ a).source := (σ a).toPartialEquiv.map_target hxa
    have hσu : σ a u = x := (σ a).toPartialEquiv.right_inv hxa
    have hU : IsOpen ((σ a).source ∩ σ a ⁻¹' W) :=
      (σ a).toOpenPartialHomeomorph.isOpen_inter_preimage hW
    have huU : u ∈ (σ a).source ∩ σ a ⁻¹' W := ⟨hus, by rw [mem_preimage, hσu]; exact hOW hx⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU u huU
    have hL : IsCompact (closedBall u (r / 2)) := isCompact_closedBall u (r / 2)
    have hLU : closedBall u (r / 2) ⊆ (σ a).source ∩ σ a ⁻¹' W :=
      (closedBall_subset_ball (by linarith)).trans hrU
    obtain ⟨hcap, hconvL⟩ := hcoord a _ hL hLU
    refine ⟨σ a '' ball u (r / 2), ?_, ?_⟩
    · rw [← hσu]
      exact (σ a).toOpenPartialHomeomorph.image_mem_nhds hus (ball_mem_nhds u (by linarith))
    · filter_upwards [eventually_isLocalDiffeomorphOn_and_injOn_of_chart_convergence hK (σ a)
        (d a) F hW hF (convex_closedBall u (r / 2)) hLU hcap hconvL] with i hi
      have hsub : σ a '' ball u (r / 2) ⊆ σ a '' closedBall u (r / 2) :=
        image_mono ball_subset_closedBall
      exact ⟨fun y => hi.1 ⟨y, hsub y.2⟩, hi.2.mono hsub⟩
  filter_upwards [DifferentialGeometry.Topology.Manifold.eventually_exists_partialDiffeomorph_of_local_diffeomorphs
    hOc hO subset_closure F q (K : ℕ∞ω) hlocal hconv.tendstoLocallyUniformlyOn continuousOn_id
    (injOn_id _)] with i hi
  obtain ⟨e, he, -, hef⟩ := hi
  exact ⟨e, he, hef⟩

end Embedding

/-- **I-STAGE (LFR14 step 4 on one compact buffer).** From the limit chart data (limit chart
parametrizations `σ a` of order `K`, smooth source charts `d a i`, convex buffers `D a`, `C^K`
transition convergence, `C^{K-1}` coefficient limits `b a`, pointed ball approximations `F i`
with chart capture), for a finite family of compact chart pieces `C a ⊆ (σ a).target` there are
an open `W ⊇ ⋃ C a ∪ {q}` with compact closure and `C^K` maps `Fm i` on `W` that are pointed
eventually, `C^K` close to the identity in every chart, pull `g i` back `C^{K-1}`-close to `b a`,
satisfy `qᵢ ∘ Fm i → id` with distortion `→ 0` on compacts of `W`, and are eventually partial
diffeomorphisms on every relatively compact open `O` with `closure O ⊆ W`.

This is the frozen interface `build-logs/scratch/D-LFR14/Interfaces.lean:197` without the
instance `[ProperSpace N]`, which the argument does not use; the verbatim frozen statement is the
`example` below. -/
theorem exists_stage_comparison_maps
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ChartedSpace E N]
    {K : ℕ} (hK : 1 ≤ K) [IsManifold 𝓘(ℝ, E) K N]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {α : Type*} (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (D : α → Set E)
    (hD : ∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source)
    (htrans : ∀ a c (L : Set E), IsCompact L → L ⊆ ((σ a).trans (σ c).symm).source →
      MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
      ∀ S : Set E, IsCompact S → S ⊆ D a →
        MapCPConvergenceOn S (K - 1) (fun i => pullbackMetricCoefficients (g i) (d a i)) (b a))
    (q : N) (p : ∀ i, Y i) (a₀ : α)
    (h₀ : 0 ∈ (σ a₀).source ∧ σ a₀ 0 = q ∧ ∀ i, d a₀ i 0 = p i)
    (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0))
    (hchart : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source →
      (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p i) (R i))) ∧
      TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L)
    (S : Finset α) (C : α → Set N) (hC : ∀ a ∈ S, IsCompact (C a) ∧ C a ⊆ (σ a).target) :
    ∃ (W : Set N) (Fm : ∀ i, N → Y i),
      IsOpen W ∧ IsCompact (closure W) ∧ ((⋃ a ∈ S, C a) ∪ {q}) ⊆ W ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (Fm i) W) ∧
      (∀ᶠ i in atTop, Fm i q = p i) ∧
      (∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
        (∀ᶠ i in atTop, MapsTo (Fm i ∘ σ a) L (d a i).target) ∧
        MapCPConvergenceOn L K (fun i x => (d a i).symm (Fm i (σ a x))) id ∧
        MapCPConvergenceOn L (K - 1)
          (fun i => pullbackMetricCoefficients (g i) (Fm i ∘ σ a)) (b a)) ∧
      (∀ C' : Set N, IsCompact C' → C' ⊆ W →
        TendstoUniformlyOn (fun i x => (F i).extendToWholeSpace (Fm i x)) id atTop C' ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ x ∈ C', ∀ y ∈ C',
          |dist (Fm i x) (Fm i y) - dist x y| < η) ∧
      (∀ O : Set N, IsOpen O → IsCompact (closure O) → closure O ⊆ W →
        ∀ᶠ i in atTop, ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K,
          e.source = O ∧ (e : N → Y i) = Fm i) := by
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hb ⊢
  have : Nonempty N := ⟨q⟩
  -- the source charts, lowered to order `K`
  let d' : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) (k + 1 : ℕ) := fun a i =>
    DifferentialGeometry.PartialDiffeomorph.ofLE (d a i) (by exact_mod_cast le_top)
  have hq : q ∈ (σ a₀).target := h₀.2.1 ▸ (σ a₀).toPartialEquiv.map_source h₀.1
  -- step 1: the patched maps (FiniteCover)
  obtain ⟨W, Fm, hW, hWc, hCW, hWσ, hFm, hgerm, hcoord⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_contMDiffOn_with_chart_convergence_on_finite_union
      σ d' D (fun a => (hD a).1) (fun a => (hD a).2.1) (fun a => (hD a).2.2.1)
      (fun a i => (hD a).2.2.2 i) htrans a₀ q hq S C (fun a ha => (hC a ha).1)
      (fun a ha => (hC a ha).2)
  have hcover : W ⊆ ⋃ a, (σ a).target := by
    intro x hx
    rcases hWσ (subset_closure hx) with hx₀ | hxS
    · exact mem_iUnion.mpr ⟨a₀, hx₀⟩
    · obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hxS
      exact mem_iUnion.mpr ⟨a, hxa⟩
  -- step 3: capture in the approximation balls and `qᵢ ∘ Fm i → id` (Chart)
  have hcap : ∀ C' : Set N, IsCompact C' → C' ⊆ W →
      (∀ᶠ i in atTop, MapsTo (Fm i) C' (closedBall (p i) (R i))) ∧
      TendstoUniformlyOn (fun i x => (F i).extendToWholeSpace (Fm i x)) id atTop C' :=
    fun C' hC' hC'W =>
      eventually_mapsTo_and_tendstoUniformlyOn_of_chart_cover hC' hC'W
        (fun a => (σ a).toOpenPartialHomeomorph) (fun a i => (d a i).toOpenPartialHomeomorph)
        Fm (fun i => (F i).extendToWholeSpace) (fun i => closedBall (p i) (R i)) hcover
        (fun a L hL hLW => ⟨(hcoord a L hL hLW).1, tendstoUniformlyOn_of_cPConvergence
          ((hcoord a L hL hLW).2.mono_order (Nat.zero_le _))⟩)
        (fun a L hL hLs => (hchart a L hL hLs).2) (fun a L hL hLs => (hchart a L hL hLs).1)
  refine ⟨W, Fm, hW, hWc, hCW, hFm, ?_, ?_, ?_, ?_⟩
  · -- pointedness, from the germ at `q`
    filter_upwards [hgerm] with i hi
    rw [hi.eq_of_nhds]
    have h0 : (σ a₀).symm q = 0 := by
      rw [← h₀.2.1]
      exact (σ a₀).toPartialEquiv.left_inv h₀.1
    change d a₀ i ((σ a₀).symm q) = p i
    rw [h0]
    exact h₀.2.2 i
  · -- chart clauses; step 2: the metric clause (FiniteCoefficientConvergence)
    intro a L hL hLW
    refine ⟨(hcoord a L hL hLW).1, (hcoord a L hL hLW).2, ?_⟩
    exact DifferentialGeometry.Geometry.pullbackMetricCoefficients_comp_mapCP_convergence_of_chart_convergence
      hW (hD a).1 (σ a) (fun _ hx => (hD a).2.2.1 hx.1) g (d a) (fun i => (hD a).2.2.2 i) Fm
      (Eventually.of_forall hFm) (fun L hL hLW => (hcoord a L hL hLW).1)
      (fun L hL hLW => (hcoord a L hL hLW).2) (fun S hS hSD => (hb a).2 S hS hSD) (hb a).1 hL
      hLW
  · -- step 4: uniform convergence and distortion
    intro C' hC' hC'W
    exact ⟨(hcap C' hC' hC'W).2, fun η hη =>
      eventually_abs_dist_sub_dist_lt_of_pointedBallApprox F hε Fm (hcap C' hC' hC'W).1
        (hcap C' hC' hC'W).2 hη⟩
  · -- step 5: embeddings
    intro O hO hOc hOW
    exact eventually_exists_partialDiffeomorph_of_chart_cover_convergence hK σ d' Fm hW hFm hcover
      (fun a L hL hLW => ⟨(hcoord a L hL hLW).1, (hcoord a L hL hLW).2.mono_order hK⟩)
      (fun i => (F i).extendToWholeSpace) hO hOc hOW (hcap _ hOc (hOW.trans subset_rfl)).2

/-- **Consumer: a stage over a compact set.** If a compact `B ⊆ N` is covered by the targets of
the `σ a`, I-STAGE produces comparison maps on an open `W ⊇ B ∪ {q}` (finitely many targets
cover `B`, and `B` splits into compact pieces inside them). This is the form in which LFR14's
assembly step uses I-STAGE, with `B` a closed ball about `q`. -/
theorem exists_stage_comparison_maps_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ChartedSpace E N]
    {K : ℕ} (hK : 1 ≤ K) [IsManifold 𝓘(ℝ, E) K N]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {α : Type*} (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (D : α → Set E)
    (hD : ∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source)
    (htrans : ∀ a c (L : Set E), IsCompact L → L ⊆ ((σ a).trans (σ c).symm).source →
      MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
      ∀ S : Set E, IsCompact S → S ⊆ D a →
        MapCPConvergenceOn S (K - 1) (fun i => pullbackMetricCoefficients (g i) (d a i)) (b a))
    (q : N) (p : ∀ i, Y i) (a₀ : α)
    (h₀ : 0 ∈ (σ a₀).source ∧ σ a₀ 0 = q ∧ ∀ i, d a₀ i 0 = p i)
    (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0))
    (hchart : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source →
      (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p i) (R i))) ∧
      TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L)
    {B : Set N} (hB : IsCompact B) (hBσ : B ⊆ ⋃ a, (σ a).target) :
    ∃ (W : Set N) (Fm : ∀ i, N → Y i),
      IsOpen W ∧ IsCompact (closure W) ∧ B ∪ {q} ⊆ W ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (Fm i) W) ∧
      (∀ᶠ i in atTop, Fm i q = p i) ∧
      (∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
        (∀ᶠ i in atTop, MapsTo (Fm i ∘ σ a) L (d a i).target) ∧
        MapCPConvergenceOn L K (fun i x => (d a i).symm (Fm i (σ a x))) id ∧
        MapCPConvergenceOn L (K - 1)
          (fun i => pullbackMetricCoefficients (g i) (Fm i ∘ σ a)) (b a)) ∧
      (∀ C' : Set N, IsCompact C' → C' ⊆ W →
        TendstoUniformlyOn (fun i x => (F i).extendToWholeSpace (Fm i x)) id atTop C' ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ x ∈ C', ∀ y ∈ C',
          |dist (Fm i x) (Fm i y) - dist x y| < η) ∧
      (∀ O : Set N, IsOpen O → IsCompact (closure O) → closure O ⊆ W →
        ∀ᶠ i in atTop, ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K,
          e.source = O ∧ (e : N → Y i) = Fm i) := by
  obtain ⟨S, hS⟩ := hB.elim_finite_subcover (fun a => (σ a).target) (fun a => (σ a).open_target)
    hBσ
  obtain ⟨C, hCc, hCσ, hBC⟩ :=
    hB.finite_compact_cover S (fun a => (σ a).target) (fun a _ => (σ a).open_target) hS
  obtain ⟨W, Fm, hW, hWc, hCW, hrest⟩ := exists_stage_comparison_maps hK g σ d D hD htrans b hb
    q p a₀ h₀ R ε F hε hchart S C (fun a _ => ⟨hCc a, hCσ a⟩)
  refine ⟨W, Fm, hW, hWc, ?_, hrest⟩
  rw [hBC]
  exact hCW

/-- The verbatim frozen statement I-STAGE (`build-logs/scratch/D-LFR14/Interfaces.lean:197`),
with the unused instance `[ProperSpace N]`. -/
example
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N]
    {K : ℕ} (hK : 1 ≤ K) [IsManifold 𝓘(ℝ, E) K N]
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E (Y i)]
    [∀ i, IsManifold 𝓘(ℝ, E) ∞ (Y i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (Y i))
    {α : Type*} (σ : α → PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E N K)
    (d : α → ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E (Y i) ∞)
    (D : α → Set E)
    (hD : ∀ a, IsOpen (D a) ∧ Convex ℝ (D a) ∧ (σ a).source ⊆ D a ∧ ∀ i, D a ⊆ (d a i).source)
    (htrans : ∀ a c (L : Set E), IsCompact L → L ⊆ ((σ a).trans (σ c).symm).source →
      MapCPConvergenceOn L K (fun i x => (d c i).symm (d a i x)) ((σ a).trans (σ c).symm) ∧
      ∀ᶠ i in atTop, L ⊆ ((d a i).trans (d c i).symm).source)
    (b : α → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ a, ContDiffOn ℝ (K - 1 : ℕ) (b a) (D a) ∧
      ∀ S : Set E, IsCompact S → S ⊆ D a →
        MapCPConvergenceOn S (K - 1) (fun i => pullbackMetricCoefficients (g i) (d a i)) (b a))
    (q : N) (p : ∀ i, Y i) (a₀ : α)
    (h₀ : 0 ∈ (σ a₀).source ∧ σ a₀ 0 = q ∧ ∀ i, d a₀ i 0 = p i)
    (R ε : ℕ → ℝ) (F : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (hε : Tendsto ε atTop (𝓝 0))
    (hchart : ∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source →
      (∀ᶠ i in atTop, MapsTo (d a i) L (closedBall (p i) (R i))) ∧
      TendstoUniformlyOn (fun i u => (F i).extendToWholeSpace (d a i u)) (σ a) atTop L)
    (S : Finset α) (C : α → Set N) (hC : ∀ a ∈ S, IsCompact (C a) ∧ C a ⊆ (σ a).target) :
    ∃ (W : Set N) (Fm : ∀ i, N → Y i),
      IsOpen W ∧ IsCompact (closure W) ∧ ((⋃ a ∈ S, C a) ∪ {q}) ⊆ W ∧
      (∀ i, ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) K (Fm i) W) ∧
      (∀ᶠ i in atTop, Fm i q = p i) ∧
      (∀ a (L : Set E), IsCompact L → L ⊆ (σ a).source ∩ σ a ⁻¹' W →
        (∀ᶠ i in atTop, MapsTo (Fm i ∘ σ a) L (d a i).target) ∧
        MapCPConvergenceOn L K (fun i x => (d a i).symm (Fm i (σ a x))) id ∧
        MapCPConvergenceOn L (K - 1)
          (fun i => pullbackMetricCoefficients (g i) (Fm i ∘ σ a)) (b a)) ∧
      (∀ C' : Set N, IsCompact C' → C' ⊆ W →
        TendstoUniformlyOn (fun i x => (F i).extendToWholeSpace (Fm i x)) id atTop C' ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ i in atTop, ∀ x ∈ C', ∀ y ∈ C',
          |dist (Fm i x) (Fm i y) - dist x y| < η) ∧
      (∀ O : Set N, IsOpen O → IsCompact (closure O) → closure O ⊆ W →
        ∀ᶠ i in atTop, ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (Y i) K,
          e.source = O ∧ (e : N → Y i) = Fm i) := by
  exact exists_stage_comparison_maps hK g σ d D hD htrans b hb q p a₀ h₀ R ε F hε hchart S C hC

end DifferentialGeometry.CheegerGromovCompactness
