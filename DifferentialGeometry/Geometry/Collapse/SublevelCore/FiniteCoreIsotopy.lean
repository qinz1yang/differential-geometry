import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteCollarTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ModelCoreTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteUniformCollarApplications
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpace
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Basic

/-!
# LC51′, isotopy half: the model core is carried onto every radial sublevel (finite limit)

Finite-order twin of LC51's isotopy clause (`exists_collar_constants_core_isotopy`,
SublevelCore/PushedCollarPacket.lean), for LFR14-shaped data whose comparison maps are SMOOTH (the
output of LFR48, `exists_smooth_comparison_maps_of_finite_limit`) and whose limit metric `G` has
finite order. Lane F8-NEW2, task 5.

* `finite_core_enclosure`: the core enclosure `{η ≤ 1/8} ⊆ int j(D)`, `j(D) ⊆ {η < 3}` from the
  pointed distance distortion `< 1/10` and the strict-radius coverage (replacing the two-sided
  smooth metric comparison of `transverse_core_enclosure`).
* `exists_finite_collar_constants_core_isotopy` (**LC51′, full**): LC51′'s collar constants
  (`exists_uniform_collar_finite_limit`, through `PartialDiffeomorph.ofLE`), then for EVERY
  smoothing tolerance `ε < 1` with `ε · 2B < α` and LC30-type radial functions on a tail, one
  tail carries, for every `ρ ∈ [1/5, 2]`, a compactly supported smooth isotopy of `M i` moving
  `j i (D)` onto `{η i ≤ ρ}`. The isotopy is LC48's source side
  (`exists_isotopy_of_collar_direction_margin`) for the pushed field `(j i)_* V`, its direction
  margin converted to `𝒰` by B5.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N]

omit [FiniteDimensional ℝ E] in
/-- **Core enclosure from distance distortion.** -/
theorem finite_core_enclosure {M : Type*} [MetricSpace M] [ChartedSpace H M]
    (j : PartialDiffeomorph I I N M ∞) (q n : N) {R : ℝ} (hnR : dist q n + 3 ≤ R)
    (hsrc : ball q R ⊆ j.source)
    (hdistj : ∀ x ∈ ball q R, ∀ y ∈ ball q R, |dist (j x) (j y) - dist x y| < 1 / 10)
    (hcov : ball (j q) (dist q n + 1) ⊆ (j : N → M) '' ball q R)
    {η : M → ℝ} {e : ℝ} (he : e < 1 / 40) (hclose : ∀ x, |η x - dist (j n) x| < e)
    {D : Set N} (hin : closedBall n (1 / 2) ⊆ interior D) (hout : D ⊆ ball n 2) :
    {x | η x ≤ 1 / 8} ⊆ interior ((j : N → M) '' D) ∧ (j : N → M) '' D ⊆ {x | η x < 3} := by
  have hqn : 0 ≤ dist q n := dist_nonneg
  have hqR : q ∈ ball q R := mem_ball_self (by linarith)
  have hnR' : n ∈ ball q R := by rw [mem_ball, dist_comm]; linarith
  have hDR : D ⊆ ball q R := fun x hx => by
    have h := hout hx
    rw [mem_ball] at h ⊢
    have := dist_triangle x n q
    rw [dist_comm n q] at this
    linarith
  refine ⟨fun y hy => ?_, ?_⟩
  · have hy' : η y ≤ 1 / 8 := hy
    have hyn : dist (j n) y < 3 / 20 := by
      have := (abs_lt.mp (hclose y)).1
      linarith
    have hjqn := (abs_lt.mp (hdistj q hqR n hnR')).2
    have hyq : y ∈ ball (j q) (dist q n + 1) := by
      rw [mem_ball]
      have := dist_triangle y (j n) (j q)
      rw [dist_comm y (j n), dist_comm (j n) (j q)] at this
      linarith
    obtain ⟨x, hxR, rfl⟩ := hcov hyq
    have hnx := (abs_lt.mp (hdistj n hnR' x hxR)).1
    have hxn : x ∈ closedBall n (1 / 2) := by
      rw [mem_closedBall, dist_comm]
      linarith
    have hopen : IsOpen ((j : N → M) '' interior D) :=
      j.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_interior
        ((interior_subset.trans hDR).trans hsrc)
    exact interior_maximal (image_mono interior_subset) hopen ⟨x, hin hxn, rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    have hxn : dist n x < 2 := by rw [dist_comm]; exact hout hx
    have h1 := (abs_lt.mp (hdistj n hnR' x (hDR hx))).2
    have h2 := (abs_lt.mp (hclose (j x))).2
    change η (j x) < 3
    linarith

variable [I.Boundaryless] [IsManifold I ∞ N] [NeZero (Module.finrank ℝ E)]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)]
  [ProperSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]

/-- **LC51′ (full) for a finite-order limit with smooth comparison maps.** LFR14-shaped data with
`2 ≤ r`, SMOOTH maps `j i` (LFR48), a compact model core `D` with `B̄(n, 1/2) ⊆ int D`,
`D ⊆ B(n, 2)`, its own field `V` smooth on an open `O ⊇ ∂D`, strictly outward on `∂D` and pairing
strictly negatively with every limit minimizing direction to `n` along `∂D`. First `α, B > 0` and
an open collar `U ⊇ ∂D` are fixed, with the pushed-field bounds on one tail; then for EVERY
`ε < 1` with `ε · 2B < α` and radial functions `η i` with the LC30 clauses on a tail, one tail
carries, for every `ρ ∈ [1/5, 2]`, a compactly supported smooth isotopy moving `j i (D)` onto
`{η i ≤ ρ}`. -/
theorem exists_finite_collar_constants_core_isotopy [∀ i, SigmaCompactSpace (M i)]
    [∀ i, CompleteSpace (M i)] {r : ℕ∞} (hr : 2 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I (M i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (n : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall n (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball n 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace I x)
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I N)) O)
    (hdef : ∀ x ∈ frontier D, ∃ L : Set N, IsOpen L ∧ x ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {y | f y ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f x (V x))
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v < 0) :
    ∃ α B : ℝ, 0 < α ∧ 0 < B ∧ ∃ U : Set N, IsOpen U ∧ frontier D ⊆ U ∧
      IsCompact (closure U) ∧ closure U ⊆ (ball n 3 \ {n}) ∩ O ∧
      (∀ᶠ i in atTop, ∀ x ∈ closure U,
        (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
            (mfderiv I I (j i : N → M i) x (V x)) ≤ (2 * B) ^ 2 ∧
        ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) {j i n} (j i x),
          (g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x)) w ≤ -α) ∧
      ∀ ε : ℝ≥0, (ε : ℝ) < 1 → (ε : ℝ) * (2 * B) < α →
      ∀ (η : ∀ i, M i → ℝ) (e : ℕ → ℝ),
      (∀ᶠ i in atTop, e i < 1 / 40 ∧ (∀ x, |η i x - dist (j i n) x| < e i) ∧
        LipschitzWith ε (fun x => η i x - dist (j i n) x) ∧
        ∃ Wi : Set (M i), IsOpen Wi ∧
          (∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 → x ∈ Wi) ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
          ∀ x, 1 / 10 ≤ dist (j i n) x → dist (j i n) x ≤ 10 →
            (1 - (ε : ℝ)) ^ 2 ≤ (g i).inner x (gradientFun (I := I) (g i) (η i) x)
              (gradientFun (I := I) (g i) (η i) x)) →
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ Hs : ℝ → Diffeomorph I I (M i) (M i) ∞,
        Hs 0 = Diffeomorph.refl I (M i) ∞ ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => Hs q.1 q.2) ∧
        ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M i => (Hs q.1).symm q.2) ∧
        (∃ S : Set (M i), IsCompact S ∧ S ⊆ η i ⁻¹' Ioo (1 / 8) 3 ∧
          ∀ t x, x ∉ S → Hs t x = x ∧ (Hs t).symm x = x) ∧
        Hs 1 '' ((j i : N → M i) '' D) = {x | η i x ≤ ρ} := by
  let jK : ∀ i, PartialDiffeomorph I I N (M i) (2 : ℕ) := fun i =>
    DifferentialGeometry.PartialDiffeomorph.ofLE (j i) (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨α, B, hα, hB, U, hUo, hDU, hcpt, hsub, hcol⟩ :=
    exists_uniform_collar_finite_limit (M := M) hr G hGnorm g hmetric (K := 2) le_rfl q jK hexh
      hconv hdist hcover n hDc hin hout hO hDO V hV.continuousOn hneg
  refine ⟨α, B, hα, hB, U, hUo, hDU, hcpt, hsub, hcol, ?_⟩
  intro ε hε1 hεB η e hη
  set R : ℝ := dist q n + 3 with hRdef
  have hqn : 0 ≤ dist q n := dist_nonneg
  filter_upwards [hcol, hη, hexh (closedBall q R) (isCompact_closedBall q R),
    hdist R (1 / 10) (by norm_num), hcover (dist q n + 1) R (by positivity) (by linarith)]
    with i hci hηi hsrcR hdistR hcovR ρ hρ
  obtain ⟨he, hclose, hlip, Wi, hWi, hCWi, hηWi, hgrad⟩ := hηi
  let : RiemannianBundle (fun x : M i => TangentSpace I x) := ⟨(g i).toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x) :=
    isContinuousRiemannianBundle_of_smoothRiemannianMetric (g i)
  have : IsRiemannianManifold I (M i) := by
    constructor
    intro a b
    change edist a b = riemannianEDistOf (g i) a b
    rw [edist_dist, hmetric]
  have hEnorm : IsMetricNorm (I := I) (g i) := isMetricNorm_of_riemannianBundle (g i)
  have : ProperSpace (M i) := Manifold.properSpace_of_isRiemannianManifold I
  have hsrcball : ball q R ⊆ (j i).source := ball_subset_closedBall.trans hsrcR
  obtain ⟨hAD, hDb⟩ := finite_core_enclosure (j i) q n le_rfl hsrcball hdistR hcovR he hclose
    hin hout
  have hDR : D ⊆ ball q R := fun x hx => by
    have h := hout hx
    rw [mem_ball] at h ⊢
    have := dist_triangle x n q
    rw [dist_comm n q] at this
    linarith
  have hDsrc : D ⊆ (j i).source := hDR.trans hsrcball
  have hnc : n ∈ (j i).source := hsrcball (by rw [mem_ball, dist_comm]; linarith)
  have hηc : Continuous (η i) :=
    (hlip.continuous.add (continuous_const.dist continuous_id)).congr
      (fun x => sub_add_cancel (η i x) (dist (j i n) x))
  have hK : IsCompact (η i ⁻¹' Icc (1 / 8 : ℝ) 3) :=
    isCompact_preimage_of_abs_sub_dist_lt hηc hclose isCompact_Icc
  have hann := radialBand_subset_annulus hclose he
  have hKC : ∀ x ∈ η i ⁻¹' Icc (1 / 8 : ℝ) 3,
      1 / 10 ≤ dist (j i n) x ∧ dist (j i n) x ≤ 10 := fun x hx =>
    ⟨(hann hx).1.le, (hann hx).2.le⟩
  have hKW : η i ⁻¹' Icc (1 / 8 : ℝ) 3 ⊆ Wi := fun x hx => hCWi x (hKC x hx).1 (hKC x hx).2
  have hpos : ∀ x ∈ η i ⁻¹' Icc (1 / 8 : ℝ) 3,
      0 < (g i).inner x (gradientFun (I := I) (g i) (η i) x)
        (gradientFun (I := I) (g i) (η i) x) := by
    intro x hx
    have hm : 0 < 1 - (ε : ℝ) := by linarith
    exact lt_of_lt_of_le (sq_pos_of_pos hm) (hgrad x (hKC x hx).1 (hKC x hx).2)
  have hjclosed : IsClosed ((j i : N → M i) '' D) :=
    (hDc.image_of_continuousOn ((j i).contMDiffOn.continuousOn.mono hDsrc)).isClosed
  have hUsub : U ⊆ closure U := subset_closure
  have hfr : frontier ((j i : N → M i) '' D) ⊆ (j i : N → M i) '' (U ∩ (j i).source) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := frontier_image_subset_image_frontier (j i) hDc hDsrc hy
    exact ⟨x, ⟨hDU hx, hDsrc (hDc.isClosed.frontier_subset hx)⟩, rfl⟩
  have hnU : n ∉ U := fun h => (hsub (hUsub h)).1.2 rfl
  have hnot : j i n ∉ (j i : N → M i) '' (U ∩ (j i).source) := by
    rintro ⟨x, hx, heq⟩
    have hxn : x = n := (j i).injOn hx.2 hnc heq
    exact hnU (hxn ▸ hx.1)
  have hdeff : ∀ y ∈ frontier ((j i : N → M i) '' D), ∃ L : Set (M i),
      IsOpen L ∧ y ∈ L ∧ ∃ f : M i → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f L ∧
        ((j i : N → M i) '' D) ∩ L = {x | f x ≤ 0} ∩ L ∧
        0 < mvfderiv (I := I) f y (modelPushedField (j i) V y) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := frontier_image_subset_image_frontier (j i) hDc hDsrc hy
    obtain ⟨L, hL, hxL, f, hf, hLf, hfv⟩ := hdef x hx
    obtain ⟨L', hL', hjL', hf', hset, hpos'⟩ := model_defining_function_pushforward (j i) V
      hDsrc (hDsrc (hDc.isClosed.frontier_subset hx)) hL hxL hf hLf hfv
    exact ⟨L', hL', hjL', fun y => f ((j i).symm y), hf', hset, hpos'⟩
  have hUO : U ⊆ O := fun x hx => (hsub (hUsub hx)).2
  have hZB : ∀ y ∈ (j i : N → M i) '' (U ∩ (j i).source),
      √((g i).inner y (modelPushedField (j i) V y) (modelPushedField (j i) V y)) ≤ 2 * B := by
    rintro y ⟨x, ⟨hxU, hxs⟩, rfl⟩
    rw [modelPushedField_apply (j i) V hxs]
    have h := (hci x (hUsub hxU)).1
    calc √((g i).inner (j i x) (mfderiv I I (j i : N → M i) x (V x))
          (mfderiv I I (j i : N → M i) x (V x))) ≤ √((2 * B) ^ 2) := Real.sqrt_le_sqrt h
      _ = 2 * B := Real.sqrt_sq (by linarith)
  have hdirU : ∀ y ∈ (j i : N → M i) '' (U ∩ (j i).source),
      ∀ u ∈ inwardMinimizingDirections (I := I) (g i) hEnorm (j i n) y,
        (g i).inner y (modelPushedField (j i) V y) u ≤ -α := by
    rintro y ⟨x, ⟨hxU, hxs⟩, rfl⟩ u hu
    rw [modelPushedField_apply (j i) V hxs]
    exact inner_le_of_mem_inwardMinimizingDirections_of_finite (g i) hEnorm
      (hci x (hUsub hxU)).2 hu
  exact exists_isotopy_of_collar_direction_margin (g i) hEnorm hηc hWi hηWi
    (⟨by linarith [hρ.1], by linarith [hρ.2]⟩ : ρ ∈ Ioo (1 / 8 : ℝ) 3)
    hK hKW hpos hlip hjclosed hAD hDb
    ((j i).toOpenPartialHomeomorph.isOpen_image_of_subset_source (hUo.inter (j i).open_source)
      inter_subset_right) hfr hnot (modelPushedField (j i) V)
    (modelPushedField_contMDiffOn (j i) V hUo (hV.mono hUO)) hZB hdirU hεB hdeff

end DifferentialGeometry.Geometry.Collapse
