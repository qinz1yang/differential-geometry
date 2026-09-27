import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation
import DifferentialGeometry.Bundle.PartialMfderiv.IteratedDeriv

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace Function.Periodic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem contDiff_of_contDiffAt_Ico {f : ℝ → F} {T : ℝ} {n : ℕ∞ω}
    (hper : Function.Periodic f T) (hT : 0 < T)
    (hlocal : ∀ x ∈ Ico (0 : ℝ) T, ContDiffAt ℝ n f x) :
    ContDiff ℝ n f := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hmem : x - (⌊x / T⌋ : ℝ) * T ∈ Ico (0 : ℝ) T :=
    ⟨Int.sub_floor_div_mul_nonneg x hT, Int.sub_floor_div_mul_lt x hT⟩
  have hc : ContDiffAt ℝ n (fun y : ℝ => f (y - (⌊x / T⌋ : ℝ) * T)) x :=
    (hlocal _ hmem).comp x ((contDiff_id.sub contDiff_const).contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => (hper.sub_int_mul_eq ⌊x / T⌋).symm

private lemma interval_grid_cover {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    ∃ i : ℤ, 0 ≤ i ∧ i < (N : ℤ) ∧ (x = (i : ℝ) / N ∨ x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
  let y : ℝ := (N : ℝ) * x
  let i : ℤ := ⌊y⌋
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact mul_nonneg (by positivity) hx.1
  have hiy_le : (i : ℝ) ≤ y := by
    dsimp [i]
    exact_mod_cast (Int.floor_le y)
  have hy_lt : y < (i : ℝ) + 1 := by
    dsimp [i]
    exact Int.lt_floor_add_one y
  have hi0 : 0 ≤ i := by
    dsimp [i]
    exact Int.floor_nonneg.mpr hy0
  have hy_ltN : y < (N : ℝ) := by
    dsimp [y]
    nlinarith [mul_lt_mul_of_pos_left hx.2 (by positivity : (0 : ℝ) < N)]
  have hix_lt : i < (N : ℤ) := by
    rw [Int.floor_lt]
    exact_mod_cast hy_ltN
  refine ⟨i, hi0, hix_lt, ?_⟩
  have hNreal : (0 : ℝ) < N := by positivity
  have hlow : (i : ℝ) / N ≤ x := by
    apply (div_le_iff₀ hNreal).2
    nlinarith [hiy_le]
  have hupp : x < ((i : ℝ) + 1) / N := by
    apply (lt_div_iff₀ hNreal).2
    nlinarith [hy_lt]
  rcases eq_or_lt_of_le hlow with hEq | hLt
  · exact Or.inl hEq.symm
  · exact Or.inr ⟨hLt, hupp⟩

private theorem contDiff_of_contDiffAt_grid {f : ℝ → F} {n : ℕ∞ω} {N : ℕ}
    (hper : Function.Periodic f 1) (hN : 0 < N)
    (hvertex : ∀ i : ℤ, 0 ≤ i → i < N → ContDiffAt ℝ n f ((i : ℝ) / N))
    (hedge : ∀ i : ℤ, 0 ≤ i → i < N → ∀ x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N),
      ContDiffAt ℝ n f x) : ContDiff ℝ n f := by
  refine hper.contDiff_of_contDiffAt_Ico zero_lt_one ?_
  intro x hx
  obtain ⟨i, hi, hiN, hxi | hxi⟩ := interval_grid_cover hN hx
  · rw [hxi]
    exact hvertex i hi hiN
  · exact hedge i hi hiN x hxi

end Function.Periodic

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem contDiffAt_map_flatPolygon_at_vertex (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ}
    (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) :
    ContDiffAt ℝ ∞ (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle)))
      ((i : ℝ) / N) :=
  (contDiffAt_map_flatPolygon_and_iteratedDeriv_eq_zero g P e hN γ hseg hi hiN).1

omit [CompleteSpace E] hT2 hCompact hConnected hBoundary in
theorem contMDiffAt_flatPolygon_interior (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N)
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {x : ℝ} (hx : x ∈ Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => flatPolygon g P N γ (t : Surgery.Topology.Circle)) x := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpiece : ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
        (P.beta ((N : ℝ) * t - i)))
      (Ioo ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
    apply contMDiffOn_shortSegment_beta g P hseg (c := (N : ℝ)) (e := -(i : ℝ))
    intro t ht
    have h1 := (div_lt_iff₀ hNR).mp ht.1
    have h2 := (lt_div_iff₀ hNR).mp ht.2
    constructor <;> linarith
  apply (hpiece.contMDiffAt (isOpen_Ioo.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  exact flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN ⟨ht.1.le, ht.2⟩

omit [CompleteSpace E] hT2 hCompact hConnected in
private theorem contMDiffAt_of_contDiffAt_comp_embedding {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {f : ℝ → Q} {x : ℝ}
    (hf : ContDiffAt ℝ ∞ (e.map ∘ f) x) : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ f x := by
  obtain ⟨r, U, hU, hxU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_local_retraction_of_embedding
      e.smooth e.isClosedEmbedding.isEmbedding (f x) (e.injective_mfderiv (f x))
  have hcomp : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (r ∘ e.map ∘ f) x :=
    (hr.contMDiffAt (hU.mem_nhds hxU)).comp x hf.contMDiffAt
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hf.continuousAt (hU.mem_nhds hxU)] with y hy
  exact (hleft (f y) hy).symm

omit [CompleteSpace E] hT2 hCompact hConnected in
theorem contMDiff_flatPolygon (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {d : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ}
    (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞
      (fun x : ℝ => flatPolygon g P N γ (x : Surgery.Topology.Circle)) := by
  have hper : Function.Periodic
      (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle))) 1 := by
    intro x
    exact congrArg e.map (flatPolygon_add_one g P N γ x)
  have hglobal : ContDiff ℝ ∞
      (fun x : ℝ => e.map (flatPolygon g P N γ (x : Surgery.Topology.Circle))) := by
    apply Function.Periodic.contDiff_of_contDiffAt_grid hper hN
    · intro i hi hiN
      exact contDiffAt_map_flatPolygon_at_vertex g P e hN γ hseg hi hiN
    · intro i hi hiN x hx
      exact (e.smooth.contMDiffAt.comp x
        (contMDiffAt_flatPolygon_interior g P hN γ hi hiN (hseg i hi hiN) hx)).contDiffAt
  intro x
  exact contMDiffAt_of_contDiffAt_comp_embedding e hglobal.contDiffAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open DifferentialGeometry.Analysis

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [TopologicalSpace Q] in
private theorem polygonVertex_period (γ : Surgery.Topology.Circle → Q) {N : ℕ}
    (hN : 0 < N) : polygonVertex γ N (N : ℤ) = polygonVertex γ N 0 := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [polygonVertex, Int.cast_natCast, div_self hNne, Int.cast_zero, zero_div]
  exact congrArg γ (AddCircle.coe_period (p := (1 : ℝ)))

theorem flatPolygon_apply_of_mem_Icc (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) {N : ℕ} (hN : 0 < N) (γ : Surgery.Topology.Circle → Q)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) {x : ℝ}
    (hx : x ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    flatPolygon g P N γ (x : Surgery.Topology.Circle) =
      shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
        (P.beta ((N : ℝ) * x - i)) := by
  rcases eq_or_lt_of_le hx.2 with hx' | hx'
  · subst x
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [mul_div_cancel₀ _ hNR.ne', add_sub_cancel_left, P.beta_one, (hseg i hi hiN).2.2.2.1]
    by_cases hi' : i + 1 < N
    · have hi0 : 0 ≤ i + 1 := by omega
      have hinterval : (((i : ℝ) + 1) / N) ∈
          Ico (((i + 1 : ℤ) : ℝ) / N) ((((i + 1 : ℤ) : ℝ) + 1) / N) := by
        constructor
        · norm_cast
        · push_cast
          exact (div_lt_div_iff_of_pos_right hNR).mpr (by linarith)
      rw [flatPolygon_apply_of_mem_Ico g P N γ hN hi0 hi' hinterval]
      have hcast : (((i + 1 : ℤ) : ℝ)) = (i : ℝ) + 1 := by push_cast; rfl
      rw [mul_div_cancel₀ _ hNR.ne', ← hcast, sub_self, P.beta_zero]
      exact (hseg (i + 1) hi0 hi').2.2.1
    · have hiEq : i + 1 = N := by omega
      have hcast : (i : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hiEq
      rw [hcast, div_self hNR.ne']
      have hper := flatPolygon_add_one g P N γ 0
      simp only [zero_add] at hper
      rw [hper]
      have hx0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := by norm_num
      rw [flatPolygon_coe_apply g P N γ hx0]
      simp only [mul_zero, Int.floor_zero, zero_add, Int.cast_zero, sub_zero, P.beta_zero]
      have hzero : shortSegment g (polygonVertex γ N 0) (polygonVertex γ N 1) 0 =
          polygonVertex γ N 0 := by
        simpa only [zero_add] using (hseg 0 (by omega) (by exact_mod_cast hN)).2.2.1
      rw [hzero, hiEq]
      exact (polygonVertex_period γ hN).symm
  · exact flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN ⟨hx.1, hx'⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end

section

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem continuousOn_shortSegment_flat_piece_jets
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ} (hN : 0 < N)
    {K : Type*} [TopologicalSpace K] {v w : K → Q}
    (hv : Continuous v) (hw : Continuous w)
    {U : Set (Q × Q)} (hU : IsOpen U)
    (hshort : ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
      (U ×ˢ Ioo (-1 : ℝ) 2))
    (hvw : ∀ k, (v k, w k) ∈ U) (i : ℤ) (j : ℕ) :
    ContinuousOn (fun q : K × ℝ =>
      iteratedDeriv j (fun t => e.map
        (shortSegment g (v q.1) (w q.1) (P.beta ((N : ℝ) * t - i)))) q.2)
      (univ ×ˢ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
  apply DifferentialGeometry.Analysis.continuousOn_iteratedDeriv_parameter_comp
    (I := I.prod I) hU isOpen_Ioo (e.smooth.comp_contMDiffOn hshort)
    (hv.prodMk hw) hvw
    (P.contDiff_beta.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
  intro t ht
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := (div_le_iff₀ hNR).mp ht.1
  have hr := (le_div_iff₀ hNR).mp ht.2
  have hbeta := P.beta_mem_Icc (show (N : ℝ) * t - i ∈ Icc (0 : ℝ) 1 by
    constructor <;> linarith)
  change P.beta ((N : ℝ) * t - i) ∈ Ioo (-1 : ℝ) 2
  constructor <;> linarith [hbeta.1, hbeta.2]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem contMDiffAt_shortSegment_flat_piece
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {N : ℕ} (hN : 0 < N)
    {p q : Q} (hseg : IsShortSegment g p q (shortSegment g p q))
    (i : ℤ) {x : ℝ} (hx : x ∈ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) :
    ContMDiffAt 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => shortSegment g p q (P.beta ((N : ℝ) * t - i))) x := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := (div_le_iff₀ hNR).mp hx.1
  have hr := (le_div_iff₀ hNR).mp hx.2
  have hbeta := P.beta_mem_Icc (show (N : ℝ) * x - i ∈ Icc (0 : ℝ) 1 by
    constructor <;> linarith)
  have hmem : P.beta ((N : ℝ) * x - i) ∈ Ioo (-1 : ℝ) 2 := by
    constructor <;> linarith [hbeta.1, hbeta.2]
  exact (hseg.1.contMDiffAt (isOpen_Ioo.mem_nhds hmem)).comp x
    (P.contDiff_beta.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).contMDiff.contMDiffAt

private theorem continuousOn_flatPolygon_jets_piece [I.Boundaryless]
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ} (hN : 0 < N)
    {K : Type*} [TopologicalSpace K] (v : K → Surgery.Topology.Circle → Q)
    (hv : ∀ i : ℤ, Continuous (fun k => polygonVertex (v k) N i))
    (hseg : ∀ k (i : ℤ), 0 ≤ i → i < N →
      IsShortSegment g (polygonVertex (v k) N i) (polygonVertex (v k) N (i + 1))
        (shortSegment g (polygonVertex (v k) N i) (polygonVertex (v k) N (i + 1))))
    {U : Set (Q × Q)} (hU : IsOpen U)
    (hshort : ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
      (U ×ˢ Ioo (-1 : ℝ) 2))
    (hvU : ∀ k (i : ℤ), 0 ≤ i → i < N →
      (polygonVertex (v k) N i, polygonVertex (v k) N (i + 1)) ∈ U)
    {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) (j : ℕ) :
    ContinuousOn (fun q : K × ℝ => iteratedDeriv j
      (fun t : ℝ => e.map (flatPolygon g P N (v q.1) (t : Surgery.Topology.Circle))) q.2)
      (univ ×ˢ Icc ((i : ℝ) / N) (((i : ℝ) + 1) / N)) := by
  have hc := continuousOn_shortSegment_flat_piece_jets g P e hN (hv i) (hv (i + 1))
    hU hshort (fun k => hvU k i hi hiN) i j
  apply hc.congr
  intro q hq
  have hab : (i : ℝ) / N < ((i : ℝ) + 1) / N := by
    exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hN)).mpr (by linarith)
  have hflat : ContDiffAt ℝ j
      (fun t : ℝ => e.map (flatPolygon g P N (v q.1) (t : Surgery.Topology.Circle))) q.2 :=
    ((e.smooth.comp (contMDiff_flatPolygon g P e hN (v q.1) (hseg q.1))).contDiff.of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top)).contDiffAt
  have hpiece : ContDiffAt ℝ j
      (fun t => e.map (shortSegment g (polygonVertex (v q.1) N i)
        (polygonVertex (v q.1) N (i + 1)) (P.beta ((N : ℝ) * t - i)))) q.2 :=
    ((e.smooth.contMDiffAt.comp q.2
      (contMDiffAt_shortSegment_flat_piece g P hN (hseg q.1 i hi hiN) i hq.2)).contDiffAt.of_le
      (show (j : ℕ∞ω) ≤ ∞ by exact_mod_cast le_top))
  dsimp only
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hflat hq.2,
    ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) hpiece hq.2]
  apply iteratedDerivWithin_congr _ hq.2
  intro t ht
  exact congrArg e.map (flatPolygon_apply_of_mem_Icc g P hN (v q.1) (hseg q.1) hi hiN ht)

private theorem continuousOn_unit_strip_of_subdivision
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    {g : K × ℝ → X} {N : ℕ} (hN : 0 < N)
    (hpiece : ∀ i : Fin N, ContinuousOn g
      (univ ×ˢ Icc ((i.val : ℝ) / N) (((i.val : ℝ) + 1) / N))) :
    ContinuousOn g (univ ×ˢ Icc (0 : ℝ) 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hchain : ∀ k : ℕ, k ≤ N → ContinuousOn g
      (univ ×ˢ Icc (0 : ℝ) ((k : ℝ) / N)) := by
    intro k
    induction k with
    | zero =>
      intro _
      apply (hpiece ⟨0, hN⟩).mono
      intro p hp
      simp only [Nat.cast_zero, zero_div, zero_add, mem_prod, mem_univ, true_and,
        mem_Icc] at hp ⊢
      refine ⟨hp.1, hp.2.trans ?_⟩
      positivity
    | succ k ih =>
      intro hk
      have hkN : k < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
      have hc := (ih (Nat.le_of_succ_le hk)).union_of_isClosed (hpiece ⟨k, hkN⟩)
        (isClosed_univ.prod isClosed_Icc) (isClosed_univ.prod isClosed_Icc)
      have h0 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
      have hstep : (k : ℝ) / N ≤ ((k : ℝ) + 1) / N :=
        (div_le_div_iff_of_pos_right hNpos).mpr (le_add_of_nonneg_right zero_le_one)
      rw [← prod_union, Icc_union_Icc_eq_Icc h0 hstep] at hc
      simpa only [Nat.cast_add, Nat.cast_one] using hc
  simpa only [div_self hNpos.ne'] using hchain N le_rfl


private theorem continuousOn_flatPolygon_jets_of_grid
    {K F : Type*} [TopologicalSpace K] [TopologicalSpace F]
    {N : ℕ} (hN : 0 < N)
    {G : K × ℝ → F}
    (hpiece : ∀ i : Fin N, ContinuousOn G
      (univ ×ˢ Icc ((i.val : ℝ) / N) (((i.val : ℝ) + 1) / N)))
    (hper : ∀ k t, G (k, t + 1) = G (k, t)) :
    Continuous G := by
  have hstrip : ContinuousOn G (univ ×ˢ Icc (0 : ℝ) 1) := by
    apply continuousOn_unit_strip_of_subdivision hN hpiece
  exact DifferentialGeometry.Topology.continuous_of_continuousOn_Icc_of_add_one hstrip hper

theorem continuous_flatPolygon_jets_of_shortSegment [I.Boundaryless]
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {N : ℕ} (hN : 0 < N)
    {K : Type*} [TopologicalSpace K] (v : K → Surgery.Topology.Circle → Q)
    (hv : ∀ i : ℤ, Continuous (fun k => polygonVertex (v k) N i))
    (hseg : ∀ k (i : ℤ), 0 ≤ i → i < N →
      IsShortSegment g (polygonVertex (v k) N i) (polygonVertex (v k) N (i + 1))
        (shortSegment g (polygonVertex (v k) N i) (polygonVertex (v k) N (i + 1))))
    {U : Set (Q × Q)} (hU : IsOpen U)
    (hshort : ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
      (U ×ˢ Ioo (-1 : ℝ) 2))
    (hvU : ∀ k (i : ℤ), 0 ≤ i → i < N →
      (polygonVertex (v k) N i, polygonVertex (v k) N (i + 1)) ∈ U) (j : ℕ) :
    Continuous (fun q : K × ℝ => iteratedDeriv j
      (fun t : ℝ => e.map (flatPolygon g P N (v q.1) (t : Surgery.Topology.Circle))) q.2) := by
  apply continuousOn_flatPolygon_jets_of_grid hN
  · intro i
    simpa only [Int.cast_natCast] using
      continuousOn_flatPolygon_jets_piece g P e hN v hv hseg hU hshort hvU
        (i := (i.val : ℤ)) (by omega) (by exact_mod_cast i.isLt) j
  · intro k t
    have hp : Function.Periodic
        (fun t : ℝ => e.map (flatPolygon g P N (v k) (t : Surgery.Topology.Circle))) 1 := by
      intro t
      exact congrArg e.map (flatPolygon_add_one g P N (v k) t)
    exact DifferentialGeometry.Topology.periodic_iteratedDeriv hp j t

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end

section

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families
open Surgery.Topology Width CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
 {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [TopologicalSpace Q] in
private theorem polygonVertex_emod (γ : Surgery.Topology.Circle → Q) {N : ℕ} (hN : 0 < N)
    (i : ℤ) : polygonVertex γ N i = polygonVertex γ N (i % N) := by
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hdecomp : (i : ℝ) / N = ((i % N : ℤ) : ℝ) / N + ((i / N : ℤ) : ℝ) := by
    have hi := Int.emod_add_mul_ediv i N
    have hiR := congrArg (fun z : ℤ => (z : ℝ)) hi
    push_cast at hiR
    rw [div_eq_iff hNne]
    field_simp
    nlinarith
  simp only [polygonVertex, hdecomp]
  have hcoe : ((((i / N : ℤ) : ℝ)) : Surgery.Topology.Circle) = 0 := by
    have hz : (((i / N : ℤ) : ℝ)) = (i / N) • (1 : ℝ) := by simp
    rw [hz, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  rw [AddCircle.coe_add, hcoe, add_zero]

theorem continuous_polygonVertex_of_fin {N : ℕ} (hN : 0 < N)
    {K : Type*} [TopologicalSpace K] (v : K → Surgery.Topology.Circle → Q)
    (hv : ∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val))
    (i : ℤ) : Continuous (fun k => polygonVertex (v k) N i) := by
  have hr0 : 0 ≤ i % N := Int.emod_nonneg i (by omega)
  have hrN : i % N < N := Int.emod_lt_of_pos i (by exact_mod_cast hN)
  let r : Fin N := ⟨(i % N).toNat, by omega⟩
  have heq (k : K) : polygonVertex (v k) N i = polygonVertex (v k) N r.val := by
    rw [polygonVertex_emod (v k) hN i]
    congr 1
    dsimp [r]
    exact (Int.toNat_of_nonneg hr0).symm
  exact (hv r).congr (fun k => (heq k).symm)

omit [FiniteDimensional ℝ E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isOpen_shortSegment_pairs [RegularSpace Q]
    (g : SmoothRiemannianMetric I Q) (radius : ℝ) :
    IsOpen {pq : Q × Q | riemannianEDistOf g pq.1 pq.2 < ENNReal.ofReal radius} := by
  let : RiemannianBundle (TangentSpace I : Q → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : Q → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : PseudoEMetricSpace Q := .ofRiemannianMetric I Q
  change IsOpen {pq : Q × Q | edist pq.1 pq.2 < ENNReal.ofReal radius}
  exact isOpen_lt continuous_edist continuous_const

theorem continuous_flatPolygon_jets_of_radius [I.Boundaryless] [RegularSpace Q]
    (g : SmoothRiemannianMetric I Q) (P : FlatteningProfile) {d : ℕ}
    (e : SmoothLoopEmbedding (I := I) (Q := Q) d) {radius : ℝ}
    (hsegment : ∀ p q, riemannianEDistOf g p q < ENNReal.ofReal radius →
      IsShortSegment g p q (shortSegment g p q))
    (hshort : ContMDiffOn ((I.prod I).prod 𝓘(ℝ, ℝ)) I ∞
      (fun z : (Q × Q) × ℝ => shortSegment g z.1.1 z.1.2 z.2)
      ({pq : Q × Q | riemannianEDistOf g pq.1 pq.2 < ENNReal.ofReal radius} ×ˢ
        Ioo (-1 : ℝ) 2))
    {N : ℕ} (hN : 0 < N)
    {K : Type*} [TopologicalSpace K] (v : K → Surgery.Topology.Circle → Q)
    (hv : ∀ i : Fin N, Continuous (fun k => polygonVertex (v k) N i.val))
    (hedges : ∀ k (i : Fin N), riemannianEDistOf g (polygonVertex (v k) N i.val)
      (polygonVertex (v k) N (i.val + 1)) < ENNReal.ofReal radius) (j : ℕ) :
    Continuous (fun q : K × ℝ => iteratedDeriv j
      (fun t : ℝ => e.map (flatPolygon g P N (v q.1) (t : Surgery.Topology.Circle))) q.2) := by
  have hcanonical : ∀ k (i : ℤ), 0 ≤ i → i < N →
      riemannianEDistOf g (polygonVertex (v k) N i)
        (polygonVertex (v k) N (i + 1)) < ENNReal.ofReal radius := by
    intro k i hi hiN
    let ii : Fin N := ⟨i.toNat, by omega⟩
    have hiCast : (ii.val : ℤ) = i := Int.toNat_of_nonneg hi
    simpa only [hiCast] using hedges k ii
  exact continuous_flatPolygon_jets_of_shortSegment g P e hN v
    (continuous_polygonVertex_of_fin hN v hv)
    (fun k i hi hiN => hsegment _ _ (hcanonical k i hi hiN))
    (isOpen_shortSegment_pairs g radius) hshort hcanonical j

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

end
