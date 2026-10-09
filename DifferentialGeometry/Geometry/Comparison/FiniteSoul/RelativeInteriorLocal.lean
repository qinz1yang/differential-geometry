import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrderImage
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.FiniteNormalChart
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.SliceOfOrder

/-!
# S3-SLICE, local part: the relative interior of a totally convex set is a relatively open slice

Lane CMS3-SLICE (group G2), design `design-finite-soul-three-20261004.md` §3 S3-SLICE and risk R1. For a
complete metric `g` of class `C^{r+1}` (`2 ≤ r`, `hnorm`) and `C` totally convex
(`IsTotallyConvexFinite`: every geodesic-flow arc with ends in `C` stays in `C`), with slices of order
`r`:

* `exists_slice_succ_finite` (cone step): if a `d`-slice `N ⊆ C` meets `closure (C \ N)` at `p`, then
  `C` contains a `(d + 1)`-slice. Nearest point `z ∈ N` to a point `q ∈ C \ N` near `p`; in the normal
  chart `e_q` the parametrization `f` of `e_q⁻¹ N` at `e_q⁻¹ z` makes `|f|²_{g_q} = d(q, e_q f)²` minimal
  at `0`, so `f 0 ∉ range (D f 0)`; the cone `(x, t) ↦ t f x` is a `(d + 1)`-slice by the order-`r` IFT,
  and `e_q` of it lies in `C` by total convexity. The IFT is applied inside the slice, never at a
  relative boundary point (risk R1).
* `maxSlice_eq_near_finite` (local uniqueness of top slices): a top-dimensional slice `N ⊆ C` agrees
  with `C` near each of its points.
* `isEmbeddedSliceOfOrder_maxSliceLocusOfOrder`, `exists_isOpen_inter_eq_maxSliceLocusOfOrder`: the
  relative interior is a slice of the relative dimension, relatively open in `C`.
* `exists_expMap_smul_mem_maxSliceLocusOfOrder` (relative radial cone, uniform on compacts): if
  `exp_y v` is in the relative interior (`y ∈ C`, `v` short) then so is `exp_y (a v)`, `a ∈ (0, 1]`.
* `isTotallyGeodesicFinite_maxSliceLocusOfOrder`: the relative interior is totally geodesic. In the
  normal chart at `x`, `V = e_x⁻¹ (relint ∩ ball)` is star-shaped, every `u ∈ V` is the velocity of a curve
  in the relative interior (`d exp_x (0) = id`), so `V ⊆ T_x relint`; `V` is a `d`-slice of `E` inside
  this `d`-dimensional subspace, hence a neighbourhood of `0` in it.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

open DifferentialGeometry.Geometry (radial_not_mem_range_of_quad_min)

/-- Near a point of a locally closed set of a proper space, nearest points exist. -/
theorem exists_nearest_of_isLocallyClosed {X : Type*} [MetricSpace X] [ProperSpace X]
    {S : Set X} (hS : IsLocallyClosed S) {p : X} (hp : p ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ ball p r, ∃ z ∈ S, ∀ y ∈ S, dist q z ≤ dist q y := by
  obtain ⟨O, Z, hO, hZ, rfl⟩ := hS
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO p hp.1
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro q hq
  obtain ⟨z, hz, hdist⟩ := hZ.exists_infDist_eq_dist ⟨p, hp.2⟩ q
  have hqz : dist q z ≤ dist q p := by rw [← hdist]; exact infDist_le_dist_of_mem hp.2
  have hzO : z ∈ O := by
    apply hrO
    have htri := dist_triangle z q p
    rw [dist_comm z q] at htri
    change dist z p < r
    have hqp : dist q p < r / 2 := hq
    linarith
  refine ⟨z, ⟨hzO, hz⟩, fun y hy => ?_⟩
  rw [← hdist]
  exact infDist_le_dist_of_mem hy.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

omit [CompleteSpace M] in
private theorem coe_ne_zero_of_two_le (hr : 2 ≤ r) : (r : ℕ∞ω) ≠ 0 := by
  have h : (1 : ℕ∞) ≤ r := one_le_two.trans hr
  have h' : (1 : ℕ∞ω) ≤ r := by exact_mod_cast h
  exact (zero_lt_one.trans_le h').ne'

/-- **Cone step.** If a `d`-slice `N ⊆ C` of order `r` meets `closure (C \ N)`, then the totally convex
set `C` contains a nonempty `(d + 1)`-slice of order `r`. -/
theorem exists_slice_succ_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C N : Set M} {d : ℕ} (hC : IsTotallyConvexFinite g C)
    (hN : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d N) (hNC : N ⊆ C)
    {p : M} (hpN : p ∈ N) (hpfront : p ∈ closure (C \ N)) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ C ∧ IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (d + 1) S := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : (r : ℕ∞ω) ≠ 0 := coe_ne_zero_of_two_le hr
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_closedBall p 1)
  obtain ⟨rN, hrN, hnearest⟩ := exists_nearest_of_isLocallyClosed hN.isLocallyClosed hpN
  set ε : ℝ := min (min rN ρ) 1 / 3 with hεdef
  have hε : 0 < ε := by positivity
  have hεrN : 3 * ε ≤ rN := by
    have := (min_le_left (min rN ρ) 1).trans (min_le_left rN ρ); linarith
  have hερ : 3 * ε ≤ ρ := by
    have := (min_le_left (min rN ρ) 1).trans (min_le_right rN ρ); linarith
  have hε1 : 3 * ε ≤ 1 := by have := min_le_right (min rN ρ) 1; linarith
  obtain ⟨q, hqCN, hpq⟩ := Metric.mem_closure_iff.1 hpfront ε hε
  have hqp : dist q p < ε := by rw [dist_comm]; exact hpq
  obtain ⟨z, hzN, hzmin⟩ := hnearest q (by
    change dist q p < rN; linarith)
  have hqz : dist q z ≤ dist q p := hzmin p hpN
  have hqK : q ∈ closedBall p 1 := by
    change dist q p ≤ 1; linarith
  obtain ⟨e, hsrc, htgt, hexp, hdist, hbal, h0, he0, -⟩ := hch q hqK
  set R : Set M := ball p (2 * ε) with hRdef
  have hRopen : IsOpen R := isOpen_ball
  have hzR : z ∈ R := by
    change dist z p < 2 * ε
    have := dist_triangle z q p
    rw [dist_comm z q] at this
    linarith
  have hNRtarget : N ∩ R ⊆ e.target := by
    rintro y ⟨-, hyR⟩
    rw [htgt]
    change dist y q < ρ
    have hyp : dist y p < 2 * ε := hyR
    have := dist_triangle y p q
    rw [dist_comm p q] at this
    linarith
  set Sco : Set E := e.symm '' (N ∩ R) with hScodef
  have hSco : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) d Sco :=
    (hN.inter_open hRopen).image e.symm hNRtarget
  have ha : e.symm z ∈ Sco := ⟨z, ⟨hzN, hzR⟩, rfl⟩
  obtain ⟨L, U, f, W₀, hLfin, hdim, hUopen, h0U, hfsmooth, hfinj, hf0, -, -, hfimage⟩ :=
    hSco.exists_param hk0 ha
  have : FiniteDimensional ℝ L := hLfin
  have hparam (x : L) (hx : x ∈ U) :
      ∃ y ∈ N ∩ R, e (f x) = y ∧ e.symm y = f x := by
    have hfx : f x ∈ Sco := by
      have hh : f x ∈ f '' U := mem_image_of_mem f hx
      rw [hfimage] at hh
      exact hh.2
    obtain ⟨y, hy, heq⟩ := hfx
    refine ⟨y, hy, ?_, heq⟩
    rw [← heq]
    exact e.toPartialEquiv.right_inv (hNRtarget hy)
  have hfsrc (x : L) (hx : x ∈ U) : f x ∈ e.source := by
    obtain ⟨y, hy, -, hsymm⟩ := hparam x hx
    rw [← hsymm]
    exact e.toPartialEquiv.map_target (hNRtarget hy)
  set B : E →L[ℝ] E →L[ℝ] ℝ := (g.inner q : E →L[ℝ] E →L[ℝ] ℝ) with hBdef
  have hradial (x : L) (hx : x ∈ U) : dist q (e (f x)) ^ 2 = B (f x) (f x) := by
    rw [hdist (f x) (hfsrc x hx),
      Real.sq_sqrt (DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g q (f x))]
    rfl
  have hDfa : e (f 0) = z := by
    rw [hf0]
    exact e.toPartialEquiv.right_inv (hNRtarget ⟨hzN, hzR⟩)
  have hlocal : IsLocalMin (fun x : L => B (f x) (f x)) 0 := by
    apply (show IsMinOn (fun x : L => B (f x) (f x)) U 0 from ?_).isLocalMin
      (hUopen.mem_nhds h0U)
    intro x hx
    change B (f 0) (f 0) ≤ B (f x) (f x)
    rw [← hradial 0 h0U, ← hradial x hx, hDfa]
    obtain ⟨y, hy, hDy, -⟩ := hparam x hx
    rw [hDy]
    exact pow_le_pow_left₀ dist_nonneg (hzmin y hy.1) 2
  have hfDiff : DifferentiableAt ℝ f 0 :=
    (hfsmooth.contDiffAt (hUopen.mem_nhds h0U)).differentiableAt hk0
  have hfne : f 0 ≠ 0 := by
    intro hzero
    have hqz' : q = z := by rw [← hDfa, hzero, he0]
    exact hqCN.2 (hqz' ▸ hzN)
  have htrans : f 0 ∉ (fderiv ℝ f 0).range :=
    radial_not_mem_range_of_quad_min B (fun v hv => g.pos q v hv) hfDiff hlocal hfne
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hbase : (1 / 2 : ℝ) • f 0 ∈ e.source :=
    hbal _ (hfsrc 0 h0U) _ ⟨by norm_num, by norm_num⟩
  obtain ⟨V, -, hbaseV, hVsub, hVsrc, hslice⟩ :=
    exists_cone_image_ofOrder (k := r) hr1 e hUopen h0U isOpen_Ioo hhalf hfsmooth hfinj
      (by norm_num) htrans hbase
  set Sraw := e '' ((fun z : L × ℝ => z.2 • f z.1) '' V) with hSrawdef
  have hrawC : Sraw ⊆ C := by
    rintro _ ⟨_, ⟨xt, hxtV, rfl⟩, rfl⟩
    have hxt := hVsub hxtV
    obtain ⟨y, hy, hDy, -⟩ := hparam xt.1 hxt.1
    have ht : xt.2 ∈ Icc (0 : ℝ) 1 := ⟨hxt.2.1.le, hxt.2.2.le⟩
    have hsrc_t : xt.2 • f xt.1 ∈ e.source := hVsrc ⟨xt, hxtV, rfl⟩
    have hend : g.expMap (⟨q, (1 : ℝ) • f xt.1⟩ : TangentBundle I M) ∈ C := by
      rw [one_smul, ← hexp _ (hfsrc xt.1 hxt.1), hDy]
      exact hNC hy.1
    have hmem := hC.expMap_mem hr hnorm zero_le_one hqCN.1 hend xt.2 ht
    change e (xt.2 • f xt.1) ∈ C
    rw [hexp _ hsrc_t]
    exact hmem
  refine ⟨Sraw, ⟨e ((1 / 2 : ℝ) • f 0), ⟨(1 / 2 : ℝ) • f 0, ⟨(0, 1 / 2), hbaseV, rfl⟩, rfl⟩⟩,
    hrawC, ?_⟩
  simpa only [hdim] using hslice

/-- **Local uniqueness of top slices.** A slice of the relative dimension inside the totally convex
`C` agrees with `C` near each of its points. -/
theorem maxSlice_eq_near_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C N : Set M} (hC : IsTotallyConvexFinite g C)
    (hN : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) N) (hNC : N ⊆ C)
    {p : M} (hpN : p ∈ N) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ∩ C = U ∩ N := by
  have hpfront : p ∉ closure (C \ N) := by
    intro hpfront
    obtain ⟨S, hSne, hSC, hS⟩ := exists_slice_succ_finite g hr hnorm hC hN hNC hpN hpfront
    exact (Nat.not_succ_le_self _) (le_maxSliceDimOfOrder (I := I) ⟨S, hSne, hSC, hS⟩)
  refine ⟨(closure (C \ N))ᶜ, isClosed_closure.isOpen_compl, hpfront, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    by_contra hxN
    exact hxU (subset_closure ⟨hxC, hxN⟩)
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, hNC hxN⟩

/-- The relative interior agrees with `C` near each of its points. -/
theorem maxSliceLocusOfOrder_eq_near
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) {p : M}
    (hp : p ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ∩ maxSliceLocusOfOrder I (r : ℕ∞ω) C = U ∩ C := by
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hEq⟩ := maxSlice_eq_near_finite g hr hnorm hC hN hNC hpN
  refine ⟨U, hU, hpU, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxU, hxL⟩
    exact ⟨hxU, maxSliceLocusOfOrder_subset hxL⟩
  · rintro x hx
    rw [hEq] at hx
    exact ⟨hx.1, N, hx.2, hNC, hN⟩

/-- **The relative interior is a slice of the relative dimension.** -/
theorem isEmbeddedSliceOfOrder_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) :
    IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C)
      (maxSliceLocusOfOrder I (r : ℕ∞ω) C) := by
  apply IsEmbeddedSliceOfOrder.of_germ
  intro p hp
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hEq⟩ := maxSlice_eq_near_finite g hr hnorm hC hN hNC hpN
  refine ⟨N, U, hN, hU, hpU, hpN, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxU, hxL⟩
    rw [← hEq]
    exact ⟨hxU, maxSliceLocusOfOrder_subset hxL⟩
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, N, hxN, hNC, hN⟩

/-- **The relative interior is relatively open:** `relint = C ∩ O` for an open `O`. -/
theorem exists_isOpen_inter_eq_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) :
    ∃ O : Set M, IsOpen O ∧ C ∩ O = maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  refine ⟨⋃₀ {U : Set M | IsOpen U ∧ U ∩ maxSliceLocusOfOrder I (r : ℕ∞ω) C = U ∩ C},
    isOpen_sUnion fun U hU => hU.1, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxC, U, hU, hxU⟩
    have hx : x ∈ U ∩ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
      rw [hU.2]
      exact ⟨hxU, hxC⟩
    exact hx.2
  · intro x hx
    obtain ⟨U, hU, hxU, hUeq⟩ := maxSliceLocusOfOrder_eq_near g hr hnorm hC hx
    exact ⟨maxSliceLocusOfOrder_subset hx, U, ⟨hU, hUeq⟩, hxU⟩

/-- **Relative radial cone** (uniform on a compact set `K`): for `y ∈ K ∩ C` and `|v|_{g_y} < ρ`, if
`exp_y v` lies in the relative interior of the totally convex `C`, so does `exp_y (a v)`, `a ∈ (0, 1]`. -/
theorem exists_expMap_smul_mem_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {K : Set M} (hK : IsCompact K) :
    ∃ ρ > 0, ∀ {C : Set M}, IsTotallyConvexFinite g C → ∀ y ∈ K, y ∈ C → ∀ v : E,
      g.inner y v v < ρ ^ 2 →
        g.expMap (⟨y, v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C →
          ∀ a ∈ Ioc (0 : ℝ) 1,
            g.expMap (⟨y, a • v⟩ : TangentBundle I M) ∈ maxSliceLocusOfOrder I (r : ℕ∞ω) C := by
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm hK
  refine ⟨ρ, hρ, fun {C} hC y hyK hyC v hv hvL a ha => ?_⟩
  obtain ⟨e, hsrc, htgt, hexp, -, hbal, -, -, -⟩ := hch y hyK
  obtain ⟨N, hvN, hNC, hN⟩ := hvL
  have hvsrc : v ∈ e.source := by rw [hsrc]; exact hv
  have hNtgt : N ∩ ball y ρ ⊆ e.target := fun _ hu => by rw [htgt]; exact hu.2
  set Sco : Set E := e.symm '' (N ∩ ball y ρ) with hScodef
  have hSco : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) Sco :=
    (hN.inter_open isOpen_ball).image e.symm hNtgt
  set St : Set E := (fun w : E => a • w) '' Sco with hStdef
  have hSt : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) St :=
    hSco.smul_image (ne_of_gt ha.1)
  have hScosrc : ∀ w ∈ Sco, w ∈ e.source := by
    rintro _ ⟨u, hu, rfl⟩
    exact e.toPartialEquiv.map_target (hNtgt hu)
  have hStsrc : St ⊆ e.source := by
    rintro _ ⟨w, hw, rfl⟩
    exact hbal w (hScosrc w hw) a ⟨by linarith [ha.1], ha.2⟩
  set T : Set M := e '' St with hTdef
  have hT : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) (maxSliceDimOfOrder I (r : ℕ∞ω) C) T :=
    hSt.image e hStsrc
  have hTC : T ⊆ C := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hw
    have hwsrc : e.symm u ∈ e.source := e.toPartialEquiv.map_target (hNtgt hu)
    have hright : e (e.symm u) = u := e.toPartialEquiv.right_inv (hNtgt hu)
    have hend : g.expMap (⟨y, (1 : ℝ) • e.symm u⟩ : TangentBundle I M) ∈ C := by
      rw [one_smul, ← hexp _ hwsrc, hright]
      exact hNC hu.1
    have hmem := hC.expMap_mem hr hnorm zero_le_one hyC hend a ⟨ha.1.le, ha.2⟩
    change e (a • e.symm u) ∈ C
    rw [hexp _ (hStsrc ⟨e.symm u, ⟨u, hu, rfl⟩, rfl⟩)]
    exact hmem
  have hevN : e v ∈ N ∩ ball y ρ := by
    refine ⟨?_, ?_⟩
    · rw [hexp v hvsrc]; exact hvN
    · rw [← htgt]; exact e.toPartialEquiv.map_source hvsrc
  have hvSco : v ∈ Sco := ⟨e v, hevN, e.toPartialEquiv.left_inv hvsrc⟩
  have hav : a • v ∈ St := ⟨v, hvSco, rfl⟩
  have heav : e (a • v) = g.expMap (⟨y, a • v⟩ : TangentBundle I M) := hexp _ (hStsrc hav)
  rw [← heav]
  exact subset_maxSliceLocusOfOrder hTC hT ⟨a • v, hav, rfl⟩

/-- **The relative interior is totally geodesic.** -/
theorem isTotallyGeodesicFinite_maxSliceLocusOfOrder
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {C : Set M} (hC : IsTotallyConvexFinite g C) :
    IsTotallyGeodesicFinite g (maxSliceLocusOfOrder I (r : ℕ∞ω) C) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : (r : ℕ∞ω) ≠ 0 := coe_ne_zero_of_two_le hr
  have hD : g.geodesicFlowDomain = univ := g.geodesicFlowDomain_eq_univ hr hnorm
  set Z := maxSliceLocusOfOrder I (r : ℕ∞ω) C with hZdef
  set d := maxSliceDimOfOrder I (r : ℕ∞ω) C with hddef
  have hZ : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d Z :=
    isEmbeddedSliceOfOrder_maxSliceLocusOfOrder g hr hnorm hC
  intro x hx v hv
  obtain ⟨ρ, hρ, hch⟩ := exists_uniform_normal_partialDiffeomorph g hr hnorm
    (isCompact_singleton (x := x))
  obtain ⟨e, hsrc, htgt, hexp, hdist, hbal, h0, he0, hderiv⟩ := hch x rfl
  obtain ⟨U, hU, hxU, hUeq⟩ := maxSliceLocusOfOrder_eq_near g hr hnorm hC hx
  obtain ⟨ρ₁, hρ₁, hρ₁U⟩ := Metric.isOpen_iff.1 hU x hxU
  set ρ' : ℝ := min ρ ρ₁ with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ hρ₁
  have hCball : C ∩ ball x ρ' ⊆ Z := by
    rintro y ⟨hyC, hyb⟩
    have hyU : y ∈ U := hρ₁U (ball_subset_ball (min_le_right _ _) hyb)
    have h : y ∈ U ∩ C := ⟨hyU, hyC⟩
    rw [← hUeq] at h
    exact h.2
  have hZtgt : Z ∩ ball x ρ' ⊆ e.target := by
    rintro y ⟨-, hyb⟩
    rw [htgt]
    exact ball_subset_ball (min_le_left _ _) hyb
  set V : Set E := e.symm '' (Z ∩ ball x ρ') with hVdef
  have hVslice : IsEmbeddedSliceOfOrder 𝓘(ℝ, E) (r : ℕ∞ω) d V :=
    (hZ.inter_open isOpen_ball).image e.symm hZtgt
  have hsymm0 : e.symm x = 0 := by
    rw [← he0]
    exact e.toPartialEquiv.left_inv h0
  have h0V : (0 : E) ∈ V := ⟨x, ⟨hx, mem_ball_self hρ'⟩, hsymm0⟩
  -- star-shapedness of `V`
  have hstar : ∀ u ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, e (t • u) ∈ Z ∩ ball x ρ' := by
    rintro _ ⟨y, hy, rfl⟩ t ht
    have husrc : e.symm y ∈ e.source := e.toPartialEquiv.map_target (hZtgt hy)
    have htsrc : t • e.symm y ∈ e.source := hbal _ husrc t ⟨by linarith [ht.1], ht.2⟩
    have hright : e (e.symm y) = y := e.toPartialEquiv.right_inv (hZtgt hy)
    have hend : g.expMap (⟨x, (1 : ℝ) • e.symm y⟩ : TangentBundle I M) ∈ C := by
      rw [one_smul, ← hexp _ husrc, hright]
      exact maxSliceLocusOfOrder_subset hy.1
    have hmemC : e (t • e.symm y) ∈ C := by
      rw [hexp _ htsrc]
      exact hC.expMap_mem hr hnorm zero_le_one (maxSliceLocusOfOrder_subset hx) hend t ht
    have hdy : dist x y < ρ' := by rw [dist_comm]; exact hy.2
    have hball : e (t • e.symm y) ∈ ball x ρ' := by
      rw [mem_ball, dist_comm, hdist _ htsrc]
      have hsm : g.inner x (t • e.symm y) (t • e.symm y) = t ^ 2 * g.inner x (e.symm y) (e.symm y) :=
        DifferentialGeometry.Geometry.Collapse.finite_inner_smul_self g x t (e.symm y)
      have hyd : Real.sqrt (g.inner x (e.symm y) (e.symm y)) = dist x y := by
        rw [← hdist _ husrc, hright]
      rw [hsm, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1, hyd]
      nlinarith [dist_nonneg (x := x) (y := y), ht.1, ht.2]
    exact ⟨hCball ⟨hmemC, hball⟩, hball⟩
  -- `V` lies in the tangent space of the relative interior
  set L : Submodule ℝ E := sliceTangent I Z x with hLdef
  have hVL : V ⊆ (L : Set E) := by
    intro u hu
    have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => t • u) 0
        ((1 : ℝ →L[ℝ] ℝ).smulRight u) := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const u).hasFDerivAt
      simp only [one_smul] at h
      exact h.hasMFDerivAt
    have hderiv' : HasMFDerivAt 𝓘(ℝ, E) I e ((fun t : ℝ => t • u) 0)
        (ContinuousLinearMap.id ℝ E) := by
      rw [show (fun t : ℝ => t • u) 0 = (0 : E) from zero_smul ℝ u]
      exact hderiv
    have hcomp := hderiv'.comp (0 : ℝ) hlin
    have hf0 : (fun t : ℝ => e (t • u)) 0 = x := by
      simp only [zero_smul]
      exact he0
    have hS : ∀ᶠ t in 𝓝[>] (0 : ℝ), (fun t : ℝ => e (t • u)) t ∈ Z := by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
      exact (hstar u hu t ⟨ht.1.le, ht.2.le⟩).1
    have hmf : mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => e (t • u)) 0 =
        (ContinuousLinearMap.id ℝ E).comp ((1 : ℝ →L[ℝ] ℝ).smulRight u) := hcomp.mfderiv
    change u ∈ sliceTangent I Z x
    refine Submodule.subset_span ⟨fun t : ℝ => e (t • u), hf0, hS, hcomp.mdifferentiableAt, ?_⟩
    rw [hmf]
    change (1 : ℝ) • u = u
    rw [one_smul]
  have hLfin : FiniteDimensional ℝ L := finiteDimensional_sliceTangent_ofOrder hk0 hZ hx
  have hdimL : Module.finrank ℝ L.toAffineSubspace.direction = d := by
    rw [Submodule.toAffineSubspace_direction]
    exact finrank_sliceTangent_ofOrder hk0 hZ hx
  have hVA : V ⊆ (L.toAffineSubspace : Set E) := fun u hu => hVL hu
  obtain ⟨ε, hε, hballV⟩ := hVslice.exists_ball_affine_subset hk0 hVA hdimL h0V
  -- conclusion
  obtain ⟨w, rfl⟩ : ∃ w : E, w = v := ⟨v, rfl⟩
  have hvL : w ∈ L := hv
  refine ⟨ε / (‖w‖ + 1), by positivity, fun t ht => ?_⟩
  have htv : t • w ∈ V := by
    apply hballV
    · exact Submodule.mem_toAffineSubspace.2 (L.smul_mem t hvL)
    · rw [dist_zero_right, norm_smul]
      have h1 : |t| < ε / (‖w‖ + 1) := abs_lt.2 ⟨by linarith [ht.1], ht.2⟩
      have h2 : |t| * (‖w‖ + 1) < ε := by
        rwa [lt_div_iff₀ (by positivity)] at h1
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg t, norm_nonneg w]
  obtain ⟨y, hy, hyv⟩ := htv
  have htvsrc : t • w ∈ e.source := by
    rw [← hyv]; exact e.toPartialEquiv.map_target (hZtgt hy)
  have hey : e (t • w) = y := by
    rw [← hyv]; exact e.toPartialEquiv.right_inv (hZtgt hy)
  have hflow : g.expMap (⟨x, t • w⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) t).proj :=
    g.expMap_smul_eq_proj_geodesicFlow hr1 x w t (by rw [hD]; exact mem_univ _)
  rw [← hflow]
  have hexp' : e (t • w) = g.expMap (⟨x, t • w⟩ : TangentBundle I M) := hexp _ htvsrc
  rw [← hexp', hey]
  exact hy.1

end DifferentialGeometry.Geometry.FiniteSoul
