import DifferentialGeometry.Geometry.Comparison.Soul.SoulConvexCore
import DifferentialGeometry.Geometry.Comparison.Soul.ConeSlice
import DifferentialGeometry.Geometry.Comparison.Convexity.Geodesic
import DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Mathlib.Topology.MetricSpace.HausdorffDistance

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Integral.L2

namespace DifferentialGeometry.Geometry.Topology

section RelBoundaryDef

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

def relBoundary (I : ModelWithCorners ℝ E H) (C : Set M) : Set M :=
  C \ maxSliceLocus I C

theorem mem_relBoundary {C : Set M} {x : M} :
    x ∈ relBoundary I C ↔ x ∈ C ∧ x ∉ maxSliceLocus I C := Iff.rfl

theorem relBoundary_subset {C : Set M} : relBoundary I C ⊆ C := sdiff_subset

theorem not_mem_relBoundary_of_mem_maxSliceLocus {C : Set M} {x : M}
    (hx : x ∈ maxSliceLocus I C) : x ∉ relBoundary I C := fun h => h.2 hx

theorem union_maxSliceLocus_relBoundary {C : Set M} :
    maxSliceLocus I C ∪ relBoundary I C = C :=
  union_sdiff_cancel maxSliceLocus_subset

theorem relBoundary_eq_empty_iff {C : Set M} :
    relBoundary I C = ∅ ↔ maxSliceLocus I C = C :=
  Set.sdiff_eq_empty.trans
    ⟨fun h => Subset.antisymm maxSliceLocus_subset h, fun h => h.ge⟩

end RelBoundaryDef

private theorem exists_nearest_of_locallyClosed {X : Type*} [MetricSpace X] [ProperSpace X]
    {S : Set X} (hS : IsLocallyClosed S) {p : X} (hp : p ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.ball p r,
      ∃ z ∈ S, IsMinOn (fun y => dist q y) S z := by
  obtain ⟨O, Z, hO, hZ, rfl⟩ := hS
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hO p hp.1
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro q hq
  obtain ⟨z, hz, hdist⟩ := hZ.exists_infDist_eq_dist ⟨p, hp.2⟩ q
  have hqz : dist q z ≤ dist q p := by rw [← hdist]; exact Metric.infDist_le_dist_of_mem hp.2
  have hzO : z ∈ O := by
    apply hrO
    have htri := dist_triangle z q p
    rw [dist_comm z q] at htri
    change dist z p < r
    have hqp : dist q p < r / 2 := hq
    linarith
  refine ⟨z, ⟨hzO, hz⟩, ?_⟩
  intro y hy
  change dist q z ≤ dist q y
  rw [← hdist]
  exact Metric.infDist_le_dist_of_mem hy.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem riemannian_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem branch_source_tube
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∃ A ∈ 𝓝 p, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ v : TangentSpace I y,
      Real.sqrt (g.inner y v v) < r → (⟨y, v⟩ : TangentBundle I M) ∈ B.hom.source := by
  let e := trivializationAt E (TangentSpace I) p
  let O : Set (M × E) := e '' (e.source ∩ B.hom.source)
  have hpbase : p ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' p
  have hO : IsOpen O := e.toOpenPartialHomeomorph.isOpen_image_source_inter B.hom.open_source
  have hpO : (p, (0 : E)) ∈ O := by
    refine ⟨⟨p, 0⟩, ⟨?_, B.zero_mem⟩, e.zeroSection ℝ hpbase⟩
    rwa [e.mem_source]
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hO.mem_nhds hpO)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  obtain ⟨C, hC, hbound⟩ := eventually_norm_trivializationAt_lt E (fun x : M => TangentSpace I x) p
  change ∀ᶠ y in 𝓝 p, ‖e.continuousLinearMapAt ℝ y‖ < C at hbound
  let A := (U ∩ {y | ‖e.continuousLinearMapAt ℝ y‖ < C}) ∩ e.baseSet
  have hA : A ∈ 𝓝 p := inter_mem (inter_mem hU hbound) (e.open_baseSet.mem_nhds hpbase)
  refine ⟨A, hA, r / C, div_pos hr hC, ?_⟩
  intro y hy v hv
  have hnorm : ‖v‖ = Real.sqrt (g.inner y v v) := by
    have h := hEnorm y v
    rw [← ofReal_norm] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).1 h
  let w := e.continuousLinearMapAt ℝ y v
  have hw : ‖w‖ < r := by
    calc
      ‖w‖ ≤ ‖e.continuousLinearMapAt ℝ y‖ * ‖v‖ := (e.continuousLinearMapAt ℝ y).le_opNorm v
      _ ≤ C * ‖v‖ := mul_le_mul_of_nonneg_right hy.1.2.le (norm_nonneg v)
      _ < C * (r / C) := mul_lt_mul_of_pos_left (by rwa [hnorm]) hC
      _ = r := mul_div_cancel₀ r hC.ne'
  have hwV : w ∈ V := hrV (by simpa only [Metric.mem_ball, dist_zero_right] using hw)
  obtain ⟨z, hz, hez⟩ := hUV (Set.mk_mem_prod hy.1.1 hwV)
  have hvsource : (⟨y, v⟩ : TangentBundle I M) ∈ e.source := by
    rw [e.mem_source]
    exact hy.2
  have hev : e (⟨y, v⟩ : TangentBundle I M) = (y, w) := by
    rw [e.apply_eq_prod_continuousLinearEquivAt ℝ y hy.2 v]
    exact congrArg (fun a : E => (y, a)) (congrFun (e.coe_continuousLinearEquivAt_eq hy.2) v)
  have hzv := e.toOpenPartialHomeomorph.injOn hz.1 hvsource (hez.trans hev.symm)
  exact hzv ▸ hz.2

private theorem branch_minimizing_pair
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (B : DiagonalInverseBranch (I := I) g hEnorm p) :
    ∀ᶠ yz : M × M in 𝓝 (p, p),
      yz.2 ∈ (B.fixed yz.1).hom.target ∧
      (B.fixed yz.1).hom.symm yz.2 = (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, t • (B.fixed yz.1).hom.symm yz.2 ∈ (B.fixed yz.1).hom.source) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        (B.fixed yz.1).hom (t • (B.fixed yz.1).hom.symm yz.2) = minJoin (I := I) g hEnorm yz.1 yz.2 t := by
  obtain ⟨A, hA, r, hr, hsource⟩ := branch_source_tube B
  have hdist : {yz : M × M | dist yz.1 yz.2 < r} ∈ 𝓝 (p, p) :=
    (isOpen_lt (continuous_fst.dist continuous_snd) continuous_const).mem_nhds (by simpa using hr)
  filter_upwards [continuous_fst.continuousAt hA, hdist] with yz hyA hyd
  have hseg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (⟨yz.1, t • minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M) ∈ B.hom.source := by
    apply hsource yz.1 hyA
    rw [sqrt_gInner_smul_self (I := I) g yz.1 ht.1, minimizingVec_len, riemannian_toReal_eq_dist (I := I)]
    exact (mul_le_of_le_one_left dist_nonneg ht.2).trans_lt hyd
  have hvsource : (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M) ∈ B.hom.source := by
    simpa only [one_smul] using hseg 1 ⟨zero_le_one, le_rfl⟩
  have hEq := B.inv_eq_of_exp hvsource (minimizingVec_exp (I := I) g hEnorm yz.1 yz.2)
  have hinv : (B.fixed yz.1).hom.symm yz.2 = (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E) := by
    exact congrArg (fun z : TangentBundle I M => (z.snd : E)) hEq
  have htarget : yz.2 ∈ (B.fixed yz.1).hom.target := by
    have hh := B.hom.map_source hvsource
    have heq : B.hom (⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ : TangentBundle I M) =
        diagExp (I := I) g hEnorm ⟨yz.1, minimizingVec (I := I) g hEnorm yz.1 yz.2⟩ :=
      B.hom_eq hvsource
    rw [heq] at hh
    have hpairmem : (yz.1, yz.2) ∈ B.hom.target := by
      simpa only [diagExp, minimizingVec_exp] using hh
    exact (DiagonalInverseBranch.fixed_target (p := yz.1) B yz.2).2 hpairmem
  refine ⟨htarget, hinv, ?_, ?_⟩
  · intro t ht
    rw [hinv]
    exact hseg t ht
  · intro t ht
    rw [hinv]
    change expMapIntrinsic (I := I) g hEnorm yz.1
      (t • minimizingVec (I := I) g hEnorm yz.1 yz.2) = minJoin (I := I) g hEnorm yz.1 yz.2 t
    exact intrinsicGeodesic_smul (I := I) g hEnorm yz.1 (minimizingVec (I := I) g hEnorm yz.1 yz.2) t


theorem IsTotallyConvex.minJoin
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {p q : M} (hp : p ∈ C) (hq : q ∈ C) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    minJoin (I := I) g hEnorm p q t ∈ C := by
  have h0 : intrinsicGeodesic (I := I) g hEnorm p (minimizingVec (I := I) g hEnorm p q) 0 = p :=
    intrinsicGeodesic_zero (I := I) g hEnorm p _
  have h1 : intrinsicGeodesic (I := I) g hEnorm p (minimizingVec (I := I) g hEnorm p q) 1 = q := by
    rw [← expMapIntrinsic_def, minimizingVec_exp]
  have hmaps : MapsTo (intrinsicGeodesic (I := I) g hEnorm p
      (minimizingVec (I := I) g hEnorm p q)) (Icc (0 : ℝ) 1) C :=
    hC zero_le_one
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (minimizingVec (I := I) g hEnorm p q)).isGeodesicOn _)
      (intrinsicGeodesic_continuous (I := I) g hEnorm p _).continuousOn
      (by rw [h0]; exact hp) (by rw [h1]; exact hq)
  exact hmaps ht

theorem exists_slice_succ
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C N : Set M} {d : ℕ} (hC : IsTotallyConvex (I := I) g C)
    (hN : IsEmbeddedSlice I d N) (hNC : N ⊆ C)
    {p : M} (hpN : p ∈ N) (hpfront : p ∈ closure (C \ N))
    {W : Set M} (hW : W ∈ 𝓝 p) :
    ∃ S : Set M, S.Nonempty ∧ S ⊆ W ∩ C ∧ IsEmbeddedSlice I (d + 1) S := by
  classical
  let : ProperSpace M := ⟨soul_isCompact_closedBall (I := I) g hEnorm⟩
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
  let D (q : M) := (B.fixed q).hom
  let Good : Set (M × M) := {yz |
    yz.2 ∈ (D yz.1).target ∧
    (D yz.1).symm yz.2 = (minimizingVec (I := I) g hEnorm yz.1 yz.2 : E) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, t • (D yz.1).symm yz.2 ∈ (D yz.1).source) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      D yz.1 (t • (D yz.1).symm yz.2) = minJoin (I := I) g hEnorm yz.1 yz.2 t}
  have hGood : Good ∈ 𝓝 (p, p) := branch_minimizing_pair B
  obtain ⟨P, Q, hPopen, hpP, hQopen, hpQ, hPQ⟩ := mem_nhds_prod_iff'.1 hGood
  obtain ⟨O, hOW, hOopen, hpO⟩ := mem_nhds_iff.1 hW
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 (hQopen.inter hOopen) p ⟨hpQ, hpO⟩
  obtain ⟨rN, hrN, hnearest⟩ := exists_nearest_of_locallyClosed hN.isLocallyClosed hpN
  let ρ : ℝ := min rN (ε / 3)
  have hρ : 0 < ρ := lt_min hrN (by positivity)
  have hnear : P ∩ Metric.ball p ρ ∈ 𝓝 p :=
    inter_mem (hPopen.mem_nhds hpP) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
  obtain ⟨q, hqnear, hqdiff⟩ := (mem_closure_iff_nhds.1 hpfront) _ hnear
  have hqball : dist q p < ρ := hqnear.2
  obtain ⟨z, hzN, hzmin⟩ := hnearest q (hqball.trans_le (min_le_left _ _))
  have hqz : dist q z ≤ dist q p := hzmin hpN
  have hzε : z ∈ Metric.ball p ε := by
    change dist z p < ε
    calc
      dist z p ≤ dist z q + dist q p := dist_triangle z q p
      _ = dist q z + dist q p := by rw [dist_comm z q]
      _ ≤ dist q p + dist q p := add_le_add hqz le_rfl
      _ < ρ + ρ := add_lt_add hqball hqball
      _ ≤ ε / 3 + ε / 3 := add_le_add (min_le_right _ _) (min_le_right _ _)
      _ < ε := by linarith
  have hzQO := hεsub hzε
  let Dq := D q
  have hqzGood : (q, z) ∈ Good := hPQ ⟨hqnear.1, hzQO.1⟩
  have hzTarget : z ∈ Dq.target := hqzGood.1
  let R := Q ∩ O
  have hRopen : IsOpen R := hQopen.inter hOopen
  have hNRtarget : N ∩ R ⊆ Dq.symm.source := by
    rintro y ⟨_, hyR⟩
    exact (hPQ (show (q, y) ∈ P ×ˢ Q from ⟨hqnear.1, hyR.1⟩)).1
  let Sco := Dq.symm '' (N ∩ R)
  have hSco : IsEmbeddedSlice 𝓘(ℝ, E) d Sco :=
    (hN.inter_open hRopen).image Dq.symm hNRtarget
  have ha : Dq.symm z ∈ Sco := ⟨z, ⟨hzN, hzQO⟩, rfl⟩
  obtain ⟨L, U, f, W₀, hLfin, hdim, hUopen, h0U, hfsmooth,
    hfinj, hf0, _, _, hfimage⟩ := hSco.exists_param ha
  let : FiniteDimensional ℝ L := hLfin
  have hparam (x : L) (hx : x ∈ U) :
      ∃ y ∈ N ∩ R, Dq (f x) = y ∧ Dq.symm y = f x := by
    have hfx : f x ∈ Sco := by
      have hh : f x ∈ f '' U := mem_image_of_mem f hx
      rw [hfimage] at hh
      exact hh.2
    obtain ⟨y, hy, heq⟩ := hfx
    refine ⟨y, hy, ?_, heq⟩
    rw [← heq]
    exact Dq.toPartialEquiv.right_inv (hNRtarget hy)
  have hmaps : MapsTo (fun x : L => Dq (f x)) U N := by
    intro x hx
    obtain ⟨y, hy, heq, _⟩ := hparam x hx
    simpa only [heq] using hy.1
  let A := modelInnerAt (I := I) g q
  have hAeq : ∀ v : TangentSpace I q, A (v : E) (v : E) = g.inner q v v := fun _ => rfl
  have hradial (x : L) (hx : x ∈ U) : dist q (Dq (f x)) ^ 2 = A (f x) (f x) := by
    obtain ⟨y, hy, hDxy, hsymm⟩ := hparam x hx
    have hyGood : (q, y) ∈ Good := hPQ ⟨hqnear.1, hy.2.1⟩
    have hlen : Real.sqrt (A (Dq.symm y) (Dq.symm y)) = dist q y := by
      rw [hyGood.2.1, hAeq, minimizingVec_len, riemannian_toReal_eq_dist (I := I)]
    rw [hDxy, ← hlen, Real.sq_sqrt (modelInnerAt_nonneg (I := I) g q _), hsymm]
  have hDfa : Dq (f 0) = z := by
    rw [hf0]
    exact Dq.toPartialEquiv.right_inv hzTarget
  have hlocal : IsLocalMin (fun x : L => A (f x) (f x)) 0 := by
    apply (show IsMinOn (fun x : L => A (f x) (f x)) U 0 from ?_).isLocalMin
      (hUopen.mem_nhds h0U)
    intro x hx
    change A (f 0) (f 0) ≤ A (f x) (f x)
    rw [← hradial 0 h0U, ← hradial x hx, hDfa]
    exact (sq_le_sq₀ dist_nonneg dist_nonneg).2 (hzmin (hmaps hx))
  have hfDiff := (hfsmooth.contDiffAt (hUopen.mem_nhds h0U)).differentiableAt (by simp)
  have hfne : f 0 ≠ 0 := by
    intro hzero
    have hzeroSource : (0 : E) ∈ Dq.source := by
      simpa only [zero_smul] using hqzGood.2.2.1 0 ⟨le_rfl, zero_le_one⟩
    have hDzero : Dq 0 = q := by
      change (B.fixed q).hom 0 = q
      rw [← (B.fixed q).hom_eq hzeroSource]
      exact expMapIntrinsic_zero (I := I) g hEnorm q
    have hqzEq : q = z := by rw [← hDfa, hzero, hDzero]
    exact hqdiff.2 (hqzEq ▸ hzN)
  have htrans : f 0 ∉ (fderiv ℝ f 0).range :=
    radial_not_mem_range_of_quad_min A
      (fun _ hv => modelInnerAt_pos_of_ne_zero (I := I) g q hv) hfDiff hlocal hfne
  let ell : ℝ → E := fun t => t • f 0
  have hell : Continuous ell := continuous_id.smul continuous_const
  have hfaSource : f 0 ∈ Dq.source := by
    rw [hf0]
    exact Dq.symm.toPartialEquiv.map_source hzTarget
  have hDcont : ContinuousAt Dq (f 0) :=
    Dq.contMDiffOn_toFun.continuousOn.continuousAt (Dq.open_source.mem_nhds hfaSource)
  have hDell : ContinuousAt (fun t => Dq (ell t)) 1 :=
    hDcont.comp_of_eq hell.continuousAt (by simp only [ell, one_smul])
  have hlineSource : ell ⁻¹' Dq.source ∈ 𝓝 (1 : ℝ) := by
    apply hell.continuousAt
    simpa only [ell, one_smul] using Dq.open_source.mem_nhds hfaSource
  have hlineO : (fun t => Dq (ell t)) ⁻¹' O ∈ 𝓝 (1 : ℝ) := by
    apply hDell
    simpa only [ell, one_smul, hDfa] using hOopen.mem_nhds hzQO.2
  have honeClosure : (1 : ℝ) ∈ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨t₀, htline, htIoo⟩ :=
    (mem_closure_iff_nhds.1 honeClosure) _ (inter_mem hlineSource hlineO)
  let cone : L × ℝ → E := fun xt => xt.2 • f xt.1
  obtain ⟨V, _, hbaseV, hVsub, _, hslice⟩ :=
    exists_cone_image Dq hUopen h0U isOpen_Ioo htIoo hfsmooth hfinj
      (ne_of_gt htIoo.1) htrans htline.1
  let Sraw := Dq '' (cone '' V)
  have hrawC : Sraw ⊆ C := by
    rintro y ⟨w, ⟨xt, hxtV, rfl⟩, rfl⟩
    have hxt := hVsub hxtV
    obtain ⟨z', hz', _, hsymm⟩ := hparam xt.1 hxt.1
    have hzGood : (q, z') ∈ Good := hPQ ⟨hqnear.1, hz'.2.1⟩
    have ht : xt.2 ∈ Icc (0 : ℝ) 1 := ⟨hxt.2.1.le, hxt.2.2.le⟩
    change Dq (xt.2 • f xt.1) ∈ C
    rw [← hsymm, hzGood.2.2.2 xt.2 ht]
    exact hC.minJoin hEnorm hqdiff.1 (hNC hz'.1) ht
  refine ⟨Sraw ∩ O, ?_, ?_, ?_⟩
  · exact ⟨Dq (t₀ • f 0), ⟨t₀ • f 0, ⟨(0, t₀), hbaseV, rfl⟩, rfl⟩, htline.2⟩
  · rintro y ⟨hy, hyO⟩
    exact ⟨hOW hyO, hrawC hy⟩
  · have hs : IsEmbeddedSlice I (d + 1) Sraw := by
      simpa only [Sraw, cone, hdim] using hslice
    exact hs.inter_open hOopen

theorem maxSlice_eq_near
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C N : Set M} (hC : IsTotallyConvex (I := I) g C)
    (hN : IsEmbeddedSlice I (maxSliceDim I C) N) (hNC : N ⊆ C) {p : M} (hpN : p ∈ N) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ∩ C = U ∩ N := by
  have hpfront : p ∉ closure (C \ N) := by
    intro hpfront
    obtain ⟨S, hSne, hSC, hS⟩ := exists_slice_succ hEnorm hC hN hNC hpN hpfront
      (W := univ) univ_mem
    exact (Nat.not_succ_le_self _) (le_maxSliceDim (I := I)
      ⟨S, hSne, fun _ hx => (hSC hx).2, hS⟩)
  refine ⟨(closure (C \ N))ᶜ, isClosed_closure.isOpen_compl, hpfront, ?_⟩
  apply Subset.antisymm
  · rintro x ⟨hxU, hxC⟩
    refine ⟨hxU, ?_⟩
    by_contra hxN
    exact hxU (subset_closure ⟨hxC, hxN⟩)
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, hNC hxN⟩


theorem maxSliceLocus_eq_near
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) {p : M} (hp : p ∈ maxSliceLocus I C) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ∩ maxSliceLocus I C = U ∩ C := by
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hEq⟩ := maxSlice_eq_near hEnorm hC hN hNC hpN
  refine ⟨U, hU, hpU, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxU, hxL⟩
    exact ⟨hxU, maxSliceLocus_subset hxL⟩
  · rintro x hx
    rw [hEq] at hx
    exact ⟨hx.1, N, hx.2, hNC, hN⟩


theorem isOpen_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsOpen ((Subtype.val : C → M) ⁻¹' maxSliceLocus I C) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨p, hpC⟩ hpL
  obtain ⟨U, hU, hpU, hEq⟩ := maxSliceLocus_eq_near hEnorm hC hpL
  refine mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hpU) ?_
  intro q hqU
  have hq : (q : M) ∈ U ∩ C := ⟨hqU, q.property⟩
  rw [← hEq] at hq
  exact hq.2

theorem isEmbeddedSlice_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    IsEmbeddedSlice I (maxSliceDim I C) (maxSliceLocus I C) := by
  apply IsEmbeddedSlice.of_germ
  intro p hp
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  obtain ⟨U, hU, hpU, hEq⟩ := maxSlice_eq_near hEnorm hC hN hNC hpN
  refine ⟨N, U, hN, hU, hpU, hpN, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxU, hxL⟩
    rw [← hEq]
    exact ⟨hxU, maxSliceLocus_subset hxL⟩
  · rintro x ⟨hxU, hxN⟩
    exact ⟨hxU, N, hxN, hNC, hN⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
private theorem slice_image_smul {S : Set E} {d : ℕ}
    (hS : IsEmbeddedSlice 𝓘(ℝ, E) d S) {t : ℝ} (ht : t ≠ 0) :
    IsEmbeddedSlice 𝓘(ℝ, E) d ((fun x : E => t • x) '' S) := by
  let e : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
  have him := hS.image e.toDiffeomorph.toPartialDiffeomorph (fun x _ => mem_univ x)
  have heq : (e.toDiffeomorph.toPartialDiffeomorph : E → E) '' S = (fun x : E => t • x) '' S :=
    Set.image_congr' (fun _ => rfl)
  rwa [heq] at him

theorem maxSliceLocus_pair
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {c : M} (B : DiagonalInverseBranch (I := I) g hEnorm c) :
    ∀ᶠ pq : M × M in 𝓝 (c, c), pq.1 ∈ maxSliceLocus I C → pq.2 ∈ C →
      ∀ t ∈ Ioc (0 : ℝ) 1, minJoin (I := I) g hEnorm pq.2 pq.1 t ∈ maxSliceLocus I C := by
  let D (q : M) := (B.fixed q).hom
  let Good : Set (M × M) := {yz | yz.2 ∈ (D yz.1).target ∧
    ∀ t ∈ Icc (0 : ℝ) 1, t • (D yz.1).symm yz.2 ∈ (D yz.1).source ∧
      D yz.1 (t • (D yz.1).symm yz.2) = minJoin (I := I) g hEnorm yz.1 yz.2 t}
  have hGood : Good ∈ 𝓝 (c, c) := by
    filter_upwards [branch_minimizing_pair B] with yz hyz
    exact ⟨hyz.1, fun t ht => ⟨hyz.2.2.1 t ht, hyz.2.2.2 t ht⟩⟩
  obtain ⟨P, Q, hP, hcP, hQ, hcQ, hPQ⟩ := mem_nhds_prod_iff'.1 hGood
  filter_upwards [prod_mem_nhds (hQ.mem_nhds hcQ) (hP.mem_nhds hcP)] with pq hpq
  rcases pq with ⟨p, q⟩
  intro hp hq t ht
  obtain ⟨N, hpN, hNC, hN⟩ := hp
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  let Dq := D q
  have hsource : N ∩ Q ⊆ Dq.symm.source := by
    rintro y ⟨_, hyQ⟩
    exact (hPQ (show (q, y) ∈ P ×ˢ Q from ⟨hpq.2, hyQ⟩)).1
  let Sco := Dq.symm '' (N ∩ Q)
  have hSco : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) Sco :=
    (hN.inter_open hQ).image Dq.symm hsource
  let St := (fun v : E => t • v) '' Sco
  have hSt : IsEmbeddedSlice 𝓘(ℝ, E) (maxSliceDim I C) St := slice_image_smul hSco ht.1.ne'
  have hStSource : St ⊆ Dq.source := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ((hPQ (show (q, y) ∈ P ×ˢ Q from ⟨hpq.2, hy.2⟩)).2 t htIcc).1
  let T := Dq '' St
  have hT : IsEmbeddedSlice I (maxSliceDim I C) T := hSt.image Dq hStSource
  have hTC : T ⊆ C := by
    rintro _ ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    have hg : (q, y) ∈ Good := hPQ ⟨hpq.2, hy.2⟩
    rw [hg.2 t htIcc |>.2]
    exact hC.minJoin hEnorm hq (hNC hy.1) htIcc
  refine ⟨T, ?_, hTC, hT⟩
  refine ⟨t • Dq.symm p, ⟨Dq.symm p, ⟨p, ⟨hpN, hpq.1⟩, rfl⟩, rfl⟩, ?_⟩
  exact ((hPQ (show (q, p) ∈ P ×ˢ Q from ⟨hpq.2, hpq.1⟩)).2 t htIcc).2

theorem minJoin_intrinsicGeodesic_near
    {g : SmoothRiemannianMetric I M} {hEnorm : IsMetricNorm (I := I) g}
    {p : M} (v : TangentSpace I p) (s₀ : ℝ)
    (B : DiagonalInverseBranch (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p v s₀)) :
    ∀ᶠ st : ℝ × ℝ in 𝓝 (s₀, s₀), ∀ t : ℝ,
      minJoin (I := I) g hEnorm
        (intrinsicGeodesic (I := I) g hEnorm p v st.2)
        (intrinsicGeodesic (I := I) g hEnorm p v st.1) t =
      intrinsicGeodesic (I := I) g hEnorm p v (t * (st.1 - st.2) + st.2) := by
  let γ := intrinsicGeodesic (I := I) g hEnorm p v
  let pair : ℝ × ℝ → M × M := fun st => (γ st.2, γ st.1)
  have hγ : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hpair : Tendsto pair (𝓝 (s₀, s₀)) (𝓝 (γ s₀, γ s₀)) :=
    (hγ.comp continuous_snd).continuousAt.prodMk (hγ.comp continuous_fst).continuousAt
  have hmin := hpair.eventually (branch_minimizing_pair B)
  obtain ⟨A, hA, δ, hδ, hsource⟩ := branch_source_tube B
  have hbase : {st : ℝ × ℝ | γ st.2 ∈ A} ∈ 𝓝 (s₀, s₀) :=
    (hγ.comp continuous_snd).continuousAt hA
  have hcontsmall : Continuous fun st : ℝ × ℝ => |st.1 - st.2| * Real.sqrt (g.inner p v v) :=
    ((continuous_fst.sub continuous_snd).abs).mul continuous_const
  have hzero : |s₀ - s₀| * Real.sqrt (g.inner p v v) < δ := by
    simpa only [sub_self, abs_zero, zero_mul] using hδ
  have hsmall : {st : ℝ × ℝ | |st.1 - st.2| * Real.sqrt (g.inner p v v) < δ} ∈ 𝓝 (s₀, s₀) :=
    (isOpen_lt hcontsmall continuous_const).mem_nhds hzero
  filter_upwards [hmin, hbase, hsmall] with st hmin hbase hsmall
  let q := γ st.2
  let w : TangentSpace I q := (st.1 - st.2) • mfderiv 𝓘(ℝ, ℝ) I γ st.2 1
  have hwlen : Real.sqrt (g.inner q w w) = |st.1 - st.2| * Real.sqrt (g.inner p v v) := by
    have hspeed := intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p v st.2
    dsimp only [q, w]
    rw [gInner_smul_self, hspeed, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hwsource : (⟨q, w⟩ : TangentBundle I M) ∈ B.hom.source :=
    hsource q hbase w (by rwa [hwlen])
  have hwexp : expMapIntrinsic (I := I) g hEnorm q w = γ st.1 := by
    have hc := congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p v st.2) (st.1 - st.2)
    dsimp only [w]
    rw [expMapIntrinsic_def, intrinsicGeo_smul_apply (I := I) g hEnorm q _ _ 1, mul_one]
    refine hc.symm.trans ?_
    congr 1
    ring
  have hvec : minimizingVec (I := I) g hEnorm q (γ st.1) = w := by
    have hi := congrArg (fun z : TangentBundle I M => (z.snd : E)) (B.inv_eq_of_exp hwsource hwexp)
    exact hmin.2.1.symm.trans hi
  intro t
  rw [minJoin, hvec]
  dsimp only [w]
  rw [intrinsicGeo_smul_apply (I := I) g hEnorm q _ _ t]
  have hc := congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm p v st.2) ((st.1 - st.2) * t)
  refine hc.symm.trans ?_
  congr 1
  ring

theorem maxSliceLocus_minJoin
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C)
    {c : M} (B : DiagonalInverseBranch (I := I) g hEnorm c) :
    ∀ᶠ pq : M × M in 𝓝 (c, c), pq.1 ∈ maxSliceLocus I C → pq.2 ∈ maxSliceLocus I C →
      ∀ t ∈ Icc (0 : ℝ) 1, minJoin (I := I) g hEnorm pq.2 pq.1 t ∈ maxSliceLocus I C := by
  filter_upwards [maxSliceLocus_pair hEnorm hC B] with pq hpq h1 h2 t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · rw [← h, minJoin_zero]
    exact h2
  · exact hpq h1 (maxSliceLocus_subset h2) t ⟨h, ht.2⟩

theorem exists_isOpen_inter_eq_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) :
    ∃ O : Set M, IsOpen O ∧ C ∩ O = maxSliceLocus I C := by
  refine ⟨⋃₀ {U : Set M | IsOpen U ∧ U ∩ maxSliceLocus I C = U ∩ C},
    isOpen_sUnion fun U hU => hU.1, Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hxC, U, hU, hxU⟩
    have hx : x ∈ U ∩ maxSliceLocus I C := by
      rw [hU.2]
      exact ⟨hxU, hxC⟩
    exact hx.2
  · intro x hx
    obtain ⟨U, hU, hxU, hUeq⟩ := maxSliceLocus_eq_near hEnorm hC hx
    exact ⟨maxSliceLocus_subset hx, U, ⟨hU, hUeq⟩, hxU⟩


theorem isClosed_relBoundary
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C) :
    IsClosed (relBoundary I C) := by
  obtain ⟨O, hO, hOeq⟩ := exists_isOpen_inter_eq_maxSliceLocus hEnorm hC
  have heq : relBoundary I C = C ∩ Oᶜ := by
    ext x
    constructor
    · rintro ⟨hxC, hxN⟩
      refine ⟨hxC, fun hxO => hxN ?_⟩
      rw [← hOeq]
      exact ⟨hxC, hxO⟩
    · rintro ⟨hxC, hxO⟩
      refine ⟨hxC, fun hxN => hxO ?_⟩
      rw [← hOeq] at hxN
      exact hxN.2
  rw [heq]
  exact hCclosed.inter hO.isClosed_compl

theorem subset_closure_maxSliceLocus
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g)
    {C : Set M} (hC : IsTotallyConvex (I := I) g C) (hconn : IsPreconnected C) :
    C ⊆ closure (maxSliceLocus I C) := by
  rcases C.eq_empty_or_nonempty with rfl | hCne
  · exact empty_subset _
  have hlocal : ∀ c ∈ C, c ∈ closure (maxSliceLocus I C) →
      ∃ V : Set M, IsOpen V ∧ c ∈ V ∧ V ∩ C ⊆ closure (maxSliceLocus I C) := by
    intro c hcC hcK
    obtain ⟨V₁, V₂, hV₁, hcV₁, hV₂, hcV₂, hV⟩ := mem_nhds_prod_iff'.1
      (maxSliceLocus_pair (C := C) hEnorm hC (standardDiagonalInverseBranch (I := I) g hEnorm c))
    refine ⟨V₂, hV₂, hcV₂, ?_⟩
    rintro x ⟨hxV₂, hxC⟩
    obtain ⟨y, hyV₁, hyN⟩ := mem_closure_iff_nhds.1 hcK V₁ (hV₁.mem_nhds hcV₁)
    have hmem := hV (Set.mk_mem_prod hyV₁ hxV₂) hyN hxC
    have hlim : Tendsto (minJoin (I := I) g hEnorm x y) (𝓝[>] (0 : ℝ)) (𝓝 x) := by
      have hcont : Tendsto (minJoin (I := I) g hEnorm x y) (𝓝 (0 : ℝ))
          (𝓝 (minJoin (I := I) g hEnorm x y 0)) :=
        (minJoin_cont (I := I) g hEnorm x y).continuousAt
      rw [minJoin_zero] at hcont
      exact hcont.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto hlim ?_
    filter_upwards [mem_of_superset (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
      Ioo_subset_Ioc_self] with t ht
    exact hmem t ht
  have hWopen : IsOpen (⋃₀ {V : Set M | IsOpen V ∧ V ∩ C ⊆ closure (maxSliceLocus I C)}) :=
    isOpen_sUnion fun V hV => hV.1
  have hWC : (⋃₀ {V : Set M | IsOpen V ∧ V ∩ C ⊆ closure (maxSliceLocus I C)}) ∩ C ⊆
      closure (maxSliceLocus I C) := by
    rintro x ⟨⟨V, hV, hxV⟩, hxC⟩
    exact hV.2 ⟨hxV, hxC⟩
  have hKW : ∀ c ∈ C, c ∈ closure (maxSliceLocus I C) →
      c ∈ ⋃₀ {V : Set M | IsOpen V ∧ V ∩ C ⊆ closure (maxSliceLocus I C)} := by
    intro c hcC hcK
    obtain ⟨V, hV, hcV, hVsub⟩ := hlocal c hcC hcK
    exact ⟨V, ⟨hV, hVsub⟩, hcV⟩
  intro x hx
  by_contra hxK
  obtain ⟨z, hzN⟩ := maxSliceLocus_nonempty (I := I) hCne
  have hzC : z ∈ C := maxSliceLocus_subset hzN
  obtain ⟨y, hyC, hyW, hyK⟩ := hconn _ _ hWopen isClosed_closure.isOpen_compl
    (fun y hy => (em (y ∈ closure (maxSliceLocus I C))).imp (hKW y hy) id)
    ⟨z, hzC, hKW z hzC (subset_closure hzN)⟩ ⟨x, hx, hxK⟩
  exact hyK (hWC ⟨hyW, hyC⟩)

end DifferentialGeometry.Geometry.Topology
