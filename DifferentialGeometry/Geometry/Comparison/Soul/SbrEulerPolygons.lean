import DifferentialGeometry.Geometry.Comparison.Soul.SbrNearestStep
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

section Gluing

variable {X : Type*} [MetricSpace X]

private theorem lipschitzWith_of_ordered_dist
    (K : ℝ≥0) (f : ℝ → X)
    (h : ∀ s t : ℝ, s ≤ t → dist (f s) (f t) ≤ K * (t - s)) :
    LipschitzWith K f := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rcases le_total s t with hst | hts
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      using h s t hst
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts), dist_comm]
      using h t s hts

private theorem lipschitzWith_glue
    (K : ℝ≥0) {f g : ℝ → X} (hf : LipschitzWith K f) (hg : LipschitzWith K g)
    (c : ℝ) (hc : f c = g c) :
    LipschitzWith K (fun t => if t ≤ c then f t else g t) := by
  have hf' (s t : ℝ) (hst : s ≤ t) : dist (f s) (f t) ≤ K * (t - s) := by
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      using hf.dist_le_mul s t
  have hg' (s t : ℝ) (hst : s ≤ t) : dist (g s) (g t) ≤ K * (t - s) := by
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
      using hg.dist_le_mul s t
  apply lipschitzWith_of_ordered_dist
  intro s t hst
  by_cases ht : t ≤ c
  · simp only [if_pos (hst.trans ht), if_pos ht]
    exact hf' s t hst
  · by_cases hs : s ≤ c
    · simp only [if_pos hs, if_neg ht]
      calc
        dist (f s) (g t) ≤ dist (f s) (f c) + dist (f c) (g t) := dist_triangle _ _ _
        _ = dist (f s) (f c) + dist (g c) (g t) := by rw [hc]
        _ ≤ K * (c - s) + K * (t - c) :=
          add_le_add (hf' s c hs) (hg' c t (le_of_not_ge ht))
        _ = K * (t - s) := by ring
    · simp only [if_neg hs, if_neg ht]
      exact hg' s t hst

private theorem exists_glued_mesh_curve
    (K : ℝ≥0) (N : ℕ) (time : ℕ → ℝ) (htime : StrictMono time)
    (node : ℕ → X) (segment : ℕ → ℝ → X) (F : X → ℝ) (err : ℝ)
    (herr : 0 ≤ err) (hzero : F (node 0) = time 0)
    (hleft : ∀ i < N, segment i (time i) = node i)
    (hright : ∀ i < N, segment i (time (i + 1)) = node (i + 1))
    (hlip : ∀ i < N, LipschitzWith K (segment i))
    (hlevel : ∀ i < N, ∀ t ∈ Icc (time i) (time (i + 1)),
      t ≤ F (segment i t) ∧ F (segment i t) ≤ t + err) :
    ∃ curve : ℝ → X, LipschitzWith K curve ∧ curve (time 0) = node 0 ∧
      (∀ i ≤ N, curve (time i) = node i) ∧
      (∀ i < N, EqOn curve (segment i) (Icc (time i) (time (i + 1)))) ∧
      ∀ t ∈ Icc (time 0) (time N), t ≤ F (curve t) ∧ F (curve t) ≤ t + err := by
  classical
  let partialCurve : ℕ → ℝ → X := fun n =>
    Nat.rec (fun _ => node 0)
      (fun i previous t => if t ≤ time i then previous t else segment i t) n
  have hprefix : ∀ n ≤ N, LipschitzWith K (partialCurve n) ∧
      partialCurve n (time n) = node n ∧ partialCurve n (time 0) = node 0 ∧
      (∀ i < n, EqOn (partialCurve n) (segment i) (Icc (time i) (time (i + 1)))) ∧
      ∀ t ∈ Icc (time 0) (time n),
        t ≤ F (partialCurve n t) ∧ F (partialCurve n t) ≤ t + err := by
    intro n
    induction n with
    | zero =>
      intro _hN
      refine ⟨?_, rfl, rfl, ?_, ?_⟩
      · apply LipschitzWith.of_dist_le_mul
        intro s t
        change dist (node 0) (node 0) ≤ K * dist s t
        simpa only [dist_self] using mul_nonneg K.coe_nonneg (dist_nonneg : 0 ≤ dist s t)
      · intro i hi
        exact False.elim (Nat.not_lt_zero i hi)
      · intro t ht
        have heq : t = time 0 := le_antisymm ht.2 ht.1
        change t ≤ F (node 0) ∧ F (node 0) ≤ t + err
        rw [heq, hzero]
        exact ⟨le_rfl, le_add_of_nonneg_right herr⟩
    | succ n ih =>
      intro hn
      have hnlt : n < N := Nat.lt_of_succ_le hn
      obtain ⟨hLip, hend, hstart, hpieces, hlevels⟩ := ih (Nat.le_of_succ_le hn)
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · change LipschitzWith K (fun t => if t ≤ time n then partialCurve n t else segment n t)
        exact lipschitzWith_glue K hLip (hlip n hnlt) (time n)
          (hend.trans (hleft n hnlt).symm)
      · change (if time (n + 1) ≤ time n then partialCurve n (time (n + 1))
          else segment n (time (n + 1))) = node (n + 1)
        rw [if_neg (not_le.mpr (htime (Nat.lt_succ_self n))), hright n hnlt]
      · change (if time 0 ≤ time n then partialCurve n (time 0) else segment n (time 0)) = node 0
        rw [if_pos (htime.monotone (Nat.zero_le n)), hstart]
      · intro i hi t ht
        by_cases hin : i < n
        · change (if t ≤ time n then partialCurve n t else segment n t) = segment i t
          rw [if_pos (ht.2.trans (htime.monotone (Nat.succ_le_of_lt hin)))]
          exact hpieces i hin ht
        · have heq : i = n := by omega
          subst i
          change (if t ≤ time n then partialCurve n t else segment n t) = segment n t
          by_cases htleft : t ≤ time n
          · have heq : t = time n := le_antisymm htleft ht.1
            rw [heq, if_pos le_rfl, hend, hleft n hnlt]
          · rw [if_neg htleft]
      · intro t ht
        change t ≤ F (if t ≤ time n then partialCurve n t else segment n t) ∧
          F (if t ≤ time n then partialCurve n t else segment n t) ≤ t + err
        by_cases htn : t ≤ time n
        · simp only [if_pos htn]
          exact hlevels t ⟨ht.1, htn⟩
        · simp only [if_neg htn]
          exact hlevel n hnlt t ⟨le_of_not_ge htn, ht.2⟩
  obtain ⟨hLip, hend, hstart, hpieces, hlevels⟩ := hprefix N le_rfl
  refine ⟨partialCurve N, hLip, hstart, ?_, hpieces, hlevels⟩
  intro i hi
  rcases eq_or_lt_of_le hi with rfl | hi
  · exact hend
  · exact (hpieces i hi ⟨le_rfl, htime.monotone (Nat.le_succ i)⟩).trans (hleft i hi)

end Gluing

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem lipschitzWith_intrinsicGeodesic_of_speed_le
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (p : M) (v : TangentSpace I p) (K : ℝ≥0)
    (hK : Real.sqrt (g.inner p v v) ≤ K) :
    LipschitzWith K (intrinsicGeodesic g hEnorm p v) := by
  apply lipschitzWith_of_ordered_dist
  intro s t hst
  have h := intrinsicGeodesic_riemannianEDist_le g hEnorm p v hst
  rw [← IsRiemannianManifold.out (I := I), edist_dist] at h
  have hd := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hst))).mp h
  exact hd.trans (mul_le_mul_of_nonneg_right hK (sub_nonneg.mpr hst))

theorem exists_nearest_superlevel_euler_polygon
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a T m : ℝ} (ha : 0 ≤ a) (haT : a < T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (N : ℕ) (hN : 0 < N) (x : M) (hx : F x = a) :
    let mesh : ℝ := (T - a) / (N : ℝ)
    let time : ℕ → ℝ := fun i => a + (i : ℝ) * mesh
    let K : ℝ≥0 := Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))
    ∃ (node : ℕ → M) (v : (i : ℕ) → TangentSpace I (node i)) (curve : ℝ → M),
      node 0 = x ∧
      (∀ i ≤ N, F (node i) = time i) ∧
      (∀ i ≤ N, node i ∈ {z : M | 0 ≤ F z}) ∧
      (∀ i < N, IsMinOn (dist (node i)) {z : M | time (i + 1) ≤ F z} (node (i + 1)) ∧
        dist (node i) (node (i + 1)) ≤ K * mesh) ∧
      (∀ i < N, intrinsicGeodesic g hEnorm (node i) (v i) 1 = node (i + 1) ∧
        Real.sqrt (g.inner (node i) (v i) (v i)) = dist (node i) (node (i + 1))) ∧
      LipschitzWith K curve ∧ curve a = x ∧
      (∀ i ≤ N, curve (time i) = node i) ∧
      (∀ i < N, EqOn curve
        (fun t => intrinsicGeodesic g hEnorm (node i) (v i) ((t - time i) / mesh))
        (Icc (time i) (time (i + 1)))) ∧
      MapsTo curve (Icc a T) {z : M | 0 ≤ F z} ∧
      ∀ t ∈ Icc a T, t ≤ F (curve t) ∧ F (curve t) ≤ t + (L : ℝ) * K * mesh := by
  classical
  dsimp only
  let mesh : ℝ := (T - a) / (N : ℝ)
  let time : ℕ → ℝ := fun i => a + (i : ℝ) * mesh
  let K : ℝ≥0 := Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmesh : 0 < mesh := div_pos (sub_pos.mpr haT) hNreal
  have hK : (K : ℝ) = Metric.diam {z : M | 0 ≤ F z} / (m - T) :=
    Real.coe_toNNReal _ (div_nonneg Metric.diam_nonneg (sub_pos.mpr hTm).le)
  have htime : StrictMono time := by
    intro i j hij
    simpa only [time, add_comm] using
      add_lt_add_left (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hij) hmesh) a
  have htime0 : time 0 = a := by simp only [time, Nat.cast_zero, zero_mul, add_zero]
  have htimeN : time N = T := by
    dsimp only [time, mesh]
    field_simp [hNreal.ne']
    ring
  have hstep (i : ℕ) : time (i + 1) - time i = mesh := by
    simp only [time, Nat.cast_add, Nat.cast_one]
    ring
  have htime_nonneg (i : ℕ) : 0 ≤ time i := by
    rw [← htime0] at ha
    exact ha.trans (htime.monotone (Nat.zero_le i))
  have hnext : ∀ i < N, ∀ p : M, F p = time i →
      ∃ q : M, F q = time (i + 1) ∧
        IsMinOn (dist p) {z : M | time (i + 1) ≤ F z} q ∧
        dist p q ≤ K * mesh := by
    intro i hi p hp
    have hiT : time (i + 1) ≤ T := by
      rw [← htimeN]
      exact htime.monotone (Nat.succ_le_of_lt hi)
    obtain ⟨q, hq, hmin, hdist⟩ := exists_nearest_superlevel_step g hEnorm F
      hF.continuous hconc hC (htime_nonneg i) (htime (Nat.lt_succ_self i))
      hiT hTm hmax p hp
    refine ⟨q, hq, hmin, ?_⟩
    simpa only [hstep, hK] using hdist
  let nextNode (i : ℕ) (p : M) : M :=
    if hi : i < N then
      if hp : F p = time i then (hnext i hi p hp).choose else p
    else p
  let node : ℕ → M := Nat.rec x (fun i p => nextNode i p)
  have hnode0 : node 0 = x := rfl
  have hnode_succ (i : ℕ) : node (i + 1) = nextNode i (node i) := rfl
  have hnodelevel : ∀ i ≤ N, F (node i) = time i := by
    intro i
    induction i with
    | zero =>
      intro _hi
      simpa only [hnode0, htime0] using hx
    | succ i ih =>
      intro hi
      have hiN : i < N := Nat.lt_of_succ_le hi
      have hp := ih (Nat.le_of_succ_le hi)
      rw [hnode_succ]
      dsimp only [nextNode]
      rw [dif_pos hiN, dif_pos hp]
      exact (hnext i hiN (node i) hp).choose_spec.1
  have hnodeC : ∀ i ≤ N, node i ∈ {z : M | 0 ≤ F z} := by
    intro i hi
    change 0 ≤ F (node i)
    rw [hnodelevel i hi]
    exact htime_nonneg i
  have hnodestep : ∀ i < N,
      IsMinOn (dist (node i)) {z : M | time (i + 1) ≤ F z} (node (i + 1)) ∧
        dist (node i) (node (i + 1)) ≤ K * mesh := by
    intro i hi
    have hp := hnodelevel i hi.le
    rw [hnode_succ]
    dsimp only [nextNode]
    rw [dif_pos hi, dif_pos hp]
    exact (hnext i hi (node i) hp).choose_spec.2
  have hminseg (i : ℕ) : ∃ v : TangentSpace I (node i),
      intrinsicGeodesic g hEnorm (node i) v 1 = node (i + 1) ∧
        Real.sqrt (g.inner (node i) v v) = dist (node i) (node (i + 1)) := by
    obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm (node i) (node (i + 1)) (by
      rw [← IsRiemannianManifold.out (I := I)]
      exact edist_ne_top _ _)
    rw [← IsRiemannianManifold.out (I := I), edist_dist,
      ENNReal.toReal_ofReal dist_nonneg] at hlen
    exact ⟨v, hv, hlen⟩
  choose v hvend hvspeed using hminseg
  let segment (i : ℕ) (t : ℝ) : M :=
    intrinsicGeodesic g hEnorm (node i) (v i) ((t - time i) / mesh)
  have hleft (i : ℕ) : segment i (time i) = node i := by
    simp only [segment, sub_self, zero_div, intrinsicGeodesic_zero]
  have hright (i : ℕ) : segment i (time (i + 1)) = node (i + 1) := by
    simp only [segment, hstep, div_self hmesh.ne', hvend]
  have hseglip : ∀ i < N, LipschitzWith K (segment i) := by
    intro i hi
    let speed : ℝ≥0 := Real.toNNReal (dist (node i) (node (i + 1)))
    have hspeed : (speed : ℝ) = dist (node i) (node (i + 1)) :=
      Real.coe_toNNReal _ dist_nonneg
    have hLip := lipschitzWith_intrinsicGeodesic_of_speed_le g hEnorm
      (node i) (v i) speed (by rw [hvspeed, hspeed])
    apply lipschitzWith_of_ordered_dist
    intro s t hst
    have hparam : (s - time i) / mesh ≤ (t - time i) / mesh :=
      div_le_div_of_nonneg_right (sub_le_sub_right hst _) hmesh.le
    have hd : dist (segment i s) (segment i t) ≤
        dist (node i) (node (i + 1)) * ((t - time i) / mesh - (s - time i) / mesh) := by
      simpa only [segment, hspeed, Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr hparam), neg_sub] using
        hLip.dist_le_mul ((s - time i) / mesh) ((t - time i) / mesh)
    refine hd.trans ((mul_le_mul_of_nonneg_right (hnodestep i hi).2
      (sub_nonneg.mpr hparam)).trans_eq ?_)
    field_simp
    ring
  let err : ℝ := (L : ℝ) * K * mesh
  have herr : 0 ≤ err := mul_nonneg (mul_nonneg L.coe_nonneg K.coe_nonneg) hmesh.le
  have hseglevel : ∀ i < N, ∀ t ∈ Icc (time i) (time (i + 1)),
      t ≤ F (segment i t) ∧ F (segment i t) ≤ t + err := by
    intro i hi t ht
    let theta : ℝ := (t - time i) / mesh
    have htheta : 0 ≤ theta := div_nonneg (sub_nonneg.mpr ht.1) hmesh.le
    have hthetaone : theta ≤ 1 := (div_le_one₀ hmesh).mpr (by
      have hs := hstep i
      linarith [ht.2])
    have hconctheta := (hconc (node i) (v i)).2
      (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
      (sub_nonneg.mpr hthetaone) htheta (by ring : (1 - theta) + theta = 1)
    simp only [smul_eq_mul, mul_zero, mul_one, zero_add, intrinsicGeodesic_zero,
      hvend, hnodelevel i hi.le, hnodelevel (i + 1) (Nat.succ_le_of_lt hi)] at hconctheta
    have hcomb : (1 - theta) * time i + theta * time (i + 1) = t := by
      calc
        (1 - theta) * time i + theta * time (i + 1) =
            time i + theta * (time (i + 1) - time i) := by ring
        _ = time i + (t - time i) := by
          rw [hstep]
          dsimp only [theta]
          rw [div_mul_cancel₀ _ hmesh.ne']
        _ = t := by ring
    have hlower : t ≤ F (segment i t) := by
      rw [hcomb] at hconctheta
      exact hconctheta
    have hsegdist : dist (segment i t) (node i) ≤ K * mesh := by
      have hd := (hseglip i hi).dist_le_mul t (time i)
      rw [hleft, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hd
      refine hd.trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
      have hs := hstep i
      linarith [ht.2]
    have hvalue := hF.dist_le_mul (segment i t) (node i)
    rw [Real.dist_eq, hnodelevel i hi.le] at hvalue
    have hupper : F (segment i t) - time i ≤ err :=
      (le_abs_self _).trans (hvalue.trans (by
        dsimp only [err]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsegdist L.coe_nonneg))
    exact ⟨hlower, by linarith [ht.1]⟩
  obtain ⟨curve, hcurveLip, hcurve0, hnodes, hpieces, hlevels⟩ :=
    exists_glued_mesh_curve K N time htime node segment F err herr
      (hnodelevel 0 (Nat.zero_le N)) (fun i _hi => hleft i) (fun i _hi => hright i)
      hseglip hseglevel
  have hstart : curve a = x := by simpa only [htime0, hnode0] using hcurve0
  have hlevels' : ∀ t ∈ Icc a T,
      t ≤ F (curve t) ∧ F (curve t) ≤ t + (L : ℝ) * K * mesh := by
    simpa only [htime0, htimeN] using hlevels
  refine ⟨node, v, curve, hnode0, hnodelevel, hnodeC, hnodestep,
    (fun i _hi => ⟨hvend i, hvspeed i⟩), hcurveLip, hstart, hnodes, hpieces, ?_, hlevels'⟩
  intro t ht
  exact (ha.trans ht.1).trans (hlevels' t ht).1

end DifferentialGeometry.Geometry.Topology

end
