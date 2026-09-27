import DifferentialGeometry.Geometry.Comparison.Soul.SbrEulerLimit
import DifferentialGeometry.Geometry.Comparison.Soul.SbrLocalStep
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal BigOperators
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

private theorem floor_mesh_index
    (a t mesh : ℝ) (hmesh : 0 < mesh) (N : ℕ)
    (hat : a ≤ t) (htN : t ≤ a + (N : ℝ) * mesh) :
    let i : ℕ := ⌊(t - a) / mesh⌋₊
    i ≤ N ∧ a + (i : ℝ) * mesh ≤ t ∧ t < a + (i : ℝ) * mesh + mesh := by
  dsimp only
  refine ⟨Nat.floor_le_of_le ((div_le_iff₀ hmesh).mpr (by linarith)), ?_, ?_⟩
  · have h := (le_div_iff₀ hmesh).mp
      (Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hmesh.le))
    linarith
  · have h := (div_lt_iff₀ hmesh).mp (Nat.lt_floor_add_one ((t - a) / mesh))
    nlinarith

section Metric

variable {X : Type*} [MetricSpace X]

private theorem local_speed_of_nearest_mesh_limit
    (F : X → ℝ) {a T : ℝ} (haT : a < T)
    (N : ℕ → ℕ) (hN : ∀ n, 0 < N n) (K : ℝ≥0)
    (node : ℕ → ℕ → X) (polygon : ℕ → ℝ → X) (eta : ℝ → X)
    (hmesh : Tendsto (fun n => (T - a) / (N n : ℝ)) atTop (𝓝 0))
    (hlevel : ∀ n i, i ≤ N n → F (node n i) = a + (i : ℝ) * ((T - a) / (N n : ℝ)))
    (hnearest : ∀ n i, i < N n →
      IsMinOn (dist (node n i))
        {z : X | a + ((i + 1 : ℕ) : ℝ) * ((T - a) / (N n : ℝ)) ≤ F z}
        (node n (i + 1)))
    (hpolyLip : ∀ n, LipschitzWith K (polygon n))
    (hpolyNode : ∀ n i, i ≤ N n →
      polygon n (a + (i : ℝ) * ((T - a) / (N n : ℝ))) = node n i)
    (hconv : TendstoUniformlyOn polygon eta atTop (Icc a T))
    {s : ℝ} (hs : s ∈ Icc a T) {a0 : ℝ} (ha0 : 0 < a0)
    (U : Set X) (hU : IsOpen U) (hp : eta s ∈ U)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hlocal : ∀ q ∈ U, ∀ tau : ℝ, 0 < tau → tau < epsilon →
      ∃ y : X, F q + tau ≤ F y ∧ dist q y ≤ tau / a0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, 0 < h → h < delta → s + h ≤ T →
      dist (eta (s + h)) (eta s) ≤ h / a0 := by
  let mesh : ℕ → ℝ := fun n => (T - a) / (N n : ℝ)
  let time : ℕ → ℕ → ℝ := fun n i => a + (i : ℝ) * mesh n
  have hmeshpos (n : ℕ) : 0 < mesh n :=
    div_pos (sub_pos.mpr haT) (Nat.cast_pos.mpr (hN n))
  have htimeN (n : ℕ) : time n (N n) = T := by
    dsimp only [time, mesh]
    have hn : (N n : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hN n) : (0 : ℝ) < N n).ne'
    field_simp [hn]
    ring
  have htimeMono (n : ℕ) : Monotone (time n) := by
    intro i j hij
    simpa only [time, add_comm] using add_le_add_left
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (hmeshpos n).le) a
  have htimeStep (n i : ℕ) : time n (i + 1) = time n i + mesh n := by
    simp only [time, Nat.cast_add, Nat.cast_one]
    ring
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hU (eta s) hp
  let delta : ℝ := rho / (4 * (K : ℝ) + 4)
  have hdenom : 0 < 4 * (K : ℝ) + 4 := by positivity
  have hdelta : 0 < delta := div_pos hrho hdenom
  have hdeltaeq : delta * (4 * (K : ℝ) + 4) = rho := div_mul_cancel₀ _ hdenom.ne'
  refine ⟨delta, hdelta, ?_⟩
  intro h hh hhdelta hshT
  have hsh : s + h ∈ Icc a T := ⟨hs.1.trans (by linarith), hshT⟩
  have hsmallmesh : ∀ᶠ n in atTop, mesh n < delta :=
    hmesh.eventually (gt_mem_nhds hdelta)
  have hlocalmesh : ∀ᶠ n in atTop, mesh n < epsilon :=
    hmesh.eventually (gt_mem_nhds hepsilon)
  have hclose : ∀ᶠ n in atTop, dist (polygon n s) (eta s) < rho / 2 :=
    (hconv.tendsto_at hs).eventually (Metric.ball_mem_nhds (eta s) (half_pos hrho))
  have hbound : ∀ᶠ n in atTop,
      dist (polygon n (s + h)) (polygon n s) ≤
        h / a0 + (2 * (K : ℝ) + 1 / a0) * mesh n := by
    filter_upwards [hsmallmesh, hlocalmesh, hclose] with n hnDelta hnEpsilon hnClose
    let i : ℕ := ⌊(s - a) / mesh n⌋₊
    let j : ℕ := ⌊(s + h - a) / mesh n⌋₊
    have hi : i ≤ N n ∧ time n i ≤ s ∧ s < time n i + mesh n :=
      floor_mesh_index a s (mesh n) (hmeshpos n) (N n) hs.1 (by
        change s ≤ time n (N n)
        rw [htimeN]
        exact hs.2)
    have hj : j ≤ N n ∧ time n j ≤ s + h ∧ s + h < time n j + mesh n :=
      floor_mesh_index a (s + h) (mesh n) (hmeshpos n) (N n) hsh.1 (by
        change s + h ≤ time n (N n)
        rw [htimeN]
        exact hsh.2)
    have hij : i ≤ j := Nat.floor_mono
      (div_le_div_of_nonneg_right (by linarith : s - a ≤ s + h - a) (hmeshpos n).le)
    have hnodeU : ∀ k, i ≤ k → k < j → node n k ∈ U := by
      intro k hik hkj
      have hkN : k ≤ N n := hkj.le.trans hj.1
      have hlow := htimeMono n hik
      have hupp := htimeMono n hkj.le
      have htdist : dist (time n k) s < delta := by
        rw [Real.dist_eq]
        apply abs_lt.mpr
        constructor <;> linarith [hi.2.2, hj.2.1]
      apply hball
      change dist (node n k) (eta s) < rho
      rw [← hpolyNode n k hkN]
      change dist (polygon n (time n k)) (eta s) < rho
      calc
        dist (polygon n (time n k)) (eta s) ≤
            dist (polygon n (time n k)) (polygon n s) + dist (polygon n s) (eta s) :=
          dist_triangle _ _ _
        _ ≤ K * dist (time n k) s + dist (polygon n s) (eta s) :=
          add_le_add ((hpolyLip n).dist_le_mul _ _) le_rfl
        _ < K * delta + rho / 2 :=
          add_lt_add_of_le_of_lt
            (mul_le_mul_of_nonneg_left htdist.le K.coe_nonneg) hnClose
        _ < rho := by nlinarith [mul_nonneg K.coe_nonneg hdelta.le]
    have hedge : ∀ k, i ≤ k → k < j →
        dist (node n k) (node n (k + 1)) ≤ mesh n / a0 := by
      intro k hik hkj
      have hkN : k < N n := hkj.trans_le hj.1
      obtain ⟨y, hy, hdist⟩ := hlocal (node n k) (hnodeU k hik hkj)
        (mesh n) (hmeshpos n) hnEpsilon
      have hyLevel : time n (k + 1) ≤ F y := by
        rw [htimeStep]
        change a + (k : ℝ) * ((T - a) / (N n : ℝ)) + mesh n ≤ F y
        rwa [hlevel n k hkN.le] at hy
      exact ((isMinOn_iff.mp (hnearest n k hkN)) y hyLevel).trans hdist
    have hnodesDist : dist (node n i) (node n j) ≤ (time n j - time n i) / a0 := by
      calc
        dist (node n i) (node n j) ≤
            ∑ k ∈ Finset.Ico i j, mesh n / a0 :=
          dist_le_Ico_sum_of_dist_le hij (fun {k} hik hkj => hedge k hik hkj)
        _ = ((j - i : ℕ) : ℝ) * (mesh n / a0) := by
          simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        _ = (time n j - time n i) / a0 := by
          rw [Nat.cast_sub hij]
          dsimp only [time]
          ring
    have hstartDist : dist (node n i) (polygon n s) ≤ K * mesh n := by
      rw [← hpolyNode n i hi.1]
      have hd := (hpolyLip n).dist_le_mul (time n i) s
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hi.2.1), neg_sub] at hd
      exact hd.trans (mul_le_mul_of_nonneg_left (by linarith [hi.2.2]) K.coe_nonneg)
    have hendDist : dist (polygon n (s + h)) (node n j) ≤ K * mesh n := by
      rw [← hpolyNode n j hj.1]
      have hd := (hpolyLip n).dist_le_mul (s + h) (time n j)
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hj.2.1)] at hd
      exact hd.trans (mul_le_mul_of_nonneg_left (by linarith [hj.2.2]) K.coe_nonneg)
    have hspan : time n j - time n i ≤ h + mesh n := by linarith [hi.2.2, hj.2.1]
    calc
      dist (polygon n (s + h)) (polygon n s) ≤
          dist (polygon n (s + h)) (node n j) + dist (node n j) (polygon n s) :=
        dist_triangle _ _ _
      _ ≤ dist (polygon n (s + h)) (node n j) +
          (dist (node n j) (node n i) + dist (node n i) (polygon n s)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ ≤ K * mesh n + ((time n j - time n i) / a0 + K * mesh n) :=
        add_le_add hendDist (add_le_add (by simpa only [dist_comm] using hnodesDist) hstartDist)
      _ ≤ K * mesh n + ((h + mesh n) / a0 + K * mesh n) :=
        add_le_add le_rfl
          (add_le_add (div_le_div_of_nonneg_right hspan ha0.le) le_rfl)
      _ = h / a0 + (2 * (K : ℝ) + 1 / a0) * mesh n := by ring
  have herror : Tendsto (fun n => (2 * (K : ℝ) + 1 / a0) * mesh n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hmesh.const_mul (2 * (K : ℝ) + 1 / a0)
  have hupper : Tendsto (fun n => h / a0 + (2 * (K : ℝ) + 1 / a0) * mesh n)
      atTop (𝓝 (h / a0)) := by
    simpa only [add_zero] using herror.const_add (h / a0)
  exact le_of_tendsto_of_tendsto
    ((hconv.tendsto_at hsh).dist (hconv.tendsto_at hs)) hupper hbound

end Metric

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

theorem exists_nearest_superlevel_limit_with_local_speed
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a T m : ℝ} (ha : 0 ≤ a) (haT : a < T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = a) :
    ∃ eta : ℝ → M,
      LipschitzWith (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))) eta ∧
      eta a = x ∧ MapsTo eta (Icc a T) {z : M | 0 ≤ F z} ∧
      (∀ t ∈ Icc a T, F (eta t) = t) ∧
      ∀ s ∈ Ico a T, ∀ v : TangentSpace I (eta s), g.inner (eta s) v v = 1 →
        ∀ a0 : ℝ, 0 < a0 → a0 < intrinsicRightDerivative g hEnorm F (eta s) v →
          ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, 0 < h → h < delta → s + h ≤ T →
            dist (eta (s + h)) (eta s) ≤ h / a0 := by
  obtain ⟨node, _v, polygon, phi, eta, hpolygons, _hphi, hmesh, hconv,
    hetaLip, hetaStart, hetaMaps, hetaLevel⟩ :=
    exists_nearest_superlevel_euler_limit g hEnorm F L hF hconc hC ha haT hTm hmax x hx
  refine ⟨eta, hetaLip, hetaStart, hetaMaps, hetaLevel, ?_⟩
  intro s hs w hw a0 ha0 hder
  obtain ⟨U, hU, hp, epsilon, hepsilon, hlocal⟩ :=
    exists_local_superlevel_step_of_positive_direction g hEnorm hF.continuous hconc
      (eta s) w hw ha0 hder
  apply local_speed_of_nearest_mesh_limit F haT (fun n => phi n + 1)
    (fun n => Nat.succ_pos (phi n))
    (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T)))
    (fun n => node (phi n)) (fun n => polygon (phi n)) eta hmesh
    ?_ ?_ ?_ ?_ hconv ⟨hs.1, hs.2.le⟩ ha0 U hU hp epsilon hepsilon hlocal
  · intro n i hi
    obtain ⟨_h0, hlevels, _hC, _hsteps, _hmin, _hLip, _hstart, _hnodes, _hpieces,
      _hmaps, _hvalues⟩ := hpolygons (phi n)
    exact hlevels i hi
  · intro n i hi
    obtain ⟨_h0, _hlevels, _hC, hsteps, _hmin, _hLip, _hstart, _hnodes, _hpieces,
      _hmaps, _hvalues⟩ := hpolygons (phi n)
    exact (hsteps i hi).1
  · intro n
    obtain ⟨_h0, _hlevels, _hC, _hsteps, _hmin, hLip, _hstart, _hnodes, _hpieces,
      _hmaps, _hvalues⟩ := hpolygons (phi n)
    exact hLip
  · intro n i hi
    obtain ⟨_h0, _hlevels, _hC, _hsteps, _hmin, _hLip, _hstart, hnodes, _hpieces,
      _hmaps, _hvalues⟩ := hpolygons (phi n)
    exact hnodes i hi

end DifferentialGeometry.Geometry.Topology

end
