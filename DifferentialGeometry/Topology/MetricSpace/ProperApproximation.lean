import DifferentialGeometry.Topology.Compactness.ImageConvergence
import DifferentialGeometry.Topology.MetricSpace.DenseExtension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

open Filter Set
open scoped Topology

namespace Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

private theorem tendsto_dist_of_distortion
    (F : ℕ → X → Y) (o : X)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (F n x) (F n y) - dist x y| < ε) (x y : X) :
    Tendsto (fun n => dist (F n x) (F n y)) atTop (𝓝 (dist x y)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hdist (max (dist x o) (dist y o)) ε hε] with n hn
  simpa only [Real.dist_eq] using
    hn x (mem_closedBall.mpr (le_max_left _ _)) y (mem_closedBall.mpr (le_max_right _ _))

private theorem exists_dense_pointwise_subsequence [ProperSpace Y]
    (F : ℕ → X → Y) (o : X) (a : ℕ → X) (q : Y)
    (hbase : Tendsto (fun n => F n o) atTop (𝓝 q))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (F n x) (F n y) - dist x y| < ε) :
    ∃ (k : ℕ → ℕ) (z : ℕ → Y), StrictMono k ∧
      ∀ j, Tendsto (fun n => F (k n) (a j)) atTop (𝓝 (z j)) := by
  have hb (j : ℕ) : ∃ R : ℝ, ∀ n, F n (a j) ∈ closedBall q R := by
    let d : ℕ → ℝ := fun n => dist (F n (a j)) (F n o) + dist (F n o) q
    have hd : Tendsto d atTop (𝓝 (dist (a j) o)) := by
      simpa only [d, dist_self, add_zero] using
        (tendsto_dist_of_distortion F o hdist (a j) o).add
          (hbase.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => q) atTop (𝓝 q)))
    obtain ⟨R, hR⟩ := (isBounded_range_of_tendsto d hd).subset_closedBall (0 : ℝ)
    refine ⟨R, fun n => ?_⟩
    have hn : |d n| ≤ R := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hR (mem_range_self n)
    exact (dist_triangle (F n (a j)) (F n o) q).trans ((le_abs_self (d n)).trans hn)
  choose R hR using hb
  let K : Set (ℕ → Y) := {z | ∀ j, z j ∈ closedBall q (R j)}
  have hK : IsCompact K := isCompact_pi_infinite fun j => isCompact_closedBall q (R j)
  obtain ⟨z, _, k, hk, hlim⟩ :=
    hK.tendsto_subseq (x := fun n j => F n (a j)) (fun n j => hR j n)
  refine ⟨k, z, hk, fun j => ?_⟩
  exact ((continuous_apply j).tendsto z).comp hlim

private theorem exists_isometry_of_dense_dist_limit [CompleteSpace Y]
    (F : ℕ → X → Y) (o : X) (a : ℕ → X) (ha : DenseRange a) (z : ℕ → Y)
    (hlim : ∀ j, Tendsto (fun n => F n (a j)) atTop (𝓝 (z j)))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (F n x) (F n y) - dist x y| < ε) :
    ∃ f : X → Y, Isometry f ∧ ∀ j, f (a j) = z j := by
  have hz (i j : ℕ) : dist (z i) (z j) = dist (a i) (a j) :=
    tendsto_nhds_unique ((hlim i).dist (hlim j))
      (tendsto_dist_of_distortion F o hdist (a i) (a j))
  obtain ⟨f, hf, heq⟩ := ha.exists_lipschitz_extension z (K := 1) (fun i j => by
    simp only [ENNReal.coe_one, one_mul, edist_dist, hz i j, le_refl])
  refine ⟨f, Isometry.of_dist_eq ?_, heq⟩
  intro x y
  exact ha.induction_on₂
    (p := fun x y => dist (f x) (f y) = dist x y)
    (isClosed_eq (hf.continuous.comp continuous_fst |>.dist
      (hf.continuous.comp continuous_snd)) continuous_dist)
    (fun i j => by rw [heq, heq, hz]) x y

private theorem tendstoUniformlyOn_of_dense_dist_limit
    (F : ℕ → X → Y) (o : X) (a : ℕ → X) (ha : DenseRange a)
    (f : X → Y) (hf : Isometry f)
    (hlim : ∀ j, Tendsto (fun n => F n (a j)) atTop (𝓝 (f (a j))))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (F n x) (F n y) - dist x y| < ε)
    {K : Set X} (hK : IsCompact K) : TendstoUniformlyOn F f atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hε4 : 0 < ε / 4 := by linarith
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun j => ball (a j) (ε / 4))
    (fun _ => isOpen_ball) (by
      intro x _
      obtain ⟨j, hj⟩ := ha.exists_dist_lt x hε4
      exact mem_iUnion.mpr ⟨j, by simpa only [mem_ball, dist_comm] using hj⟩)
  obtain ⟨R, hR⟩ := (hK.isBounded.union (s.finite_toSet.image a).isBounded).subset_closedBall o
  have hcenters : ∀ᶠ n in atTop, ∀ j ∈ s, dist (f (a j)) (F n (a j)) < ε / 4 := by
    apply (Filter.eventually_all_finset s).mpr
    intro j _
    simpa only [mem_ball, dist_comm] using
      (hlim j).eventually (Metric.ball_mem_nhds _ hε4)
  filter_upwards [hdist R (ε / 4) hε4, hcenters] with n hn hcn x hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hs hx)
  have hsmall : dist x (a j) < ε / 4 := hxj
  have hdistxy := hn x (hR (Or.inl hx)) (a j) (hR (Or.inr ⟨j, hj, rfl⟩))
  have hdistupper := (abs_lt.mp hdistxy).2
  have htriangle := dist_triangle4 (f x) (f (a j)) (F n (a j)) (F n x)
  rw [hf.dist_eq, dist_comm (F n (a j)) (F n x)] at htriangle
  have hcenter := hcn j hj
  linarith

theorem exists_isometryEquiv_subsequence_of_distortion [ProperSpace X] [ProperSpace Y]
    (F : ℕ → X → Y) (o : X)
    (hbase : ∃ K : Set Y, IsCompact K ∧ ∃ᶠ n in atTop, F n o ∈ K)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (F n x) (F n y) - dist x y| < ε)
    (hcapture : ∀ R : ℝ, 0 < R → ∃ S : ℝ, ∀ᶠ n in atTop,
      ball (F n o) R ⊆ F n '' closedBall o S) :
    ∃ (k : ℕ → ℕ) (e : X ≃ᵢ Y), StrictMono k ∧
      ∀ K : Set X, IsCompact K →
        TendstoUniformlyOn (fun n => F (k n)) (e : X → Y) atTop K := by
  classical
  let : Nonempty X := ⟨o⟩
  obtain ⟨K, hK, hFK⟩ := hbase
  obtain ⟨q, _, k₀, hk₀, hq⟩ := hK.tendsto_subseq' hFK
  let H : ℕ → X → Y := fun n => F (k₀ n)
  have hHbase : Tendsto (fun n => H n o) atTop (𝓝 q) := hq
  have hHdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (H n x) (H n y) - dist x y| < ε := by
    intro R ε hε
    exact hk₀.tendsto_atTop.eventually (hdist R ε hε)
  obtain ⟨a, ha⟩ := TopologicalSpace.exists_dense_seq X
  obtain ⟨k₁, z, hk₁, hz⟩ := exists_dense_pointwise_subsequence H o a q hHbase hHdist
  let k : ℕ → ℕ := k₀ ∘ k₁
  have hk : StrictMono k := hk₀.comp hk₁
  let G : ℕ → X → Y := fun n => F (k n)
  have hGdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x ∈ closedBall o R, ∀ y ∈ closedBall o R,
        |dist (G n x) (G n y) - dist x y| < ε := by
    intro R ε hε
    exact hk.tendsto_atTop.eventually (hdist R ε hε)
  have hGlim : ∀ j, Tendsto (fun n => G n (a j)) atTop (𝓝 (z j)) := hz
  obtain ⟨f, hf, hfz⟩ := exists_isometry_of_dense_dist_limit G o a ha z hGlim hGdist
  have hconv : ∀ K : Set X, IsCompact K → TendstoUniformlyOn G f atTop K := by
    intro K hK
    apply tendstoUniformlyOn_of_dense_dist_limit G o a ha f hf
    · intro j
      rw [hfz]
      exact hGlim j
    · exact hGdist
    · exact hK
  have hbaseconv : Tendsto (fun n => G n o) atTop (𝓝 (f o)) :=
    (hconv {o} isCompact_singleton).tendsto_at (mem_singleton o)
  have hsurj : Function.Surjective f := by
    apply surjective_of_tendstoUniformlyOn_of_compact_preimages hf.continuous hconv
    intro y
    let R : ℝ := dist y (f o) + 1
    have hR : 0 < R := by dsimp [R]; positivity
    obtain ⟨S, hS⟩ := hcapture R hR
    have hc : ∀ᶠ n in atTop, ball (G n o) R ⊆ G n '' closedBall o S :=
      hk.tendsto_atTop.eventually hS
    have hy : ∀ᶠ n in atTop, y ∈ ball (G n o) R := by
      have hlim : Tendsto (fun n => dist y (G n o)) atTop (𝓝 (dist y (f o))) :=
        tendsto_const_nhds.dist hbaseconv
      exact hlim.eventually_lt_const (lt_add_one _)
    refine ⟨closedBall o S, isCompact_closedBall o S, ?_⟩
    exact (hc.and hy).frequently.mono fun _ hn => hn.1 hn.2
  let e : X ≃ᵢ Y :=
    { toEquiv := Equiv.ofBijective f ⟨hf.injective, hsurj⟩
      isometry_toFun := hf }
  exact ⟨k, e, hk, hconv⟩

end Metric
