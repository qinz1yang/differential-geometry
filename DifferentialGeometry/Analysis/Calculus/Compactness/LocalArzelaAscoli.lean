import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli

set_option autoImplicit false
noncomputable section

namespace ArzelaAscoli
open Filter Set
open scoped Topology NNReal

variable {X : Type*} [PseudoMetricSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]

theorem exists_locallyLipschitz_subseq_limit_of_eventually_lipschitzOn_closedBall
    (f : ℕ → X → ℝ) (p : X)
    (hLip : ∀ R : ℝ, 0 ≤ R → ∃ K : ℝ≥0, ∀ᶠ n in atTop,
      LipschitzOnWith K (f n) (Metric.closedBall p R))
    (hbdd : ∃ B : ℝ, ∀ᶠ n in atTop, |f n p| ≤ B) :
    ∃ (phi : ℕ → ℕ) (g : C(X, ℝ)), StrictMono phi ∧ LocallyLipschitz g ∧
      ∀ A : Set X, IsCompact A → TendstoUniformlyOn (fun n => f (phi n)) g atTop A := by
  classical
  obtain ⟨B, hB⟩ := hbdd
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hB
  choose K hK using fun n : ℕ => hLip n (Nat.cast_nonneg n)
  choose N hN using fun n : ℕ => eventually_atTop.mp (hK n)
  let u : ℕ → ℕ := fun n => max n (max (N n) Nb)
  obtain ⟨rho, hrho, hurho⟩ := strictMono_subseq_of_id_le (u := u) (fun n => le_max_left _ _)
  let psi := u ∘ rho
  have hpsi : StrictMono psi := hurho
  have hLipPsi (n : ℕ) :
      LipschitzOnWith (K (rho n)) (f (psi n)) (Metric.closedBall p (n : ℝ)) := by
    have hindex : N (rho n) ≤ psi n := (le_max_left _ _).trans (le_max_right _ _)
    apply (hN (rho n) (psi n) hindex).mono
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hrho.id_le n)
  choose g hg heq using fun n => (hLipPsi n).extend_real
  let G : ℕ → C(X, ℝ) := fun n => ⟨g n, (hg n).continuous⟩
  have hbase (n : ℕ) : |g n p| ≤ B := by
    rw [← heq n (Metric.mem_closedBall_self (Nat.cast_nonneg n))]
    apply hNb
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hlocal (R : ℝ) (hR : 0 ≤ R) : ∃ L : ℝ≥0,
      ∀ n, LipschitzOnWith L (g n) (Metric.closedBall p R) := by
    obtain ⟨L, hL⟩ := hLip R hR
    have hlarge : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
        (eventually_ge_atTop R)
    have hevent : ∀ᶠ n in atTop, LipschitzOnWith L (g n) (Metric.closedBall p R) := by
      filter_upwards [hpsi.tendsto_atTop hL, hlarge] with n hn hnR
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      rw [← heq n (Metric.closedBall_subset_closedBall hnR hx),
        ← heq n (Metric.closedBall_subset_closedBall hnR hy)]
      exact hn.dist_le_mul x hx y hy
    obtain ⟨m, hm⟩ := eventually_atTop.mp hevent
    refine ⟨max L ((Finset.range m).sup (fun n => K (rho n))), fun n => ?_⟩
    by_cases hn : n < m
    · exact (hg n).lipschitzOnWith.weaken
        ((Finset.le_sup (f := fun n => K (rho n)) (Finset.mem_range.mpr hn)).trans (le_max_right _ _))
    · exact (hm n (Nat.le_of_not_gt hn)).weaken (le_max_left _ _)
  have hbound (x : X) : BddAbove (range fun n => |G n x|) := by
    obtain ⟨L, hL⟩ := hlocal (dist x p) dist_nonneg
    refine ⟨(L : ℝ) * dist x p + B, ?_⟩
    rintro _ ⟨n, rfl⟩
    change |g n x| ≤ _
    calc
      _ ≤ |g n x - g n p| + |g n p| := by
        simpa only [sub_add_cancel] using abs_add_le (g n x - g n p) (g n p)
      _ ≤ (L : ℝ) * dist x p + B := by
        have hd := (hL n).dist_le_mul x (Metric.mem_closedBall.mpr le_rfl) p
          (Metric.mem_closedBall_self dist_nonneg)
        exact add_le_add hd (hbase n)
  have hequi : Equicontinuous (fun n => (G n : X → ℝ)) := by
    intro x
    obtain ⟨L, hL⟩ := hlocal (dist x p + 1) (by positivity)
    apply Metric.equicontinuousAt_iff.mpr
    intro epsilon hepsilon
    refine ⟨min 1 (epsilon / ((L : ℝ) + 1)), lt_min one_pos (by positivity), ?_⟩
    intro y hy n
    have hy1 : dist y x < 1 := hy.trans_le (min_le_left _ _)
    have hxR : x ∈ Metric.closedBall p (dist x p + 1) := by
      change dist x p ≤ dist x p + 1
      linarith
    have hyR : y ∈ Metric.closedBall p (dist x p + 1) :=
      (dist_triangle y x p).trans (by linarith only [hy1])
    calc
      dist (G n x) (G n y) ≤ (L : ℝ) * dist x y := (hL n).dist_le_mul x hxR y hyR
      _ ≤ (L : ℝ) * (epsilon / ((L : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
        rw [dist_comm]
        exact (hy.trans_le (min_le_right _ _)).le
      _ < ((L : ℝ) + 1) * (epsilon / ((L : ℝ) + 1)) :=
        mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      _ = epsilon := by field_simp
  obtain ⟨sigma, limit, hsigma, hconv⟩ :=
    DifferentialGeometry.CheegerGromovCompactness.arzelaAscoli_subseq_tendstoUniformlyOnCompacts
      G hequi hbound
  have hpoint (x : X) : Tendsto (fun n => G (sigma n) x) atTop (𝓝 (limit x)) :=
    (hconv {x} isCompact_singleton).tendsto_at (mem_singleton x)
  have hlimit : LocallyLipschitz limit := by
    intro x
    let R := dist x p + 1
    obtain ⟨L, hL⟩ := hlocal R (by dsimp [R]; positivity)
    refine ⟨L, Metric.closedBall p R, ?_, LipschitzOnWith.of_dist_le_mul ?_⟩
    · apply Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds ?_) Metric.ball_subset_closedBall
      change dist x p < dist x p + 1
      exact lt_add_one _
    · intro y hy z hz
      exact le_of_tendsto ((hpoint y).dist (hpoint z))
        (Eventually.of_forall fun n => (hL (sigma n)).dist_le_mul y hy z hz)
  refine ⟨psi ∘ sigma, limit, hpsi.comp hsigma, hlimit, ?_⟩
  intro A hA
  obtain ⟨R, hR⟩ := hA.isBounded.subset_closedBall p
  have hlarge : ∀ᶠ n in atTop, R ≤ (sigma n : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hsigma.tendsto_atTop) (eventually_ge_atTop R)
  apply (hconv A hA).congr
  filter_upwards [hlarge] with n hn
  intro x hx
  exact (heq (sigma n) (Metric.closedBall_subset_closedBall hn (hR hx))).symm

end ArzelaAscoli
