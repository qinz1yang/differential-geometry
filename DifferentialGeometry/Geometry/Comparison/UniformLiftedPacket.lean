import DifferentialGeometry.Geometry.Comparison.UniformPacketPerturbation
import DifferentialGeometry.Geometry.Metric.Approximation.FiniteConfiguration

set_option autoImplicit false

open Set Metric Filter Real
open scoped Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u v w

theorem PairedComparisonPacket.eventually_uniform_lift
    {X : Type v} [MetricSpace X] {Z : ℕ → Type u}
    [∀ n, MetricSpace (Z n)] [∀ n, CompleteSpace (Z n)]
    {ι : Type w} [Finite ι] {p : ∀ n, Z n} {x q : X} {a b : ι → X}
    (hconv : GC.MetricGeometry.PointedGHConverges p x)
    (hcomp : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop, fourPointComparison 1 (ball (p n) R))
    {τ δ a₀ A : ℝ} (hpacket : PairedComparisonPacket τ {q} a b)
    (hquality : τ < δ) (ha₀ : 0 < a₀)
    (hbounds : ∀ j : ι ⊕ ι, dist q (Sum.elim a b j) ∈ Icc a₀ A)
    (hq : dist q x < 1 / 4) :
    ∃ r R : ℝ, 0 < r ∧ r < 1 / 4 ∧ 0 < R ∧
      ∀ᶠ n in atTop, ∃ y : Z n, ∃ c d : ι → Z n,
        dist y (p n) < 1 / 2 ∧ fourPointComparison 1 (ball (p n) R) ∧
        range c ∪ range d ⊆ ball (p n) R ∧ ball y (2 * r) ⊆ ball (p n) R ∧
        PairedComparisonPacket δ (ball y (2 * r)) c d ∧
        IsComplete (closedBall y r) ∧
        ∀ z ∈ ball y (2 * r), ∀ e ∈ range c ∪ range d,
          dist z e ∈ Icc (a₀ / 2) (A + 1) := by
  classical
  obtain ⟨η, r, hη, hr, hrsmall, hperturb⟩ :=
    hpacket.exists_uniform_metric_perturbation hquality ha₀ (by norm_num : (0 : ℝ) < 1 / 4) hbounds
  let v : Option (ι ⊕ ι) → X := fun j => j.elim q (Sum.elim a b)
  obtain ⟨D, hD⟩ := (finite_range (fun j => dist (v j) x)).bddAbove
  let M := max 1 D
  have hM : 1 ≤ M := le_max_left _ _
  have hv (j : Option (ι ⊕ ι)) : dist (v j) x ≤ M :=
    (hD ⟨j, rfl⟩).trans (le_max_right _ _)
  let ε := min (η / 4) (min (1 / 8) ((1 / 2 - dist q x) / 4))
  have hε : 0 < ε := lt_min (by positivity) (lt_min (by norm_num) (by linarith))
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεsmall : ε < 1 / 4 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by norm_num)
  have hεq : ε ≤ (1 / 2 - dist q x) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hR : 0 < M + 3 := by linarith
  refine ⟨r, M + 3, hr, hrsmall, hR, ?_⟩
  filter_upwards [hconv.eventually_approx (R := M + 2) hε (by linarith), hcomp (M + 3) hR] with n hn hcn
  obtain ⟨f⟩ := hn
  obtain ⟨z, _, hzrad, _, hzdist⟩ := f.exists_lift_configuration hM hεsmall v hv
  let y : Z n := (z none).val
  let c : ι ⊕ ι → Z n := fun j => (z (some j)).val
  have hy : dist y (p n) < 1 / 2 := by
    have hh := hzrad none
    change dist y (p n) < dist q x + 2 * ε at hh
    linarith
  have hcentral (j : ι ⊕ ι) : |dist y (c j) - dist q (Sum.elim a b j)| < η :=
    (hzdist none (some j)).trans (by linarith)
  have hpair (j k : ι ⊕ ι) :
      |dist (c j) (c k) - dist (Sum.elim a b j) (Sum.elim a b k)| < η :=
    (hzdist (some j) (some k)).trans (by linarith)
  obtain ⟨hp, hb⟩ := hperturb (Z n) y c hcentral hpair
  refine ⟨y, c ∘ Sum.inl, c ∘ Sum.inr, hy, hcn, ?_, ?_, hp,
    isClosed_closedBall.isComplete, ?_⟩
  · rintro e (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact lt_of_le_of_lt (z (some (Sum.inl i))).property (by linarith)
    · exact lt_of_le_of_lt (z (some (Sum.inr i))).property (by linarith)
  · intro w hw
    have ht := dist_triangle w y (p n)
    have hw' := mem_ball.mp hw
    rw [mem_ball]
    linarith
  · rintro w hw e (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hb w hw (Sum.inl i)
    · exact hb w hw (Sum.inr i)

end DifferentialGeometry.Geometry.Comparison.Toponogov
