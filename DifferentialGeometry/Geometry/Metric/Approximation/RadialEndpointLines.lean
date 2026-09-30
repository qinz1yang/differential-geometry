import DifferentialGeometry.Topology.MetricSpace.SignedPrefix
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixLineLimit

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {L : ℕ → ι → ℝ} {R ε : ℕ → ℝ}

theorem exists_calibrated_lines_of_opposite_radial_isometries
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (aPlus aMinus : ∀ i, ι → A i)
    (hLpos : ∀ i j, 0 < L i j) (hL : ∀ j, Tendsto (fun i => L i j) atTop atTop)
    (qPlus qMinus : ∀ i j, Icc (0 : ℝ) (L i j) → A i)
    (hpIso : ∀ i j, Isometry (qPlus i j)) (hmIso : ∀ i j, Isometry (qMinus i j))
    (hp0 : ∀ i j, qPlus i j ⟨0, ⟨le_rfl, (hLpos i j).le⟩⟩ = o i)
    (hm0 : ∀ i j, qMinus i j ⟨0, ⟨le_rfl, (hLpos i j).le⟩⟩ = o i)
    (hpEnd : ∀ i j, qPlus i j ⟨L i j, ⟨(hLpos i j).le, le_rfl⟩⟩ = aPlus i j)
    (hmEnd : ∀ i j, qMinus i j ⟨L i j, ⟨(hLpos i j).le, le_rfl⟩⟩ = aMinus i j)
    (hE : ∀ j, Tendsto (fun i => 2 * L i j - dist (aPlus i j) (aMinus i j)) atTop (𝓝 0)) :
    ∃ Q : ∀ i j, Icc (-(L i j)) (L i j) → A i,
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [hLpos i j], (hLpos i j).le⟩⟩ = o i) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (L i j),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, hLpos i j], t.property.2⟩⟩ = qPlus i j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos i j]⟩⟩ = qMinus i j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) (L i j),
        t.val ≤ L i j - dist (Q i j ⟨t.val, ⟨by linarith [t.property.1, hLpos i j], t.property.2⟩⟩) (aPlus i j) ∧
        L i j - dist (Q i j ⟨t.val, ⟨by linarith [t.property.1, hLpos i j], t.property.2⟩⟩) (aPlus i j) ≤ t.val ∧
        -t.val ≤ L i j - dist (Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos i j]⟩⟩) (aPlus i j) ∧
        L i j - dist (Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hLpos i j]⟩⟩) (aPlus i j) ≤
          -t.val + (2 * L i j - dist (aPlus i j) (aMinus i j))) ∧
      ∃ (γ : ι → ℝ → Y) (φ : ℕ → ℕ),
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧ StrictMono φ ∧
        ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R (φ i) ∧ ∀ j, S ≤ L (φ i) j ∧
          ∀ t : Icc (-(L (φ i) j)) (L (φ i) j), |t.val| ≤ S →
            ∀ ht : dist (Q (φ i) j t) (o (φ i)) ≤ R (φ i),
              dist ((f (φ i)).toFun ⟨Q (φ i) j t, ht⟩) (γ j t.val) < ζ := by
  classical
  have hpRad (i : ℕ) (j : ι) (t : Icc (0 : ℝ) (L i j)) :
      dist (o i) (qPlus i j t) = t.val := by
    rw [← hp0 i j, (hpIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      zero_sub, abs_neg, abs_of_nonneg t.property.1]
  have hmRad (i : ℕ) (j : ι) (t : Icc (0 : ℝ) (L i j)) :
      dist (o i) (qMinus i j t) = t.val := by
    rw [← hm0 i j, (hmIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      zero_sub, abs_neg, abs_of_nonneg t.property.1]
  have hpTail (i : ℕ) (j : ι) (t : Icc (0 : ℝ) (L i j)) :
      dist (qPlus i j t) (aPlus i j) = L i j - t.val := by
    rw [← hpEnd i j, (hpIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  have hmTail (i : ℕ) (j : ι) (t : Icc (0 : ℝ) (L i j)) :
      dist (qMinus i j t) (aMinus i j) = L i j - t.val := by
    rw [← hmEnd i j, (hmIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    ring
  have hp (i : ℕ) (j : ι) : dist (o i) (aPlus i j) = L i j := by
    rw [← hpEnd i j]
    exact hpRad i j _
  have hm (i : ℕ) (j : ι) : dist (o i) (aMinus i j) = L i j := by
    rw [← hmEnd i j]
    exact hmRad i j _
  have hEnonneg (i : ℕ) (j : ι) : 0 ≤ 2 * L i j - dist (aPlus i j) (aMinus i j) := by
    have hh := dist_triangle (aPlus i j) (o i) (aMinus i j)
    rw [dist_comm (aPlus i j) (o i), hp i j, hm i j] at hh
    linarith
  have hcal (i : ℕ) (j : ι) := opposite_prefix_distance_calibration (η := 0)
    (hp i j) (qPlus i j) (qMinus i j)
    (fun t => (hpRad i j t).le) (fun t => (hmRad i j t).le)
    (fun t => by rw [hpTail i j t]; simp only [add_zero, le_refl])
    (fun t => by rw [hmTail i j t]; simp only [add_zero, le_refl])
  have hpDist (i : ℕ) (j : ι) (s t : Icc (0 : ℝ) (L i j)) (hst : s ≤ t) :
      t.val - s.val - 0 ≤ dist (qPlus i j s) (qPlus i j t) := by
    rw [(hpIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst))]
    linarith
  have hmDist (i : ℕ) (j : ι) (s t : Icc (0 : ℝ) (L i j)) (hst : s ≤ t) :
      t.val - s.val - 0 ≤ dist (qMinus i j s) (qMinus i j t) := by
    rw [(hmIso i j).dist_eq, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (show s.val ≤ t.val from hst))]
    linarith
  choose Q hQLip hQbase hAlign hLower _ using fun i j =>
    exists_signed_prefix_of_opposite_prefixes (hLpos i j).le (hEnonneg i j) (le_refl (0 : ℝ))
      (qPlus i j) (qMinus i j) (hpIso i j).lipschitzWith (hmIso i j).lipschitzWith
      (hp0 i j) (hm0 i j) (hpDist i j) (hmDist i j) (fun t u => ((hcal i j).1 t u).1)
  have hLower' (i : ℕ) (j : ι) (s t : Icc (-(L i j)) (L i j)) :
      |s.val - t.val| - (2 * L i j - dist (aPlus i j) (aMinus i j)) ≤ dist (Q i j s) (Q i j t) := by
    simpa only [mul_zero, sub_zero] using hLower i j s t
  obtain ⟨γ, φ, hγ, hγ0, hφ, hconv⟩ := exists_isometric_lines_of_signed_prefixes
    f hR hε (fun i j => (hLpos i j).le) hL hE Q hQLip hQbase hLower'
  refine ⟨Q, hQLip, hQbase, hAlign, ?_, γ, φ, hγ, hγ0, hφ, hconv⟩
  intro i j t
  rw [(hAlign i j t).1, (hAlign i j t).2]
  simpa only [sub_zero, add_zero] using (hcal i j).2 t

end GC.MetricGeometry
