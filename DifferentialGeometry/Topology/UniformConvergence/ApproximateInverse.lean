import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false

open Filter Set

theorem TendstoUniformlyOn.comp_of_approximate_inverse
    {ι X E : Type*} {Y : ι → Type*} [UniformSpace X] [PseudoMetricSpace E]
    {l : Filter ι} {K : Set X} {S : ∀ i, Set (Y i)}
    {j : ∀ i, X → Y i} {h : ∀ i, Y i → X} {u : ∀ i, Y i → E} {t : X → E}
    (hround : TendstoUniformlyOn (fun i x => h i (j i x)) id l K)
    (ht : UniformContinuous t)
    (hmap : ∀ᶠ i in l, MapsTo (j i) K (S i))
    (hclose : ∀ η : ℝ, 0 < η → ∀ᶠ i in l,
      ∀ y ∈ S i, dist (u i y) (t (h i y)) ≤ η) :
    TendstoUniformlyOn (fun i x => u i (j i x)) t l K := by
  have htarget := ht.comp_tendstoUniformlyOn hround
  rw [Metric.tendstoUniformlyOn_iff] at htarget ⊢
  intro ε hε
  filter_upwards [hmap, hclose (ε / 2) (half_pos hε),
    htarget (ε / 2) (half_pos hε)] with i hi hci hti x hx
  calc
    dist (t x) (u i (j i x)) ≤
        dist (t x) (t (h i (j i x))) + dist (t (h i (j i x))) (u i (j i x)) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add_of_lt_of_le (hti x hx) (by simpa only [dist_comm] using hci _ (hi hx))
    _ = ε := add_halves ε
