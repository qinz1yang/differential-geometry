import DifferentialGeometry.Geometry.Metric.CloudCoverBindings
import DifferentialGeometry.Analysis.InnerProductSpace.BufferedNormalGraphAllJets

/-!
# Abstract chapter 14 cloud rows: CFS02, CFS03, CFS09 (row-named wrappers)

Blueprint `master207B.tex`: the cloud convention (CS) (lines 1768–1782), CFS02
(`lem:fibration-cloud-small-cover`, 1826–1850), CFS03 (`lem:fibration-cloud-plane-coherence`,
1884–1921), CFS09 (`lem:fibration-buffered-graph-nearest-projection`, 2262–2290).

* `cfs02_cfs03_row`: for a nonempty-or-not bounded cloud `S ⊆ S̃` in a finite-dimensional inner
  product space `H`, planes `L_x` of dimension `k`, a radius `r` bounded above and away from zero
  on `S` with the radius inequality, and the truncated-set bounds (CS), the greedy selection `T`
  of CFS02 exists: disjoint balls `B(x, λ r x)`, the cover `N_{λ r}(S) ⊆ ⋃ B(x, 5λ r x)` and, for
  every `v ∈ B(x₀, 5λ r₀)`, the comparisons (NC) `A⁻¹ r₀ ≤ r_i ≤ A r₀`, `|x_i − x₀| ≤ Dλ r₀`,
  `|J| ≤ N = ⌈(1 + 2AD)ᵏ⌉`, and CFS03's (PC) `|P₀(x_i − x₀)| ≤ δ r₀`,
  `‖P_i − P₀‖ ≤ 6(A + 1)δ` for the normal projectors (no further reduction of `δ` is needed).
  `cfs02_row` is the CFS02 part alone.
* `cfs09_row`: nearest points to a buffered graph, with all derivatives, in the row's
  coordinates (`o = 0`, `H = E ⊕ E⊥`, (IS) as the set equality
  `W ∩ B(0, 3R) = G ∩ B(0, 3R)`); the derivative clause is `‖DP − π_E‖ ≤ 7a` (row: `8a`).

Kernels: Codex X80 Sol `exists_coherent_cloud_cover`, X63
`exists_uniform_buffered_normal_graph_nearest_all_jets`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ContDiff

namespace GC.MetricGeometry

section CFS0203

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- CFS02 and CFS03 for the same selection. -/
theorem cfs02_cfs03_row (S St : Set H) (hSSt : S ⊆ St) (hS : Bornology.IsBounded S)
    (r : H → ℝ) (L : S → Submodule ℝ H) (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (L x) = k)
    (rmin R C δ : ℝ) (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hCS : ∀ x : S, hausdorffEDist (St ∩ ball (x : H) (r x / δ))
      ((AffineSubspace.mk' (x : H) (L x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
        ENNReal.ofReal (δ * r x)) :
    let lam : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∃ (T : Set H) (hTS : T ⊆ S), T.Finite ∧
      T.PairwiseDisjoint (fun i => ball i (lam * r i)) ∧
      ((⋃ x ∈ S, ball x (lam * r x)) ⊆ ⋃ i ∈ T, ball i (5 * lam * r i)) ∧
      ∀ x₀ : S, ∀ v ∈ ball (x₀ : H) (5 * lam * r x₀),
        let J := T ∩ {i | (closedBall i (20 * lam * r i) ∩ ball v (lam * r x₀)).Nonempty}
        J.ncard ≤ ⌈(1 + 2 * A * D) ^ k⌉₊ ∧
        ∀ (i : H) (hi : i ∈ J), r x₀ / A ≤ r i ∧ r i ≤ A * r x₀ ∧
          dist i x₀ ≤ D * lam * r x₀ ∧
          ‖(L x₀)ᗮ.starProjection (i - x₀)‖ ≤ δ * r x₀ ∧
          ‖(L ⟨i, hTS hi.1⟩)ᗮ.starProjection - (L x₀)ᗮ.starProjection‖ ≤
            6 * (A + 1) * δ := by
  have hTB : TotallyBounded S := hS.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨T, hTS, hfin, hdisj, hcover, hloc⟩ := exists_coherent_cloud_cover S St hSSt hTB r L k
    hdim rmin R C δ hrmin hlower hupper hC hδ hδsmall hscale hCS
  refine ⟨T, hTS, hfin, hdisj, hcover, fun x₀ v hv => ?_⟩
  obtain ⟨hcard, hrest⟩ := hloc x₀ v hv
  exact ⟨by exact_mod_cast hcard.trans (Nat.le_ceil _), hrest⟩

/-- CFS02 (`lem:fibration-cloud-small-cover`) alone. -/
theorem cfs02_row (S St : Set H) (hSSt : S ⊆ St) (hS : Bornology.IsBounded S)
    (r : H → ℝ) (L : S → Submodule ℝ H) (k : ℕ) (hdim : ∀ x : S, Module.finrank ℝ (L x) = k)
    (rmin R C δ : ℝ) (hrmin : 0 < rmin)
    (hlower : ∀ x ∈ S, rmin ≤ r x) (hupper : ∀ x ∈ S, r x ≤ R)
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hδsmall : δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))))
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hCS : ∀ x : S, hausdorffEDist (St ∩ ball (x : H) (r x / δ))
      ((AffineSubspace.mk' (x : H) (L x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
        ENNReal.ofReal (δ * r x)) :
    let lam : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let D : ℝ := 20 * A + 6
    ∃ T : Set H, T ⊆ S ∧ T.Finite ∧
      T.PairwiseDisjoint (fun i => ball i (lam * r i)) ∧
      ((⋃ x ∈ S, ball x (lam * r x)) ⊆ ⋃ i ∈ T, ball i (5 * lam * r i)) ∧
      ∀ x₀ : S, ∀ v ∈ ball (x₀ : H) (5 * lam * r x₀),
        let J := T ∩ {i | (closedBall i (20 * lam * r i) ∩ ball v (lam * r x₀)).Nonempty}
        J.ncard ≤ ⌈(1 + 2 * A * D) ^ k⌉₊ ∧
        ∀ i ∈ J, r x₀ / A ≤ r i ∧ r i ≤ A * r x₀ ∧ dist i x₀ ≤ D * lam * r x₀ := by
  obtain ⟨T, hTS, hfin, hdisj, hcover, hloc⟩ := cfs02_cfs03_row S St hSSt hS r L k hdim rmin R C
    δ hrmin hlower hupper hC hδ hδsmall hscale hCS
  refine ⟨T, hTS, hfin, hdisj, hcover, fun x₀ v hv => ?_⟩
  obtain ⟨hcard, hrest⟩ := hloc x₀ v hv
  exact ⟨hcard, fun i hi => ⟨(hrest i hi).1, (hrest i hi).2.1, (hrest i hi).2.2.1⟩⟩

end CFS0203

section CFS09

open DifferentialGeometry.Analysis

universe u

/-- CFS09 (`lem:fibration-buffered-graph-nearest-projection`) in the row's coordinates: `H`
complete, `E ≤ H` finite-dimensional, `g : B_E(0, 4R) → E⊥` with (GB), the graph `G` of `g`,
`G ⊆ W` and `W ∩ B(0, 3R) = G ∩ B(0, 3R)` (IS). -/
theorem cfs09_row :
    ∃ c : ℕ → ℝ, (∀ q, 0 ≤ c q) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
        (E : Submodule ℝ H) [FiniteDimensional ℝ E] (m : ℕ), 1 ≤ m →
        ∀ (g : E → Eᗮ) (W : Set H) (R a : ℝ), 0 < R → 0 < a → a ≤ 1 / 100 →
        ContDiffOn ℝ (m + 1 : ℕ) g (ball (0 : E) (4 * R)) →
        (∀ q ≤ m + 1, ∀ t ∈ ball (0 : E) (4 * R),
          ‖iteratedFDeriv ℝ q g t‖ ≤ a * R * (R⁻¹) ^ q) →
        let G : Set H := (fun t => orthogonalCoordinateSum E (t, g t)) '' ball (0 : E) (4 * R)
        G ⊆ W → W ∩ ball (0 : H) (3 * R) = G ∩ ball (0 : H) (3 * R) →
        ∃ P : H → H, ContDiffOn ℝ m P (ball 0 R) ∧
          (∀ z ∈ ball (0 : H) R, P z ∈ W ∧ IsMinOn (fun y => dist z y) W (P z) ∧
            (∀ y ∈ W, IsMinOn (fun w => dist z w) W y → y = P z) ∧
            ‖P z - E.starProjection z‖ ≤ 3 * a * R ∧
            ‖fderiv ℝ P z - E.starProjection‖ ≤ 7 * a ∧
            Module.finrank ℝ (LinearMap.range (fderiv ℝ P z).toLinearMap) =
              Module.finrank ℝ E ∧
            ∀ q, 2 ≤ q → q ≤ m →
              ‖iteratedFDeriv ℝ q (fun y => P y - E.starProjection y) z‖ ≤
                c q * a * R * (R⁻¹) ^ q) ∧
          (ContDiffOn ℝ ∞ g (ball (0 : E) (4 * R)) → ContDiffOn ℝ ∞ P (ball 0 R)) := by
  obtain ⟨c, hc, hker⟩ := exists_uniform_buffered_normal_graph_nearest_all_jets.{u}
  refine ⟨c, hc, ?_⟩
  intro H _ _ _ E _ m hm g W R a hR ha ha1 hg hGB G hGW hIS
  obtain ⟨P, hPsmooth, hPz, hPinf⟩ := hker H E m hm 0 g W R a hR ha.le ha1 hg hGB
    (fun t ht => by simpa only [zero_add] using hGW ⟨t, ht, rfl⟩)
    (fun y hy => by
      have hy' : y ∈ G ∩ ball (0 : H) (3 * R) := by
        rw [← hIS]
        simpa using hy
      obtain ⟨⟨t, ht, rfl⟩, -⟩ := hy'
      exact ⟨t, ht, by simp⟩)
  refine ⟨P, hPsmooth, fun z hz => ?_, hPinf⟩
  simpa using hPz z (by simpa using hz)

end CFS09

end GC.MetricGeometry
