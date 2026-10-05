import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBFRZ
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRegionalBinding

/-!
# BCF02's eligibility on the complete final boundary family (lane BFAM-ZD)

External review 53 §4.2: (BD) (`LocalPacketsOnBFRZ.weak_edge_density`) does NOT put the strong edge
`a` into the edge region `Ue₁ = {D > 20}`; that is derived at the consumer from BCP04.a and the
consumer's distance margin, and only then is the SAME revised edge family `edgeB` used
(`edgeB.covers_strong`). BCF02's limit points `q` satisfy `D(q) ≥ 35`.

* `ofReal_twenty_lt_of_near_BFZD`: the margin — a point `v` of `W°` that is `Vρ_v`-close for
  `d_ĝ` to a point `z` with `D(z) ≥ 20 + m` has `D(v) > 20`, by BCP04.a at `v` and `23V ≤ m n`
  (`ĝ ≥ g°`; the pattern of `ofReal_ten_lt_of_near_BDRY5`).
* `LocalPacketsOnBFRZ.weak_edge_eligible_BFZD` (consumer): on the final family of T2B / T3B
  (regions `{D > 10}`, `{D ≥ 20}`, `{D > 20}`, `{D ≥ 35}` of the completion `(W°, d_ĝ)`), with
  BCP04.a at `n ≥ 2`: for a nonslim one-stratum point `p` of `{D > 10}` and a weak edge `q` with
  `D(q) ≥ 35` and `d(q, p) < 10Δρ(p)`, the strong edge `a` of (BD) has `d(q, a) < ρ(a)`,
  `D(a) > 20` (`a ∈ Ue₁`) and lies within `Δρ(j)` of a centre `j` of the SAME `edgeB`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry GC.Endpoint GC.MetricGeometry DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **Margin for the edge region.** A point `v` of `W°` that is `V ρ_v`-close for `d_ĝ` to a point
`z` with `D(z) ≥ 20 + m` has `D(v) > 20`, by BCP04.a at `v` and `23 V ≤ m n` (`ĝ ≥ g°`). -/
theorem ofReal_twenty_lt_of_near_BFZD (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (v z : W.pieceInterior ⊤) {ρv V m n : ℝ} (hρv : 0 < ρv) (hV : 0 ≤ V) (hm : 0 < m)
    (hVn : 23 * V ≤ m * n)
    (hbcp : n * (distanceToBoundary W g v).toReal / ((distanceToBoundary W g v).toReal + 3) <
      (distanceToBoundary W g v).toReal / ρv)
    (hz : ENNReal.ofReal (20 + m) ≤ distanceToBoundary W g z)
    (hvz : riemannianEDistOf ĝ v z < ENNReal.ofReal (V * ρv)) :
    ENNReal.ofReal 20 < distanceToBoundary W g v := by
  by_contra h20
  have hD20 : distanceToBoundary W g v ≤ ENNReal.ofReal 20 := not_lt.mp h20
  have htop : distanceToBoundary W g v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD20
  have hd0 : 0 ≤ (distanceToBoundary W g v).toReal := ENNReal.toReal_nonneg
  have hd20 : (distanceToBoundary W g v).toReal ≤ 20 := by
    rw [← ENNReal.ofReal_le_ofReal_iff (by norm_num), ENNReal.ofReal_toReal htop]
    exact hD20
  have hdpos : 0 < (distanceToBoundary W g v).toReal := by
    by_contra hd0'
    have hd00 : (distanceToBoundary W g v).toReal = 0 := le_antisymm (not_lt.mp hd0') hd0
    rw [hd00] at hbcp
    simp at hbcp
  have hnρ : n * ρv < (distanceToBoundary W g v).toReal + 3 := by
    rw [div_lt_div_iff₀ (by linarith) hρv] at hbcp
    nlinarith
  have hVρ : V * ρv < m := by
    have h23 : n * ρv < 23 := by linarith
    by_cases hV0 : V = 0
    · rw [hV0, zero_mul]; exact hm
    have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
    have hn : 0 < n := by nlinarith
    nlinarith
  have : Nonempty (W.pieceInterior ⊤) := ⟨v⟩
  have hdist := (riemannianEDistOf_val_le_completion_BDRY1 W g ĝ hle v z).trans_lt hvz
  have htri := distanceToBoundary_le_add W g z.val v.val
  rw [riemannianEDistOf_comm] at htri
  have hlt : distanceToBoundary W g z < ENNReal.ofReal (20 + m) := by
    calc distanceToBoundary W g z ≤ distanceToBoundary W g v + riemannianEDistOf g v.val z.val :=
          htri
      _ < ENNReal.ofReal 20 + ENNReal.ofReal m := by
          exact ENNReal.add_lt_add_of_le_of_lt htop hD20
            (hdist.trans_le (ENNReal.ofReal_le_ofReal hVρ.le))
      _ = ENNReal.ofReal (20 + m) := by
          rw [← ENNReal.ofReal_add (by norm_num) hm.le]
  exact (lt_irrefl _) (hz.trans_lt hlt)

/-- **BCF02's eligibility on the complete final boundary family** (consumer of (BD)). On the
final family of T2B / T3B over the completion `(W°, d_ĝ)` (regions `{D > 10}`, `{D ≥ 20}`,
`{D > 20}`, `{D ≥ 35}`), with BCP04.a at `n ≥ 2`: a weak edge `q` with `D(q) ≥ 35` within
`10Δρ(p)` of a nonslim one-stratum point `p` of `{D > 10}` is within `ρ(a)` of a strong edge `a`
with `D(a) > 20` (eligible: `a ∈ Ue₁`), and `a` is within `Δρ(j)` of a centre `j` of the SAME
revised edge family `edgeB`. -/
theorem LocalPacketsOnBFRZ.weak_edge_eligible_BFZD (W : CompactCarrier.{0})
    [ConnectedSpace W.Carrier] (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))
    (hle : ∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
      (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ} (hn : 2 ≤ n)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3) :
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM)
      (p : W.pieceInterior ⊤), ENNReal.ofReal 10 < distanceToBoundary W g p →
      p ∈ scaledSplittingStratum.{0, 0} (fun x : W.pieceInterior ⊤ => ρ x) (fun x => hρ x) β 1 →
      ¬ (∃ (Z : Type) (mZ : MetricSpace Z) (z : Z), letI := mZ
        Bornology.IsBounded (univ : Set Z) ∧ diam (univ : Set Z) < 1000 * Δ ∧
        Nonempty (@KleinerLottApprox (W.pieceInterior ⊤) (WithLp 2 (ℝ × Z))
          ((inducedMetricSpace ĝ).rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
          (WithLp.toLp 2 ((0 : ℝ), z)) (β 1))) →
      ∀ q : W.pieceInterior ⊤, @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
          ((inducedMetricSpace ĝ).rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) q Δ b' s' →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q → dist q p < 10 * Δ * ρ p →
        ∃ a : W.pieceInterior ⊤, @isEdgePoint.{0, 0} (W.pieceInterior ⊤)
            ((inducedMetricSpace ĝ).rescale (ρ a)⁻¹ (inv_pos.mpr (hρ a))) a Δ b s ∧
          dist q a < ρ a ∧ ENNReal.ofReal 20 < distanceToBoundary W g a ∧
          ∃ j ∈ F.edgeB.centres, dist a j < Δ * ρ j := by
  let _ : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  intro _ F p hp10 hp hns q hq hq35 hqp
  obtain ⟨a, ha, hqa⟩ := F.weak_edge_density p hp10 hp hns q hq hqp
  have hint : a.val ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1 W]
    exact a.property
  have hD0 := distanceToBoundary_pos_of_mem_interior W g hint
  have hvz : riemannianEDistOf ĝ a q < ENNReal.ofReal (1 * ρ a) := by
    rw [inducedMetricSpace_hmetric ĝ a q, one_mul, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff (hρ a)).mpr hqa
  have hq35' : ENNReal.ofReal (20 + 15) ≤ distanceToBoundary W g q := by
    rw [show (20 : ℝ) + 15 = 35 by norm_num]
    exact hq35
  have h20 := ofReal_twenty_lt_of_near_BFZD W g ĝ hle a q (hρ a) zero_le_one
    (by norm_num : (0 : ℝ) < 15) (by linarith) (hbcp a.val hD0) hq35' hvz
  obtain ⟨j, hj, haj⟩ := F.edgeB.covers_strong a h20 ha
  exact ⟨a, ha, hqa, h20, j, hj, haj⟩

end DifferentialGeometry.Geometry.Collapse
