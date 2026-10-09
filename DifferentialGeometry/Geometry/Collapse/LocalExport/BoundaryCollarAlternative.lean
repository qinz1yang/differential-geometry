import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarPacket
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapBCP03Unit
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02Contract

/-!
# LC88: the product-or-disjoint alternative and the slim adapted coordinate

Blueprint row LC88 (`def:collapse-boundary-packet`, master207A): "Either the whole connected
carrier is already such a product, or the retained boundary and zero-model regions are pairwise
disjoint", and KL 16.4's "slim adapted coordinate on the depth band `(5, 95)`". The collar layer
`BoundaryCollarPacket` (F9-C) left both open (they needed BCP03 with E7 and BCP02). Here, for a
collar packet on a CONNECTED carrier:

* `BoundaryCollarPacket.exists_of_level_le_add`: the retained piece `{F_i ≤ 90}` lies in
  `e_i{z ≤ 90 + ε}`;
* `BoundaryCollarPacket.product_or_retained_disjoint` (KL 16.5, BCP03 in the blueprint's
  `T² × [0, 1]` form): either `W ≅ T² × [0, 1]` with two distinct labelled boundary components at
  the ends, or the enlarged collars `e_i{z < 92}` are pairwise disjoint and the retained pieces
  `{F_i ≤ 90}` of the packet are pairwise disjoint at intrinsic distance `≥ 1` (`ε ≤ 1/2`);
* `BoundaryCollarPacket.adapted_coordinate` (KL 16.4 / BCP02 for the packet's OWN height `η_i`):
  BCP02.a, BCP02.b with buffer and the adapted clauses of quality `γ` (`1 ≤ K`, `ε ≤ 1/1000`);
* `BoundaryExportPacket`: the collar packet together with these two fields, and its producer
  `BoundaryExportPacket.ofCollarPacket`.

Still open for LC88 (other rows): the zero-model half of the disjointness (BCP05, which needs the
BCP04 zero family) and the interior family with centres at boundary distance greater than ten
(LPA06, lane F8-LPA2, with KL 16.5–16.6).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Collapse

universe u

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- The retained piece `{F_i ≤ 90}` lies in the collar below depth `90 + ε`. -/
theorem exists_of_level_le_add (P : BoundaryCollarPacket W g K A w₀ ε) (i : Fin P.cusp.count)
    {y : W.Carrier} (hy : P.level i y ≤ 90) :
    ∃ p ∈ cuspDomain, (P.cusp.collar i).toFun p = y ∧ p.2.val 0 ≤ 90 + ε := by
  have hy' : y ∈ {y | P.level i y ≤ 90} := hy
  rw [P.level_sublevel_eq i] at hy'
  obtain ⟨p, ⟨hp, h⟩, rfl⟩ := hy'
  refine ⟨p, hp, rfl, ?_⟩
  rcases h with h2 | ⟨h98, hη⟩
  · linarith [P.tolerance_pos]
  · rcases le_or_gt (p.2.val 0) 2 with h2 | h2
    · linarith [P.tolerance_pos]
    · have h := abs_lt.mp (P.height_contract i p hp h2.le h98).1
      linarith

/-- **LC88 / KL 16.5: product or disjoint retained pieces.** On a connected carrier
(`1 ≤ K`, tolerance `ε ≤ 1/2`): either `W ≅ T² × [0, 1]` with `T² × {0}` onto `∂_i W` and
`T² × {1}` onto `∂_j W` for two distinct components, or the enlarged collars `e_i{z < 92}` are
pairwise disjoint and the retained pieces `{F_i ≤ 90}` are pairwise disjoint at intrinsic
distance `≥ 1`. -/
theorem product_or_retained_disjoint [ConnectedSpace W.Carrier]
    (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K) (hε : ε ≤ 1 / 2) :
    (∃ (i j : Fin P.cusp.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
          ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
    ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      Disjoint {x | P.level i x ≤ 90} {y | P.level j y ≤ 90} ∧
      ∀ x y, P.level i x ≤ 90 → P.level j y ≤ 90 →
        ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  have hw₀ : 0 ≤ w₀ := (P.cusp.collar ⟨0, P.cusp.count_pos⟩).delta_nonneg
  rcases P.cusp.bcp03_unit hK hw₀ (by linarith [P.threshold]) with hprod | hdisj
  · exact Or.inl hprod
  · refine Or.inr fun i j hij => ⟨(hdisj i j hij).1, ?_⟩
    have hsub : ∀ k : Fin P.cusp.count, ∀ y, P.level k y ≤ 90 →
        y ∈ (P.cusp.collar k).toFun '' {p : CuspHalfSpace | p.2.val 0 ≤ 181 / 2} := by
      intro k y hy
      obtain ⟨p, -, rfl, hp⟩ := P.exists_of_level_le_add k hy
      exact ⟨p, show p.2.val 0 ≤ 181 / 2 by linarith, rfl⟩
    exact P.cusp.bcp03b (by linarith [P.threshold]) (hdisj i j hij).1 (hsub i) (hsub j)

/-- **LC88 / KL 16.4: the slim adapted coordinate for the packet's own height** (BCP02 with
`η = η_i`; connected carrier, `1 ≤ K`, tolerance `ε ≤ 1/1000`). -/
theorem adapted_coordinate [ConnectedSpace W.Carrier] (P : BoundaryCollarPacket W g K A w₀ ε)
    (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000) (i : Fin P.cusp.count) :
    ∀ (β γ L r : ℝ) (q₀ : CuspHalfSpace) (hr : 0 < r), 0 < β → β < γ → γ < 1 → 0 ≤ L →
      w₀ ≤ β ^ 2 / 1000 → ε ≤ β ^ 2 / 1000 → r ≤ β ^ 3 / (2000 * (1 + L)) →
      2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 → 5 ≤ P.height i ((P.cusp.collar i).toFun q₀) →
          P.height i ((P.cusp.collar i).toFun q₀) ≤ 95 →
      @HasEuclideanSplitting.{u, 0} W.Carrier
          ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) ((P.cusp.collar i).toFun q₀) 1 β ∧
      (∀ x x' : W.Carrier,
        r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
        r⁻¹ * (riemannianEDistOf g x' ((P.cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
        (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
            Real.sqrt (((P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r -
                (P.height i x' - P.height i ((P.cusp.collar i).toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                  (riemannianEDistOf (P.cusp.collar i).cusp.torusMetric
                (invFunOn (P.cusp.collar i).toFun cuspDomain x).1
                (invFunOn (P.cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ∧
          Real.sqrt (((P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r -
              (P.height i x' - P.height i ((P.cusp.collar i).toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                  (riemannianEDistOf (P.cusp.collar i).cusp.torusMetric
                (invFunOn (P.cusp.collar i).toFun cuspDomain x).1
                (invFunOn (P.cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ≤
            (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal < 1 →
        r⁻¹ * (riemannianEDistOf g x' ((P.cusp.collar i).toFun q₀)).toReal < 1 →
        |(P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r - (P.height i x' - P.height i
            ((P.cusp.collar i).toFun q₀)) / r| ≤
          (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 + γ⁻¹ →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
          (P.cusp.collar i).toFun p = c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) →
        |deriv (fun t => (P.height i (c t) - P.height i ((P.cusp.collar i).toFun q₀)) / r) x₀ -
          ((P.height i (c (x₀ +
              ℓ)) - P.height i ((P.cusp.collar i).toFun q₀)) / r - (P.height i (c x₀) - P.height i
                  ((P.cusp.collar i).toFun q₀)) / r) / ℓ| <
          γ) ∧
      (∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp ((P.cusp.collar i).toFun q₀)).toReal < 1 ∧
        r⁻¹ * (riemannianEDistOf g xm ((P.cusp.collar i).toFun q₀)).toReal < 1 ∧
        |(P.height i xp - P.height i ((P.cusp.collar i).toFun q₀)) / r - 1| < γ ∧
            |(P.height i xm - P.height i ((P.cusp.collar i).toFun q₀)) / r + 1| < γ) ∧
      ∀ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((P.cusp.collar i).toFun q₀)).toReal < 1 →
        |(P.height i x - P.height i ((P.cusp.collar i).toFun q₀)) / r| < 1 + γ :=
  (P.cusp.collar i).bcp02_of_contract hK (P.cusp.collar i).delta_nonneg
    (by linarith [P.threshold]) P.tolerance_pos hε (P.contMDiff_height i) (P.height_contract i)

end BoundaryCollarPacket

/-- **LC88, boundary export layer.** The collar packet with KL 16.5's product-or-disjoint
alternative on its retained pieces and KL 16.4's slim adapted coordinate for its own heights.
DATA with proofs of these fields (connected carrier). -/
structure BoundaryExportPacket (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ ε : ℝ)
    extends BoundaryCollarPacket W g K A w₀ ε where
  /-- KL 16.5: the whole carrier is `T² × [0, 1]` with two labels, or the enlarged collars and
  the retained pieces are pairwise disjoint, the retained pieces at distance `≥ 1`. -/
  alternative : (∃ (i j : Fin cusp.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ cusp.component i ↔ p.2.1 = 0) ∧ ∀ p, D p ∈ cusp.component j ↔ p.2.1 = 1) ∨
    ∀ i j : Fin cusp.count, i ≠ j →
      Disjoint ((cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      Disjoint {x | level i x ≤ 90} {y | level j y ≤ 90} ∧
      ∀ x y, level i x ≤ 90 → level j y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y
  /-- KL 16.4: BCP02 for the packet's height `η_i` on the depth band. -/
  adapted : ∀ i : Fin cusp.count,
    ∀ (β γ L r : ℝ) (q₀ : CuspHalfSpace) (hr : 0 < r), 0 < β → β < γ → γ < 1 → 0 ≤ L →
      w₀ ≤ β ^ 2 / 1000 → ε ≤ β ^ 2 / 1000 → r ≤ β ^ 3 / (2000 * (1 + L)) →
      2 ≤ q₀.2.val 0 → q₀.2.val 0 ≤ 98 → 5 ≤ height i ((cusp.collar i).toFun q₀) →
          height i ((cusp.collar i).toFun q₀) ≤ 95 →
      @HasEuclideanSplitting.{u, 0} W.Carrier
          ((inducedMetricSpace g).rescale r⁻¹ (inv_pos.mpr hr)) ((cusp.collar i).toFun q₀) 1 β ∧
      (∀ x x' : W.Carrier,
        r⁻¹ * (riemannianEDistOf g x ((cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
        r⁻¹ * (riemannianEDistOf g x' ((cusp.collar i).toFun q₀)).toReal ≤ β⁻¹ + β + L →
        (1 - β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal) ≤
            Real.sqrt (((height i x - height i ((cusp.collar i).toFun q₀)) / r -
                (height i x' - height i ((cusp.collar i).toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                  (riemannianEDistOf (cusp.collar i).cusp.torusMetric
                (invFunOn (cusp.collar i).toFun cuspDomain x).1
                (invFunOn (cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ∧
          Real.sqrt (((height i x - height i ((cusp.collar i).toFun q₀)) / r -
              (height i x' - height i ((cusp.collar i).toFun q₀)) / r) ^ 2 +
              (r⁻¹ * Real.exp (-(q₀.2.val 0) / 2) *
                  (riemannianEDistOf (cusp.collar i).cusp.torusMetric
                (invFunOn (cusp.collar i).toFun cuspDomain x).1
                (invFunOn (cusp.collar i).toFun cuspDomain x').1).toReal) ^ 2) ≤
            (1 + β ^ 2 / 20) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ x x' : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((cusp.collar i).toFun q₀)).toReal < 1 →
        r⁻¹ * (riemannianEDistOf g x' ((cusp.collar i).toFun q₀)).toReal < 1 →
        |(height i x - height i ((cusp.collar i).toFun q₀)) / r - (height i x' - height i
            ((cusp.collar i).toFun q₀)) / r| ≤
          (1 + γ / 2) * (r⁻¹ * (riemannianEDistOf g x x').toReal)) ∧
      (∀ (c : ℝ → W.Carrier) (x₀ ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 + γ⁻¹ →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
          (cusp.collar i).toFun p = c t) →
        (∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
          (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ r ^ 2) →
        |deriv (fun t => (height i (c t) - height i ((cusp.collar i).toFun q₀)) / r) x₀ -
          ((height i (c (x₀ +
              ℓ)) - height i ((cusp.collar i).toFun q₀)) / r - (height i (c x₀) - height i
                  ((cusp.collar i).toFun q₀)) / r) / ℓ| <
          γ) ∧
      (∃ xp xm : W.Carrier, r⁻¹ * (riemannianEDistOf g xp ((cusp.collar i).toFun q₀)).toReal < 1 ∧
        r⁻¹ * (riemannianEDistOf g xm ((cusp.collar i).toFun q₀)).toReal < 1 ∧
        |(height i xp - height i ((cusp.collar i).toFun q₀)) / r - 1| < γ ∧
            |(height i xm - height i ((cusp.collar i).toFun q₀)) / r + 1| < γ) ∧
      ∀ x : W.Carrier, r⁻¹ * (riemannianEDistOf g x ((cusp.collar i).toFun q₀)).toReal < 1 →
        |(height i x - height i ((cusp.collar i).toFun q₀)) / r| < 1 + γ

namespace BoundaryExportPacket

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **Producer.** Every collar packet on a connected carrier with `1 ≤ K` and tolerance
`ε ≤ 1/1000` extends to an export packet. -/
def ofCollarPacket (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000) :
    BoundaryExportPacket W g K A w₀ ε where
  toBoundaryCollarPacket := P
  alternative := P.product_or_retained_disjoint hK (by linarith)
  adapted := P.adapted_coordinate hK hε

/-- The premises with `2 ≤ K`, `w₀ ≤ 1/6408` give an export packet at every tolerance
`0 < ε ≤ 1/1000`. -/
theorem nonempty_of_premises (P : BoundaryCollapsePremises W g K A w₀) (hK : 2 ≤ K)
    (hw : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hε1 : ε ≤ 1 / 1000) :
    Nonempty (BoundaryExportPacket W g K A w₀ ε) :=
  ⟨ofCollarPacket (BoundaryCollarPacket.ofPremises P hK hw hε (by linarith)) (by omega) hε1⟩

end BoundaryExportPacket

end DifferentialGeometry.Geometry.Collapse
