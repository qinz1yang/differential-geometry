import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovBoundaryBuffer

/-!
# Volume at all centres from a seed (chapters 9–10, adapter A13)

A seed volume `vol B(p, r₀) ≥ w r₀³` and `sec ≥ -Λ` on the buffer `B(p, 3R)` give, at every centre
`x ∈ B̄(p, R)` and radius `a ≤ R`, `vol B(x, a) ≥ κ a³` with
`κ = w r₀³ V_{-Λ}(a) / (a³ V_{-Λ}(2R))`, `V_{-Λ} = modelVolume (-Λ) 3`, chosen before the manifold.

* `localBishopGromov_cross_of_compact_three`: relative Bishop–Gromov on a closed (compact,
  boundaryless) three-manifold, with NO connectedness assumption.  This is the boundaryless case of
  `localBishopGromov_cross_of_distanceToBoundary` (`BishopGromovBoundaryBuffer.lean`): the ball
  `U = B(p, R + 1)` is path-connected, it carries a complete metric equal to `g` near `B̄(p, R)`
  (`exists_riemannianMetricComplete_eqOn_of_isCompact`), and the comparison is transported along the
  inverse of the inclusion (`localBishopGromov_cross_of_isometricOn`).  The connected-component
  restriction of the design is thus done inside the proof, on a connected ball.
* `A13_all_centre_volume_of_seed_explicit`: the errata constant.
* `A13_all_centre_volume_of_seed`: the interface statement.

For `x ∈ B̄(p, R)`: `B(p, r₀) ⊆ B(x, 2R) ⊆ B(p, 3R)` (strict inequalities in the open balls), and
`vol B(x, a) ≥ (V(a)/V(2R)) vol B(x, 2R) ≥ w r₀³ V(a)/V(2R)`.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Closed

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]

/-- Relative Bishop–Gromov on a closed three-manifold, without connectedness: if `sec ≥ -κ`
(`κ ≥ 0`) on `B(p, R)`, the balls about `p` of radii `0 < s ≤ R` satisfy the cross inequality
of `localBishopGromov_cross_endpoint_sectional_three`. -/
theorem localBishopGromov_cross_of_compact_three (g : SmoothRiemannianMetric ThreeModel X)
    (p : X) {κ s R : ℝ} (hκ : 0 ≤ κ) (hs : 0 < s) (hsR : s ≤ R)
    (hsec : ∀ q ∈ riemannianBallOf g p R, SectionalBoundedBelowAt g q (-κ)) :
    ballVolume g p R * ENNReal.ofReal (modelVolume (-κ) 3 s) ≤
      ENNReal.ofReal (modelVolume (-κ) 3 R) * ballVolume g p s := by
  have hR : 0 < R := hs.trans_le hsR
  have hρ : 0 < R + 1 := by linarith
  -- the connected open ball `U = B(p, R + 1)`
  let U : Opens X :=
    ⟨riemannianBallOf g p (R + 1), isOpen_lt (continuous_riemannianEDist g p) continuous_const⟩
  have hpU : p ∈ U := by
    change riemannianEDistOf g p p < ENNReal.ofReal (R + 1)
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hρ
  have hcloU : riemannianClosedBallOf g p R ⊆ U := fun x hx =>
    lt_of_le_of_lt (show riemannianEDistOf g p x ≤ ENNReal.ofReal R from hx)
      ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith))
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  have : ConnectedSpace U :=
    isConnected_iff_connectedSpace.mp (isPathConnected_riemannianBallOf g p hρ).isConnected
  have : Nonempty U := ⟨⟨p, hpU⟩⟩
  have hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (Subtype.val : U → X) :=
    isLocalDiffeomorph_subtype_val U
  let gU : SmoothRiemannianMetric ThreeModel U := localPullMetric g Subtype.val hι
  -- a complete metric on `U` equal to `gU` near the closed `R`-ball
  let K : Set U := Subtype.val ⁻¹' riemannianClosedBallOf g p R
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    change IsCompact (Subtype.val '' (Subtype.val ⁻¹' riemannianClosedBallOf g p R))
    rw [Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, hcloU hx⟩, rfl⟩)]
    exact (Geometry.Metric.isClosed_riemannianClosedBallOf g p R).isCompact
  obtain ⟨g', O, hg', hO, hKO, hg'O, -⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := ThreeModel) gU hK
  -- the inverse of the inclusion of `O`, isometric on its source
  let O' : Opens U := ⟨O, hO⟩
  have hF : IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun x : O' => (x : U).val) :=
    isLocalDiffeomorph_comp hι (isLocalDiffeomorph_subtype_val (I := ThreeModel) O')
  let Ψ : PartialDiffeomorph ThreeModel ThreeModel U X ∞ :=
    partialDiffeomorphOfInjOn Subtype.val O' hι.contMDiff.contMDiffOn hF
      Subtype.val_injective.injOn
  have hmetric := isometricOn_symm g g' Ψ (fun z hz a b => by
    rw [hg'O z hz]
    exact localPullMetric_inner g Subtype.val hι z a b)
  have hball : riemannianBallOf g p R ⊆ Ψ.symm.source := by
    intro y hy
    have hyc : y ∈ riemannianClosedBallOf g p R :=
      show riemannianEDistOf g p y ≤ ENNReal.ofReal R from le_of_lt hy
    exact ⟨⟨y, hcloU hyc⟩, hKO hyc, rfl⟩
  exact localBishopGromov_cross_of_isometricOn g g' hg' finrank_euclideanSpace_fin Ψ.symm
    hmetric p hκ hs hsR hball hsec

end Closed

/-- A13 with the errata constant `κ = w r₀³ V_{-Λ}(a) / (a³ V_{-Λ}(2R))`. -/
theorem A13_all_centre_volume_of_seed_explicit {r₀ w Λ R a : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hΛ : 0 ≤ Λ) (hR : r₀ ≤ R) (ha : 0 < a) (haR : a ≤ R) :
    0 < w * r₀ ^ 3 * modelVolume (-Λ) 3 a / (a ^ 3 * modelVolume (-Λ) 3 (2 * R)) ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X),
        ENNReal.ofReal (w * r₀ ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p r₀) →
        (∀ y ∈ riemannianBallOf g p (3 * R), SectionalBoundedBelowAt g y (-Λ)) →
        ∀ x ∈ riemannianClosedBallOf g p R,
          ENNReal.ofReal
              (w * r₀ ^ 3 * modelVolume (-Λ) 3 a / (a ^ 3 * modelVolume (-Λ) 3 (2 * R)) *
                a ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g x a) := by
  have hRpos : 0 < R := hr₀.trans_le hR
  have hm : ∀ r : ℝ, 0 < r → 0 < modelVolume (-Λ) 3 r := fun r hr =>
    modelVolume_pos (by norm_num) hr
      ⟨hr.le, fun hpos => (not_lt_of_ge (neg_nonpos.mpr hΛ) hpos).elim⟩
  have hma := hm a ha
  have hm2R := hm (2 * R) (by linarith)
  refine ⟨by positivity, ?_⟩
  intro X _ _ _ _ _ g p hseed hsec x hx
  -- the buffer: `B(x, 2R) ⊆ B(p, 3R)`
  have hsecx : ∀ q ∈ riemannianBallOf g x (2 * R), SectionalBoundedBelowAt g q (-Λ) := by
    intro q hq
    apply hsec q
    change riemannianEDistOf g p q < ENNReal.ofReal (3 * R)
    calc riemannianEDistOf g p q ≤ riemannianEDistOf g p x + riemannianEDistOf g x q :=
          riemannianEDistOf_triangle g p x q
      _ < ENNReal.ofReal R + ENNReal.ofReal (2 * R) :=
          ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx) hx hq
      _ = ENNReal.ofReal (3 * R) := by
          rw [← ENNReal.ofReal_add hRpos.le (by linarith)]
          ring_nf
  -- the seed ball: `B(p, r₀) ⊆ B(x, 2R)`
  have hseedsub : riemannianBallOf g p r₀ ⊆ riemannianBallOf g x (2 * R) := by
    intro y hy
    change riemannianEDistOf g x y < ENNReal.ofReal (2 * R)
    calc riemannianEDistOf g x y ≤ riemannianEDistOf g x p + riemannianEDistOf g p y :=
          riemannianEDistOf_triangle g x p y
      _ < ENNReal.ofReal R + ENNReal.ofReal r₀ := by
          rw [riemannianEDistOf_comm g x p]
          exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx) hx hy
      _ = ENNReal.ofReal (R + r₀) := (ENNReal.ofReal_add hRpos.le hr₀.le).symm
      _ ≤ ENNReal.ofReal (2 * R) := ENNReal.ofReal_le_ofReal (by linarith)
  have hcross := localBishopGromov_cross_of_compact_three g x hΛ ha (by linarith) hsecx
  have hvol2R : ENNReal.ofReal (w * r₀ ^ 3) ≤ ballVolume g x (2 * R) :=
    hseed.trans (MeasureTheory.measure_mono hseedsub)
  -- cancel `V(2R)`
  have hkey : ENNReal.ofReal (modelVolume (-Λ) 3 (2 * R)) *
      ENNReal.ofReal (w * r₀ ^ 3 * modelVolume (-Λ) 3 a /
        (a ^ 3 * modelVolume (-Λ) 3 (2 * R)) * a ^ 3) ≤
      ENNReal.ofReal (modelVolume (-Λ) 3 (2 * R)) * ballVolume g x a := by
    have heq : modelVolume (-Λ) 3 (2 * R) *
        (w * r₀ ^ 3 * modelVolume (-Λ) 3 a / (a ^ 3 * modelVolume (-Λ) 3 (2 * R)) * a ^ 3) =
        w * r₀ ^ 3 * modelVolume (-Λ) 3 a := by
      field_simp
    rw [← ENNReal.ofReal_mul hm2R.le, heq, ENNReal.ofReal_mul (by positivity)]
    calc ENNReal.ofReal (w * r₀ ^ 3) * ENNReal.ofReal (modelVolume (-Λ) 3 a)
        ≤ ballVolume g x (2 * R) * ENNReal.ofReal (modelVolume (-Λ) 3 a) := by gcongr
      _ ≤ ENNReal.ofReal (modelVolume (-Λ) 3 (2 * R)) * ballVolume g x a := hcross
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hm2R).ne'
    ENNReal.ofReal_ne_top).mp hkey

/-- A13 (I13 volume bridge, M): a seed volume at one ball and a sectional lower bound on the
buffer `B(p, 3R)` give a volume lower bound at every centre of `B̄(p, R)`, with `κ` chosen before
the manifold (the uniform shape of the `hvol` input of the local and ancient compactness
theorems).  No connectedness is assumed. -/
theorem A13_all_centre_volume_of_seed {r₀ w Λ R a : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hΛ : 0 ≤ Λ) (hR : r₀ ≤ R) (ha : 0 < a) (haR : a ≤ R) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace ThreeSpace X]
        [IsManifold ThreeModel ∞ X] [T2Space X] [CompactSpace X]
        (g : SmoothRiemannianMetric ThreeModel X) (p : X),
        ENNReal.ofReal (w * r₀ ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g p r₀) →
        (∀ y ∈ riemannianBallOf g p (3 * R),
          DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt g y (-Λ)) →
        ∀ x ∈ riemannianClosedBallOf g p R,
          ENNReal.ofReal (κ * a ^ 3) ≤
            Integral.Measure.riemannianVolumeMeasure ThreeModel X g (riemannianBallOf g x a) :=
  ⟨_, (A13_all_centre_volume_of_seed_explicit.{u} hr₀ hw hΛ hR ha haR).1,
    (A13_all_centre_volume_of_seed_explicit.{u} hr₀ hw hΛ hR ha haR).2⟩

end FILL910
