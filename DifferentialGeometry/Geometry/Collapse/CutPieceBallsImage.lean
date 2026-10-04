import DifferentialGeometry.Geometry.Collapse.CutPieceBalls
import DifferentialGeometry.Geometry.Comparison.BallCapture
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Metric.Distance.LocalBall
import DifferentialGeometry.Analysis.Integration.Measure.PullbackCross

/-!
# Cut pieces: intrinsic balls are ambient balls below the boundary distance (A7 CPI, T3)

Let `W = D.component i` be a piece of a torus decomposition of `M`, with a metric `h` induced by
a metric `g` on `M` (`isInducedCutMetric g D i h`, `Geometry/Collapse/LatePieceGeometry.lean:17`).
If `0 < r` and `r ≤ d_h(p, ∂W)`, then `cutPieceMap D i` (T3, `cutPieceMap_riemannianBallOf`)

* is injective on the `h`-ball `B_h(p, r)`,
* maps it onto the `g`-ball `B_g(cutPieceMap D i p, r)`,
* preserves distances between points of `B_h(p, r / 4)`,
* preserves the Riemannian volume of the ball.

The only hypothesis on the position of the ball is `r ≤ d_h(p, ∂W)`; nothing is assumed about
the seams of the decomposition.

## Route

The statements are first proved for an arbitrary partial diffeomorphism `Φ : N ⇀ M` between
manifolds with possibly different models which is isometric on a ball contained in its source,
with `N` compact (section `Isometric`); they are then applied to the partial diffeomorphism
`cutPiecePartialDiffeomorph D i` of T2, whose source is the interior of the piece and which
contains the ball by T1.

* Forward inclusion: `Φ` does not increase lengths of curves in its source
  (`KappaSolutions.edistOf_map_le_of_metric_upper_on_ball`,
  `Geometry/Metric/Comparison/PartialDiffeomorphDistance.lean:57`).
* Reverse inclusion, i.e. lifting a short `g`-curve: this is the first-exit argument of
  `PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower`
  (`Geometry/Comparison/BallCapture.lean:184`): a `g`-curve of length `< R` from `Φ p` cannot leave
  the `Φ`-image of the compact closed ball `B̄_h(p, R)` before its end, since its lift is no
  longer than the curve. Both lemmas are cross-model, so no boundarylessness of the piece is
  needed. This replicates `image_riemannianBall_eq_of_isometric_on_compact_ball`
  (`Geometry/Metric/Comparison/IsometricBalls.lean:53`, same model only).
* Distances on `B_h(p, r / 4)`: the upper bound is the buffered form of the length estimate
  (`..._on_buffered_ball`, which needs `3 · (r / 4) < r`); the lower bound applies the lifting
  argument around `x`, whose closed `5r/8`-ball still lies in `B_h(p, r)`, to `Φ y`, and uses
  injectivity of `Φ` on its source.
* Volume: `Integral.Measure.riemannianVolumeMeasure_image_of_partialIsometry`
  (`Analysis/Integration/Measure/PullbackCross.lean:217`) requires a boundaryless model on the
  domain only; it is applied to `Φ.symm`, whose domain is the ambient manifold.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Topology
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

/-! ## Partial diffeomorphisms that are isometric on a ball -/

section Isometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space N] in
private theorem closedBall_subset_ball {h : SmoothRiemannianMetric I N} {p : N} {R r : ℝ}
    (hR : 0 ≤ R) (hRr : R < r) :
    riemannianClosedBallOf h p R ⊆ riemannianBallOf h p r := fun _ hx =>
  lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (hR.trans_lt hRr)).mpr hRr)

omit [FiniteDimensional ℝ E] [T2Space N] in
private theorem pos_of_mem_riemannianBallOf {h : SmoothRiemannianMetric I N} {p x : N} {r : ℝ}
    (hx : x ∈ riemannianBallOf h p r) : 0 < r :=
  ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hx)

omit [FiniteDimensional ℝ E] [T2Space N] [FiniteDimensional ℝ F] [T2Space M] in
/-- A partial diffeomorphism that is isometric on a ball in its source does not increase the
distance from the centre of the ball. -/
theorem riemannianEDistOf_map_le_of_isometricOn (h : SmoothRiemannianMetric I N)
    (g : SmoothRiemannianMetric J M) (Φ : PartialDiffeomorph I J N M ∞) {p : N} {r : ℝ}
    (hsource : riemannianBallOf h p r ⊆ Φ.source)
    (hmetric : ∀ x ∈ riemannianBallOf h p r, ∀ v : TangentSpace I x,
      g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) = h.inner x v v)
    {x : N} (hx : x ∈ riemannianBallOf h p r) :
    riemannianEDistOf g (Φ p) (Φ x) ≤ riemannianEDistOf h p x := by
  have hr : 0 < r := pos_of_mem_riemannianBallOf hx
  have hlt : riemannianEDistOf h p x < ENNReal.ofReal r := hx
  have hfin : riemannianEDistOf h p x ≠ ⊤ := ne_top_of_lt hlt
  have hdr : (riemannianEDistOf h p x).toReal < r := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hd0 : 0 ≤ (riemannianEDistOf h p x).toReal := ENNReal.toReal_nonneg
  set R : ℝ := ((riemannianEDistOf h p x).toReal + r) / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRr : R < r := by rw [hRdef]; linarith
  have hxR : riemannianEDistOf h p x < ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr (by rw [hRdef]; linarith)
  have hsub := closedBall_subset_ball (h := h) (p := p) hRpos.le hRr
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    h g Φ p x hRpos one_pos (hsub.trans hsource)
    (fun z hz v => by rw [one_pow, one_mul, hmetric z (hsub hz) v]) hxR
  simpa only [ENNReal.ofReal_one, one_mul] using hle

omit [FiniteDimensional ℝ F] in
/-- Lifting short curves: a point of the ambient ball of radius `r` about `Φ p` lies in the
target of `Φ`, and its preimage lies in the ball of radius `r` about `p`. -/
theorem mem_target_and_symm_mem_riemannianBallOf_of_isometricOn [CompactSpace N]
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞) {p : N} {r : ℝ}
    (hsource : riemannianBallOf h p r ⊆ Φ.source)
    (hmetric : ∀ x ∈ riemannianBallOf h p r, ∀ v : TangentSpace I x,
      g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) = h.inner x v v)
    {y : M} (hy : y ∈ riemannianBallOf g (Φ p) r) :
    y ∈ Φ.target ∧ Φ.symm y ∈ riemannianBallOf h p r := by
  have hlt : riemannianEDistOf g (Φ p) y < ENNReal.ofReal r := hy
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt zero_le hlt)
  have hfin : riemannianEDistOf g (Φ p) y ≠ ⊤ := ne_top_of_lt hlt
  set s : ℝ := (riemannianEDistOf g (Φ p) y).toReal with hsdef
  have hsr : s < r := ENNReal.toReal_lt_of_lt_ofReal hlt
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  set R : ℝ := (s + r) / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hRr : R < r := by rw [hRdef]; linarith
  have hsub := closedBall_subset_ball (h := h) (p := p) hRpos.le hRr
  have hcpt : IsCompact (riemannianClosedBallOf h p R) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf h p R).isCompact
  have hy' : y ∈ riemannianClosedBallOf g (Φ p) s := by
    change riemannianEDistOf g (Φ p) y ≤ ENNReal.ofReal s
    rw [hsdef, ENNReal.ofReal_toReal hfin]
  obtain ⟨ht, hball⟩ := DifferentialGeometry.PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
    h g Φ p hs0 one_pos (by rw [one_mul, hRdef]; linarith) hcpt (hsub.trans hsource)
    (fun x hx v => by rw [one_pow, one_mul, hmetric x (hsub hx) v]) y hy'
  refine ⟨ht, ?_⟩
  rw [one_mul] at hball
  exact closedBall_subset_ball hs0 hsr hball

omit [FiniteDimensional ℝ F] in
/-- A partial diffeomorphism that is isometric on a ball contained in its source, from a compact
manifold, maps the ball onto the ball of the same radius about the image of the centre. -/
theorem image_riemannianBallOf_eq_of_isometricOn [CompactSpace N]
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞) {p : N} {r : ℝ}
    (hsource : riemannianBallOf h p r ⊆ Φ.source)
    (hmetric : ∀ x ∈ riemannianBallOf h p r, ∀ v : TangentSpace I x,
      g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) = h.inner x v v) :
    Φ '' riemannianBallOf h p r = riemannianBallOf g (Φ p) r := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact lt_of_le_of_lt (riemannianEDistOf_map_le_of_isometricOn h g Φ hsource hmetric hx) hx
  · intro y hy
    obtain ⟨ht, hball⟩ :=
      mem_target_and_symm_mem_riemannianBallOf_of_isometricOn h g Φ hsource hmetric hy
    exact ⟨Φ.symm y, hball, Φ.right_inv' ht⟩

omit [FiniteDimensional ℝ E] [T2Space N] in
private theorem closedBall_subset_ball_of_mem_quarter {h : SmoothRiemannianMetric I N}
    {p x : N} {r ρ : ℝ} (hρ : 0 ≤ ρ) (hρr : r / 4 + ρ ≤ r)
    (hx : x ∈ riemannianBallOf h p (r / 4)) :
    riemannianClosedBallOf h x ρ ⊆ riemannianBallOf h p r := by
  intro z hz
  have hr : 0 < r / 4 := pos_of_mem_riemannianBallOf hx
  have hxz : riemannianEDistOf h x z ≤ ENNReal.ofReal ρ := hz
  have hpx : riemannianEDistOf h p x < ENNReal.ofReal (r / 4) := hx
  change riemannianEDistOf h p z < ENNReal.ofReal r
  calc riemannianEDistOf h p z ≤ riemannianEDistOf h p x + riemannianEDistOf h x z :=
        riemannianEDistOf_triangle h p x z
    _ < ENNReal.ofReal (r / 4) + ENNReal.ofReal ρ :=
        ENNReal.add_lt_add_of_lt_of_le (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hxz) hpx hxz
    _ = ENNReal.ofReal (r / 4 + ρ) := (ENNReal.ofReal_add hr.le hρ).symm
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hρr

omit [FiniteDimensional ℝ F] in
/-- A partial diffeomorphism that is isometric on a ball `B(p, r)` contained in its source, from
a compact manifold, preserves the distance between any two points of `B(p, r / 4)`. -/
theorem riemannianEDistOf_map_eq_of_isometricOn [CompactSpace N]
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞) {p : N} {r : ℝ}
    (hsource : riemannianBallOf h p r ⊆ Φ.source)
    (hmetric : ∀ x ∈ riemannianBallOf h p r, ∀ v : TangentSpace I x,
      g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x v) = h.inner x v v)
    {x y : N} (hx : x ∈ riemannianBallOf h p (r / 4)) (hy : y ∈ riemannianBallOf h p (r / 4)) :
    riemannianEDistOf g (Φ x) (Φ y) = riemannianEDistOf h x y := by
  have hr4 : 0 < r / 4 := pos_of_mem_riemannianBallOf hx
  have hr : 0 < r := by linarith
  have hsub : riemannianClosedBallOf h p (7 * r / 8) ⊆ riemannianBallOf h p r :=
    closedBall_subset_ball (by linarith) (by linarith)
  have hx' : x ∈ riemannianClosedBallOf h p (r / 4) :=
    le_of_lt (show riemannianEDistOf h p x < ENNReal.ofReal (r / 4) from hx)
  have hy' : y ∈ riemannianClosedBallOf h p (r / 4) :=
    le_of_lt (show riemannianEDistOf h p y < ENNReal.ofReal (r / 4) from hy)
  have hle : riemannianEDistOf g (Φ x) (Φ y) ≤ riemannianEDistOf h x y := by
    have h0 := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      h g Φ p x y hr4.le (by linarith) one_pos (hsub.trans hsource)
      (fun z hz v => by rw [one_pow, one_mul, hmetric z (hsub hz) v]) hx' hy'
    simpa only [ENNReal.ofReal_one, one_mul] using h0
  refine le_antisymm hle ?_
  -- the distance of `x` and `y` is below `r / 2`
  have hxy : riemannianEDistOf h x y < ENNReal.ofReal (r / 2) := by
    have hxp : riemannianEDistOf h x p < ENNReal.ofReal (r / 4) := by
      rw [riemannianEDistOf_comm]
      exact hx
    calc riemannianEDistOf h x y ≤ riemannianEDistOf h x p + riemannianEDistOf h p y :=
          riemannianEDistOf_triangle h x p y
      _ < ENNReal.ofReal (r / 4) + ENNReal.ofReal (r / 4) :=
          ENNReal.add_lt_add hxp hy
      _ = ENNReal.ofReal (r / 2) := by
          rw [← ENNReal.ofReal_add hr4.le hr4.le]
          congr 1
          ring
  have hglt : riemannianEDistOf g (Φ x) (Φ y) < ENNReal.ofReal (r / 2) := lt_of_le_of_lt hle hxy
  have hfin : riemannianEDistOf g (Φ x) (Φ y) ≠ ⊤ := ne_top_of_lt hglt
  set s : ℝ := (riemannianEDistOf g (Φ x) (Φ y)).toReal with hsdef
  have hs0 : 0 ≤ s := ENNReal.toReal_nonneg
  have hsr : s < r / 2 := ENNReal.toReal_lt_of_lt_ofReal hglt
  have hsubx : riemannianClosedBallOf h x (5 * r / 8) ⊆ riemannianBallOf h p r :=
    closedBall_subset_ball_of_mem_quarter (by linarith) (by linarith) hx
  have hcpt : IsCompact (riemannianClosedBallOf h x (5 * r / 8)) :=
    (Geometry.Metric.isClosed_riemannianClosedBallOf h x _).isCompact
  have hΦy : Φ y ∈ riemannianClosedBallOf g (Φ x) s := by
    change riemannianEDistOf g (Φ x) (Φ y) ≤ ENNReal.ofReal s
    rw [hsdef, ENNReal.ofReal_toReal hfin]
  obtain ⟨-, hball⟩ := DifferentialGeometry.PartialDiffeomorph.symm_mem_riemannianClosedBall_of_metric_lower
    h g Φ x hs0 one_pos (by rw [one_mul]; linarith) hcpt (hsubx.trans hsource)
    (fun z hz v => by rw [one_pow, one_mul, hmetric z (hsubx hz) v]) (Φ y) hΦy
  have hyx : y ∈ riemannianBallOf h p r := closedBall_subset_ball hr4.le (by linarith) hy'
  have hyy : Φ.symm (Φ y) = y := Φ.left_inv' (hsource hyx)
  rw [hyy, one_mul] at hball
  change riemannianEDistOf h x y ≤ ENNReal.ofReal s at hball
  rwa [hsdef, ENNReal.ofReal_toReal hfin] at hball

private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- `Φ` regarded as a partial diffeomorphism of class `C¹`. -/
private def levelOne {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace G Y]
    (Φ : PartialDiffeomorph I J X Y ∞) : PartialDiffeomorph I J X Y 1 where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le (by norm_num)
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le (by norm_num)

/-- A partial diffeomorphism into a manifold with boundaryless model, isometric on its source,
preserves the Riemannian volume of open subsets of its source. -/
theorem riemannianVolumeMeasure_image_eq_of_isometricOn [J.Boundaryless]
    [SigmaCompactSpace N] [SigmaCompactSpace M]
    (h : SmoothRiemannianMetric I N) (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞)
    (hmetric : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I x,
      h.inner x v w = g.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w))
    {A : Set N} (hA : IsOpen A) (hAs : A ⊆ Φ.source) :
    Integral.Measure.riemannianVolumeMeasure I N h A =
      Integral.Measure.riemannianVolumeMeasure J M g (Φ '' A) := by
  have hmd : Φ.toOpenPartialHomeomorph.MDifferentiable I J :=
    ⟨Φ.contMDiffOn_toFun.mdifferentiableOn (by simp),
      Φ.contMDiffOn_invFun.mdifferentiableOn (by simp)⟩
  have hsymm : ∀ y ∈ (levelOne Φ.symm).source, ∀ v w : TangentSpace J y,
      g.inner y v w = h.inner (levelOne Φ.symm y)
        (mfderiv J I (levelOne Φ.symm) y v) (mfderiv J I (levelOne Φ.symm) y w) := by
    intro y hy v w
    change y ∈ Φ.target at hy
    have hx : Φ.symm y ∈ Φ.source := Φ.map_target' hy
    have hd := hmd.comp_symm_deriv hy
    have hv : mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y v) = v :=
      congrArg (fun L => L v) hd
    have hw : mfderiv I J Φ (Φ.symm y) (mfderiv J I Φ.symm y w) = w :=
      congrArg (fun L => L w) hd
    change g.inner y v w = h.inner (Φ.symm y)
      (mfderiv J I Φ.symm y v) (mfderiv J I Φ.symm y w)
    have hxy : Φ.toPartialEquiv (Φ.symm.toPartialEquiv y) = y := Φ.right_inv' hy
    rw [hmetric _ hx, hv, hw, hxy]
  have himage : IsOpen (Φ '' A) := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hA hAs
  have hvol := Integral.Measure.riemannianVolumeMeasure_image_of_partialIsometry g h
    (levelOne Φ.symm) hsymm himage.measurableSet
    (by rintro _ ⟨x, hx, rfl⟩; exact Φ.map_source' (hAs hx))
  have hback : (levelOne Φ.symm) '' (Φ '' A) = A := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      have hzz : Φ.symm (Φ z) = z := Φ.left_inv' (hAs hz)
      change Φ.symm (Φ z) ∈ A
      rwa [hzz]
    · intro hx
      exact ⟨Φ x, ⟨x, hx, rfl⟩, Φ.left_inv' (hAs hx)⟩
  rw [hvol, hback]

end Isometric

/-! ## T3 for cut pieces -/

section CutPiece

variable {M : ConnectedClosedOrientedManifold.{u} 3}

/-- Below the boundary distance the `h`-ball lies in the source of the cut-piece partial
diffeomorphism. -/
theorem riemannianBallOf_subset_cutPiecePartialDiffeomorph_source (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    riemannianBallOf h p r ⊆ (cutPiecePartialDiffeomorph D i).source :=
  riemannianBallOf_subset_interior (D.component i) h hd

private theorem cutPiece_isometric (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (x : (D.component i).Carrier)
    (v : TangentSpace (D.component i).model x) :
    g.inner (cutPiecePartialDiffeomorph D i x)
        (mfderiv (D.component i).model (𝓡 3) (cutPiecePartialDiffeomorph D i) x v)
        (mfderiv (D.component i).model (𝓡 3) (cutPiecePartialDiffeomorph D i) x v) =
      h.inner x v v :=
  (hind x v v).symm

/-- T3 (injectivity). Below the boundary distance the cut-piece map is injective on the
`h`-ball. -/
theorem injOn_cutPieceMap_riemannianBallOf (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    Set.InjOn (cutPieceMap D i) (riemannianBallOf h p r) :=
  (injOn_cutPieceMap_interior D i).mono (riemannianBallOf_subset_interior (D.component i) h hd)

/-- T3 (balls). Below the boundary distance the cut-piece map sends the `h`-ball onto the
`g`-ball of the same radius. -/
theorem image_cutPieceMap_riemannianBallOf (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    cutPieceMap D i '' riemannianBallOf h p r = riemannianBallOf g (cutPieceMap D i p) r :=
  image_riemannianBallOf_eq_of_isometricOn h g (cutPiecePartialDiffeomorph D i)
    (riemannianBallOf_subset_cutPiecePartialDiffeomorph_source D i h hd)
    (fun x _ v => cutPiece_isometric g D i h hind x v)

/-- T3 (distances). Below the boundary distance the cut-piece map preserves the distance between
points of the `h`-ball of a quarter of the radius. -/
theorem riemannianEDistOf_cutPieceMap_eq (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p)
    {x y : (D.component i).Carrier} (hx : x ∈ riemannianBallOf h p (r / 4))
    (hy : y ∈ riemannianBallOf h p (r / 4)) :
    riemannianEDistOf g (cutPieceMap D i x) (cutPieceMap D i y) = riemannianEDistOf h x y :=
  riemannianEDistOf_map_eq_of_isometricOn h g (cutPiecePartialDiffeomorph D i)
    (riemannianBallOf_subset_cutPiecePartialDiffeomorph_source D i h hd)
    (fun z _ v => cutPiece_isometric g D i h hind z v) hx hy

/-- T3 (volume). Below the boundary distance the `h`-ball and the `g`-ball of the same radius
have the same Riemannian volume. -/
theorem riemannianVolumeMeasure_cutPieceMap_riemannianBallOf
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier)
    (D : TorusDecomposition M) (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) {p : (D.component i).Carrier} {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    Integral.Measure.riemannianVolumeMeasure _ _ h (riemannianBallOf h p r) =
      Integral.Measure.riemannianVolumeMeasure _ _ g
        (riemannianBallOf g (cutPieceMap D i p) r) := by
  rw [← image_cutPieceMap_riemannianBallOf g D i h hind hd]
  exact riemannianVolumeMeasure_image_eq_of_isometricOn h g (cutPiecePartialDiffeomorph D i)
    (fun x _ v w => hind x v w)
    (isOpen_lt (Geometry.Riemannian.continuous_riemannianEDist h p) continuous_const)
    (riemannianBallOf_subset_cutPiecePartialDiffeomorph_source D i h hd)

/-- T3 (plan statement). Let `h` be the metric induced on the cut piece by `g`. Below the
distance to the boundary of the piece, the cut-piece map is injective on the intrinsic ball,
maps it onto the ambient ball of the same radius, preserves distances on the ball of a quarter
of the radius, and preserves the volume of the ball. -/
theorem cutPieceMap_riemannianBallOf
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (D : TorusDecomposition M)
    (i : Fin D.components.count)
    (h : SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (hind : isInducedCutMetric g D i h) (p : (D.component i).Carrier) {r : ℝ}
    (hd : ENNReal.ofReal r ≤ distanceToBoundary (D.component i) h p) :
    Set.InjOn (cutPieceMap D i) (riemannianBallOf h p r) ∧
    cutPieceMap D i '' riemannianBallOf h p r = riemannianBallOf g (cutPieceMap D i p) r ∧
    (∀ x ∈ riemannianBallOf h p (r / 4), ∀ y ∈ riemannianBallOf h p (r / 4),
      riemannianEDistOf g (cutPieceMap D i x) (cutPieceMap D i y) = riemannianEDistOf h x y) ∧
    DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure _ _ h (riemannianBallOf h p r) =
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure _ _ g
        (riemannianBallOf g (cutPieceMap D i p) r) :=
  ⟨injOn_cutPieceMap_riemannianBallOf D i h hd, image_cutPieceMap_riemannianBallOf g D i h hind hd,
    fun _ hx _ hy => riemannianEDistOf_cutPieceMap_eq g D i h hind hd hx hy,
    riemannianVolumeMeasure_cutPieceMap_riemannianBallOf g D i h hind hd⟩

end CutPiece

end DifferentialGeometry.Geometry.Collapse
