import DifferentialGeometry.Geometry.Neck.SpatialMinimizer
import DifferentialGeometry.Geometry.Neck.SpatialFixedRecentering
import DifferentialGeometry.Geometry.Neck.SpatialTolerance
import DifferentialGeometry.Geometry.Neck.PointedEndpoint
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckRestriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PointedPinchingLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarRay
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalPinching
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal Topology NNReal

universe u

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {g : SmoothRiemannianMetric I3 M} {eps C1 C2 alpha : ℝ} {x : M}

theorem SpatialCanonicalWitness.nonempty_spatialNeck_of_minimizing_segment
    (W : SpatialCanonicalWitness g eps C1 C2 x) (hW : W.capTubeHasNeckChart eps)
    (halpha : alpha < 1 / 11) (heps : 13000 * (13000 * eps) ≤ alpha)
    {γ : ℝ → M} {a t b : ℝ} (hat : a < t) (htb : t < b)
    (hmin : ∀ s ∈ Icc a b, ∀ u ∈ Icc a b,
      riemannianEDistOf g (γ s) (γ u) = ENNReal.ofReal |s - u|)
    (hx : γ t = x) (hleft : C2 * metricScalarAt g (γ a) < metricScalarAt g x)
    (hright : C2 * metricScalarAt g x < metricScalarAt g (γ b)) :
    Nonempty (SpatialNeck g alpha x) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hepspos := W.eps_pos
  have hnotA : γ a ∉ W.domain.carrier := by
    intro h
    have hlow := mul_le_mul_of_nonneg_left (W.scalar_bounds _ h).1 hC2.le
    rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hlow
    linarith
  have hnotB : γ b ∉ W.domain.carrier := by
    intro h
    linarith [(W.scalar_bounds _ h).2]
  have hcomp : γ a ∈ connectedComponent x := by
    have hball : γ a ∈ {y : M | riemannianEDistOf g x y < ENNReal.ofReal (|t - a| + 1)} := by
      change riemannianEDistOf g x (γ a) < _
      rw [← hx, hmin t ⟨hat.le, htb.le⟩ a ⟨le_rfl, (hat.trans htb).le⟩]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (lt_add_one _)
    exact Geometry.Metric.edistOf_ball_subset_connCompOpen g x _ hball
  cases halt : W.alternative with
  | neck data => exact ⟨data.neck.mono (by linarith) halpha⟩
  | cap data deep =>
    obtain ⟨v, nk, hmap⟩ := hW data deep halt
    have hα₁ : 13000 * eps < 1 / 11 := by linarith
    have hshift : |(-1 / 2 : ℝ)| * eps ≤ 1 / 2 := by
      rw [abs_of_neg (by norm_num)]
      linarith [nk.eps_small]
    obtain ⟨out, _, hout⟩ := nk.exists_at_coordinate_of_tolerance hα₁ le_rfl nk.center hshift
    have hfront : frontier data.core.carrier =
        range (fun z : Sphere 2 => out.map (z, 1 / 2)) := by
      rw [← data.inner_boundary]
      ext y
      constructor
      · rintro ⟨⟨z, w⟩, ⟨_, hw⟩, rfl⟩
        refine ⟨z, ?_⟩
        have hw0 : w = 0 := hw
        dsimp only
        rw [nk.translated_map_apply nk.center out hout, hmap, hw0]
        norm_num
      · rintro ⟨z, rfl⟩
        refine ⟨(z, 0), ⟨mem_univ _, rfl⟩, ?_⟩
        dsimp only
        rw [nk.translated_map_apply nk.center out hout, hmap]
        norm_num
    have hcoreU : data.core.carrier ⊆ W.domain.carrier := fun y hy => by
      have h := data.union_eq
      exact h ▸ (subset_union_left hy : y ∈ data.core.carrier ∪ data.tube)
    obtain ⟨N⟩ := out.exists_at_minimizing_point_of_frontier_eq_slice halpha heps hfront hat htb
      hmin (fun h => hnotA (hcoreU (interior_subset h)))
      (fun h => hnotB (hcoreU (interior_subset h))) (hx ▸ data.center_inside)
    exact ⟨hx ▸ N⟩
  | positive whole _ _ => exact absurd (whole ▸ hcomp) hnotA
  | round whole _ => exact absurd (whole ▸ hcomp) hnotA

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


variable {P : OrientedThreeStage.{u}} {a b : ℝ}

private local instance (A : P.ClosedSlab a b) :
    SigmaCompactSpace (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen.isOpen)

theorem ClosedSlab.nonempty_scaled_spatialNeck_of_minimizing_segment (A : P.ClosedSlab a b)
    {eps C1 C2 alpha q Q : ℝ} (hQ : 0 < Q) (halpha : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤ alpha)
    (hW : ∀ y, q < A.flow.scalar b y →
      ∃ W : SpatialCanonicalWitness (A.flow.base.metric b) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {γ : ℝ → (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen} {l t r : ℝ}
    (hlt : l < t) (htr : t < r)
    (hmin : ∀ s ∈ Icc l r, ∀ v ∈ Icc l r, riemannianEDistOf
      (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric) (γ s) (γ v) =
        ENNReal.ofReal |s - v|)
    (hq : q < A.flow.scalar b (γ t).val)
    (hleft : C2 * A.flow.scalar b (γ l).val < A.flow.scalar b (γ t).val)
    (hright : C2 * A.flow.scalar b (γ t).val < A.flow.scalar b (γ r).val) :
    Nonempty (SpatialNeck (scaleMetric Q hQ (A.endpointTerminalLimitMetric P).metric)
      alpha (γ t)) := by
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let γc : ℝ → P.Carrier := fun v => (γ (Real.sqrt Q * v)).val
  have hmem (v : ℝ) (hv : v ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q)) :
      Real.sqrt Q * v ∈ Icc l r := by
    constructor
    · have := (div_le_iff₀ hs).mp hv.1
      linarith
    · have := (le_div_iff₀ hs).mp hv.2
      linarith
  have hmin' : ∀ s ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q),
      ∀ v ∈ Icc (l / Real.sqrt Q) (r / Real.sqrt Q),
        riemannianEDistOf (A.flow.base.metric b) (γc s) (γc v) = ENNReal.ofReal |s - v| := by
    intro s hsI v hvI
    have h := hmin _ (hmem s hsI) _ (hmem v hvI)
    rw [DifferentialGeometry.edistOf_scale, A.riemannianEDistOf_endpointTerminalLimitMetric,
      ← mul_sub, abs_mul, abs_of_pos hs, ENNReal.ofReal_mul hs.le] at h
    exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hs).ne' ENNReal.ofReal_ne_top).mp h
  have hts : Real.sqrt Q * (t / Real.sqrt Q) = t := mul_div_cancel₀ t hs.ne'
  have hls : Real.sqrt Q * (l / Real.sqrt Q) = l := mul_div_cancel₀ l hs.ne'
  have hrs : Real.sqrt Q * (r / Real.sqrt Q) = r := mul_div_cancel₀ r hs.ne'
  obtain ⟨W, hWn⟩ := hW (γ t).val hq
  obtain ⟨nk⟩ := W.nonempty_spatialNeck_of_minimizing_segment hWn halpha heps
    (a := l / Real.sqrt Q) (t := t / Real.sqrt Q) (b := r / Real.sqrt Q) (γ := γc)
    (div_lt_div_of_pos_right hlt hs) (div_lt_div_of_pos_right htr hs) hmin'
    (by simp only [γc, hts]) (by simp only [γc, hls]; exact hleft)
    (by simp only [γc, hrs]; exact hright)
  have hU : (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion = univ :=
    A.terminalRegularRegion_eq_univ P
  exact ⟨(nk.restrictOpen (U := (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularOpen)
    (x := γ t) (fun y _ => by
      change y ∈ (A.restrictIncoming le_rfl A.lt le_rfl).terminalRegularRegion
      rw [hU]
      trivial)).scaleMetric Q hQ⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn


attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

private theorem eventually_scalar_le_on_inner_ball_of_pointed_convergence
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {L : PointedRiemannianManifold.{u, 0, 0} ThreeModel} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f) (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ} (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf L.metric L.basepoint R))
    {R : ℝ} (hR : 0 < R) (hRrho : R < rho) :
    ∃ B : ℝ, ∀ᶠ n in atTop, ∀ y : (X.obj (f n)).M,
      riemannianEDistOf (X.obj (f n)).metric (X.obj (f n)).basepoint y < ENNReal.ofReal R →
        metricScalarAt (X.obj (f n)).metric y ≤ B := by
  let R' := (R + rho) / 2
  let factor := (R + R') / (2 * R)
  have hRR' : R < R' := by dsimp only [R']; linarith
  have hfactor : 1 < factor := by
    dsimp only [factor]
    rw [lt_div_iff₀ (by positivity)]
    linarith
  have hbuffer : factor * R < R' := by
    have heq : factor * R = (R + R') / 2 := by dsimp only [factor]; field_simp
    rw [heq]
    linarith
  have hK := hcompact R' (by dsimp only [R']; linarith) (by dsimp only [R']; linarith)
  have hconv : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
      (riemannianClosedBallOf L.metric L.basepoint R') 0 := by
    have heq : M.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
    rw [← heq]
    exact M.converges _ hK 0
  obtain ⟨B, _, hB⟩ := Perelman.KappaSolutions.exists_pointed_scalar_bound_on_compact M
    hcanonical _ hK
  refine ⟨B, ?_⟩
  filter_upwards [pointed_metric_eventually_inverse_ball_capture L.basepoint hR.le hfactor
    hbuffer hK hconv, hB] with n hn hb
  intro y hy
  have hy' : y ∈ riemannianClosedBallOf (X.obj (f n)).metric (F.map n L.basepoint) R := by
    change y ∈ riemannianClosedBallOf (X.obj (f n)).metric ((F.partialDiffeomorph n) L.basepoint) R
    rw [F.basepoint_map]
    exact hy.le
  obtain ⟨_, _, hin, heq⟩ := hn.2 y hy'
  have hmem : (F.partialDiffeomorph n).symm y ∈ riemannianClosedBallOf L.metric L.basepoint R' :=
    riemannianClosedBallOf_mono _ _ hbuffer.le hin
  have h := hb.2 _ hmem
  rw [heq] at h
  exact (le_abs_self _).trans h

theorem exists_isometric_ray_with_spatialNecks_of_scalar_escape
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (Ctime Cgrad : ℝ≥0) (q : ℕ → ℝ)
    (htime : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      |derivWithin (fun v => (A i).flow.scalar v y) (Iic t) t| ≤
        Ctime * (A i).flow.scalar t y ^ 2)
    (hgradient : ∀ i y, ∀ t ∈ Ioo (a i) (s i), q i < (A i).flow.scalar t y →
      ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential
            ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow t y v| ≤
          Cgrad * (A i).flow.scalar t y * Real.sqrt ((A i).flow.scalar t y) *
            Real.sqrt (((A i).flow.base.metric t).inner y v v))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    (hqQ : ∀ i, q i ≤ (A i).flow.scalar (s i) (x i).val)
    (hqlim : Tendsto (fun i => q i / (A i).flow.scalar (s i) (x i).val) atTop (𝓝 0))
    {eps C1 C2 alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1 / 11)
    (heps : 13000 * (13000 * eps) ≤
      min (neckModelTolerance (alpha / 26000)) ((alpha / 26000) / 64))
    (hW : ∀ i y, q i < (A i).flow.scalar (s i) y →
      ∃ W : SpatialCanonicalWitness ((A i).flow.base.metric (s i)) eps C1 C2 y,
        W.capTubeHasNeckChart eps)
    {rho : ℝ} (hrho : 0 < rho) (f : ℕ → ℕ) (hf : StrictMono f)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 rho))
    (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hradial : ∀ z : Pl.M, riemannianEDistOf Pl.metric Pl.basepoint z < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho →
      IsCompact (riemannianClosedBallOf Pl.metric Pl.basepoint R))
    (hcapture : ∀ n, riemannianClosedBallOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (r n) ⊆ F.target n)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y ∈ F.source n, ∀ v : TangentSpace ThreeModel y,
      (1 - ε) * Pl.metric.inner y v v ≤
        (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
          (zero_lt_one.trans_le (hQ (f n)))
          ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric).inner (F.map n y)
          (mfderiv ThreeModel ThreeModel (F.map n) y v)
          (mfderiv ThreeModel ThreeModel (F.map n) y v))
    (z : ∀ n, ((A (f n)).restrictIncoming le_rfl (A (f n)).lt le_rfl).terminalRegularOpen)
    (hfinite : ∀ n, riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n) ≠ ⊤)
    (hdist : Tendsto (fun n => (riemannianEDistOf
      (scaleMetric ((A (f n)).flow.scalar (s (f n)) (x (f n)).val)
        (zero_lt_one.trans_le (hQ (f n))) ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric)
      (x (f n)) (z n)).toReal) atTop (𝓝 rho))
    (hhigh : Tendsto (fun n => metricScalarAt
      ((A (f n)).endpointTerminalLimitMetric (P (f n))).metric (z n) /
        (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    let _ : EMetricSpace Pl.M := Pl.emetricSpace
    ∃ g : C(Ico 0 rho, Pl.M), Isometry g ∧ g ⟨0, le_rfl, hrho⟩ = Pl.basepoint ∧
      Tendsto (fun t => metricScalarAt Pl.metric (g t))
        (comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho)) atTop ∧
      ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho),
        Nonempty (SpatialNeck Pl.metric alpha (g t)) := by
  intro _
  let G := fun i => (A i).restrictIncoming le_rfl (A i).lt le_rfl
  let L := fun i => (A i).endpointTerminalLimitMetric (P i)
  let Q := fun i => (A i).flow.scalar (s i) (x i).val
  have hQpos : ∀ i, 0 < Q i := fun i => zero_lt_one.trans_le (hQ i)
  have hLscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (L i).metric y = (A i).flow.scalar (s i) y.val :=
    metricScalarAt_restrictOpen _ _ _
  have hXscalar (i : ℕ) (y : (G i).terminalRegularOpen) :
      metricScalarAt (scaleMetric (Q i) (hQpos i) (L i).metric) y =
        metricScalarAt (L i).metric y / Q i := by
    rw [metricScalarAt_scaleMetric, inv_mul_eq_div]
  have hinner : ∀ R : ℝ, 0 < R → R < rho → ∃ B : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G (f n)).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q (f n)) (hQpos (f n)) (L (f n)).metric)
          (x (f n)) y < ENNReal.ofReal R →
            metricScalarAt (L (f n)).metric y / Q (f n) ≤ B := by
    intro R hR hRrho
    obtain ⟨B, hB⟩ :=
      eventually_scalar_le_on_inner_ball_of_pointed_convergence F M hcanonical hcompact hR hRrho
    refine ⟨B, hB.mono fun n hn y hy => ?_⟩
    rw [← hXscalar]
    exact hn y hy
  obtain ⟨κ₁, hκ₁, A', ell, y, γ, _, hAlim, helllim, _, hy, _, _, hends, _, _, _, hmin,
      φ, g, hφ, hg, hgbase, hconv, _, hscalar, _, _, hblowup⟩ :=
    exists_isometric_terminal_scalar_blowup_curve_of_scalar_escape P a s G L Q hQpos q 1
      (Eventually.of_forall fun i => by simpa only [one_mul] using hqQ i) Cgrad hgradient x Pl
      f hf F M hcanonical hrho r hr hrlim
      (fun n y hy => hcapture n (show riemannianEDistOf _ _ y ≤ _ from le_of_lt hy)) hlower
      hcompact hradial (fun _ => Ctime)
      (fun i y t ht hy => htime i y t ht ((hqQ i).trans_lt hy))
      (fun i => (hLscalar i (x i)).le) z hfinite hdist hhigh hinner
  refine ⟨g, hg, hgbase, hblowup, ?_⟩
  have hsub : StrictMono (fun n => f (κ₁ (φ n))) := hf.comp (hκ₁.comp hφ)
  have hqsub := hqlim.comp hsub.tendsto_atTop
  have hpos : ∀ᶠ t : Ico 0 rho in comap (Subtype.val : Ico 0 rho → ℝ) (𝓝 rho), 0 < (t : ℝ) :=
    (tendsto_comap : Tendsto (Subtype.val : Ico 0 rho → ℝ) _ (𝓝 rho)).eventually
      (eventually_gt_nhds hrho)
  filter_upwards [hblowup.eventually_gt_atTop (max 2 (C2 + 1)), hpos] with τ hτ hτpos
  let F2 := (F.compSubseq κ₁ hκ₁).compSubseq φ hφ
  let M2 := (M.compSubseq κ₁ hκ₁).compSubseq φ hφ
  have hcanonical2 (n : ℕ) :
      M2.domain n = CanonicalMetricCompactness.canonicalSourceData F2 n := by
    change ((M.domain (κ₁ (φ n))).compSubseq κ₁ hκ₁ (φ n)).compSubseq φ hφ n = _
    rw [hcanonical (κ₁ (φ n))]
    rfl
  have hRτ : Tendsto (fun n => metricScalarAt (L (f (κ₁ (φ n)))).metric (γ (φ n) τ) /
      Q (f (κ₁ (φ n)))) atTop (𝓝 (metricScalarAt Pl.metric (g τ))) := hscalar τ
  have hellτ : ∀ᶠ n in atTop, (τ : ℝ) < ell (φ n) :=
    (helllim.comp hφ.tendsto_atTop).eventually (eventually_gt_nhds τ.property.2)
  have hbig := hRτ.eventually (eventually_gt_nhds hτ)
  have hsmallq := hqsub.eventually (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))
  have hAbig := (hAlim.comp hφ.tendsto_atTop).eventually_gt_atTop
    (C2 * (metricScalarAt Pl.metric (g τ) + 1))
  have hRτup := hRτ.eventually (eventually_lt_nhds (lt_add_one (metricScalarAt Pl.metric (g τ))))
  apply nonempty_spatial_neck_at_limit_of_endpoint_blowup M2 hcanonical2 halpha halpha1
    (fun n => γ (φ n) τ) (fun n => γ (φ n) (ell (φ n))) (g τ) τ.property.1 τ.property.2
    hcompact ((le_max_left _ _).trans_lt hτ)
    ((hconv {τ} isCompact_singleton).tendsto_at (mem_singleton τ)) ?_ (fun n => ell (φ n))
    (helllim.comp hφ.tendsto_atTop) ?_ ?_ ?_
  · refine (hAlim.comp hφ.tendsto_atTop).congr fun n => ?_
    change A' (φ n) = metricScalarAt (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (γ (φ n) (ell (φ n)))
    rw [hXscalar, (hends (φ n)).2, hy]
  · filter_upwards [hellτ] with n hn
    change riemannianEDistOf (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (γ (φ n) τ) (γ (φ n) (ell (φ n))) ≤ _
    rw [hmin (φ n) τ ⟨τ.property.1, hn.le⟩ (ell (φ n)) ⟨τ.property.1.trans hn.le, le_rfl⟩,
      abs_sub_comm, abs_of_pos (sub_pos.mpr hn)]
  · filter_upwards [hellτ] with n hn
    change riemannianEDistOf (scaleMetric (Q (f (κ₁ (φ n)))) (hQpos _)
      (L (f (κ₁ (φ n)))).metric) (x (f (κ₁ (φ n)))) _ ≤ _
    rw [← (hends (φ n)).1, hmin (φ n) 0 ⟨le_rfl, τ.property.1.trans hn.le⟩ τ
      ⟨τ.property.1, hn.le⟩, zero_sub, abs_neg, abs_of_nonneg τ.property.1]
  · filter_upwards [hellτ, hbig, hsmallq, hAbig, hRτup] with n hn hnbig hnq hnA hnup
    have hQi : 0 < (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val :=
      hQpos _
    have hRt : metricScalarAt (L (f (κ₁ (φ n)))).metric (γ (φ n) τ) =
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := hLscalar _ _
    have hRe : metricScalarAt (L (f (κ₁ (φ n)))).metric (y (φ n)) =
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (y (φ n)).val := hLscalar _ _
    have h1 : max 2 (C2 + 1) *
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      rw [← hRt]
      exact (lt_div_iff₀ hQi).mp hnbig
    have h2 : q (f (κ₁ (φ n))) <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val := by
      have hh := (div_lt_iff₀ hQi).mp hnq
      linarith
    have h3 : (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val <
        (metricScalarAt Pl.metric (g τ) + 1) *
          (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val := by
      rw [← hRt]
      exact (div_lt_iff₀ hQi).mp hnup
    have h4 : C2 * (metricScalarAt Pl.metric (g τ) + 1) *
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (y (φ n)).val := by
      rw [← hRe]
      have hh := hy (φ n)
      rw [div_eq_iff hQi.ne'] at hh
      rw [hh]
      exact mul_lt_mul_of_pos_right hnA hQi
    have hm2 := le_max_left (2 : ℝ) (C2 + 1)
    have hmC := le_max_right (2 : ℝ) (C2 + 1)
    have hq : q (f (κ₁ (φ n))) <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      nlinarith
    obtain ⟨W0, _⟩ := hW _ _ hq
    have hC2pos : 0 ≤ C2 := zero_le_one.trans W0.one_le_comparison_constant
    have hleft : C2 * (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) 0).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val := by
      rw [(hends (φ n)).1]
      nlinarith
    have hright : C2 * (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) τ).val <
        (A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (γ (φ n) (ell (φ n))).val := by
      rw [(hends (φ n)).2]
      nlinarith
    have hmin' : ∀ a ∈ Icc 0 (ell (φ n)), ∀ b ∈ Icc 0 (ell (φ n)), riemannianEDistOf
        (scaleMetric ((A (f (κ₁ (φ n)))).flow.scalar (s (f (κ₁ (φ n)))) (x (f (κ₁ (φ n)))).val)
          hQi ((A (f (κ₁ (φ n)))).endpointTerminalLimitMetric (P (f (κ₁ (φ n))))).metric)
        (γ (φ n) a) (γ (φ n) b) = ENNReal.ofReal |a - b| := hmin (φ n)
    exact (A (f (κ₁ (φ n)))).nonempty_scaled_spatialNeck_of_minimizing_segment hQi
      (lt_of_le_of_lt (min_le_right _ _) (by linarith)) heps (hW _) hτpos hn hmin' hq hleft
      hright

theorem metricRm04StandardAt_nonneg_of_normalized_terminal_pinching
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ) (A : ∀ i, (P i).ClosedSlab (a i) (s i))
    (x : ∀ i, ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen)
    (hQ : ∀ i, 1 ≤ (A i).flow.scalar (s i) (x i).val)
    {Phi : ℝ → ℝ} (hPhi : Perelman.AdmissiblePinchingFunction Phi)
    (hpinch : ∀ i, Perelman.PhiAlmostNonnegative
      ((A i).restrictIncoming le_rfl (A i).lt le_rfl).flow (Ico (a i) (s i)) Phi)
    {f : ℕ → ℕ} (Pl : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
    (F : PointedRiemannianConvergenceMaps
      ({ obj := fun i =>
          { M := ((A i).restrictIncoming le_rfl (A i).lt le_rfl).terminalRegularOpen
            basepoint := x i
            metric := scaleMetric ((A i).flow.scalar (s i) (x i).val)
              (zero_lt_one.trans_le (hQ i)) ((A i).endpointTerminalLimitMetric (P i)).metric } } :
        PointedRiemannianSeq.{u, 0, 0} ThreeModel) Pl f)
    (M : MetricConvergenceData F)
    (hcanonical : ∀ n, M.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    (hQlim : Tendsto (fun n => (A (f n)).flow.scalar (s (f n)) (x (f n)).val) atTop atTop) :
    ∀ (z : Pl.M) (v w : TangentSpace ThreeModel z),
      0 ≤ metricRm04StandardAt Pl.metric z v w w v := by
  have hQpos : ∀ i, 0 < (A i).flow.scalar (s i) (x i).val := fun i => zero_lt_one.trans_le (hQ i)
  apply sectional_nonnegative_of_pointed_admissible_pinching
    M hcanonical hPhi (fun i => (A i).flow.scalar (s i) (x i).val) hQpos hQlim
  intro i y
  have hp :=
    ((A i).endpointTerminalLimitMetric (P i)).curvatureOperatorLowerBoundAt_of_phiAlmostNonnegative
      hPhi.contDiff.continuous (hpinch i) y
  change curvatureOperatorLowerBoundAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
    ((A i).endpointTerminalLimitMetric (P i)).metric) y
    (metricAlgebraicCurvatureTensorAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
      ((A i).endpointTerminalLimitMetric (P i)).metric) y)
    (Perelman.rescalePinchingFunction ((A i).flow.scalar (s i) (x i).val) Phi
      (metricScalarAt (scaleMetric ((A i).flow.scalar (s i) (x i).val) (hQpos i)
        ((A i).endpointTerminalLimitMetric (P i)).metric) y))
  rw [curvatureOperatorLowerBoundAt_scaleMetric_iff, metricScalarAt_scaleMetric,
    Perelman.rescalePinchingFunction]
  simpa only [← mul_assoc, mul_inv_cancel₀ (hQpos i).ne', one_mul] using hp

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
