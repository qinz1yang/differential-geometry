import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BoundedCurvatureAtDistanceNecks

/-!
# CH12-O47, group 1: KL70.2 B1 — the isometric ray with spatial necks on the escape limit

`[FROZEN] CH12-O47` G1.  The limit of B1 is the tree's escape limit `(Pl, F, M)` (the data of
`exists_pointed_convergence_at_scalar_escape_of_traced_buffer`); on it the tree theorem
`exists_isometric_ray_with_spatialNecks_of_scalar_escape` gives an isometric ray
`g : C(Ico 0 rho, Pl.M)` from the basepoint with `R → ∞` and eventual spatial necks along the
filter `comap val (𝓝 rho)`.  `ray_of_isometry_O47` converts this to the O38/O39 ray form
(`γ : ℝ → X`, the ray clause written with the given distance `dX`, blow-up along `𝓝[<] rho`,
necks on a tail `Ico t₀ rho` with `0 ≤ t₀ < rho`); `escape_ray_necks_O47` is the result on the
escape limit, with finiteness of the Riemannian distance on `Pl.M` (so that
`EMetricSpace.toMetricSpace` gives the metric-space structure of B1 v2).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff NNReal ENNReal

namespace GC.LongTime.Ch12

universe u

/-- The ray of an isometry `C(Ico 0 ρ, X)`, extended to `ℝ`, in the O38/O39 form. -/
theorem ray_of_isometry_O47 {X : Type u} [PseudoEMetricSpace X] (dX : X → X → ℝ≥0∞)
    (hd : ∀ a b, edist a b = dX a b) {ρ : ℝ} (hρ : 0 < ρ) (g : C(Ico (0 : ℝ) ρ, X))
    (hg : Isometry g) (Rf : X → ℝ)
    (hblow : Tendsto (fun t => Rf (g t)) (comap (Subtype.val : Ico (0 : ℝ) ρ → ℝ) (𝓝 ρ)) atTop)
    (Nk : X → Prop)
    (hnk : ∀ᶠ t in comap (Subtype.val : Ico (0 : ℝ) ρ → ℝ) (𝓝 ρ), Nk (g t)) :
    ∃ γ : ℝ → X, (∀ t : Ico (0 : ℝ) ρ, γ t = g t) ∧ γ 0 = g ⟨0, le_rfl, hρ⟩ ∧
      (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
        dX (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
      Tendsto (fun t => Rf (γ t)) (𝓝[<] ρ) atTop ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < ρ ∧ ∀ t ∈ Ico t₀ ρ, Nk (γ t) := by
  classical
  let γ : ℝ → X := fun t => if h : t ∈ Ico (0 : ℝ) ρ then g ⟨t, h⟩ else g ⟨0, le_rfl, hρ⟩
  have hγ : ∀ t : Ico (0 : ℝ) ρ, γ t = g t := fun t => by
    simp only [γ, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta]
  refine ⟨γ, hγ, hγ ⟨0, le_rfl, hρ⟩, ?_, ?_, ?_⟩
  · intro t₁ h₁ t₂ h₂
    have e₁ : γ t₁ = g ⟨t₁, h₁⟩ := hγ ⟨t₁, h₁⟩
    have e₂ : γ t₂ = g ⟨t₂, h₂⟩ := hγ ⟨t₂, h₂⟩
    rw [e₁, e₂, ← hd, hg.edist_eq, edist_dist, Subtype.dist_eq, Real.dist_eq]
  · have hle : 𝓝[<] ρ ≤ map (Subtype.val : Ico (0 : ℝ) ρ → ℝ) (comap Subtype.val (𝓝 ρ)) := by
      rw [subtype_coe_map_comap]
      exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ico_mem_nhdsLT hρ))
    refine Tendsto.mono_left ?_ hle
    rw [tendsto_map'_iff]
    exact hblow.congr fun t => by simp only [Function.comp_apply, hγ]
  · obtain ⟨U, hU, hUs⟩ := mem_comap.mp hnk
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine ⟨max 0 (ρ - ε / 2), le_max_left _ _, max_lt hρ (by linarith), ?_⟩
    intro t ht
    have ht0 : t ∈ Ico (0 : ℝ) ρ := ⟨(le_max_left _ _).trans ht.1, ht.2⟩
    have htU : t ∈ U := hball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith [le_max_right 0 (ρ - ε / 2), ht.1, ht.2])
    have hN := hUs (show (⟨t, ht0⟩ : Ico (0 : ℝ) ρ) ∈ Subtype.val ⁻¹' U from htU)
    have e : γ t = g ⟨t, ht0⟩ := hγ ⟨t, ht0⟩
    rw [e]
    exact hN

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

private local instance {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) :
    SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel G.terminalRegularOpen.isOpen)

/-- **B1 on the escape limit**: binders of `exists_isometric_ray_with_spatialNecks_of_scalar_escape`
verbatim; output in the O38/O39 ray form, plus finiteness of the distance on `Pl.M`. -/
theorem escape_ray_necks_O47
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
    (∀ a b : Pl.M, edist a b ≠ ⊤) ∧
    ∃ γ : ℝ → Pl.M, γ 0 = Pl.basepoint ∧
      (∀ t₁ ∈ Ico (0 : ℝ) rho, ∀ t₂ ∈ Ico (0 : ℝ) rho,
        riemannianEDistOf Pl.metric (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
      Tendsto (fun t => metricScalarAt Pl.metric (γ t)) (𝓝[<] rho) atTop ∧
      ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ < rho ∧ ∀ t ∈ Ico t₀ rho, Nonempty (SpatialNeck Pl.metric alpha (γ t)) := by
  intro _
  have hfin : ∀ a b : Pl.M, edist a b ≠ ⊤ := by
    intro a b
    apply ne_top_of_le_ne_top _ (edist_triangle_left a b Pl.basepoint)
    exact ENNReal.add_ne_top.mpr ⟨(hradial a).ne_top, (hradial b).ne_top⟩
  obtain ⟨g, hg, hg0, hblow, hnecks⟩ := exists_isometric_ray_with_spatialNecks_of_scalar_escape
    P a s A Ctime Cgrad q htime hgradient x hQ hqQ hqlim halpha halpha1 heps hW hrho f hf r hr
    hrlim Pl F M hcanonical hradial hcompact hcapture hlower z hfinite hdist hhigh
  obtain ⟨γ, -, hγ0, hiso, hγblow, t₀, ht₀, ht₀ρ, hγnk⟩ :=
    ray_of_isometry_O47 (riemannianEDistOf Pl.metric) (fun _ _ => rfl) hrho g hg
      (metricScalarAt Pl.metric) hblow (fun y => Nonempty (SpatialNeck Pl.metric alpha y)) hnecks
  exact ⟨hfin, γ, hγ0.trans hg0, hiso, hγblow, t₀, ht₀, ht₀ρ, hγnk⟩

end GC.LongTime.Ch12
