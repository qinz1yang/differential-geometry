import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeLocal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeFoot

/-!
# S3-TUBE: the normal tube of a compact finite-order slice (lane CMS3-FLOW, G1)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §0.6, §3 "S3-TUBE", §4 §8;
frozen statement `exists_normalTube_finite` (`build-logs/scratch/D-CMS3/FiniteSoulThreeInterfaces.lean`
§8), confirmed by the external review (§9). One statement for slices of every dimension `d` (souls of
dimension 0, 1, 2); no total geodesy and no curvature sign.

Route.
* Local tubes (`exists_local_normalTube`, `NormalTubeLocal.lean`) at every point of `S`: a `C^(r−1)`
  map `ψᵢ` on an open set and a radius `δᵢ` such that `ψᵢ (exp v) = v` for every normal `v` based within
  `δᵢ` of the centre with `|v| < δᵢ`.
* A finite subcover of the compact `S` by balls of radius `δᵢ / 2`; `ε = min δᵢ / 8`.
* Uniqueness of the normal representative of norm `< ε` (`eq_of_expMap_eq_tube`): both base points lie
  within `δᵢ` of one centre.
* Existence and calibration from foot points (`exists_normal_expMap_eq_infDist`): `ψ x` is a normal
  vector of length `d_S x` with `exp (ψ x) = x`; near each tube point `ψ` agrees with one `ψᵢ`, hence
  is `C^(r−1)`; `d_S = √(g(ψ, ψ))` is `C^(r−1)` where it is positive.

The same `(ε, ψ)` serves every clause; consumers obtain it once.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

section Inner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The squared `g`-length along a `C^m` map into `TM` is `C^m` (`m ≤ n`). -/
theorem contMDiffAt_inner_self_tube {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    {ψ : M → TangentBundle I M} {x : M} (hψ : ContMDiffAt I I.tangent m ψ x) :
    ContMDiffAt I 𝓘(ℝ, ℝ) m (fun y => g.inner (ψ y).proj (ψ y).snd (ψ y).snd) x := by
  have hb : ContMDiffAt I I m (fun y => (ψ y).proj) x :=
    (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp x hψ
  have hG : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] Bundle.Trivial M ℝ b)
        (ψ y).proj (g.inner (ψ y).proj)) x :=
    (g.contMDiff.of_le hmn).contMDiffAt.comp x hb
  have h := ContMDiffAt.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M ℝ) (b := fun y => (ψ y).proj) (ψ := fun y => g.inner (ψ y).proj)
    (v := fun y => (ψ y).snd) (w := fun y => (ψ y).snd) hG hψ hψ
  exact (contMDiffAt_totalSpace.mp h).2

end Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M] [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- The radial geodesic of `v` has length `|v|`: `d(π v, exp v) ≤ |v|`. -/
theorem dist_proj_expMap_le_tube
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (v : TangentBundle I M) :
    dist v.proj (g.expMap v) ≤ Real.sqrt (g.inner v.proj v.snd v.snd) :=
  g.dist_expMap_le hr hnorm v.proj v.snd fun _ _ => by
    rw [g.geodesicFlowDomain_eq_univ_of_one_le hr hnorm]
    exact mem_univ _

/-- **S3-TUBE** (`2 ≤ r`, any compact `C^r` slice of any dimension `d`; for `d = 0` this is CMS-T's
`exists_point_normalTube`). `Φ = exp` on the `ε`-disc bundle of `ν_g S = normalSetFinite g S ⊆ TM` is a
bijection onto `{d_S < ε}` with inverse `ψ` of class `C^{r−1} = C^{m−2}` (as a map into `TM`), fixing `S`,
calibrated `d_S (exp v) = |v|`; `d_S` is `C^{r−1}` on the punctured tube. -/
theorem exists_normalTube_finite [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hSc : IsCompact S) (hSne : S.Nonempty) {d : ℕ}
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) :
    ∃ ε > 0, ∃ ψ : M → TangentBundle I M,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) ψ {x | infDist x S < ε} ∧
      (∀ x, infDist x S < ε → ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧
        Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S) ∧
      (∀ v ∈ normalSetFinite g S, Real.sqrt (g.inner v.proj v.snd v.snd) < ε →
        ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = Real.sqrt (g.inner v.proj v.snd v.snd)) ∧
      (∀ s ∈ S, ψ s = (⟨s, 0⟩ : TangentBundle I M)) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => infDist x S)
        {x | 0 < infDist x S ∧ infDist x S < ε} := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hmn : m ≤ (r : ℕ∞ω) + 1 := coe_sub_one_le_add_one_tube
  -- notation: the `g`-length
  set nrm : TangentBundle I M → ℝ := fun v => Real.sqrt (g.inner v.proj v.snd v.snd) with hnrm
  have hsq : ∀ v : TangentBundle I M, ∀ δ : ℝ, 0 < δ → nrm v < δ →
      g.inner v.proj v.snd v.snd < δ ^ 2 := by
    intro v δ hδ hv
    have h0 : 0 ≤ g.inner v.proj v.snd v.snd :=
      DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g v.proj v.snd
    calc g.inner v.proj v.snd v.snd = nrm v ^ 2 := (Real.sq_sqrt h0).symm
      _ < δ ^ 2 := pow_lt_pow_left₀ hv (Real.sqrt_nonneg _) two_ne_zero
  have hdist : ∀ v : TangentBundle I M, dist v.proj (g.expMap v) ≤ nrm v :=
    dist_proj_expMap_le_tube g hr1 hnorm
  -- local tubes at the points of `S`
  have hloc : ∀ s : S, ∃ U : Set M, IsOpen U ∧ ∃ ψ₀ : M → TangentBundle I M,
      ContMDiffOn I I.tangent m ψ₀ U ∧ ∃ δ > 0, ∀ v ∈ normalSetFinite g S,
        dist (s : M) v.proj < δ → g.inner v.proj v.snd v.snd < δ ^ 2 →
          g.expMap v ∈ U ∧ ψ₀ (g.expMap v) = v := fun s =>
    exists_local_normalTube g hr hnorm hS s.2
  choose U hU ψl hψl δ hδ hprop using hloc
  -- a finite subcover
  obtain ⟨t, hcover⟩ := hSc.elim_finite_subcover (fun s : S => ball (s : M) (δ s / 2))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (by
      have := hδ ⟨x, hx⟩; positivity)⟩)
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hcover hx)
    exact ⟨i, hi⟩
  set ε : ℝ := t.inf' htne δ / 8 with hε
  have hε0 : 0 < ε := by
    have : 0 < t.inf' htne δ := (Finset.lt_inf'_iff htne).mpr fun i _ => hδ i
    positivity
  have hεδ : ∀ i ∈ t, 8 * ε ≤ δ i := by
    intro i hi
    have := Finset.inf'_le δ hi
    rw [hε]
    linarith
  have hnear : ∀ s ∈ S, ∃ i ∈ t, dist (i : M) s < δ i / 2 := by
    intro s hs
    obtain ⟨i, hi, hsi⟩ := mem_iUnion₂.mp (hcover hs)
    exact ⟨i, hi, by rw [dist_comm]; exact hsi⟩
  -- the local claim at a centre
  have hclaim : ∀ i ∈ t, ∀ v ∈ normalSetFinite g S, dist (i : M) v.proj < δ i → nrm v < ε →
      g.expMap v ∈ U i ∧ ψl i (g.expMap v) = v := by
    intro i hi v hv hvd hvn
    have hεi : ε < δ i := by have := hεδ i hi; linarith
    exact hprop i v hv hvd (hsq v (δ i) (hδ i) (hvn.trans hεi))
  -- uniqueness of the small normal representative
  have huniq : ∀ v ∈ normalSetFinite g S, ∀ v' ∈ normalSetFinite g S, nrm v < ε → nrm v' < ε →
      g.expMap v = g.expMap v' → v = v' := by
    intro v hv v' hv' hvn hv'n heq
    obtain ⟨i, hi, hvi⟩ := hnear v.proj hv.1
    have hεi := hεδ i hi
    have hd1 := hdist v
    have hd2 := hdist v'
    have hv'i : dist (i : M) v'.proj < δ i := by
      calc dist (i : M) v'.proj ≤ dist (i : M) v.proj + dist v.proj (g.expMap v) +
            dist (g.expMap v') v'.proj := by
            rw [heq]
            exact (dist_triangle _ _ _).trans (add_le_add_left (dist_triangle _ _ _) _)
              |>.trans (by rw [add_assoc])
        _ < δ i / 2 + ε + ε := by
            rw [dist_comm (g.expMap v') v'.proj]
            linarith
        _ ≤ δ i := by linarith
    have h1 := (hclaim i hi v hv (by linarith) hvn).2
    have h2 := (hclaim i hi v' hv' hv'i hv'n).2
    rw [← h1, ← h2, heq]
  -- the global inverse
  have hfoot := exists_normal_expMap_eq_infDist g hr hnorm hSc hSne hS
  set ψ : M → TangentBundle I M := fun x => Classical.choose (hfoot x) with hψ
  have hψspec : ∀ x, ψ x ∈ normalSetFinite g S ∧ g.expMap (ψ x) = x ∧ nrm (ψ x) = infDist x S :=
    fun x => Classical.choose_spec (hfoot x)
  have hclause3 : ∀ v ∈ normalSetFinite g S, nrm v < ε →
      ψ (g.expMap v) = v ∧ infDist (g.expMap v) S = nrm v := by
    intro v hv hvn
    have hle : infDist (g.expMap v) S ≤ nrm v :=
      (infDist_le_dist_of_mem hv.1).trans (by rw [dist_comm]; exact hdist v)
    obtain ⟨hw, hwexp, hwn⟩ := hψspec (g.expMap v)
    have hwv : ψ (g.expMap v) = v :=
      huniq _ hw v hv (by rw [hwn]; exact hle.trans_lt hvn) hvn hwexp
    refine ⟨hwv, ?_⟩
    rw [← hwn, hwv]
  -- `ψ` agrees with one local inverse near each tube point
  have hsmooth : ∀ x₀, infDist x₀ S < ε → ContMDiffAt I I.tangent m ψ x₀ := by
    intro x₀ hx₀
    obtain ⟨hv₀, hv₀exp, hv₀n⟩ := hψspec x₀
    obtain ⟨i, hi, hsi⟩ := hnear (ψ x₀).proj hv₀.1
    have hεi := hεδ i hi
    have hsx : dist (ψ x₀).proj x₀ < ε := by
      have := hdist (ψ x₀)
      rw [hv₀exp] at this
      linarith
    have hevent : ∀ᶠ y in 𝓝 x₀, y ∈ U i ∧ ψl i y = ψ y := by
      have hopen : IsOpen {y : M | infDist y S < ε} :=
        isOpen_lt (continuous_infDist_pt S) continuous_const
      filter_upwards [hopen.mem_nhds hx₀, ball_mem_nhds x₀ hε0] with y hy hyx
      obtain ⟨hw, hwexp, hwn⟩ := hψspec y
      have hwn' : nrm (ψ y) < ε := by rw [hwn]; exact hy
      have hdy : dist y (ψ y).proj < ε := by
        have := hdist (ψ y)
        rw [hwexp, dist_comm] at this
        linarith
      have hwi : dist (i : M) (ψ y).proj < δ i := by
        have hyx' : dist x₀ y < ε := by rw [dist_comm]; exact hyx
        calc dist (i : M) (ψ y).proj ≤ dist (i : M) (ψ x₀).proj + dist (ψ x₀).proj x₀ +
              dist x₀ y + dist y (ψ y).proj := by
              have h1 := dist_triangle (i : M) (ψ x₀).proj (ψ y).proj
              have h2 := dist_triangle (ψ x₀).proj x₀ (ψ y).proj
              have h3 := dist_triangle x₀ y (ψ y).proj
              linarith
          _ < δ i / 2 + ε + ε + ε := by linarith
          _ ≤ δ i := by linarith
      have h := hclaim i hi (ψ y) hw hwi hwn'
      rw [hwexp] at h
      exact h
    have hx₀U : x₀ ∈ U i := hevent.self_of_nhds.1
    have hψl : ContMDiffAt I I.tangent m (ψl i) x₀ :=
      (hψl i).contMDiffAt ((hU i).mem_nhds hx₀U)
    exact hψl.congr_of_eventuallyEq (hevent.mono fun y hy => hy.2.symm)
  refine ⟨ε, hε0, ψ, fun x hx => (hsmooth x hx).contMDiffWithinAt, fun x _ => hψspec x,
    hclause3, fun s hs => ?_, ?_⟩
  · have h := (hclause3 ⟨s, 0⟩ (zero_mem_normalSetFinite g hs) (by
      change Real.sqrt (g.inner s 0 0) < ε
      rw [map_zero]
      simpa using hε0)).1
    rwa [g.expMap_zero hr1 s] at h
  · intro x hx
    have hq : ContMDiffAt I 𝓘(ℝ, ℝ) m (fun y => g.inner (ψ y).proj (ψ y).snd (ψ y).snd) x :=
      contMDiffAt_inner_self_tube g hmn (hsmooth x hx.2)
    have hqpos : 0 < g.inner (ψ x).proj (ψ x).snd (ψ x).snd := by
      have h := (hψspec x).2.2
      have h0 : 0 ≤ g.inner (ψ x).proj (ψ x).snd (ψ x).snd :=
        DifferentialGeometry.Geometry.Collapse.finite_inner_self_nonneg g _ _
      rcases h0.lt_or_eq with h0 | h0
      · exact h0
      · exfalso
        change Real.sqrt (g.inner (ψ x).proj (ψ x).snd (ψ x).snd) = infDist x S at h
        rw [← h0, Real.sqrt_zero] at h
        exact hx.1.ne h
    have hsqrt : ContMDiffAt I 𝓘(ℝ, ℝ) m
        (fun y => Real.sqrt (g.inner (ψ y).proj (ψ y).snd (ψ y).snd)) x :=
      ((Real.contDiffAt_sqrt hqpos.ne').contMDiffAt).comp x hq
    have hopen : IsOpen {y : M | infDist y S < ε} :=
      isOpen_lt (continuous_infDist_pt S) continuous_const
    refine (hsqrt.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hopen.mem_nhds hx.2] with y _
    exact ((hψspec y).2.2).symm

end DifferentialGeometry.Geometry.FiniteSoul
