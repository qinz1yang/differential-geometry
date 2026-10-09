import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.RegularCollisionNodalArcs
import DifferentialGeometry.Analysis.Calculus.Inverse.SmoothLocalInverse
import DifferentialGeometry.Topology.Maps.CollisionPairs
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundaryTraceInjectivity
import Mathlib.Topology.Sequences

set_option autoImplicit false
noncomputable section

open Set Filter Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped Topology ContDiff Manifold

namespace CuspIncompressibility.ConsumerAudit

-- Internal receiving mechanics for the actual collision closure theorem below.
-- These do not constitute a separate public supplier packet.
private theorem range_fderiv_le_of_coincident_germ_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {X : ℂ → E} {s : Set ℂ} (hs : IsOpen s) (hX : ContDiffOn ℝ ∞ X s)
    {a b : ℂ} (ha : a ∈ s) (hb : b ∈ s) (hvalue : X a = X b)
    (hDb : Function.Injective (fderiv ℝ X b))
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop, Filter.map X (𝓝 (α n)) = Filter.map X (𝓝 (β n))) :
    LinearMap.range (fderiv ℝ X a).toLinearMap ≤
      LinearMap.range (fderiv ℝ X b).toLinearMap := by
  obtain ⟨r, U, V, hU, hUb, hV, hbV, _hVs, hr, hleft, hrb⟩ :=
    Analysis.exists_smooth_local_leftInverse hs hX hb hDb
  have hra : r (X a) = b := by rw [hvalue]; exact hrb
  have hXa : ContDiffAt ℝ ∞ X a := hX.contDiffAt (hs.mem_nhds ha)
  have hXb : ContDiffAt ℝ ∞ X b := hX.contDiffAt (hs.mem_nhds hb)
  have hraSmooth : ContDiffAt ℝ ∞ r (X a) := by
    rw [hvalue]
    exact hr.contDiffAt (hU.mem_nhds hUb)
  have hXr : ContDiffAt ℝ ∞ X (r (X a)) := by rwa [hra]
  let G : ℂ → E := X ∘ r ∘ X
  have hG : ContDiffAt ℝ ∞ G a := hXr.comp a (hraSmooth.comp a hXa)
  have hevent : ∀ᶠ n in atTop, fderiv ℝ G (α n) = fderiv ℝ X (α n) := by
    filter_upwards [hβ.eventually (hV.mem_nhds hbV), hgerm] with n hn hgn
    have hfix : {y : E | X (r y) = y} ∈ Filter.map X (𝓝 (β n)) := by
      apply Filter.mem_map.mpr
      apply Filter.mem_of_superset (hV.mem_nhds hn)
      intro z hz
      change X (r (X z)) = X z
      rw [hleft z hz]
    rw [← hgn] at hfix
    have heq : G =ᶠ[𝓝 (α n)] X := Filter.mem_map.mp hfix
    exact heq.fderiv_eq
  have hDGa : ContinuousAt (fderiv ℝ G) a :=
    (hG.fderiv_right (m := 0) (by simp)).continuousAt
  have hDXa : ContinuousAt (fderiv ℝ X) a :=
    (hXa.fderiv_right (m := 0) (by simp)).continuousAt
  have hD : fderiv ℝ G a = fderiv ℝ X a :=
    tendsto_nhds_unique (hDGa.tendsto.comp hα)
      ((hDXa.tendsto.comp hα).congr' (Filter.EventuallyEq.symm hevent))
  have hchain := (hXr.differentiableAt (by simp)).hasFDerivAt.comp a
    ((hraSmooth.differentiableAt (by simp)).hasFDerivAt.comp a
      (hXa.differentiableAt (by simp)).hasFDerivAt)
  have hfactor : fderiv ℝ X a = (fderiv ℝ X b).comp
      ((fderiv ℝ r (X a)).comp (fderiv ℝ X a)) := by
    exact hD.symm.trans (by simpa only [G, hra] using hchain.fderiv)
  rintro v ⟨z, rfl⟩
  refine ⟨fderiv ℝ r (X a) (fderiv ℝ X a z), ?_⟩
  exact (congrArg (fun L : ℂ →L[ℝ] E => L z) hfactor).symm

private theorem fixed_graphs_eventuallyEq_of_coincident_germs
    {E : Type*} {X : ℂ → E} (P : E → ℂ)
    (e₁ e₂ : OpenPartialHomeomorph ℂ ℂ)
    (he₁ : (e₁ : ℂ → ℂ) = P ∘ X) (he₂ : (e₂ : ℂ → ℂ) = P ∘ X)
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (hgerm : Filter.map X (𝓝 a) = Filter.map X (𝓝 b)) :
    (X ∘ e₁.symm) =ᶠ[𝓝 (P (X a))] (X ∘ e₂.symm) := by
  have hpre : X ⁻¹' (X '' e₂.source) ∈ 𝓝 a := by
    apply Filter.mem_map.mp
    rw [hgerm]
    exact Filter.image_mem_map (e₂.open_source.mem_nhds hb)
  have hmap : Filter.map e₁.symm (𝓝 (P (X a))) = 𝓝 a := by
    simpa only [he₁, Function.comp_apply] using e₁.symm_map_nhds_eq ha
  have ht : Tendsto e₁.symm (𝓝 (P (X a))) (𝓝 a) := by
    change Filter.map e₁.symm (𝓝 (P (X a))) ≤ 𝓝 a
    rw [hmap]
  have hat : P (X a) ∈ e₁.target := by
    simpa only [he₁, Function.comp_apply] using e₁.map_source ha
  filter_upwards [ht.eventually hpre, e₁.open_target.mem_nhds hat] with y hy hyt
  obtain ⟨z, hz, hXz⟩ := hy
  have hey : e₂ z = y := by
    calc
      e₂ z = P (X z) := congrFun he₂ z
      _ = P (X (e₁.symm y)) := congrArg P hXz
      _ = e₁ (e₁.symm y) := (congrFun he₁ _).symm
      _ = y := e₁.right_inv hyt
  have hzy : e₂.symm y = z := by rw [← hey]; exact e₂.left_inv hz
  change X (e₁.symm y) = X (e₂.symm y)
  rw [hzy]
  exact hXz.symm

private theorem zero_germ_of_closure_interior_zero_of_nodal_alternative
    {v : ℂ → ℝ}
    (halt : (∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        z ≠ 0 → fderiv ℝ v z ≠ 0)
    (hcl : (0 : ℂ) ∈ closure (interior (v ⁻¹' ({0} : Set ℝ)))) :
    ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0 := by
  rcases halt with hzero | ⟨ρ, hρ, hregular⟩
  · exact hzero
  · obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp hcl ρ hρ
    have hzero : v =ᶠ[𝓝 z] fun _ => (0 : ℝ) := mem_interior_iff_mem_nhds.mp hz
    by_cases hz0 : z = 0
    · exact hz0 ▸ hzero
    · have hdz : fderiv ℝ v z = 0 := by
        simpa only [fderiv_const_apply] using hzero.fderiv_eq (𝕜 := ℝ)
      exact (hregular z (Metric.mem_ball.mpr (by simpa only [dist_comm] using hdist)) hz0 hdz).elim

private theorem fixed_isothermal_zero_germ_of_coincident_pair_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : ℂ → E} (P : E →L[ℝ] ℂ) (height : E → ℝ)
    (e₁ e₂ e : OpenPartialHomeomorph ℂ ℂ)
    (he₁ : (e₁ : ℂ → ℂ) = P ∘ X) (he₂ : (e₂ : ℂ → ℂ) = P ∘ X)
    {a b : ℂ} (ha : a ∈ e₁.source) (hb : b ∈ e₂.source)
    (he : P (X a) ∈ e.source) (he0 : e (P (X a)) = 0)
    (hXa : ContinuousAt X a)
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop, Filter.map X (𝓝 (α n)) = Filter.map X (𝓝 (β n))) :
    let w : ℂ → ℝ := fun y => height (X (e₁.symm y)) - height (X (e₂.symm y))
    let v : ℂ → ℝ := w ∘ e.symm
    ((∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        z ≠ 0 → fderiv ℝ v z ≠ 0) →
    ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0 := by
  intro w v halt
  have hF : Tendsto (fun n => P (X (α n))) atTop (𝓝 (P (X a))) :=
    (P.continuous.continuousAt.comp hXa).tendsto.comp hα
  have htheta : Tendsto (fun n => e (P (X (α n)))) atTop (𝓝 (0 : ℂ)) := by
    simpa only [he0, Function.comp_def] using (e.continuousAt he).tendsto.comp hF
  apply zero_germ_of_closure_interior_zero_of_nodal_alternative halt
  apply mem_closure_of_tendsto htheta
  filter_upwards [hα.eventually (e₁.open_source.mem_nhds ha),
    hβ.eventually (e₂.open_source.mem_nhds hb),
    hF.eventually (e.open_source.mem_nhds he), hgerm] with n hn₁ hn₂ hnE hgn
  have hgraph := fixed_graphs_eventuallyEq_of_coincident_germs P e₁ e₂ he₁ he₂ hn₁ hn₂ hgn
  have hw : ∀ᶠ y in 𝓝 (P (X (α n))), w y = 0 := by
    filter_upwards [hgraph] with y hy
    change height (X (e₁.symm y)) - height (X (e₂.symm y)) = 0
    exact sub_eq_zero.mpr (congrArg height hy)
  have hi : Tendsto e.symm (𝓝 (e (P (X (α n))))) (𝓝 (P (X (α n)))) := by
    change Filter.map e.symm _ ≤ _
    rw [e.symm_map_nhds_eq hnE]
  exact mem_interior_iff_mem_nhds.mpr (hi.eventually hw)

/-- Coincident image germs of the actual disk persist at a distinct regular
interior collision limit. Limit nontransversality is derived from a smooth
local left inverse; the single nodal supplier application then retains its
fixed original graph and isothermal witnesses. This is a local closure result,
not exclusion of all collisions or global embeddedness. -/
theorem morrey_image_germs_eq_of_regular_interior_collision_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (hd3 : Module.finrank ℝ E = 3)
    {a b : ℂ} (ha : a ∈ Metric.ball (0 : ℂ) 1) (hb : b ∈ Metric.ball (0 : ℂ) 1)
    (hab : a ≠ b) (hvalue : diskExtension u a = diskExtension u b)
    (hDa : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) a))
    (hDb : Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension u) b))
    {α β : ℕ → ℂ} (hα : Tendsto α atTop (𝓝 a)) (hβ : Tendsto β atTop (𝓝 b))
    (hgerm : ∀ᶠ n in atTop,
      Filter.map (diskExtension u) (𝓝 (α n)) =
        Filter.map (diskExtension u) (𝓝 (β n))) :
    Filter.map (diskExtension u) (𝓝 a) = Filter.map (diskExtension u) (𝓝 b) := by
  classical
  let U : ℂ → M := diskExtension u
  have hUV : U a = U b := hvalue
  let p := U a
  let s : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ U ⁻¹' (chartAt E p).source
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  have hUc : Continuous U := u.continuous.comp diskRetraction_lipschitz.continuous
  have hs : IsOpen s := Metric.isOpen_ball.inter ((chartAt E p).open_source.preimage hUc)
  have has : a ∈ s := ⟨ha, mem_chart_source E p⟩
  have hbs : b ∈ s := ⟨hb, by
    change U b ∈ (chartAt E p).source
    rw [← hUV]
    exact mem_chart_source E p⟩
  have hUs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s :=
    hu.smoothInterior.mono inter_subset_left
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz.2).comp z
      (hUs.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  let C : E →L[ℝ] E :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) p) p
  let Da : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U a
  let Db : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U b
  have hC : Function.Injective C :=
    (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, E))
      (mem_extChartAt_source p)).injective
  have hDX (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ X z =
        (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
          (extChartAt 𝓘(ℝ, E) p) (U z)).comp
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) := by
    have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) hz.2
    exact mfderiv_eq_fderiv.symm.trans
      (mfderiv_comp z (hc.mdifferentiableAt (by simp))
        ((hUs.contMDiffAt (hs.mem_nhds hz)).mdifferentiableAt (by simp)))
  have hDXa : fderiv ℝ X a = C.comp Da := hDX a has
  have hDXb : fderiv ℝ X b = C.comp Db := by
    have h := hDX b hbs
    change fderiv ℝ X b =
      (show E →L[ℝ] E from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
        (extChartAt 𝓘(ℝ, E) p) (U b)).comp Db at h
    rw [← hUV] at h
    exact h
  have hXgerm : ∀ᶠ n in atTop, Filter.map X (𝓝 (α n)) = Filter.map X (𝓝 (β n)) := by
    filter_upwards [hgerm] with n hn
    change Filter.map U (𝓝 (α n)) = Filter.map U (𝓝 (β n)) at hn
    change Filter.map ((extChartAt 𝓘(ℝ, E) p) ∘ U) (𝓝 (α n)) =
      Filter.map ((extChartAt 𝓘(ℝ, E) p) ∘ U) (𝓝 (β n))
    rw [← Filter.map_map, ← Filter.map_map, hn]
  have hXDb : Function.Injective (fderiv ℝ X b) := by
    rw [hDXb]
    exact hC.comp hDb
  have hrangeX := range_fderiv_le_of_coincident_germ_limit hs hX has hbs
    (congrArg (extChartAt 𝓘(ℝ, E) p) hvalue) hXDb hα hβ hXgerm
  have hrange : LinearMap.range Da.toLinearMap ≤ LinearMap.range Db.toLinearMap := by
    rintro v ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hrangeX (LinearMap.mem_range_self (fderiv ℝ X a).toLinearMap z)
    change fderiv ℝ X b w = fderiv ℝ X a z at hw
    refine ⟨w, hC ?_⟩
    change C (Db w) = C (Da z)
    simpa only [hDXa, hDXb, ContinuousLinearMap.comp_apply] using hw
  have hnot : ¬ Function.Surjective (Da.coprod (-Db)) := by
    intro hsurj
    have hDbSurj : Function.Surjective Db := by
      intro v
      obtain ⟨z, hz⟩ := hsurj v
      obtain ⟨w, hw⟩ := hrange (LinearMap.mem_range_self Da.toLinearMap z.1)
      refine ⟨w - z.2, ?_⟩
      change Db w = Da z.1 at hw
      change Da z.1 + -(Db z.2) = v at hz
      calc
        Db (w - z.2) = Db w - Db z.2 := Db.map_sub _ _
        _ = Da z.1 - Db z.2 := congrArg (fun t : E => t - Db z.2) hw
        _ = v := by simpa only [sub_eq_add_neg] using hz
    have hdim := LinearMap.finrank_le_finrank_of_surjective
      (f := Db.toLinearMap) hDbSurj
    rw [hd3, Complex.finrank_real_complex] at hdim
    omega
  let ξ : Fin (Module.finrank ℝ E) → ℂ := fun i => chartComplexGradient p U i a
  let Q := chartGramBilin g p p
  let proj := chartLeadingPlaneProjection g p p ξ
  let F : ℂ → ℂ := fun z => proj (X z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * ξ i).re)
  with_reducible
    obtain ⟨N, e₁, e₂, O, _hNN, _hPN, hsplit, hae₁, hbe₂, he₁s, he₂s,
      _hdisj, he₁, he₂, _hOo, _haO, _hOsub, _hw0, _hDw0, _hrecon,
      A, beta, c, e, lam, _hpdeOriginal, hep, _heO, he0, _he, _hei,
      _hlam, _hlampos, _hv0, _hDv0, _hv, _hB, _hq, _hpde, hmap, _hzeros,
      _hZ0, _hZ, _hlinear, _hconjugate, _hsystem, _hzero,
      T, Cbound, _hTo, _h0T, _hTe, _hCbound, _hbound, R, _hR, _hRT, _hk,
      K, _hKmeas, _hKeq, _hKbound, _hKzero, P, _hnear, _hunit,
      _hH0, _hrep, _hPunit, _hweak, _hcontinuous, _hintegral, _hanalytic, halt⟩ :=
      morrey_regular_collision_zero_germ_or_smooth_nodal_arcs hu hd3 ha hb hab hvalue hDa hDb hnot
  change (e₁ : ℂ → ℂ) = F at he₁
  change (e₂ : ℂ → ℂ) = F at he₂
  let height : E → ℝ := fun v => Q N (v - X a)
  let w : ℂ → ℝ := fun y => height (X (e₁.symm y)) - height (X (e₂.symm y))
  let v : ℂ → ℝ := w ∘ e.symm
  have halt' : (∀ᶠ z in 𝓝 (0 : ℂ), v z = 0) ∨
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ Metric.ball (0 : ℂ) ρ,
        z ≠ 0 → fderiv ℝ v z ≠ 0 := by
    rcases halt with hz | ⟨ρ, hρ, _hsub, hreg, _harcs⟩
    · exact Or.inl hz
    · exact Or.inr ⟨ρ, hρ, hreg⟩
  have hvzero : ∀ᶠ z in 𝓝 (0 : ℂ), v z = 0 :=
    fixed_isothermal_zero_germ_of_coincident_pair_limit proj height e₁ e₂ e
      he₁ he₂ hae₁ hbe₂ hep he0 (hX.continuousOn.continuousAt (hs.mem_nhds has))
      hα hβ hXgerm halt'
  have heT : Tendsto e (𝓝 (F a)) (𝓝 (0 : ℂ)) := by
    simpa only [he0] using (e.continuousAt hep).tendsto
  have hwzero : ∀ᶠ y in 𝓝 (F a), w y = 0 := by
    filter_upwards [heT.eventually hvzero, e.open_source.mem_nhds hep] with y hy hys
    exact (hmap y hys).symm.trans hy
  have hFvalue : F a = F b := congrArg proj (congrArg (extChartAt 𝓘(ℝ, E) p) hvalue)
  have ht₁ : F a ∈ e₁.target := by rw [← he₁]; exact e₁.map_source hae₁
  have ht₂ : F a ∈ e₂.target := by rw [hFvalue, ← he₂]; exact e₂.map_source hbe₂
  have hgraphs : (U ∘ e₁.symm) =ᶠ[𝓝 (F a)] (U ∘ e₂.symm) := by
    filter_upwards [hwzero, e₁.open_target.mem_nhds ht₁,
      e₂.open_target.mem_nhds ht₂] with y hy hy₁ hy₂
    have hheight : height (X (e₁.symm y)) = height (X (e₂.symm y)) := sub_eq_zero.mp hy
    have hnormal : Q N (X (e₁.symm y)) = Q N (X (e₂.symm y)) := by
      simpa only [height, map_sub, sub_left_inj] using hheight
    have hproj₁ : proj (X (e₁.symm y)) = y := by
      change F (e₁.symm y) = y
      rw [← he₁]
      exact e₁.right_inv hy₁
    have hproj₂ : proj (X (e₂.symm y)) = y := by
      change F (e₂.symm y) = y
      rw [← he₂]
      exact e₂.right_inv hy₂
    apply (extChartAt 𝓘(ℝ, E) p).injOn
    · have hmem := (he₁s (e₁.map_target hy₁)).2
      change U (e₁.symm y) ∈ (chartAt E p).source at hmem
      simpa only [extChartAt_source, Function.comp_def] using hmem
    · have hmem := (he₂s (e₂.map_target hy₂)).2
      change U (e₂.symm y) ∈ (chartAt E p).source at hmem
      simpa only [extChartAt_source, Function.comp_def] using hmem
    · change X (e₁.symm y) = X (e₂.symm y)
      calc
        X (e₁.symm y) = lift (proj (X (e₁.symm y))) + Q N (X (e₁.symm y)) • N := hsplit _
        _ = lift (proj (X (e₂.symm y))) + Q N (X (e₂.symm y)) • N := by
          rw [hproj₁, hproj₂, hnormal]
        _ = X (e₂.symm y) := (hsplit _).symm
  have hmap₁ : Filter.map e₁.symm (𝓝 (F a)) = 𝓝 a := by
    rw [← he₁]
    exact e₁.symm_map_nhds_eq hae₁
  have hmap₂ : Filter.map e₂.symm (𝓝 (F a)) = 𝓝 b := by
    rw [hFvalue, ← he₂]
    exact e₂.symm_map_nhds_eq hbe₂
  change Filter.map U (𝓝 a) = Filter.map U (𝓝 b)
  rw [← hmap₁, ← hmap₂, Filter.map_map, Filter.map_map]
  exact Filter.map_congr hgraphs

end CuspIncompressibility.ConsumerAudit

namespace IMS03Embeddedness

/-- Relative closedness of the actual coincident-germ relation inside the
ordered collision space. Full rank belongs to this global receiving layer;
the analytic limit argument does not assume all collisions nontransverse.
Boundary singleton fibers are supplied by the original trace and extension. -/
theorem actual_morrey_coincident_germ_pairs_isClosed
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q) (hγ : IsSmoothEmbeddedLoop (E := E) γ)
    (hd3 : Module.finrank ℝ E = 3)
    {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    (hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z))
    (hseparate : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 →
      ∀ θ : loopCircle, q z ≠ γ θ) :
    IsClosed {p : orderedCollisionPairs (q : closedDisk → M) |
      Filter.map q (𝓝 p.1.1) = Filter.map q (𝓝 p.1.2)} := by
  classical
  obtain ⟨σ, hσ, htrace⟩ := hq.trace
  have hboundary := hQ.boundary_fiber_eq hγ hσ htrace
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz)) hseparate
  have hinterior (x y : closedDisk) (hne : x ≠ y) (hxy : q x = q y) :
      (x : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    by_contra hx
    have hnorm : ‖(x : ℂ)‖ = 1 := by
      have hle : ‖(x : ℂ)‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
      have hnotlt : ¬ ‖(x : ℂ)‖ < 1 := by
        simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact le_antisymm hle (le_of_not_gt hnotlt)
    let c : Circle := ⟨(x : ℂ), mem_sphere_zero_iff_norm.mpr hnorm⟩
    obtain ⟨θ, hθ⟩ :=
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective c
    have hbx : diskBoundary θ = x := by
      apply Subtype.ext
      have hc := congrArg (fun w : Circle => (w : ℂ)) hθ
      simpa only [AddCircle.homeomorphCircle_apply] using! hc
    exact hne ((hboundary θ y
      (hxy.symm.trans (congrArg q hbx).symm)).trans hbx).symm
  have hrankInterior (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
    have hder :
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) =
          (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z) := by
      ext v
      exact congrArg (fun L => L v)
        ((hQ.eventuallyEq_diskExtension hz).mfderiv_eq
          (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)))
    have hQrank : Function.Injective
        (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) Q z) :=
      hrank z (Metric.ball_subset_closedBall hz)
    change Function.Injective
      (show ℂ →L[ℝ] E from mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) z)
    intro v w hvw
    apply hQrank
    exact (congrArg (fun L : ℂ →L[ℝ] E => L v) hder).trans
      (hvw.trans (congrArg (fun L : ℂ →L[ℝ] E => L w) hder).symm)
  have hrestriction : diskExtension q ∘ (Subtype.val : closedDisk → ℂ) =
      (q : closedDisk → M) := funext (diskExtension_coe q)
  have hdisk (z : closedDisk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
      Filter.map q (𝓝 z) = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
    calc
      Filter.map q (𝓝 z) =
          Filter.map (diskExtension q ∘ (Subtype.val : closedDisk → ℂ)) (𝓝 z) :=
        congrArg (fun f : closedDisk → M => Filter.map f (𝓝 z)) hrestriction.symm
      _ = Filter.map (diskExtension q) (𝓝 (z : ℂ)) := by
        rw [← Filter.map_map, map_nhds_subtype_val]
        rw [nhdsWithin_eq_nhds.2
          (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz)
            Metric.ball_subset_closedBall)]
  apply IsSeqClosed.isClosed
  intro seq p hseq hlim
  have ha := hinterior p.1.1 p.1.2 p.2.1 p.2.2
  have hb := hinterior p.1.2 p.1.1 (Ne.symm p.2.1) p.2.2.symm
  have hα : Tendsto (fun n => ((seq n).1.1 : ℂ)) atTop (𝓝 (p.1.1 : ℂ)) :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).continuousAt.tendsto.comp hlim
  have hβ : Tendsto (fun n => ((seq n).1.2 : ℂ)) atTop (𝓝 (p.1.2 : ℂ)) :=
    (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).continuousAt.tendsto.comp hlim
  have hgerms : ∀ᶠ n in atTop,
      Filter.map (diskExtension q) (𝓝 ((seq n).1.1 : ℂ)) =
        Filter.map (diskExtension q) (𝓝 ((seq n).1.2 : ℂ)) := by
    apply Filter.Eventually.of_forall
    intro n
    have hna := hinterior (seq n).1.1 (seq n).1.2 (seq n).2.1 (seq n).2.2
    have hnb := hinterior (seq n).1.2 (seq n).1.1 (Ne.symm (seq n).2.1) (seq n).2.2.symm
    exact (hdisk _ hna).symm.trans ((hseq n).trans (hdisk _ hnb))
  have hvalue : diskExtension q p.1.1 = diskExtension q p.1.2 := by
    simpa only [diskExtension_coe] using p.2.2
  have hne : (p.1.1 : ℂ) ≠ (p.1.2 : ℂ) := fun h => p.2.1 (Subtype.ext h)
  have hgerm :=
    CuspIncompressibility.ConsumerAudit.morrey_image_germs_eq_of_regular_interior_collision_limit
      hq hd3 ha hb hne hvalue
      (hrankInterior _ ha) (hrankInterior _ hb) hα hβ hgerms
  exact (hdisk _ ha).trans (hgerm.trans (hdisk _ hb).symm)

end IMS03Embeddedness
