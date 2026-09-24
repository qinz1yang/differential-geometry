import DifferentialGeometry.Geometry.Metric.ConeChart.Defs
import DifferentialGeometry.Geometry.Metric.ConeDilation
import DifferentialGeometry.Geometry.Curve.Reparametrization
import DifferentialGeometry.Geometry.Metric.Pullback.Immersion
import DifferentialGeometry.Topology.Manifold.RegularLevel.Coordinates
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Geometry.Operator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] {m : ℕ}
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private def levelDomain
    (φ : PartialDiffeomorph I (𝓘(ℝ, ℝ).prod (𝓡 m)) M (ℝ × EuclideanSpace ℝ (Fin m)) ∞)
    (a : ℝ) : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m)) :=
  ⟨{u | (a, u) ∈ φ.target}, φ.open_target.preimage (continuous_const.prodMk continuous_id)⟩

private def levelMap
    (φ : PartialDiffeomorph I (𝓘(ℝ, ℝ).prod (𝓡 m)) M (ℝ × EuclideanSpace ℝ (Fin m)) ∞)
    (a : ℝ) : levelDomain φ a → M := fun u => φ.symm (a, u)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] in
private theorem levelMap_smooth
    (φ : PartialDiffeomorph I (𝓘(ℝ, ℝ).prod (𝓡 m)) M (ℝ × EuclideanSpace ℝ (Fin m)) ∞)
    (a : ℝ) : ContMDiff (𝓡 m) I ∞ (levelMap φ a) := by
  apply contMDiffOn_univ.mp
  exact φ.symm.contMDiffOn.comp
    (contMDiff_const.prodMk contMDiff_subtype_val).contMDiffOn (fun u _ => u.property)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] in
private theorem levelMap_mfderiv_injective
    (φ : PartialDiffeomorph I (𝓘(ℝ, ℝ).prod (𝓡 m)) M (ℝ × EuclideanSpace ℝ (Fin m)) ∞)
    (a : ℝ) (u : levelDomain φ a) : Function.Injective (mfderiv (𝓡 m) I (levelMap φ a) u) := by
  let f := levelMap φ a
  have hf : ContMDiff (𝓡 m) I ∞ f := levelMap_smooth φ a
  have hback : MDifferentiableAt I (𝓡 m) (fun y => (φ y).2) (f u) :=
    ((φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds (φ.map_target u.property))).snd).mdifferentiableAt (by decide)
  have heq : (fun y => (φ y).2) ∘ f = (Subtype.val : levelDomain φ a → EuclideanSpace ℝ (Fin m)) := by
    funext z
    exact congrArg Prod.snd (φ.right_inv z.property)
  have hderiv := mfderiv_comp u hback (hf.mdifferentiable (by decide) u)
  rw [heq, mfderiv_subtype_val] at hderiv
  intro v w hvw
  have hv := DFunLike.congr_fun hderiv v
  have hw := DFunLike.congr_fun hderiv w
  change v = (mfderiv I (𝓡 m) (fun y => (φ y).2) (f u)) (mfderiv (𝓡 m) I f u v) at hv
  change w = (mfderiv I (𝓡 m) (fun y => (φ y).2) (f u)) (mfderiv (𝓡 m) I f u w) at hw
  exact hv.trans ((congrArg (mfderiv I (𝓡 m) (fun y => (φ y).2) (f u)) hvw).trans hw.symm)

variable {Y : Type*} [PseudoMetricSpace Y] [NeZero (Module.finrank ℝ E)]

private theorem radial_velocity
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = Metric.coneDistance (e x) (e y))
    (r : ℝ) (u : Y) (hu : (r, u) ∈ e.target)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun t : ℝ => e.symm (t, u)) r) :
    (mfderiv 𝓘(ℝ, ℝ) I (fun t : ℝ => e.symm (t, u)) r 1 : E) =
      gradientFun g (fun x => (e x).1) (e.symm (r, u)) := by
  have hgrad := gradient_radius_eq_radial_velocity_of_coneDistance
    g hmetric e hpositive hdist (e.map_target hu)
  rw [e.right_inv hu] at hgrad
  have hs := mfderiv_comp_add_apply_one (I := I) 0 r (by simpa only [zero_add] using hc)
  rw [zero_add] at hs
  rw [show (fun s : ℝ => e.symm (r + s, u)) = (fun s : ℝ => e.symm (s + r, u)) by
    funext s; rw [add_comm r s]] at hgrad
  exact hs.symm.trans hgrad.symm


variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]
  [IsManifold (𝓡 m) ∞ S]

private def radialMap (e : OpenPartialHomeomorph M (ℝ × Y)) (ι : S → M) : ℝ × S → M :=
  fun z => e.symm (z.1, (e (ι z.2)).2)

omit [IsManifold (𝓡 m) ∞ S] in
private theorem radial_map_tangential_metric
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = Metric.coneDistance (e x) (e y))
    (ι : S → M) (hι : ContMDiff (𝓡 m) I ∞ ι)
    (hsource : ∀ u, ι u ∈ e.source) (a : ℝ) (ha : 0 < a)
    (hlevel : ∀ u, (e (ι u)).1 = a) (u₀ : S) :
    ∃ W : Set (ℝ × S), IsOpen W ∧ (a, u₀) ∈ W ∧ W ⊆ Ioi 0 ×ˢ univ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 m)) I ∞ (radialMap e ι) W ∧
      (∀ z ∈ W, (z.1, (e (ι z.2)).2) ∈ e.target) ∧
      ∀ z ∈ W, ∀ v w : TangentSpace (𝓡 m) z.2,
        g.inner (radialMap e ι z)
          (mfderiv (𝓡 m) I (fun u => radialMap e ι (z.1, u)) z.2 v)
          (mfderiv (𝓡 m) I (fun u => radialMap e ι (z.1, u)) z.2 w) =
            (z.1 / a) ^ 2 * g.inner (ι z.2)
              (mfderiv (𝓡 m) I ι z.2 v) (mfderiv (𝓡 m) I ι z.2 w) := by
  obtain ⟨Ω, hΩ, hΩbase, hΩsource, hΩtarget, hD, hmetricD⟩ :=
    exists_smooth_dilation_of_coneDistance g hmetric e hpositive hdist (hsource u₀)
  let P : ℝ × S → ℝ × M := fun z => (z.1 / a, ι z.2)
  have hP : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 m)) (𝓘(ℝ, ℝ).prod I) ∞ P :=
    (contMDiff_fst.div_const a).prodMk (hι.comp contMDiff_snd)
  let W := P ⁻¹' Ω
  have hW : IsOpen W := hΩ.preimage hP.continuous
  have hbase : (a, u₀) ∈ W := by
    change (a / a, ι u₀) ∈ Ω
    rwa [div_self ha.ne']
  have hformula (z : ℝ × S) : (z.1 / a * (e (ι z.2)).1, (e (ι z.2)).2) =
      (z.1, (e (ι z.2)).2) := by
    rw [hlevel, div_mul_cancel₀ _ ha.ne']
  have heq : (fun z : ℝ × M => e.symm (z.1 * (e z.2).1, (e z.2).2)) ∘ P =
      radialMap e ι := by
    funext z
    change e.symm (z.1 / a * (e (ι z.2)).1, (e (ι z.2)).2) = _
    rw [hformula]
    rfl
  have hH : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 m)) I ∞ (radialMap e ι) W := by
    rw [← heq]
    exact hD.comp hP.contMDiffOn (fun z hz => hz)
  have htarget (z : ℝ × S) (hz : z ∈ W) : (z.1, (e (ι z.2)).2) ∈ e.target := by
    have h := hΩtarget hz
    change (z.1 / a * (e (ι z.2)).1, (e (ι z.2)).2) ∈ e.target at h
    rwa [hformula] at h
  refine ⟨W, hW, hbase, ?_, hH, htarget, ?_⟩
  · intro z hz
    exact ⟨(div_pos_iff_of_pos_right ha).mp (hΩsource hz).1, mem_univ _⟩
  · intro z hz v w
    let D : M → M := fun x => e.symm (z.1 / a * (e x).1, (e x).2)
    have hDdiff : MDifferentiableAt I I D (ι z.2) :=
      ((hD.contMDiffAt (hΩ.mem_nhds hz)).comp (ι z.2)
        (contMDiffAt_const.prodMk contMDiffAt_id)).mdifferentiableAt (by decide)
    have hcomp : (fun u => radialMap e ι (z.1, u)) = D ∘ ι := by
      funext u
      change e.symm (z.1, (e (ι u)).2) = e.symm (z.1 / a * (e (ι u)).1, (e (ι u)).2)
      rw [hlevel, div_mul_cancel₀ _ ha.ne']
    rw [hcomp, mfderiv_comp z.2 hDdiff (hι.mdifferentiable (by decide) z.2)]
    have h := hmetricD (P z) hz (mfderiv (𝓡 m) I ι z.2 v) (mfderiv (𝓡 m) I ι z.2 w)
    dsimp only [P] at h
    erw [hlevel, div_mul_cancel₀ _ ha.ne'] at h
    exact h


omit [IsManifold (𝓡 m) ∞ S] in
private theorem radial_map_metric
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = Metric.coneDistance (e x) (e y))
    (ι : S → M) (hι : ContMDiff (𝓡 m) I ∞ ι)
    (hsource : ∀ u, ι u ∈ e.source) (a : ℝ) (ha : 0 < a)
    (hlevel : ∀ u, (e (ι u)).1 = a) (u₀ : S) :
    ∃ W : Set (ℝ × S), IsOpen W ∧ (a, u₀) ∈ W ∧ W ⊆ Ioi 0 ×ˢ univ ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 m)) I ∞ (radialMap e ι) W ∧
      (∀ z ∈ W, (z.1, (e (ι z.2)).2) ∈ e.target) ∧
      ∀ z ∈ W, ∀ v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 m)) z,
        g.inner (radialMap e ι z)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I (radialMap e ι) z v)
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I (radialMap e ι) z w) =
            v.1 * w.1 + (z.1 / a) ^ 2 * g.inner (ι z.2)
              (mfderiv (𝓡 m) I ι z.2 v.2) (mfderiv (𝓡 m) I ι z.2 w.2) := by
  obtain ⟨W, hW, hbase, hpositiveW, hH, htarget, htan⟩ :=
    radial_map_tangential_metric g hmetric e hpositive hdist ι hι hsource a ha hlevel u₀
  refine ⟨W, hW, hbase, hpositiveW, hH, htarget, ?_⟩
  intro z hz v w
  let b := radialMap e ι z
  let G : TangentSpace I b := gradientFun g (fun x => (e x).1) b
  let A := mfderiv (𝓡 m) I (fun u => radialMap e ι (z.1, u)) z.2
  have hb : b ∈ e.source := e.map_target (htarget z hz)
  have hdiff := (hH.contMDiffAt (hW.mem_nhds hz)).mdifferentiableAt (by decide)
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun r => radialMap e ι (r, z.2)) z.1 :=
    hdiff.comp (f := fun r : ℝ => (r, z.2)) (g := radialMap e ι) z.1
      (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hrad : (mfderiv 𝓘(ℝ, ℝ) I (fun r => radialMap e ι (r, z.2)) z.1 1 : E) = G :=
    radial_velocity g hmetric e hpositive hdist z.1 (e (ι z.2)).2 (htarget z hz)
      hcurve
  have hr (t : ℝ) :
      (mfderiv 𝓘(ℝ, ℝ) I (fun r => radialMap e ι (r, z.2)) z.1 t : E) = t • G := by
    calc
      _ = mfderiv 𝓘(ℝ, ℝ) I (fun r => radialMap e ι (r, z.2)) z.1 (t • (1 : ℝ)) := by
        rw [smul_eq_mul, mul_one]
      _ = t • (mfderiv 𝓘(ℝ, ℝ) I (fun r => radialMap e ι (r, z.2)) z.1 1 : E) := map_smul _ _ _
      _ = _ := by rw [hrad]
  have hunit : g.inner b G G = 1 :=
    gradient_radius_normSq_eq_one_of_coneDistance g hmetric e hpositive hdist hb
  have hρ : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => (e x).1) b :=
    ((contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist).contMDiffAt (e.open_source.mem_nhds hb)).mdifferentiableAt (by decide)
  have htdiff : MDifferentiableAt (𝓡 m) I (fun u => radialMap e ι (z.1, u)) z.2 :=
    hdiff.comp (f := fun u : S => (z.1, u)) (g := radialMap e ι) z.2
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have heq : (fun u => (e (radialMap e ι (z.1, u))).1) =ᶠ[𝓝 z.2] fun _ => z.1 := by
    have hev : ∀ᶠ u in 𝓝 z.2, (z.1, u) ∈ W :=
      (continuousAt_const.prodMk continuousAt_id) (hW.mem_nhds hz)
    filter_upwards [hev] with u hu
    exact congrArg Prod.fst (e.right_inv (htarget (z.1, u) hu))
  have hcross (v : TangentSpace (𝓡 m) z.2) : g.inner b G (A v) = 0 := by
    rw [inner_gradientFun, ← mvfderiv_comp_apply z.2 hρ htdiff v]
    simp only [Function.comp_def]
    unfold mvfderiv
    erw [heq.mfderiv_eq, mfderiv_const]
    rfl
  have hcross' (v : TangentSpace (𝓡 m) z.2) : g.inner b (A v) G = 0 :=
    (g.symm b (A v) G).trans (hcross v)
  have hdecomp (v : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 m)) z) :
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I (radialMap e ι) z v : E) = v.1 • G + A v.2 := by
    rw [mfderiv_prod_eq_add_apply hdiff, hr]
  rw [hdecomp v, hdecomp w]
  change g.inner b (v.1 • G + A v.2) (w.1 • G + A w.2) = _
  simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul, hunit, mul_one]
  erw [hcross' v.2, hcross w.2]
  rw [htan z hz v.2 w.2]
  ring


omit [NeZero (Module.finrank ℝ E)] in
theorem exists_cone_chart_of_coneDistance
    (g : SmoothRiemannianMetric I M)
    (hmetric : ∀ x y : M, edist x y = riemannianEDistOf g x y)
    (e : OpenPartialHomeomorph M (ℝ × Y))
    (hpositive : ∀ z ∈ e.target, 0 < z.1)
    (hdist : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = Metric.coneDistance (e x) (e y))
    (hdim : Module.finrank ℝ E = m + 1) {p : M} (hp : p ∈ e.source) :
    ∃ U : Set M, p ∈ U ∧ U ⊆ e.source ∧ Nonempty (ConeChart.{_, _, _, 0} m g U) := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; omega⟩
  obtain ⟨φ, hpφ, hφsource, hφlevel⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_product_coordinates_of_contMDiffOn I hdim
      e.open_source (contMDiffOn_radius_of_coneDistance g hmetric e hpositive hdist) hp
      (mfderiv_radius_ne_zero_of_coneDistance g hmetric e hpositive hdist hp)
  let a := (e p).1
  have ha : 0 < a := hpositive (e p) (e.map_source hp)
  let S := levelDomain φ a
  let ι : S → M := levelMap φ a
  have hι : ContMDiff (𝓡 m) I ∞ ι := levelMap_smooth φ a
  have hιsource (u : S) : ι u ∈ e.source := hφsource (φ.map_target u.property)
  have hιlevel (u : S) : (e (ι u)).1 = a := by
    have h := hφlevel (ι u) (φ.map_target u.property)
    have hφ := congrArg Prod.fst (φ.right_inv u.property)
    exact h.symm.trans hφ
  have hu₀ : (a, (φ p).2) ∈ φ.target := by
    have heq : (a, (φ p).2) = φ p := Prod.ext (hφlevel p hpφ).symm rfl
    rw [heq]
    exact φ.map_source hpφ
  let u₀ : S := ⟨(φ p).2, hu₀⟩
  have hιbase : ι u₀ = p := by
    change φ.symm ((e p).1, (φ p).2) = p
    rw [← hφlevel p hpφ]
    exact φ.left_inv hpφ
  obtain ⟨W, hW, hbase, hWpos, hH, htarget, hradial⟩ :=
    radial_map_metric g hmetric e hpositive hdist ι hι hιsource a ha hιlevel u₀
  let Hmap := radialMap e ι
  have hHbase : Hmap (a, u₀) = p := by
    change e.symm (a, (e (ι u₀)).2) = p
    rw [hιbase]
    exact e.left_inv hp
  let _ : LocallyCompactSpace S := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) S
  let _ : SigmaCompactSpace S := sigmaCompactSpace_of_locallyCompact_secondCountable
  have himm (u : S) : Function.Injective (mfderiv (𝓡 m) I ι u) :=
    levelMap_mfderiv_injective φ a u
  let k := scaleMetric (a ^ 2)⁻¹ (inv_pos.mpr (pow_pos ha 2)) (g.pullback ι hι himm)
  have hmetricH (z : ℝ × S) (hz : z ∈ W)
      (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 m)) z) :
      g.inner (Hmap z) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I Hmap z v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I Hmap z w) =
          v.1 * w.1 + z.1 ^ 2 * k.inner z.2 v.2 w.2 := by
    rw [hradial z hz]
    change _ = v.1 * w.1 + z.1 ^ 2 * ((a ^ 2)⁻¹ *
      g.inner (ι z.2) (mfderiv (𝓡 m) I ι z.2 v.2) (mfderiv (𝓡 m) I ι z.2 w.2))
    rw [div_pow, div_eq_mul_inv]
    ring
  let D : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] E :=
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I Hmap (a, u₀)
  have hker (v : ℝ × EuclideanSpace ℝ (Fin m)) (hv : D v = 0) : v = 0 := by
    have h := hmetricH (a, u₀) hbase v v
    change g.inner (Hmap (a, u₀)) (D v) (D v) = v.1 * v.1 + a ^ 2 * k.inner u₀ v.2 v.2 at h
    rw [hv] at h
    have hzero : g.inner (Hmap (a, u₀)) (0 : TangentSpace I (Hmap (a, u₀))) 0 = 0 := map_zero _
    erw [hzero] at h
    have hv₂ : v.2 = 0 := by
      by_contra hne
      have hk := k.pos u₀ v.2 hne
      have hp := mul_pos (pow_pos ha 2) hk
      nlinarith only [h, hp, mul_self_nonneg v.1]
    have hv₁ : v.1 = 0 := by
      erw [hv₂, map_zero, mul_zero, add_zero] at h
      exact mul_self_eq_zero.mp h.symm
    exact Prod.ext hv₁ hv₂
  have hinj : Function.Injective D := by
    intro v w h
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, h, sub_self]
  have hdimension : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin m)) = Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim]
    omega
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimension).mp hinj
  let A := ContinuousLinearEquiv.ofBijective D (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  obtain ⟨Ψ, hΨbase, hΨeq⟩ :=
    DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
      hW hbase hH ⟨A, rfl⟩
  let Γ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Ψ W hW
  have hΓbase : (a, u₀) ∈ Γ.source := ⟨hΨbase, hbase⟩
  have hΓbaseeq : Γ (a, u₀) = p := (hΨeq hΨbase).symm.trans hHbase
  refine ⟨Γ.target, hΓbaseeq ▸ Γ.map_source hΓbase, ?_, ?_⟩
  · intro y hy
    rw [← Γ.right_inv hy]
    change Ψ (Γ.symm y) ∈ e.source
    exact (hΨeq (Γ.map_target hy).1) ▸ e.map_target (htarget (Γ.symm y) (Γ.map_target hy).2)
  · refine ⟨{
      surface := S
      topology := inferInstance
      charted := inferInstance
      smooth := inferInstance
      t2 := inferInstance
      sigmaCompact := inferInstance
      metric := k
      map := Γ
      positive_radius := fun z hz => (hWpos hz.2).1
      target_eq := rfl
      radial_metric := ?_ }⟩
    intro z hz v w
    have heq : Hmap =ᶠ[𝓝 z] Γ := by
      filter_upwards [Γ.open_source.mem_nhds hz] with y hy
      exact hΨeq hy.1
    have hval : Γ z = Hmap z := heq.eq_of_nhds.symm
    have hd : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I Γ z =
        mfderiv (𝓘(ℝ, ℝ).prod (𝓡 m)) I Hmap z := heq.mfderiv_eq.symm
    erw [hval, hd]
    exact hmetricH z hz.2 v w

end DifferentialGeometry.Geometry.Riemannian
