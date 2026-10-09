import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceTypes
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointLevelConsumers
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.LipschitzHittingTimeBinding
import DifferentialGeometry.Geometry.Curvature.Surface.FlatTorusTranslation
import DifferentialGeometry.Topology.Surface.Recognition.JordanDomainDisk

/-!
# LFR23: an endpoint interval gives an actual disk band (the row)

Row LFR23 (`thm:collapse-finite-endpoint-disk-band`, master207A:26745). A complete connected
orientable surface (model `𝓡 2`) with a metric of class `C^{r+1}`, `r ≥ 3` (`m = r + 1 ≥ 4`), and
nonnegative curvature, a base point `z₀`, and an endpoint model `q` on `B̄(z₀, 10)` (`q z₀ = 0`,
`q ≥ 0`, distortion `≤ δ`, `δ`-dense image in `[0, 10]`), with `δ ≤ 1/24000000` (the universal
threshold):
* (i) on `1/2 ≤ r ≤ 37/4` any two inward unit directions are within `2√(600δ)`;
* (ii) ONE smooth outward field on an open neighbourhood of the closed band, norm `< 2`, pairing
  `< -3/4` with EVERY inward direction; its flow, the locally Lipschitz hitting time, and for all
  `a, b ∈ [1, 9]` the hitting-time homeomorphism `{r = a} ≃ₜ {r = b}` of the SAME flow;
* (iii) for every `a ∈ [1, 9]`, `B̄(z₀, a)` is a topological closed disk (a closed embedding of the
  unit disk) whose boundary circle is the connected level `{r = a}`.

Route of (iii) (blueprint, with the recorded changes): the level is a Jordan circle and the frontier
of the ball (`EndpointLevelCircle.lean`, `EndpointLevels.lean`); the surface is `S²`, `T²`, `ℝ²` or
`S¹ × ℝ` (LFR22, `SurfaceTypes.lean`); the torus is excluded GLOBALLY by SF-FT2
(`false_of_nonneg_torus_of_endpoint_interval`, along the unit segment of length `5` from `z₀`); in
the other three models a compact domain with a Jordan frontier is a disk (X93,
`exists_disk_of_jordan_frontier_sphereTwo/plane/cylinder`), transported back by the homeomorphism.

Deviations (recorded): the threshold is explicit; the row's bound `q ≤ 10` is not used; "Lipschitz
circle" is delivered as the locally Lipschitz hitting time of the band (CMS-T B2), whose level
graphs in flow boxes are locally Lipschitz (`exists_endpoint_band_field_lipschitz`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Surface
open DifferentialGeometry.Geometry.FiniteSoul

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Kernels

variable {X : Type*} [TopologicalSpace X]

/-- **Transport of disk recognition along a homeomorphism.** If every compact domain with
nonempty interior and a Jordan frontier in `Y` is a closed disk, the same holds in `Z ≃ₜ Y`. -/
theorem exists_disk_of_homeomorph_recognition {Y : Type*} [TopologicalSpace Y] (φ : X ≃ₜ Y)
    (hY : ∀ D' : Set Y, IsCompact D' → (interior D').Nonempty → ∀ c' : Circle → Y,
      Continuous c' → Injective c' → frontier D' = range c' →
        ∃ e : Disk 2 → Y, IsClosedEmbedding e ∧ range e = D' ∧ e '' diskSphere 2 = range c')
    {D : Set X} (hD : IsCompact D) (hint : (interior D).Nonempty) {c : Circle → X}
    (hc : Continuous c) (hinj : Injective c) (hfr : frontier D = range c) :
    ∃ e : Disk 2 → X, IsClosedEmbedding e ∧ range e = D ∧ e '' diskSphere 2 = range c := by
  obtain ⟨e', he', hr', hb'⟩ := hY (φ '' D) (hD.image φ.continuous)
    (by rw [← φ.image_interior]; exact hint.image φ) (φ ∘ c) (φ.continuous.comp hc)
    (φ.injective.comp hinj) (by rw [← φ.image_frontier, hfr, range_comp])
  refine ⟨φ.symm ∘ e', φ.symm.isClosedEmbedding.comp he', ?_, ?_⟩
  · rw [range_comp, hr']
    exact φ.toEquiv.symm_image_image D
  · rw [image_comp, hb', range_comp]
    exact φ.toEquiv.symm_image_image (range c)

/-- **The hitting-time homeomorphism between two levels** of a flow band. -/
theorem exists_homeomorph_level_of_hittingTime {Φ : ℝ → X → X}
    (hΦ : Continuous (fun p : ℝ × X => Φ p.1 p.2)) (hΦ0 : ∀ x, Φ 0 x = x)
    (hΦadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x)) {η : X → ℝ} (hη : Continuous η) {U : Set X}
    (hU : IsOpen U) {κ a b : ℝ} (hκ : 0 < κ) (hbandU : η ⁻¹' Icc a b ⊆ U)
    (hrate : ∀ x t, 0 ≤ t → (∀ s ∈ Icc 0 t, Φ s x ∈ U) → η x + κ * t ≤ η (Φ t x))
    (hcont : ContinuousOn (fun p : X × ℝ => hittingTime Φ η p.1 p.2) ((η ⁻¹' Icc a b) ×ˢ Icc a b))
    {s s' : ℝ} (hs : s ∈ Icc a b) (hs' : s' ∈ Icc a b) :
    ∃ h : {x : X // η x = s} ≃ₜ {x : X // η x = s'},
      ∀ x, (h x : X) = Φ (hittingTime Φ η x s') x := by
  have hmap : ∀ {t t' : ℝ}, t ∈ Icc a b → t' ∈ Icc a b → ∀ x : {x : X // η x = t},
      η (Φ (hittingTime Φ η x t') x) = t' := fun ht ht' x =>
    (hittingTime_spec hΦ hΦ0 hΦadd hη hU hκ hbandU hrate (by rw [x.2]; exact ht) ht').1
  have hcont' : ∀ {t t' : ℝ}, t ∈ Icc a b → t' ∈ Icc a b →
      Continuous (fun x : {x : X // η x = t} => Φ (hittingTime Φ η x t') x) := by
    intro t t' ht ht'
    have h1 : Continuous (fun x : {x : X // η x = t} => hittingTime Φ η x t') :=
      hcont.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        fun x => ⟨by change η x ∈ Icc a b; rw [x.2]; exact ht, ht'⟩
    exact hΦ.comp (h1.prodMk continuous_subtype_val)
  have hinv : ∀ {t t' : ℝ}, t ∈ Icc a b → t' ∈ Icc a b → ∀ x : {x : X // η x = t},
      Φ (hittingTime Φ η (Φ (hittingTime Φ η x t') x) t) (Φ (hittingTime Φ η x t') x) = x := by
    intro t t' ht ht' x
    have h := hittingTime_flow_hittingTime hΦ hΦ0 hΦadd hη hU hκ hbandU hrate
      (by rw [x.2]; exact ht) ht'
    rw [x.2] at h
    rw [h, flow_neg_apply_flow hΦ0 hΦadd]
  refine ⟨{ toFun := fun x => ⟨Φ (hittingTime Φ η x s') x, hmap hs hs' x⟩
            invFun := fun y => ⟨Φ (hittingTime Φ η y s) y, hmap hs' hs y⟩
            left_inv := fun x => Subtype.ext (hinv hs hs' x)
            right_inv := fun y => Subtype.ext (hinv hs' hs y)
            continuous_toFun := (hcont' hs hs').subtype_mk _
            continuous_invFun := (hcont' hs' hs).subtype_mk _ }, fun x => rfl⟩

end Kernels

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **LFR23 (iii): the disks.** For every `a ∈ [1, 9]`, `B̄(z₀, a)` is a topological closed disk with
boundary circle the connected level `{r = a}`. -/
theorem finiteSurface_endpoint_closedBall_disk (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {z₀ : Z} {q : Z → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 24000000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) 9) :
    IsConnected (sphere z₀ a) ∧ ∃ e : Disk 2 → Z, IsClosedEmbedding e ∧
      range e = closedBall z₀ a ∧ e '' diskSphere 2 = sphere z₀ a := by
  have : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩
  have : ProperSpace Z := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hdim : Module.finrank ℝ E2 = 2 := by simp
  obtain ⟨hfr, hpc, c, hc, hinj, hrange⟩ :=
    endpoint_sphere_jordan k hr2 hnorm hK hdim hδ hδ' hq0 hqnn hdist hdense ha
  refine ⟨hpc.isConnected, ?_⟩
  have hD : IsCompact (closedBall z₀ a) := isCompact_closedBall z₀ a
  have hint : (interior (closedBall z₀ a)).Nonempty :=
    ⟨z₀, ball_subset_interior_closedBall (mem_ball_self (by linarith [ha.1]))⟩
  have hfr' : frontier (closedBall z₀ a) = range c := by rw [hfr, hrange]
  rw [← hrange]
  rcases finiteSurface_types o k hr hnorm hK with ⟨-, hS | ⟨hT, -⟩⟩ | ⟨-, hP | hC⟩
  · obtain ⟨Φ⟩ := hS
    exact exists_disk_of_homeomorph_recognition Φ.toHomeomorph
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_sphereTwo hD' hint' hc' hinj' hfr'') hD hint hc hinj hfr'
  · exfalso
    obtain ⟨Φ⟩ := hT
    obtain ⟨u, -, hiso, hz⟩ := exists_endpoint_far_segment k hr2 hnorm (by linarith) hq0 hqnn hdist
      hdense
    exact Bundle.ContMDiffRiemannianMetric.false_of_nonneg_torus_of_endpoint_interval hdim k
      (two_le_coe_add_one_of_three_le hr) hnorm Φ.symm hK hq0 hqnn hdist (by linarith)
      (γ := fun t => k.expMap (⟨z₀, t • u⟩ : TangentBundle (𝓡 2) Z)) hz
      (fun t ht t' ht' => hiso t ⟨ht.1, by linarith [ht.2]⟩ t' ⟨ht'.1, by linarith [ht'.2]⟩)
  · obtain ⟨φ⟩ := hP
    exact exists_disk_of_homeomorph_recognition φ
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_plane hD' hint' hc' hinj' hfr'') hD hint hc hinj hfr'
  · obtain ⟨φ⟩ := hC
    exact exists_disk_of_homeomorph_recognition
      (φ.trans ((AddCircle.homeomorphCircle one_ne_zero).prodCongr (Homeomorph.refl ℝ)))
      (fun D' hD' hint' c' hc' hinj' hfr'' =>
        exists_disk_of_jordan_frontier_cylinder hD' hint' hc' hinj' hfr'') hD hint hc hinj hfr'

/-- **LFR23 (the row).** Under the endpoint hypotheses with `δ ≤ 1/24000000`: (i) the inward
directions on the band have diameter `< 2√(600δ)`; (ii) ONE smooth outward field near the closed
band, norm `< 2`, pairing `< -3/4` with EVERY inward direction, its complete flow, the locally
Lipschitz hitting time, and the hitting-time homeomorphisms between all levels in `[1, 9]` of the
SAME flow; (iii) for `a ∈ [1, 9]`, `B̄(z₀, a)` is a topological closed disk with boundary circle the
connected level `{r = a}`. -/
theorem finiteSurface_endpoint_disk_band (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {z₀ : Z} {q : Z → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 24000000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) :
    (∀ x, 1 / 2 ≤ dist z₀ x → dist z₀ x ≤ 37 / 4 →
      ∀ v ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
        ∀ v' ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
          Real.sqrt (k.inner x ((v : E2) - v') ((v : E2) - v')) < 2 * Real.sqrt (600 * δ)) ∧
    (∃ V : (x : Z) → TangentSpace (𝓡 2) x,
      ContMDiff (𝓡 2) (𝓡 2).tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle (𝓡 2) Z)) ∧
      (∀ x, k.inner x (V x) (V x) < 2 ^ 2) ∧
      ∃ O : Set Z, IsOpen O ∧
        (fun x => infDist x ({z₀} : Set Z)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4) ⊆ O ∧
        (∀ x ∈ O, ∀ u ∈ k.finiteMinimizingDirectionsTo ({z₀} : Set Z) x,
          k.inner x (V x) u < -(3 / 4)) ∧
      ∃ Φ : ℝ → Z → Z,
        ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ (fun q : ℝ × Z => Φ q.1 q.2) ∧
        (∀ x, Φ 0 x = x) ∧ (∀ s t x, Φ (s + t) x = Φ s (Φ t x)) ∧
        (∀ t x, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 2) (fun s => Φ s x) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (Φ t x)))) ∧
        LocallyLipschitzOn
          (((fun x => infDist x ({z₀} : Set Z)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4)) ×ˢ
            Icc (1 / 2 : ℝ) (37 / 4))
          (fun p : Z × ℝ => hittingTime Φ (fun x => infDist x ({z₀} : Set Z)) p.1 p.2) ∧
        ∀ a ∈ Icc (1 : ℝ) 9, ∀ b ∈ Icc (1 : ℝ) 9,
          ∃ h : {x : Z // infDist x ({z₀} : Set Z) = a} ≃ₜ {x : Z // infDist x ({z₀} : Set Z) = b},
            ∀ x, (h x : Z) = Φ (hittingTime Φ (fun x => infDist x ({z₀} : Set Z)) x b) x) ∧
    ∀ a ∈ Icc (1 : ℝ) 9, IsConnected (sphere z₀ a) ∧ ∃ e : Disk 2 → Z, IsClosedEmbedding e ∧
      range e = closedBall z₀ a ∧ e '' diskSphere 2 = sphere z₀ a := by
  have : NeZero (Module.finrank ℝ E2) := ⟨by simp⟩
  have : ProperSpace Z := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  have hr2 : 2 ≤ r := le_trans (by norm_num) hr
  have hδ1 : δ ≤ 1 / 9600 := hδ'.trans (by norm_num)
  refine ⟨fun x hx₁ hx₂ v hv v' hv' => sqrt_inner_sub_lt_of_endpoint_band k hr2 hnorm hK hδ
    (by linarith) hq0 hqnn hdist hdense hx₁ hx₂ hv hv', ?_,
    fun a ha => finiteSurface_endpoint_closedBall_disk o k hr hnorm hK hδ hδ' hq0 hqnn hdist hdense ha⟩
  obtain ⟨V, hV, hVR, O, hO, hAO, hOout, Φ, hΦ, hΦ0, hΦadd, hder, hrate, hcont, -⟩ :=
    exists_endpoint_field k hr2 hnorm hK hδ hδ1 hq0 hqnn hdist hdense
  have hUo : IsOpen (O ∩ ({z₀} : Set Z)ᶜ) := hO.inter isClosed_singleton.isOpen_compl
  have hbandU : (fun x => infDist x ({z₀} : Set Z)) ⁻¹' Icc (1 / 2 : ℝ) (37 / 4) ⊆
      O ∩ ({z₀} : Set Z)ᶜ := fun x hx => ⟨hAO hx, fun hxz => by
    have h0 : infDist x ({z₀} : Set Z) = 0 := infDist_zero_of_mem hxz
    have : (1 / 2 : ℝ) ≤ infDist x ({z₀} : Set Z) := hx.1
    linarith⟩
  have hΦ1 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 1 (fun q : ℝ × Z => Φ q.1 q.2) :=
    hΦ.of_le (by exact_mod_cast le_top)
  refine ⟨V, hV, hVR, O, hO, hAO, hOout, Φ, hΦ, hΦ0, hΦadd, hder,
    locallyLipschitzOn_infDist_hittingTime k hr2 hnorm {z₀} hΦ1 hΦ0 hΦadd hUo (by norm_num) hbandU
      hrate, fun a ha b hb => ?_⟩
  exact exists_homeomorph_level_of_hittingTime hΦ.continuous hΦ0 hΦadd (continuous_infDist_pt _)
    hUo (by norm_num : (0 : ℝ) < 3 / 4) hbandU hrate hcont
    ⟨by linarith [ha.1], by linarith [ha.2]⟩ ⟨by linarith [hb.1], by linarith [hb.2]⟩

end DifferentialGeometry.Geometry.Collapse
