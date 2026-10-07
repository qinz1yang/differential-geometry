import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthDepthExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.UniformCapWindowBirthSpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingAncientLimitSpatialC11X

/-!
# S-CH11-FIX8 port of astra `UniformBirthSpatialCanonicalWitness`（`PortC11P`）

来源：donor `UniformBirthSpatialCanonicalWitness.lean`（Jui-Hui `chapter11-astra` @ `a73e4bdbfd`）。
donor 文本在本树编不过的原因只有两处，均非数学内容：

* 用到 `ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time`，
  它在本树里是 EXT2 的 extension `CrossingAncientLimitSpatialC11X`（donor 把它写进了宿主文件），
  补 `import …CrossingAncientLimitSpatialC11X`；
* `open private … from …BirthTimeZeroBound`：原路径现在是 shim，private 声明留在
  `BirthTimeZeroBoundPortC11P`，`from` 改指 `…BirthTimeZeroBoundPortC11P`。

* 三个 opened-private 助手（`le_static_scale_of_neckRadius_le`、
  `curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched`、
  `exists_spatialCanonicalWitness_before_birth`）
  在 `namespace RetainedCoreHistory` 里按短名解析不到，
  调用处写全名 `RetainedCoreHistory.<name>`；
* 末尾 `simpa only [hmetric _] using hout`：simp 改写不进 `∃ Wt : SpatialCanonicalWitness g …` 的
  binder 类型，改为 `rw [hmetric _] at hout; exact hout`。

* 定理陈述里的 binder `(I : InitialIdentification …)` 不被引用（donor 的 unused-variable warning），
  仅把 binder 名改为 `_I`（alpha-等价，陈述的类型项不变）。

陈述 / 定义 / 证明思路逐字不改。原路径 `UniformBirthSpatialCanonicalWitness` 是只 import 本文件的 shim。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open private RetainedCoreHistory.le_static_scale_of_neckRadius_le from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SpatialCrossingContinuationLeaf
open private RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
  RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched from
  DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BirthTimeZeroBoundPortC11P

universe u

namespace RetainedCoreHistory

/-- Uniform spatial canonicality at every actual nonzero birth. The output
coefficient precedes initial data; the threshold and quality precede the actual
history. Incoming estimates and a genuine outgoing slab refer to that same
history. Cap exclusion and all traced depths are produced within the proof. -/
theorem exists_uniform_spatialCanonicalWitness_at_nonzero_birth :
    ∃ εbar : ℝ, 0 < εbar ∧
    ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ εbar →
    ∃ Cbirth : ℝ, 1 ≤ Cbirth ∧
    ∀ (P₀ : OrientedThreeStage.{u}) (g₀ : P₀.Metric)
      (κ ρ C1s C2s : ℝ) (Ctime Cgrad : ℝ≥0) (phi : ℝ → ℝ) (Q : ℝ),
      0 < κ → 0 < ρ → Perelman.AdmissiblePinchingFunction phi → 1 ≤ Q →
    ∃ (Qbirth δmax ρmax εcap Dcap : ℝ) (mcap : ℕ),
      Q ≤ Qbirth ∧ 0 < δmax ∧ 0 < ρmax ∧ 0 < εcap ∧ 0 < Dcap ∧
    ∀ (p₀ : CutoffParameters) (δbound ρbound : ℝ),
      p₀.modelAccuracy ≤ εcap → Dcap ≤ p₀.modelRadius → mcap ≤ p₀.modelOrder →
      δbound ≤ δmax → ρbound ≤ ρmax → p₀.recenterConstant * δbound ≤ 1 / 2 →
    ∀ (H : RetainedCoreHistory.{u})
      (_I : InitialIdentification P₀ g₀ H.toHistory)
      (p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p),
      H.IsCanonicalCutoffRecordFamily p₀ δbound ρbound records →
      H.EventSlabsPinched phi →
      (∀ hfinal : H.time (Fin.last H.eventCount) < H.horizon,
        Perelman.PhiAlmostNonnegative (H.finalSlab hfinal).flow
          (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) →
    ∀ t : Icc (0 : ℝ) H.toHistory.horizon,
      (t : ℝ) < H.horizon → H.time (H.toHistory.activeStage t) = (t : ℝ) →
      H.toHistory.activeStage t ≠ 0 →
      H.EventSlabsSpatiallyCanonical ε C1s C2s Q (H.toHistory.activeStage t) →
      H.EventSlabsDerivative Ctime Q (H.toHistory.activeStage t) →
      H.EventSlabsGradient Cgrad Q (H.toHistory.activeStage t) →
      H.NoncollapsedBefore κ ρ (t : ℝ) →
    ∀ (s : ℝ) (G : (H.stage (H.toHistory.activeStage t)).IncomingSlab
        (H.time (H.toHistory.activeStage t)) s),
      (∀ v : ℝ, G.flow.base.metric v =
        H.toHistory.stageMetric (H.toHistory.activeStage t) v) →
      G.DerivativeBoundBefore Ctime Q s → G.GradientBoundBefore Cgrad Q s →
    ∀ y : (H.toHistory.stageAt t).Carrier,
      Qbirth < metricScalarAt (H.initialMetric (H.toHistory.activeStage t)) y →
      ∃ W : SpatialCanonicalWitness (H.initialMetric (H.toHistory.activeStage t))
        ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
  obtain ⟨epsW, hepsW, hclosed⟩ :=
    ObservedHistory.exists_eventually_spatialCanonicalWitness_of_isTracedRegion_at_closed_time.{u}
  refine ⟨min coneAccuracy (min epsW
    (min crossingNeckAccuracy.{u} crossingWindowNeckAccuracy.{u})),
    lt_min coneAccuracy_pos (lt_min hepsW
      (lt_min crossingNeckAccuracy_pos crossingWindowNeckAccuracy_pos)), ?_⟩
  intro ε hε hε11 hεbar
  have hεcone : ε ≤ coneAccuracy := hεbar.trans (min_le_left _ _)
  have hεW : ε ≤ epsW := hεbar.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεN : ε ≤ crossingNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεWN : ε ≤ crossingWindowNeckAccuracy.{u} :=
    hεbar.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Cclosed, hCclosed, hclosed⟩ := hclosed ε hε hε11 hεW
  obtain ⟨Cw, -, hcap⟩ :=
    exists_uniform_capWindowPoint_spatialCanonicalWitness_at_birth.{u} hε hε11
  let Cbirth := max Cclosed Cw
  have hCclosedB : Cclosed ≤ Cbirth := le_max_left _ _
  have hCwB : Cw ≤ Cbirth := le_max_right _ _
  refine ⟨Cbirth, hCclosed.trans hCclosedB, ?_⟩
  intro P₀ g₀ κ ρ C1s C2s Ctime Cgrad phi Q hκ hρ hphi hQ
  by_contra hneg
  push Not at hneg
  let q : ℕ → ℝ := fun n => max Q ((n : ℝ) + 1)
  let D : ℕ → ℝ := fun n => (n : ℝ) + 1
  let θcap : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hQq : ∀ n, Q ≤ q n := fun _ => le_max_left _ _
  have hqn : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n := fun _ => le_max_right _ _
  have hq0 : ∀ n, 0 < q n := fun n => (zero_lt_one.trans_le hQ).trans_le (hQq n)
  have hpack : ∀ n : ℕ, ∃ (H : RetainedCoreHistory.{u})
      (p₀ p : CutoffParameters) (records : ∀ i, GeometricCutoffRecord H.toHistory i p)
      (δb ρb : ℝ) (t : Icc (0 : ℝ) H.toHistory.horizon)
      (y : (H.toHistory.stageAt t).Carrier),
      Nonempty (InitialIdentification P₀ g₀ H.toHistory) ∧
      H.IsCanonicalCutoffRecordFamily p₀ δb ρb records ∧
      q n < metricScalarAt (H.initialMetric (H.toHistory.activeStage t)) y ∧
      (p₀.modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ p₀.modelRadius ∧ n + 2 ≤ p₀.modelOrder ∧ δb ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ i b, ((n : ℝ) + 1) * q n ≤ ((records i).static b).neck.scale) ∧
      H.time (H.toHistory.activeStage t) = (t : ℝ) ∧
      H.toHistory.activeStage t ≠ 0 ∧ H.EventSlabsPinched phi ∧
      (H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi) ∧
      (H.EventSlabsSpatiallyCanonical ε C1s C2s (q n) (H.toHistory.activeStage t) ∧
        H.EventSlabsDerivative Ctime (q n) (H.toHistory.activeStage t) ∧
        H.EventSlabsGradient Cgrad (q n) (H.toHistory.activeStage t)) ∧
      H.NoncollapsedBefore κ ρ (t : ℝ) ∧
      ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t (D n) (θcap n) ∧
      ¬ ∃ W : SpatialCanonicalWitness (H.initialMetric (H.toHistory.activeStage t))
          ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
    intro n
    have hD : 0 < D n := by dsimp [D]; positivity
    have hθ : θcap n < 1 := by
      dsimp [θcap]
      have : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    obtain ⟨Rcap, mcap, -, hcapn⟩ := hcap P₀ g₀ Ctime Cgrad (D n) (θcap n) hD hθ
    obtain ⟨δcap, ρcap, εcap, hδcap, hρcap, hεcap, hcapn⟩ := hcapn (q n) (hq0 n)
    have hX : 0 < ((n : ℝ) + 1) * q n := mul_pos (by positivity) (hq0 n)
    have hρsmall : 0 < Real.sqrt (1 / (2 * (((n : ℝ) + 1) * q n))) :=
      Real.sqrt_pos.mpr (div_pos one_pos (mul_pos two_pos hX))
    obtain ⟨p₀, δb, ρb, hacc, hrad, hord, hδb, hρb, hΛδ, H, I, p, records,
        hrec, hpinch, hfinal, t, htop, hbirth, hne, hspat, hder, hgrad, hnc,
        s, G, hG, hdG, hgG, y, hRy, hfail⟩ :=
      hneg (q n) (min δcap (1 / ((n : ℝ) + 1)))
        (min ρcap (Real.sqrt (1 / (2 * (((n : ℝ) + 1) * q n)))))
        (min εcap (1 / ((n : ℝ) + 1))) (max Rcap (D n)) (max mcap (n + 2))
        (hQq n) (lt_min hδcap (by positivity)) (lt_min hρcap hρsmall)
        (lt_min hεcap (by positivity)) (lt_max_of_lt_right hD)
    have hacc' := le_min_iff.mp hacc
    have hrad' := max_le_iff.mp hrad
    have hord' := max_le_iff.mp hord
    have hδb' := le_min_iff.mp hδb
    have hρb' := le_min_iff.mp hρb
    have hspatq : H.EventSlabsSpatiallyCanonical ε C1s C2s (q n)
        (H.toHistory.activeStage t) :=
      fun j hj z v hv hz => hspat j hj z v hv ((hQq n).trans_lt hz)
    have hderq : H.EventSlabsDerivative Ctime (q n) (H.toHistory.activeStage t) :=
      fun j hj z v hv hz => hder j hj z v hv ((hQq n).trans_lt hz)
    have hgradq : H.EventSlabsGradient Cgrad (q n) (H.toHistory.activeStage t) :=
      fun j hj z v hv hz => hgrad j hj z v hv ((hQq n).trans_lt hz)
    have hdGq : G.DerivativeBoundBefore Ctime (q n) s :=
      fun z v hv hz => hdG z v hv ((hQq n).trans_lt hz)
    have hgGq : G.GradientBoundBefore Cgrad (q n) s :=
      fun z v hv hz => hgG z v hv ((hQq n).trans_lt hz)
    have hGi : G.flow.base.metric (H.time (H.toHistory.activeStage t)) =
        H.initialMetric (H.toHistory.activeStage t) :=
      (hG _).trans (H.toHistory.stageMetric_initial _)
    have hbad : ¬ ∃ W : SpatialCanonicalWitness (H.initialMetric (H.toHistory.activeStage t))
        ε Cbirth (max Cbirth (Cgrad : ℝ)) y, W.capTubeHasNeckChart ε := by
      simpa only [not_exists] using hfail
    have hnot : ¬ H.CapWindowPoint records (H.toHistory.activeStage t) y t (D n) (θcap n) := by
      intro hcw
      obtain ⟨W, hW⟩ := hcapn p₀ δb ρb hacc'.1 hrad'.1 hord'.1 hδb'.1 hρb'.1
        H ⟨I⟩ hΛδ p records hrec (H.toHistory.activeStage t) s G hGi hderq hdGq hgGq y
        (by simpa only [hbirth] using hcw) hRy
      have h2 : max Cw (Cgrad : ℝ) ≤ max Cbirth (Cgrad : ℝ) := max_le_max hCwB le_rfl
      exact hbad ⟨W.enlargeConstants hCwB h2, hW.enlarge_constants hCwB h2⟩
    have hlast : H.toHistory.activeStage t = Fin.last H.eventCount →
        ∃ h : H.time (Fin.last H.eventCount) < H.horizon,
          Perelman.PhiAlmostNonnegative (H.finalSlab h).flow
            (Icc (H.time (Fin.last H.eventCount)) H.horizon) phi := by
      intro hk
      have hf : H.time (Fin.last H.eventCount) < H.horizon := by
        rw [← hk, hbirth]
        exact htop
      exact ⟨hf, hfinal hf⟩
    exact ⟨H, p₀, p, records, δb, ρb, t, y, ⟨I⟩, hrec, hRy,
      ⟨hacc'.2, le_rfl, hrad'.2, hord'.2, hδb'.2⟩,
      RetainedCoreHistory.le_static_scale_of_neckRadius_le hrec hΛδ hX hρb'.2,
      hbirth, hne, hpinch, hlast, ⟨hspatq, hderq, hgradq⟩, hnc, hnot, hbad⟩
  choose H p₀ p records δb ρb t y hinit hrec hqR hpar hscale hbirth hne hpinch hlast
    hslabs hnc hnot hbad using hpack
  let R : ℕ → ℝ := fun n =>
    metricScalarAt ((H n).initialMetric ((H n).toHistory.activeStage (t n))) (y n)
  have hq : ∀ n : ℕ, (n : ℝ) + 1 ≤ q n ∧ q n < R n := fun n => ⟨hqn n, hqR n⟩
  have hRpos : ∀ n, 0 < R n := fun n => (hq0 n).trans (hq n).2
  have hmetric : ∀ n, (H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n) =
      (H n).initialMetric ((H n).toHistory.activeStage (t n)) := by
    intro n
    rw [← hbirth n]
    exact (H n).toHistory.stageMetric_initial _
  have hRscalar : ∀ n, R n = metricScalarAt
      ((H n).toHistory.stageMetric ((H n).toHistory.activeStage (t n)) (t n)) (y n) := by
    intro n
    rw [hmetric n]
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono
    (fun n => ((hq n).1.trans_lt (hq n).2).le)
    (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  obtain ⟨σ, hσ, hall⟩ := exists_subseq_depthExtendable_all_at_birth_of_initialIdentification
    hphi hinit hrec hq hbirth hne hpar hscale (fun _ => le_rfl) hpinch hlast hnot
    hεcone hκ hρ hslabs hnc hRscalar hε hεN hεWN id strictMono_id
  have hall' : ∀ T : ℝ, 0 < T →
      ObservedHistory.DepthExtendable (fun n => (H n).toHistory) t y R σ T := by
    simpa only [Function.id_comp] using hall
  have hgap : Tendsto (fun n => R (σ n) * ((t (σ n) : ℝ) - (t (σ n) : ℝ)))
      atTop (𝓝 0) := by
    simpa only [sub_self, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  obtain ⟨ψ, -, hev⟩ := hclosed (fun n => (H (σ n)).toHistory) (fun n => t (σ n))
    (fun n => y (σ n)) (fun n => R (σ n)) (fun n => hRpos (σ n))
    (fun n => (hRscalar (σ n)).symm) (hRlim.comp hσ.tendsto_atTop)
    (fun A T hA hT => hall' T hT A hA) hκ hρ (t₀ := fun n => (t (σ n) : ℝ)) hgap
    (fun n v z r hv hr hb => hnc (σ n) v z r hv.le hr hb) hphi
    (fun n v hv z => RetainedCoreHistory.curvatureOperatorLowerBoundAt_before_of_eventSlabsPinched
      (H (σ n)) (hpinch (σ n)) (hlast (σ n)) v hv z)
    (C1s := C1s) (C2s := C2s) (Cs := 1) (Cq := 1) (Ctime := Ctime)
    (qs := fun n => q (σ n)) (qcan := fun n => q (σ n))
    (fun n => by simpa only [one_mul] using (hq (σ n)).2.le)
    (fun n => by simpa only [one_mul] using (hq (σ n)).2.le)
    (fun n v hv hvk z hz => RetainedCoreHistory.exists_spatialCanonicalWitness_before_birth
      (H (σ n)) (hbirth (σ n)) (hslabs (σ n)).1 v hv hvk z hz)
    (fun n v hv hvk z hz =>
      (H (σ n)).abs_derivWithin_stageMetric_scalar_le_of_derivative_bounds_of_lt
        (t := t (σ n)) (t₀ := (t (σ n) : ℝ)) le_rfl (hslabs (σ n)).2.1
        ((H (σ n)).derivativeBound_inputs_at_birth (hbirth (σ n)) Ctime (q (σ n))).1
        ((H (σ n)).derivativeBound_inputs_at_birth (hbirth (σ n)) Ctime (q (σ n))).2
        v hv hvk z hz)
  obtain ⟨i, W, hW⟩ := hev.exists
  have h2 : Cclosed ≤ max Cbirth (Cgrad : ℝ) := hCclosedB.trans (le_max_left _ _)
  have hout : ∃ Wt : SpatialCanonicalWitness
      ((H (σ (ψ i))).toHistory.stageMetric
        ((H (σ (ψ i))).toHistory.activeStage (t (σ (ψ i)))) (t (σ (ψ i))))
      ε Cbirth (max Cbirth (Cgrad : ℝ)) (y (σ (ψ i))), Wt.capTubeHasNeckChart ε :=
    ⟨W.enlargeConstants hCclosedB h2, hW.enlarge_constants hCclosedB h2⟩
  apply hbad (σ (ψ i))
  rw [hmetric (σ (ψ i))] at hout
  exact hout

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
