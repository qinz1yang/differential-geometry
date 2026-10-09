import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeBornPatchC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeBornFlowC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NativeBornShiScaledC11SP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LinkedBirthJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TracedInnerJetsCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreDefP6TC

set_option autoImplicit false

/-!
# hBorn′ = SL2-c（born patch jets，O-CH11-NATIVE-BORN G3，后缀 `_C11SP`）

`hBorn_linked_C11SP : hBorn′`（PROVED）。hBorn′ 与 `P6NativeNJSlotV2C11SP` 的冻结 binder `hBorn`
**只差两处**（其余逐字，生成器 `build-logs/scratch/O-CH11-NATIVE-BORN/wip/gen_g3.py` 断言）：
1. records 条件 `hasCanonicalWindow` → `hasLinkedCanonicalWindow_C12X`（O1）：任意阶 born-cap 初始 jets
   树内唯一 producer G63 `exists_linked_window_birth_jets_CXSP` 要 linked（`δ' ≤ S.delta ∧ 2⌊δ'⁻¹⌋ ≤ k`）；
   `hasCanonicalWindow` 是 `∃ δ k d w`，精度与阶都不受控，高阶 jets 无界。
2. 加 `H.time (H.activeStage t) < t`（O2）：窄情形（`0 < t − u* < θ/(2Q)`）走 Q 一致 reset Shi，
   要闭窗 Gram（G6 右端），incoming slab 只有 `Ico` 的 `smoothUpTo`。
证明（逐 `w ∈ B̄_Q(y, R)`）：取小 patch `B(w, ρ0/√Q)`（G1c，`ρ0` 由 margin、`c`、`L0 = e^{9Kθ/2}` 定）。
* 无 born 点，或最大 born 时刻 `u*` 满足 `t − u* ≥ θ/(2Q)`：整块从 `t − θ/(2Q)` traced（G2a），
  走 CXSP `exists_inner_jets_of_traced_region_CXSP`（positive-time，不要初始 jets、不要 hpos）；
* `u* = t`：born 于 t，G1 capture 把 `w` 放进 G63 window，G63 直接给 t 时刻 jets；
* `u* < t` 且 `t − u* < θ/(2Q)`：G2 公共 flow + 距离畸变（`riemannianEDistOf_exp_bounds_of_curvature_bound`）
  + 局部等距（`edistOf_le_of_quad_of_localDiffeomorph`）+ G1 capture ⇒ `u*` 时 Shi 初始球在 G63 window 内；
  G63 jets × `scale ≤ cQ` 给 `A j·Q^{2+j}`；G3b `exists_reset_shi_commonFlow_scaled_C11SP` 收尾。
`u* ≥ t/2 ≥ T₀`（因 `a = t − θ/Q ≥ 0`），所以 G63 的 late 门槛 `δ(time) < δ*/C_rec` 成立。
-/

noncomputable section

open Set Filter Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open GC.GeneralFlow
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace GC.LongTime.Ch11

universe u

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

/-- **G3c（PROVED）**：event output 在 cap window 点的 jets 界 ⇒ birth stage 度量在同一点（HEq 形）的界。 -/
theorem stage_jets_of_output_window_C11SP (H : RetainedCoreHistory.{u}) {p : CutoffParameters}
    (records : ∀ i : Fin H.eventCount, GeometricCutoffRecord H.toHistory i p)
    (e : Fin H.eventCount) (j : Fin (H.toHistory.eventCount + 1)) (hj : e.succ = j)
    (b : (H.toHistory.event e).RetainedBoundaryIndex) (k : ℕ) {X : ℝ}
    (x : standardCapWindow p.modelRadius)
    (hcap : curvDerivNormSq k (H.toHistory.event e).outputMetric
      (((records e).static b).window x) ≤ X)
    (q : (H.toHistory.stage j).Carrier) (hq : HEq (((records e).static b).window x) q) :
    curvDerivNormSq k (H.toHistory.stageMetric j (H.toHistory.time j)) q ≤ X := by
  subst hj
  rw [H.toHistory.stageMetric_initial, ← H.toHistory.event_output e, ← eq_of_heq hq]
  exact hcap

/-- **G3（PROVED）**：hBorn′（= 冻结 hBorn，records 改 linked、t 加正 stage age）。 -/
theorem hBorn_linked_C11SP (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {pBase : CutoffParameters} {Γf : ClosedBirthConstants}
        {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
        (S : PreparedSpatialChain pBase Γf P g) (F : GC.Interface.RawSurgery P g)
        (q : CutoffParameters), F.tower = S.tower →
        (∀ t : ℝ, 0 ≤ t → q.delta t = (chainDiagonal_C11A S).delta t ∧
          q.neckRadius t = (chainDiagonal_C11A S).neckRadius t) →
        pBase.modelAccuracy ≤ ε₀ → capWindowRadius_C11E + 1 ≤ pBase.modelRadius →
        2 ≤ pBase.modelOrder →
        CanonicalLateTimeCore_P6X F ε C1 C2 Ctime →
      ∀ (params : CutoffParameters)
        (records : ∀ n, ∀ e : Fin (F.tower.history n).eventCount,
          GeometricCutoffRecord (F.tower.history n).toHistory e params),
        params.modelRadius = pBase.modelRadius → params.modelOrder = pBase.modelOrder →
        params.modelAccuracy = pBase.modelAccuracy →
        (∀ t : ℝ, 0 ≤ t → params.delta t = q.delta t ∧
          params.neckRadius t = q.neckRadius t) →
        (∀ n e b, ((records n e).static b).hasLinkedCanonicalWindow_C12X) →
        (∀ n e, ((F.tower.history n).toHistory.event e).old =
          ((F.tower.history n).toHistory.event e).transition.trace.retainedCore) →
        Tendsto params.delta atTop (𝓝 0) →
        (∀ η : ℝ, 0 < η → ∃ T : ℝ, 0 < T ∧
          ∀ t : ℝ, T ≤ t → ∀ n : ℕ, ∀ e : Fin (F.tower.history n).eventCount,
            (F.tower.history n).time e.succ ∈ Icc (t / 2) t →
            ∀ h, (records n e).nominalRadius h ≤ η * params.neckRadius t) →
      ∀ (R Rwide θ K c : ℝ), 0 < R → R < Rwide → 0 < θ → 0 < K → 0 < c → ∀ k : ℕ,
      ∃ J T : ℝ, 0 ≤ J ∧ ∀ n : ℕ,
        let H := (F.tower.history n).toHistory
        ∀ (t : Icc (0 : ℝ) H.horizon) (y : (H.stageAt t).Carrier) (Q : ℝ) (hQ : 0 < Q)
          (a : Icc (0 : ℝ) H.horizon) (hat : a ≤ t), T ≤ (t : ℝ) →
          (a : ℝ) = (t : ℝ) - θ / Q → H.time (H.activeStage t) < t →
        let Born : (H.stageAt t).Carrier → Prop := fun x =>
          ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
            ∃ e : Fin H.eventCount, H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
            ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
                (H.activeStage_mono hut) x,
              B.isRmBoundedBy (hat := hut) (K * Q) ∧
              ∃ (b : (H.event e).RetainedBoundaryIndex)
                (z : standardCapWindow params.modelRadius),
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
                HEq (((records n e).static b).window z)
                  (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
                ((records n e).static b).neck.scale ≤ c * Q
        (∀ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
              (H.activeStage_mono hat) x, B.isRmBoundedBy (hat := hat) (K * Q)) ∨ Born x) →
        (∃ x ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y (Rwide / Real.sqrt Q),
          Born x) →
        ∀ w ∈ riemannianClosedBallOf
            (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) y R,
          curvDerivNorm k (scaleMetric Q hQ (H.stageMetric (H.activeStage t) t)) w ≤ J
    := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro pBase Γf ε C1 C2 Ctime S F q hTower hdiag hacc hrad hord hb params records hmR hmO hmA
    hpar hlink hold hdel hrec R Rwide θ K c hR hRR hθ hK hc k
  have hTE := StandardCap.transitionEnd_pos
  have hZD : 2 * (StandardCap.transitionEnd + 10) < params.modelRadius := by
    rw [hmR]
    unfold capWindowRadius_C11E at hrad
    linarith
  have hDpos : 0 < params.modelRadius := by linarith
  have hacc' : params.modelAccuracy ≤ 1 / 2 := by rw [hmA]; exact hacc
  have hcan : ∀ n e b, ((records n e).static b).hasCanonicalWindow := fun n e b =>
    (hlink n e b).hasCanonicalWindow
  choose Cj δj _hCj hδj hjets using fun j : ℕ =>
    exists_linked_window_birth_jets_CXSP.{u} params.fixed params.modelRadius hDpos j
  have hne : (Finset.range (k + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.succ_pos k)⟩
  let δmin : ℝ := (Finset.range (k + 1)).inf' hne δj
  have hδmin : 0 < δmin := (Finset.lt_inf'_iff hne).mpr fun j _ => hδj j
  have hδle : ∀ j, j ≤ k → δmin ≤ δj j := fun j hj =>
    Finset.inf'_le δj (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hrc : 0 < params.recenterConstant := by linarith [params.recenterConstant_ge_four]
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (hdel.eventually (Iio_mem_nhds (div_pos hδmin hrc)))
  let θ1 : ℝ := θ / 2
  have hθ1 : 0 < θ1 := half_pos hθ
  let L0 : ℝ := Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * θ1)
  have hL0 : 1 ≤ L0 := Real.one_le_exp (mul_nonneg (mul_nonneg (sq_nonneg _) hK.le) hθ1.le)
  obtain ⟨ρ0, hρ0, hρ0R, hfitρ⟩ := smallPatch_radius_fit_C11SP hRR hL0 hc hZD
  let R0 : ℝ := ρ0 / (2 * L0)
  have hR0 : 0 < R0 := div_pos hρ0 (by linarith)
  let A : ℕ → ℝ := fun j => Cj j ^ 2 * c ^ (j + 2)
  have hA : ∀ j, 1 ≤ j → j ≤ k → 0 ≤ A j := fun j _ _ =>
    mul_nonneg (sq_nonneg _) (pow_nonneg hc.le _)
  obtain ⟨Bsh, _hBsh, hShi⟩ :=
    exists_reset_shi_commonFlow_scaled_C11SP.{u} k θ1 R0 (K ^ 2) hR0 A hA
  obtain ⟨Jt, hJt1, hJt⟩ :=
    exists_inner_jets_of_traced_region_CXSP.{u} 0 ρ0 θ1 K le_rfl hρ0 hθ1 hK
  let Jcap : ℝ := Real.sqrt (A k)
  refine ⟨max (Jt k) (max (Real.sqrt Bsh) Jcap), 2 * max T₀ 1,
    (zero_le_one.trans (hJt1 k)).trans (le_max_left _ _), ?_⟩
  intro n H t y Q hQ a hat hT ha hpos Born hall hex w hw
  let gt := H.stageMetric (H.activeStage t) t
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let ρ : ℝ := ρ0 / Real.sqrt Q
  have hρ : 0 < ρ := div_pos hρ0 hsQ
  have hwphys : riemannianEDistOf gt y w ≤ ENNReal.ofReal (R / Real.sqrt Q) := by
    have h := riemannianClosedBallOf_scaleMetric Q hQ gt y (R / Real.sqrt Q)
    rw [mul_div_cancel₀ R hsQ.ne'] at h
    rw [h] at hw
    exact hw
  have hsub : riemannianBallOf gt w ρ ⊆ riemannianBallOf gt y (Rwide / Real.sqrt Q) := by
    intro x hx
    have hsum : R / Real.sqrt Q + ρ ≤ Rwide / Real.sqrt Q := by
      change R / Real.sqrt Q + ρ0 / Real.sqrt Q ≤ Rwide / Real.sqrt Q
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by linarith) hsQ.le
    have hne' : riemannianEDistOf gt y w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hwphys
    calc riemannianEDistOf gt y x ≤ riemannianEDistOf gt y w + riemannianEDistOf gt w x :=
          riemannianEDistOf_triangle gt y w x
      _ < ENNReal.ofReal (R / Real.sqrt Q) + ENNReal.ofReal ρ :=
          ENNReal.add_lt_add_of_le_of_lt hne' hwphys hx
      _ = ENNReal.ofReal (R / Real.sqrt Q + ρ) :=
          (ENNReal.ofReal_add (div_nonneg hR.le hsQ.le) hρ.le).symm
      _ ≤ ENNReal.ofReal (Rwide / Real.sqrt Q) := ENNReal.ofReal_le_ofReal hsum
  have hθQ : θ / Q ≤ (t : ℝ) := by
    have h0 : (0 : ℝ) ≤ a := a.2.1
    linarith
  have hθ1Q : θ1 / Q = θ / Q / 2 := by
    change θ / 2 / Q = θ / Q / 2
    ring
  have hθQpos : 0 < θ / Q := div_pos hθ hQ
  let a' : Icc (0 : ℝ) H.horizon :=
    ⟨(t : ℝ) - θ1 / Q, by linarith, by linarith [t.2.2, div_pos hθ1 hQ]⟩
  have haa' : a ≤ a' := by
    change (a : ℝ) ≤ (t : ℝ) - θ1 / Q
    linarith
  have ha't : a' ≤ t := by
    change (t : ℝ) - θ1 / Q ≤ t
    linarith [div_pos hθ1 hQ]
  have hlt' : (a' : ℝ) < t := by
    change (t : ℝ) - θ1 / Q < t
    linarith [div_pos hθ1 hQ]
  have hdepth' : (t : ℝ) - (a' : ℝ) = θ1 / Q := by
    change (t : ℝ) - ((t : ℝ) - θ1 / Q) = θ1 / Q
    ring
  have hw0 : w ∈ riemannianClosedBallOf (scaleMetric Q hQ gt) w 0 := by
    change riemannianEDistOf (scaleMetric Q hQ gt) w w ≤ ENNReal.ofReal 0
    rw [riemannianEDistOf_self]
    exact bot_le
  have hdeep : (∀ x ∈ riemannianBallOf gt w ρ,
      (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          B.isRmBoundedBy (hat := hat) (K * Q)) ∨
      ∃ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t), v ≤ a' ∧
        ∃ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) x,
          B.isRmBoundedBy (hat := hvt) (K * Q)) →
      curvDerivNorm k (scaleMetric Q hQ gt) w ≤ max (Jt k) (max (Real.sqrt Bsh) Jcap) := by
    intro hall''
    have htr := bornPatch_isTracedRegion_C11SP H t w hρ a a' hat haa' ha't hlt' hall''
    rw [hdepth'] at htr
    exact (hJt H t w Q hQ htr k w hw0).trans (le_max_left _ _)
  by_cases hB : ∃ x ∈ riemannianBallOf gt w ρ, Born x
  swap
  · apply hdeep
    intro x hx
    exact Or.inl ((hall x (hsub hx)).resolve_right fun hbx => hB ⟨x, hx, hbx⟩)
  obtain ⟨xs, hxs, es, ⟨us, hust, haus, hes1, hes2, Bs, _hBs, bs, zs, hzs, hheqs, hscs⟩, hmax⟩ :=
    exists_max_bornTime_C11SP H (riemannianBallOf gt w ρ)
      (fun x e => ∃ (u : Icc (0 : ℝ) H.horizon) (hut : u ≤ t), a < u ∧
        H.time e.succ = (u : ℝ) ∧ e.succ = H.activeStage u ∧
        ∃ B : BackwardPointTrace H (H.activeStage u) (H.activeStage t)
            (H.activeStage_mono hut) x,
          B.isRmBoundedBy (hat := hut) (K * Q) ∧
          ∃ (b : (H.event e).RetainedBoundaryIndex)
            (z : standardCapWindow params.modelRadius),
            ‖z.val‖ ≤ StandardCap.transitionEnd + 10 ∧
            HEq (((records n e).static b).window z)
              (B.point (H.activeStage u) le_rfl (H.activeStage_mono hut)) ∧
            ((records n e).static b).neck.scale ≤ c * Q)
      (by
        obtain ⟨x, hx, u, hut, hau, e, he1, he2, rest⟩ := hB
        exact ⟨x, hx, e, u, hut, hau, he1, he2, rest⟩)
  have hall' : ∀ x ∈ riemannianBallOf gt w ρ,
      (∃ B : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) x,
          B.isRmBoundedBy (hat := hat) (K * Q)) ∨
      ∃ (v : Icc (0 : ℝ) H.horizon) (hvt : v ≤ t), v ≤ us ∧
        ∃ B : BackwardPointTrace H (H.activeStage v) (H.activeStage t) (H.activeStage_mono hvt) x,
          B.isRmBoundedBy (hat := hvt) (K * Q) := by
    intro x hx
    rcases hall x (hsub hx) with halive | ⟨u, hut, hau, e, he1, he2, Bx, hBx, rest⟩
    · exact Or.inl halive
    · refine Or.inr ⟨u, hut, ?_, Bx, hBx⟩
      have h := hmax x hx e ⟨u, hut, hau, he1, he2, Bx, hBx, rest⟩
      change (u : ℝ) ≤ (us : ℝ)
      rw [← he1, ← hes1]
      exact h
  by_cases hdeepc : θ1 / Q ≤ (t : ℝ) - us
  · apply hdeep
    intro x hx
    rcases hall' x hx with h | ⟨v, hvt, hvu, Bx, hBx⟩
    · exact Or.inl h
    · refine Or.inr ⟨v, hvt, ?_, Bx, hBx⟩
      change (v : ℝ) ≤ (t : ℝ) - θ1 / Q
      have h1 : (v : ℝ) ≤ us := hvu
      linarith
  rw [not_le] at hdeepc
  have hus_late : T₀ ≤ (us : ℝ) := by
    linarith [le_max_left T₀ 1]
  have hcapδ : ∀ j, j ≤ k → ((records n es).static bs).delta ≤ δj j := by
    intro j hj
    have hδt : params.delta (H.time es.succ) < δmin / params.recenterConstant :=
      hT₀ _ (by rw [hes1]; exact hus_late)
    have hmul : params.recenterConstant * params.delta (H.time es.succ) ≤ δmin := by
      have h := (lt_div_iff₀ hrc).mp hδt
      nlinarith
    calc ((records n es).static bs).delta
        = params.recenterConstant * (records n es).delta bs.1.1 :=
          (records n es).recenter_delta bs
      _ ≤ params.recenterConstant * params.delta (H.time es.succ) :=
          mul_le_mul_of_nonneg_left ((records n es).delta_le bs.1.1) hrc.le
      _ ≤ δmin := hmul
      _ ≤ δj j := hδle j hj
  have hscale_pow : ∀ j, Cj j ^ 2 * ((records n es).static bs).neck.scale ^ (j + 2) ≤
      A j * Q ^ (2 + j) := by
    intro j
    have h0 : 0 ≤ ((records n es).static bs).neck.scale :=
      ((records n es).static bs).neck.scale_pos.le
    calc Cj j ^ 2 * ((records n es).static bs).neck.scale ^ (j + 2)
        ≤ Cj j ^ 2 * (c * Q) ^ (j + 2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hscs _) (sq_nonneg _)
      _ = A j * Q ^ (2 + j) := by
          change Cj j ^ 2 * (c * Q) ^ (j + 2) = Cj j ^ 2 * c ^ (j + 2) * Q ^ (2 + j)
          rw [mul_pow, add_comm 2 j]
          ring
  have hddnn : 0 ≤ L0 * (2 * ρ0 / Real.sqrt Q) :=
    mul_nonneg (by linarith) (div_nonneg (by linarith) hsQ.le)
  have hsM : ((records n es).static bs).neck.scale ≤ 4 * (c * Q / 4) := by linarith
  rcases lt_or_eq_of_le (show (us : ℝ) ≤ t from hust) with hlt | heq
  · -- 窄情形：公共 flow + Q 一致 reset Shi
    obtain ⟨U, hU, f, hf, hpt, Sf, hSf, hmetric, hRm, hterm⟩ :=
      bornPatch_commonFlow_C11SP H t w hρ a us hat haus.le hust hlt hall'
    have hUmem : ∀ x, x ∈ riemannianBallOf gt w ρ → x ∈ (U : Set (H.stageAt t).Carrier) := by
      intro x hx
      rw [hU]
      exact hx
    have hwU : w ∈ U := by
      refine SetLike.mem_coe.mp (hUmem w ?_)
      change riemannianEDistOf gt w w < ENNReal.ofReal ρ
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hρ
    have hxsU : xs ∈ U := SetLike.mem_coe.mp (hUmem xs hxs)
    let pU : U := ⟨w, hwU⟩
    let xU : U := ⟨xs, hxsU⟩
    let ja : H.StageInterval (H.activeStage us) (H.activeStage t) :=
      ⟨H.activeStage us, le_rfl, H.activeStage_mono hust⟩
    have hfxs : f ja xU = Bs.point (H.activeStage us) le_rfl (H.activeStage_mono hust) :=
      hpt xU Bs ja
    have htus : H.time (H.activeStage us) = us := hes2 ▸ hes1
    have hSu : Sf.base.metric us =
        localPullMetric (H.stageMetric (H.activeStage us) us) (f ja) (hf ja) :=
      hmetric ja us ⟨le_rfl, hust⟩ (H.activeStage_mem us)
    have hcarS : Icc (us : ℝ) t ⊆ (RealTimeInterval.closed us.val t.val hust).carrier :=
      fun _ h => h
    have hregS : Ioo (us : ℝ) t ⊆ (RealTimeInterval.closed us.val t.val hust).regular :=
      fun _ h => h
    have hcmp := (riemannianEDistOf_exp_bounds_of_curvature_bound Sf hSf hcarS hregS hRm
      (s := (us : ℝ)) (t := (t : ℝ)) ⟨le_rfl, hust⟩ ⟨hust, le_rfl⟩ xU pU).2
    have hQt : Q * ((t : ℝ) - us) ≤ θ1 := by
      have h := (lt_div_iff₀ hQ).mp hdeepc
      linarith [mul_comm Q ((t : ℝ) - us)]
    have hexp : Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt ((K * Q) ^ 2) *
        |(us : ℝ) - t|) ≤ L0 := by
      change _ ≤ Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * θ1)
      apply Real.exp_le_exp.mpr
      rw [Real.sqrt_sq (mul_pos hK hQ).le, abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)]
      have h1 : K * Q * ((t : ℝ) - us) ≤ K * θ1 := by
        calc K * Q * ((t : ℝ) - us) = K * (Q * ((t : ℝ) - us)) := by ring
          _ ≤ K * θ1 := mul_le_mul_of_nonneg_left hQt hK.le
      calc (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (K * Q) * ((t : ℝ) - us)
          = (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (K * Q * ((t : ℝ) - us)) := by ring
        _ ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * (K * θ1) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * K * θ1 := by ring
    have hdt : riemannianEDistOf (Sf.base.metric t) pU xU < ENNReal.ofReal ρ := by
      rw [hterm]
      exact Geometry.Metric.riemannianEDistOf_restrictOpen_lt_of_riemannianBallOf_subset gt U
        pU xU (fun x hx => hUmem x hx) hxs
    have hdus : riemannianEDistOf (Sf.base.metric us) xU pU ≤ ENNReal.ofReal (L0 * ρ) := by
      calc riemannianEDistOf (Sf.base.metric us) xU pU
          ≤ ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
              Real.sqrt ((K * Q) ^ 2) * |(us : ℝ) - t|)) *
            riemannianEDistOf (Sf.base.metric t) xU pU := hcmp
        _ ≤ ENNReal.ofReal L0 * ENNReal.ofReal ρ := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) ?_
            rw [riemannianEDistOf_comm]
            exact hdt.le
        _ = ENNReal.ofReal (L0 * ρ) := (ENNReal.ofReal_mul (by linarith)).symm
    have hdd : L0 * ρ + R0 / Real.sqrt Q ≤ L0 * (2 * ρ0 / Real.sqrt Q) := by
      have hR0le : R0 ≤ ρ0 := div_le_self hρ0.le (by linarith)
      have h1 : R0 / Real.sqrt Q ≤ L0 * (ρ0 / Real.sqrt Q) :=
        calc R0 / Real.sqrt Q ≤ ρ0 / Real.sqrt Q := div_le_div_of_nonneg_right hR0le hsQ.le
          _ ≤ L0 * (ρ0 / Real.sqrt Q) :=
            le_mul_of_one_le_left (div_nonneg hρ0.le hsQ.le) hL0
      have h2 : L0 * (2 * ρ0 / Real.sqrt Q) =
          L0 * (ρ0 / Real.sqrt Q) + L0 * (ρ0 / Real.sqrt Q) := by ring
      rw [h2]
      change L0 * (ρ0 / Real.sqrt Q) + R0 / Real.sqrt Q ≤ _
      linarith
    have hinit : ∀ j, 1 ≤ j → j ≤ k → ∀ x : U,
        riemannianEDistOf (Sf.base.metric us) pU x ≤ ENNReal.ofReal (R0 / Real.sqrt Q) →
        curvDerivNormSq j (H.stageMetric (H.activeStage us) us)
          (f ⟨H.activeStage us, le_rfl, H.activeStage_mono hust⟩ x) ≤ A j * Q ^ (2 + j) := by
      intro j _ hjk x hx
      have hdS : riemannianEDistOf (Sf.base.metric us) xU x ≤
          ENNReal.ofReal (L0 * ρ + R0 / Real.sqrt Q) := by
        calc riemannianEDistOf (Sf.base.metric us) xU x
            ≤ riemannianEDistOf (Sf.base.metric us) xU pU +
                riemannianEDistOf (Sf.base.metric us) pU x :=
              riemannianEDistOf_triangle _ _ _ _
          _ ≤ ENNReal.ofReal (L0 * ρ) + ENNReal.ofReal (R0 / Real.sqrt Q) := add_le_add hdus hx
          _ = ENNReal.ofReal (L0 * ρ + R0 / Real.sqrt Q) :=
              (ENNReal.ofReal_add (mul_nonneg (by linarith) hρ.le)
                (div_nonneg hR0.le hsQ.le)).symm
      have hpull : riemannianEDistOf (H.stageMetric (H.activeStage us) us) (f ja xU) (f ja x) ≤
          riemannianEDistOf (Sf.base.metric us) xU x := by
        have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph (Sf.base.metric us)
          (H.stageMetric (H.activeStage us) us) (f ja) (hf ja) one_pos
          (fun z v => by rw [hSu, localPullMetric_inner, one_mul]) xU x
        simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using h
      have hnear : riemannianEDistOf ((F.tower.history n).toHistory.stageMetric
          (H.activeStage us) ((F.tower.history n).toHistory.time (H.activeStage us)))
          (Bs.point (H.activeStage us) le_rfl (H.activeStage_mono hust)) (f ja x) ≤
          ENNReal.ofReal (L0 * (2 * ρ0 / Real.sqrt Q)) := by
        change riemannianEDistOf (H.stageMetric (H.activeStage us) (H.time (H.activeStage us)))
          _ _ ≤ _
        rw [htus, ← hfxs]
        exact (hpull.trans hdS).trans (ENNReal.ofReal_le_ofReal hdd)
      obtain ⟨x', hx'D, hx'eq⟩ := bornPoint_window_capture_C11SP (F.tower.history n) (records n)
        (hcan n) hacc' es (H.activeStage us) hes2 bs hsM le_rfl zs hzs _ (f ja x) hheqs hnear
        hddnn (hfitρ Q hQ)
      have hj := stage_jets_of_output_window_C11SP (F.tower.history n) (records n) es
        (H.activeStage us) hes2 bs j x'
        (hjets j ((records n es).static bs) (hlink n es bs) (hcapδ j hjk) x' hx'D) (f ja x) hx'eq
      change curvDerivNormSq j (H.stageMetric (H.activeStage us) (H.time (H.activeStage us)))
        (f ja x) ≤ _ at hj
      rw [htus] at hj
      exact hj.trans (hscale_pow j)
    have hRm' : ∀ v ∈ Icc us.val t.val, ∀ x : U,
        normSq0S (Sf.base.metric v) x 4 (Sf.base.rm04 v x) ≤ K ^ 2 * Q ^ 2 :=
      fun v hv x => (hRm v hv x).trans_eq (mul_pow K Q 2)
    let Rbig : ℝ≥0 := (ρ / 2).toNNReal
    have hballR : {x | riemannianEDistOf gt pU.val x ≤ (Rbig : ℝ≥0∞)} ⊆ U := by
      intro x hx
      refine hUmem x ?_
      change riemannianEDistOf gt w x < ENNReal.ofReal ρ
      have hx' : riemannianEDistOf gt w x ≤ ENNReal.ofReal (ρ / 2) := hx
      exact hx'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hρ).mpr (by linarith))
    have hfit : ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
        Real.sqrt (K ^ 2 * Q ^ 2) * |(us : ℝ) - t|)) * ENNReal.ofReal (R0 / Real.sqrt Q) ≤
        (Rbig : ℝ≥0∞) := by
      rw [← mul_pow]
      have hL0ne : L0 ≠ 0 := ne_of_gt (by linarith)
      have heqR : L0 * (R0 / Real.sqrt Q) = ρ / 2 := by
        change L0 * (ρ0 / (2 * L0) / Real.sqrt Q) = ρ0 / Real.sqrt Q / 2
        field_simp
      calc ENNReal.ofReal (Real.exp ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
            Real.sqrt ((K * Q) ^ 2) * |(us : ℝ) - t|)) * ENNReal.ofReal (R0 / Real.sqrt Q)
          ≤ ENNReal.ofReal L0 * ENNReal.ofReal (R0 / Real.sqrt Q) :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hexp) le_rfl
        _ = ENNReal.ofReal (L0 * (R0 / Real.sqrt Q)) := (ENNReal.ofReal_mul (by linarith)).symm
        _ = ENNReal.ofReal (ρ / 2) := by rw [heqR]
    have hfinal := hShi H hust Q hQ hlt hQt hpos U f hf Sf hSf hmetric hRm' hterm pU Rbig
      hballR hfit hinit k le_rfl
    exact hfinal.trans ((le_max_left _ _).trans (le_max_right _ _))
  · -- born 于 t：G1 capture + G63 直接给 t 时刻 jets
    have hEq : us = t := Subtype.ext heq
    subst us
    have htt : H.time (H.activeStage t) = t := hes2 ▸ hes1
    have hPx : Bs.point (H.activeStage t) le_rfl (H.activeStage_mono hust) = xs := Bs.endpoint_eq
    have hnear : riemannianEDistOf ((F.tower.history n).toHistory.stageMetric
        (H.activeStage t) ((F.tower.history n).toHistory.time (H.activeStage t)))
        (Bs.point (H.activeStage t) le_rfl (H.activeStage_mono hust)) w ≤
        ENNReal.ofReal (L0 * (2 * ρ0 / Real.sqrt Q)) := by
      change riemannianEDistOf (H.stageMetric (H.activeStage t) (H.time (H.activeStage t)))
        _ _ ≤ _
      rw [htt, hPx, riemannianEDistOf_comm]
      refine hxs.le.trans (ENNReal.ofReal_le_ofReal ?_)
      change ρ0 / Real.sqrt Q ≤ L0 * (2 * ρ0 / Real.sqrt Q)
      calc ρ0 / Real.sqrt Q ≤ 2 * ρ0 / Real.sqrt Q :=
            div_le_div_of_nonneg_right (by linarith) hsQ.le
        _ ≤ L0 * (2 * ρ0 / Real.sqrt Q) :=
            le_mul_of_one_le_left (div_nonneg (by linarith) hsQ.le) hL0
    obtain ⟨x', hx'D, hx'eq⟩ := bornPoint_window_capture_C11SP (F.tower.history n) (records n)
      (hcan n) hacc' es (H.activeStage t) hes2 bs hsM le_rfl zs hzs _ w hheqs hnear
      hddnn (hfitρ Q hQ)
    have hj := stage_jets_of_output_window_C11SP (F.tower.history n) (records n) es
      (H.activeStage t) hes2 bs k x'
      (hjets k ((records n es).static bs) (hlink n es bs) (hcapδ k le_rfl) x' hx'D) w hx'eq
    change curvDerivNormSq k (H.stageMetric (H.activeStage t) (H.time (H.activeStage t))) w ≤ _
      at hj
    rw [htt] at hj
    have hsq : curvDerivNormSq k (scaleMetric Q hQ gt) w ≤ A k := by
      rw [curvDerivNormSq_scaleMetric]
      have hQk : Q⁻¹ ^ (k + 2) * (A k * Q ^ (2 + k)) = A k := by
        rw [add_comm 2 k, mul_left_comm, ← mul_pow, inv_mul_cancel₀ hQ.ne', one_pow, mul_one]
      calc Q⁻¹ ^ (k + 2) * curvDerivNormSq k gt w ≤ Q⁻¹ ^ (k + 2) * (A k * Q ^ (2 + k)) :=
            mul_le_mul_of_nonneg_left (hj.trans (hscale_pow k))
              (pow_nonneg (inv_pos.mpr hQ).le _)
        _ = A k := hQk
    have hnorm : curvDerivNorm k (scaleMetric Q hQ gt) w ≤ Jcap := by
      unfold curvDerivNorm
      exact Real.sqrt_le_sqrt hsq
    exact hnorm.trans ((le_max_right _ _).trans (le_max_right _ _))

/-- consumer：hBorn′ 的类型检查（G4 NJSlot v3 暂缓，见 state O2）。 -/
example (P : OrientedThreeStage.{u}) (g : P.Metric) : True := by
  have _h := hBorn_linked_C11SP P g
  trivial

end GC.LongTime.Ch11
