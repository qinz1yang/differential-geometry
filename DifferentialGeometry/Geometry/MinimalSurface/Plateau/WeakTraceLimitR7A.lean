import DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeaklyMonotoneLimitR7A
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SecondTrimR8

/-!
# S-MY-R7A G3 consumer：`C⁰` 极限盘的 trace 仍是 `Γ` 的 weak Jordan 参数化

R7 需要"正确 weak trace"：`uₙ` 的 trace 是 `Γ ∘ σₙ`（`σₙ` weakly monotone once），`uₙ → w` 在闭盘上
`C⁰` 一致（`riemannianEDistOf G`），`Γ` 是 embedding ⇒ `w` 的 trace 也是 `Γ ∘ σ`，`σ` weakly monotone once。

证明：`C⁰` 收敛使 `Γ (σₙ θ) = uₙ (∂θ) → w (∂θ)`，`range Γ` 闭 ⇒ `w (∂θ) = Γ (σ θ)`；`Γ` embedding ⇒
`σ` 连续；`σₙ → σ` 一致（紧集 `{dist ≥ ε'}` 上 `edist_G (Γ ·) (Γ ·)` 有正下界）；
再由 G3（`weaklyMonotoneOnce_closed_under_uniform_limit_R7A`）得 `σ` weakly monotone once。
不加 chord-arc，不把"极限严格单调"当中间结论。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- `riemannianEDistOf G` 的小球给出流形拓扑下的收敛。 -/
theorem tendsto_of_riemannianEDistOf_R7A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {ι : Type*} {l : Filter ι} {f : ι → M} {x : M}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ i in l, riemannianEDistOf G (f i) x < ε) :
    Tendsto f l (𝓝 x) := by
  let : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have : RegularSpace M := inferInstance
  let : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) M
  exact EMetric.tendsto_nhds.mpr h

/-- **G3 consumer**：`C⁰` 一致极限盘的 trace 仍是 `Γ` 的 weak Jordan 参数化（`Γ` embedding）。 -/
theorem diskWeakJordanTrace_of_C0_limit_R7A (G : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {Γ : freeLoop M} (hΓ : Topology.IsEmbedding Γ)
    {u : ℕ → C(closedDisk, M)} (hu : ∀ n, DiskWeakJordanTrace Γ (u n)) {w : C(closedDisk, M)}
    (hC0 : ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ n in atTop, ∀ z, riemannianEDistOf G (u n z) (w z) < ε) :
    DiskWeakJordanTrace Γ w := by
  choose σs hσs hσtr using hu
  have hclosed : IsClosed (range Γ) :=
    (Γ.continuous.isClosedEmbedding hΓ.injective).isClosed_range
  -- 极限 trace 落在 `range Γ`
  have hmem : ∀ θ : loopCircle, ∃ a : loopCircle, Γ a = w (diskBoundary θ) := by
    intro θ
    have hlim : Tendsto (fun n => u n (diskBoundary θ)) atTop (𝓝 (w (diskBoundary θ))) :=
      tendsto_of_riemannianEDistOf_R7A G fun ε hε => (hC0 ε hε).mono fun n hn => hn _
    refine hclosed.mem_of_tendsto hlim (Eventually.of_forall fun n => ⟨σs n θ, ?_⟩)
    have := congrArg (fun f : freeLoop M => f θ) (hσtr n)
    exact this.symm
  choose σf hσf using hmem
  have hcomp : (Γ ∘ σf) = fun θ => w (diskBoundary θ) := funext hσf
  have hσc : Continuous σf := hΓ.continuous_iff.mpr (by
    rw [hcomp]
    exact w.continuous.comp diskBoundary.continuous)
  let σ : C(loopCircle, loopCircle) := ⟨σf, hσc⟩
  -- `σₙ → σ` 一致
  have hunif : TendstoUniformly (fun n => (σs n : loopCircle → loopCircle)) σ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε' hε'
    set K : Set (loopCircle × loopCircle) := {p | ε' ≤ dist p.1 p.2} with hK
    have hKc : IsCompact K := (isClosed_le continuous_const
      (continuous_fst.dist continuous_snd)).isCompact
    have hcont : Continuous (fun p : loopCircle × loopCircle =>
        riemannianEDistOf G (Γ p.1) (Γ p.2)) :=
      (continuous_riemannianEDistOf_prod_R8 G).comp
        ((Γ.continuous.comp continuous_fst).prodMk (Γ.continuous.comp continuous_snd))
    have hη : ∃ η : ℝ≥0∞, 0 < η ∧ ∀ p ∈ K, η ≤ riemannianEDistOf G (Γ p.1) (Γ p.2) := by
      rcases K.eq_empty_or_nonempty with hKe | hKne
      · exact ⟨1, one_pos, by simp [hKe]⟩
      · obtain ⟨p₀, hp₀, hmin⟩ := hKc.exists_isMinOn hKne hcont.continuousOn
        refine ⟨_, ?_, fun p hp => isMinOn_iff.mp hmin p hp⟩
        rw [pos_iff_ne_zero]
        intro h0
        have heq : p₀.1 = p₀.2 :=
          hΓ.injective (eq_of_riemannianEDistOf_eq_zero_R8 G h0)
        have : ε' ≤ dist p₀.1 p₀.2 := hp₀
        rw [heq, dist_self] at this
        linarith
    obtain ⟨η, hη0, hηK⟩ := hη
    filter_upwards [hC0 η hη0] with n hn θ
    by_contra hnot
    have hmemK : (σ θ, σs n θ) ∈ K := by
      change ε' ≤ dist (σ θ) (σs n θ)
      exact not_lt.mp hnot
    have h1 := hηK _ hmemK
    have h2 := hn (diskBoundary θ)
    have hx : Γ (σs n θ) = u n (diskBoundary θ) := by
      have := congrArg (fun f : freeLoop M => f θ) (hσtr n)
      exact this.symm
    have hy : Γ (σ θ) = w (diskBoundary θ) := hσf θ
    simp only [hx, hy] at h1
    rw [riemannianEDistOf_comm] at h1
    exact absurd h2 (not_lt.mpr h1)
  have hwmo := weaklyMonotoneOnce_closed_under_uniform_limit_R7A (l := atTop)
    (Eventually.of_forall hσs) hunif
  refine ⟨σ, hwmo, ?_⟩
  ext θ
  exact (hσf θ).symm

end DifferentialGeometry.Geometry

end
