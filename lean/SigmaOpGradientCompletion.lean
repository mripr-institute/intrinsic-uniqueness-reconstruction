import SigmaOpFormCore
import SigmaOpCanonicalClosure
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

namespace Sigma
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def weightedTestDerivative (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Complex.ofReal (Real.sqrt t)*deriv f t

theorem weighted_test_derivative_mem_l2 (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : Memℒp (weightedTestDerivative f) 2 gammaProbability := by
  have hd : Continuous (deriv f) := (contDiff_infty_iff_deriv.mp hf).2.continuous
  exact ((Complex.continuous_ofReal.comp Real.continuous_sqrt).mul hd).memℒp_of_hasCompactSupport
    hs.deriv.mul_left

def smoothCompactGradient (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) : LaguerreWeightedHilbert :=
  (weighted_test_derivative_mem_l2 f hf hs).toLp (weightedTestDerivative f)

theorem smooth_compact_gradient_coe (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    (smoothCompactGradient f hf hs : ℝ → ℂ) =ᵐ[gammaProbability] weightedTestDerivative f :=
  Memℒp.coeFn_toLp _

theorem smooth_compact_gradient_norm_sq (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ‖smoothCompactGradient f hf hs‖^2 =
      ∫ t : ℝ in Ioi 0, steinFlux t*‖deriv f t‖^2 := by
  rw [laguerre_l2_norm_sq_of_ae _ _ (smooth_compact_gradient_coe f hf hs),
    gamma_probability_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [weightedTestDerivative, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, Real.sq_sqrt (le_of_lt ht), steinFlux, SigmaPresentations.density]
  ring

theorem smooth_compact_gradient_norm_eq_root (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    ‖smoothCompactGradient f hf hs‖ =
      ‖laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector f hf hs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hs)⟩‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [smooth_compact_gradient_norm_sq, smooth_compact_square_root_differential_energy]

theorem complex_compact_sub {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hg : HasCompactSupport g) :
    HasCompactSupport (fun t => f t-g t) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg'

theorem smooth_compact_vector_sub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    smoothCompactL2Vector (fun t => f t-g t) (hf.sub hg) (complex_compact_sub hfs hgs) =
      smoothCompactL2Vector f hf hfs-smoothCompactL2Vector g hg hgs := by
  apply Lp.ext
  filter_upwards [smooth_compact_l2_coe _ (hf.sub hg) (complex_compact_sub hfs hgs),
    Lp.coeFn_sub (smoothCompactL2Vector f hf hfs) (smoothCompactL2Vector g hg hgs),
    smooth_compact_l2_coe f hf hfs, smooth_compact_l2_coe g hg hgs] with t ht hsub hft hgt
  simpa only [Pi.sub_apply, hft, hgt, ht] using hsub.symm

theorem smooth_compact_gradient_sub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    smoothCompactGradient (fun t => f t-g t) (hf.sub hg) (complex_compact_sub hfs hgs) =
      smoothCompactGradient f hf hfs-smoothCompactGradient g hg hgs := by
  apply Lp.ext
  filter_upwards [smooth_compact_gradient_coe _ (hf.sub hg) (complex_compact_sub hfs hgs),
    Lp.coeFn_sub (smoothCompactGradient f hf hfs) (smoothCompactGradient g hg hgs),
    smooth_compact_gradient_coe f hf hfs, smooth_compact_gradient_coe g hg hgs] with t ht hsub hft hgt
  rw [ht, hsub, Pi.sub_apply, hft, hgt]
  simp only [weightedTestDerivative,
    deriv_sub (hf.differentiable (by simp) t) (hg.differentiable (by simp) t), mul_sub]

theorem smooth_compact_gradient_sub_norm (f g : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    ‖smoothCompactGradient f hf hfs-smoothCompactGradient g hg hgs‖ =
      ‖laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector f hf hfs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hfs)⟩-
       laguerreSpectralOperator Real.sqrt ⟨smoothCompactL2Vector g hg hgs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain g hg hgs)⟩‖ := by
  rw [← smooth_compact_gradient_sub f g hf hg hfs hgs, smooth_compact_gradient_norm_eq_root]
  congr 1
  have he : (⟨smoothCompactL2Vector (fun t => f t-g t) (hf.sub hg) (complex_compact_sub hfs hgs),
      laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩ :
      (laguerreSpectralOperator Real.sqrt).domain) =
      ⟨smoothCompactL2Vector f hf hfs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain f hf hfs)⟩-
      ⟨smoothCompactL2Vector g hg hgs,
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain g hg hgs)⟩ := by
    apply Subtype.ext
    exact smooth_compact_vector_sub f g hf hg hfs hgs
  rw [he, LinearPMap.map_sub]

/-- Every vector in the full square-root domain admits genuine compact
interior smooth approximants whose weighted classical derivatives converge
in the actual Gamma L² space. No regularity of the limit is assumed. -/
theorem laguerre_weighted_gradient_completion
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ f : ℕ → ℝ → ℂ, ∃ hf : ∀ k, ContDiff ℝ ∞ (f k),
    ∃ hs : ∀ k, HasCompactSupport (f k),
      (∀ k, tsupport (f k) ⊆ Ioi 0) ∧
      ∃ g : LaguerreWeightedHilbert,
        Tendsto (fun k => smoothCompactL2Vector (f k) (hf k) (hs k)) atTop (𝓝 x.val) ∧
        Tendsto (fun k => smoothCompactGradient (f k) (hf k) (hs k)) atTop (𝓝 g) ∧
        ‖g‖^2 = ‖laguerreSpectralOperator Real.sqrt x‖^2 := by
  obtain ⟨u, hu, hSu⟩ := laguerre_compact_form_sequence_of_modes
    laguerre_modes_mem_minimal_graph_closure x
  have hrep (k : ℕ) : ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ Ioi 0 ∧ ((u k).val : ℝ → ℂ) =ᵐ[gammaProbability] f := by
    have hle : laguerreMinimalFormRoot.domain ≤ laguerreCompactTestDomain := by
      rw [laguerre_minimal_form_root_domain, laguerre_minimal_domain]
    exact hle (u k).property
  choose f hf hs hp hrep using hrep
  have hv (k : ℕ) : smoothCompactL2Vector (f k) (hf k) (hs k) = (u k).val :=
    smooth_compact_vector_eq_of_ae _ _ _ _ (hrep k)
  have hroot (k : ℕ) : laguerreSpectralOperator Real.sqrt
      ⟨smoothCompactL2Vector (f k) (hf k) (hs k),
        laguerre_integer_domain_le_square_root (smooth_compact_mem_laguerre_domain _ _ _)⟩ =
      laguerreMinimalFormRoot (u k) :=
    (laguerre_minimal_form_root_le.2 (hv k).symm).symm
  have hc : CauchySeq (fun k => smoothCompactGradient (f k) (hf k) (hs k)) := by
    have hcs := Metric.cauchySeq_iff.mp hSu.cauchySeq
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := hcs ε hε
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [dist_eq_norm, smooth_compact_gradient_sub_norm, hroot m, hroot n]
    exact hN m hm n hn
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨f,hf,hs,hp,g, ?_, hg, ?_⟩
  · simpa only [hv] using hu
  · have hnorm (k : ℕ) : ‖smoothCompactGradient (f k) (hf k) (hs k)‖ =
        ‖laguerreMinimalFormRoot (u k)‖ := by
      rw [smooth_compact_gradient_norm_eq_root, hroot k]
    have hn : ‖g‖ = ‖laguerreSpectralOperator Real.sqrt x‖ :=
      tendsto_nhds_unique hg.norm (by simpa only [hnorm] using hSu.norm)
    rw [hn]

theorem laguerre_l2_ae_subsequence (u : ℕ → LaguerreWeightedHilbert)
    (x : LaguerreWeightedHilbert) (hu : Tendsto u atTop (𝓝 x))
    (f : ℕ → ℝ → ℂ) (hf : ∀ k, (u k : ℝ → ℂ) =ᵐ[gammaProbability] f k) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ t ∂gammaProbability, Tendsto (fun k => f (ns k) t) atTop (𝓝 (x t)) := by
  have hm := (tendstoInMeasure_of_tendsto_Lp hu).congr_left hf
  exact hm.exists_seq_tendsto_ae

theorem laguerre_weighted_gradient_completion_ae
    (x : (laguerreSpectralOperator Real.sqrt).domain) :
    ∃ f : ℕ → ℝ → ℂ, ∃ hf : ∀ k, ContDiff ℝ ∞ (f k),
    ∃ hs : ∀ k, HasCompactSupport (f k),
      (∀ k, tsupport (f k) ⊆ Ioi 0) ∧
      ∃ g : LaguerreWeightedHilbert,
        Tendsto (fun k => smoothCompactL2Vector (f k) (hf k) (hs k)) atTop (𝓝 x.val) ∧
        Tendsto (fun k => smoothCompactGradient (f k) (hf k) (hs k)) atTop (𝓝 g) ∧
        (∀ᵐ t ∂gammaProbability, Tendsto (fun k => f k t) atTop (𝓝 (x.val t))) ∧
        ‖g‖^2 = ‖laguerreSpectralOperator Real.sqrt x‖^2 := by
  obtain ⟨f,hf,hs,hp,g,hv,hg,he⟩ := laguerre_weighted_gradient_completion x
  obtain ⟨ns,hns,hae⟩ := laguerre_l2_ae_subsequence _ x.val hv f
    (fun k => smooth_compact_l2_coe _ _ _)
  exact ⟨fun k => f (ns k), fun k => hf (ns k), fun k => hs (ns k),
    fun k => hp (ns k),g,hv.comp hns.tendsto_atTop,hg.comp hns.tendsto_atTop,hae,he⟩

end
end Sigma
