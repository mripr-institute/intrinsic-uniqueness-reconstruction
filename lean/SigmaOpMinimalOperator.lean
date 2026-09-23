import SigmaOpDifferentialBridge
import Mathlib.Topology.Algebra.Module.LinearPMap

namespace Sigma
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- The literal image of C_c^infinity(0,infinity) in the weighted Hilbert
space. Derivative or spectral-domain conditions are not part of this domain. -/
def laguerreCompactTestDomain : Submodule ℂ LaguerreWeightedHilbert where
  carrier := {x | ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ Ioi 0 ∧ (x : ℝ → ℂ) =ᵐ[gammaProbability] f}
  zero_mem' := by
    refine ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, ?_, Lp.coeFn_zero ℂ 2 gammaProbability⟩
    simp [tsupport, Function.support]
  add_mem' := by
    rintro x y ⟨f,hf,hfs,hfp,hfx⟩ ⟨g,hg,hgs,hgp,hgy⟩
    refine ⟨fun t => f t+g t, hf.add hg, hfs.add hgs, ?_, ?_⟩
    · exact tsupport_add.trans (union_subset hfp hgp)
    · filter_upwards [Lp.coeFn_add x y, hfx, hgy] with t ht hx hy
      simpa only [Pi.add_apply, hx, hy] using ht
  smul_mem' := by
    rintro c x ⟨f,hf,hfs,hfp,hfx⟩
    refine ⟨fun t => c * f t, contDiff_const.mul hf, hfs.mul_left, ?_, ?_⟩
    · exact tsupport_mul_subset_right.trans hfp
    · filter_upwards [Lp.coeFn_smul c x, hfx] with t ht hx
      simpa only [Pi.smul_apply, smul_eq_mul, hx] using ht

theorem smooth_compact_vector_eq_of_ae (x : LaguerreWeightedHilbert) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hx : (x : ℝ → ℂ) =ᵐ[gammaProbability] f) :
    smoothCompactL2Vector f hf hs = x := by
  apply Lp.ext
  exact (smooth_compact_l2_coe f hf hs).trans hx.symm

theorem laguerre_compact_test_domain_le_spectral :
    laguerreCompactTestDomain ≤ (laguerreSpectralOperator id).domain := by
  rintro x ⟨f,hf,hs,_,hx⟩
  rw [← smooth_compact_vector_eq_of_ae x f hf hs hx]
  exact smooth_compact_mem_laguerre_domain f hf hs

/-- The actual compact-test differential operator, bundled by restricting the
already constructed spectral operator. The preceding integration-by-parts
theorem proves that this action is the literal differential expression; the
following domain theorem proves the restriction adds no spectral assumption.
Equality of its graph closure with the spectral operator remains a theorem
to be proved, not a definition of this operator. -/
def laguerreMinimalOperator : LaguerreWeightedHilbert →ₗ.[ℂ] LaguerreWeightedHilbert :=
  (laguerreSpectralOperator id).domRestrict laguerreCompactTestDomain

theorem laguerre_minimal_domain :
    laguerreMinimalOperator.domain = laguerreCompactTestDomain :=
  inf_eq_left.mpr laguerre_compact_test_domain_le_spectral

theorem laguerre_minimal_le_spectral :
    laguerreMinimalOperator ≤ laguerreSpectralOperator id :=
  LinearPMap.domRestrict_le

theorem laguerre_compact_test_mem (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    smoothCompactL2Vector f hf hs ∈ laguerreMinimalOperator.domain := by
  rw [laguerre_minimal_domain]
  exact ⟨f,hf,hs,hpos,smooth_compact_l2_coe f hf hs⟩

/-- Every actual compact-interior smooth test is mapped to its actual
second-order differential image in weighted L2. -/
theorem laguerre_minimal_test_action (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) (hpos : tsupport f ⊆ Ioi 0) :
    laguerreMinimalOperator ⟨smoothCompactL2Vector f hf hs,
      laguerre_compact_test_mem f hf hs hpos⟩ = smoothCompactL2Image f hf hs := by
  exact (laguerre_minimal_le_spectral.2 (y :=
    ⟨smoothCompactL2Vector f hf hs, smooth_compact_mem_laguerre_domain f hf hs⟩) rfl).trans
      (laguerre_spectral_extends_differential_test f hf hs)

theorem laguerre_minimal_representative_action (x : laguerreMinimalOperator.domain)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f)
    (hx : (x.val : ℝ → ℂ) =ᵐ[gammaProbability] f) :
    (laguerreMinimalOperator x : ℝ → ℂ) =ᵐ[gammaProbability]
      opComplexLaguerreExpression f := by
  have hval := smooth_compact_vector_eq_of_ae x.val f hf hs hx
  have hact : laguerreMinimalOperator x = smoothCompactL2Image f hf hs := by
    calc
      _ = laguerreSpectralOperator id ⟨smoothCompactL2Vector f hf hs,
          smooth_compact_mem_laguerre_domain f hf hs⟩ :=
        laguerre_minimal_le_spectral.2 hval.symm
      _ = _ := laguerre_spectral_extends_differential_test f hf hs
  rw [hact]
  exact smooth_compact_image_coe f hf hs

theorem laguerre_minimal_formal_adjoint :
    laguerreMinimalOperator.IsFormalAdjoint laguerreMinimalOperator := by
  intro x y
  have h := laguerre_spectral_formal_adjoint id
    ⟨x.val, laguerre_minimal_le_spectral.1 x.property⟩
    ⟨y.val, laguerre_minimal_le_spectral.1 y.property⟩
  rwa [← laguerre_minimal_le_spectral.2 (x := x) rfl,
    ← laguerre_minimal_le_spectral.2 (x := y) rfl] at h

end
end Sigma
